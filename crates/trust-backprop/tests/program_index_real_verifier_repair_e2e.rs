use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use serde_json::{Value, json};

const TRANSPORT_PREFIX: &str = "TRUST_JSON:";
const FLAWED_FIXTURE: &str = "examples/bench/program_index/cases/proof_div_zero_flawed.rs";
const BEFORE_STDERR: &str = "before.stderr";
const AFTER_STDERR: &str = "after.stderr";
const REPAIRED_RS: &str = "repaired.rs";
const PATCH_DIFF: &str = "patch.diff";
const IMPROVEMENT_JSON: &str = "repair-proof-improvement.json";
const IMPROVEMENT_MD: &str = "repair-proof-improvement.md";

/// End-to-end repair test that requires a real stage2 trustc.
///
/// When `TRUST_REPAIR_E2E_TRUSTC` is unset the helper prints a SKIP notice and
/// the test early-returns without invoking the compiler, so the test passes
/// trivially in normal `cargo test` runs. CI configurations that exercise the
/// full repair pipeline supply `TRUST_REPAIR_E2E_TRUSTC` + `TRUST_REPAIR_E2E_REPORT_DIR`.
#[test]
fn real_stage2_program_index_divzero_repair_improves_proof_counts() {
    let Some(trustc) = explicit_stage2_trustc_or_skip() else {
        return;
    };
    let report_dir = required_report_dir();
    fs::create_dir_all(&report_dir).expect("create TRUST_REPAIR_E2E_REPORT_DIR");

    let repo_root = repo_root();
    let fixture = repo_root.join(FLAWED_FIXTURE);
    assert!(fixture.is_file(), "program-index div-zero fixture is missing: {}", fixture.display());

    let temp = tempfile::tempdir().expect("create repair e2e tempdir");
    let work_dir = temp.path().join("work");
    fs::create_dir(&work_dir).expect("create repair work dir");
    let temp_source = work_dir.join("proof_div_zero_flawed.rs");
    fs::copy(&fixture, &temp_source).expect("copy flawed div-zero fixture to temp");

    let before = run_trustc_verify(&trustc, &temp_source, &work_dir, "before");
    fs::write(report_dir.join(BEFORE_STDERR), &before.stderr).expect("archive before stderr");
    assert_before_has_real_divzero_failure(&before);

    let original_source = fs::read_to_string(&temp_source).expect("read copied flawed source");
    let repaired_source = deterministic_divzero_repair(&original_source);
    assert_ne!(original_source, repaired_source, "repair must change the temp source");
    fs::write(&temp_source, &repaired_source).expect("write repaired temp source");
    fs::write(report_dir.join(REPAIRED_RS), &repaired_source).expect("archive repaired source");
    fs::write(
        report_dir.join(PATCH_DIFF),
        full_file_unified_diff(
            "proof_div_zero_flawed.rs",
            "repaired.rs",
            &original_source,
            &repaired_source,
        ),
    )
    .expect("archive repair diff");

    let after = run_trustc_verify(&trustc, &temp_source, &work_dir, "after");
    fs::write(report_dir.join(AFTER_STDERR), &after.stderr).expect("archive after stderr");

    write_improvement_artifacts(&report_dir, &trustc, &fixture, &before, &after);
    assert_after_improved(&before, &after);
}

#[derive(Debug, Clone, Copy, Default)]
struct ProofCounts {
    proved: usize,
    failed: usize,
    unknown: usize,
    runtime_checked: usize,
    total: usize,
    divzero_proved: usize,
    divzero_failed: usize,
    divzero_unknown: usize,
    divzero_runtime_checked: usize,
}

impl ProofCounts {
    fn add_result(&mut self, result: &TransportObligationResult) {
        match result.outcome.as_str() {
            "proved" => self.proved += 1,
            "failed" => self.failed += 1,
            "runtime_checked" => self.runtime_checked += 1,
            "unknown" | "timeout" => self.unknown += 1,
            _ => self.unknown += 1,
        }
        self.total += 1;

        if !is_divzero_obligation(result) {
            return;
        }
        match result.outcome.as_str() {
            "proved" => self.divzero_proved += 1,
            "failed" => self.divzero_failed += 1,
            "runtime_checked" => self.divzero_runtime_checked += 1,
            "unknown" | "timeout" => self.divzero_unknown += 1,
            _ => self.divzero_unknown += 1,
        }
    }
}

#[derive(Debug)]
struct VerifierRun {
    label: &'static str,
    command_display: String,
    status_success: bool,
    exit_code: Option<i32>,
    stdout: String,
    stderr: String,
    function_results: Vec<TransportFunctionResult>,
    counts: ProofCounts,
    divzero_counterexamples: Vec<String>,
}

#[derive(Debug, Clone)]
struct TransportFunctionResult {
    function: String,
    results: Vec<TransportObligationResult>,
}

#[derive(Debug, Clone)]
struct TransportObligationResult {
    // Retain the live transport correlation field even though this repair test
    // currently classifies rows by outcome and VC family only.
    #[allow(dead_code)]
    claim_digest_sha256: Option<String>,
    kind: String,
    description: String,
    outcome: String,
    counterexample: Option<String>,
    counterexample_model: Option<Value>,
}

impl VerifierRun {
    fn from_output(label: &'static str, command_display: String, output: Output) -> Self {
        let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        let function_results = parse_function_results(&stderr);
        let counts = aggregate_counts(&function_results);
        let divzero_counterexamples = divzero_counterexamples(&function_results);
        Self {
            label,
            command_display,
            status_success: output.status.success(),
            exit_code: output.status.code(),
            stdout,
            stderr,
            function_results,
            counts,
            divzero_counterexamples,
        }
    }

    fn stderr_tail(&self) -> String {
        tail_excerpt(&self.stderr, 8_000)
    }
}

fn explicit_stage2_trustc_or_skip() -> Option<PathBuf> {
    let value = match std::env::var_os("TRUST_REPAIR_E2E_TRUSTC") {
        Some(value) if !value.is_empty() => value,
        _ => {
            eprintln!(
                "SKIPPING: TRUST_REPAIR_E2E_TRUSTC is unset; set it to a real stage2 trustc to run this ignored e2e test"
            );
            return None;
        }
    };
    let raw = PathBuf::from(value);
    let path = if raw.is_absolute() { raw } else { repo_root().join(raw) };
    assert!(path.is_file(), "TRUST_REPAIR_E2E_TRUSTC is not a file: {}", path.display());
    assert!(
        is_stage2_path(&path),
        "TRUST_REPAIR_E2E_TRUSTC must point at a stage2 compiler path, got {}",
        path.display()
    );
    Some(path)
}

fn required_report_dir() -> PathBuf {
    let value = std::env::var_os("TRUST_REPAIR_E2E_REPORT_DIR")
        .expect("TRUST_REPAIR_E2E_REPORT_DIR must be set when TRUST_REPAIR_E2E_TRUSTC is set");
    assert!(
        !value.is_empty(),
        "TRUST_REPAIR_E2E_REPORT_DIR must not be empty when TRUST_REPAIR_E2E_TRUSTC is set"
    );
    let raw = PathBuf::from(value);
    if raw.is_absolute() { raw } else { repo_root().join(raw) }
}

fn repo_root() -> PathBuf {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest.parent().and_then(|path| path.parent()).map(Path::to_path_buf).unwrap_or(manifest)
}

fn is_stage2_path(path: &Path) -> bool {
    path_has_component(path, "stage2")
        || fs::canonicalize(path).is_ok_and(|resolved| path_has_component(&resolved, "stage2"))
}

fn path_has_component(path: &Path, needle: &str) -> bool {
    path.components().any(|component| component.as_os_str() == OsStr::new(needle))
}

fn run_trustc_verify(
    trustc: &Path,
    source: &Path,
    work_dir: &Path,
    label: &'static str,
) -> VerifierRun {
    let output_path = work_dir.join(format!("{label}.o"));
    let command_args = [
        "--edition=2021",
        "--crate-type=bin",
        "--crate-name",
        "program_index_divzero_repair_e2e",
        "--color=never",
        "-Z",
        "trust-verify-level=1",
        "-Z",
        "trust-verify-output=json",
        "--emit=obj",
        "-o",
    ];
    let mut command = Command::new(trustc);
    command
        .current_dir(work_dir)
        .env("CARGO_INCREMENTAL", "0")
        .env("CARGO_TERM_COLOR", "never")
        .env("RUST_BACKTRACE", "0")
        .env_remove("TRUST_COMPILER_CACHE")
        .env_remove("TRUST_VERIFY_POLICY")
        .env_remove("RUSTFLAGS")
        .env_remove("RUSTFLAGS_BOOTSTRAP")
        .env_remove("RUSTFLAGS_NOT_BOOTSTRAP")
        .env_remove("CARGO_ENCODED_RUSTFLAGS")
        .args(command_args)
        .arg(&output_path)
        .arg(source);
    apply_runtime_library_path(&mut command, trustc);

    let command_display = render_command(&command);
    let output = command.output().unwrap_or_else(|err| {
        panic!("failed to invoke trustc {label} run: {err}\n{command_display}")
    });
    VerifierRun::from_output(label, command_display, output)
}

fn apply_runtime_library_path(command: &mut Command, trustc: &Path) {
    let Some(path_var) = runtime_library_path_var() else {
        return;
    };
    let paths = runtime_library_paths_for_trustc(trustc);
    if paths.is_empty() {
        return;
    }
    let mut joined = std::env::join_paths(paths).expect("join trustc runtime library paths");
    if let Some(existing) = std::env::var_os(path_var)
        && !existing.is_empty()
    {
        let mut all = std::env::split_paths(&joined).collect::<Vec<_>>();
        all.extend(std::env::split_paths(&existing));
        joined = std::env::join_paths(all).expect("join existing runtime library paths");
    }
    command.env(path_var, joined);
}

fn runtime_library_path_var() -> Option<&'static str> {
    match std::env::consts::OS {
        "macos" => Some("DYLD_LIBRARY_PATH"),
        "linux" => Some("LD_LIBRARY_PATH"),
        _ => None,
    }
}

fn runtime_library_paths_for_trustc(trustc: &Path) -> Vec<PathBuf> {
    let Some(bin_dir) = trustc.parent() else {
        return Vec::new();
    };
    let Some(sysroot) = bin_dir.parent() else {
        return Vec::new();
    };
    let Some(stage_name) = sysroot.file_name() else {
        return Vec::new();
    };
    let Some(build_dir) = sysroot.parent() else {
        return Vec::new();
    };

    let mut paths = Vec::new();
    push_existing_dir(&mut paths, sysroot.join("lib"));

    let rustlib_root = sysroot.join("lib/rustlib");
    if let Ok(entries) = fs::read_dir(&rustlib_root) {
        for entry in entries.flatten() {
            push_existing_dir(&mut paths, entry.path().join("lib"));
        }
    }

    let deps_root = build_dir.join(format!("{}-rustc", stage_name.to_string_lossy()));
    if let Ok(entries) = fs::read_dir(&deps_root) {
        for entry in entries.flatten() {
            push_existing_dir(&mut paths, entry.path().join("release/deps"));
        }
    }

    paths
}

fn push_existing_dir(paths: &mut Vec<PathBuf>, path: PathBuf) {
    if path.is_dir() && !paths.iter().any(|existing| existing == &path) {
        paths.push(path);
    }
}

fn parse_function_results(stderr: &str) -> Vec<TransportFunctionResult> {
    stderr
        .lines()
        .filter_map(|line| {
            let json = line.trim().strip_prefix(TRANSPORT_PREFIX)?;
            let message = serde_json::from_str::<Value>(json)
                .unwrap_or_else(|err| panic!("malformed TRUST_JSON transport line: {err}\n{line}"));
            if message.get("type").and_then(Value::as_str) != Some("function_result") {
                return None;
            }
            Some(parse_function_result_value(&message, line))
        })
        .collect()
}

fn parse_function_result_value(message: &Value, line: &str) -> TransportFunctionResult {
    let function = message
        .get("function")
        .and_then(Value::as_str)
        .unwrap_or_else(|| panic!("TRUST_JSON function_result missing function field\n{line}"))
        .to_string();
    let results = message
        .get("results")
        .and_then(Value::as_array)
        .unwrap_or_else(|| panic!("TRUST_JSON function_result missing results array\n{line}"))
        .iter()
        .map(|result| parse_obligation_result_value(result, line))
        .collect();
    TransportFunctionResult { function, results }
}

fn parse_obligation_result_value(result: &Value, line: &str) -> TransportObligationResult {
    let field = |key: &str| -> String {
        result
            .get(key)
            .and_then(Value::as_str)
            .unwrap_or_else(|| panic!("TRUST_JSON obligation missing string field {key:?}\n{line}"))
            .to_string()
    };
    TransportObligationResult {
        claim_digest_sha256: result
            .get("claim_digest_sha256")
            .and_then(Value::as_str)
            .map(str::to_string),
        kind: field("kind"),
        description: field("description"),
        outcome: field("outcome"),
        counterexample: result.get("counterexample").and_then(Value::as_str).map(str::to_string),
        counterexample_model: result.get("counterexample_model").cloned(),
    }
}

fn aggregate_counts(function_results: &[TransportFunctionResult]) -> ProofCounts {
    let mut counts = ProofCounts::default();
    for function in function_results {
        for result in &function.results {
            counts.add_result(result);
        }
    }
    counts
}

fn divzero_counterexamples(function_results: &[TransportFunctionResult]) -> Vec<String> {
    let mut counterexamples = Vec::new();
    for function in function_results {
        for result in &function.results {
            if !is_divzero_obligation(result) || result.outcome != "failed" {
                continue;
            }
            if let Some(counterexample) =
                result.counterexample.as_ref().filter(|value| !value.trim().is_empty())
            {
                counterexamples.push(format!("{}: {counterexample}", function.function));
            } else if let Some(model) = &result.counterexample_model {
                counterexamples.push(format!("{}: {model}", function.function));
            }
        }
    }
    counterexamples
}

fn is_divzero_obligation(result: &TransportObligationResult) -> bool {
    let kind = result.kind.to_ascii_lowercase();
    let description = result.description.to_ascii_lowercase();
    kind.contains("divzero")
        || kind == "division_by_zero"
        || description.contains("division by zero")
}

fn assert_before_has_real_divzero_failure(before: &VerifierRun) {
    assert!(
        !before.function_results.is_empty(),
        "before run emitted no TRUST_JSON function_result transport\ncommand: {}\nstatus: {:?}\nstdout:\n{}\nstderr:\n{}",
        before.command_display,
        before.exit_code,
        before.stdout,
        before.stderr_tail(),
    );
    assert!(
        before.counts.total > 0,
        "before run had function_result transport but zero obligations\ncommand: {}\nstderr:\n{}",
        before.command_display,
        before.stderr_tail(),
    );
    assert!(
        before.counts.divzero_failed > 0,
        "before run did not report a failed real divzero obligation\ncounts: {:?}\ncommand: {}\nstderr:\n{}",
        before.counts,
        before.command_display,
        before.stderr_tail(),
    );
    assert!(
        !before.divzero_counterexamples.is_empty(),
        "before run reported divzero failure without a counterexample; refusing fake repair evidence\ncounts: {:?}\ncommand: {}\nstderr:\n{}",
        before.counts,
        before.command_display,
        before.stderr_tail(),
    );
}

fn assert_after_improved(before: &VerifierRun, after: &VerifierRun) {
    assert!(
        after.status_success,
        "after repair trustc run failed\ncommand: {}\nstatus: {:?}\nstdout:\n{}\nstderr:\n{}",
        after.command_display,
        after.exit_code,
        after.stdout,
        after.stderr_tail(),
    );
    assert!(
        !after.function_results.is_empty() && after.counts.total > 0,
        "after repair emitted no real verifier obligations\ncommand: {}\nstderr:\n{}",
        after.command_display,
        after.stderr_tail(),
    );
    assert!(
        after.counts.divzero_failed < before.counts.divzero_failed,
        "divzero failed count did not decrease\nbefore: {:?}\nafter: {:?}\nafter stderr:\n{}",
        before.counts,
        after.counts,
        after.stderr_tail(),
    );
    assert!(
        after.counts.divzero_proved > before.counts.divzero_proved,
        "divzero proved count did not increase\nbefore: {:?}\nafter: {:?}\nafter stderr:\n{}",
        before.counts,
        after.counts,
        after.stderr_tail(),
    );
    assert!(
        after.counts.failed < before.counts.failed,
        "total failed proof count did not decrease\nbefore: {:?}\nafter: {:?}",
        before.counts,
        after.counts,
    );
    assert!(
        after.counts.proved > before.counts.proved,
        "total proved proof count did not increase\nbefore: {:?}\nafter: {:?}",
        before.counts,
        after.counts,
    );
}

fn deterministic_divzero_repair(source: &str) -> String {
    let before = "\
fn divide_unchecked(x: u32, y: u32) -> u32 {
    x / y
}

fn main() {
    let _ = divide_unchecked(10, 2);
}
";
    let after = "\
fn divide_unchecked(x: u32, y: u32) -> u32 {
    if y == 0 {
        0
    } else {
        x / y
    }
}

fn main() {
    let _ = divide_unchecked(10, 2);
    let _ = divide_unchecked(10, 0);
}
";
    assert_eq!(
        source.matches(before).count(),
        1,
        "div-zero fixture no longer matches the deterministic repair input"
    );
    source.replacen(before, after, 1)
}

fn full_file_unified_diff(
    before_label: &str,
    after_label: &str,
    before: &str,
    after: &str,
) -> String {
    let before_count = before.lines().count();
    let after_count = after.lines().count();
    let mut diff = format!(
        "--- {before_label}\n+++ {after_label}\n@@ -1,{before_count} +1,{after_count} @@\n"
    );
    for line in before.lines() {
        diff.push('-');
        diff.push_str(line);
        diff.push('\n');
    }
    for line in after.lines() {
        diff.push('+');
        diff.push_str(line);
        diff.push('\n');
    }
    diff
}

fn write_improvement_artifacts(
    report_dir: &Path,
    trustc: &Path,
    fixture: &Path,
    before: &VerifierRun,
    after: &VerifierRun,
) {
    let proved_delta = after.counts.proved as isize - before.counts.proved as isize;
    let failed_delta = after.counts.failed as isize - before.counts.failed as isize;
    let divzero_proved_delta =
        after.counts.divzero_proved as isize - before.counts.divzero_proved as isize;
    let divzero_failed_delta =
        after.counts.divzero_failed as isize - before.counts.divzero_failed as isize;
    let improved = after.counts.failed < before.counts.failed
        && after.counts.proved > before.counts.proved
        && after.counts.divzero_failed < before.counts.divzero_failed
        && after.counts.divzero_proved > before.counts.divzero_proved;

    let report = json!({
        "schema": "trust.repair-e2e.proof-improvement.v1",
        "fixture": fixture.display().to_string(),
        "trustc": trustc.display().to_string(),
        "before": run_json(before),
        "after": run_json(after),
        "improvement": {
            "proved_delta": proved_delta,
            "failed_delta": failed_delta,
            "divzero_proved_delta": divzero_proved_delta,
            "divzero_failed_delta": divzero_failed_delta,
            "improved": improved,
        },
        "artifacts": {
            "before_stderr": BEFORE_STDERR,
            "after_stderr": AFTER_STDERR,
            "repaired_source": REPAIRED_RS,
            "patch_diff": PATCH_DIFF,
            "markdown": IMPROVEMENT_MD,
        },
        "claim": "real stage2 trustc transport only; no fake verifier results",
    });
    let json_text = serde_json::to_string_pretty(&report).expect("serialize improvement report");
    fs::write(report_dir.join(IMPROVEMENT_JSON), json_text).expect("archive improvement json");

    let markdown = format!(
        "# Program-index div-zero repair evidence\n\n\
         Fixture: `{}`\n\n\
         Compiler: `{}`\n\n\
         Before: {} proved, {} failed, {} unknown, {} runtime_checked, {} total; \
         divzero {} proved / {} failed.\n\n\
         After: {} proved, {} failed, {} unknown, {} runtime_checked, {} total; \
         divzero {} proved / {} failed.\n\n\
         Improvement: proved_delta={}, failed_delta={}, divzero_proved_delta={}, \
         divzero_failed_delta={}, improved={}.\n\n\
         Counterexample evidence before repair:\n\n{}\n",
        fixture.display(),
        trustc.display(),
        before.counts.proved,
        before.counts.failed,
        before.counts.unknown,
        before.counts.runtime_checked,
        before.counts.total,
        before.counts.divzero_proved,
        before.counts.divzero_failed,
        after.counts.proved,
        after.counts.failed,
        after.counts.unknown,
        after.counts.runtime_checked,
        after.counts.total,
        after.counts.divzero_proved,
        after.counts.divzero_failed,
        proved_delta,
        failed_delta,
        divzero_proved_delta,
        divzero_failed_delta,
        improved,
        before
            .divzero_counterexamples
            .iter()
            .map(|counterexample| format!("- `{counterexample}`"))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    fs::write(report_dir.join(IMPROVEMENT_MD), markdown).expect("archive improvement markdown");
}

fn run_json(run: &VerifierRun) -> serde_json::Value {
    json!({
        "label": run.label,
        "command": run.command_display,
        "status_success": run.status_success,
        "exit_code": run.exit_code,
        "function_results": run.function_results.len(),
        "counts": {
            "proved": run.counts.proved,
            "failed": run.counts.failed,
            "unknown": run.counts.unknown,
            "runtime_checked": run.counts.runtime_checked,
            "total": run.counts.total,
            "divzero_proved": run.counts.divzero_proved,
            "divzero_failed": run.counts.divzero_failed,
            "divzero_unknown": run.counts.divzero_unknown,
            "divzero_runtime_checked": run.counts.divzero_runtime_checked,
        },
        "divzero_counterexamples": run.divzero_counterexamples,
    })
}

fn render_command(command: &Command) -> String {
    let mut parts = Vec::new();
    if let Some(current_dir) = command.get_current_dir() {
        parts.push("cd".to_string());
        parts.push(shell_quote(current_dir.as_os_str()));
        parts.push("&&".to_string());
    }
    for (key, value) in command.get_envs() {
        if let Some(value) = value {
            parts.push(format!("{}={}", key.to_string_lossy(), shell_quote(value)));
        }
    }
    parts.push(shell_quote(command.get_program()));
    parts.extend(command.get_args().map(shell_quote));
    parts.join(" ")
}

fn shell_quote(value: &OsStr) -> String {
    let value = value.to_string_lossy();
    if value
        .chars()
        .all(|c| c.is_ascii_alphanumeric() || matches!(c, '/' | '.' | '_' | '-' | ':' | '=' | '+'))
    {
        value.into_owned()
    } else {
        format!("'{}'", value.replace('\'', "'\\''"))
    }
}

fn tail_excerpt(text: &str, max_bytes: usize) -> String {
    if text.len() <= max_bytes {
        return text.to_string();
    }
    let mut start = text.len() - max_bytes;
    while !text.is_char_boundary(start) {
        start += 1;
    }
    format!("...{}", &text[start..])
}
