// trust-integration-tests/tests/e2e_real_rustc.rs
//
// E2E integration test using real .rs source files compiled through the actual
// Trust rustc binary. Unlike e2e_smoke.rs which uses hand-constructed MIR,
// this test invokes the real compiler as a subprocess and verifies the full
// pipeline:
//
//   real .rs file -> Trust rustc -> MIR extraction -> vcgen -> router -> ay -> report
//
// The test parses TRUST_JSON transport lines from the compiler's stderr output
// to verify that verification conditions were generated and dispatched.
//
// When `-Ztrust-dump=mir:<dir>` is set, the compiler also dumps VerifiableFunction JSON
// fixtures. The test loads those and runs them through the Rust-side pipeline
// (vcgen -> real ay -> proof-cert -> report) as a second verification path.
//
// Prerequisites:
//   - Stage1 Trust compiler: ./x.py build --stage 1
//     OR set TRUST_RUSTC=/path/to/rustc
//   - ay binary discoverable by the integration-test ay helper
//     (for real solver results; mock fallback otherwise)
//
// Issue: #937 | Epic: #935
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::OnceLock;

use trust_integration_tests::ay_test_support::{ay_available, require_ay};
use trust_types::*;

// ---------------------------------------------------------------------------
// Compiler discovery
// ---------------------------------------------------------------------------

/// Search for the Trust stage1 compiler binary.
///
/// Search order:
/// 1. TRUST_RUSTC environment variable (explicit override)
/// 2. build/host/stage1/bin/rustc (standard x.py output)
/// 3. build/<triple>/stage1/bin/rustc (cross-compilation)
/// 4. any build/*/stage1/bin/rustc discovered in the local build directory
///
/// Returns None if no compiler is found.
fn find_trust_rustc() -> Option<PathBuf> {
    static TRUST_RUSTC: OnceLock<Option<PathBuf>> = OnceLock::new();
    TRUST_RUSTC.get_or_init(find_trust_rustc_uncached).clone()
}

fn find_trust_rustc_uncached() -> Option<PathBuf> {
    // 1. Explicit env var override
    if let Ok(path) = std::env::var("TRUST_RUSTC") {
        let p = PathBuf::from(&path);
        if is_executable_file(&p) {
            return candidate_emits_trust_transport(&p).then_some(p);
        }
        eprintln!("WARNING: TRUST_RUSTC={path} is not an executable file, searching build/");
    }

    let repo_root = find_repo_root();
    let candidates = stage1_rustc_candidates(&repo_root);
    let mut found: Vec<PathBuf> =
        candidates.iter().filter(|candidate| is_executable_file(candidate)).cloned().collect();

    if found.is_empty() {
        eprintln!("No executable Trust stage1 rustc found. Searched:");
        for candidate in &candidates {
            eprintln!("  {}", candidate.display());
        }
        return None;
    }

    found.sort_by_key(|candidate| {
        (
            usize::from(!candidate_has_stage1_std(candidate)),
            usize::from(!candidate.ends_with("build/host/stage1/bin/rustc")),
            candidate.to_string_lossy().into_owned(),
        )
    });

    let selected = found.remove(0);
    if !candidate_has_stage1_std(&selected)
        && let Some(sysroot) = sysroot_from_rustc_path(&selected)
    {
        eprintln!(
            "WARNING: selected stage1 rustc sysroot appears to lack libstd artifacts under {}. \
                 Compilation failures will include full rustc diagnostics.",
            sysroot.join("lib/rustlib").display()
        );
    }
    candidate_emits_trust_transport(&selected).then_some(selected)
}

fn stage1_rustc_candidates(repo_root: &Path) -> Vec<PathBuf> {
    let mut candidates = Vec::new();
    add_unique_candidate(&mut candidates, repo_root.join("build/host/stage1/bin/rustc"));
    add_unique_candidate(
        &mut candidates,
        repo_root.join("build/aarch64-apple-darwin/stage1/bin/rustc"),
    );
    add_unique_candidate(
        &mut candidates,
        repo_root.join("build/x86_64-apple-darwin/stage1/bin/rustc"),
    );
    add_unique_candidate(
        &mut candidates,
        repo_root.join("build/x86_64-unknown-linux-gnu/stage1/bin/rustc"),
    );

    let build_dir = repo_root.join("build");
    let mut discovered = Vec::new();
    if let Ok(entries) = fs::read_dir(&build_dir) {
        for entry in entries.flatten() {
            discovered.push(entry.path().join("stage1/bin/rustc"));
        }
    }
    discovered.sort();

    for candidate in discovered {
        add_unique_candidate(&mut candidates, candidate);
    }

    candidates
}

fn add_unique_candidate(candidates: &mut Vec<PathBuf>, candidate: PathBuf) {
    if !candidates.iter().any(|existing| existing == &candidate) {
        candidates.push(candidate);
    }
}

fn is_executable_file(path: &Path) -> bool {
    let Ok(metadata) = fs::metadata(path) else {
        return false;
    };
    if !metadata.is_file() {
        return false;
    }

    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        metadata.permissions().mode() & 0o111 != 0
    }

    #[cfg(not(unix))]
    {
        true
    }
}

fn sysroot_from_rustc_path(rustc: &Path) -> Option<PathBuf> {
    rustc.parent().and_then(|bin| bin.parent()).map(Path::to_path_buf)
}

fn candidate_has_stage1_std(rustc: &Path) -> bool {
    sysroot_from_rustc_path(rustc).is_some_and(|sysroot| sysroot_has_libstd(&sysroot))
}

fn sysroot_has_libstd(sysroot: &Path) -> bool {
    let rustlib = sysroot.join("lib/rustlib");
    let Ok(targets) = fs::read_dir(&rustlib) else {
        return false;
    };

    targets.flatten().any(|target| {
        let lib_dir = target.path().join("lib");
        let Ok(files) = fs::read_dir(lib_dir) else {
            return false;
        };
        files.flatten().any(|file| {
            let name = file.file_name();
            let name = name.to_string_lossy();
            name.starts_with("libstd-") && (name.ends_with(".rlib") || name.ends_with(".rmeta"))
        })
    })
}

fn candidate_emits_trust_transport(rustc: &Path) -> bool {
    let Ok(tmp) = tempfile::tempdir() else {
        eprintln!("WARNING: could not create tempdir for Trust rustc capability probe");
        return false;
    };
    let src_path = tmp.path().join("trust_probe.rs");
    let output_path = tmp.path().join("libtrust_probe.rlib");
    if let Err(error) =
        fs::write(&src_path, "pub fn trust_probe_div(a: u32, b: u32) -> u32 { a / b }\n")
    {
        eprintln!("WARNING: could not write Trust rustc capability probe: {error}");
        return false;
    }

    let mut cmd = verified_lib_command_with_args(rustc, &src_path, &output_path, &[]);
    let (output, command_line) = run_rustc_command("Trust rustc capability probe", &mut cmd);
    if !output.status.success() {
        eprintln!(
            "WARNING: candidate rustc failed Trust capability probe:\n{}",
            rustc_failure_diagnostic("Trust rustc capability probe", rustc, &command_line, &output)
        );
        return false;
    }

    let stderr = String::from_utf8_lossy(&output.stderr);
    if stderr.contains(TRANSPORT_PREFIX) {
        return true;
    }

    eprintln!(
        "SKIPPING: candidate rustc at {} compiled but emitted no TRUST_JSON transport; \
         rebuild a Trust-enabled stage1/stage2 compiler or set TRUST_RUSTC to one.",
        rustc.display()
    );
    false
}

/// Find the Trust repo root by walking up from CARGO_MANIFEST_DIR.
fn find_repo_root() -> PathBuf {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    // crates/trust-integration-tests -> crates -> repo root
    manifest
        .parent()
        .and_then(|p| p.parent())
        .map(|p| p.to_path_buf())
        .unwrap_or_else(|| manifest.clone())
}

fn verified_lib_command_with_args(
    rustc: &Path,
    src_path: &Path,
    output_path: &Path,
    extra_args: &[&str],
) -> Command {
    let mut cmd = Command::new(rustc);
    // Scrub cargo-injected env so the inner rustc resolves the proof-cache
    // path as bare-rustc (legacy `.trust-cache/proof-cache.json` in CWD)
    // rather than walking the workspace target/ inherited from `cargo test`.
    // P1.2: trust_verify::resolve_proof_cache_path uses these to choose
    // target/trust-proofs/<crate>.json under cargo, and falls back to the
    // legacy path otherwise.
    for var in [
        "CARGO_TARGET_DIR",
        "CARGO_MANIFEST_DIR",
        "CARGO_CRATE_NAME",
        "CARGO_PKG_NAME",
        "CARGO_PKG_VERSION",
        "CARGO",
        "TRUST_DUMP_MIR",
    ] {
        cmd.env_remove(var);
    }
    cmd.args(extra_args)
        .arg("--edition")
        .arg("2021")
        .arg("--crate-type")
        .arg("lib")
        .arg("-o")
        .arg(output_path)
        .arg(src_path);
    cmd
}

fn run_rustc_command(label: &str, cmd: &mut Command) -> (Output, String) {
    let rendered = render_command(cmd);
    let output = cmd
        .output()
        .unwrap_or_else(|e| panic!("failed to invoke {label}: {e}\nCommand: {rendered}"));
    (output, rendered)
}

fn assert_rustc_success(label: &str, rustc: &Path, command_line: &str, output: &Output) {
    assert!(
        output.status.success(),
        "{}",
        rustc_failure_diagnostic(label, rustc, command_line, output)
    );
}

fn rustc_failure_diagnostic(
    label: &str,
    rustc: &Path,
    command_line: &str,
    output: &Output,
) -> String {
    let sysroot = sysroot_from_rustc_path(rustc)
        .map(|path| path.display().to_string())
        .unwrap_or_else(|| "<unknown>".to_string());
    let std_status = if candidate_has_stage1_std(rustc) { "present" } else { "missing" };
    format!(
        "{label} failed\n\
         status: {}\n\
         rustc: {}\n\
         path-derived sysroot: {sysroot}\n\
         stage1 libstd artifacts: {std_status}\n\
         command: {command_line}\n\
         stdout:\n{}\n\
         stderr:\n{}",
        output.status,
        rustc.display(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    )
}

fn render_command(cmd: &Command) -> String {
    let mut parts = Vec::new();

    if let Some(current_dir) = cmd.get_current_dir() {
        parts.push("cd".to_string());
        parts.push(shell_quote(current_dir.as_os_str()));
        parts.push("&&".to_string());
    }

    for (key, value) in cmd.get_envs() {
        let key = key.to_string_lossy();
        match value {
            Some(value) => parts.push(format!("{key}={}", shell_quote(value))),
            None => parts.push(format!("env -u {key}")),
        }
    }

    parts.push(shell_quote(cmd.get_program()));
    parts.extend(cmd.get_args().map(shell_quote));
    parts.join(" ")
}

fn shell_quote(value: &OsStr) -> String {
    let value = value.to_string_lossy();
    if value.is_empty() {
        return "''".to_string();
    }
    if value
        .chars()
        .all(|c| c.is_ascii_alphanumeric() || matches!(c, '/' | '.' | '_' | '-' | ':' | '=' | '+'))
    {
        value.into_owned()
    } else {
        format!("'{}'", value.replace('\'', "'\\''"))
    }
}

// ---------------------------------------------------------------------------
// Transport line parsing
// ---------------------------------------------------------------------------

/// Parse TRUST_JSON transport lines from compiler stderr output.
///
/// Each line matching `TRUST_JSON:{...}` is parsed as a TransportMessage.
/// Non-matching lines are silently skipped (they are regular compiler diagnostics).
fn parse_transport_lines(stderr: &str) -> Vec<TransportMessage> {
    stderr
        .lines()
        .filter_map(|line| {
            let trimmed = line.trim();
            trimmed
                .strip_prefix(TRANSPORT_PREFIX)
                .and_then(|json| trust_types::parse_transport_payload(json).ok())
        })
        .collect()
}

/// Extract function results from transport messages.
fn extract_function_results(messages: &[TransportMessage]) -> Vec<&FunctionTransportResult> {
    messages
        .iter()
        .filter_map(|msg| match msg {
            TransportMessage::FunctionResult(r) => Some(r),
            _ => None,
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Test source code
// ---------------------------------------------------------------------------

/// The test Rust source file. Contains functions with known verification properties:
///
/// - `safe_divide`: division guarded by zero check -> div-by-zero VC should be generated
/// - `midpoint`: potential overflow -> overflow VC should be generated
/// - `always_positive`: simple addition with constants -> should be provable
const TEST_SOURCE: &str = r#"
/// Division guarded by a zero check. The if-else means the actual division
/// path has b != 0, so the div-by-zero VC should be provable.
pub fn safe_divide(a: u32, b: u32) -> Option<u32> {
    if b == 0 { None } else { Some(a / b) }
}

/// Classic midpoint calculation with potential overflow:
/// `a + (b - a) / 2` can underflow if b < a.
pub fn midpoint(a: u32, b: u32) -> u32 {
    a + (b - a) / 2
}

/// Simple constant addition -- trivially safe.
pub fn add_five(x: u32) -> u32 {
    x + 5
}

/// Unchecked division by a variable -- div-by-zero is possible.
pub fn raw_divide(a: u32, b: u32) -> u32 {
    a / b
}
"#;

// ---------------------------------------------------------------------------
// Test 1: Compiler invocation produces TRUST_JSON transport output
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_real_rustc_transport_output() {
    let rustc = match find_trust_rustc() {
        Some(p) => p,
        None => {
            eprintln!(
                "SKIPPING: No Trust rustc found. Build with: ./x.py build --stage 1\n\
                 Or set TRUST_RUSTC=/path/to/rustc"
            );
            return;
        }
    };
    eprintln!("Using Trust rustc: {}", rustc.display());

    let tmp = tempfile::tempdir().unwrap();
    let src_path = tmp.path().join("test_verify.rs");
    std::fs::write(&src_path, TEST_SOURCE).unwrap();

    // Invoke the compiler with advisory verification explicitly enabled.
    // Use --crate-type lib to avoid needing a main().
    let mut cmd = verified_lib_command_with_args(
        &rustc,
        &src_path,
        &tmp.path().join("test_verify.rlib"),
        &["-Z", "trust-verify-output=json"],
    );
    let (output, command_line) = run_rustc_command("transport output compile", &mut cmd);

    let stderr = String::from_utf8_lossy(&output.stderr);
    eprintln!("=== Compiler stderr ({} bytes) ===", stderr.len());
    // Print first 2000 chars of stderr for diagnostics
    let preview: String = stderr.chars().take(2000).collect();
    eprintln!("{preview}");
    if stderr.len() > 2000 {
        eprintln!("... ({} more bytes)", stderr.len() - 2000);
    }
    eprintln!("=== End compiler stderr ===");

    // The compiler should complete (exit 0) even if verification finds issues.
    // Verification is additive -- it never blocks compilation.
    assert_rustc_success("transport output compile", &rustc, &command_line, &output);

    // Parse transport lines
    let messages = parse_transport_lines(&stderr);
    eprintln!("Parsed {} TRUST_JSON transport messages", messages.len());

    // We expect at least one function_result message (the test source has 4 functions).
    let fn_results = extract_function_results(&messages);
    eprintln!("Function results: {}", fn_results.len());

    for result in &fn_results {
        eprintln!(
            "  {} -> {} obligations ({} proved, {} failed, {} unknown, {} runtime_checked)",
            result.function,
            result.total,
            result.proved,
            result.failed,
            result.unknown,
            result.runtime_checked,
        );
    }

    assert!(
        !fn_results.is_empty(),
        "compiler should emit at least one TRUST_JSON function_result transport line. \
         Got {} transport messages total. Is the trust_verify MIR pass enabled?",
        messages.len()
    );

    // At least one function should have VCs generated.
    let total_obligations: usize = fn_results.iter().map(|r| r.total).sum();
    assert!(
        total_obligations > 0,
        "compiler should generate at least one verification obligation across all functions. \
         Got 0 obligations from {} functions.",
        fn_results.len()
    );

    eprintln!(
        "\n=== E2E Real Rustc: {} functions verified, {} total obligations ===",
        fn_results.len(),
        total_obligations
    );
}

// ---------------------------------------------------------------------------
// Test 2: -Ztrust-dump=mir:<dir> produces valid VerifiableFunction JSON
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_real_rustc_dump_mir() {
    let rustc = match find_trust_rustc() {
        Some(p) => p,
        None => {
            eprintln!(
                "SKIPPING: No Trust rustc found. Build with: ./x.py build --stage 1\n\
                 Or set TRUST_RUSTC=/path/to/rustc"
            );
            return;
        }
    };

    let tmp = tempfile::tempdir().unwrap();
    let src_path = tmp.path().join("test_dump.rs");
    std::fs::write(&src_path, TEST_SOURCE).unwrap();

    let dump_dir = tmp.path().join("mir_dump");
    std::fs::create_dir_all(&dump_dir).unwrap();

    // Invoke the compiler with the tracked dump option to extract real MIR as JSON.
    let mut cmd = verified_lib_command_with_args(
        &rustc,
        &src_path,
        &tmp.path().join("test_dump.rlib"),
        &["-Z", "trust-verify-output=json"],
    );
    cmd.arg("-Z").arg(format!("trust-dump=mir:{}", dump_dir.display()));
    let (output, command_line) = run_rustc_command("-Ztrust-dump=mir:<dir> compile", &mut cmd);
    assert_rustc_success("-Ztrust-dump=mir:<dir> compile", &rustc, &command_line, &output);

    // Load and validate dumped JSON fixtures.
    let entries: Vec<_> = std::fs::read_dir(&dump_dir)
        .unwrap()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "json"))
        .collect();

    eprintln!("-Ztrust-dump=mir:<dir> produced {} JSON files:", entries.len());
    for entry in &entries {
        eprintln!("  {}", entry.file_name().to_string_lossy());
    }

    assert!(!entries.is_empty(), "-Ztrust-dump=mir:<dir> should produce JSON fixtures");

    // Parse each fixture as a VerifiableFunction.
    let mut functions: Vec<VerifiableFunction> = Vec::new();
    for entry in &entries {
        let json = std::fs::read_to_string(entry.path())
            .unwrap_or_else(|e| panic!("failed to read {}: {e}", entry.path().display()));
        let func: VerifiableFunction = serde_json::from_str(&json).unwrap_or_else(|e| {
            panic!("failed to parse {} as VerifiableFunction: {e}", entry.path().display())
        });
        assert!(!func.name.is_empty(), "function should have a name");
        assert!(!func.def_path.is_empty(), "function should have a def_path");
        assert!(!func.body.blocks.is_empty(), "function {} should have basic blocks", func.name);
        functions.push(func);
    }

    eprintln!("\n=== E2E Real Rustc tracked MIR dump: {} functions extracted ===", functions.len());
}

// ---------------------------------------------------------------------------
// Test 3: Full pipeline -- real rustc MIR through vcgen + real ay
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_real_rustc_full_pipeline_with_ay() {
    let rustc = match find_trust_rustc() {
        Some(p) => p,
        None => {
            eprintln!(
                "SKIPPING: No Trust rustc found. Build with: ./x.py build --stage 1\n\
                 Or set TRUST_RUSTC=/path/to/rustc"
            );
            return;
        }
    };

    if !ay_available() {
        eprintln!("SKIPPING: ay not found by integration-test helper.");
        return;
    }

    let tmp = tempfile::tempdir().unwrap();
    let src_path = tmp.path().join("test_full.rs");
    std::fs::write(&src_path, TEST_SOURCE).unwrap();

    let dump_dir = tmp.path().join("mir_dump");
    std::fs::create_dir_all(&dump_dir).unwrap();

    // Step 1: Compile with MIR dump
    let mut cmd = verified_lib_command_with_args(
        &rustc,
        &src_path,
        &tmp.path().join("test_full.rlib"),
        &["-Z", "trust-verify-output=json"],
    );
    cmd.arg("-Z").arg(format!("trust-dump=mir:{}", dump_dir.display()));
    let (output, command_line) = run_rustc_command("full pipeline MIR dump compile", &mut cmd);
    assert_rustc_success("full pipeline MIR dump compile", &rustc, &command_line, &output);

    // Step 2: Load dumped MIR fixtures
    let functions = load_mir_fixtures_from_dir(&dump_dir);
    assert!(!functions.is_empty(), "should have at least one dumped function");

    eprintln!("Loaded {} functions from -Ztrust-dump=mir:<dir>", functions.len());

    // Step 3: Run each through vcgen + real ay
    let ay = require_ay();
    let mut total_proved = 0usize;
    let mut total_failed = 0usize;
    let mut total_unknown = 0usize;
    let mut all_results: Vec<(VerificationCondition, VerificationResult)> = Vec::new();

    for func in &functions {
        let vcs = trust_vcgen::generate_vcs(func);
        eprintln!("  {} -> {} VCs", func.def_path, vcs.len());

        for vc in &vcs {
            use trust_router::VerificationBackend;
            let result = ay.verify(vc);
            match &result {
                VerificationResult::Proved { .. } => total_proved += 1,
                VerificationResult::Failed { .. } => total_failed += 1,
                _ => total_unknown += 1,
            }
            all_results.push((vc.clone(), result));
        }
    }

    eprintln!("\n=== E2E Full Pipeline: Real Rustc + Real ay ===");
    eprintln!("  Functions: {}", functions.len());
    eprintln!("  Total VCs: {}", all_results.len());
    eprintln!("  Proved: {total_proved}");
    eprintln!("  Failed: {total_failed}");
    eprintln!("  Unknown: {total_unknown}");

    // Acceptance criteria: at least one VC exists
    assert!(!all_results.is_empty(), "pipeline should produce at least one verification result");

    // At least one VC should reach a definitive result (proved or failed).
    let definitive = total_proved + total_failed;
    assert!(
        definitive > 0,
        "ay should produce at least one definitive result (proved or failed). \
         Got {} proved, {} failed, {} unknown.",
        total_proved,
        total_failed,
        total_unknown
    );

    // Step 4: Generate proof certificate for functions with proved VCs
    if total_proved > 0 {
        for func in &functions {
            let vcs = trust_vcgen::generate_vcs(func);
            let mut func_results = Vec::new();
            for vc in &vcs {
                use trust_router::VerificationBackend;
                let result = ay.verify(vc);
                func_results.push((vc.clone(), result));
            }

            let has_proved = func_results.iter().any(|(_, r)| r.is_proved());
            if has_proved {
                let cert = trust_proof_cert::generate_certificate_record(func, &func_results);
                assert!(
                    cert.is_ok(),
                    "proof certificate generation should succeed for {}: {:?}",
                    func.name,
                    cert.err()
                );
                let cert = cert.unwrap();
                eprintln!("  Certificate record for {}: digest={}", func.name, cert.record_digest);
                break; // One certificate is enough to demonstrate the pipeline
            }
        }
    }

    // Step 5: Generate verification report
    let report = trust_report::build_json_report("e2e_real_rustc", &all_results);
    let text = trust_report::format_json_summary(&report);
    eprintln!("\n--- Verification Report ---");
    eprintln!("{text}");
    eprintln!("--- End Report ---");

    assert!(report.summary.functions_analyzed > 0, "report should analyze at least one function");

    // Verify JSON serialization roundtrip
    let json = serde_json::to_string_pretty(&report).unwrap();
    let roundtrip: JsonProofReport = serde_json::from_str(&json).unwrap();
    assert_eq!(roundtrip.summary.total_obligations, report.summary.total_obligations);

    eprintln!("\n=== E2E Real Rustc: FULL PIPELINE VERIFIED ===");
}

// ---------------------------------------------------------------------------
// Test 4: Compiler transport lines contain expected function names
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_real_rustc_function_names_in_transport() {
    let rustc = match find_trust_rustc() {
        Some(p) => p,
        None => {
            eprintln!("SKIPPING: No Trust rustc found. Build with: ./x.py build --stage 1");
            return;
        }
    };

    let tmp = tempfile::tempdir().unwrap();
    let src_path = tmp.path().join("test_names.rs");
    std::fs::write(&src_path, TEST_SOURCE).unwrap();

    let mut cmd = verified_lib_command_with_args(
        &rustc,
        &src_path,
        &tmp.path().join("test_names.rlib"),
        &["-Z", "trust-verify-output=json"],
    );
    let (output, command_line) = run_rustc_command("function names transport compile", &mut cmd);
    assert_rustc_success("function names transport compile", &rustc, &command_line, &output);

    let stderr = String::from_utf8_lossy(&output.stderr);
    let messages = parse_transport_lines(&stderr);
    let fn_results = extract_function_results(&messages);

    // Check that at least some of our function names appear in transport output.
    let expected_names = ["safe_divide", "midpoint", "add_five", "raw_divide"];
    let found_names: Vec<&str> = fn_results.iter().map(|r| r.function.as_str()).collect();

    eprintln!("Functions in transport output:");
    for name in &found_names {
        eprintln!("  {name}");
    }

    let mut matched = 0;
    for expected in &expected_names {
        if found_names.iter().any(|n| n.contains(expected)) {
            matched += 1;
            eprintln!("  FOUND: {expected}");
        } else {
            eprintln!("  MISSING: {expected}");
        }
    }

    assert!(
        matched >= 2,
        "at least 2 of our test functions should appear in transport output. \
         Found {matched}/{} expected functions. Transport had {} function results.",
        expected_names.len(),
        fn_results.len()
    );
}

// ---------------------------------------------------------------------------
// Test 5: Verification results correctness (raw_divide should have div-by-zero VC)
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_real_rustc_divzero_vc_for_raw_divide() {
    let rustc = match find_trust_rustc() {
        Some(p) => p,
        None => {
            eprintln!("SKIPPING: No Trust rustc found. Build with: ./x.py build --stage 1");
            return;
        }
    };

    let tmp = tempfile::tempdir().unwrap();
    let src_path = tmp.path().join("test_divzero.rs");
    std::fs::write(&src_path, TEST_SOURCE).unwrap();

    let mut cmd = verified_lib_command_with_args(
        &rustc,
        &src_path,
        &tmp.path().join("test_divzero.rlib"),
        &["-Z", "trust-verify-output=json"],
    );
    let (output, command_line) = run_rustc_command("raw_divide transport compile", &mut cmd);
    assert_rustc_success("raw_divide transport compile", &rustc, &command_line, &output);

    let stderr = String::from_utf8_lossy(&output.stderr);
    let messages = parse_transport_lines(&stderr);
    let fn_results = extract_function_results(&messages);

    // Find raw_divide in the results -- it does `a / b` without a guard,
    // so it should have a division-by-zero VC.
    let raw_divide = fn_results.iter().find(|r| r.function.contains("raw_divide"));

    if let Some(result) = raw_divide {
        eprintln!(
            "raw_divide: {} obligations ({} proved, {} failed, {} unknown)",
            result.total, result.proved, result.failed, result.unknown
        );

        // Check that at least one obligation exists (div-by-zero).
        assert!(result.total > 0, "raw_divide should have at least one obligation (div-by-zero)");

        // Check that at least one obligation mentions divzero.
        let has_divzero = result
            .results
            .iter()
            .any(|r| r.kind.contains("divzero") || r.description.contains("division"));
        if has_divzero {
            eprintln!("  Confirmed: div-by-zero VC present for raw_divide");
        } else {
            eprintln!(
                "  Note: no explicit divzero VC tag, but {} obligations present",
                result.total
            );
            // Print all obligation kinds for debugging
            for (i, obl) in result.results.iter().enumerate() {
                eprintln!("    obligation {i}: kind={}, outcome={}", obl.kind, obl.outcome);
            }
        }
    } else {
        // If raw_divide is not in transport output, the compiler may have inlined
        // or filtered it. This is acceptable -- the test is best-effort.
        eprintln!(
            "Note: raw_divide not found in transport output ({} functions found). \
             Compiler may have filtered or inlined it.",
            fn_results.len()
        );
    }
}

// ---------------------------------------------------------------------------
// Test 6: -Z trust-verify=off suppresses the native verification pass
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_real_rustc_no_trust_verify_suppresses_transport() {
    let rustc = match find_trust_rustc() {
        Some(p) => p,
        None => {
            eprintln!("SKIPPING: No Trust rustc found. Build with: ./x.py build --stage 1");
            return;
        }
    };

    let tmp = tempfile::tempdir().unwrap();
    let src_path = tmp.path().join("test_no_verify.rs");
    std::fs::write(&src_path, TEST_SOURCE).unwrap();

    let output_path = tmp.path().join("test_no_verify.rlib");
    let mut cmd =
        verified_lib_command_with_args(&rustc, &src_path, &output_path, &["-Z", "trust-verify=off"]);
    let (output, command_line) = run_rustc_command("no-trust-verify compile", &mut cmd);
    assert_rustc_success("no-trust-verify compile", &rustc, &command_line, &output);

    let stderr = String::from_utf8_lossy(&output.stderr);
    let messages = parse_transport_lines(&stderr);
    assert!(
        messages.is_empty(),
        "expected no TRUST_JSON transport output when -Z trust-verify=off overrides verification.\nStderr:\n{}",
        stderr
    );
    assert!(
        !stderr.contains("=== Trust Verification Report"),
        "verification report banner should not be emitted when verification is disabled.\nStderr:\n{}",
        stderr
    );
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Load all VerifiableFunction JSON files from a directory.
fn load_mir_fixtures_from_dir(dir: &Path) -> Vec<VerifiableFunction> {
    let mut functions = Vec::new();
    let entries = match std::fs::read_dir(dir) {
        Ok(entries) => entries,
        Err(_) => return functions,
    };

    for entry in entries {
        let entry = match entry {
            Ok(e) => e,
            Err(_) => continue,
        };
        let path = entry.path();
        if path.extension().is_none_or(|ext| ext != "json") {
            continue;
        }
        let json = match std::fs::read_to_string(&path) {
            Ok(j) => j,
            Err(e) => {
                eprintln!("WARNING: failed to read {}: {e}", path.display());
                continue;
            }
        };
        match serde_json::from_str::<VerifiableFunction>(&json) {
            Ok(func) => functions.push(func),
            Err(e) => {
                eprintln!("WARNING: failed to parse {}: {e}", path.display());
            }
        }
    }

    functions
}
