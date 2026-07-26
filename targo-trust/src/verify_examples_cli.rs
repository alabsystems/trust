// Rust-owned verifier example corpus regression diagnostics.

use std::fs::File;
use std::io::{self, Read};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, ExitStatus};
use std::time::Duration;
use std::{env, fs};

use sha2::{Digest, Sha256};

use crate::stage2_tools::{
    discover_unique_repo_stage2_tool, host_executable_name, validate_repo_stage2_tool,
};
use crate::{bounded_process, durable_io};

const USAGE: &str = "\
Usage: targo trust verify examples [options]

Options:
  --repo-root <path>    Trust checkout root (default: discovered checkout)
  --metadata-only       Check Expected headers without invoking trustc (diagnostic only)
  --allow-l0-gaps       Development opt-out: run raw warning mode instead of fail-closed verification
  --allow-stage1-developer
                        Permit stage1 trustc for a developer-only diagnostic
  --trustc <path>       Repo-local stage2 trustc to use for the live diagnostic
  --example <path>      Check one example; may be repeated
  --out-dir <path>      Compiler output directory (default: target/verify-example-check)
  --json                Emit a machine-readable report
  --json-output <path>  Write a machine-readable report to a durable path
  -h, --help            Show this help
";

const STATUS_WORDS: &[&str] =
    &["PROVED", "FAILED", "RUNTIME-CHECKED", "UNKNOWN", "TIMEOUT", "ABSENT"];

#[derive(Debug, Clone)]
struct Args {
    repo_root: Option<PathBuf>,
    metadata_only: bool,
    allow_l0_gaps: bool,
    allow_stage1_developer: bool,
    json: bool,
    json_output: Option<PathBuf>,
    trustc: Option<PathBuf>,
    examples: Vec<PathBuf>,
    out_dir: Option<PathBuf>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ExpectedMatch {
    kind: String,
    status: String,
    op: Option<String>,
}

#[derive(Debug, Clone)]
struct TrustcIdentity {
    path: PathBuf,
    sha256: String,
}

impl TrustcIdentity {
    fn verify_unchanged(&self) -> Result<(), String> {
        let observed = exact_executable_sha256(&self.path).map_err(|error| {
            format!(
                "could not re-hash exact trustc {} after verifier examples: {error}",
                self.path.display()
            )
        })?;
        if observed != self.sha256 {
            return Err(format!(
                "trustc {} changed during verifier examples (expected SHA-256 {}, observed {})",
                self.path.display(),
                self.sha256,
                observed
            ));
        }
        Ok(())
    }
}

pub(crate) fn run(args: &[String]) -> ExitCode {
    let args = match parse_args(args) {
        Ok(args) => args,
        Err(message) if message == "help" => {
            print!("{USAGE}");
            return ExitCode::SUCCESS;
        }
        Err(message) => {
            eprintln!("targo trust verify examples: {message}");
            eprint!("{USAGE}");
            return ExitCode::from(2);
        }
    };

    let root = match canonicalize_repo_root(&args.repo_root.clone().unwrap_or_else(repo_root)) {
        Ok(root) => root,
        Err(error) => {
            eprintln!("targo trust verify examples: {error}");
            return ExitCode::from(2);
        }
    };
    let examples = if args.examples.is_empty() {
        match discover_verify_examples(&root) {
            Ok(examples) => examples,
            Err(error) => {
                eprintln!("targo trust verify examples: {error}");
                return ExitCode::from(2);
            }
        }
    } else {
        args.examples
            .iter()
            .map(|path| if path.is_absolute() { path.clone() } else { root.join(path) })
            .collect()
    };

    let mut parsed = Vec::new();
    let mut failures = Vec::new();
    for example in examples {
        match example_header_metadata(&example).and_then(|(expected, vc_kind)| {
            let matches = expected_matches(&expected);
            if matches.is_empty() {
                Err(format!(
                    "{}: Expected header did not contain checkable terms",
                    example.display()
                ))
            } else if let Some(vc_kind) = vc_kind {
                let missing = matches
                    .iter()
                    .filter(|expected| !vc_kind_mentions_expected_kind(&vc_kind, expected))
                    .map(expected_terms)
                    .map(|terms| terms.join(" "))
                    .collect::<Vec<_>>();
                if !missing.is_empty() {
                    Err(format!(
                        "{}: Expected header term(s) {:?} are not present in VcKind header `{}`",
                        example.display(),
                        missing,
                        vc_kind
                    ))
                } else {
                    Ok((example, expected, matches))
                }
            } else {
                Ok((example, expected, matches))
            }
        }) {
            Ok(row) => parsed.push(row),
            Err(error) => failures.push(error),
        }
    }

    if args.metadata_only {
        if let Err(error) = emit_report(
            &args,
            &root,
            "metadata-regression-diagnostic",
            parsed.len(),
            &parsed,
            &[],
            &failures,
            0,
            0,
            None,
        ) {
            eprintln!("targo trust verify examples: {error}");
            return ExitCode::from(2);
        }
        if failures.is_empty() {
            return ExitCode::SUCCESS;
        }
        print_failures(&failures);
        return ExitCode::from(1);
    }

    let trustc = match find_trustc(&root, args.trustc.as_deref(), args.allow_stage1_developer) {
        Ok(identity) => identity,
        Err(error) => {
            eprintln!("targo trust verify examples: {error}");
            return ExitCode::from(2);
        }
    };
    let out_dir = args.out_dir.clone().unwrap_or_else(|| root.join("target/verify-example-check"));
    let out_dir = if out_dir.is_absolute() { out_dir } else { root.join(out_dir) };
    if let Err(error) = fs::create_dir_all(&out_dir) {
        eprintln!("targo trust verify examples: failed to create {}: {error}", out_dir.display());
        return ExitCode::from(2);
    }

    let mut trustc_exits = Vec::new();
    let mut trustc_attempts = 0usize;
    let mut trustc_completed_runs = 0usize;
    for (example, expected, matches) in &parsed {
        let session = match fresh_verification_session() {
            Ok(session) => session,
            Err(error) => {
                failures.push(format!(
                    "{}: failed to create a fresh verifier-result correlation session: {error}",
                    example.display()
                ));
                continue;
            }
        };
        trustc_attempts = trustc_attempts.saturating_add(1);
        let (status, output) =
            match run_example(&trustc.path, example, &out_dir, args.allow_l0_gaps, &session) {
                Ok(result) => {
                    trustc_completed_runs = trustc_completed_runs.saturating_add(1);
                    result
                }
                Err(error) => {
                    failures.push(format!("{}: failed to run trustc: {error}", example.display()));
                    continue;
                }
            };
        let Some(status_code) = status.code() else {
            failures.push(format!(
                "{}: trustc terminated by signal while checking header={expected:?}",
                example.display()
            ));
            continue;
        };
        trustc_exits.push((example.clone(), status_code));
        if status_code > 1 {
            failures.push(format!(
                "{}: trustc exited with tool/setup status {status_code}; header={expected:?}",
                example.display()
            ));
            continue;
        }
        if status_code != 0 && matches.iter().all(|row| row.status == "PROVED") {
            failures.push(format!(
                "{}: trustc exited {status_code} for all-PROVED expectation; header={expected:?}",
                example.display()
            ));
        }
        let actual = match session_bound_actual_matches(&output, &session) {
            Ok(actual) => actual,
            Err(error) => {
                failures.push(format!(
                    "{}: regression matching requires structured verifier results bound to this fresh session: {error}; trustc_exit={status_code}; header={expected:?}",
                    example.display(),
                ));
                continue;
            }
        };
        let missing = matches
            .iter()
            .filter(|expected| !actual_satisfies_expected(&actual, expected))
            .collect::<Vec<_>>();
        if !missing.is_empty() {
            failures.push(format!(
                "{}: missing expected structured verifier result(s) {:?}; trustc_exit={status_code}; actual={:?}; header={expected:?}",
                example.display(),
                missing
                    .iter()
                    .map(|expected| expected_terms(expected).join(" "))
                    .collect::<Vec<_>>(),
                actual,
            ));
        }
    }

    let trustc_unchanged = match trustc.verify_unchanged() {
        Ok(()) => true,
        Err(error) => {
            failures.push(error);
            false
        }
    };
    if let Err(error) = emit_report(
        &args,
        &root,
        "compiler-regression-diagnostic",
        parsed.len(),
        &parsed,
        &trustc_exits,
        &failures,
        trustc_attempts,
        trustc_completed_runs,
        Some((&trustc, trustc_unchanged)),
    ) {
        eprintln!("targo trust verify examples: {error}");
        return ExitCode::from(2);
    }
    if !trustc_unchanged {
        print_failures(&failures);
        ExitCode::from(2)
    } else if failures.is_empty() {
        ExitCode::SUCCESS
    } else {
        print_failures(&failures);
        ExitCode::from(1)
    }
}

pub(crate) fn run_verify_metadata_gate(repo_root: &Path) -> bool {
    run(&[
        "--repo-root".to_string(),
        repo_root.display().to_string(),
        "--metadata-only".to_string(),
    ]) == ExitCode::SUCCESS
}

fn parse_args(args: &[String]) -> Result<Args, String> {
    let mut parsed = Args {
        repo_root: None,
        metadata_only: false,
        allow_l0_gaps: false,
        allow_stage1_developer: false,
        json: false,
        json_output: None,
        trustc: None,
        examples: Vec::new(),
        out_dir: None,
    };
    let mut index = 0;
    while index < args.len() {
        match args[index].as_str() {
            "--repo-root" | "--root" => {
                let Some(value) = args.get(index + 1) else {
                    return Err("--repo-root requires a path".to_string());
                };
                parsed.repo_root = Some(PathBuf::from(value));
                index += 2;
            }
            "--metadata-only" => {
                parsed.metadata_only = true;
                index += 1;
            }
            "--allow-l0-gaps" => {
                parsed.allow_l0_gaps = true;
                index += 1;
            }
            "--allow-level0-gaps" => {
                return Err("--allow-level0-gaps has been removed; use --allow-l0-gaps".to_string());
            }
            value if value.starts_with("--allow-level0-gaps=") => {
                return Err("--allow-level0-gaps has been removed; use --allow-l0-gaps".to_string());
            }
            "--allow-stage1-developer" => {
                parsed.allow_stage1_developer = true;
                index += 1;
            }
            "--json" | "--format=json" => {
                parsed.json = true;
                index += 1;
            }
            "--format" => {
                let Some(value) = args.get(index + 1) else {
                    return Err("--format requires a value".to_string());
                };
                match value.as_str() {
                    "json" => parsed.json = true,
                    "terminal" | "text" => parsed.json = false,
                    other => return Err(format!("unsupported --format `{other}`")),
                }
                index += 2;
            }
            "--trustc" => {
                let Some(value) = args.get(index + 1) else {
                    return Err("--trustc requires a path".to_string());
                };
                parsed.trustc = Some(PathBuf::from(value));
                index += 2;
            }
            "--json-output" => {
                let Some(value) = args.get(index + 1) else {
                    return Err("--json-output requires a path".to_string());
                };
                parsed.json_output = Some(PathBuf::from(value));
                index += 2;
            }
            value if value.starts_with("--json-output=") => {
                let value = value.trim_start_matches("--json-output=");
                if value.is_empty() {
                    return Err("--json-output requires a path".to_string());
                }
                parsed.json_output = Some(PathBuf::from(value));
                index += 1;
            }
            "--example" => {
                let Some(value) = args.get(index + 1) else {
                    return Err("--example requires a path".to_string());
                };
                parsed.examples.push(PathBuf::from(value));
                index += 2;
            }
            "--out-dir" => {
                let Some(value) = args.get(index + 1) else {
                    return Err("--out-dir requires a path".to_string());
                };
                parsed.out_dir = Some(PathBuf::from(value));
                index += 2;
            }
            "help" | "--help" | "-h" => return Err("help".to_string()),
            other => return Err(format!("unknown argument `{other}`")),
        }
    }
    Ok(parsed)
}

fn emit_report(
    args: &Args,
    root: &Path,
    mode: &str,
    checked: usize,
    parsed: &[(PathBuf, String, Vec<ExpectedMatch>)],
    trustc_exits: &[(PathBuf, i32)],
    failures: &[String],
    trustc_attempts: usize,
    trustc_completed_runs: usize,
    trustc: Option<(&TrustcIdentity, bool)>,
) -> Result<(), String> {
    let metadata_only = mode == "metadata-regression-diagnostic";
    if args.json || args.json_output.is_some() {
        let status = if failures.is_empty() { "diagnostic_passed" } else { "diagnostic_failed" };
        let evidence = if metadata_only {
            serde_json::json!({
                "kind": "verifier-example-header-regression-diagnostic",
                "status": status,
                "proof_evidence": false,
                "release_evidence": false,
                "trustc_invocation_attempted": false,
                "trustc_completed_runs": 0,
            })
        } else if args.allow_l0_gaps {
            serde_json::json!({
                "kind": "verifier-example-raw-warning-regression-diagnostic",
                "status": status,
                "proof_evidence": false,
                "release_evidence": false,
                "trustc_invocation_attempted": trustc_attempts > 0,
                "trustc_completed_runs": trustc_completed_runs,
            })
        } else {
            serde_json::json!({
                "kind": "verifier-example-strict-regression-diagnostic",
                "status": status,
                "proof_evidence": false,
                "release_evidence": false,
                "trustc_invocation_attempted": trustc_attempts > 0,
                "trustc_completed_runs": trustc_completed_runs,
            })
        };
        let examples = parsed
            .iter()
            .map(|(path, expected, matches)| {
                let terms = matches.iter().flat_map(expected_terms).collect::<Vec<_>>();
                let trustc_exit = trustc_exits
                    .iter()
                    .find_map(|(exit_path, status)| (exit_path == path).then_some(*status));
                serde_json::json!({
                    "path": path.display().to_string(),
                    "expected": expected,
                    "terms": terms,
                    "trustc_exit": trustc_exit,
                })
            })
            .collect::<Vec<_>>();
        let report = serde_json::json!({
            "schema": "trust.verify-examples.report.v2",
            "report_kind": "regression_diagnostic",
            "mode": mode,
            "status": status,
            "proof_evidence": false,
            "release_evidence": false,
            "source_provenance_authenticated": false,
            "tool_provenance_authenticated": false,
            "trustc_invocation_attempts": trustc_attempts,
            "trustc_completed_runs": trustc_completed_runs,
            "provenance_limit": "example source bytes, checkout identity, compiler provenance, and exact argv are not authenticated together; this report cannot be promoted to proof or release evidence",
            "corpus_scope": if args.examples.is_empty() {
                "complete_discovered_corpus_diagnostic"
            } else {
                "selected_examples_diagnostic"
            },
            "verification_mode": if metadata_only {
                "metadata-only"
            } else if args.allow_l0_gaps {
                "raw-warning"
            } else {
                "strict"
            },
            "evidence": evidence,
            "fail_closed": !metadata_only && !args.allow_l0_gaps,
            "fail_closed_scope": "declared-expected-row-regression-matching-only",
            "trustc": trustc.map(|(identity, post_use_sha256_verified)| {
                serde_json::json!({
                    "path": identity.path.display().to_string(),
                    "stage": trustc_stage(root, &identity.path),
                    "sha256": identity.sha256,
                    "exact_regular_executable": true,
                    "post_use_sha256_verified": post_use_sha256_verified,
                    "replacement_detection": "before-and-after-sha256",
                    "toctou_residual": "a same-user transient swap-and-restore entirely between checks is not excluded",
                    "provenance_authenticated": false,
                    "identity_scope": "observed executable path and bytes only; no authenticated binding to checkout source or build lineage",
                    "stage1_developer_allowed": args.allow_stage1_developer,
                })
            }),
            "checked": checked,
            "examples": examples,
            "failures": failures,
        });
        let rendered = serde_json::to_string_pretty(&report)
            .map_err(|error| format!("failed to render JSON: {error}"))?;
        if args.json {
            println!("{rendered}");
        }
        if let Some(path) = args.json_output.as_ref() {
            let output_path = if path.is_absolute() { path.clone() } else { root.join(path) };
            durable_io::atomic_write_private(&output_path, format!("{rendered}\n").as_bytes())
                .map_err(|error| format!("failed to write {}: {error}", output_path.display()))?;
        }
    } else if failures.is_empty() {
        if metadata_only {
            println!(
                "checked {checked} verifier example headers: diagnostic_passed (not proof or release evidence)"
            );
        } else {
            println!(
                "checked {checked} verifier examples: diagnostic_passed (not proof or release evidence; source/tool provenance unauthenticated)"
            );
        }
    }
    Ok(())
}

fn repo_root() -> PathBuf {
    if let Ok(root) = env::var("TRUST_REPO_ROOT") {
        return PathBuf::from(root);
    }
    if let Ok(cwd) = env::current_dir() {
        for ancestor in cwd.ancestors() {
            if ancestor.join("examples").is_dir() && ancestor.join("targo-trust").is_dir() {
                return ancestor.to_path_buf();
            }
        }
    }
    Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap_or_else(|| Path::new(".")).to_path_buf()
}

fn canonicalize_repo_root(root: &Path) -> Result<PathBuf, String> {
    root.canonicalize()
        .map_err(|error| format!("failed to canonicalize repo root {}: {error}", root.display()))
}

fn discover_verify_examples(root: &Path) -> Result<Vec<PathBuf>, String> {
    let examples_dir = root.join("examples");
    let mut examples = Vec::new();
    for entry in fs::read_dir(&examples_dir)
        .map_err(|error| format!("failed to read {}: {error}", examples_dir.display()))?
    {
        let path = entry.map_err(|error| format!("failed to read examples entry: {error}"))?.path();
        if path.extension().and_then(|ext| ext.to_str()) == Some("rs")
            && path
                .file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.starts_with("verify"))
        {
            examples.push(path);
        }
    }
    examples.sort();
    Ok(examples)
}

fn example_header_metadata(path: &Path) -> Result<(String, Option<String>), String> {
    const MAX_HEADER_LINE_BYTES: usize = 64 * 1024;
    let file =
        File::open(path).map_err(|error| format!("{}: failed to open: {error}", path.display()))?;
    let mut reader = io::BufReader::new(file);
    let mut lines = Vec::with_capacity(20);
    for _ in 0..20 {
        let Some(line) =
            crate::input_limits::read_bounded_utf8_line(&mut reader, MAX_HEADER_LINE_BYTES)
                .map_err(|error| {
                    format!("{}: failed to read bounded header: {error}", path.display())
                })?
        else {
            break;
        };
        lines.push(line);
    }
    let vc_kind = lines
        .iter()
        .find_map(|line| line.trim().strip_prefix("// VcKind:").map(str::trim).map(str::to_string));
    for (index, line) in lines.iter().enumerate() {
        let stripped = line.trim();
        if let Some(rest) = stripped.strip_prefix("// Expected:") {
            let mut parts = vec![rest.trim().to_string()];
            for continuation in &lines[index + 1..] {
                let Some(text) = continuation.trim().strip_prefix("//").map(str::trim) else {
                    break;
                };
                if text.is_empty()
                    || text.starts_with("Counterexample:")
                    || text.starts_with("Safe pattern:")
                    || text.starts_with("NOTE:")
                {
                    break;
                }
                if STATUS_WORDS.iter().any(|status| text.contains(status)) {
                    parts.push(text.to_string());
                }
            }
            return Ok((parts.join(" "), vc_kind));
        }
    }
    Err(format!("{} has no '// Expected:' header in the first 20 lines", path.display()))
}

fn expected_matches(expected: &str) -> Vec<ExpectedMatch> {
    expected
        .split_whitespace()
        .collect::<Vec<_>>()
        .windows(2)
        .filter_map(|window| {
            let status = window[1].trim_matches(|ch: char| ch == ',' || ch == ';');
            if !STATUS_WORDS.contains(&status) {
                return None;
            }
            let raw = window[0].trim_matches(|ch: char| ch == ',' || ch == ';');
            let (kind, op) = if let Some((kind, rest)) = raw.split_once('(') {
                (kind.to_string(), rest.strip_suffix(')').map(str::to_string))
            } else {
                (raw.to_string(), None)
            };
            (kind.chars().next().is_some_and(|ch| ch.is_ascii_alphabetic())
                && kind
                    .chars()
                    .all(|ch| ch.is_ascii_alphanumeric() || ch == '_' || ch == '-' || ch == '.'))
            .then(|| ExpectedMatch { kind, status: status.to_string(), op })
        })
        .collect()
}

fn vc_kind_mentions_expected_kind(vc_kind: &str, expected: &ExpectedMatch) -> bool {
    output_contains_term(vc_kind, &expected.kind)
}

fn find_trustc(
    root: &Path,
    explicit: Option<&Path>,
    allow_stage1_developer: bool,
) -> Result<TrustcIdentity, String> {
    let configured = explicit
        .map(|path| if path.is_absolute() { path.to_path_buf() } else { root.join(path) })
        .or_else(|| env::var_os("TRUSTC_BIN").map(PathBuf::from));
    if let Some(candidate) = configured {
        let canonical_candidate = inspect_trustc_candidate(&candidate, true)?
            .expect("required candidate inspection cannot return missing");
        return accept_trustc_stage(root, canonical_candidate, allow_stage1_developer);
    }

    if let Some(candidate) = discover_unique_repo_stage2_tool(root, "trustc")? {
        return trustc_identity(candidate);
    }

    let executable = host_executable_name("trustc");
    let build_dir = root.join("build");
    let mut raw_stage1_candidates = vec![build_dir.join("host/stage1/bin").join(&executable)];
    if let Ok(entries) = fs::read_dir(&build_dir) {
        raw_stage1_candidates.extend(
            entries
                .filter_map(Result::ok)
                .map(|entry| entry.path().join("stage1/bin").join(&executable)),
        );
    }
    raw_stage1_candidates.sort();
    raw_stage1_candidates.dedup();
    let mut stage1_candidates = Vec::new();
    for candidate in raw_stage1_candidates {
        if let Some(candidate) = inspect_trustc_candidate(&candidate, false)? {
            if trustc_stage(root, &candidate) == "stage1-developer" {
                stage1_candidates.push(candidate);
            }
        }
    }
    if !stage1_candidates.is_empty() && !allow_stage1_developer {
        return Err(format!(
            "stage2 trustc not found; stage1 developer trustc exists but requires --allow-stage1-developer: {}",
            stage1_candidates[0].display()
        ));
    }
    stage1_candidates.sort();
    stage1_candidates.dedup();
    match stage1_candidates.as_slice() {
        [candidate] => trustc_identity(candidate.clone()),
        many @ [_, _, ..] => Err(format!(
            "stage1 developer trustc discovery is ambiguous ({}); pass one explicit --trustc path",
            many.iter().map(|path| path.display().to_string()).collect::<Vec<_>>().join(", ")
        )),
        [] => Err(
            "stage2 trustc not found; pass a repo-local --trustc, set TRUSTC_BIN to a repo-local stage2 trustc, or build stage2 first"
                .to_string(),
        ),
    }
}

fn accept_trustc_stage(
    root: &Path,
    canonical_candidate: PathBuf,
    allow_stage1_developer: bool,
) -> Result<TrustcIdentity, String> {
    match trustc_stage(root, &canonical_candidate) {
        "stage2" => validate_repo_stage2_tool(
            root,
            &canonical_candidate,
            "configured verifier example compiler",
            "trustc",
        )
        .and_then(trustc_identity),
        "stage1-developer" if allow_stage1_developer => trustc_identity(canonical_candidate),
        "stage1-developer" => Err(format!(
            "stage1 developer trustc requires --allow-stage1-developer: {}",
            canonical_candidate.display()
        )),
        _ => Err(format!(
            "external trustc is not accepted for the bounded verifier-example regression diagnostic; use repo-local build/host/stage2/bin/trustc: {}",
            canonical_candidate.display()
        )),
    }
}

fn inspect_trustc_candidate(path: &Path, required: bool) -> Result<Option<PathBuf>, String> {
    let metadata = match fs::symlink_metadata(path) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == io::ErrorKind::NotFound && !required => return Ok(None),
        Err(error) => {
            return Err(format!(
                "trustc candidate {} is missing or unreadable: {error}",
                path.display()
            ));
        }
    };
    if metadata.file_type().is_symlink() {
        return Err(format!(
            "trustc candidate {} is a symlink; the regression diagnostic requires the exact installed executable leaf",
            path.display()
        ));
    }
    if !metadata.file_type().is_file() {
        return Err(format!("trustc candidate {} is not a regular file", path.display()));
    }
    if !is_executable_metadata(&metadata) {
        return Err(format!("trustc candidate {} is not executable", path.display()));
    }
    let canonical = path.canonicalize().map_err(|error| {
        format!("failed to canonicalize trustc candidate {}: {error}", path.display())
    })?;
    // Re-check the selected canonical leaf as well. Directory symlinks (for a
    // canonicalized checkout root) are harmless; a redirected executable leaf
    // is not.
    exact_executable_metadata(&canonical).map_err(|error| {
        format!("canonical trustc candidate {} is invalid: {error}", canonical.display())
    })?;
    Ok(Some(canonical))
}

fn trustc_identity(path: PathBuf) -> Result<TrustcIdentity, String> {
    let sha256 = exact_executable_sha256(&path)
        .map_err(|error| format!("could not hash exact trustc {}: {error}", path.display()))?;
    Ok(TrustcIdentity { path, sha256 })
}

fn exact_executable_sha256(path: &Path) -> io::Result<String> {
    const MAX_EXECUTABLE_BYTES: u64 = 1024 * 1024 * 1024;
    let path_metadata = exact_executable_metadata(path)?;
    if path_metadata.len() == 0 || path_metadata.len() > MAX_EXECUTABLE_BYTES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "executable size {} is outside the 1..={MAX_EXECUTABLE_BYTES} byte identity bound",
                path_metadata.len()
            ),
        ));
    }
    let mut file = File::open(path)?;
    let opened_metadata = file.metadata()?;
    if !same_file_identity(&path_metadata, &opened_metadata) {
        return Err(io::Error::other("executable changed while it was opened"));
    }
    let mut hasher = Sha256::new();
    let mut buffer = [0u8; 64 * 1024];
    let mut total = 0_u64;
    loop {
        let read = file.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        total = total
            .checked_add(read as u64)
            .ok_or_else(|| io::Error::other("executable byte count overflowed"))?;
        if total > path_metadata.len() || total > MAX_EXECUTABLE_BYTES {
            return Err(io::Error::other("executable grew while it was hashed"));
        }
        hasher.update(&buffer[..read]);
    }
    if total != path_metadata.len() {
        return Err(io::Error::other("executable length changed while it was hashed"));
    }
    let after = exact_executable_metadata(path)?;
    if !same_file_identity(&path_metadata, &after) {
        return Err(io::Error::other("executable changed while it was hashed"));
    }
    Ok(format!("{:x}", hasher.finalize()))
}

fn exact_executable_metadata(path: &Path) -> io::Result<fs::Metadata> {
    let metadata = fs::symlink_metadata(path)?;
    if metadata.file_type().is_symlink() {
        return Err(io::Error::other("executable leaf is a symlink"));
    }
    if !metadata.file_type().is_file() {
        return Err(io::Error::other("executable leaf is not a regular file"));
    }
    if !is_executable_metadata(&metadata) {
        return Err(io::Error::other("executable leaf has no execute bit"));
    }
    Ok(metadata)
}

#[cfg(unix)]
fn is_executable_metadata(metadata: &fs::Metadata) -> bool {
    use std::os::unix::fs::PermissionsExt;

    metadata.permissions().mode() & 0o111 != 0
}

#[cfg(not(unix))]
fn is_executable_metadata(metadata: &fs::Metadata) -> bool {
    metadata.is_file()
}

#[cfg(unix)]
fn same_file_identity(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    use std::os::unix::fs::MetadataExt;

    left.dev() == right.dev() && left.ino() == right.ino()
}

#[cfg(not(unix))]
fn same_file_identity(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    left.is_file() && right.is_file() && left.len() == right.len()
}

fn trustc_stage(root: &Path, path: &Path) -> &'static str {
    let rel = path.strip_prefix(root).unwrap_or(path);
    let components =
        rel.components().filter_map(|component| component.as_os_str().to_str()).collect::<Vec<_>>();
    if components.len() == 5
        && components[0] == "build"
        && !components[1].is_empty()
        && components[3] == "bin"
        && components[4] == host_executable_name("trustc")
    {
        if components[2] == "stage2" {
            return "stage2";
        }
        if components[2] == "stage1" {
            return "stage1-developer";
        }
    }
    "explicit-external"
}

fn run_example(
    trustc: &Path,
    source: &Path,
    out_dir: &Path,
    allow_l0_gaps: bool,
    verification_session: &str,
) -> Result<(ExitStatus, String), String> {
    let output =
        out_dir.join(source.file_stem().and_then(|stem| stem.to_str()).unwrap_or("example"));
    let crate_name = example_crate_name(source);
    // Strict verification is batteries-on. This is a raw compiler invocation,
    // so the default `unscoped` role is in scope and no Cargo-owned scope
    // metadata is synthesized. `--allow-l0-gaps` selects allow_l0_gaps (warnings).
    let advisory_lane: Vec<String> =
        if allow_l0_gaps { vec!["-Z".to_string(), "trust-policy=advisory".to_string()] } else { Vec::new() };
    let mut command = Command::new(trustc);
    command
        .env_remove("TRUST_VERIFY")
        .env_remove("TRUST_DUMP_ONLY")
        .args(["-Z", "trust-verify-output=json"])
        .args(["-Z", &format!("trust-verify-session={verification_session}")])
        // Proof budgets affect verdicts and therefore must enter rustc's
        // tracked option set. The retired environment input is intentionally
        // not forwarded to the compiler.
        .args(["-Z", "trust-verify-timeout-ms=5000"])
        .args(&advisory_lane)
        .args(["--crate-name", crate_name.as_str()])
        .arg(source)
        .arg("-o")
        .arg(output);
    let run = bounded_process::output(
        &mut command,
        &format!("verifier example {}", source.display()),
        64 * 1024 * 1024,
        Duration::from_secs(60),
    )?;
    let mut combined = String::from_utf8(run.stdout)
        .map_err(|_| format!("verifier example {} stdout was not valid UTF-8", source.display()))?;
    let stderr = String::from_utf8(run.stderr)
        .map_err(|_| format!("verifier example {} stderr was not valid UTF-8", source.display()))?;
    combined.push_str(&stderr);
    Ok((run.status, combined))
}

fn example_crate_name(source: &Path) -> String {
    let stem = source.file_stem().and_then(|stem| stem.to_str()).unwrap_or("example");
    let mut name = String::from("trust_verify_example");
    if !stem.is_empty() {
        name.push('_');
    }
    for ch in stem.chars() {
        if ch.is_ascii_alphanumeric() {
            name.push(ch.to_ascii_lowercase());
        } else if !name.ends_with('_') {
            name.push('_');
        }
    }
    name.trim_end_matches('_').to_string()
}

fn expected_terms(expected: &ExpectedMatch) -> Vec<String> {
    let mut terms = vec![expected.kind.clone(), expected.status.clone()];
    if let Some(op) = &expected.op {
        terms.push(op.clone());
    }
    terms
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ActualMatch {
    kind: String,
    outcome: trust_types::Outcome,
    description: String,
}

fn actual_matches(output: &str) -> Vec<ActualMatch> {
    output
        .lines()
        .filter_map(|line| line.trim_start().strip_prefix("TRUST_JSON:"))
        .filter_map(|json| serde_json::from_str::<serde_json::Value>(json).ok())
        .flat_map(|value| {
            value.get("results").and_then(|results| results.as_array()).cloned().unwrap_or_default()
        })
        .filter_map(|result| {
            let kind = result.get("kind")?.as_str()?.to_string();
            let outcome = trust_types::Outcome::parse(result.get("outcome")?.as_str()?)?;
            let description = result
                .get("description")
                .and_then(|value| value.as_str())
                .unwrap_or_default()
                .to_string();
            Some(ActualMatch { kind, outcome, description })
        })
        .collect()
}

fn fresh_verification_session() -> Result<String, String> {
    let mut nonce = [0u8; 32];
    getrandom::fill(&mut nonce).map_err(|error| {
        format!("operating-system randomness failed while creating verification session: {error}")
    })?;
    Ok(nonce.iter().map(|byte| format!("{byte:02x}")).collect())
}

fn session_bound_actual_matches(
    output: &str,
    expected_session: &str,
) -> Result<Vec<ActualMatch>, String> {
    if expected_session.is_empty() {
        return Err("verification session is empty".to_string());
    }
    let mut found_results = false;
    for line in output.lines() {
        let Some(payload) = line.trim_start().strip_prefix("TRUST_JSON:") else {
            continue;
        };
        let value = serde_json::from_str::<serde_json::Value>(payload)
            .map_err(|error| format!("malformed TRUST_JSON payload: {error}"))?;
        let Some(results) = value.get("results") else {
            continue;
        };
        let rows = results
            .as_array()
            .ok_or_else(|| "structured verifier results is not an array".to_string())?;
        if value.get("verification_session").and_then(serde_json::Value::as_str)
            != Some(expected_session)
        {
            return Err(
                "structured verifier results has a missing or mismatched session".to_string()
            );
        }
        if value.get("total").and_then(serde_json::Value::as_u64) != u64::try_from(rows.len()).ok()
        {
            return Err("structured verifier result total does not match its rows".to_string());
        }
        for row in rows {
            let kind = row.get("kind").and_then(serde_json::Value::as_str).unwrap_or_default();
            let outcome =
                row.get("outcome").and_then(serde_json::Value::as_str).unwrap_or_default();
            if kind.is_empty()
                || !matches!(
                    trust_types::Outcome::parse(outcome),
                    Some(
                        trust_types::Outcome::Proved
                            | trust_types::Outcome::Failed
                            | trust_types::Outcome::Unknown
                            | trust_types::Outcome::Timeout
                            | trust_types::Outcome::RuntimeChecked
                            | trust_types::Outcome::Skipped
                    )
                )
            {
                return Err("structured verifier result has an invalid kind or outcome".to_string());
            }
            if kind != "no_obligations"
                && (row
                    .get("obligation_id")
                    .and_then(serde_json::Value::as_str)
                    .is_none_or(str::is_empty)
                    || !row.get("location").is_some_and(serde_json::Value::is_object))
            {
                return Err(
                    "structured verifier obligation lacks a stable obligation_id or source location"
                        .to_string(),
                );
            }
        }
        found_results = true;
    }
    if !found_results {
        return Err("no structured verifier results envelope was emitted".to_string());
    }
    Ok(actual_matches(output))
}

fn actual_satisfies_expected(actual: &[ActualMatch], expected: &ExpectedMatch) -> bool {
    let matching = actual
        .iter()
        .filter(|row| {
            actual_contains_term(row, &expected.kind)
                && expected.op.as_ref().is_none_or(|op| actual_contains_term(row, op))
        })
        .collect::<Vec<_>>();
    if expected.status == "ABSENT" {
        return matching.is_empty();
    }
    // A fixture header states its expectation the way a human writes it
    // (`RUNTIME-CHECKED`); the shared outcome parser reconciles that with the
    // compiler's spelling, so a header naming an outcome nothing produces
    // matches nothing instead of comparing two unrelated strings.
    let Some(outcome) = trust_types::Outcome::parse(&expected.status) else {
        return false;
    };
    if expected.status == "PROVED" {
        return !matching.is_empty() && matching.iter().all(|row| row.outcome == outcome);
    }
    matching.iter().any(|row| row.outcome == outcome)
}

fn actual_contains_term(actual: &ActualMatch, term: &str) -> bool {
    output_contains_term(&actual.kind, term) || output_contains_term(&actual.description, term)
}

fn output_contains_term(output: &str, term: &str) -> bool {
    let haystacks = normalized_haystacks(output);
    normalized_needles(term).iter().any(|needle| {
        !needle.is_empty() && haystacks.iter().any(|haystack| haystack.contains(needle))
    })
}

fn normalized_haystacks(text: &str) -> Vec<String> {
    let lower = text.to_ascii_lowercase();
    vec![lower.clone(), normalize_separators(&lower), compact_alnum(&lower)]
}

fn normalized_needles(term: &str) -> Vec<String> {
    let lower = term.to_ascii_lowercase();
    let snake = camel_to_snake(term);
    let mut needles = vec![
        lower,
        snake.clone(),
        snake.replace('_', "-"),
        snake.replace('_', " "),
        compact_alnum(&snake),
    ];
    needles.sort();
    needles.dedup();
    needles
}

fn camel_to_snake(term: &str) -> String {
    let mut out = String::new();
    for (index, ch) in term.chars().enumerate() {
        if ch.is_ascii_alphanumeric() {
            if ch.is_ascii_uppercase() && index > 0 {
                out.push('_');
            }
            out.push(ch.to_ascii_lowercase());
        } else if !out.ends_with('_') {
            out.push('_');
        }
    }
    out.trim_matches('_').to_string()
}

fn normalize_separators(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for ch in text.chars() {
        if ch.is_ascii_alphanumeric() {
            out.push(ch);
        } else if !out.ends_with('_') {
            out.push('_');
        }
    }
    out.trim_matches('_').to_string()
}

fn compact_alnum(text: &str) -> String {
    text.chars().filter(|ch| ch.is_ascii_alphanumeric()).collect()
}

fn print_failures(failures: &[String]) {
    for failure in failures {
        eprintln!("FAIL: {failure}");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn expected_parser_handles_multi_obligation_headers() {
        let parsed =
            expected_matches("Overflow(Add) FAILED, BoundsCheck PROVED; BorrowConflict UNKNOWN");
        assert_eq!(parsed.len(), 3);
        assert_eq!(parsed[0].kind, "Overflow");
        assert_eq!(parsed[0].op.as_deref(), Some("Add"));
        assert_eq!(parsed[1].status, "PROVED");
        assert_eq!(parsed[2].kind, "BorrowConflict");
    }

    #[test]
    fn expected_parser_recognizes_absent_without_calling_it_proved() {
        let parsed = expected_matches("FloatDivisionByZero ABSENT");
        assert_eq!(
            parsed,
            vec![ExpectedMatch {
                kind: "FloatDivisionByZero".to_string(),
                status: "ABSENT".to_string(),
                op: None,
            }]
        );
    }

    #[test]
    fn verifier_result_sessions_are_fresh_canonical_256_bit_nonces() {
        let first = fresh_verification_session().expect("create first verifier session");
        let second = fresh_verification_session().expect("create second verifier session");
        assert_ne!(first, second);
        for session in [first, second] {
            assert_eq!(session.len(), 64);
            assert!(
                session.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
            );
        }
    }

    #[test]
    fn expected_parser_rejects_prose_instead_of_defaulting_to_failed() {
        assert!(expected_matches("deref NOT proved (arbitrary pointer stays CAUGHT)").is_empty());
    }

    #[test]
    fn absent_requires_a_valid_envelope_and_forbids_the_named_kind() {
        let expected = ExpectedMatch {
            kind: "FloatDivisionByZero".to_string(),
            status: "ABSENT".to_string(),
            op: None,
        };
        let unrelated = ActualMatch {
            kind: "assert".to_string(),
            outcome: trust_types::Outcome::Unknown,
            description: "assertion".to_string(),
        };
        let prohibited = ActualMatch {
            kind: "float_division_by_zero".to_string(),
            outcome: trust_types::Outcome::Unknown,
            description: "float division by zero".to_string(),
        };
        assert!(actual_satisfies_expected(&[unrelated], &expected));
        assert!(!actual_satisfies_expected(&[prohibited], &expected));
        assert!(session_bound_actual_matches("ordinary stderr only", "session-a").is_err());
        assert!(session_bound_actual_matches(
            r#"TRUST_JSON:{"type":"function_result","verification_session":"session-a","results":[],"total":0}"#,
            "session-a",
        )
        .is_ok());
        assert!(session_bound_actual_matches(
            r#"TRUST_JSON:{"type":"function_result","verification_session":"wrong","results":[],"total":0}"#,
            "session-a",
        )
        .is_err());
    }

    #[test]
    fn expected_statuses_are_exact() {
        let failed = ExpectedMatch {
            kind: "DivisionByZero".to_string(),
            status: "FAILED".to_string(),
            op: None,
        };
        let runtime_checked = ActualMatch {
            kind: "divzero".to_string(),
            outcome: trust_types::Outcome::RuntimeChecked,
            description: "division by zero".to_string(),
        };
        assert!(!actual_satisfies_expected(&[runtime_checked], &failed));

        let proved = ExpectedMatch {
            kind: "DivisionByZero".to_string(),
            status: "PROVED".to_string(),
            op: None,
        };
        let proved_row = ActualMatch {
            kind: "divzero".to_string(),
            outcome: trust_types::Outcome::Proved,
            description: "division by zero".to_string(),
        };
        let failed_row = ActualMatch {
            kind: "divzero".to_string(),
            outcome: trust_types::Outcome::Failed,
            description: "division by zero".to_string(),
        };
        assert!(!actual_satisfies_expected(&[proved_row, failed_row], &proved));
    }

    #[test]
    fn example_header_is_single_pass_and_bounded_before_parsing() {
        let temp = tempfile::tempdir().expect("header fixture");
        let valid = temp.path().join("valid.rs");
        fs::write(
            &valid,
            "// Expected: BoundsCheck PROVED\n// VcKind: BoundsCheck\nfn main() {}\n",
        )
        .expect("valid header");
        let (expected, vc_kind) = example_header_metadata(&valid).expect("header metadata");
        assert_eq!(expected, "BoundsCheck PROVED");
        assert_eq!(vc_kind.as_deref(), Some("BoundsCheck"));

        let oversized = temp.path().join("oversized.rs");
        fs::write(&oversized, format!("// {}\n", "x".repeat(64 * 1024))).expect("oversized header");
        let error = example_header_metadata(&oversized)
            .expect_err("oversized header line must fail before unbounded allocation");
        assert!(error.contains("65536-byte safety limit"), "{error}");
    }

    #[test]
    fn expected_parser_accepts_dotted_hyphenated_proof_metric_kinds() {
        let parsed = expected_matches("proof.functional-best-existing-tools UNKNOWN");
        assert_eq!(parsed.len(), 1);
        assert_eq!(parsed[0].kind, "proof.functional-best-existing-tools");
        assert_eq!(parsed[0].status, "UNKNOWN");
        assert_eq!(parsed[0].op, None);
        assert!(vc_kind_mentions_expected_kind("Proof functional best existing tools", &parsed[0]));
    }

    #[test]
    fn output_matching_accepts_camel_snake_and_kebab_case() {
        assert!(output_contains_term("vc_kind: bounds-check", "BoundsCheck"));
        assert!(output_contains_term("status=proved", "PROVED"));
        assert!(output_contains_term("operation add", "Add"));
        assert!(output_contains_term("description: division by zero", "DivisionByZero"));
        assert!(output_contains_term("description: index out of bounds", "IndexOutOfBounds"));
    }

    #[test]
    fn structured_matching_requires_same_result_outcome() {
        let actual = actual_matches(
            r#"
TRUST_JSON:{"type":"function_result","function":"divide","results":[{"kind":"divzero","description":"division by zero","outcome":"runtime_checked"}],"failed":0}
"#,
        );
        let failed = ExpectedMatch {
            kind: "DivisionByZero".to_string(),
            status: "FAILED".to_string(),
            op: None,
        };

        assert!(!actual_satisfies_expected(&actual, &failed));
    }

    #[test]
    fn structured_matching_accepts_dotted_hyphenated_proof_metric_json() {
        let actual = actual_matches(
            r#"
TRUST_JSON:{"type":"function_result","function":"proof_metric","results":[{"kind":"proof.functional-best-existing-tools","description":"best existing tools coverage","outcome":"unknown"}]}
"#,
        );
        let expected = ExpectedMatch {
            kind: "proof.functional-best-existing-tools".to_string(),
            status: "UNKNOWN".to_string(),
            op: None,
        };

        assert!(actual_satisfies_expected(&actual, &expected));
    }

    #[test]
    fn structured_matching_keeps_kind_status_and_op_on_one_row() {
        let actual = actual_matches(
            r#"
TRUST_JSON:{"type":"function_result","function":"mixed","results":[{"kind":"overflow:add","description":"arithmetic overflow (Add)","outcome":"failed"},{"kind":"bounds","description":"index out of bounds","outcome":"proved"}]}
"#,
        );
        let add_failed = ExpectedMatch {
            kind: "ArithmeticOverflow".to_string(),
            status: "FAILED".to_string(),
            op: Some("Add".to_string()),
        };
        let add_proved = ExpectedMatch {
            kind: "ArithmeticOverflow".to_string(),
            status: "PROVED".to_string(),
            op: Some("Add".to_string()),
        };

        assert!(actual_satisfies_expected(&actual, &add_failed));
        assert!(!actual_satisfies_expected(&actual, &add_proved));
    }

    #[test]
    fn example_crate_name_marks_single_file_examples_as_trust_owned() {
        let name = example_crate_name(Path::new("examples/verify-div-zero.rs"));
        assert_eq!(name, "trust_verify_example_verify_div_zero");
        assert!(name.starts_with("trust_"));
    }

    #[test]
    fn stage_classification_requires_exact_platform_leaf_and_shape() {
        let root = Path::new("/repo");
        let exact = root.join("build/host/stage2/bin").join(host_executable_name("trustc"));
        assert_eq!(trustc_stage(root, &exact), "stage2");
        let nested = root.join("build/host/stage2/bin/nested").join(host_executable_name("trustc"));
        assert_eq!(trustc_stage(root, &nested), "explicit-external");
    }

    #[cfg(unix)]
    #[test]
    fn verifier_example_preserves_signal_termination_as_tool_failure() {
        use std::os::unix::fs::PermissionsExt as _;

        let temp = tempfile::tempdir().expect("signaled verifier fixture");
        let trustc = temp.path().join("trustc");
        fs::write(&trustc, b"#!/bin/sh\nkill -TERM $$\n").expect("write fake trustc");
        fs::set_permissions(&trustc, fs::Permissions::from_mode(0o700)).expect("chmod trustc");
        let source = temp.path().join("example.rs");
        fs::write(&source, "fn main() {}\n").expect("source");
        let out = temp.path().join("out");
        fs::create_dir(&out).expect("out dir");

        let (status, _) = run_example(&trustc, &source, &out, false, "signal-test-session")
            .expect("run signaled trustc");
        assert_eq!(status.code(), None, "a signal must not be collapsed into verifier exit 1");
    }

    #[cfg(unix)]
    #[test]
    fn trustc_identity_rejects_persistent_replacement_and_symlink() {
        use std::os::unix::fs::{PermissionsExt, symlink};

        let temp = tempfile::tempdir().expect("trustc identity fixture");
        let trustc = temp.path().join("trustc");
        fs::write(&trustc, b"#!/bin/sh\nexit 0\n").expect("write trustc");
        let mut permissions = fs::metadata(&trustc).expect("trustc metadata").permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(&trustc, permissions).expect("make trustc executable");

        let identity = trustc_identity(trustc.clone()).expect("capture trustc identity");
        fs::write(&trustc, b"#!/bin/sh\nexit 9\n").expect("replace trustc bytes");
        assert!(identity.verify_unchanged().is_err());

        let target = temp.path().join("real-trustc");
        fs::rename(&trustc, &target).expect("move replacement aside");
        symlink(&target, &trustc).expect("install trustc symlink");
        assert!(exact_executable_sha256(&trustc).is_err());
    }
}
