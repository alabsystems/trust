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
// POLICY. TEST_SOURCE carries three REAL safety defects on purpose (midpoint's
// `b - a` underflow, add_five's `x + 5` overflow, raw_divide's unguarded `a / b`),
// so the default STRICT policy correctly refuses to compile it. Every compile
// that needs transport or a MIR dump therefore passes `-Ztrust-policy=advisory`
// (the survey lane: verification still runs and every row is reported, the
// refutations are downgraded to warnings). The strict refusal itself is asserted
// by test_e2e_real_rustc_strict_policy_refuses_unsafe_fixture, so advisory can
// never hide a strict lane that stopped refusing.
//
// Prerequisites (each test FAILS, never skips, without them):
//   - a Trust rustc: TRUST_RUSTC=/path/to/rustc (authoritative when set), else
//     discovered under build/*/stage{1,2}/bin/rustc (./x.py build --stage 1)
//   - ay, discovered by the integration-test ay helper (require_ay)
//
// History (fixed 2026-09-30): the capability probe compiled its unguarded divide
// with no flags, i.e. under the strict default, which every Trust rustc refuses
// (rc=1, no TRUST_JSON). Discovery therefore found "no Trust rustc" and every
// test printed SKIPPING and passed, on every host, without running anything.
//
// Issue: #937 | Epic: #935
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_integration_tests::ay_test_support::require_ay;
use trust_integration_tests::trust_rustc::{
    ADVISORY_JSON_ARGS, FLAG_SURFACE, Provenance, TrustRustc, assert_rustc_success,
    extract_function_results, find_repo_root, is_executable_file, parse_transport_lines,
    provenance, resolve_trust_rustc_from, run_rustc_command, rustc_failure_diagnostic,
    verified_lib_command_with_args,
};
use trust_types::*;

// ---------------------------------------------------------------------------
// Compiler discovery
// ---------------------------------------------------------------------------

/// The Trust rustc every test in this file measures; panics with how to get
/// one when none is usable. The resolver, its capability probe and the command
/// helpers this file uses live in `trust_integration_tests::trust_rustc`
/// (hoisted 2026-10-09 so the real-MIR loop tests share them); its module docs
/// give the resolution order. These tests need nothing past the flag surface.
fn require_trust_rustc() -> PathBuf {
    trust_integration_tests::trust_rustc::require_trust_rustc(None).path
}

// ---------------------------------------------------------------------------
// Test source code
// ---------------------------------------------------------------------------

/// The test Rust source file. Contains functions with known verification properties:
///
/// - `safe_divide`: division guarded by a zero check -> its div-by-zero VC is proved
/// - `midpoint`: `b - a` can underflow -> an overflow VC the strict policy refutes
/// - `add_five`: `x + 5` can overflow -> an overflow VC the strict policy refutes
/// - `raw_divide`: unguarded division -> a div-by-zero VC the strict policy refutes
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

/// Addition of a constant: overflows for x > u32::MAX - 5.
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
    let rustc = require_trust_rustc();

    let tmp = tempfile::tempdir().unwrap();
    let src_path = tmp.path().join("test_verify.rs");
    std::fs::write(&src_path, TEST_SOURCE).unwrap();

    // Invoke the compiler with advisory verification explicitly enabled.
    // Use --crate-type lib to avoid needing a main().
    let mut cmd = verified_lib_command_with_args(
        &rustc,
        &src_path,
        &tmp.path().join("test_verify.rlib"),
        ADVISORY_JSON_ARGS,
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

    // Under the advisory policy the compiler completes (exit 0) although
    // verification refutes three of the fixture's obligations; the strict
    // default would refuse it (asserted in the strict-policy test below).
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
    let rustc = require_trust_rustc();

    let tmp = tempfile::tempdir().unwrap();
    let src_path = tmp.path().join("test_dump.rs");
    std::fs::write(&src_path, TEST_SOURCE).unwrap();

    let dump_dir = tmp.path().join("mir_dump");
    std::fs::create_dir_all(&dump_dir).unwrap();

    // Invoke the compiler with the tracked dump option to extract real MIR as JSON.
    // Strict refuses TEST_SOURCE, and `-Ztrust-verify=off` is refused for
    // `-Ztrust-dump=mir:<dir>` (it needs batteries-on verification), so the
    // dump runs in the advisory lane.
    let mut cmd = verified_lib_command_with_args(
        &rustc,
        &src_path,
        &tmp.path().join("test_dump.rlib"),
        ADVISORY_JSON_ARGS,
    );
    cmd.arg("-Z").arg(format!("trust-dump=mir:{}", dump_dir.display()));
    let (output, command_line) = run_rustc_command("-Ztrust-dump=mir:<dir> compile", &mut cmd);
    assert_rustc_success("-Ztrust-dump=mir:<dir> compile", &rustc, &command_line, &output);

    // Load and validate dumped JSON fixtures.
    let entries: Vec<_> = std::fs::read_dir(&dump_dir)
        .unwrap_or_else(|e| panic!("failed to read dump dir {}: {e}", dump_dir.display()))
        .map(|e| {
            e.unwrap_or_else(|e| panic!("failed to read an entry of {}: {e}", dump_dir.display()))
        })
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

    // Every TEST_SOURCE function is dumped: a dump that dropped one (say
    // raw_divide, the refuted one) must not pass here.
    for expected in ["safe_divide", "midpoint", "add_five", "raw_divide"] {
        assert!(
            functions
                .iter()
                .any(|f| f.name == expected || f.def_path.ends_with(&format!("::{expected}"))),
            "-Ztrust-dump=mir:<dir> dumped no fixture for `{expected}`; dumped: {:?}",
            functions.iter().map(|f| &f.def_path).collect::<Vec<_>>()
        );
    }

    eprintln!("\n=== E2E Real Rustc tracked MIR dump: {} functions extracted ===", functions.len());
}

// ---------------------------------------------------------------------------
// Test 3: Full pipeline -- real rustc MIR through vcgen + real ay
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_real_rustc_full_pipeline_with_ay() {
    let rustc = require_trust_rustc();
    // Fails closed (panics with the searched conventions) when ay is absent.
    let ay = require_ay();

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
        ADVISORY_JSON_ARGS,
    );
    cmd.arg("-Z").arg(format!("trust-dump=mir:{}", dump_dir.display()));
    let (output, command_line) = run_rustc_command("full pipeline MIR dump compile", &mut cmd);
    assert_rustc_success("full pipeline MIR dump compile", &rustc, &command_line, &output);

    // Step 2: Load dumped MIR fixtures
    let functions = load_mir_fixtures_from_dir(&dump_dir);
    assert!(!functions.is_empty(), "should have at least one dumped function");

    eprintln!("Loaded {} functions from -Ztrust-dump=mir:<dir>", functions.len());

    // Step 3: Run each through vcgen + real ay
    let mut total_proved = 0usize;
    let mut total_failed = 0usize;
    let mut total_unknown = 0usize;
    let mut all_results: Vec<(VerificationCondition, VerificationResult)> = Vec::new();
    let mut per_function: Vec<(
        &VerifiableFunction,
        Vec<(VerificationCondition, VerificationResult)>,
    )> = Vec::new();

    for func in &functions {
        let vcs = trust_vcgen::generate_vcs(func);
        eprintln!("  {} -> {} VCs", func.def_path, vcs.len());

        let mut func_results = Vec::new();
        for vc in &vcs {
            use trust_router::VerificationBackend;
            let result = ay.verify(vc);
            match &result {
                VerificationResult::Proved { .. } => total_proved += 1,
                VerificationResult::Failed { .. } => total_failed += 1,
                _ => total_unknown += 1,
            }
            func_results.push((vc.clone(), result));
        }
        all_results.extend(func_results.iter().cloned());
        per_function.push((func, func_results));
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

    // SOUNDNESS on the Rust-side path too: raw_divide's unguarded `a / b`
    // division-by-zero VC is refutable (b == 0), so ay must never prove it.
    let raw_divide_divzero: Vec<&VerificationResult> = per_function
        .iter()
        .filter(|(func, _)| func.name == "raw_divide")
        .flat_map(|(_, results)| results.iter())
        .filter(|(vc, _)| matches!(vc.kind, VcKind::DivisionByZero))
        .map(|(_, result)| result)
        .collect();
    assert!(
        !raw_divide_divzero.is_empty(),
        "vcgen produced no DivisionByZero VC for the dumped raw_divide MIR"
    );
    assert!(
        raw_divide_divzero.iter().all(|result| !result.is_proved()),
        "ay PROVED raw_divide's unguarded division-by-zero VC (b == 0 is reachable): \
         {raw_divide_divzero:?}"
    );

    // Step 4: Generate a proof certificate record from a function with a
    // proved VC. safe_divide's division is guarded by `b == 0`, so ay proves
    // it; a run that proves nothing would skip the proof-cert stage this test
    // names, so that fails instead of passing.
    let (func, func_results) = per_function
        .iter()
        .find(|(_, results)| results.iter().any(|(_, r)| r.is_proved()))
        .unwrap_or_else(|| {
            panic!(
                "ay proved none of the {} VCs (safe_divide's guarded division should be \
                 provable), so the proof-cert stage cannot run",
                all_results.len()
            )
        });
    let cert = trust_proof_cert::generate_certificate_record(func, func_results);
    assert!(
        cert.is_ok(),
        "proof certificate generation should succeed for {}: {:?}",
        func.name,
        cert.err()
    );
    let cert = cert.unwrap();
    eprintln!("  Certificate record for {}: digest={}", func.name, cert.record_digest);

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
    let rustc = require_trust_rustc();

    let tmp = tempfile::tempdir().unwrap();
    let src_path = tmp.path().join("test_names.rs");
    std::fs::write(&src_path, TEST_SOURCE).unwrap();

    let mut cmd = verified_lib_command_with_args(
        &rustc,
        &src_path,
        &tmp.path().join("test_names.rlib"),
        ADVISORY_JSON_ARGS,
    );
    let (output, command_line) = run_rustc_command("function names transport compile", &mut cmd);
    assert_rustc_success("function names transport compile", &rustc, &command_line, &output);

    let stderr = String::from_utf8_lossy(&output.stderr);
    let messages = parse_transport_lines(&stderr);
    let fn_results = extract_function_results(&messages);

    // Every pub fn of the crate under verification is eligible, so each one
    // must appear in the transport output; a missing one is a coverage gap.
    let expected_names = ["safe_divide", "midpoint", "add_five", "raw_divide"];
    let found_names: Vec<&str> = fn_results.iter().map(|r| r.function.as_str()).collect();

    eprintln!("Functions in transport output:");
    for name in &found_names {
        eprintln!("  {name}");
    }

    let mut missing = Vec::new();
    for expected in &expected_names {
        if found_names.iter().any(|n| n.ends_with(&format!("::{expected}"))) {
            eprintln!("  FOUND: {expected}");
        } else {
            eprintln!("  MISSING: {expected}");
            missing.push(*expected);
        }
    }

    assert!(
        missing.is_empty(),
        "every test function should appear in transport output. Missing {missing:?} of \
         {expected_names:?}; transport had {} function results: {found_names:?}",
        fn_results.len()
    );
}

// ---------------------------------------------------------------------------
// Test 5: Verification results correctness (raw_divide should have div-by-zero VC)
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_real_rustc_divzero_vc_for_raw_divide() {
    let rustc = require_trust_rustc();

    let tmp = tempfile::tempdir().unwrap();
    let src_path = tmp.path().join("test_divzero.rs");
    std::fs::write(&src_path, TEST_SOURCE).unwrap();

    let mut cmd = verified_lib_command_with_args(
        &rustc,
        &src_path,
        &tmp.path().join("test_divzero.rlib"),
        ADVISORY_JSON_ARGS,
    );
    let (output, command_line) = run_rustc_command("raw_divide transport compile", &mut cmd);
    assert_rustc_success("raw_divide transport compile", &rustc, &command_line, &output);

    let stderr = String::from_utf8_lossy(&output.stderr);
    let messages = parse_transport_lines(&stderr);
    let fn_results = extract_function_results(&messages);

    // Find raw_divide in the results -- it does `a / b` without a guard,
    // so it must have a division-by-zero VC. A pub fn of the crate under
    // verification is not filtered or inlined away; its absence is a
    // coverage defect, not a pass.
    let found: Vec<&str> = fn_results.iter().map(|r| r.function.as_str()).collect();
    let result =
        fn_results.iter().find(|r| r.function.ends_with("::raw_divide")).unwrap_or_else(|| {
            panic!(
                "raw_divide missing from transport output; function results: {found:?}\n\
                 rustc: {}\nstderr:\n{stderr}",
                rustc.display()
            )
        });
    eprintln!(
        "raw_divide: {} obligations ({} proved, {} failed, {} unknown)",
        result.total, result.proved, result.failed, result.unknown
    );
    for (i, obl) in result.results.iter().enumerate() {
        eprintln!("    obligation {i}: kind={}, outcome={}", obl.kind, obl.outcome);
    }

    let divzero = result
        .results
        .iter()
        .find(|r| {
            r.kind == "divzero"
                || r.typed_kind.as_deref().is_some_and(|k| matches!(k, VcKind::DivisionByZero))
        })
        .unwrap_or_else(|| {
            panic!(
                "raw_divide has no division-by-zero obligation among its {} obligation(s): {:?}",
                result.total,
                result.results.iter().map(|r| r.kind.as_str()).collect::<Vec<_>>()
            )
        });

    // SOUNDNESS: `a / b` with an unconstrained `b` panics for b == 0, so its
    // division-by-zero obligation must never come back proved.
    assert!(
        !divzero.outcome.is_proved(),
        "raw_divide's unguarded `a / b` division-by-zero obligation was reported PROVED \
         (outcome={}); b == 0 is reachable, so this is a false proof",
        divzero.outcome
    );
    eprintln!("  Confirmed: div-by-zero VC present for raw_divide, outcome={}", divzero.outcome);
}

// ---------------------------------------------------------------------------
// Test 6: -Z trust-verify=off suppresses the native verification pass
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_real_rustc_no_trust_verify_suppresses_transport() {
    let rustc = require_trust_rustc();

    let tmp = tempfile::tempdir().unwrap();
    let src_path = tmp.path().join("test_no_verify.rs");
    std::fs::write(&src_path, TEST_SOURCE).unwrap();

    let output_path = tmp.path().join("test_no_verify.rlib");
    let mut cmd = verified_lib_command_with_args(
        &rustc,
        &src_path,
        &output_path,
        // The JSON transport is requested, so its absence is the off switch's
        // doing, not the human-readable default's.
        &["-Z", "trust-verify-output=json", "-Z", "trust-verify=off"],
    );
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
// Test 7: the strict default policy refuses TEST_SOURCE's real defects
// ---------------------------------------------------------------------------

/// The witness that ADVISORY_JSON_ARGS downgrades real refutations rather
/// than masking a compiler that stopped finding them: with no policy flag, the
/// strict default must FAIL the build on raw_divide (and on midpoint's
/// underflow and add_five's overflow) while leaving the guarded safe_divide
/// alone.
#[test]
fn test_e2e_real_rustc_strict_policy_refuses_unsafe_fixture() {
    let rustc = require_trust_rustc();

    let tmp = tempfile::tempdir().unwrap();
    let src_path = tmp.path().join("test_strict.rs");
    std::fs::write(&src_path, TEST_SOURCE).unwrap();

    let mut cmd = verified_lib_command_with_args(
        &rustc,
        &src_path,
        &tmp.path().join("test_strict.rlib"),
        &["-Z", "trust-verify-output=json"],
    );
    let (output, command_line) = run_rustc_command("strict-policy compile", &mut cmd);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "the strict default policy compiled TEST_SOURCE although raw_divide's `a / b`, \
         midpoint's `b - a` and add_five's `x + 5` are refutable.\n{}",
        rustc_failure_diagnostic("strict-policy compile", &rustc, &command_line, &output)
    );

    let error_lines: Vec<&str> = stderr.lines().filter(|line| line.starts_with("error")).collect();
    for name in ["raw_divide", "midpoint", "add_five"] {
        assert!(
            error_lines.iter().any(|line| line.contains(&format!("::{name}`"))),
            "strict compile should refuse `{name}`; error lines: {error_lines:#?}"
        );
    }
    assert!(
        !error_lines.iter().any(|line| line.contains("::safe_divide`")),
        "strict compile refused the guarded `safe_divide`; error lines: {error_lines:#?}"
    );
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Load all VerifiableFunction JSON files from a directory. Fails closed: an
/// unreadable directory, entry or file, or a fixture this tree's
/// `VerifiableFunction` cannot parse (a compiler older than the checkout),
/// panics instead of silently shrinking the set the pipeline then verifies.
fn load_mir_fixtures_from_dir(dir: &Path) -> Vec<VerifiableFunction> {
    let entries = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("failed to read MIR dump dir {}: {e}", dir.display()));

    let mut functions = Vec::new();
    for entry in entries {
        let entry =
            entry.unwrap_or_else(|e| panic!("failed to read an entry of {}: {e}", dir.display()));
        let path = entry.path();
        if path.extension().is_none_or(|ext| ext != "json") {
            continue;
        }
        let json = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));
        let func = serde_json::from_str::<VerifiableFunction>(&json).unwrap_or_else(|e| {
            panic!(
                "failed to parse {} as VerifiableFunction: {e} (a compiler older than this \
                 checkout dumps an older schema; rebuild it)",
                path.display()
            )
        });
        functions.push(func);
    }

    functions
}

// ---------------------------------------------------------------------------
// Discovery self-tests: the fail-closed paths, hermetic (no Trust rustc needed)
// ---------------------------------------------------------------------------

/// FLAG_SURFACE's parent: the last revision whose fork rejects `-Ztrust-policy`.
const FLAG_SURFACE_PARENT: &str = "b383be6a5bc6193d59f2f3fee990a3589a5acf7a";

// Regression (2026-09-30): with nothing to measure, every test in this file
// printed SKIPPING and passed. Now nothing to measure is an error that says what
// was searched and how to build a compiler.
#[test]
fn discovery_without_any_compiler_fails_closed() {
    let root = tempfile::tempdir().unwrap();
    let why = resolve_trust_rustc_from(root.path(), None, None)
        .expect_err("no compiler anywhere must be an error, not a selection");
    assert!(
        why.contains("No executable Trust rustc found") && why.contains("x.py build --stage 1"),
        "{why}"
    );
    // An empty TRUST_RUSTC is unset, not a path.
    let why = resolve_trust_rustc_from(root.path(), Some("".into()), None)
        .expect_err("an empty TRUST_RUSTC with no compiler must be an error");
    assert!(why.contains("No executable Trust rustc found"), "{why}");
}

/// TRUST_RUSTC is authoritative: one that names no file is an error even
/// against this checkout, where discovery may well find a compiler, instead of
/// silently measuring a discovered one in its place.
#[test]
fn discovery_trust_rustc_naming_no_file_is_an_error_not_a_fallback() {
    let dir = tempfile::tempdir().unwrap();
    let missing = dir.path().join("no-such-rustc");
    let why = resolve_trust_rustc_from(&find_repo_root(), Some(missing.into_os_string()), None)
        .expect_err("a missing TRUST_RUSTC must be an error");
    assert!(
        why.contains("TRUST_RUSTC=")
            && why.contains("no-such-rustc")
            && why.contains("authoritative"),
        "{why}"
    );
    // A directory is not a compiler either.
    let why =
        resolve_trust_rustc_from(&find_repo_root(), Some(dir.path().as_os_str().to_owned()), None)
            .expect_err("a directory TRUST_RUSTC must be an error");
    assert!(why.contains("is not an executable file"), "{why}");
}

/// A discovered executable that is not a Trust rustc fails the capability
/// probe instead of being skipped. `true` stands in for it: it exits 0 on any
/// command line and prints nothing, like a compiler without the verify pass.
#[cfg(unix)]
#[test]
fn discovery_non_trust_compiler_fails_the_capability_probe() {
    let true_bin = ["/usr/bin/true", "/bin/true"]
        .into_iter()
        .map(Path::new)
        .find(|path| is_executable_file(path))
        .expect("no `true` binary at /usr/bin/true or /bin/true");
    let root = tempfile::tempdir().unwrap();
    let bin = root.path().join("build/host/stage1/bin");
    fs::create_dir_all(&bin).unwrap();
    std::os::unix::fs::symlink(true_bin, bin.join("rustc")).unwrap();

    let why = resolve_trust_rustc_from(root.path(), None, None)
        .expect_err("a non-Trust compiler must fail the capability probe");
    assert!(why.contains("emitted no parseable `function_result` transport"), "{why}");
    assert!(why.contains("build/host/stage1/bin/rustc"), "the failure names the compiler: {why}");
}

/// Only a negative ancestry answer marks a fork stale, and a stale fork's
/// identity, which every failure message carries, says so.
#[test]
fn discovery_flag_surface_ancestry_and_stale_identity() {
    let root = find_repo_root();
    let at = provenance(&root, FLAG_SURFACE, Some(FLAG_SURFACE));
    let parent = provenance(&root, FLAG_SURFACE, Some(FLAG_SURFACE_PARENT));
    assert_ne!(at, Provenance::Predates, "a revision contains itself");
    assert_ne!(parent, Provenance::Contains, "FLAG_SURFACE's parent cannot contain it");
    // A clone without these commits (a history-rewritten snapshot) answers
    // Unknown for both, which is still neither wrong answer above.
    let knows_surface = Command::new("git")
        .arg("-C")
        .arg(&root)
        .args(["cat-file", "-e", &format!("{FLAG_SURFACE}^{{commit}}")])
        .status()
        .is_ok_and(|status| status.success());
    if knows_surface {
        assert_eq!(at, Provenance::Contains);
        assert_eq!(parent, Provenance::Predates);
    }
    assert!(matches!(provenance(&root, FLAG_SURFACE, None), Provenance::Unknown(_)));

    let stale = TrustRustc {
        path: PathBuf::from("build/host/stage1/bin/rustc"),
        commit: Some(FLAG_SURFACE_PARENT.to_string()),
        surface: Provenance::Predates,
        min_fix: None,
        behind_head: Some(1234),
    };
    let identity = stale.identity();
    assert!(
        identity.contains(FLAG_SURFACE_PARENT)
            && identity.contains(&format!("PREDATES {}", &FLAG_SURFACE[..10]))
            && identity.contains("1234 commit(s) behind"),
        "{identity}"
    );
}
