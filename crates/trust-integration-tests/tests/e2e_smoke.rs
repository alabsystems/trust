// trust-integration-tests/tests/e2e_smoke.rs: E2E smoke test for the verification pipeline
//
// This is the ground truth for "does Trust actually verify Rust code?"
//
// Each test loads REAL compiler-extracted MIR from JSON fixtures produced by
// compiling tests/real_mir/src/test_functions.rs through rustc with
// -Ztrust-dump=mir:<dir>. No synthetic MIR. No mocks. No ConstantFolderBackend.
//
// Pipeline exercised:
//   Real .rs source -> rustc + -Ztrust-dump=mir:<dir> -> JSON fixture
//   -> serde deserialize -> build_v1_vcs -> ay (real solver)
//   -> proof-cert -> report
//
// Requirements: ay binary discoverable by the integration-test ay helper
//               (tests skip gracefully if absent).
//               MIR fixtures in fixtures/real_mir/ (tests skip if absent).
//
// Issue: #937 | Epic: #935
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use std::path::PathBuf;

use trust_integration_tests::ay_test_support::{ay_available, require_ay};
use trust_router::{MirRouter, MirRouterConfig, Router, VerificationBackend, build_v1_vcs};
use trust_types::*;

// ---------------------------------------------------------------------------
// Fixture loading helpers
// ---------------------------------------------------------------------------

/// Path to real MIR fixtures directory (extracted from real .rs compilation).
fn fixtures_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("fixtures").join("real_mir")
}

/// Load a single VerifiableFunction from a JSON fixture file.
///
/// Returns None if the fixture does not exist (tests skip gracefully).
fn load_fixture(name: &str) -> Option<VerifiableFunction> {
    let path = fixtures_dir().join(format!("{name}.json"));
    if !path.exists() {
        return None;
    }
    let json = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("failed to read fixture {}: {e}", path.display()));
    let func: VerifiableFunction = serde_json::from_str(&json)
        .unwrap_or_else(|e| panic!("failed to parse fixture {}: {e}", path.display()));
    Some(func)
}

/// Load all JSON fixtures from the fixtures directory.
fn load_all_fixtures() -> Vec<(String, VerifiableFunction)> {
    let dir = fixtures_dir();
    if !dir.exists() {
        return vec![];
    }
    let mut fixtures = Vec::new();
    for entry in std::fs::read_dir(&dir).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.extension().is_none_or(|ext| ext != "json") {
            continue;
        }
        let name = path.file_stem().unwrap().to_string_lossy().to_string();
        let json = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));
        match serde_json::from_str::<VerifiableFunction>(&json) {
            Ok(func) => fixtures.push((name, func)),
            Err(e) => eprintln!("WARNING: skipping invalid fixture {}: {e}", path.display()),
        }
    }
    fixtures
}

/// Create a MirRouter backed by real ay.
fn create_real_mir_router() -> MirRouter {
    let v1_router = Router::with_backends(vec![Box::new(require_ay())]);
    let config = MirRouterConfig { produce_proofs: true, ..MirRouterConfig::default() };
    MirRouter::new(v1_router, config)
}

// ===========================================================================
// Test 1: Division by variable -- ay finds counterexample (FAILED)
//
// Source: fn safe_divide(x: u32, y: u32) -> u32 { x / y }
// Fixture: test_functions__safe_divide.json (real compiler MIR)
//
// Expected: DivisionByZero VC, ay says SAT (y=0 is a valid counterexample).
// ===========================================================================

#[test]
fn test_e2e_real_mir_division_counterexample() {
    if !ay_available() {
        eprintln!("SKIP: ay not found by integration-test helper");
        return;
    }
    let func = match load_fixture("test_functions__safe_divide") {
        Some(f) => f,
        None => {
            eprintln!("SKIP: fixture test_functions__safe_divide.json not found");
            return;
        }
    };

    eprintln!("Source: fn safe_divide(x: u32, y: u32) -> u32 {{ x / y }}");
    eprintln!("Fixture: real compiler-extracted MIR from test_functions.rs");

    let ay = require_ay();

    // Step 1: Generate VCs from real MIR
    let vcs = build_v1_vcs(&func);
    eprintln!("Generated {} VCs for safe_divide", vcs.len());
    assert!(!vcs.is_empty(), "safe_divide should produce at least 1 VC (DivisionByZero)");

    let divzero_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::DivisionByZero)).collect();
    assert!(
        !divzero_vcs.is_empty(),
        "safe_divide(x/y) should produce DivisionByZero VCs, got none"
    );

    // Step 2: Verify with real ay
    let mut results: Vec<(VerificationCondition, VerificationResult)> = Vec::new();
    for vc in &vcs {
        let result = ay.verify(vc);
        eprintln!("  ay result for {:?}: {:?}", vc.kind, result);
        results.push((vc.clone(), result));
    }

    // Step 3: Assert ay finds the division-by-zero vulnerability
    let failed_count = results.iter().filter(|(_, r)| r.is_failed()).count();
    assert!(
        failed_count >= 1,
        "ay must find division-by-zero is possible (y=0). Got {failed_count} failed"
    );

    // Step 4: Generate verification report
    let report = trust_report::build_json_report("e2e_smoke_real", &results);
    assert!(report.summary.total_failed >= 1, "report should show at least 1 failed");
    assert_eq!(
        report.summary.verdict,
        CrateVerdict::HasViolations,
        "report verdict should be HasViolations for unsafe division"
    );

    let text = trust_report::format_json_summary(&report);
    eprintln!("\n{text}");

    eprintln!("\n=== E2E REAL MIR: safe_divide FAILED with counterexample from real ay ===");
}

// ===========================================================================
// Test 2: Checked overflow -- ay proves assertion (PROVED)
//
// Source: fn checked_add(a: u32, b: u32) -> u32 { a + b }
// Fixture: test_functions__checked_add.json (real compiler MIR)
//
// Expected: ArithmeticOverflow(Add) VC from Assert terminator, ay proves
// the assertion condition (Formula::Bool(false) -> UNSAT -> Proved).
// ===========================================================================

#[test]
fn test_e2e_real_mir_overflow_proved() {
    if !ay_available() {
        eprintln!("SKIP: ay not found by integration-test helper");
        return;
    }
    let func = match load_fixture("test_functions__checked_add") {
        Some(f) => f,
        None => {
            eprintln!("SKIP: fixture test_functions__checked_add.json not found");
            return;
        }
    };

    eprintln!("Source: fn checked_add(a: u32, b: u32) -> u32 {{ a + b }}");
    eprintln!("Fixture: real compiler-extracted MIR from test_functions.rs");

    let ay = require_ay();

    // Step 1: Generate VCs from real MIR
    let vcs = build_v1_vcs(&func);
    eprintln!("Generated {} VCs for checked_add", vcs.len());
    assert!(!vcs.is_empty(), "checked_add should produce at least 1 VC (ArithmeticOverflow)");

    let overflow_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .collect();
    assert_eq!(overflow_vcs.len(), 1, "checked_add should produce 1 ArithmeticOverflow(Add) VC");

    // Step 2: Verify with real ay
    let mut results: Vec<(VerificationCondition, VerificationResult)> = Vec::new();
    for vc in &vcs {
        let result = ay.verify(vc);
        eprintln!("  ay result for {:?}: {:?}", vc.kind, result);
        results.push((vc.clone(), result));
    }

    // Step 3: Assert ay proves the overflow assertion
    let proved_count = results.iter().filter(|(_, r)| r.is_proved()).count();
    assert!(
        proved_count >= 1,
        "ay must prove overflow assertion from real MIR. Got {proved_count} proved"
    );

    // Step 4: Generate proof certificate
    let cert_result = trust_proof_cert::generate_certificate_record(&func, &results);
    assert!(
        cert_result.is_ok(),
        "proof certificate generation should succeed: {:?}",
        cert_result.err()
    );
    let cert = cert_result.unwrap();
    eprintln!("Certificate record: digest={}", cert.record_digest);
    assert!(!cert.record_digest.is_empty(), "record digest should be non-empty");

    // Step 5: Generate verification report
    //
    // ay reports this overflow obligation as `Proved{assurance: Unchecked}`
    // (smt_unsat_unvalidated -- the Alethe cert is captured but not independently
    // validated on the subprocess path). `build_json_report` applies the
    // `SmtBacked` assurance floor (report_builder.rs:318), which downgrades an
    // Unchecked proof into the runtime-checked lane. So at the report level the
    // obligation is RUNTIME CHECKED, not PROVED. This is the intentional assurance
    // floor, not a lost proof.
    let report = trust_report::build_json_report("e2e_smoke_real", &results);
    assert!(
        report.summary.total_runtime_checked >= 1,
        "report should show at least 1 runtime-checked (overflow obligation downgraded \
         from Proved{{Unchecked}} by the SmtBacked assurance floor)"
    );
    assert_eq!(
        report.summary.total_proved, 0,
        "no obligation clears the SmtBacked floor, so report shows 0 proved"
    );

    let text = trust_report::format_json_summary(&report);
    eprintln!("\n{text}");
    assert!(
        text.contains("RUNTIME CHECKED"),
        "text report should contain RUNTIME CHECKED for the floor-downgraded overflow obligation"
    );

    eprintln!("\n=== E2E REAL MIR: checked_add overflow RUNTIME CHECKED by real ay ===");
}

// ===========================================================================
// Test 3: Full pipeline across ALL real MIR fixtures
//
// Source: all functions in fixtures/real_mir/src/test_functions.rs
// Fixtures: all *.json files in fixtures/real_mir/
//
// Expected: at least 1 proved (checked_add), at least 1 failed (safe_divide).
// ===========================================================================

#[test]
fn test_e2e_real_mir_full_pipeline() {
    if !ay_available() {
        eprintln!("SKIP: ay not found by integration-test helper");
        return;
    }
    let fixtures = load_all_fixtures();
    if fixtures.is_empty() {
        eprintln!("SKIP: no real MIR fixtures found. Run: ./scripts/generate_mir_fixtures.sh");
        return;
    }

    eprintln!("Loaded {} real MIR fixtures", fixtures.len());

    let mut all_results: Vec<(VerificationCondition, VerificationResult)> = Vec::new();
    let mut total_vcs = 0usize;

    for (name, func) in &fixtures {
        let vcs = build_v1_vcs(func);
        if vcs.is_empty() {
            eprintln!("  {name}: 0 VCs (no arithmetic hazards)");
            continue;
        }

        let ay = require_ay();
        for vc in &vcs {
            let result = ay.verify(vc);
            all_results.push((vc.clone(), result));
        }
        total_vcs += vcs.len();
        eprintln!("  {name}: {} VCs verified", vcs.len());
    }

    eprintln!("\nTotal: {} VCs across {} fixtures", total_vcs, fixtures.len());

    // Build combined report
    let report = trust_report::build_json_report("e2e_smoke_real_all", &all_results);
    let text = trust_report::format_json_summary(&report);
    eprintln!("\n{text}");

    // Acceptance criteria
    assert!(
        report.summary.total_obligations > 0,
        "real MIR fixtures should produce at least some VCs"
    );
    // checked_add's overflow obligation is reported `Proved{Unchecked}` by ay and
    // downgraded to the runtime-checked lane by the `SmtBacked` assurance floor
    // (report_builder.rs:318), so it lands in `total_runtime_checked`, not
    // `total_proved`. This is the intentional assurance floor.
    assert!(
        report.summary.total_runtime_checked >= 1,
        "at least one VC should be runtime-checked (checked_add overflow obligation, \
         downgraded from Proved{{Unchecked}} by the SmtBacked floor). Got {} runtime-checked",
        report.summary.total_runtime_checked
    );
    assert!(
        report.summary.total_failed >= 1,
        "at least one VC should be failed (safe_divide div-by-zero). Got {} failed",
        report.summary.total_failed
    );

    eprintln!(
        "\n=== E2E REAL MIR FULL PIPELINE: {} proved, {} failed, {} unknown ===",
        report.summary.total_proved, report.summary.total_failed, report.summary.total_unknown,
    );
}

// ===========================================================================
// Test 4: Pipeline-v2 MirRouter with real ay on real MIR
//
// Exercises MirRouter classification and dispatch on real compiler MIR,
// plus v1 VC-level verification for the combined report.
// ===========================================================================

#[test]
fn test_e2e_real_mir_pipeline_v2_router() {
    if !ay_available() {
        eprintln!("SKIP: ay not found by integration-test helper");
        return;
    }
    let fixtures = load_all_fixtures();
    if fixtures.is_empty() {
        eprintln!("SKIP: no real MIR fixtures found. Run: ./scripts/generate_mir_fixtures.sh");
        return;
    }

    let mir_router = create_real_mir_router();

    eprintln!("\n=== E2E REAL MIR: MirRouter pipeline-v2 dispatch ===");

    let mut all_results: Vec<(VerificationCondition, VerificationResult)> = Vec::new();
    let mut proved_functions = 0u32;
    let mut failed_functions = 0u32;

    for (name, func) in &fixtures {
        let strategy = mir_router.classify(func);
        let result = mir_router.verify_function(func);
        eprintln!("  {name}: strategy={strategy:?}, result={result:?}");

        // Also build v1 VCs for per-VC results
        let vcs = build_v1_vcs(func);
        if !vcs.is_empty() {
            let ay = require_ay();
            for vc in &vcs {
                let vc_result = ay.verify(vc);
                all_results.push((vc.clone(), vc_result));
            }
        }

        if result.is_proved() {
            proved_functions += 1;
        } else if result.is_failed() {
            failed_functions += 1;
        }
    }

    // Generate combined report
    let report = trust_report::build_json_report("e2e_smoke_v2_real", &all_results);
    let text = trust_report::format_json_summary(&report);
    eprintln!("\n{text}");

    // Acceptance criteria
    //
    // The checked_add overflow obligation is reported `Proved{Unchecked}` by ay and
    // downgraded into the runtime-checked lane by the `SmtBacked` assurance floor
    // (report_builder.rs:318), so the report shows it as runtime-checked, not proved.
    assert!(
        report.summary.total_runtime_checked >= 1,
        "at least one VC should be runtime-checked (overflow obligation downgraded from \
         Proved{{Unchecked}} by the SmtBacked floor). Got {} runtime-checked",
        report.summary.total_runtime_checked
    );
    assert!(
        report.summary.total_failed >= 1,
        "at least one VC should be failed. Got {} failed",
        report.summary.total_failed
    );
    assert!(
        report.summary.functions_analyzed >= 2,
        "report should analyze at least 2 functions. Got {}",
        report.summary.functions_analyzed
    );

    // Verify JSON serialization roundtrip
    let json = serde_json::to_string_pretty(&report).unwrap();
    let roundtrip: JsonProofReport = serde_json::from_str(&json).unwrap();
    assert_eq!(roundtrip.summary.total_proved, report.summary.total_proved);
    assert_eq!(roundtrip.summary.total_runtime_checked, report.summary.total_runtime_checked);

    eprintln!(
        "\n=== E2E REAL MIR pipeline-v2: {} functions proved, {} failed out of {} total ===",
        proved_functions,
        failed_functions,
        fixtures.len(),
    );
}

// ===========================================================================
// Test 5: M2 milestone demonstration with real MIR
//
// The "money test" -- proves the full pipeline works on real compiler output:
//   Real .rs -> real MIR (fixture) -> build_v1_vcs -> ay -> proof cert -> report
//
// This is the test that demonstrates M2 milestone completion with REAL code.
// ===========================================================================

#[test]
fn test_e2e_real_mir_m2_demonstration() {
    if !ay_available() {
        eprintln!("SKIP: ay not found by integration-test helper");
        return;
    }
    let func = match load_fixture("test_functions__checked_add") {
        Some(f) => f,
        None => {
            eprintln!("SKIP: fixture test_functions__checked_add.json not found");
            return;
        }
    };

    eprintln!("\n=== E2E REAL MIR: Full pipeline M2 demonstration ===\n");
    eprintln!("Source: fn checked_add(a: u32, b: u32) -> u32 {{ a + b }}");
    eprintln!("Origin: fixtures/real_mir/src/test_functions.rs (compiled via -Ztrust-dump=mir:<dir>)");
    eprintln!();

    let ay = require_ay();

    // Phase 1: VC generation from real MIR
    let vcs = build_v1_vcs(&func);
    eprintln!("Phase 1 (build_v1_vcs): {} verification conditions generated", vcs.len());
    for vc in &vcs {
        eprintln!("  - {:?} at {:?}", vc.kind, vc.location);
    }

    // Phase 2: Real ay verification
    let mut results: Vec<(VerificationCondition, VerificationResult)> = Vec::new();
    for vc in &vcs {
        let result = ay.verify(vc);
        let status = if result.is_proved() {
            "PROVED"
        } else if result.is_failed() {
            "FAILED"
        } else {
            "UNKNOWN"
        };
        eprintln!("Phase 2 (ay): {:?} -> {status}", vc.kind);
        results.push((vc.clone(), result));
    }

    // Phase 3: Proof certificate
    let cert = trust_proof_cert::generate_certificate_record(&func, &results)
        .expect("certificate-record generation should succeed for real MIR");
    eprintln!("Phase 3 (proof-cert): record digest = {}", cert.record_digest);
    eprintln!(
        "  {} VC entries, primary proved: {}",
        cert.vc_entries.len(),
        cert.vc_entries.iter().any(|entry| entry.reported_proved)
    );

    // Phase 4: Verification report
    let report = trust_report::build_json_report("e2e_real_mir_m2", &results);
    eprintln!(
        "Phase 4 (report): verdict = {:?}, {} proved / {} failed / {} unknown",
        report.summary.verdict,
        report.summary.total_proved,
        report.summary.total_failed,
        report.summary.total_unknown,
    );

    let text = trust_report::format_json_summary(&report);
    eprintln!("\n--- Verification Report ---");
    eprintln!("{text}");
    eprintln!("--- End Report ---\n");

    // Final assertions: M2 acceptance check with REAL compiler MIR.
    //
    // ay proves the checked_add overflow obligation but reports it as
    // `Proved{assurance: Unchecked}` (the Alethe cert is captured but not
    // independently validated on the subprocess path). `build_json_report`
    // applies the `SmtBacked` assurance floor (report_builder.rs:318), which
    // downgrades the Unchecked proof into the runtime-checked lane. So the M2
    // report surfaces the obligation as RUNTIME CHECKED, not PROVED -- this is
    // the intentional assurance floor, the obligation is still discharged.
    assert!(
        report.summary.total_runtime_checked >= 1,
        "M2: at least one function has at least one runtime-checked VC (overflow \
         obligation downgraded from Proved{{Unchecked}} by the SmtBacked floor)"
    );
    assert!(!cert.record_digest.is_empty(), "M2: certificate record was generated");
    assert!(
        text.contains("RUNTIME CHECKED"),
        "M2: verification report shows RUNTIME CHECKED status for the floor-downgraded obligation"
    );

    // Verify JSON serialization roundtrip
    let json = serde_json::to_string_pretty(&report).unwrap();
    let roundtrip: JsonProofReport = serde_json::from_str(&json).unwrap();
    assert_eq!(roundtrip.summary.total_proved, report.summary.total_proved);

    eprintln!("=== E2E REAL MIR: M2 milestone DEMONSTRATED with real compiler MIR ===");
    eprintln!(
        "  checked_add: {} proved VCs, certificate hash: {}",
        report.summary.total_proved,
        &cert.record_digest[..16]
    );
}
