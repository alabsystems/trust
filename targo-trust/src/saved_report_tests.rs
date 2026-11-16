// Tests for crate::saved_report: the canonical loader's first-pass receipt,
// its bounds, and the refusal of every non-canonical format.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fs;
use std::path::PathBuf;

use trust_types::determinism::BudgetProfile;
use trust_types::*;

use super::*;

fn test_gate_determinism(profile: BudgetProfile) -> trust_types::determinism::GateDeterminism {
    let vector = trust_types::determinism::VerdictVector::default();
    trust_types::determinism::GateDeterminism {
        outcome: trust_types::determinism::UnitOutcome::Measured,
        budget_profile_id: profile.id(),
        budget_profile: profile,
        vector_digest: vector.digest(),
        stop_causes: trust_types::determinism::StopCauseTally::default(),
        stop_items: trust_types::determinism::StopItemTally::default(),
        vector: Vec::new(),
        volatile_keys: Vec::new(),
        unkeyed_functions: Vec::new(),
        noted_stops: Vec::new(),
    }
}

fn forged_canonical_proved_report_without_evidence() -> JsonProofReport {
    let obligation = ObligationReport {
        assumes: Vec::new(),
        obligation_id: Some("obl-forged".to_string()),
        description: "forged proof row".to_string(),
        kind: "postcondition".to_string(),
        proof_level: ProofLevel::L0Safety,
        location: None,
        outcome: ObligationOutcome::Proved { strength: ProofStrength::deductive() },
        solver: "forged".to_string(),
        time_ms: 5,
        evidence: None,
        proof_evidence: None,
        transport_evidence: None,
    };
    JsonProofReport {
        metadata: ReportMetadata {
            schema_version: "1.0".to_string(),
            trust_version: "forged-test".to_string(),
            timestamp: String::new(),
            total_time_ms: 5,
        },
        crate_name: "forged".to_string(),
        summary: CrateSummary {
            functions_analyzed: 1,
            functions_verified: 1,
            functions_runtime_checked: 0,
            functions_with_violations: 0,
            functions_inconclusive: 0,
            total_obligations: 1,
            total_proved: 1,
            total_runtime_checked: 0,
            total_failed: 0,
            total_unknown: 0,
            total_timed_out: 0,
            total_design_requirements: 0,
            total_failed_unproved: 0,
            total_unattributed_failed: 0,
            total_unattributed_unknown: 0,
            total_unattributed_proved: 0,
            proof_grade_engine_statuses: vec![],
            verdict: CrateVerdict::Verified,
        },
        functions: vec![FunctionProofReport {
            function: "fixture::forged".to_string(),
            summary: FunctionSummary {
                total_obligations: 1,
                proved: 1,
                runtime_checked: 0,
                failed: 0,
                unknown: 0,
                timed_out: 0,
                design_requirements: 0,
                failed_unproved: 0,
                unattributed_failed: 0,
                unattributed_unknown: 0,
                unattributed_proved: 0,
                total_time_ms: 5,
                max_proof_level: Some(ProofLevel::L0Safety),
                verdict: FunctionVerdict::Verified,
            },
            obligations: vec![obligation],
        }],
        hardened: None,
        assumptions: Vec::new(),
        cargo_proof_inventory: None,
        verification_gate: None,
    }
}

fn canonical_runtime_checked_report() -> JsonProofReport {
    let mut report = forged_canonical_proved_report_without_evidence();
    report.functions[0].obligations[0].outcome =
        ObligationOutcome::RuntimeChecked { note: Some("certified monitor installed".to_string()) };
    report.functions[0].summary.proved = 0;
    report.functions[0].summary.runtime_checked = 1;
    report.functions[0].summary.verdict = FunctionVerdict::RuntimeChecked;
    report.summary.functions_verified = 0;
    report.summary.functions_runtime_checked = 1;
    report.summary.total_proved = 0;
    report.summary.total_runtime_checked = 1;
    report.summary.verdict = CrateVerdict::RuntimeChecked;
    report.verification_gate = Some(VerificationGateReport {
        lane: "advisory".to_string(),
        verification_level: Some("L0".to_string()),
        decision: "conditional-pass".to_string(),
        exit_code: 0,
        counts: VerificationGateCounts {
            total: 1,
            proved: 0,
            failed: 0,
            unknown: 0,
            runtime_checked: 1,
            assumed: 0,
            mandated: 0,
            contract_panics: 0,
            excluded: 0,
        },
        conditional_on_assumption_rows: false,
        conditional_on_dependency_entries: false,
        conditional_on_runtime_checks: true,
        conditional_on_unknown_rows: false,
        conditional_on_visitation_entries: false,
        coverage: None,
        test_execution: None,
        exclusions: Vec::new(),
        determinism: Some(test_gate_determinism(BudgetProfile::builtin())),
        failure_sites: None,
        project_requirements: None,
    });
    report
}

fn report_path(dir: &tempfile::TempDir, name: &str) -> PathBuf {
    dir.path().join(format!("{name}.json"))
}

fn write_json_report(path: &Path, report: &JsonProofReport) {
    fs::write(path, serde_json::to_vec_pretty(report).expect("serialize report"))
        .expect("write report");
}

#[test]
fn a_schema_3_budget_profile_is_refused_by_name() {
    let dir = tempfile::tempdir().expect("tempdir");
    let current = canonical_runtime_checked_report();
    let path = report_path(&dir, "budget-profile-schema-3");
    write_json_report(&path, &current);
    // Rewrite the saved profile into the shape the deployed seal writes
    // (schema 3: lane fields and per-field bounds, no effort scale).
    let mut saved: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&path).expect("read the saved report"))
            .expect("the saved report is JSON");
    let profile = saved
        .pointer_mut("/verification_gate/determinism/budget_profile")
        .expect("the saved report records its budget profile");
    *profile = serde_json::json!({
        "schema": 3, "name": "builtin", "function_budget_steps": 64_000_000,
        "vc_timeout_ms": 5000, "function_budget_ms": 120_000, "worker_threads": 0
    });
    fs::write(&path, serde_json::to_vec_pretty(&saved).expect("serialize")).expect("write");

    let error = load_report(&path).expect_err("a schema-3 report does not load");
    assert!(
        error.contains("budget profile schema 3 is not readable")
            && error.contains("regenerate the report"),
        "the refusal names the schema: {error}"
    );

    // Control: the same report as written loads, so the refusal is about
    // the schema-3 block and nothing else.
    let control_path = report_path(&dir, "budget-profile-schema-current");
    write_json_report(&control_path, &current);
    load_report(&control_path).expect("the current-schema control loads");
}

#[test]
fn load_report_returns_sanitized_canonical_report_and_first_pass_provenance() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = report_path(&dir, "canonical-forged");
    write_json_report(&path, &forged_canonical_proved_report_without_evidence());

    let loaded = load_report(&path).expect("observational load must remain available");

    assert_eq!(loaded.sanitization.downgraded_proved, 1);
    assert_eq!(loaded.sanitization.evidence_defects, 1);
    assert_eq!(loaded.report.summary.total_proved, 0);
    assert_eq!(loaded.report.summary.total_unknown, 1);
    assert_eq!(loaded.report.summary.verdict, CrateVerdict::Inconclusive);
    let error = loaded
        .reject_unreplayed_proved_claims(&path)
        .expect_err("proof consumption must require verifier replay");
    assert!(error.contains("saved report authority gate failed"), "{error}");
    assert!(error.contains("lacked live verifier replay authority"), "{error}");
}

#[test]
fn load_report_downgrades_runtime_claim_and_reports_first_pass_provenance() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = report_path(&dir, "canonical-runtime");
    write_json_report(&path, &canonical_runtime_checked_report());

    let loaded = load_report(&path).expect("observational load must remain available");

    assert_eq!(loaded.sanitization.downgraded_proved, 0);
    assert_eq!(loaded.sanitization.downgraded_runtime_checked, 1);
    assert_eq!(loaded.sanitization.evidence_defects, 0);
    assert_eq!(loaded.report.summary.total_runtime_checked, 0);
    assert_eq!(loaded.report.summary.total_unknown, 1);
    assert_eq!(loaded.report.summary.verdict, CrateVerdict::Inconclusive);
    let gate = loaded.report.verification_gate.as_ref().expect("diagnostic gate");
    assert_eq!(gate.counts.runtime_checked, 0);
    assert_eq!(gate.counts.unknown, 1);
    assert!(!gate.conditional_on_runtime_checks);
    assert!(
        loaded.reject_unreplayed_proved_claims(&path).is_ok(),
        "runtime authority defects must not be mislabeled as proof-evidence defects"
    );
}

#[test]
fn load_report_rejects_oversized_file_before_json_deserialization() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = report_path(&dir, "oversized");
    let file = fs::File::create(&path).expect("create sparse report");
    file.set_len(MAX_SAVED_PROOF_REPORT_BYTES as u64 + 1).expect("extend sparse report");

    let error = load_report(&path).expect_err("oversized saved report must be bounded");

    assert!(error.contains("safety limit"), "{error}");
}

#[test]
fn a_malformed_canonical_report_is_refused() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = report_path(&dir, "canonical-malformed");
    let mut malformed = serde_json::to_value(forged_canonical_proved_report_without_evidence())
        .expect("serialize canonical fixture");
    malformed["functions"] = serde_json::json!("not an array");
    fs::write(&path, serde_json::to_vec_pretty(&malformed).expect("serialize malformed fixture"))
        .expect("write malformed canonical report");

    let error = load_report(&path).expect_err("malformed canonical input is refused");

    assert!(error.contains("failed to parse"), "{error}");
}

/// T9, no legacy decode path: the pre-canonical `{ results: [...] }` saved
/// report is refused, not converted — even a well-formed one.
#[test]
fn a_pre_canonical_results_report_is_refused_not_converted() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = report_path(&dir, "legacy-results");
    fs::write(
        &path,
        serde_json::to_vec_pretty(&serde_json::json!({
            "results": [{
                "kind": "postcondition",
                "message": "legacy forged proof row",
                "outcome": "Proved",
                "backend": "forged",
                "time_ms": 5
            }]
        }))
        .expect("serialize legacy fixture"),
    )
    .expect("write legacy fixture");

    let error = load_report(&path).expect_err("an older format is never read");
    assert!(error.contains("no older saved report format is read"), "{error}");
}
