//! Tests for trust-report core functionality.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap; // Trust: BTreeMap for deterministic output

use sha2::{Digest, Sha256};
use trust_types::*;

use crate::crate_report::{
    append_dep_tcb_ledger, build_crate_verification_report,
    build_crate_verification_report_with_policy, format_crate_verification_summary,
};
use crate::formatting::proof_evidence_label;
use crate::legacy::{build_report, format_summary};
use crate::report_builder::vc_kind_tag;
use crate::{
    SCHEMA_VERSION, TRUST_VERSION, build_json_report, build_json_report_from_annotations,
    build_json_report_with_policy, format_json_summary, write_json_report, write_ndjson,
    write_ndjson_report,
};

fn annotation_obligation(
    description: &str,
    kind: &str,
    status: AnnotationStatus,
    proof_level: ProofLevel,
    time_ms: u64,
    location: Option<SourceSpan>,
) -> ObligationAnnotation {
    ObligationAnnotation {
        description: description.to_string(),
        kind: kind.to_string(),
        proof_level,
        status,
        strength: matches!(status, AnnotationStatus::Proved).then_some(ProofStrength::smt_unsat()),
        solver: "ay".into(),
        time_ms,
        location,
        counterexample: matches!(status, AnnotationStatus::Failed)
            .then(|| Counterexample::new(vec![("x".to_string(), CounterexampleValue::Int(-1))])),
        fingerprint: [1, 2],
    }
}

fn annotation_summary(obligations: &[ObligationAnnotation]) -> AnnotationSummary {
    AnnotationSummary {
        total: obligations.len(),
        proved: obligations
            .iter()
            .filter(|obligation| obligation.status == AnnotationStatus::Proved)
            .count(),
        failed: obligations
            .iter()
            .filter(|obligation| obligation.status == AnnotationStatus::Failed)
            .count(),
        unknown: obligations
            .iter()
            .filter(|obligation| {
                matches!(obligation.status, AnnotationStatus::Unknown | AnnotationStatus::Timeout)
            })
            .count(),
        runtime_checked: obligations
            .iter()
            .filter(|obligation| obligation.status == AnnotationStatus::RuntimeChecked)
            .count(),
        max_level: obligations.iter().map(|obligation| obligation.proof_level).max(),
    }
}

fn proof_annotation(
    function_name: &str,
    function_path: &str,
    obligations: Vec<ObligationAnnotation>,
) -> ProofAnnotation {
    ProofAnnotation {
        function_name: function_name.to_string(),
        function_path: function_path.to_string(),
        summary: annotation_summary(&obligations),
        obligations,
        certificate: Some(ProofCertificateRef {
            prover: "ay".to_string(),
            vc_fingerprint: [7, 11],
            prover_version: "1.0.0".to_string(),
        }),
    }
}

/// Build a standard test fixture with mixed results for get_midpoint.
fn midpoint_results() -> Vec<(VerificationCondition, VerificationResult)> {
    vec![
        (
            VerificationCondition {
                kind: VcKind::ArithmeticOverflow {
                    op: BinOp::Add,
                    operand_tys: (Ty::usize(), Ty::usize()),
                },
                function: "get_midpoint".into(),
                location: SourceSpan {
                    file: "src/midpoint.rs".to_string(),
                    line_start: 5,
                    col_start: 5,
                    line_end: 5,
                    col_end: 10,
                },
                formula: Formula::Bool(true),
                contract_metadata: None,
                obligation: None,
            },
            VerificationResult::Failed {
                solver: "ay".into(),
                time_ms: 3,
                counterexample: Some(Counterexample::new(vec![
                    ("a".to_string(), CounterexampleValue::Uint(u64::MAX as u128)),
                    ("b".to_string(), CounterexampleValue::Uint(1)),
                ])),
            },
        ),
        (
            VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: "get_midpoint".into(),
                location: SourceSpan {
                    file: "src/midpoint.rs".to_string(),
                    line_start: 5,
                    col_start: 18,
                    line_end: 5,
                    col_end: 23,
                },
                formula: Formula::Bool(false),
                contract_metadata: None,
                obligation: None,
            },
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        ),
    ]
}

/// Build test data with multiple functions and all outcome types.
fn multi_function_results() -> Vec<(VerificationCondition, VerificationResult)> {
    let mut results = midpoint_results();
    results.push((
        VerificationCondition {
            kind: VcKind::IndexOutOfBounds,
            function: "lookup".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        },
        VerificationResult::Unknown {
            solver: "ay".into(),
            time_ms: 50,
            reason: "nonlinear arithmetic".to_string(),
        },
    ));
    results.push((
        VerificationCondition {
            kind: VcKind::Postcondition,
            function: "compute".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        },
        VerificationResult::Timeout { solver: "ay".into(), timeout_ms: 5000 },
    ));
    results.push((
        VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Mul,
                operand_tys: (Ty::i32(), Ty::i32()),
            },
            function: "compute".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        },
        VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: 2,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        },
    ));
    results
}

/// Build a report that contains a runtime-checked obligation.
fn runtime_checked_report() -> JsonProofReport {
    JsonProofReport {
        metadata: ReportMetadata {
            schema_version: SCHEMA_VERSION.to_string(),
            trust_version: TRUST_VERSION.to_string(),
            timestamp: "0".to_string(),
            total_time_ms: 11,
            timeout_ms: None,
            function_budget_ms: None,
        },
        crate_name: "runtime_checked".to_string(),
        summary: CrateSummary {
            proof_grade_engine_statuses: Vec::new(),
            functions_analyzed: 1,
            functions_verified: 0,
            functions_runtime_checked: 1,
            functions_with_violations: 0,
            functions_inconclusive: 0,
            total_obligations: 1,
            total_proved: 0,
            total_runtime_checked: 1,
            total_failed: 0,
            total_unknown: 0,
            total_timed_out: 0,
            total_design_requirements: 0,
            total_unattributed_failed: 0,
            total_unattributed_unknown: 0,
            total_unattributed_proved: 0,
            verdict: CrateVerdict::RuntimeChecked,
        },
        functions: vec![FunctionProofReport {
            function: "dynamic_check".into(),
            summary: FunctionSummary {
                total_obligations: 1,
                proved: 0,
                runtime_checked: 1,
                failed: 0,
                unknown: 0,
                timed_out: 0,
                design_requirements: 0,
                unattributed_failed: 0,
                unattributed_unknown: 0,
                unattributed_proved: 0,
                total_time_ms: 11,
                max_proof_level: Some(ProofLevel::L0Safety),
                verdict: FunctionVerdict::RuntimeChecked,
            },
            obligations: vec![ObligationReport {
                obligation_id: None,
                description: "runtime safety check".to_string(),
                kind: "postcondition".to_string(),
                proof_level: ProofLevel::L0Safety,
                location: Some(SourceSpan {
                    file: "src/runtime.rs".to_string(),
                    line_start: 10,
                    col_start: 1,
                    line_end: 10,
                    col_end: 12,
                }),
                outcome: ObligationOutcome::RuntimeChecked {
                    note: Some("validated by runtime instrumentation".to_string()),
                },
                solver: "runtime".into(),
                time_ms: 11,
                evidence: None,
                proof_evidence: None,
                transport_evidence: None,
            }],
        }],
        hardened: None,
        assumptions: Vec::new(),
        verification_gate: None,
        cargo_proof_inventory: None,
    }
}

// -----------------------------------------------------------------------
// Legacy API tests (backward compat)
// -----------------------------------------------------------------------

#[test]
fn test_build_and_format_report() {
    let results = midpoint_results();
    let report = build_report("midpoint", &results);
    assert_eq!(report.total_proved, 1);
    assert_eq!(report.total_failed, 1);
    assert_eq!(report.total_unknown, 0);
    assert_eq!(report.functions.len(), 1);
    assert_eq!(report.functions[0].function, "get_midpoint");

    let summary = format_summary(&report);
    assert!(summary.contains("PROVED"));
    assert!(summary.contains("FAILED"));
    assert!(summary.contains("counterexample"));

    let json = serde_json::to_string_pretty(&report).expect("serialize");
    assert!(json.contains("get_midpoint"));
}

// -----------------------------------------------------------------------
// JSON report construction tests
// -----------------------------------------------------------------------

#[test]
fn test_json_report_schema_version() {
    let report = build_json_report("test_crate", &[]);
    assert_eq!(report.metadata.schema_version, SCHEMA_VERSION);
    assert_eq!(report.metadata.trust_version, TRUST_VERSION);
}

#[test]
fn test_json_report_empty_crate() {
    let report = build_json_report("empty", &[]);
    assert_eq!(report.crate_name, "empty");
    assert_eq!(report.summary.functions_analyzed, 0);
    assert_eq!(report.summary.total_obligations, 0);
    assert_eq!(report.summary.verdict, CrateVerdict::NoObligations);
    assert!(report.functions.is_empty());
    assert!(report.cargo_proof_inventory.is_none());
    let serialized = serde_json::to_value(&report).expect("serialize direct report");
    assert!(
        serialized.get("cargo_proof_inventory").is_none(),
        "non-Cargo/direct report producers must omit Cargo inventory"
    );
}

#[test]
fn test_json_report_single_function_mixed_results() {
    let results = midpoint_results();
    let report = build_json_report("midpoint", &results);

    assert_eq!(report.crate_name, "midpoint");
    assert_eq!(report.summary.functions_analyzed, 1);
    assert_eq!(report.summary.total_obligations, 2);
    assert_eq!(report.summary.total_proved, 0);
    assert_eq!(report.summary.total_failed, 1);
    assert_eq!(report.summary.total_unknown, 1);
    assert_eq!(report.summary.verdict, CrateVerdict::HasViolations);
    assert_eq!(report.summary.functions_with_violations, 1);

    let func = &report.functions[0];
    assert_eq!(func.function, "get_midpoint");
    assert_eq!(func.summary.verdict, FunctionVerdict::HasViolations);
    assert_eq!(func.obligations.len(), 2);
}

#[test]
fn test_json_report_obligation_detail() {
    let results = midpoint_results();
    let report = build_json_report("midpoint", &results);

    let func = &report.functions[0];

    // Check the failed obligation (overflow)
    let overflow = func
        .obligations
        .iter()
        .find(|o| o.kind == "arithmetic_overflow_add")
        .expect("should have overflow obligation");
    assert_eq!(overflow.description, "arithmetic overflow (Add)");
    assert_eq!(overflow.proof_level, ProofLevel::L0Safety);
    assert_eq!(overflow.solver, "ay");
    assert_eq!(overflow.time_ms, 3);
    assert!(matches!(&overflow.outcome, ObligationOutcome::Failed { counterexample: Some(_) }));

    // Check counterexample variables
    if let ObligationOutcome::Failed { counterexample: Some(cex) } = &overflow.outcome {
        assert_eq!(cex.variables.len(), 2);
        assert_eq!(cex.variables[0].name, "a");
        assert_eq!(cex.variables[0].value, "18446744073709551615");
        assert_eq!(cex.variables[0].value_type, "uint");
        assert_eq!(cex.variables[0].display, "18446744073709551615");
        assert_eq!(cex.variables[1].name, "b");
        assert_eq!(cex.variables[1].value, "1");
        assert_eq!(cex.variables[1].value_type, "uint");
    } else {
        panic!("expected failed with counterexample");
    }

    // A raw status label is retained as diagnostic metadata but cannot publish
    // proof credit without structured proof and transport evidence.
    let divzero = func
        .obligations
        .iter()
        .find(|o| o.kind == "division_by_zero")
        .expect("should have divzero obligation");
    assert_eq!(divzero.solver, "ay");
    assert_eq!(divzero.time_ms, 1);
    assert!(matches!(
        &divzero.outcome,
        ObligationOutcome::Unknown { reason }
            if reason.contains("proof_evidence is missing")
    ));
}

#[test]
fn test_json_report_binary_copy_sink_kind_is_not_unknown() {
    let results = vec![(
        VerificationCondition {
            kind: VcKind::BinaryCopySinkLengthViolation {
                callee: "memcpy".to_string(),
                desc: "copy sink length may exceed destination capacity".to_string(),
            },
            function: "copy_into_stack".into(),
            location: SourceSpan::binary_address(0x401040),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        },
        VerificationResult::Failed { solver: "ay".into(), time_ms: 7, counterexample: None },
    )];

    let report = build_json_report("copy_sink", &results);
    let obligation = &report.functions[0].obligations[0];

    assert_eq!(obligation.kind, "binary_copy_sink_length_violation");
    assert_ne!(obligation.kind, "unknown");
    assert_eq!(
        obligation.description,
        "binary copy-sink length violation in `memcpy`: copy sink length may exceed destination capacity"
    );
    assert_eq!(obligation.proof_level, ProofLevel::L0Safety);
    assert_eq!(report.summary.verdict, CrateVerdict::HasViolations);

    let json = serde_json::to_value(&report).expect("report serializes");
    assert_eq!(json["functions"][0]["obligations"][0]["kind"], "binary_copy_sink_length_violation");
}

#[test]
fn test_json_report_obligation_location() {
    let results = midpoint_results();
    let report = build_json_report("midpoint", &results);

    let func = &report.functions[0];
    let overflow = func
        .obligations
        .iter()
        .find(|o| o.kind == "arithmetic_overflow_add")
        .expect("should have overflow obligation");

    let loc = overflow.location.as_ref().expect("should have location");
    assert_eq!(loc.file, "src/midpoint.rs");
    assert_eq!(loc.line_start, 5);
    assert_eq!(loc.col_start, 5);
}

#[test]
fn test_json_report_empty_span_no_location() {
    let results = vec![(
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        },
        VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: 1,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        },
    )];
    let report = build_json_report("test", &results);
    assert!(report.functions[0].obligations[0].location.is_none());
}

#[test]
fn test_json_report_multi_function() {
    let results = multi_function_results();
    let report = build_json_report("multi", &results);

    assert_eq!(report.summary.functions_analyzed, 3);
    assert_eq!(report.summary.total_obligations, 5);
    assert_eq!(report.summary.total_proved, 0);
    assert_eq!(report.summary.total_failed, 1);
    assert_eq!(report.summary.total_runtime_checked, 0);
    assert_eq!(report.summary.total_unknown, 4);
    assert_eq!(report.summary.verdict, CrateVerdict::HasViolations);

    // Functions sorted alphabetically
    assert_eq!(report.functions[0].function, "compute");
    assert_eq!(report.functions[1].function, "get_midpoint");
    assert_eq!(report.functions[2].function, "lookup");

    // compute: one raw proof status is downgraded + one timeout = inconclusive
    assert_eq!(report.functions[0].summary.verdict, FunctionVerdict::Inconclusive);

    // get_midpoint: one raw proof status is downgraded + one failure = violations
    assert_eq!(report.functions[1].summary.verdict, FunctionVerdict::HasViolations);

    // lookup: a public report adapter cannot install or authenticate the
    // certified monitor, so a policy-selected fallback remains inconclusive.
    assert_eq!(report.functions[2].summary.verdict, FunctionVerdict::Inconclusive);
}

#[test]
fn test_json_report_raw_proved_statuses_are_not_verified() {
    let results = vec![
        (
            VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: "safe_div".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
                obligation: None,
            },
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        ),
        (
            VerificationCondition {
                kind: VcKind::ArithmeticOverflow {
                    op: BinOp::Add,
                    operand_tys: (Ty::u32(), Ty::u32()),
                },
                function: "safe_div".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
                obligation: None,
            },
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        ),
    ];
    let report = build_json_report("safe", &results);
    assert_eq!(report.summary.total_proved, 0);
    assert_eq!(report.summary.total_unknown, 2);
    assert_eq!(report.summary.verdict, CrateVerdict::Inconclusive);
    assert_eq!(report.functions[0].summary.verdict, FunctionVerdict::Inconclusive);
}

#[test]
fn test_annotation_report_single_function() {
    let annotation = proof_annotation(
        "checked_add",
        "crate::math::checked_add",
        vec![
            annotation_obligation(
                "overflow check",
                "arithmetic_overflow_add",
                AnnotationStatus::Proved,
                ProofLevel::L0Safety,
                5,
                Some(SourceSpan {
                    file: "src/math.rs".to_string(),
                    line_start: 12,
                    col_start: 9,
                    line_end: 12,
                    col_end: 21,
                }),
            ),
            annotation_obligation(
                "postcondition",
                "postcondition",
                AnnotationStatus::Failed,
                ProofLevel::L1Functional,
                8,
                None,
            ),
        ],
    );

    let report = build_json_report_from_annotations("math", &[annotation]);

    assert_eq!(report.summary.functions_analyzed, 1);
    assert_eq!(report.summary.total_obligations, 2);
    assert_eq!(report.summary.total_proved, 0);
    assert_eq!(report.summary.total_failed, 1);
    assert_eq!(report.summary.total_unknown, 1);
    assert_eq!(report.summary.verdict, CrateVerdict::HasViolations);

    let function = &report.functions[0];
    assert_eq!(function.function, "crate::math::checked_add");
    assert_eq!(function.summary.verdict, FunctionVerdict::HasViolations);
    assert_eq!(function.summary.total_time_ms, 13);
    assert_eq!(function.obligations.len(), 2);
    assert!(matches!(
        &function.obligations[0].outcome,
        ObligationOutcome::Unknown { reason }
            if reason.contains("proof_evidence is missing")
    ));
    assert!(matches!(
        function.obligations[1].outcome,
        ObligationOutcome::Failed { counterexample: Some(_) }
    ));
    assert_eq!(
        function.obligations[0].location.as_ref().map(|location| location.file.as_str()),
        Some("src/math.rs")
    );
}

#[test]
fn test_annotation_report_empty() {
    let report = build_json_report_from_annotations("empty", &[]);

    assert_eq!(report.summary.verdict, CrateVerdict::NoObligations);
    assert_eq!(report.summary.functions_analyzed, 0);
    assert_eq!(report.summary.total_obligations, 0);
    assert!(report.functions.is_empty());
}

#[test]
fn test_annotation_report_roundtrip() {
    let report = build_json_report_from_annotations(
        "roundtrip",
        &[proof_annotation(
            "checked_mul",
            "crate::math::checked_mul",
            vec![
                annotation_obligation(
                    "overflow check",
                    "arithmetic_overflow_mul",
                    AnnotationStatus::Proved,
                    ProofLevel::L0Safety,
                    3,
                    Some(SourceSpan {
                        file: "src/math.rs".to_string(),
                        line_start: 20,
                        col_start: 5,
                        line_end: 20,
                        col_end: 17,
                    }),
                ),
                annotation_obligation(
                    "contract",
                    "postcondition",
                    AnnotationStatus::Timeout,
                    ProofLevel::L1Functional,
                    25,
                    None,
                ),
            ],
        )],
    );

    let json = serde_json::to_string(&report).expect("serialize annotation report");
    let roundtrip: JsonProofReport =
        serde_json::from_str(&json).expect("deserialize annotation report");

    assert_eq!(roundtrip.crate_name, "roundtrip");
    assert_eq!(roundtrip.summary.total_obligations, 2);
    assert_eq!(roundtrip.functions.len(), 1);
    assert_eq!(roundtrip.functions[0].function, "crate::math::checked_mul");
    assert!(matches!(
        roundtrip.functions[0].obligations[1].outcome,
        ObligationOutcome::Timeout { timeout_ms: 25 }
    ));
}

#[test]
fn test_annotation_report_raw_proved_statuses_are_not_verified() {
    let raw_proved_report = build_json_report_from_annotations(
        "raw_proved",
        &[proof_annotation(
            "safe_div",
            "crate::math::safe_div",
            vec![
                annotation_obligation(
                    "div by zero",
                    "division_by_zero",
                    AnnotationStatus::Proved,
                    ProofLevel::L0Safety,
                    2,
                    None,
                ),
                annotation_obligation(
                    "postcondition",
                    "postcondition",
                    AnnotationStatus::Proved,
                    ProofLevel::L1Functional,
                    4,
                    None,
                ),
            ],
        )],
    );
    assert_eq!(raw_proved_report.summary.total_proved, 0);
    assert_eq!(raw_proved_report.summary.total_unknown, 2);
    assert_eq!(raw_proved_report.summary.verdict, CrateVerdict::Inconclusive);
    assert_eq!(raw_proved_report.functions[0].summary.verdict, FunctionVerdict::Inconclusive);

    let failing_report = build_json_report_from_annotations(
        "failing",
        &[proof_annotation(
            "unsafe_div",
            "crate::math::unsafe_div",
            vec![
                annotation_obligation(
                    "div by zero",
                    "division_by_zero",
                    AnnotationStatus::Proved,
                    ProofLevel::L0Safety,
                    1,
                    None,
                ),
                annotation_obligation(
                    "postcondition",
                    "postcondition",
                    AnnotationStatus::Failed,
                    ProofLevel::L1Functional,
                    6,
                    None,
                ),
            ],
        )],
    );
    assert_eq!(failing_report.summary.verdict, CrateVerdict::HasViolations);
    assert_eq!(failing_report.functions[0].summary.verdict, FunctionVerdict::HasViolations);
}

#[test]
fn test_build_json_report_auto_policy_cannot_mint_runtime_check_authority() {
    let results = vec![(
        VerificationCondition {
            kind: VcKind::IndexOutOfBounds,
            function: "lookup".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        },
        VerificationResult::Unknown {
            solver: "ay".into(),
            time_ms: 50,
            reason: "nonlinear arithmetic".to_string(),
        },
    )];

    let report =
        build_json_report_with_policy("runtime_auto", &results, RuntimeCheckPolicy::Auto, true);
    let obligation = &report.functions[0].obligations[0];

    assert!(matches!(
        &obligation.outcome,
        ObligationOutcome::Unknown { reason }
            if reason.contains("no live authenticated compiler/monitor capability")
                && reason.contains("cannot carry runtime-check authority")
    ));
    assert_eq!(report.summary.total_runtime_checked, 0);
    assert_eq!(report.summary.total_unknown, 1);
    assert_eq!(report.functions[0].summary.verdict, FunctionVerdict::Inconclusive);
}

#[test]
fn test_memory_guard_solver_skip_is_reported_as_release_blocking_proof_gap() {
    let results = vec![(
        VerificationCondition {
            kind: VcKind::IndexOutOfBounds,
            function: "checked_lookup".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        },
        VerificationResult::Unknown {
            solver: "memory-guard".into(),
            time_ms: 0,
            reason: "memory limit exceeded: 2048MB used, 1024MB limit (peak: 2048MB) - skipping solver dispatch".to_string(),
        },
    )];

    let report = build_json_report("resource_gap", &results);
    let obligation = &report.functions[0].obligations[0];

    assert_eq!(report.summary.total_unknown, 1);
    assert_eq!(report.summary.verdict, CrateVerdict::Inconclusive);
    assert_eq!(obligation.kind, "memory_guard_resource_proof_gap");
    assert_eq!(obligation.solver, "memory-guard");
    assert!(matches!(
        &obligation.outcome,
        ObligationOutcome::Unknown { reason }
            if reason.contains("release-blocking proof gap")
                && reason.contains("memory guard skipped solver dispatch")
    ));
}

#[test]
fn test_build_json_report_force_static_produces_compile_error_verdict() {
    let results = vec![(
        VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::u32(), Ty::u32()),
            },
            function: "checked_add".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        },
        VerificationResult::Unknown {
            solver: "ay".into(),
            time_ms: 12,
            reason: "solver returned unknown".to_string(),
        },
    )];

    let report = build_json_report_with_policy(
        "force_static",
        &results,
        RuntimeCheckPolicy::ForceStatic,
        true,
    );
    let obligation = &report.functions[0].obligations[0];

    assert!(matches!(
        &obligation.outcome,
        ObligationOutcome::Unknown { reason }
            if reason.contains("`#[trust(static)]` requires a static proof")
                && reason.contains("solver returned unknown")
    ));
    assert_eq!(report.summary.total_runtime_checked, 0);
    assert_eq!(report.summary.total_unknown, 1);
    assert_eq!(report.functions[0].summary.verdict, FunctionVerdict::Inconclusive);
}

// -----------------------------------------------------------------------
// JSON serialization tests
// -----------------------------------------------------------------------

#[test]
fn test_json_serialization_roundtrip() {
    let results = multi_function_results();
    let report = build_json_report("roundtrip", &results);

    let json = serde_json::to_string_pretty(&report).expect("serialize");
    let deserialized: JsonProofReport = serde_json::from_str(&json).expect("deserialize");

    assert_eq!(deserialized.crate_name, "roundtrip");
    assert_eq!(deserialized.metadata.schema_version, report.metadata.schema_version);
    assert_eq!(deserialized.summary.total_obligations, 5);
    assert_eq!(deserialized.functions.len(), 3);
}

#[test]
fn test_json_output_has_required_fields() {
    let results = midpoint_results();
    let report = build_json_report("fields_test", &results);
    let json_value: serde_json::Value = serde_json::to_value(&report).expect("to_value");

    // Top-level required fields
    assert!(json_value.get("metadata").is_some());
    assert!(json_value.get("crate_name").is_some());
    assert!(json_value.get("summary").is_some());
    assert!(json_value.get("functions").is_some());

    // Metadata fields
    let meta = &json_value["metadata"];
    assert!(meta.get("schema_version").is_some());
    assert!(meta.get("trust_version").is_some());
    assert!(meta.get("timestamp").is_some());
    assert!(meta.get("total_time_ms").is_some());

    // Summary fields
    let summary = &json_value["summary"];
    assert!(summary.get("functions_analyzed").is_some());
    assert!(summary.get("functions_verified").is_some());
    assert!(summary.get("functions_runtime_checked").is_some());
    assert!(summary.get("functions_with_violations").is_some());
    assert!(summary.get("functions_inconclusive").is_some());
    assert!(summary.get("total_obligations").is_some());
    assert!(summary.get("total_proved").is_some());
    assert!(summary.get("total_runtime_checked").is_some());
    assert!(summary.get("total_failed").is_some());
    assert!(summary.get("total_unknown").is_some());
    assert!(summary.get("verdict").is_some());

    // Function fields
    let func = &json_value["functions"][0];
    assert!(func.get("function").is_some());
    assert!(func.get("summary").is_some());
    assert!(func.get("obligations").is_some());

    // Obligation fields
    let ob = &func["obligations"][0];
    assert!(ob.get("description").is_some());
    assert!(ob.get("kind").is_some());
    assert!(ob.get("proof_level").is_some());
    assert!(ob.get("outcome").is_some());
    assert!(ob.get("solver").is_some());
    assert!(ob.get("time_ms").is_some());
}

#[test]
fn test_json_outcome_tagged_union() {
    // Verify that the outcome uses internally-tagged serde representation
    let results = midpoint_results();
    let report = build_json_report("tags", &results);
    let json_value: serde_json::Value = serde_json::to_value(&report).expect("to_value");

    // Find the failed obligation
    let func = &json_value["functions"][0];
    for ob in func["obligations"].as_array().unwrap() {
        let outcome = &ob["outcome"];
        let status = outcome["status"].as_str().unwrap();
        match status {
            "proved" => {
                assert!(outcome.get("strength").is_some());
            }
            "failed" => {
                // counterexample may or may not be present
            }
            "unknown" => {
                assert!(outcome.get("reason").is_some());
            }
            "timeout" => {
                assert!(outcome.get("timeout_ms").is_some());
            }
            "runtime_checked" => {
                assert!(outcome.get("note").is_some() || outcome.get("note").is_none());
            }
            other => panic!("unexpected status: {other}"),
        }
    }
}

#[test]
fn test_json_report_runtime_checked_status() {
    let report = runtime_checked_report();

    assert_eq!(report.summary.verdict, CrateVerdict::RuntimeChecked);
    assert_eq!(report.summary.total_runtime_checked, 1);
    assert_eq!(report.summary.functions_runtime_checked, 1);
    assert_eq!(report.functions[0].summary.verdict, FunctionVerdict::RuntimeChecked);
    assert_eq!(report.functions[0].summary.runtime_checked, 1);

    let json = serde_json::to_string_pretty(&report).expect("serialize runtime-checked");
    let parsed: JsonProofReport = serde_json::from_str(&json).expect("deserialize runtime-checked");
    assert_eq!(parsed.summary.total_runtime_checked, 0);
    assert_eq!(parsed.summary.total_unknown, 1);
    assert_eq!(parsed.summary.verdict, CrateVerdict::Inconclusive);
    assert_eq!(parsed.functions[0].summary.runtime_checked, 0);
    assert_eq!(parsed.functions[0].summary.unknown, 1);

    let value: serde_json::Value = serde_json::from_str(&json).expect("parse runtime-checked");
    let ob = &value["functions"][0]["obligations"][0];
    assert_eq!(ob["outcome"]["status"], "runtime_checked");
    assert_eq!(ob["outcome"]["note"].as_str(), Some("validated by runtime instrumentation"));

    let text = format_json_summary(&report);
    assert!(text.contains("runtime-checked"));
    assert!(text.contains("RUNTIME CHECKED"));
    assert!(text.contains("validated by runtime instrumentation"));
}

#[test]
fn test_json_counterexample_structure() {
    let results = midpoint_results();
    let report = build_json_report("cex", &results);
    let json_value: serde_json::Value = serde_json::to_value(&report).expect("to_value");

    let func = &json_value["functions"][0];
    let failed_ob = func["obligations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|ob| ob["outcome"]["status"].as_str() == Some("failed"))
        .expect("should have a failed obligation");

    let cex = &failed_ob["outcome"]["counterexample"];
    assert!(cex.is_object());

    let vars = cex["variables"].as_array().unwrap();
    assert_eq!(vars.len(), 2);

    assert_eq!(vars[0]["name"].as_str().unwrap(), "a");
    assert!(vars[0].get("value").is_some());
    assert!(vars[0].get("value_type").is_some());
    assert_eq!(vars[0]["value_type"].as_str().unwrap(), "uint");
    assert!(vars[0].get("display").is_some());
}

#[test]
fn test_json_kind_tags_are_snake_case() {
    // Kind tags must be machine-parseable snake_case strings
    assert_eq!(vc_kind_tag(&VcKind::DivisionByZero), "division_by_zero");
    assert_eq!(vc_kind_tag(&VcKind::RemainderByZero), "remainder_by_zero");
    assert_eq!(vc_kind_tag(&VcKind::IndexOutOfBounds), "index_out_of_bounds");
    assert_eq!(vc_kind_tag(&VcKind::Postcondition), "postcondition");
    assert_eq!(vc_kind_tag(&VcKind::Unreachable), "unreachable");
    assert_eq!(
        vc_kind_tag(&VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (Ty::u32(), Ty::u32())
        }),
        "arithmetic_overflow_add"
    );
    assert_eq!(
        vc_kind_tag(&VcKind::ShiftOverflow {
            op: BinOp::Shl,
            operand_ty: Ty::u32(),
            shift_ty: Ty::u32()
        }),
        "shift_overflow_shl"
    );
    assert_eq!(
        vc_kind_tag(&VcKind::BinaryCopySinkLengthViolation {
            callee: "memcpy".to_string(),
            desc: "copy sink length may exceed destination capacity".to_string(),
        }),
        "binary_copy_sink_length_violation"
    );
    assert_eq!(
        vc_kind_tag(&VcKind::FfiBoundaryViolation {
            callee: "strncpy".to_string(),
            desc: "copy sink length for `strncpy` lacks destination capacity".to_string(),
        }),
        "binary_copy_sink_length_violation"
    );
    assert_eq!(
        vc_kind_tag(&VcKind::FfiBoundaryViolation {
            callee: "malloc".to_string(),
            desc: "return contract may be null".to_string(),
        }),
        "hardened_ffi_boundary"
    );
    assert_eq!(vc_kind_tag(&VcKind::AliasingViolation { mutable: true }), "aliasing_violation");
    assert_eq!(vc_kind_tag(&VcKind::LifetimeViolation), "lifetime_violation");
    assert_eq!(vc_kind_tag(&VcKind::SendViolation), "send_violation");
    assert_eq!(vc_kind_tag(&VcKind::SyncViolation), "sync_violation");
    assert_eq!(
        vc_kind_tag(&VcKind::LoopInvariantInitiation {
            invariant: "i <= n".to_string(),
            header_block: 3,
        }),
        "loop_invariant_initiation"
    );
    assert_eq!(
        vc_kind_tag(&VcKind::LoopInvariantConsecution {
            invariant: "i <= n".to_string(),
            header_block: 3,
        }),
        "loop_invariant_consecution"
    );
    assert_eq!(
        vc_kind_tag(&VcKind::LoopInvariantSufficiency {
            invariant: "i <= n".to_string(),
            header_block: 3,
        }),
        "loop_invariant_sufficiency"
    );
    assert_eq!(
        vc_kind_tag(&VcKind::TypeRefinementViolation {
            variable: "n".to_string(),
            predicate: "n >= 0".to_string(),
        }),
        "type_refinement_violation"
    );
    assert_eq!(
        vc_kind_tag(&VcKind::FrameConditionViolation {
            variable: "state".to_string(),
            function: "update".to_string(),
        }),
        "frame_condition_violation"
    );
    assert_eq!(
        vc_kind_tag(&VcKind::HardenedBoundary {
            category: HardenedVcCategory::RawPathApi,
            callee: "std::fs::remove_file".to_string(),
            detail: "path removal re-resolves a mutable direntry".to_string(),
        }),
        "hardened_raw_path_api"
    );
    assert_eq!(
        vc_kind_tag(&VcKind::FunctionalCorrectness {
            property: "hardened::byte_loss".to_string(),
            context: "to_string_lossy: lossy OS/path conversion".to_string(),
        }),
        "hardened_byte_loss"
    );
    assert_eq!(
        vc_kind_tag(&VcKind::FunctionalCorrectness {
            property: "result_correctness".to_string(),
            context: "binary_search postcondition".to_string(),
        }),
        "functional_correctness"
    );
    assert_eq!(
        vc_kind_tag(&VcKind::CopyBoundsViolation {
            callee: "copy_nonoverlapping".to_string(),
            direction: "dst".to_string(),
            detail: "copy count exceeds the destination allocation".to_string(),
        }),
        "copy_bounds_violation"
    );
    assert_eq!(
        vc_kind_tag(&VcKind::ExternallyMutableAllocationBounds {
            allocation_kind: "mmap_file".to_string(),
            live_size: "live_file_len".to_string(),
            detail: "captured length was not revalidated".to_string(),
        }),
        "externally_mutable_allocation_bounds"
    );
    assert_eq!(
        vc_kind_tag(&VcKind::UnboundedAllocation {
            callee: "Vec::with_capacity".to_string(),
            count: "n".to_string(),
            detail: "no allocation budget".to_string(),
        }),
        "unbounded_allocation"
    );
    assert_eq!(
        vc_kind_tag(&VcKind::UnsupportedMir {
            kind: "AArch64AtomicSemanticFactNotProofConsumed".to_string(),
            detail: "opcode=ldar; proof obligation: consume AArch64 acquire ordering event, synchronization edge, thread identity, and happens-before witness; access=Read; ordering=Acquire; exclusive_monitor=None; reports_status=false".to_string(),
        }),
        "aarch64_atomic_acquire_ordering_unsupported"
    );
    assert_eq!(
        vc_kind_tag(&VcKind::UnsupportedMir {
            kind: "AArch64AtomicSemanticFactNotProofConsumed".to_string(),
            detail: "opcode=stlr; proof obligation: consume AArch64 release ordering event, synchronization edge, thread identity, and happens-before witness; access=Write; ordering=Release; exclusive_monitor=None; reports_status=false".to_string(),
        }),
        "aarch64_atomic_release_ordering_unsupported"
    );
    assert_eq!(
        vc_kind_tag(&VcKind::UnsupportedMir {
            kind: "AArch64AtomicSemanticFactNotProofConsumed".to_string(),
            detail: "opcode=stlxr; unsupported proof obligation: exclusive-monitor reservation, invalidation, thread identity, and status semantics are not proof-consumed; store-conditional status result; access=Write; ordering=Release; exclusive_monitor=StoreConditional; reports_status=true".to_string(),
        }),
        "aarch64_exclusive_monitor_status_unsupported"
    );
    assert_eq!(
        vc_kind_tag(&VcKind::UnsupportedMir {
            kind: "SourceBackpropagationGateBlocker".to_string(),
            detail: "source_backpropagation_gate label=checked_certificate_identity; checked certificate identity is missing".to_string(),
        }),
        "source_backpropagation_checked_certificate_identity"
    );
    assert_eq!(
        vc_kind_tag(&VcKind::UnsupportedMir {
            kind: "SourceBackpropagationGateBlocker".to_string(),
            detail: "source_backpropagation_gate label=replay_identity; replay identity is missing"
                .to_string(),
        }),
        "source_backpropagation_replay_identity"
    );
    assert_eq!(
        vc_kind_tag(&VcKind::UnsupportedMir {
            kind: "SourceBackpropagationGateBlocker".to_string(),
            detail: "source_backpropagation_gate label=type_ownership; type ownership is not exact for source backpropagation".to_string(),
        }),
        "source_backpropagation_type_ownership"
    );
    assert_eq!(
        vc_kind_tag(&VcKind::UnsupportedMir {
            kind: "SourceBackpropagationGateBlocker".to_string(),
            detail: "checked proof-cert readback row accepted for proof-grade release; manifest_identity_sha256=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa; source_backpropagation_gate_sha256=bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".to_string(),
        }),
        "source_backpropagation_checked_certificate_identity"
    );
    assert_eq!(
        vc_kind_tag(&VcKind::UnsupportedMir {
            kind: "SourceBackpropagationGateBlocker".to_string(),
            detail: "source-backprop requires machine-effect witnesses consumed for every replayed instruction step: machine-code replay backend omitted memory_write effect witness memory_access#0:8B; concrete scalar memory address/width evidence is required".to_string(),
        }),
        "source_backpropagation_replay_identity"
    );
    assert_eq!(
        vc_kind_tag(&VcKind::UnsupportedMir {
            kind: "SourceBackpropagationGateBlocker".to_string(),
            detail: "trust-cg target proof consumer consumed binary proof inputs, but binary-proof-obligation-pending-refinement-metadata remains; bidirectional refinement metadata is missing".to_string(),
        }),
        "source_backpropagation_target_validation"
    );
    assert_eq!(
        vc_kind_tag(&VcKind::UnsupportedMir {
            kind: "TrustSymbolicFormulaNotProofConsumed".to_string(),
            detail: "trust_symbolic.formula location=bb0[1].rvalue; structured formula payload is preserved but no proof consumer accepted it".to_string(),
        }),
        "trust_symbolic_formula_not_consumed"
    );
}

#[test]
fn every_current_vc_kind_has_a_non_unknown_canonical_tag() {
    let sample = |value: &str| value.to_string();
    let kinds = vec![
        VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (Ty::u32(), Ty::u32()),
        },
        VcKind::ShiftOverflow {
            op: BinOp::Shl,
            operand_ty: Ty::u32(),
            shift_ty: Ty::u32(),
        },
        VcKind::DivisionByZero,
        VcKind::RemainderByZero,
        VcKind::IndexOutOfBounds,
        VcKind::SliceBoundsCheck,
        VcKind::Assertion { message: sample("assert") },
        VcKind::Precondition { callee: sample("callee") },
        VcKind::Postcondition,
        VcKind::CastOverflow { from_ty: Ty::u32(), to_ty: Ty::i32() },
        VcKind::NegationOverflow { ty: Ty::i32() },
        VcKind::Unreachable,
        VcKind::UnsupportedMir { kind: sample("future_mir"), detail: sample("unsupported") },
        VcKind::DeadState { state: sample("closed") },
        VcKind::Deadlock,
        VcKind::Temporal { property: sample("always ready"), machine: None },
        VcKind::Liveness {
            property: LivenessProperty {
                name: sample("eventual progress"),
                operator: TemporalOperator::Eventually,
                predicate: sample("done"),
                consequent: None,
                fairness: Vec::new(),
            },
            machine: None,
        },
        VcKind::Fairness {
            constraint: FairnessConstraint::Weak {
                action: sample("schedule"),
                vars: vec![sample("task")],
            },
        },
        VcKind::TaintViolation {
            source_label: sample("input"),
            sink_kind: sample("exec"),
            path_length: 1,
        },
        VcKind::RefinementViolation { spec_file: sample("spec"), action: sample("step") },
        VcKind::ResilienceViolation {
            service: sample("db"),
            failure_mode: sample("timeout"),
            reason: sample("unhandled"),
        },
        VcKind::ProtocolViolation { protocol: sample("raft"), violation: sample("split brain") },
        VcKind::NonTermination { context: sample("loop"), measure: sample("n") },
        VcKind::DataRace {
            variable: sample("x"),
            thread_a: sample("a"),
            thread_b: sample("b"),
        },
        VcKind::InsufficientOrdering {
            variable: sample("x"),
            actual: sample("Relaxed"),
            required: sample("Acquire"),
        },
        VcKind::TranslationValidation { pass: sample("dce"), check: sample("refinement") },
        VcKind::FloatDivisionByZero,
        VcKind::FloatOverflowToInfinity {
            op: BinOp::Mul,
            operand_ty: Ty::Float { width: 64 },
        },
        VcKind::InvalidDiscriminant { place_name: sample("value") },
        VcKind::AggregateArrayLengthMismatch { expected: 2, actual: 1 },
        VcKind::UnsafeOperation { desc: sample("raw pointer dereference") },
        VcKind::SavedReturnAddressOverwrite { access_width_bytes: 8, slot: sample("saved ra") },
        VcKind::FormatStringViolation { callee: sample("printf"), evidence: sample("tainted") },
        VcKind::TaintedIndirectBranch {
            sink_kind: sample("indirect_call"),
            target: sample("rax"),
            evidence: sample("unresolved"),
        },
        VcKind::BinaryAbiContradiction { fact: sample("stack slot"), evidence: sample("conflict") },
        VcKind::BinaryCopySinkLengthViolation { callee: sample("memcpy"), desc: sample("length") },
        VcKind::FfiBoundaryViolation { callee: sample("malloc"), desc: sample("null return") },
        VcKind::CopyBoundsViolation {
            callee: sample("copy_nonoverlapping"),
            direction: sample("dst"),
            detail: sample("unbounded count"),
        },
        VcKind::ExternallyMutableAllocationBounds {
            allocation_kind: sample("mmap_file"),
            live_size: sample("file_len"),
            detail: sample("not revalidated"),
        },
        VcKind::UnboundedAllocation {
            callee: sample("Vec::reserve"),
            count: sample("n"),
            detail: sample("no budget"),
        },
        VcKind::UseAfterFree,
        VcKind::DoubleFree,
        VcKind::AliasingViolation { mutable: true },
        VcKind::LifetimeViolation,
        VcKind::SendViolation,
        VcKind::SyncViolation,
        VcKind::FunctionalCorrectness {
            property: sample("result_correctness"),
            context: sample("search"),
        },
        VcKind::HardenedBoundary {
            category: HardenedVcCategory::ByteLoss,
            callee: sample("to_string_lossy"),
            detail: sample("lossy conversion"),
        },
        VcKind::LoopInvariantInitiation { invariant: sample("i <= n"), header_block: 1 },
        VcKind::LoopInvariantConsecution { invariant: sample("i <= n"), header_block: 1 },
        VcKind::LoopInvariantSufficiency { invariant: sample("i <= n"), header_block: 1 },
        VcKind::TypeRefinementViolation { variable: sample("n"), predicate: sample("n >= 0") },
        VcKind::FrameConditionViolation { variable: sample("state"), function: sample("update") },
    ];

    assert_eq!(kinds.len(), 53, "update the canonical-tag inventory when VcKind grows");
    for kind in kinds {
        assert_ne!(vc_kind_tag(&kind), "unknown", "missing canonical tag for {kind:?}");
    }
}

#[test]
fn hardened_categories_are_distinct_in_json_and_text_reports() {
    let hardened = VerificationCondition {
        kind: VcKind::HardenedBoundary {
            category: HardenedVcCategory::ByteLoss,
            callee: "std::path::Path::to_string_lossy".to_string(),
            detail: "lossy OS/path conversion must be explicit".to_string(),
        },
        function: "crate::paths::render".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
        obligation: None,
    };
    let ordinary = VerificationCondition {
        kind: VcKind::FunctionalCorrectness {
            property: "result_correctness".to_string(),
            context: "binary_search postcondition".to_string(),
        },
        function: "crate::search::binary_search".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
        obligation: None,
    };
    let proved = VerificationResult::Proved {
        solver: "ay".into(),
        time_ms: 1,
        strength: ProofStrength::smt_unsat(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    };
    let report = build_json_report("hardened", &[(hardened, proved.clone()), (ordinary, proved)]);

    let json = serde_json::to_value(&report).expect("serialize report");
    let kinds: Vec<&str> = json["functions"]
        .as_array()
        .expect("functions")
        .iter()
        .flat_map(|function| function["obligations"].as_array().expect("obligations"))
        .map(|obligation| obligation["kind"].as_str().expect("kind"))
        .collect();
    assert!(kinds.contains(&"hardened_byte_loss"));
    assert!(kinds.contains(&"functional_correctness"));

    let text = format_json_summary(&report);
    assert!(text.contains("[hardened_byte_loss]"));
    assert!(text.contains("hardened boundary (byte_loss)"));
    assert!(text.contains("[functional_correctness] functional correctness (result_correctness)"));

    let terminal = crate::terminal::format_terminal_report_impl(&report, false);
    assert!(terminal.contains("[hardened_byte_loss]"));
    assert!(
        terminal.contains("[functional_correctness] functional correctness (result_correctness)")
    );
}

#[test]
fn test_json_report_classifies_aarch64_atomic_unsupported_vcs() {
    let ldar_detail = "opcode=ldar; proof obligation: consume AArch64 acquire ordering event, synchronization edge, thread identity, and happens-before witness; access=Read; ordering=Acquire; exclusive_monitor=None; reports_status=false";
    let stlr_detail = "opcode=stlr; proof obligation: consume AArch64 release ordering event, synchronization edge, thread identity, and happens-before witness; access=Write; ordering=Release; exclusive_monitor=None; reports_status=false";
    let stlxr_detail = "opcode=stlxr; unsupported proof obligation: exclusive-monitor reservation, invalidation, thread identity, and status semantics are not proof-consumed; store-conditional status result; access=Write; ordering=Release; exclusive_monitor=StoreConditional; reports_status=true";
    let results = [ldar_detail, stlr_detail, stlxr_detail]
        .into_iter()
        .enumerate()
        .map(|(idx, detail)| {
            (
                VerificationCondition {
                    kind: VcKind::UnsupportedMir {
                        kind: "AArch64AtomicSemanticFactNotProofConsumed".to_string(),
                        detail: detail.to_string(),
                    },
                    function: "aarch64_atomic".into(),
                    location: SourceSpan::binary_address(0x2230 + (idx as u64) * 4),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                    obligation: None,
                },
                VerificationResult::Unknown {
                    solver: "router".into(),
                    time_ms: 0,
                    reason: format!("unsupported MIR AArch64AtomicSemanticFactNotProofConsumed preserved in TrustIr: {detail}"),
                },
            )
        })
        .collect::<Vec<_>>();

    let report = build_json_report("atomic_vcs", &results);
    let obligations = &report.functions[0].obligations;
    let kinds = obligations.iter().map(|ob| ob.kind.as_str()).collect::<Vec<_>>();

    assert_eq!(
        kinds,
        vec![
            "aarch64_atomic_acquire_ordering_unsupported",
            "aarch64_atomic_release_ordering_unsupported",
            "aarch64_exclusive_monitor_status_unsupported",
        ]
    );
    assert!(obligations[0].description.contains("happens-before witness"));
    assert!(obligations[1].description.contains("synchronization edge"));
    assert!(obligations[2].description.contains("exclusive-monitor reservation"));
    assert!(obligations[2].description.contains("store-conditional status result"));
    assert!(matches!(
        &obligations[0].outcome,
        ObligationOutcome::Unknown { reason }
            if reason.contains("happens-before witness")
    ));

    let json = serde_json::to_value(&report).expect("report serializes");
    assert_eq!(
        json["functions"][0]["obligations"][0]["kind"],
        "aarch64_atomic_acquire_ordering_unsupported"
    );
    assert_eq!(
        json["functions"][0]["obligations"][2]["kind"],
        "aarch64_exclusive_monitor_status_unsupported"
    );

    let text = format_json_summary(&report);
    assert!(text.contains("happens-before witness"));
    assert!(text.contains("exclusive-monitor reservation"));
    let terminal = crate::terminal::format_terminal_report(&report);
    assert!(terminal.contains("store-conditional status result"));
}

#[test]
fn test_json_report_classifies_source_backpropagation_gate_blockers() {
    let labels = [
        ("missing_reconstruction", "accepted reconstruction is missing"),
        ("exact_source_provenance", "exact source provenance is missing"),
        ("type_ownership", "type ownership is not exact"),
        ("target_validation", "target validation is not accepted"),
        ("checked_certificate_identity", "checked certificate identity is missing"),
        ("replay_identity", "replay identity is missing"),
    ];
    let results = labels
        .into_iter()
        .map(|(label, detail)| {
            (
                VerificationCondition {
                    kind: VcKind::UnsupportedMir {
                        kind: "SourceBackpropagationGateBlocker".to_string(),
                        detail: format!("source_backpropagation_gate label={label}; {detail}"),
                    },
                    function: "binary::source_backprop".into(),
                    location: SourceSpan::binary_address(0x401000),
                    formula: Formula::Bool(false),
                    contract_metadata: None,
                    obligation: None,
                },
                VerificationResult::Unknown {
                    solver: "router".into(),
                    time_ms: 0,
                    reason: format!(
                        "unsupported MIR SourceBackpropagationGateBlocker [source_backpropagation_{label}] preserved in TrustIr: source_backpropagation_gate label={label}; {detail}"
                    ),
                },
            )
        })
        .collect::<Vec<_>>();

    let report = build_json_report("source_backprop", &results);
    let obligations = &report.functions[0].obligations;
    let kinds = obligations.iter().map(|obligation| obligation.kind.as_str()).collect::<Vec<_>>();

    assert_eq!(
        kinds,
        vec![
            "source_backpropagation_missing_reconstruction",
            "source_backpropagation_exact_source_provenance",
            "source_backpropagation_type_ownership",
            "source_backpropagation_target_validation",
            "source_backpropagation_checked_certificate_identity",
            "source_backpropagation_replay_identity",
        ]
    );
    for (obligation, (label, _)) in obligations.iter().zip(labels) {
        assert!(obligation.description.contains(label));
        assert!(matches!(
            &obligation.outcome,
            ObligationOutcome::Unknown { reason }
                if reason.contains("SourceBackpropagationGateBlocker")
                    && reason.contains(label)
        ));
    }
}

#[test]
fn test_json_report_classifies_recent_source_backpropagation_gate_details() {
    let cases = [
        (
            "checked proof-cert readback row accepted for proof-grade release; manifest_identity_sha256=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa; source_backpropagation_gate_sha256=bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
            "source_backpropagation_checked_certificate_identity",
            "manifest_identity_sha256",
        ),
        (
            "source-backprop requires machine-effect witnesses consumed for every replayed instruction step: machine-code replay backend omitted memory_write effect witness memory_access#0:8B; concrete scalar memory address/width evidence is required",
            "source_backpropagation_replay_identity",
            "concrete scalar memory address",
        ),
        (
            "trust-cg target proof consumer consumed binary proof inputs, but binary-proof-obligation-pending-refinement-metadata remains; bidirectional refinement metadata is missing",
            "source_backpropagation_target_validation",
            "bidirectional refinement metadata",
        ),
    ];
    let results = cases
        .into_iter()
        .enumerate()
        .map(|(idx, (detail, expected, _))| {
            (
                VerificationCondition {
                    kind: VcKind::UnsupportedMir {
                        kind: "SourceBackpropagationGateBlocker".to_string(),
                        detail: detail.to_string(),
                    },
                    function: "binary::source_backprop".into(),
                    location: SourceSpan::binary_address(0x401200 + (idx as u64) * 4),
                    formula: Formula::Bool(false),
                    contract_metadata: None,
                    obligation: None,
                },
                VerificationResult::Unknown {
                    solver: "router".into(),
                    time_ms: 0,
                    reason: format!(
                        "unsupported MIR SourceBackpropagationGateBlocker [{expected}] preserved in TrustIr: {detail}"
                    ),
                },
            )
        })
        .collect::<Vec<_>>();

    let report = build_json_report("source_backprop_recent", &results);
    let obligations = &report.functions[0].obligations;
    let kinds = obligations.iter().map(|obligation| obligation.kind.as_str()).collect::<Vec<_>>();

    assert_eq!(kinds, cases.iter().map(|(_, expected, _)| *expected).collect::<Vec<_>>());
    for (obligation, (detail, _, marker)) in obligations.iter().zip(cases) {
        assert!(obligation.description.contains(marker));
        assert!(obligation.description.contains(detail));
        assert!(matches!(
            &obligation.outcome,
            ObligationOutcome::Unknown { reason }
                if reason.contains("SourceBackpropagationGateBlocker")
                    && reason.contains(marker)
        ));
    }
}

#[test]
fn test_json_report_classifies_symbolic_formula_consumer_blocker() {
    let detail = "trust_symbolic.formula location=bb0[1].rvalue; structured formula payload is preserved but no schema-aware proof consumer accepted it; rejecting instead of Undef";
    let vc = VerificationCondition {
        kind: VcKind::UnsupportedMir {
            kind: "TrustSymbolicFormulaNotProofConsumed".to_string(),
            detail: detail.to_string(),
        },
        function: "binary::symbolic_formula".into(),
        location: SourceSpan::binary_address(0x401030),
        formula: Formula::Bool(false),
        contract_metadata: None,
        obligation: None,
    };
    let result = VerificationResult::Unknown {
        solver: "router".into(),
        time_ms: 0,
        reason: format!(
            "unsupported MIR TrustSymbolicFormulaNotProofConsumed [trust_symbolic_formula_not_consumed] preserved in TrustIr: {detail}"
        ),
    };

    let report = build_json_report("symbolic_formula", &[(vc, result)]);
    let obligation = &report.functions[0].obligations[0];

    assert_eq!(obligation.kind, "trust_symbolic_formula_not_consumed");
    assert!(obligation.description.contains("trust_symbolic.formula"));
    assert!(matches!(
        &obligation.outcome,
        ObligationOutcome::Unknown { reason }
            if reason.contains("trust_symbolic_formula_not_consumed")
                && reason.contains("Undef")
    ));

    let json = serde_json::to_value(&report).expect("report serializes");
    assert_eq!(
        json["functions"][0]["obligations"][0]["kind"],
        "trust_symbolic_formula_not_consumed"
    );
    let text = format_json_summary(&report);
    assert!(text.contains("trust_symbolic.formula"));
    assert!(text.contains("Undef"));
}

// -----------------------------------------------------------------------
// NDJSON streaming tests
// -----------------------------------------------------------------------

#[test]
fn test_ndjson_output_format() {
    let results = midpoint_results();
    let report = build_json_report("ndjson_test", &results);

    let mut buf = Vec::new();
    write_ndjson(&report, &mut buf).expect("write ndjson");
    let output = String::from_utf8(buf).expect("utf8");

    let lines: Vec<&str> = output.trim_end().split('\n').collect();
    // header + 1 function + footer = 3 lines
    assert_eq!(lines.len(), 3, "expected 3 NDJSON lines, got {}", lines.len());

    // Each line must be valid JSON
    for (i, line) in lines.iter().enumerate() {
        let parsed: serde_json::Value =
            serde_json::from_str(line).unwrap_or_else(|e| panic!("line {i} not valid JSON: {e}"));
        assert!(parsed.get("record_type").is_some(), "line {i} missing record_type");
    }

    // NDJSON wire records are intentionally Serialize-only: a standalone
    // function line cannot enforce the whole-report publication gate. Inspect
    // their JSON shape without reconstituting proof-bearing typed DTOs.
    let header: serde_json::Value = serde_json::from_str(lines[0]).expect("parse header JSON");
    assert_eq!(header["record_type"], "header");
    assert_eq!(header["schema"], "trust.report.ndjson.v2");
    assert_eq!(header["authority"], SERIALIZED_REPORT_AUTHORITY);
    assert_eq!(header["crate_name"], "ndjson_test");
    assert_eq!(header["expected_functions"], report.functions.len());
    assert_eq!(header["hardened"], serde_json::to_value(&report.hardened).unwrap());
    if report.assumptions.is_empty() {
        assert!(header.get("assumptions").is_none());
    } else {
        assert_eq!(header["assumptions"], serde_json::to_value(&report.assumptions).unwrap());
    }
    assert_eq!(
        header["verification_gate"],
        serde_json::to_value(&report.verification_gate).unwrap()
    );

    let function: serde_json::Value = serde_json::from_str(lines[1]).expect("parse function JSON");
    assert_eq!(function["record_type"], "function");
    assert_eq!(function["function"], "get_midpoint");

    let footer: serde_json::Value = serde_json::from_str(lines[2]).expect("parse footer JSON");
    assert_eq!(footer["record_type"], "footer");
    assert_eq!(footer["schema"], "trust.report.ndjson.v2");
    assert_eq!(footer["functions_emitted"], report.functions.len());
    assert_eq!(footer["summary"]["total_proved"], 0);
    assert_eq!(footer["summary"]["total_failed"], 1);
    assert_eq!(footer["summary"]["total_unknown"], 1);

    let function_bytes = lines[1].as_bytes();
    let mut function_digest = Sha256::new();
    function_digest.update(b"trust.report.ndjson.function-records.v2");
    function_digest.update((report.functions.len() as u64).to_be_bytes());
    function_digest.update((function_bytes.len() as u64).to_be_bytes());
    function_digest.update(function_bytes);
    assert_eq!(
        footer["function_records_sha256"],
        format!("sha256:{:x}", function_digest.finalize())
    );

    let mut canonical_digest = Sha256::new();
    canonical_digest.update(b"trust.report.ndjson.canonical-report.v2");
    canonical_digest.update(serde_json::to_vec(&report).expect("serialize canonical report"));
    assert_eq!(
        footer["canonical_report_sha256"],
        format!("sha256:{:x}", canonical_digest.finalize())
    );
}

#[test]
fn serialized_json_explicitly_disclaims_live_proof_authority() {
    let report = build_json_report("observational", &midpoint_results());
    let json = serde_json::to_value(report).expect("serialize report");

    assert_eq!(json["authority"], SERIALIZED_REPORT_AUTHORITY);
}

#[test]
fn test_ndjson_multi_function() {
    let results = multi_function_results();
    let report = build_json_report("multi_ndjson", &results);

    let mut buf = Vec::new();
    write_ndjson(&report, &mut buf).expect("write ndjson");
    let output = String::from_utf8(buf).expect("utf8");

    let lines: Vec<&str> = output.trim_end().split('\n').collect();
    // header + 3 functions + footer = 5 lines
    assert_eq!(lines.len(), 5, "expected 5 NDJSON lines, got {}", lines.len());

    // Verify all function records
    let func_lines = &lines[1..4];
    for line in func_lines {
        let record: serde_json::Value =
            serde_json::from_str(line).expect("parse function record JSON");
        assert_eq!(record["record_type"], "function");
        assert_eq!(record["crate_name"], "multi_ndjson");
    }
}

#[test]
fn test_ndjson_empty_crate() {
    let report = build_json_report("empty", &[]);

    let mut buf = Vec::new();
    write_ndjson(&report, &mut buf).expect("write ndjson");
    let output = String::from_utf8(buf).expect("utf8");

    let lines: Vec<&str> = output.trim_end().split('\n').collect();
    // header + footer = 2 lines
    assert_eq!(lines.len(), 2);
}

// -----------------------------------------------------------------------
// Text formatting (derived from JSON) tests
// -----------------------------------------------------------------------

#[test]
fn test_json_summary_text_format() {
    let results = midpoint_results();
    let report = build_json_report("midpoint", &results);
    let text = format_json_summary(&report);

    assert!(text.contains("get_midpoint"));
    assert!(text.contains("[VIOLATIONS]"));
    assert!(text.contains("UNKNOWN"));
    assert!(text.contains("proof_evidence is missing"));
    assert!(text.contains("FAILED"));
    assert!(text.contains("counterexample"));
    assert!(text.contains("a = 18446744073709551615"));
    assert!(text.contains("max level: L0 safety"));
    assert!(text.contains("Verdict: HAS VIOLATIONS"));
}

#[test]
fn test_json_summary_raw_proved_is_inconclusive() {
    let results = vec![(
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "safe_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        },
        VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: 1,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        },
    )];
    let report = build_json_report("safe", &results);
    let text = format_json_summary(&report);

    assert!(text.contains("[INCONCLUSIVE]"));
    assert!(text.contains("UNKNOWN"));
    assert!(text.contains("proof_evidence is missing"));
    assert!(text.contains("Verdict: INCONCLUSIVE"));
}

#[test]
fn test_json_summary_timeout() {
    let results = vec![(
        VerificationCondition {
            kind: VcKind::Postcondition,
            function: "slow_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        },
        VerificationResult::Timeout { solver: "ay".into(), timeout_ms: 10000 },
    )];
    let report = build_json_report("slow", &results);
    let text = format_json_summary(&report);

    assert!(text.contains("TIMEOUT"));
    assert!(text.contains("10000ms"));
    assert!(text.contains("0 unknown, 1 timeout"));
    assert!(!text.contains("1 unknown (1 timeout)"));
    assert!(text.contains("Verdict: INCONCLUSIVE"));
}

// -----------------------------------------------------------------------
// File I/O tests
// -----------------------------------------------------------------------

#[test]
fn test_write_json_report_file() {
    let results = midpoint_results();
    let report = build_json_report("file_test", &results);

    let dir = std::env::temp_dir().join("trust_report_test_json");
    let _ = std::fs::remove_dir_all(&dir);

    write_json_report(&report, &dir).expect("write json");

    let content = std::fs::read_to_string(dir.join("report.json")).expect("read json");
    let parsed: JsonProofReport = serde_json::from_str(&content).expect("parse json");
    assert_eq!(parsed.crate_name, "file_test");
    assert_eq!(parsed.functions.len(), 1);

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_write_ndjson_report_file() {
    let results = multi_function_results();
    let report = build_json_report("ndjson_file", &results);

    let dir = std::env::temp_dir().join("trust_report_test_ndjson");
    let _ = std::fs::remove_dir_all(&dir);

    write_ndjson_report(&report, &dir).expect("write ndjson");

    let content = std::fs::read_to_string(dir.join("report.ndjson")).expect("read ndjson");
    let lines: Vec<&str> = content.trim_end().split('\n').collect();
    assert_eq!(lines.len(), 5); // header + 3 functions + footer

    // Each line parseable
    for line in &lines {
        let _: serde_json::Value = serde_json::from_str(line).expect("valid json");
    }

    let _ = std::fs::remove_dir_all(&dir);
}

// -----------------------------------------------------------------------
// Proof level and kind coverage
// -----------------------------------------------------------------------

#[test]
fn test_obligation_proof_levels() {
    let results = vec![
        (
            VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: "f".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
                obligation: None,
            },
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        ),
        (
            VerificationCondition {
                kind: VcKind::Postcondition,
                function: "f".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
                obligation: None,
            },
            VerificationResult::Proved {
                solver: "trust-wp".into(),
                time_ms: 10,
                strength: ProofStrength::deductive(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        ),
        (
            VerificationCondition {
                kind: VcKind::Deadlock,
                function: "f".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
                obligation: None,
            },
            VerificationResult::Proved {
                solver: "ty".into(),
                time_ms: 100,
                strength: ProofStrength::inductive(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        ),
    ];

    let report = build_json_report("levels", &results);
    let func = &report.functions[0];

    // Max proof level should be L2Domain (deadlock)
    assert_eq!(func.summary.max_proof_level, Some(ProofLevel::L2Domain));

    // Check individual proof levels
    let levels: Vec<ProofLevel> = func.obligations.iter().map(|o| o.proof_level).collect();
    assert!(levels.contains(&ProofLevel::L0Safety));
    assert!(levels.contains(&ProofLevel::L1Functional));
    assert!(levels.contains(&ProofLevel::L2Domain));
}

#[test]
fn test_all_proof_strengths_serialize() {
    let strengths = vec![
        ProofStrength::smt_unsat(),
        ProofStrength::bounded(100),
        ProofStrength::inductive(),
        ProofStrength::deductive(),
        ProofStrength::constructive(),
    ];

    for strength in &strengths {
        let json = serde_json::to_string(strength).expect("serialize strength");
        let roundtrip: ProofStrength = serde_json::from_str(&json).expect("deserialize strength");
        assert_eq!(&roundtrip, strength);
    }
}

#[test]
fn test_function_summary_timing() {
    let results = multi_function_results();
    let report = build_json_report("timing", &results);

    // get_midpoint: 3ms + 1ms = 4ms
    let midpoint = report.functions.iter().find(|f| f.function == "get_midpoint").unwrap();
    assert_eq!(midpoint.summary.total_time_ms, 4);

    // compute: 5000ms + 2ms = 5002ms
    let compute = report.functions.iter().find(|f| f.function == "compute").unwrap();
    assert_eq!(compute.summary.total_time_ms, 5002);
}

// -----------------------------------------------------------------------
// Whole-crate verification report tests
// -----------------------------------------------------------------------

fn crate_verification_result_fixture() -> CrateVerificationResult {
    let results = multi_function_results();

    // Split results by function to build per-function entries.
    let mut func_map: BTreeMap<String, Vec<(VerificationCondition, VerificationResult)>> =
        BTreeMap::new();
    for (vc, result) in results {
        func_map.entry(vc.function.as_str().to_string()).or_default().push((vc, result));
    }

    let mut crate_result = CrateVerificationResult::new("multi_crate");
    for (func_name, func_results) in func_map {
        crate_result.add_function(FunctionVerificationResult {
            function_path: format!("crate::{func_name}"),
            function_name: func_name,
            results: func_results,
            from_notes: 0,
            with_assumptions: 0,
        });
    }
    crate_result
}

#[test]
fn test_build_crate_verification_report_produces_valid_report() {
    let crate_result = crate_verification_result_fixture();
    let report = build_crate_verification_report(&crate_result);

    assert_eq!(report.crate_name, "multi_crate");
    assert_eq!(report.summary.functions_analyzed, 3);
    assert_eq!(report.summary.total_obligations, 5);
    assert_eq!(report.summary.total_proved, 0);
    assert_eq!(report.summary.total_failed, 1);
    assert_eq!(report.summary.total_unknown, 4);
    assert_eq!(report.summary.verdict, CrateVerdict::HasViolations);
}

#[test]
fn test_build_crate_verification_report_empty() {
    let crate_result = CrateVerificationResult::new("empty_crate");
    let report = build_crate_verification_report(&crate_result);

    assert_eq!(report.crate_name, "empty_crate");
    assert_eq!(report.summary.functions_analyzed, 0);
    assert_eq!(report.summary.verdict, CrateVerdict::NoObligations);
    assert!(report.functions.is_empty());
}

#[test]
fn test_build_crate_verification_report_with_policy() {
    let crate_result = crate_verification_result_fixture();
    let report = build_crate_verification_report_with_policy(
        &crate_result,
        RuntimeCheckPolicy::ForceStatic,
        true,
    );

    assert_eq!(report.crate_name, "multi_crate");
    // ForceStatic should not reclassify unknowns to runtime-checked
    assert_eq!(report.summary.total_runtime_checked, 0);
}

#[test]
fn test_format_crate_verification_summary_no_specs() {
    let crate_result = crate_verification_result_fixture();
    let report = build_crate_verification_report(&crate_result);
    let text = format_crate_verification_summary(&report, &crate_result);

    // Without spec composition, no composition lines should appear.
    assert!(!text.contains("Cross-function composition:"));
    assert!(text.contains("Verdict:"));
}

#[test]
fn test_append_dep_tcb_ledger_empty_is_noop() {
    let mut summary = "Verdict: ok".to_string();
    append_dep_tcb_ledger(&mut summary, &[]);
    assert_eq!(summary, "Verdict: ok", "empty ledger must not alter the summary");
}

#[test]
fn test_append_dep_tcb_ledger_renders_rows() {
    let mut summary = "Verdict: ok".to_string();
    let lines = vec![
        "Trusted      core  (std hard-skip)".to_string(),
        "Conditional  serde  (scoped out)".to_string(),
    ];
    append_dep_tcb_ledger(&mut summary, &lines);
    assert!(summary.contains("Dependency trust base (scoped out of verification):"));
    assert!(summary.contains("core"));
    assert!(summary.contains("serde"));
}

#[test]
fn test_format_crate_verification_summary_with_specs() {
    let mut crate_result = CrateVerificationResult::new("spec_crate");
    crate_result.add_function(FunctionVerificationResult {
        function_path: "crate::f".to_string(),
        function_name: "f".to_string(),
        results: vec![(
            VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: "f".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
                obligation: None,
            },
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )],
        from_notes: 3,
        with_assumptions: 2,
    });

    let report = build_crate_verification_report(&crate_result);
    let text = format_crate_verification_summary(&report, &crate_result);

    assert!(text.contains("Cross-function composition:"));
    assert!(text.contains("3 VCs satisfied from proved callee specs (free)"));
    assert!(text.contains("2 VCs sent to solver with callee assumptions"));
}

#[test]
fn test_crate_verification_report_serialization_roundtrip() {
    let crate_result = crate_verification_result_fixture();
    let report = build_crate_verification_report(&crate_result);

    let json = serde_json::to_string_pretty(&report).expect("serialize");
    let deserialized: JsonProofReport = serde_json::from_str(&json).expect("deserialize");

    assert_eq!(deserialized.crate_name, "multi_crate");
    assert_eq!(deserialized.summary.functions_analyzed, 3);
    assert_eq!(deserialized.summary.total_obligations, 5);
}

// -----------------------------------------------------------------------
// #382: ProofEvidence downstream usage tests
// -----------------------------------------------------------------------

#[test]
fn test_proof_evidence_label_smt() {
    let strength = ProofStrength::smt_unsat();
    let label = proof_evidence_label(&strength);
    assert!(label.contains("SMT UNSAT"), "expected SMT UNSAT in {label}");
    assert!(label.contains("smt-backed"), "expected smt-backed in {label}");
}

#[test]
fn test_proof_evidence_label_bounded() {
    let strength = ProofStrength::bounded(100);
    let label = proof_evidence_label(&strength);
    assert!(label.contains("BOUNDED"), "expected BOUNDED in {label}");
    assert!(label.contains("trusted"), "expected trusted assurance in {label}");
}

#[test]
fn test_proof_evidence_label_constructive() {
    let strength = ProofStrength::constructive();
    let label = proof_evidence_label(&strength);
    assert!(label.contains("CONSTRUCTIVE"), "expected CONSTRUCTIVE in {label}");
}

#[test]
fn test_proof_evidence_from_proof_strength_roundtrip() {
    // Verify the From<ProofStrength> for ProofEvidence conversion is used
    let strength = ProofStrength::deductive();
    let evidence: ProofEvidence = strength.into();
    assert_eq!(evidence.reasoning, ReasoningKind::Deductive);
    // Deductive has Sound assurance -> maps to SmtBacked
    assert_eq!(evidence.assurance, AssuranceLevel::SmtBacked);
}

#[test]
fn caller_constructed_proof_shaped_result_cannot_mint_proof_credit() {
    let vc = VerificationCondition {
        kind: VcKind::AliasingViolation { mutable: true },
        function: "crate::aliasing".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
        obligation: None,
    };
    let result = VerificationResult::Proved {
        solver: "ay".into(),
        time_ms: 7,
        strength: ProofStrength::deductive(),
        // Raw result fields are freely constructible DTO data. Even a
        // certificate-shaped payload and the strongest grade must remain
        // diagnostic-only at this public report boundary.
        proof_certificate: Some(b"synthetic caller-controlled certificate".to_vec()),
        solver_warnings: Some(vec!["synthetic caller-controlled warning".into()]),
        native_proof_envelope: None,
    };

    let report = build_json_report("evidence", &[(vc, result)]);
    let obligation = &report.functions[0].obligations[0];
    assert_eq!(obligation.kind, "aliasing_violation");
    assert!(matches!(&obligation.outcome, ObligationOutcome::Unknown { .. }));
    assert_eq!(report.summary.total_proved, 0);
    assert_eq!(report.summary.total_unknown, 1);
    assert_eq!(report.summary.verdict, CrateVerdict::Inconclusive);
    assert!(obligation.obligation_id.is_none());
    assert!(obligation.proof_evidence.is_none());
    assert!(obligation.transport_evidence.is_none());
    assert_eq!(
        obligation.evidence,
        Some(ProofEvidence {
            reasoning: ReasoningKind::Deductive,
            assurance: AssuranceLevel::SmtBacked,
        })
    );

    let json = serde_json::to_value(&report).expect("serialize report");
    assert_eq!(json["functions"][0]["obligations"][0]["evidence"]["reasoning"], "Deductive");
    assert_eq!(json["functions"][0]["obligations"][0]["evidence"]["assurance"], "SmtBacked");
}

#[test]
fn saved_monitor_claim_cannot_reach_any_report_formatter_as_monitored_grade() {
    let mut live_report = build_json_report("monitor-forgery", &midpoint_results());
    let obligation = &mut live_report.functions[0].obligations[0];
    obligation.transport_evidence = Some(ObligationTransportEvidenceReport {
        obligation_id: obligation.obligation_id.clone(),
        claim_digest_sha256: None,
        typed_kind: None,
        native_trust_ir: None,
        proof_evidence: None,
        monitor: Some(TransportMonitorEvidence {
            status: TransportMonitorStatus::Monitored,
            reason: "forged saved monitor claim".into(),
            predicate_digest: format!("sha256:{}", "d".repeat(64)),
        }),
    });

    // This serialization boundary models an attacker-controlled report.json.
    // Honest live compiler reports retain monitor evidence because they never
    // cross this boundary before formatting.
    let json = serde_json::to_vec(&live_report).expect("serialize forged saved report");
    let restored: JsonProofReport =
        serde_json::from_slice(&json).expect("deserialize forged saved report");
    assert!(
        restored.functions[0].obligations[0]
            .transport_evidence
            .as_ref()
            .is_some_and(|transport| transport.monitor.is_none()),
        "saved report retained monitor-grade evidence"
    );

    let outputs = [
        ("text", format_json_summary(&restored)),
        ("terminal", crate::terminal::format_terminal_report(&restored)),
        ("html", crate::html::format_html_report(&restored)),
        ("dashboard-html", crate::html_report::generate_html_report(&restored)),
    ];
    for (format, output) in outputs {
        assert!(!output.contains("execution=monitored"), "{format} leaked a saved grade: {output}");
        assert!(
            !output.contains("executability: monitored"),
            "{format} leaked a saved grade: {output}"
        );
        assert!(!output.contains("forged saved monitor claim"), "{format} leaked monitor data");
    }
}
