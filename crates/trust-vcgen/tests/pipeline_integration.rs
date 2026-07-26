// trust_vcgen/tests/pipeline_integration.rs: Cross-crate integration tests
//
// Exercises the full verification pipeline: vcgen -> router -> report.
// Uses ConstantFolderBackend so no external solvers are needed.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_report::{build_json_report, format_json_summary};
use trust_router::{Router, VerificationBackend};
use trust_types::*;
use trust_vcgen::{
    binary_security_family_counts, classify_binary_security_vc, filter_vcs_by_level, generate_vcs,
};

// ---------------------------------------------------------------------------
// Test helpers: build VerifiableFunction fixtures
// ---------------------------------------------------------------------------

/// Midpoint function: `(a + b) / 2` with checked add.
/// Produces 1 VC: ArithmeticOverflow for the addition.
fn midpoint_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "get_midpoint".to_string(),
        def_path: "test::get_midpoint".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
                LocalDecl { index: 4, ty: Ty::usize(), name: None },
                LocalDecl { index: 5, ty: Ty::usize(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
                                Operand::Copy(Place::local(4)),
                                Operand::Constant(ConstValue::Uint(2, 64)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(5))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::usize(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Division function: `x / y` with no guards.
/// Produces 1 VC: DivisionByZero.
fn division_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "divide".to_string(),
        def_path: "test::divide".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("y".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Shift function: `x << y` which may overflow.
/// Produces 1 VC: ShiftOverflow.
fn shift_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "shift_left".to_string(),
        def_path: "test::shift_left".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("y".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Shl,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Trivially safe function: returns a constant. No VCs generated.
fn trivially_safe_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "safe_const".to_string(),
        def_path: "test::safe_const".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::u32(), name: None }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(42, 64))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Helper: make a VC directly (not from MIR) with a given kind and formula.
fn make_vc(kind: VcKind, function: &str, formula: Formula) -> VerificationCondition {
    VerificationCondition {
        kind,
        function: function.into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
    }
}

// A router pinned to the deterministic `ConstantFolderBackend` only, so these
// pipeline tests stay independent of workspace feature unification (which
// otherwise registers the real in-process ay backend via `Router::new()`).
fn mock_router() -> Router {
    Router::with_backends(vec![Box::new(trust_router::constant_folder::ConstantFolderBackend)])
}

/// Raw `VerificationResult::Proved` values are useful diagnostic evidence, but
/// they are freely constructible and do not carry the request-bound TrustIR
/// proof/transport graph required for publication.  The report boundary must
/// therefore retain the obligation while downgrading it to `Unknown`.
fn assert_unstructured_proved_rows_are_publication_gated(
    report: &JsonProofReport,
    expected: usize,
) {
    let gated = report
        .functions
        .iter()
        .flat_map(|function| &function.obligations)
        .filter(|obligation| {
            matches!(
                &obligation.outcome,
                ObligationOutcome::Unknown { reason }
                    if reason.contains("proof_evidence is missing")
            )
        })
        .count();
    assert_eq!(gated, expected, "every unstructured Proved row must fail closed");
}

// ---------------------------------------------------------------------------
// vcgen -> router pipeline tests
// ---------------------------------------------------------------------------

#[test]
fn test_vcgen_to_router_midpoint_overflow_is_unknown() {
    // Generate VCs from midpoint MIR
    let func = midpoint_function();
    let vcs = generate_vcs(&func);
    assert_eq!(vcs.len(), 1, "midpoint produces exactly 1 VC");
    assert!(matches!(vcs[0].kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }));

    // Route through ConstantFolderBackend
    let router = mock_router(); // default = ConstantFolderBackend
    let results = router.verify_all(&vcs);
    assert_eq!(results.len(), 1);

    // The overflow formula contains variables, so ConstantFolderBackend returns Unknown
    let (vc, result) = &results[0];
    assert!(matches!(vc.kind, VcKind::ArithmeticOverflow { .. }));
    assert!(
        matches!(result, VerificationResult::Unknown { .. }),
        "overflow with variables should be Unknown from mock, got: {result:?}"
    );
}

#[test]
fn test_vcgen_to_router_division_by_zero_is_unknown() {
    let func = division_function();
    let vcs = generate_vcs(&func);

    let div_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::DivisionByZero)).collect();
    assert_eq!(div_vcs.len(), 1, "division produces exactly 1 div-by-zero VC");

    let router = mock_router();
    let result = router.verify_one(div_vcs[0]);

    // DivisionByZero formula has variables -> Unknown from mock
    assert!(
        matches!(result, VerificationResult::Unknown { .. }),
        "div-by-zero with variables should be Unknown, got: {result:?}"
    );
}

#[test]
fn test_vcgen_to_router_trivially_false_formula_is_proved() {
    // A VC with formula Bool(false) => UNSAT => Proved
    let vc = make_vc(VcKind::DivisionByZero, "safe_div", Formula::Bool(false));

    let router = mock_router();
    let result = router.verify_one(&vc);
    assert!(result.is_proved(), "Bool(false) should be proved, got: {result:?}");
    assert_eq!(result.solver_name(), "constant-folder");
}

#[test]
fn test_vcgen_to_router_trivially_true_formula_is_failed() {
    // A VC with formula Bool(true) => SAT => Failed (counterexample exists)
    let vc = make_vc(
        VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::u32(), Ty::u32()) },
        "overflow_fn",
        Formula::Bool(true),
    );

    let router = mock_router();
    let result = router.verify_one(&vc);
    assert!(result.is_failed(), "Bool(true) should be failed, got: {result:?}");
    assert_eq!(result.solver_name(), "constant-folder");
}

// ---------------------------------------------------------------------------
// vcgen -> router -> report pipeline tests
// ---------------------------------------------------------------------------

#[test]
fn test_full_pipeline_midpoint_report_structure() {
    let func = midpoint_function();
    let vcs = generate_vcs(&func);
    let router = mock_router();
    let results = router.verify_all(&vcs);

    let report = build_json_report("midpoint", &results);

    assert_eq!(report.crate_name, "midpoint");
    assert_eq!(report.summary.functions_analyzed, 1);
    assert_eq!(report.summary.total_obligations, 1);
    assert_eq!(report.functions[0].function, "get_midpoint");

    // The overflow with variables is Unknown. With Auto policy,
    // ArithmeticOverflow has a runtime fallback, but `build_json_report`
    // publishes through the canonical un-forgeable-proof gate
    // (`gate_report_for_publication` -> `sanitize_deserialized`): a policy
    // choice is not a compiler/monitor capability, so without Targo's private
    // live compiler-transport receipt the tentative RuntimeChecked disposition
    // is published as the fail-closed Unknown — visible, never dropped.
    assert_eq!(report.summary.total_runtime_checked, 0);
    assert_eq!(report.summary.total_unknown, 1);
    assert_eq!(report.functions[0].summary.verdict, FunctionVerdict::Inconclusive);
}

#[test]
fn test_full_pipeline_report_text_output_contains_key_info() {
    let func = midpoint_function();
    let vcs = generate_vcs(&func);
    let router = mock_router();
    let results = router.verify_all(&vcs);
    let report = build_json_report("midpoint", &results);
    let text = format_json_summary(&report);

    assert!(text.contains("get_midpoint"), "report should name the function");
    assert!(text.contains("1 obligations"), "report should show obligation count: {text}");
    assert!(text.contains("Verdict:"), "report should have a verdict line");
}

#[test]
fn test_full_pipeline_division_report() {
    let func = division_function();
    let vcs = generate_vcs(&func);
    let router = mock_router();
    let results = router.verify_all(&vcs);
    let report = build_json_report("division", &results);

    assert_eq!(report.crate_name, "division");
    // Division function produces div-by-zero VC(s)
    assert!(report.summary.total_obligations >= 1);
    assert_eq!(report.functions[0].function, "divide");
}

#[test]
fn test_full_pipeline_trivially_safe_no_obligations() {
    let func = trivially_safe_function();
    let vcs = generate_vcs(&func);
    assert!(vcs.is_empty(), "trivially safe function should produce 0 VCs");

    let router = mock_router();
    let results = router.verify_all(&vcs);
    assert!(results.is_empty());

    let report = build_json_report("safe_crate", &results);
    assert_eq!(report.summary.verdict, CrateVerdict::NoObligations);
    assert_eq!(report.summary.functions_analyzed, 0);
}

// ---------------------------------------------------------------------------
// Multiple VcKinds through the pipeline
// ---------------------------------------------------------------------------

#[test]
fn test_multiple_vc_kinds_through_pipeline() {
    let vcs = vec![
        make_vc(VcKind::DivisionByZero, "fn_a", Formula::Bool(false)),
        make_vc(
            VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::u32(), Ty::u32()) },
            "fn_a",
            Formula::Bool(false),
        ),
        make_vc(VcKind::IndexOutOfBounds, "fn_b", Formula::Bool(false)),
        make_vc(
            VcKind::CastOverflow { from_ty: Ty::i32(), to_ty: Ty::u32() },
            "fn_b",
            Formula::Bool(false),
        ),
        make_vc(
            VcKind::ShiftOverflow { op: BinOp::Shl, operand_ty: Ty::u32(), shift_ty: Ty::u32() },
            "fn_c",
            Formula::Bool(false),
        ),
        make_vc(VcKind::NegationOverflow { ty: Ty::i32() }, "fn_c", Formula::Bool(false)),
    ];

    let router = mock_router();
    let results = router.verify_all(&vcs);

    // All formulas are Bool(false) -> all should be Proved
    for (vc, result) in &results {
        assert!(
            result.is_proved(),
            "VC {:?} with Bool(false) should be proved, got: {result:?}",
            vc.kind
        );
    }

    let report = build_json_report("multi_kind", &results);
    assert_eq!(report.summary.total_obligations, 6);
    assert_eq!(report.summary.total_proved, 0);
    assert_eq!(report.summary.total_unknown, 6);
    assert_eq!(report.summary.total_failed, 0);
    assert_eq!(report.summary.verdict, CrateVerdict::Inconclusive);
    assert_eq!(report.summary.functions_analyzed, 3);
    assert_unstructured_proved_rows_are_publication_gated(&report, 6);
}

#[test]
fn test_binary_security_vc_kinds_report_json_tags_and_counts() {
    let cases = [
        (
            VcKind::SavedReturnAddressOverwrite {
                access_width_bytes: 8,
                slot: "saved_return_address".to_string(),
            },
            "saved_return_address_overwrite",
        ),
        (
            VcKind::FormatStringViolation {
                callee: "printf".to_string(),
                evidence: "format argument is tainted".to_string(),
            },
            "format_string_violation",
        ),
        (
            VcKind::TaintedIndirectBranch {
                sink_kind: "indirect_branch".to_string(),
                target: "unresolved_indirect_target".to_string(),
                evidence: "target taint unavailable".to_string(),
            },
            "tainted_indirect_branch",
        ),
        (
            VcKind::BinaryAbiContradiction {
                fact: "parameter 0 storage".to_string(),
                evidence: "ABI says RDI, storage says RSI".to_string(),
            },
            "binary_abi_contradiction",
        ),
        (VcKind::UseAfterFree, "use_after_free"),
        (VcKind::DoubleFree, "double_free"),
    ];

    let vcs: Vec<_> = cases
        .iter()
        .map(|(kind, _)| make_vc(kind.clone(), "binary_security_fn", Formula::Bool(true)))
        .collect();

    let router = mock_router();
    let results = router.verify_all(&vcs);
    let report = build_json_report("binary_security", &results);

    assert_eq!(report.summary.total_obligations, cases.len());
    assert_eq!(report.summary.total_failed, cases.len());
    assert_eq!(report.summary.total_runtime_checked, 0);
    assert_eq!(report.summary.total_unknown, 0);
    assert_eq!(report.summary.verdict, CrateVerdict::HasViolations);

    let function = &report.functions[0];
    assert_eq!(function.function, "binary_security_fn");
    assert_eq!(function.summary.total_obligations, cases.len());
    assert_eq!(function.summary.failed, cases.len());

    let json = serde_json::to_value(&report).expect("serialize binary security report");
    let obligations = json["functions"][0]["obligations"]
        .as_array()
        .expect("JSON report should contain obligation array");
    assert_eq!(obligations.len(), cases.len());

    let actual_tags: Vec<_> =
        obligations.iter().map(|obligation| obligation["kind"].as_str().unwrap()).collect();
    let expected_tags: Vec<_> = cases.iter().map(|(_, tag)| *tag).collect();
    assert_eq!(actual_tags, expected_tags);
    assert!(
        !actual_tags.contains(&"unknown"),
        "binary security VC families must not collapse to the generic unknown JSON kind"
    );

    let counts = binary_security_family_counts(&vcs);
    for tag in &expected_tags {
        assert_eq!(counts.get(*tag), Some(&1), "missing family count for `{tag}`");
    }
    assert_eq!(counts.len(), expected_tags.len());

    let classifications: Vec<_> =
        vcs.iter().map(|vc| classify_binary_security_vc(vc).unwrap()).collect();
    assert!(
        classifications
            .iter()
            .all(|classification| { !classification.proof_grade_blockers.is_empty() })
    );
    assert!(classifications.iter().any(|classification| {
        classification.family_id == "saved_return_address_overwrite"
            && classification
                .proof_grade_blockers
                .iter()
                .any(|blocker| blocker.code == "saved_return_address_alias")
    }));
    assert!(classifications.iter().any(|classification| {
        classification.family_id == "tainted_indirect_branch"
            && classification
                .proof_grade_blockers
                .iter()
                .any(|blocker| blocker.code == "missing_indirect_target_taint")
    }));
}

#[test]
fn test_l0_safety_kinds_raw_proved_but_report_fail_closed() {
    // All L0 safety VcKinds with trivially false formulas
    let safety_kinds: Vec<VcKind> = vec![
        VcKind::DivisionByZero,
        VcKind::RemainderByZero,
        VcKind::IndexOutOfBounds,
        VcKind::SliceBoundsCheck,
        VcKind::Unreachable,
        VcKind::Assertion { message: "test assert".to_string() },
        VcKind::ArithmeticOverflow { op: BinOp::Mul, operand_tys: (Ty::i32(), Ty::i32()) },
        VcKind::CastOverflow { from_ty: Ty::i32(), to_ty: Ty::Int { width: 8, signed: false } },
        VcKind::NegationOverflow { ty: Ty::i32() },
        VcKind::ShiftOverflow {
            op: BinOp::Shr,
            operand_ty: Ty::Int { width: 64, signed: false },
            shift_ty: Ty::u32(),
        },
    ];

    let vcs: Vec<_> = safety_kinds
        .into_iter()
        .map(|kind| make_vc(kind, "safety_fn", Formula::Bool(false)))
        .collect();

    let router = mock_router();
    let results = router.verify_all(&vcs);

    for (vc, result) in &results {
        assert_eq!(vc.kind.proof_level(), ProofLevel::L0Safety);
        assert!(result.is_proved());
    }

    let report = build_json_report("all_safety", &results);
    assert_eq!(report.summary.verdict, CrateVerdict::Inconclusive);
    assert_eq!(report.summary.total_proved, 0);
    assert_eq!(report.summary.total_unknown, vcs.len());
    assert_unstructured_proved_rows_are_publication_gated(&report, vcs.len());
}

// ---------------------------------------------------------------------------
// Batch verification: multiple functions at once
// ---------------------------------------------------------------------------

#[test]
fn test_batch_verification_multiple_functions() {
    let functions =
        vec![midpoint_function(), division_function(), shift_function(), trivially_safe_function()];

    let mut all_vcs: Vec<VerificationCondition> = Vec::new();
    for func in &functions {
        all_vcs.extend(generate_vcs(func));
    }

    // midpoint: 1 VC (overflow), division: 1+ VC (divzero), shift: 1 VC (shift),
    // safe: 0 VCs
    assert!(all_vcs.len() >= 3, "expected at least 3 VCs from batch, got {}", all_vcs.len());

    let router = mock_router();
    let results = router.verify_all(&all_vcs);
    assert_eq!(results.len(), all_vcs.len());

    let report = build_json_report("batch_crate", &results);
    // Functions with VCs: midpoint, divide, shift_left (safe_const has none)
    assert!(
        report.summary.functions_analyzed >= 3,
        "at least 3 functions should appear in report, got {}",
        report.summary.functions_analyzed
    );
    assert_eq!(
        report.summary.total_obligations,
        all_vcs.len(),
        "total obligations should match VC count"
    );
}

#[test]
fn test_batch_verification_parallel() {
    // Use parallel verification with multiple functions
    let vcs: Vec<_> = (0..10)
        .map(|i| make_vc(VcKind::DivisionByZero, &format!("fn_{i}"), Formula::Bool(false)))
        .collect();

    let router = mock_router();
    let results = router.verify_all_parallel(&vcs, 4);
    assert_eq!(results.len(), 10);

    for (_, result) in &results {
        assert!(result.is_proved());
    }

    let report = build_json_report("parallel_batch", &results);
    assert_eq!(report.summary.total_proved, 0);
    assert_eq!(report.summary.total_unknown, 10);
    assert_eq!(report.summary.functions_analyzed, 10);
    assert_eq!(report.summary.verdict, CrateVerdict::Inconclusive);
    assert_unstructured_proved_rows_are_publication_gated(&report, 10);
}

// ---------------------------------------------------------------------------
// Failure handling: VCs that should fail produce correct results
// ---------------------------------------------------------------------------

#[test]
fn test_failed_vc_produces_correct_report() {
    let vcs = vec![
        make_vc(
            VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::u32(), Ty::u32()) },
            "overflow_fn",
            Formula::Bool(true), // SAT -> Failed
        ),
        make_vc(
            VcKind::DivisionByZero,
            "overflow_fn",
            Formula::Bool(false), // UNSAT -> Proved
        ),
    ];

    let router = mock_router();
    let results = router.verify_all(&vcs);

    assert!(results[0].1.is_failed(), "Bool(true) should produce Failed");
    assert!(results[1].1.is_proved(), "Bool(false) should produce Proved");

    let report = build_json_report("failure_test", &results);
    assert_eq!(report.summary.total_failed, 1);
    assert_eq!(report.summary.total_proved, 0);
    assert_eq!(report.summary.total_unknown, 1);
    assert_eq!(report.summary.verdict, CrateVerdict::HasViolations);
    assert_unstructured_proved_rows_are_publication_gated(&report, 1);

    let func = &report.functions[0];
    assert_eq!(func.summary.verdict, FunctionVerdict::HasViolations);

    // Check that the failed obligation has the right kind
    let failed_ob = func
        .obligations
        .iter()
        .find(|ob| matches!(ob.outcome, ObligationOutcome::Failed { .. }))
        .expect("should have a failed obligation");
    assert_eq!(failed_ob.kind, "arithmetic_overflow_add");
}

#[test]
fn test_unknown_vc_report_outcome() {
    let vc = make_vc(
        VcKind::Postcondition,
        "complex_fn",
        Formula::Var("x".into(), Sort::Int), // Unknown from mock
    );

    let router = mock_router();
    let result = router.verify_one(&vc);
    assert!(matches!(result, VerificationResult::Unknown { .. }));

    let results = vec![(vc, result)];
    let report = build_json_report("unknown_test", &results);

    // Postcondition has no runtime fallback, so Unknown stays Unknown
    assert_eq!(report.summary.total_unknown, 1);
    assert_eq!(report.summary.verdict, CrateVerdict::Inconclusive);
    assert_eq!(report.functions[0].summary.verdict, FunctionVerdict::Inconclusive);
}

#[test]
fn test_mixed_results_across_functions() {
    let vcs_and_formulas = vec![
        // Function A: all proved
        make_vc(VcKind::DivisionByZero, "fn_safe", Formula::Bool(false)),
        make_vc(
            VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::u32(), Ty::u32()) },
            "fn_safe",
            Formula::Bool(false),
        ),
        // Function B: has a failure
        make_vc(VcKind::IndexOutOfBounds, "fn_buggy", Formula::Bool(true)),
        // Function C: unknown result
        make_vc(VcKind::Postcondition, "fn_complex", Formula::Var("result".into(), Sort::Int)),
    ];

    let router = mock_router();
    let results = router.verify_all(&vcs_and_formulas);
    let report = build_json_report("mixed", &results);

    assert_eq!(report.summary.functions_analyzed, 3);
    assert_eq!(report.summary.total_proved, 0);
    assert_eq!(report.summary.total_failed, 1);
    assert_eq!(report.summary.total_unknown, 3);
    // IndexOutOfBounds is L0 safety -> with Auto policy, its Failed stays Failed
    assert_eq!(report.summary.verdict, CrateVerdict::HasViolations);

    // Check per-function verdicts
    let safe_fn = report.functions.iter().find(|f| f.function == "fn_safe").unwrap();
    assert_eq!(safe_fn.summary.verdict, FunctionVerdict::Inconclusive);

    let buggy_fn = report.functions.iter().find(|f| f.function == "fn_buggy").unwrap();
    assert_eq!(buggy_fn.summary.verdict, FunctionVerdict::HasViolations);

    let complex_fn = report.functions.iter().find(|f| f.function == "fn_complex").unwrap();
    assert_eq!(complex_fn.summary.verdict, FunctionVerdict::Inconclusive);
    assert_unstructured_proved_rows_are_publication_gated(&report, 2);
}

// ---------------------------------------------------------------------------
// Level filtering tests: ProofLevel filtering before routing
// ---------------------------------------------------------------------------

#[test]
fn test_level_filter_l0_removes_functional_and_domain_vcs() {
    let vcs = vec![
        make_vc(VcKind::DivisionByZero, "f", Formula::Bool(false)),
        make_vc(VcKind::Postcondition, "f", Formula::Bool(false)),
        make_vc(VcKind::Deadlock, "f", Formula::Bool(false)),
        make_vc(VcKind::Precondition { callee: "g".to_string() }, "f", Formula::Bool(false)),
    ];

    let filtered = filter_vcs_by_level(vcs, ProofLevel::L0Safety);
    assert_eq!(filtered.len(), 1, "only DivisionByZero is L0");
    assert!(matches!(filtered[0].kind, VcKind::DivisionByZero));

    // Route filtered VCs
    let router = mock_router();
    let results = router.verify_all(&filtered);
    assert_eq!(results.len(), 1);
    assert!(results[0].1.is_proved());

    let report = build_json_report("l0_only", &results);
    assert_eq!(report.summary.total_proved, 0);
    assert_eq!(report.summary.total_unknown, 1);
    assert_eq!(report.summary.verdict, CrateVerdict::Inconclusive);
    assert_unstructured_proved_rows_are_publication_gated(&report, 1);
}

#[test]
fn test_level_filter_l1_keeps_safety_and_functional() {
    let vcs = vec![
        make_vc(VcKind::DivisionByZero, "f", Formula::Bool(false)),
        make_vc(VcKind::Postcondition, "f", Formula::Bool(false)),
        make_vc(VcKind::Deadlock, "f", Formula::Bool(false)),
        make_vc(VcKind::Temporal { property: "liveness".to_string(), machine: None }, "f", Formula::Bool(false)),
    ];

    let filtered = filter_vcs_by_level(vcs, ProofLevel::L1Functional);
    assert_eq!(filtered.len(), 2, "L0 + L1 = DivisionByZero + Postcondition");

    for vc in &filtered {
        assert!(vc.kind.proof_level() <= ProofLevel::L1Functional);
    }
}

#[test]
fn test_level_filter_l2_keeps_all() {
    let vcs = vec![
        make_vc(VcKind::DivisionByZero, "f", Formula::Bool(false)),
        make_vc(VcKind::Postcondition, "f", Formula::Bool(false)),
        make_vc(VcKind::Deadlock, "f", Formula::Bool(false)),
    ];

    let filtered = filter_vcs_by_level(vcs.clone(), ProofLevel::L2Domain);
    assert_eq!(filtered.len(), 3, "L2 should keep all VCs");
}

#[test]
fn test_level_filtering_then_route_then_report() {
    // Full pipeline with level filtering: L0 only
    let func = midpoint_function();
    let all_vcs = generate_vcs(&func);

    // Add a synthetic L1 VC
    let mut vcs = all_vcs;
    vcs.push(make_vc(VcKind::Postcondition, "get_midpoint", Formula::Bool(false)));

    // Filter to L0 only
    let filtered = filter_vcs_by_level(vcs.clone(), ProofLevel::L0Safety);
    assert!(filtered.len() < vcs.len(), "filtering should remove L1 postcondition");

    // Route and report L0-only
    let router = mock_router();
    let results = router.verify_all(&filtered);
    let report = build_json_report("l0_filtered", &results);

    // Only the overflow VC should remain
    assert_eq!(report.summary.total_obligations, filtered.len());
    for func_report in &report.functions {
        for ob in &func_report.obligations {
            assert_eq!(ob.proof_level, ProofLevel::L0Safety);
        }
    }
}

// ---------------------------------------------------------------------------
// Report serialization roundtrip through the full pipeline
// ---------------------------------------------------------------------------

#[test]
fn test_pipeline_report_json_roundtrip() {
    let func = midpoint_function();
    let vcs = generate_vcs(&func);
    let router = mock_router();
    let results = router.verify_all(&vcs);
    let report = build_json_report("roundtrip_test", &results);

    let json = serde_json::to_string_pretty(&report).expect("serialize report");
    let deserialized: JsonProofReport = serde_json::from_str(&json).expect("deserialize report");

    assert_eq!(deserialized.crate_name, "roundtrip_test");
    assert_eq!(deserialized.summary.total_obligations, report.summary.total_obligations);
    assert_eq!(deserialized.summary.functions_analyzed, report.summary.functions_analyzed);
    assert_eq!(deserialized.summary.verdict, report.summary.verdict);
}

// ---------------------------------------------------------------------------
// Custom backend through pipeline
// ---------------------------------------------------------------------------

/// A backend that always returns Failed with a counterexample.
struct FailingBackend;

impl VerificationBackend for FailingBackend {
    fn name(&self) -> &str {
        "failing_backend"
    }

    fn can_handle(&self, _vc: &VerificationCondition) -> bool {
        true
    }

    fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
        VerificationResult::Failed {
            solver: "failing_backend".into(),
            time_ms: 1,
            counterexample: Some(Counterexample::new(vec![
                ("x".to_string(), CounterexampleValue::Uint(u64::MAX as u128)),
                ("y".to_string(), CounterexampleValue::Int(0)),
            ])),
        }
    }
}

#[test]
fn test_custom_backend_counterexample_in_report() {
    let vc = make_vc(VcKind::DivisionByZero, "test_fn", Formula::Var("y".into(), Sort::Int));

    let router = Router::with_backends(vec![Box::new(FailingBackend)]);
    let results = router.verify_all(&[vc]);

    assert_eq!(results.len(), 1);
    let (_, result) = &results[0];
    assert!(result.is_failed());

    let report = build_json_report("cex_test", &results);
    let func = &report.functions[0];
    let ob = &func.obligations[0];

    assert!(matches!(
        &ob.outcome,
        ObligationOutcome::Failed { counterexample: Some(cex) }
            if cex.variables.len() == 2
    ));

    // Verify counterexample in text output
    let text = format_json_summary(&report);
    assert!(text.contains("FAILED"));
    assert!(text.contains("counterexample"));
    assert!(text.contains("x = 18446744073709551615"));
    assert!(text.contains("y = 0"));
}

// ---------------------------------------------------------------------------
// End-to-end: vcgen from MIR -> filter -> route -> report -> serialize
// ---------------------------------------------------------------------------

#[test]
fn test_end_to_end_pipeline_multiple_functions_mixed_verdicts() {
    // Build VCs from multiple MIR functions
    let mut all_vcs = Vec::new();
    all_vcs.extend(generate_vcs(&midpoint_function()));
    all_vcs.extend(generate_vcs(&division_function()));
    all_vcs.extend(generate_vcs(&trivially_safe_function()));

    // Add some synthetic VCs for coverage
    all_vcs.push(make_vc(
        VcKind::Postcondition,
        "contract_fn",
        Formula::Bool(false), // provable
    ));
    all_vcs.push(make_vc(
        VcKind::Deadlock,
        "concurrent_fn",
        Formula::Bool(true), // violation
    ));

    // Filter to L0+L1 (excludes L2 Deadlock)
    let filtered = filter_vcs_by_level(all_vcs.clone(), ProofLevel::L1Functional);
    let deadlock_removed = !filtered.iter().any(|vc| matches!(vc.kind, VcKind::Deadlock));
    assert!(deadlock_removed, "L1 filter should remove L2 Deadlock VC");

    // Route
    let router = mock_router();
    let results = router.verify_all(&filtered);

    // Build report
    let report = build_json_report("e2e_mixed", &results);

    // Verify structural properties
    assert!(report.summary.total_obligations > 0);
    assert!(report.summary.functions_analyzed >= 2);

    // Serialize roundtrip
    let json = serde_json::to_string(&report).expect("serialize");
    let roundtrip: JsonProofReport = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(roundtrip.crate_name, "e2e_mixed");
    assert_eq!(roundtrip.summary.total_obligations, report.summary.total_obligations);

    // Text summary should mention key elements
    let text = format_json_summary(&report);
    assert!(text.contains("Verdict:"));
}
