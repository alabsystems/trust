// Cross-crate integration tests for the Trust verification pipeline.
//
// Exercises the full pipeline: trust-types (IR) -> trust_vcgen (VC generation)
// -> trust-router (dispatch) -> trust-report (output), testing crate boundary
// interactions that unit tests in individual crates cannot cover.
//
// Part of #151
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

// A router pinned to the deterministic `ConstantFolderBackend` only, so these
// cross-crate plumbing tests stay independent of workspace feature unification
// (which otherwise registers the real in-process ay backend via `Router::new()`).
fn mock_router() -> trust_router::Router {
    trust_router::Router::with_backends(vec![Box::new(
        trust_router::constant_folder::ConstantFolderBackend,
    )])
}

// ---------------------------------------------------------------------------
// Helpers: MIR function builders
// ---------------------------------------------------------------------------

/// Build the canonical midpoint function MIR: `fn get_midpoint(a: usize, b: usize) -> usize`
/// Has a checked add (overflow VC) and a constant-divisor divide (no div-by-zero VC).
fn midpoint_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "get_midpoint".to_string(),
        def_path: "pipeline::get_midpoint".to_string(),
        span: SourceSpan {
            file: "src/pipeline.rs".to_string(),
            line_start: 1,
            col_start: 1,
            line_end: 3,
            col_end: 1,
        },
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
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                        unwind: UnwindEdge::Unreachable,
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

/// Build a safe division function with a variable divisor: `fn divide(x: u32, y: u32) -> u32`
/// Produces a div-by-zero VC because y is not constant.
fn division_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "divide".to_string(),
        def_path: "pipeline::divide".to_string(),
        span: SourceSpan {
            file: "src/pipeline.rs".to_string(),
            line_start: 10,
            col_start: 1,
            line_end: 12,
            col_end: 1,
        },
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

/// Build a guarded function: `fn guarded_div(flag: bool, x: u32, y: u32) -> u32`
/// Division is only reachable when flag is true (SwitchInt guard).
fn guarded_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "guarded_div".to_string(),
        def_path: "pipeline::guarded_div".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("flag".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("y".into()) },
                LocalDecl { index: 4, ty: Ty::u32(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(1, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
                                Operand::Copy(Place::local(2)),
                                Operand::Copy(Place::local(3)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(4))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 3,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Build an identity function: `fn identity(x: u32) -> u32` -- no VCs at all.
fn identity_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "identity".to_string(),
        def_path: "pipeline::identity".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

// ===========================================================================
// Test 1: Full pipeline end-to-end (types -> vcgen -> router -> report)
// ===========================================================================

#[test]
fn test_pipeline_types_vcgen_router_report_midpoint() {
    // Step 1: Create VerifiableFunction from trust-types
    let func = midpoint_function();

    // Step 2: Generate VCs with trust_vcgen
    let vcs = trust_vcgen::generate_vcs(&func);
    assert_eq!(vcs.len(), 1, "midpoint should produce exactly 1 VC (overflow)");
    assert!(
        matches!(vcs[0].kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }),
        "the VC must be arithmetic overflow for Add"
    );
    assert_eq!(vcs[0].kind.proof_level(), ProofLevel::L0Safety);

    // Step 3: Dispatch through trust-router (mock backend)
    let router = mock_router();
    let results = router.verify_all(&vcs);
    assert_eq!(results.len(), 1, "one result per VC");

    // Mock backend evaluates formulas with variables as Unknown
    let (ref vc, ref result) = results[0];
    assert_eq!(vc.function, "get_midpoint");
    // The midpoint overflow formula contains variables, so mock returns Unknown
    assert!(
        matches!(result, VerificationResult::Unknown { .. }),
        "mock backend should return Unknown for variable-containing formula"
    );

    // Step 4: Build report with trust-report
    let json_report = trust_report::build_json_report("pipeline_test", &results);
    assert_eq!(json_report.crate_name, "pipeline_test");
    assert_eq!(json_report.summary.functions_analyzed, 1);
    assert_eq!(json_report.summary.total_obligations, 1);

    // Step 5: Verify JSON serialization roundtrip
    let json = serde_json::to_string(&json_report).unwrap();
    let roundtrip: JsonProofReport = serde_json::from_str(&json).unwrap();
    assert_eq!(roundtrip.summary.total_obligations, 1);
    assert_eq!(roundtrip.functions[0].function, "get_midpoint");
}

// ===========================================================================
// Test 2: Multiple functions with different VC types
// ===========================================================================

#[test]
fn test_pipeline_multiple_functions_batch_verification() {
    let functions =
        vec![midpoint_function(), division_function(), guarded_function(), identity_function()];

    // Generate VCs for all functions
    let mut all_vcs = Vec::new();
    for func in &functions {
        let vcs = trust_vcgen::generate_vcs(func);
        all_vcs.extend(vcs);
    }

    // midpoint: 1 overflow VC
    // divide: 1 div-by-zero VC
    // guarded_div: 1 guarded div-by-zero VC
    // identity: 0 VCs
    assert!(
        all_vcs.len() >= 3,
        "should produce at least 3 VCs from the 4 functions, got {}",
        all_vcs.len()
    );

    // Verify VC kinds are present
    let has_overflow =
        all_vcs.iter().any(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. }));
    let has_divzero = all_vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero));
    assert!(has_overflow, "should have overflow VC from midpoint");
    assert!(has_divzero, "should have div-by-zero VC from divide or guarded_div");

    // Dispatch all VCs through router
    let router = mock_router();
    let results = router.verify_all(&all_vcs);
    assert_eq!(results.len(), all_vcs.len());

    // Build JSON report spanning multiple functions
    let report = trust_report::build_json_report("batch_test", &results);
    assert!(report.summary.functions_analyzed >= 2, "at least 2 functions should appear in report");

    // Verify report has data for each function that produced VCs
    let function_names: Vec<&str> = report.functions.iter().map(|f| f.function.as_str()).collect();
    assert!(function_names.contains(&"get_midpoint"));

    // Check report text formatting
    let text = trust_report::format_json_summary(&report);
    assert!(!text.is_empty());
    assert!(text.contains("Verdict:"));
}

// ===========================================================================
// Test 3: Guard conditions flow through the full pipeline
// ===========================================================================

#[test]
fn test_pipeline_guarded_vc_carries_guard_to_report() {
    let func = guarded_function();

    // Generate VCs -- the div-by-zero VC should have a guard
    let vcs = trust_vcgen::generate_vcs(&func);
    let div_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::DivisionByZero)).collect();
    assert_eq!(div_vcs.len(), 1, "guarded_div should produce 1 div-by-zero VC");

    // Verify the guard is embedded in the formula
    match &div_vcs[0].formula {
        Formula::And(clauses) => {
            assert_eq!(clauses.len(), 2, "guarded VC = And([guard, violation])");
        }
        _ => panic!("expected guarded formula to be And(...)"),
    }

    // Route and build report
    let router = mock_router();
    let results = router.verify_all(&vcs);
    let report = trust_report::build_json_report("guarded_test", &results);

    // The report should have obligations for guarded_div
    let func_report = report
        .functions
        .iter()
        .find(|f| f.function == "guarded_div")
        .expect("guarded_div should be in report");
    assert!(func_report.summary.total_obligations >= 1);
}

// ===========================================================================
// Test 4: VC level filtering flows through pipeline
// ===========================================================================

#[test]
fn test_pipeline_vc_level_filtering() {
    let func = midpoint_function();
    let all_vcs = trust_vcgen::generate_vcs(&func);

    // Filter to L0 only
    let l0_vcs = trust_vcgen::filter_vcs_by_level(all_vcs.clone(), ProofLevel::L0Safety);
    assert!(!l0_vcs.is_empty(), "midpoint should have L0 VCs");

    // All midpoint VCs should be L0
    for vc in &l0_vcs {
        assert_eq!(vc.kind.proof_level(), ProofLevel::L0Safety);
    }

    // Route filtered VCs
    let router = mock_router();
    let results = router.verify_all(&l0_vcs);
    let report = trust_report::build_json_report("filtered_test", &results);

    // Report should contain only L0 obligations
    for func in &report.functions {
        for ob in &func.obligations {
            assert_eq!(ob.proof_level, ProofLevel::L0Safety);
        }
    }
}

// ===========================================================================
// Test 5: Parallel verification produces same results as sequential
// ===========================================================================

#[test]
fn test_pipeline_parallel_verification_consistency() {
    let functions = vec![midpoint_function(), division_function(), guarded_function()];

    let mut all_vcs = Vec::new();
    for func in &functions {
        all_vcs.extend(trust_vcgen::generate_vcs(func));
    }

    let router = mock_router();

    // Sequential
    let sequential_results = router.verify_all(&all_vcs);

    // Parallel (4 threads)
    let parallel_results = router.verify_all_parallel(&all_vcs, 4);

    assert_eq!(sequential_results.len(), parallel_results.len());

    // Same VCs produce same outcomes (may differ in timing)
    for (seq, par) in sequential_results.iter().zip(parallel_results.iter()) {
        assert_eq!(seq.0.function, par.0.function, "VC function names must match");
        assert_eq!(seq.0.kind.description(), par.0.kind.description(), "VC kinds must match");

        // Both should have the same proof status category
        let seq_proved = seq.1.is_proved();
        let par_proved = par.1.is_proved();
        let seq_failed = seq.1.is_failed();
        let par_failed = par.1.is_failed();
        assert_eq!(seq_proved, par_proved, "proved status must match");
        assert_eq!(seq_failed, par_failed, "failed status must match");
    }

    // Both produce valid reports
    let seq_report = trust_report::build_json_report("seq", &sequential_results);
    let par_report = trust_report::build_json_report("par", &parallel_results);

    assert_eq!(seq_report.summary.total_obligations, par_report.summary.total_obligations);
    assert_eq!(seq_report.summary.total_proved, par_report.summary.total_proved);
}

// ===========================================================================
// Test 6: Raw proved statuses fail closed at the publication boundary
// ===========================================================================

#[test]
fn test_pipeline_raw_proved_statuses_are_not_published_as_verified() {
    // These freely constructible statuses are useful diagnostic inputs, but
    // they do not carry publication-grade structured/transport proof evidence.
    let results = vec![
        (
            VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: "safe_fn".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false), // trivially UNSAT -> proved
                contract_metadata: None,
                obligation: None,
            },
            VerificationResult::Proved {
                solver: "constant-folder".into(),
                time_ms: 0,
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
                function: "safe_fn".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
                obligation: None,
            },
            VerificationResult::Proved {
                solver: "constant-folder".into(),
                time_ms: 0,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        ),
    ];

    let report = trust_report::build_json_report("all_proved", &results);
    assert_eq!(report.summary.verdict, CrateVerdict::Inconclusive);
    assert_eq!(report.summary.total_proved, 0);
    assert_eq!(report.summary.total_unknown, 2);
    assert_eq!(report.summary.total_runtime_checked, 0);
    assert_eq!(report.summary.total_failed, 0);
    assert_eq!(report.functions[0].summary.verdict, FunctionVerdict::Inconclusive);
}

// ===========================================================================
// Test 7: Pipeline with mixed results (proved + failed + unknown)
// ===========================================================================

#[test]
fn test_pipeline_mixed_results_verdict() {
    let results = vec![
        (
            VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: "fn_a".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
                obligation: None,
            },
            VerificationResult::Proved {
                solver: "constant-folder".into(),
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
                function: "fn_b".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(true),
                contract_metadata: None,
                obligation: None,
            },
            VerificationResult::Failed {
                solver: "constant-folder".into(),
                time_ms: 1,
                counterexample: Some(Counterexample::new(vec![
                    ("a".to_string(), CounterexampleValue::Uint(u32::MAX as u128)),
                    ("b".to_string(), CounterexampleValue::Uint(1)),
                ])),
            },
        ),
        (
            VerificationCondition {
                kind: VcKind::IndexOutOfBounds,
                function: "fn_c".into(),
                location: SourceSpan::default(),
                formula: Formula::Var("idx".to_string(), Sort::Int),
                contract_metadata: None,
                obligation: None,
            },
            VerificationResult::Unknown {
                solver: "constant-folder".into(),
                time_ms: 1,
                reason: "complex formula".to_string(),
            },
        ),
    ];

    let report = trust_report::build_json_report("mixed", &results);
    assert_eq!(report.summary.functions_analyzed, 3);
    assert_eq!(report.summary.total_proved, 0);
    assert_eq!(report.summary.total_failed, 1);
    // A freely constructible RuntimeChecked status is only a policy proposal.
    // Without the compiler's private certified-monitor receipt the public
    // report gate must scrub it to Unknown.
    assert_eq!(report.summary.total_unknown, 2);
    assert_eq!(report.summary.total_runtime_checked, 0);
    assert_eq!(report.summary.verdict, CrateVerdict::HasViolations);

    // Check counterexample flows through to report
    let fn_b = report.functions.iter().find(|f| f.function == "fn_b").unwrap();
    let failed_ob = fn_b
        .obligations
        .iter()
        .find(|o| matches!(o.outcome, ObligationOutcome::Failed { .. }))
        .unwrap();
    if let ObligationOutcome::Failed { counterexample: Some(cex) } = &failed_ob.outcome {
        assert_eq!(cex.variables.len(), 2);
        assert_eq!(cex.variables[0].name, "a");
    } else {
        panic!("expected failed with counterexample");
    }
}

// ===========================================================================
// Test 8: Backend plan selection across the pipeline
// ===========================================================================

#[test]
fn test_pipeline_backend_plan_for_different_vc_kinds() {
    let router = mock_router();

    let l0_vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
        obligation: None,
    };

    let l1_vc = VerificationCondition {
        kind: VcKind::Postcondition,
        function: "g".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
        obligation: None,
    };

    let l2_vc = VerificationCondition {
        kind: VcKind::Temporal { property: "liveness".to_string(), machine: None },
        function: "h".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
        obligation: None,
    };

    // All three should get a backend plan from the mock router
    let plan_l0 = router.backend_plan(&l0_vc);
    let plan_l1 = router.backend_plan(&l1_vc);
    let plan_l2 = router.backend_plan(&l2_vc);

    assert!(!plan_l0.is_empty(), "L0 VC should have at least one backend");
    assert!(!plan_l1.is_empty(), "L1 VC should have at least one backend");
    assert!(!plan_l2.is_empty(), "L2 VC should have at least one backend");

    // Mock backend can handle all three
    assert!(plan_l0[0].can_handle);
    assert!(plan_l1[0].can_handle);
    assert!(plan_l2[0].can_handle);
}

// ===========================================================================
// Test 9: JSON and NDJSON report generation from pipeline output
// ===========================================================================

#[test]
fn test_pipeline_json_and_ndjson_report_generation() {
    let functions = vec![midpoint_function(), division_function()];
    let mut all_vcs = Vec::new();
    for func in &functions {
        all_vcs.extend(trust_vcgen::generate_vcs(func));
    }

    let router = mock_router();
    let results = router.verify_all(&all_vcs);
    let report = trust_report::build_json_report("ndjson_pipeline", &results);

    // JSON output
    let json = serde_json::to_string_pretty(&report).unwrap();
    let json_value: serde_json::Value = serde_json::from_str(&json).unwrap();

    // Required top-level fields
    assert!(json_value.get("metadata").is_some());
    assert!(json_value.get("crate_name").is_some());
    assert!(json_value.get("summary").is_some());
    assert!(json_value.get("functions").is_some());

    // NDJSON output
    let mut ndjson_buf = Vec::new();
    trust_report::write_ndjson(&report, &mut ndjson_buf).unwrap();
    let ndjson = String::from_utf8(ndjson_buf).unwrap();
    let lines: Vec<&str> = ndjson.trim_end().split('\n').collect();

    // header + N functions + footer
    assert_eq!(
        lines.len(),
        report.functions.len() + 2,
        "NDJSON should have header + functions + footer"
    );

    // Each line must be valid JSON
    for (i, line) in lines.iter().enumerate() {
        let parsed: serde_json::Value = serde_json::from_str(line)
            .unwrap_or_else(|e| panic!("NDJSON line {i} not valid JSON: {e}"));
        assert!(parsed.get("record_type").is_some());
    }
}

// ===========================================================================
// Test 10: CrateVerificationResult flows to report
// ===========================================================================

#[test]
fn test_pipeline_crate_verification_result_to_report() {
    let func = midpoint_function();
    let vcs = trust_vcgen::generate_vcs(&func);
    let router = mock_router();
    let results = router.verify_all(&vcs);

    // Build a CrateVerificationResult
    let mut crate_result = CrateVerificationResult::new("crate_pipeline");
    crate_result.add_function(FunctionVerificationResult {
        function_path: func.def_path.clone(),
        function_name: func.name.clone(),
        results,
        from_notes: 2,
        with_assumptions: 1,
    });

    // Build report from CrateVerificationResult
    let report = trust_report::build_crate_verification_report(&crate_result);
    assert_eq!(report.crate_name, "crate_pipeline");
    assert_eq!(report.summary.functions_analyzed, 1);

    // Format with cross-function stats
    let text = trust_report::format_crate_verification_summary(&report, &crate_result);
    assert!(text.contains("Cross-function composition:"));
    assert!(text.contains("2 VCs satisfied from proved callee specs (free)"));
    assert!(text.contains("1 VCs sent to solver with callee assumptions"));
}

// ===========================================================================
// Test 11: Empty pipeline (no functions) produces valid empty report
// ===========================================================================

#[test]
fn test_pipeline_empty_input_produces_valid_report() {
    let vcs: Vec<VerificationCondition> = vec![];
    let router = mock_router();
    let results = router.verify_all(&vcs);

    assert!(results.is_empty());

    let report = trust_report::build_json_report("empty_pipeline", &results);
    assert_eq!(report.summary.functions_analyzed, 0);
    assert_eq!(report.summary.total_obligations, 0);
    assert_eq!(report.summary.verdict, CrateVerdict::NoObligations);

    // NDJSON for empty crate
    let mut buf = Vec::new();
    trust_report::write_ndjson(&report, &mut buf).unwrap();
    let ndjson = String::from_utf8(buf).unwrap();
    let lines: Vec<&str> = ndjson.trim_end().split('\n').collect();
    assert_eq!(lines.len(), 2, "empty crate: header + footer");
}

// ===========================================================================
// Test 12: Path map and discovered clauses integrate with pipeline
// ===========================================================================

#[test]
fn test_pipeline_path_map_integrates_with_vcgen() {
    let func = guarded_function();

    // Discover clauses (trust_vcgen public API)
    let clauses = trust_vcgen::discover_clauses(&func);
    assert!(!clauses.is_empty(), "should discover SwitchInt clauses");

    // Build path map (trust_vcgen public API)
    let path_map = trust_vcgen::build_path_map(&func);
    assert_eq!(path_map.len(), 3, "3 blocks in guarded function");

    // Verify guard accumulation is reflected in generated VCs
    let vcs = trust_vcgen::generate_vcs(&func);
    let div_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::DivisionByZero)).collect();

    // The div-by-zero VC in bb1 should have the SwitchInt guard
    assert_eq!(div_vcs.len(), 1);
    assert!(
        matches!(&div_vcs[0].formula, Formula::And(_)),
        "guarded VC should be wrapped in And(guard, violation)"
    );

    // Clauses and path map should serialize for report consumption
    let clauses_json = serde_json::to_string(&clauses).unwrap();
    let path_map_json = serde_json::to_string(&path_map).unwrap();
    assert!(!clauses_json.is_empty());
    assert!(!path_map_json.is_empty());
}

// ===========================================================================
// Test 13: Router with Arc backends through pipeline
// ===========================================================================

#[test]
fn test_pipeline_arc_backends_verification() {
    use std::sync::Arc;

    let backends: Vec<Arc<dyn trust_router::VerificationBackend>> =
        vec![Arc::new(trust_router::constant_folder::ConstantFolderBackend)];
    let router = trust_router::Router::with_arc_backends(backends);

    let func = division_function();
    let vcs = trust_vcgen::generate_vcs(&func);

    let results = router.verify_all(&vcs);
    assert_eq!(results.len(), vcs.len());

    // Verify Arc-backed router returns same results
    let arc_backends = router.arc_backends();
    assert_eq!(arc_backends.len(), 1);
    assert_eq!(arc_backends[0].name(), "constant-folder");
}

// ===========================================================================
// Test 14: Report with runtime check policy through pipeline
// ===========================================================================

#[test]
fn test_pipeline_runtime_check_policy_propagation() {
    // Unknown result for an index-out-of-bounds VC
    let results = vec![(
        VerificationCondition {
            kind: VcKind::IndexOutOfBounds,
            function: "lookup".into(),
            location: SourceSpan::default(),
            formula: Formula::Var("idx".to_string(), Sort::Int),
            contract_metadata: None,
            obligation: None,
        },
        VerificationResult::Unknown {
            solver: "constant-folder".into(),
            time_ms: 5,
            reason: "nonlinear".to_string(),
        },
    )];

    // Auto policy may tentatively classify an unknown OOB as runtime checked,
    // but this raw-result adapter has no private certified-monitor receipt.
    // Its publication gate therefore fails closed to Unknown.
    let auto_report = trust_report::build_json_report_with_policy(
        "auto_policy",
        &results,
        RuntimeCheckPolicy::Auto,
        true,
    );
    assert_eq!(auto_report.summary.total_runtime_checked, 0);
    assert_eq!(auto_report.summary.total_unknown, 1);

    // ForceStatic policy: should keep as Unknown
    let static_report = trust_report::build_json_report_with_policy(
        "static_policy",
        &results,
        RuntimeCheckPolicy::ForceStatic,
        true,
    );
    assert_eq!(static_report.summary.total_runtime_checked, 0);
    assert_eq!(static_report.summary.total_unknown, 1);
}

// ===========================================================================
// Test 15: Legacy report API through pipeline
// ===========================================================================

#[test]
fn test_pipeline_legacy_report_api() {
    let func = midpoint_function();
    let vcs = trust_vcgen::generate_vcs(&func);
    let router = mock_router();
    let results = router.verify_all(&vcs);

    // Legacy API
    let legacy_report = trust_report::build_report("legacy_test", &results);
    assert_eq!(legacy_report.functions.len(), 1);
    assert_eq!(legacy_report.functions[0].function, "get_midpoint");

    let legacy_summary = trust_report::format_summary(&legacy_report);
    assert!(!legacy_summary.is_empty());

    // JSON API
    let json_report = trust_report::build_json_report("json_test", &results);

    // Both should report the same number of obligations
    let legacy_total =
        legacy_report.total_proved + legacy_report.total_failed + legacy_report.total_unknown;
    assert_eq!(legacy_total, json_report.summary.total_obligations);
}

// ===========================================================================
// Test 16: Large batch - 100 functions through pipeline
// ===========================================================================

#[test]
fn test_pipeline_large_batch_100_functions() {
    let mut all_vcs = Vec::new();
    for i in 0..100 {
        let func = VerifiableFunction {
            name: format!("fn_{i}"),
            def_path: format!("batch::fn_{i}"),
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
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };
        all_vcs.extend(trust_vcgen::generate_vcs(&func));
    }

    assert_eq!(all_vcs.len(), 100, "each function should produce 1 div-by-zero VC");

    let router = mock_router();
    let results = router.verify_all_parallel(&all_vcs, 4);
    assert_eq!(results.len(), 100);

    let report = trust_report::build_json_report("large_batch", &results);
    assert_eq!(report.summary.functions_analyzed, 100);
    assert_eq!(report.summary.total_obligations, 100);

    // All should be the same kind
    for func in &report.functions {
        assert_eq!(func.summary.total_obligations, 1);
    }
}

// ===========================================================================
// Test 17: Terminal report format through full pipeline
// ===========================================================================

#[test]
fn test_pipeline_terminal_report_format() {
    let functions = vec![midpoint_function(), division_function()];
    let mut all_vcs = Vec::new();
    for func in &functions {
        all_vcs.extend(trust_vcgen::generate_vcs(func));
    }

    let router = mock_router();
    let results = router.verify_all(&all_vcs);
    let report = trust_report::build_json_report("terminal_test", &results);

    let terminal_output = trust_report::terminal::format_terminal_report(&report);

    // Terminal output must contain key structural elements
    assert!(
        terminal_output.contains("Trust verification report:"),
        "terminal output must have header"
    );
    assert!(terminal_output.contains("terminal_test"), "terminal output must contain crate name");
    assert!(
        terminal_output.contains("get_midpoint"),
        "terminal output must contain function names"
    );
    assert!(terminal_output.contains("divide"), "terminal output must contain function names");
    assert!(terminal_output.contains("Verdict:"), "terminal output must contain verdict");
    assert!(!terminal_output.is_empty(), "terminal output must not be empty");
}

// ===========================================================================
// Test 18: HTML report format through full pipeline
// ===========================================================================

#[test]
fn test_pipeline_html_report_format() {
    let functions = vec![midpoint_function(), division_function(), guarded_function()];
    let mut all_vcs = Vec::new();
    for func in &functions {
        all_vcs.extend(trust_vcgen::generate_vcs(func));
    }

    let router = mock_router();
    let results = router.verify_all(&all_vcs);
    let report = trust_report::build_json_report("html_test", &results);

    let html = trust_report::html::format_html_report(&report);

    // Valid HTML structure
    assert!(html.starts_with("<!DOCTYPE html>"), "must start with DOCTYPE");
    assert!(html.contains("<html lang=\"en\">"), "must have html tag");
    assert!(html.contains("</html>"), "must close html tag");
    assert!(html.contains("<style>"), "must have inline CSS");
    assert!(html.contains("<script>"), "must have inline JS");

    // Contains crate and function names
    assert!(html.contains("html_test"), "must contain crate name");
    assert!(html.contains("get_midpoint"), "must contain function name");
    assert!(html.contains("divide"), "must contain function name");
    assert!(html.contains("guarded_div"), "must contain function name");

    // Interactive elements
    assert!(html.contains("filterFunctions"), "must have filter JS");
    assert!(html.contains("expandAll"), "must have expand/collapse JS");

    // Self-contained (no external resources)
    assert!(!html.contains("src=\"http"), "must not reference external scripts");
    assert!(!html.contains("href=\"http"), "must not reference external stylesheets");
}

// ===========================================================================
// Test 19: File I/O -- write JSON and NDJSON report files
// ===========================================================================

#[test]
fn test_pipeline_write_report_files() {
    let func = midpoint_function();
    let vcs = trust_vcgen::generate_vcs(&func);
    let router = mock_router();
    let results = router.verify_all(&vcs);
    let report = trust_report::build_json_report("file_io_test", &results);

    // Write JSON report
    let dir = std::env::temp_dir().join("trust_cross_crate_json");
    let _ = std::fs::remove_dir_all(&dir);
    trust_report::write_json_report(&report, &dir).expect("write json report");

    let json_content = std::fs::read_to_string(dir.join("report.json")).expect("read json report");
    let parsed: JsonProofReport = serde_json::from_str(&json_content).expect("parse json report");
    assert_eq!(parsed.crate_name, "file_io_test");
    assert_eq!(parsed.summary.total_obligations, report.summary.total_obligations);

    let _ = std::fs::remove_dir_all(&dir);

    // Write NDJSON report
    let ndjson_dir = std::env::temp_dir().join("trust_cross_crate_ndjson");
    let _ = std::fs::remove_dir_all(&ndjson_dir);
    trust_report::write_ndjson_report(&report, &ndjson_dir).expect("write ndjson report");

    let ndjson_content =
        std::fs::read_to_string(ndjson_dir.join("report.ndjson")).expect("read ndjson report");
    let lines: Vec<&str> = ndjson_content.trim_end().split('\n').collect();
    assert_eq!(lines.len(), report.functions.len() + 2, "NDJSON: header + functions + footer");
    for (i, line) in lines.iter().enumerate() {
        let _: serde_json::Value = serde_json::from_str(line)
            .unwrap_or_else(|e| panic!("NDJSON line {i} invalid JSON: {e}"));
    }

    let _ = std::fs::remove_dir_all(&ndjson_dir);
}

// ===========================================================================
// Test 20: All VC kinds exercised through mock backend
// ===========================================================================

#[test]
fn test_pipeline_all_vc_kinds_through_mock() {
    let vc_kinds = vec![
        VcKind::DivisionByZero,
        VcKind::RemainderByZero,
        VcKind::IndexOutOfBounds,
        VcKind::SliceBoundsCheck,
        VcKind::Postcondition,
        VcKind::Precondition { callee: "callee_fn".to_string() },
        VcKind::Unreachable,
        VcKind::Assertion { message: "user assert".to_string() },
        VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::u32(), Ty::u32()) },
        VcKind::ArithmeticOverflow { op: BinOp::Sub, operand_tys: (Ty::i32(), Ty::i32()) },
        VcKind::ArithmeticOverflow { op: BinOp::Mul, operand_tys: (Ty::u32(), Ty::u32()) },
        VcKind::ShiftOverflow { op: BinOp::Shl, operand_ty: Ty::u32(), shift_ty: Ty::u32() },
        VcKind::CastOverflow { from_ty: Ty::usize(), to_ty: Ty::u32() },
        VcKind::NegationOverflow { ty: Ty::i32() },
        VcKind::Temporal { property: "eventually done".to_string(), machine: None },
        VcKind::Deadlock,
        VcKind::RefinementViolation {
            spec_file: "Spec.tla".to_string(),
            action: "step".to_string(),
        },
    ];

    let router = mock_router();

    let vcs: Vec<VerificationCondition> = vc_kinds
        .into_iter()
        .enumerate()
        .map(|(i, kind)| VerificationCondition {
            kind,
            function: format!("fn_{i}").into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        })
        .collect();

    let results = router.verify_all(&vcs);
    assert_eq!(results.len(), vcs.len(), "one result per VC");

    // All should be proved (trivially false formula)
    for (vc, result) in &results {
        assert!(
            result.is_proved(),
            "VC {:?} for {} should be proved with Bool(false) formula, got {:?}",
            vc.kind,
            vc.function,
            result
        );
    }

    // The router results are diagnostic status objects. Report publication
    // must downgrade them without structured/transport proof authority.
    let report = trust_report::build_json_report("all_kinds", &results);
    assert_eq!(report.summary.total_obligations, results.len());
    assert_eq!(report.summary.total_proved, 0);
    assert_eq!(report.summary.total_unknown, results.len());
    assert_eq!(report.summary.verdict, CrateVerdict::Inconclusive);

    // Verify JSON roundtrip
    let json = serde_json::to_string(&report).unwrap();
    let roundtrip: JsonProofReport = serde_json::from_str(&json).unwrap();
    assert_eq!(roundtrip.summary.total_obligations, report.summary.total_obligations);
}

// ===========================================================================
// Test 21: Counterexample flows through full pipeline to all report formats
// ===========================================================================

#[test]
fn test_pipeline_counterexample_in_all_formats() {
    let results = vec![(
        VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::usize(), Ty::usize()),
            },
            function: "overflow_fn".into(),
            location: SourceSpan {
                file: "src/overflow.rs".to_string(),
                line_start: 10,
                col_start: 5,
                line_end: 10,
                col_end: 20,
            },
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        },
        VerificationResult::Failed {
            solver: "constant-folder".into(),
            time_ms: 2,
            counterexample: Some(Counterexample::new(vec![
                ("x".to_string(), CounterexampleValue::Uint(u64::MAX as u128)),
                ("y".to_string(), CounterexampleValue::Uint(1)),
            ])),
        },
    )];

    let report = trust_report::build_json_report("cex_test", &results);

    // JSON format: counterexample present
    let json = serde_json::to_string_pretty(&report).unwrap();
    assert!(json.contains("counterexample"), "JSON must contain counterexample");
    assert!(json.contains("18446744073709551615"), "JSON must contain max uint value");

    // Text summary: counterexample present
    let text = trust_report::format_json_summary(&report);
    assert!(text.contains("counterexample"), "text summary must contain counterexample");
    assert!(text.contains("x = 18446744073709551615"), "text must show variable values");

    // Terminal: counterexample present
    let terminal = trust_report::terminal::format_terminal_report(&report);
    assert!(terminal.contains("counterexample"), "terminal must contain counterexample");

    // HTML: counterexample present
    let html = trust_report::html::format_html_report(&report);
    assert!(html.contains("Counterexample"), "HTML must contain counterexample");
    assert!(html.contains("18446744073709551615"), "HTML must show value");
}

// ===========================================================================
// Test 22: Timeout flows through full pipeline to all report formats
// ===========================================================================

#[test]
fn test_pipeline_timeout_in_all_formats() {
    let results = vec![(
        VerificationCondition {
            kind: VcKind::Postcondition,
            function: "slow_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        },
        VerificationResult::Timeout { solver: "constant-folder".into(), timeout_ms: 30000 },
    )];

    let report = trust_report::build_json_report("timeout_test", &results);
    assert_eq!(report.summary.verdict, CrateVerdict::Inconclusive);

    // JSON roundtrip preserves timeout
    let json = serde_json::to_string(&report).unwrap();
    let roundtrip: JsonProofReport = serde_json::from_str(&json).unwrap();
    assert!(matches!(
        &roundtrip.functions[0].obligations[0].outcome,
        ObligationOutcome::Timeout { timeout_ms: 30000 }
    ));

    // Text summary
    let text = trust_report::format_json_summary(&report);
    assert!(text.contains("TIMEOUT"), "text must show TIMEOUT");
    assert!(text.contains("30000"), "text must show timeout value");

    // Terminal
    let terminal = trust_report::terminal::format_terminal_report(&report);
    assert!(terminal.contains("30000"), "terminal must show timeout value");

    // HTML
    let html = trust_report::html::format_html_report(&report);
    assert!(html.contains("TIMEOUT"), "HTML must show TIMEOUT");
    assert!(html.contains("30000"), "HTML must show timeout value");
}

// ===========================================================================
// Test 23: Multiple proof strengths through pipeline
// ===========================================================================

#[test]
fn test_pipeline_proof_strengths_fail_closed_without_publication_evidence() {
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
        (
            VerificationCondition {
                kind: VcKind::IndexOutOfBounds,
                function: "f".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
                obligation: None,
            },
            VerificationResult::Proved {
                solver: "trust-mc".into(),
                time_ms: 5,
                strength: ProofStrength::bounded(100),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        ),
    ];

    let report = trust_report::build_json_report("strengths", &results);
    // The three freely constructible unbounded Proved statuses carry no
    // publication-grade structured/transport evidence. The bounded result
    // also lacks a private certified-monitor receipt. All four fail closed to
    // Unknown at the public report boundary.
    assert_eq!(report.summary.verdict, CrateVerdict::Inconclusive);
    assert_eq!(report.summary.total_proved, 0);
    assert_eq!(report.summary.total_unknown, 4);
    assert_eq!(report.summary.total_runtime_checked, 0);

    // Unpublished static strength labels must not survive as proof claims.
    // The bounded result must not retain runtime authority either.
    let text = trust_report::format_json_summary(&report);
    assert!(!text.contains("SMT UNSAT"), "must not publish raw SMT UNSAT status as proof");
    assert!(!text.contains("DEDUCTIVE"), "must not publish raw deductive status as proof");
    assert!(!text.contains("INDUCTIVE"), "must not publish raw inductive status as proof");
    assert!(text.contains("UNKNOWN"), "unpublished proof statuses must surface as unknown");
    assert!(
        !text.contains("RUNTIME CHECKED"),
        "bounded proof without a certified monitor must surface as unknown"
    );

    // HTML applies the same publication gate.
    let html = trust_report::html::format_html_report(&report);
    assert!(!html.contains("SMT UNSAT"), "HTML must not publish raw SMT UNSAT status");
    assert!(!html.contains("DEDUCTIVE"), "HTML must not publish raw deductive status");
    assert!(!html.contains("INDUCTIVE"), "HTML must not publish raw inductive status");
    assert!(html.contains("UNKNOWN"), "HTML must show fail-closed unknown statuses");
    assert!(
        !html.contains("RUNTIME-CHECKED"),
        "HTML must not publish an uncertified bounded runtime check"
    );

    // JSON roundtrip cannot resurrect the three rejected static proof labels
    // or the bounded obligation's unauthenticated runtime classification.
    let json = serde_json::to_string(&report).unwrap();
    let roundtrip: JsonProofReport = serde_json::from_str(&json).unwrap();
    let strengths: Vec<_> = roundtrip.functions[0]
        .obligations
        .iter()
        .filter_map(|o| match &o.outcome {
            ObligationOutcome::Proved { strength } => Some(strength.clone()),
            _ => None,
        })
        .collect();
    assert!(strengths.is_empty());
    assert_eq!(
        roundtrip.functions[0]
            .obligations
            .iter()
            .filter(|o| matches!(&o.outcome, ObligationOutcome::Unknown { .. }))
            .count(),
        4
    );
    assert!(
        roundtrip.functions[0]
            .obligations
            .iter()
            .all(|o| !matches!(&o.outcome, ObligationOutcome::RuntimeChecked { .. })),
        "the bounded proof must round-trip without runtime authority"
    );
}

// ===========================================================================
// Test 24: Proof levels flow correctly through report
// ===========================================================================

#[test]
fn test_pipeline_proof_levels_in_report() {
    let results = vec![
        (
            VerificationCondition {
                kind: VcKind::DivisionByZero, // L0
                function: "mixed_levels".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
                obligation: None,
            },
            VerificationResult::Proved {
                solver: "constant-folder".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        ),
        (
            VerificationCondition {
                kind: VcKind::Postcondition, // L1
                function: "mixed_levels".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
                obligation: None,
            },
            VerificationResult::Proved {
                solver: "constant-folder".into(),
                time_ms: 1,
                strength: ProofStrength::deductive(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        ),
        (
            VerificationCondition {
                kind: VcKind::Temporal { property: "liveness".to_string(), machine: None }, // L2
                function: "mixed_levels".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
                obligation: None,
            },
            VerificationResult::Proved {
                solver: "constant-folder".into(),
                time_ms: 1,
                strength: ProofStrength::inductive(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        ),
    ];

    let report = trust_report::build_json_report("levels", &results);
    let func = &report.functions[0];

    // Max proof level should be L2
    assert_eq!(func.summary.max_proof_level, Some(ProofLevel::L2Domain));

    // Individual obligations have correct levels
    let levels: Vec<ProofLevel> = func.obligations.iter().map(|o| o.proof_level).collect();
    assert!(levels.contains(&ProofLevel::L0Safety));
    assert!(levels.contains(&ProofLevel::L1Functional));
    assert!(levels.contains(&ProofLevel::L2Domain));

    // Text summary shows max level
    let text = trust_report::format_json_summary(&report);
    assert!(text.contains("L2 domain"), "text must show max proof level");
}

// ===========================================================================
// Test 25: vcgen + router + report for shift overflow function
// ===========================================================================

#[test]
fn test_pipeline_shift_overflow_function() {
    // fn shl_fn(x: u32, shift: u32) -> u32 { x << shift }
    let func = VerifiableFunction {
        name: "shl_fn".to_string(),
        def_path: "pipeline::shl_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("shift".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Shl,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = trust_vcgen::generate_vcs(&func);
    // Should produce a shift overflow VC
    let shift_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::ShiftOverflow { .. })).collect();
    assert!(!shift_vcs.is_empty(), "shift left should produce a ShiftOverflow VC");

    let router = mock_router();
    let results = router.verify_all(&vcs);
    let report = trust_report::build_json_report("shift_test", &results);

    assert_eq!(report.summary.functions_analyzed, 1);
    assert!(report.summary.total_obligations >= 1);

    // Check the VC kind tag in the report
    let shift_obs: Vec<_> = report.functions[0]
        .obligations
        .iter()
        .filter(|o| o.kind.starts_with("shift_overflow"))
        .collect();
    assert!(!shift_obs.is_empty(), "report must contain shift_overflow obligation");
}

// ===========================================================================
// Test 26: vcgen + router + report for negation overflow function
// ===========================================================================

#[test]
fn test_pipeline_negation_overflow_function() {
    // fn negate(x: i32) -> i32 { -x }
    let func = VerifiableFunction {
        name: "negate".to_string(),
        def_path: "pipeline::negate".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = trust_vcgen::generate_vcs(&func);
    let neg_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::NegationOverflow { .. })).collect();
    assert!(!neg_vcs.is_empty(), "negation of i32 should produce a NegationOverflow VC");

    let router = mock_router();
    let results = router.verify_all(&vcs);
    let report = trust_report::build_json_report("negation_test", &results);

    let neg_obs: Vec<_> =
        report.functions[0].obligations.iter().filter(|o| o.kind == "negation_overflow").collect();
    assert!(!neg_obs.is_empty(), "report must contain negation_overflow obligation");
}
