// trust-integration-tests/tests/complex_roundtrip.rs: E2E round-trip tests for
// complex functions (branches, loops, nested control flow, batch verification).
//
// Exercises the full MirRouter pipeline with synthetic MIR bodies that go beyond
// trivial single-block functions: SwitchInt branches, Goto back-edges (loops),
// Call terminators, and multi-function batch dispatch.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use trust_router::{MirRouter, MirStrategy};
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, Contract, ContractKind, Formula, LocalDecl, Operand,
    Place, Rvalue, SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
    VerificationResult,
};

// ---------------------------------------------------------------------------
// Fixture builders
// ---------------------------------------------------------------------------

/// Build `max(a: i32, b: i32) -> i32` with an if/else branch.
///
/// MIR equivalent:
/// ```text
/// bb0: _3 = Gt(_1, _2);  SwitchInt(_3) { 0 => bb2, otherwise => bb1 }
/// bb1: _0 = _1; goto bb3
/// bb2: _0 = _2; goto bb3
/// bb3: return
/// ```
fn max_function() -> VerifiableFunction {
    let i32_ty = Ty::Int { width: 32, signed: true };
    VerifiableFunction {
        name: "max".to_string(),
        def_path: "complex::max".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: i32_ty.clone(), name: None }, // _0: return
                LocalDecl { index: 1, ty: i32_ty.clone(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: i32_ty.clone(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: None }, // _3: cmp result
            ],
            blocks: vec![
                // bb0: compare and branch
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Gt,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(3)),
                        targets: vec![(0, BlockId(2))], // false => bb2 (else)
                        otherwise: BlockId(1),          // true  => bb1 (then)
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                // bb1: then branch (a > b, return a)
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                // bb2: else branch (return b)
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                // bb3: return
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: i32_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Build `sum_1_to_n(n: u32) -> u32` with a loop (Goto back-edge).
///
/// MIR equivalent:
/// ```text
/// bb0: _2 = const 0u32;  _3 = const 1u32;  goto bb1     // init: sum=0, i=1
/// bb1: _4 = Le(_3, _1);  SwitchInt(_4) { 0 => bb3, otherwise => bb2 }  // while i <= n
/// bb2: _5 = CheckedAdd(_2, _3); assert(!_5.1, overflow, bb2cont)
/// bb2cont: _2 = _5.0; _6 = CheckedAdd(_3, const 1); assert(!_6.1, overflow, bb2done)
/// bb2done: _3 = _6.0; goto bb1   // sum += i; i += 1; loop back
/// bb3: _0 = _2; return            // return sum
/// ```
///
/// Simplified to avoid Assert complexity — uses unchecked ops for readability:
/// ```text
/// bb0: _2 = 0; _3 = 1; goto bb1
/// bb1: _4 = Le(_3, _1); SwitchInt(_4) { 0 => bb3, _ => bb2 }
/// bb2: _2 = Add(_2, _3); _3 = Add(_3, 1); goto bb1
/// bb3: _0 = _2; return
/// ```
fn sum_1_to_n_function() -> VerifiableFunction {
    let u32_ty = Ty::u32();
    VerifiableFunction {
        name: "sum_1_to_n".to_string(),
        def_path: "complex::sum_1_to_n".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: u32_ty.clone(), name: None }, // _0: return
                LocalDecl { index: 1, ty: u32_ty.clone(), name: Some("n".into()) }, // _1: param
                LocalDecl { index: 2, ty: u32_ty.clone(), name: Some("sum".into()) },
                LocalDecl { index: 3, ty: u32_ty.clone(), name: Some("i".into()) },
                LocalDecl { index: 4, ty: Ty::Bool, name: None }, // _4: cmp
            ],
            blocks: vec![
                // bb0: init sum=0, i=1
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(1, 32))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                // bb1: loop condition (i <= n)
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Le,
                            Operand::Copy(Place::local(3)),
                            Operand::Copy(Place::local(1)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(4)),
                        targets: vec![(0, BlockId(3))], // false => exit
                        otherwise: BlockId(2),          // true  => loop body
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                // bb2: loop body (sum += i; i += 1; goto bb1)
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(2)),
                                Operand::Copy(Place::local(3)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(3)),
                                Operand::Constant(ConstValue::Uint(1, 32)),
                            ),
                            span: SourceSpan::default(),
                        },
                    ],
                    // Goto back to bb1 — this is the back-edge that makes it a loop
                    terminator: Terminator::Goto(BlockId(1)),
                },
                // bb3: return sum
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: u32_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Build `clamp(x: i32, lo: i32, hi: i32) -> i32` with nested branches.
///
/// MIR equivalent:
/// ```text
/// bb0: _4 = Lt(_1, _2); SwitchInt(_4) { 0 => bb2, _ => bb1 }
/// bb1: _0 = _2; goto bb5          // x < lo => return lo
/// bb2: _5 = Gt(_1, _3); SwitchInt(_5) { 0 => bb4, _ => bb3 }
/// bb3: _0 = _3; goto bb5          // x > hi => return hi
/// bb4: _0 = _1; goto bb5          // lo <= x <= hi => return x
/// bb5: return
/// ```
fn clamp_function() -> VerifiableFunction {
    let i32_ty = Ty::Int { width: 32, signed: true };
    VerifiableFunction {
        name: "clamp".to_string(),
        def_path: "complex::clamp".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: i32_ty.clone(), name: None },
                LocalDecl { index: 1, ty: i32_ty.clone(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: i32_ty.clone(), name: Some("lo".into()) },
                LocalDecl { index: 3, ty: i32_ty.clone(), name: Some("hi".into()) },
                LocalDecl { index: 4, ty: Ty::Bool, name: None }, // x < lo
                LocalDecl { index: 5, ty: Ty::Bool, name: None }, // x > hi
            ],
            blocks: vec![
                // bb0: if x < lo
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(4)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                // bb1: return lo
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(5)),
                },
                // bb2: if x > hi
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Gt,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(3)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(5)),
                        targets: vec![(0, BlockId(4))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                // bb3: return hi
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(5)),
                },
                // bb4: return x
                BasicBlock {
                    id: BlockId(4),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(5)),
                },
                // bb5: return
                BasicBlock { id: BlockId(5), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 3,
            return_ty: i32_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Build `call_max_then_clamp(a: i32, b: i32, lo: i32, hi: i32) -> i32`
/// that calls `max` then `clamp`.
///
/// MIR:
/// ```text
/// bb0: _5 = Call(max, [_1, _2]) -> bb1
/// bb1: _0 = Call(clamp, [_5, _3, _4]) -> bb2
/// bb2: return
/// ```
fn call_chain_function() -> VerifiableFunction {
    let i32_ty = Ty::Int { width: 32, signed: true };
    VerifiableFunction {
        name: "call_max_then_clamp".to_string(),
        def_path: "complex::call_max_then_clamp".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: i32_ty.clone(), name: None },
                LocalDecl { index: 1, ty: i32_ty.clone(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: i32_ty.clone(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: i32_ty.clone(), name: Some("lo".into()) },
                LocalDecl { index: 4, ty: i32_ty.clone(), name: Some("hi".into()) },
                LocalDecl { index: 5, ty: i32_ty.clone(), name: None }, // max result
            ],
            blocks: vec![
                // bb0: call max(a, b)
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { is_unsafe_sig: false, is_foreign: false,
                        func: "complex::max".to_string(),
                        args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                        dest: Place::local(5),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        unwind: trust_types::UnwindEdge::Unreachable,
                    },
                },
                // bb1: call clamp(max_result, lo, hi)
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call { is_unsafe_sig: false, is_foreign: false,
                        func: "complex::clamp".to_string(),
                        args: vec![
                            Operand::Copy(Place::local(5)),
                            Operand::Copy(Place::local(3)),
                            Operand::Copy(Place::local(4)),
                        ],
                        dest: Place::local(0),
                        target: Some(BlockId(2)),
                        span: SourceSpan::default(),
                        atomic: None,
                        unwind: trust_types::UnwindEdge::Unreachable,
                    },
                },
                // bb2: return
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 4,
            return_ty: i32_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Build `sum_with_contract(n: u32) -> u32` — same loop as sum_1_to_n but with
/// an ensures contract (result == n * (n + 1) / 2).
fn sum_with_contract_function() -> VerifiableFunction {
    let mut func = sum_1_to_n_function();
    func.name = "sum_with_contract".to_string();
    func.def_path = "complex::sum_with_contract".to_string();
    func.contracts = vec![Contract {
        kind: ContractKind::Ensures,
        span: SourceSpan::default(),
        body: "result == n * (n + 1) / 2".to_string(),
    }];
    func.postconditions = vec![Formula::Eq(
        Box::new(Formula::Var("result".into(), trust_types::Sort::Int)),
        Box::new(Formula::Div(
            Box::new(Formula::Mul(
                Box::new(Formula::Var("n".into(), trust_types::Sort::Int)),
                Box::new(Formula::Add(
                    Box::new(Formula::Var("n".into(), trust_types::Sort::Int)),
                    Box::new(Formula::Int(1)),
                )),
            )),
            Box::new(Formula::Int(2)),
        )),
    )];
    func
}

// ---------------------------------------------------------------------------
// 1. Branch test: max(a, b) via SwitchInt
// ---------------------------------------------------------------------------

#[test]
fn test_roundtrip_branch_max_function() {
    let func = max_function();
    let router = MirRouter::with_defaults();

    // Classification: no loops, no contracts, no unsafe => V1Fallback
    let strategy = router.classify(&func);
    assert!(
        matches!(strategy, MirStrategy::V1Fallback),
        "max() with branches but no loops should be V1Fallback, got: {strategy}"
    );

    // Verify: should produce a result (not panic, not crash)
    let result = router.verify_function(&func);
    assert_result_is_terminal(&result, "max");

    // Structural: 4 basic blocks, 2 branches from SwitchInt
    assert_eq!(func.body.blocks.len(), 4, "max should have 4 basic blocks");
    assert!(
        matches!(func.body.blocks[0].terminator, Terminator::SwitchInt { .. }),
        "bb0 should have SwitchInt terminator"
    );
}

// ---------------------------------------------------------------------------
// 2. Loop test: sum_1_to_n with Goto back-edge
// ---------------------------------------------------------------------------

#[test]
fn test_roundtrip_loop_sum_function() {
    let func = sum_1_to_n_function();
    let router = MirRouter::with_defaults();

    // Classification: has Goto back-edge (bb2 -> bb1) => BoundedModelCheck
    let strategy = router.classify(&func);
    assert!(
        matches!(strategy, MirStrategy::BoundedModelCheck),
        "sum_1_to_n with loop back-edge should be BoundedModelCheck, got: {strategy}"
    );

    // Verify: should produce a result
    let result = router.verify_function(&func);
    assert_result_is_terminal(&result, "sum_1_to_n");

    // Structural: 4 blocks, bb2 has back-edge to bb1
    assert_eq!(func.body.blocks.len(), 4, "sum_1_to_n should have 4 basic blocks");
    assert!(
        matches!(func.body.blocks[2].terminator, Terminator::Goto(BlockId(1))),
        "bb2 should goto bb1 (back-edge)"
    );
}

// ---------------------------------------------------------------------------
// 3. Nested branch test: clamp(x, lo, hi)
// ---------------------------------------------------------------------------

#[test]
fn test_roundtrip_nested_branch_clamp_function() {
    let func = clamp_function();
    let router = MirRouter::with_defaults();

    // Classification: multiple branches but no loops => V1Fallback
    let strategy = router.classify(&func);
    assert!(
        matches!(strategy, MirStrategy::V1Fallback),
        "clamp() with nested branches should be V1Fallback, got: {strategy}"
    );

    let result = router.verify_function(&func);
    assert_result_is_terminal(&result, "clamp");

    // Structural: 6 basic blocks, 2 SwitchInt terminators
    assert_eq!(func.body.blocks.len(), 6, "clamp should have 6 basic blocks");
    let switch_count = func
        .body
        .blocks
        .iter()
        .filter(|bb| matches!(bb.terminator, Terminator::SwitchInt { .. }))
        .count();
    assert_eq!(switch_count, 2, "clamp should have 2 SwitchInt terminators");
}

// ---------------------------------------------------------------------------
// 4. Call chain test: call_max_then_clamp
// ---------------------------------------------------------------------------

#[test]
fn test_roundtrip_call_chain_function() {
    let func = call_chain_function();
    let router = MirRouter::with_defaults();

    // Classification: has Call terminators but no loops/contracts/unsafe => V1Fallback
    let strategy = router.classify(&func);
    assert!(
        matches!(strategy, MirStrategy::V1Fallback),
        "call chain should be V1Fallback, got: {strategy}"
    );

    let result = router.verify_function(&func);
    assert_result_is_terminal(&result, "call_max_then_clamp");

    // Structural: 3 blocks, 2 Call terminators
    let call_count = func
        .body
        .blocks
        .iter()
        .filter(|bb| matches!(bb.terminator, Terminator::Call { .. }))
        .count();
    assert_eq!(call_count, 2, "call chain should have 2 Call terminators");
}

// ---------------------------------------------------------------------------
// 5. Loop with contract: sum_with_contract (triggers ContractVerification)
// ---------------------------------------------------------------------------

#[test]
fn test_roundtrip_loop_with_contract() {
    let func = sum_with_contract_function();
    let router = MirRouter::with_defaults();

    // Classification: has contracts => ContractVerification (overrides loop)
    let strategy = router.classify(&func);
    assert!(
        matches!(strategy, MirStrategy::ContractVerification),
        "sum_with_contract should be ContractVerification, got: {strategy}"
    );

    let result = router.verify_function(&func);
    assert_result_is_terminal(&result, "sum_with_contract");

    // The function has both a loop AND a contract
    assert!(!func.contracts.is_empty(), "should have ensures contract");
    assert!(
        matches!(func.body.blocks[2].terminator, Terminator::Goto(BlockId(1))),
        "should still have loop back-edge"
    );
}

// ---------------------------------------------------------------------------
// 6. Batch verification: all complex functions together
// ---------------------------------------------------------------------------

#[test]
fn test_roundtrip_batch_all_complex_functions() {
    let funcs = vec![
        max_function(),
        sum_1_to_n_function(),
        clamp_function(),
        call_chain_function(),
        sum_with_contract_function(),
    ];
    let router = MirRouter::with_defaults();

    let results = router.verify_all(&funcs);

    // All 5 functions should produce results
    assert_eq!(results.len(), 5, "batch should produce 5 results");

    // Verify function names in results
    let names: Vec<&str> = results.iter().map(|(name, _, _)| name.as_str()).collect();
    assert!(names.contains(&"max"));
    assert!(names.contains(&"sum_1_to_n"));
    assert!(names.contains(&"clamp"));
    assert!(names.contains(&"call_max_then_clamp"));
    assert!(names.contains(&"sum_with_contract"));

    // Verify strategy diversity (not all the same strategy)
    let strategies: Vec<&MirStrategy> = results.iter().map(|(_, s, _)| s).collect();
    let has_v1 = strategies.iter().any(|s| matches!(s, MirStrategy::V1Fallback));
    let has_bmc = strategies.iter().any(|s| matches!(s, MirStrategy::BoundedModelCheck));
    let has_contract = strategies.iter().any(|s| matches!(s, MirStrategy::ContractVerification));
    assert!(has_v1, "batch should include V1Fallback strategies");
    assert!(has_bmc, "batch should include BoundedModelCheck strategies");
    assert!(has_contract, "batch should include ContractVerification strategies");

    // All results should be terminal (not None/empty)
    for (name, _strategy, result) in &results {
        assert_result_is_terminal(result, name);
    }
}

// ---------------------------------------------------------------------------
// 7. Report integration: batch results produce valid report
// ---------------------------------------------------------------------------

#[test]
fn test_roundtrip_batch_report_generation() {
    let funcs = vec![max_function(), sum_1_to_n_function(), clamp_function()];
    let router = MirRouter::with_defaults();

    // Convert MirRouter results to the (VC, VerificationResult) pairs that
    // trust-report expects. Each function becomes one synthetic VC.
    let mir_results = router.verify_all(&funcs);
    let vc_results: Vec<(trust_types::VerificationCondition, VerificationResult)> = mir_results
        .iter()
        .map(|(name, _strategy, result)| {
            let vc = trust_types::VerificationCondition {
                kind: trust_types::VcKind::Assertion { message: format!("verification of {name}") },
                function: name.clone().into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(true),
                contract_metadata: None,
                obligation: None,
            };
            (vc, result.clone())
        })
        .collect();

    let report = trust_report::build_json_report("complex_roundtrip", &vc_results);

    assert_eq!(report.crate_name, "complex_roundtrip");
    assert_eq!(report.summary.functions_analyzed, 3, "report should analyze 3 functions");
    assert_eq!(report.summary.total_obligations, 3, "report should have 3 obligations");

    // JSON roundtrip
    let json = serde_json::to_string_pretty(&report).expect("serialize report");
    let roundtrip: trust_types::JsonProofReport =
        serde_json::from_str(&json).expect("deserialize report");
    assert_eq!(roundtrip.crate_name, "complex_roundtrip");
    assert_eq!(roundtrip.summary.total_obligations, 3);

    // Text summary contains all function names
    let text = trust_report::format_json_summary(&report);
    assert!(text.contains("max"), "report text should mention max");
    assert!(text.contains("sum_1_to_n"), "report text should mention sum_1_to_n");
    assert!(text.contains("clamp"), "report text should mention clamp");
}

// ---------------------------------------------------------------------------
// 8. Structural validation: complex MIR properties
// ---------------------------------------------------------------------------

#[test]
fn test_complex_mir_structural_properties() {
    // Verify that our synthetic MIR bodies have the structural complexity
    // claimed by the issue (multiple BBs, back-edges, branches, calls).

    let max_fn = max_function();
    let sum_fn = sum_1_to_n_function();
    let clamp_fn = clamp_function();
    let call_fn = call_chain_function();

    // Block counts
    assert!(max_fn.body.blocks.len() >= 3, "branch function needs >= 3 blocks");
    assert!(sum_fn.body.blocks.len() >= 3, "loop function needs >= 3 blocks");
    assert!(clamp_fn.body.blocks.len() >= 5, "nested branch needs >= 5 blocks");
    assert!(call_fn.body.blocks.len() >= 2, "call chain needs >= 2 blocks");

    // Back-edge detection (same logic as MirRouter::has_loops)
    let has_back_edge = |func: &VerifiableFunction| -> bool {
        func.body.blocks.iter().any(|bb| {
            let current = bb.id.0;
            successor_ids(&bb.terminator).iter().any(|&target| target <= current)
        })
    };

    assert!(!has_back_edge(&max_fn), "max() should NOT have a back-edge");
    assert!(has_back_edge(&sum_fn), "sum_1_to_n() MUST have a back-edge (loop)");
    assert!(!has_back_edge(&clamp_fn), "clamp() should NOT have a back-edge");
    assert!(!has_back_edge(&call_fn), "call_max_then_clamp() should NOT have a back-edge");

    // Terminator diversity
    let terminator_kinds = |func: &VerifiableFunction| -> Vec<&'static str> {
        func.body
            .blocks
            .iter()
            .map(|bb| match &bb.terminator {
                Terminator::Goto(_) => "Goto",
                Terminator::SwitchInt { .. } => "SwitchInt",
                Terminator::Return => "Return",
                Terminator::Call { .. } => "Call",
                Terminator::Assert { .. } => "Assert",
                Terminator::Drop { .. } => "Drop",
                Terminator::Unreachable => "Unreachable",
                _ => "Other",
            })
            .collect()
    };

    let max_terms = terminator_kinds(&max_fn);
    assert!(max_terms.contains(&"SwitchInt"), "max needs SwitchInt");
    assert!(max_terms.contains(&"Goto"), "max needs Goto");
    assert!(max_terms.contains(&"Return"), "max needs Return");

    let sum_terms = terminator_kinds(&sum_fn);
    assert!(sum_terms.contains(&"SwitchInt"), "sum needs SwitchInt");
    assert!(sum_terms.contains(&"Goto"), "sum needs Goto (loop)");

    let call_terms = terminator_kinds(&call_fn);
    assert!(call_terms.contains(&"Call"), "call chain needs Call");
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Assert that a verification result is a terminal state (Proved, Failed, or
/// Unknown with a reason), not a default/empty value.
fn assert_result_is_terminal(result: &VerificationResult, func_name: &str) {
    match result {
        VerificationResult::Proved { solver, .. } => {
            assert!(!solver.is_empty(), "{func_name}: proved result should name a solver");
        }
        VerificationResult::Failed { solver, .. } => {
            assert!(!solver.is_empty(), "{func_name}: failed result should name a solver");
        }
        VerificationResult::Unknown { solver, reason, .. } => {
            assert!(!solver.is_empty(), "{func_name}: unknown result should name a solver");
            assert!(!reason.is_empty(), "{func_name}: unknown result should have a reason");
        }
        _ => panic!("{func_name}: expected a terminal verification result"),
    }
}

/// Extract successor block IDs from a terminator (mirrors mir_router logic).
fn successor_ids(terminator: &Terminator) -> Vec<usize> {
    match terminator {
        Terminator::Goto(bid) => vec![bid.0],
        Terminator::SwitchInt { targets, otherwise, .. } => {
            let mut ids: Vec<usize> = targets.iter().map(|(_, bid)| bid.0).collect();
            ids.push(otherwise.0);
            ids
        }
        Terminator::Return | Terminator::Unreachable => vec![],
        Terminator::Call { target, .. } => target.iter().map(|bid| bid.0).collect(),
        Terminator::Assert { target, .. } => vec![target.0],
        Terminator::Drop { target, .. } => vec![target.0],
        _ => vec![],
    }
}
