// trust-integration-tests/tests/real_ay_verification.rs: Real ay solver verification
//
// These tests call REAL ay via the IncrementalAYSession subprocess. They are the ground
// truth for "does Trust actually prove things?" — no mocks, no simulations.
//
// Requirements: ay binary discoverable by the integration-test ay helper.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use trust_integration_tests::ay_test_support::{require_ay, ay_available};
use trust_router::VerificationBackend;
use trust_types::*;

// ---------------------------------------------------------------------------
// Synthetic MIR builders
// ---------------------------------------------------------------------------

/// Buggy midpoint: `mid = (lo + hi) / 2` — has CheckedAdd overflow
fn buggy_midpoint_mir() -> VerifiableFunction {
    VerifiableFunction {
        name: "buggy_midpoint".to_string(),
        def_path: "test::buggy_midpoint".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("lo".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("hi".into()) },
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
                        unwind: trust_types::UnwindEdge::Unreachable,
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
        spec: FunctionSpec::default(),
    }
}

/// Safe midpoint: `mid = lo + (hi - lo) / 2` — no overflow possible
fn safe_midpoint_mir() -> VerifiableFunction {
    VerifiableFunction {
        name: "safe_midpoint".to_string(),
        def_path: "test::safe_midpoint".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("lo".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("hi".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
                LocalDecl { index: 4, ty: Ty::usize(), name: None },
                LocalDecl { index: 5, ty: Ty::usize(), name: None },
                LocalDecl { index: 6, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
                LocalDecl { index: 7, ty: Ty::usize(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Sub,
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(1)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Sub),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                        unwind: trust_types::UnwindEdge::Unreachable,
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
                    ],
                    terminator: Terminator::Goto(BlockId(2)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(6),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(5)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(6, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(3),
                        span: SourceSpan::default(),
                        unwind: trust_types::UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::field(6, 0))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::usize(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    }
}

/// Division by variable — should detect possible division by zero
fn div_by_variable_mir() -> VerifiableFunction {
    VerifiableFunction {
        name: "div_by_var".to_string(),
        def_path: "test::div_by_var".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
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
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    }
}

/// Division by constant 2 — should prove safe (no division by zero possible)
fn div_by_constant_mir() -> VerifiableFunction {
    VerifiableFunction {
        name: "div_by_two".to_string(),
        def_path: "test::div_by_two".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("n".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Div,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Int(2)),
                    ),
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
        spec: FunctionSpec::default(),
    }
}

// ===========================================================================
// Tests: Real ay calls
// ===========================================================================

#[test]
fn test_real_ay_detects_midpoint_overflow() {
    if !ay_available() {
        eprintln!("SKIP: ay not found by integration-test helper");
        return;
    }
    let ay = require_ay();
    let func = buggy_midpoint_mir();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("Generated {} VCs for buggy_midpoint", vcs.len());
    for vc in &vcs {
        eprintln!("  VC: {:?} — {}", vc.kind, vc.function);
    }

    let overflow_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .collect();

    assert!(
        !overflow_vcs.is_empty(),
        "vcgen must produce at least one ArithmeticOverflow(Add) VC for buggy midpoint"
    );

    for vc in &overflow_vcs {
        let result = ay.verify(vc);
        eprintln!("ay result for {:?}: {:?}", vc.kind, result);

        assert!(
            result.is_failed(),
            "ay must find the midpoint overflow (SAT = violation exists). Got: {result:?}"
        );

        if let VerificationResult::Failed { counterexample: Some(cex), solver, time_ms } = &result {
            assert_eq!(solver, "ay-smtlib");
            assert!(*time_ms < 30_000, "should complete in under 30s");
            assert!(!cex.assignments.is_empty(), "counterexample must have assignments");
            eprintln!("  Counterexample: {cex}");
        }
    }
}

#[test]
fn test_real_ay_proves_constant_division_safe() {
    if !ay_available() {
        eprintln!("SKIP: ay not found by integration-test helper");
        return;
    }
    let ay = require_ay();
    let func = div_by_constant_mir();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("Generated {} VCs for div_by_two", vcs.len());

    let divzero_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::DivisionByZero)).collect();

    for vc in &divzero_vcs {
        let result = ay.verify(vc);
        eprintln!("ay result for div_by_two {:?}: {:?}", vc.kind, result);

        assert!(
            result.is_proved(),
            "ay must prove division by constant 2 is safe (UNSAT). Got: {result:?}"
        );
    }
}

#[test]
fn test_real_ay_detects_division_by_variable() {
    if !ay_available() {
        eprintln!("SKIP: ay not found by integration-test helper");
        return;
    }
    let ay = require_ay();
    let func = div_by_variable_mir();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("Generated {} VCs for div_by_var", vcs.len());

    let divzero_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::DivisionByZero)).collect();

    assert!(
        !divzero_vcs.is_empty(),
        "vcgen must produce a DivisionByZero VC for division by variable"
    );

    for vc in &divzero_vcs {
        let result = ay.verify(vc);
        eprintln!("ay result for div_by_var {:?}: {:?}", vc.kind, result);

        assert!(
            result.is_failed(),
            "ay must find that variable divisor CAN be zero. Got: {result:?}"
        );

        if let VerificationResult::Failed { counterexample: Some(cex), .. } = &result {
            eprintln!("  Counterexample: {cex}");
        }
    }
}

#[test]
fn test_real_ay_full_pipeline_buggy_vs_safe() {
    if !ay_available() {
        eprintln!("SKIP: ay not found by integration-test helper");
        return;
    }
    let ay = require_ay();

    let buggy = buggy_midpoint_mir();
    let buggy_vcs = trust_vcgen::generate_vcs(&buggy);
    eprintln!("\n=== BUGGY MIDPOINT: {} VCs ===", buggy_vcs.len());

    let (mut bp, mut bf, mut bu) = (0u32, 0u32, 0u32);
    for vc in &buggy_vcs {
        if !ay.can_handle(vc) {
            bu += 1;
            continue;
        }
        match ay.verify(vc) {
            VerificationResult::Proved { .. } => {
                bp += 1;
                eprintln!("  PROVED: {:?}", vc.kind);
            }
            VerificationResult::Failed { ref counterexample, .. } => {
                bf += 1;
                eprintln!("  FAILED: {:?}", vc.kind);
                if let Some(cex) = counterexample {
                    eprintln!("    Counterexample: {cex}");
                }
            }
            ref other => {
                bu += 1;
                eprintln!("  UNKNOWN: {:?} — {other:?}", vc.kind);
            }
        }
    }
    eprintln!("Buggy: {bp} proved, {bf} failed, {bu} unknown");
    assert!(bf > 0, "buggy midpoint must have at least one failure");

    let safe = safe_midpoint_mir();
    let safe_vcs = trust_vcgen::generate_vcs(&safe);
    eprintln!("\n=== SAFE MIDPOINT: {} VCs ===", safe_vcs.len());

    let (mut sp, mut sf, mut su) = (0u32, 0u32, 0u32);
    for vc in &safe_vcs {
        if !ay.can_handle(vc) {
            su += 1;
            continue;
        }
        match ay.verify(vc) {
            VerificationResult::Proved { .. } => {
                sp += 1;
                eprintln!("  PROVED: {:?}", vc.kind);
            }
            VerificationResult::Failed { ref counterexample, .. } => {
                sf += 1;
                eprintln!("  FAILED: {:?}", vc.kind);
                if let Some(cex) = counterexample {
                    eprintln!("    Counterexample: {cex}");
                }
            }
            ref other => {
                su += 1;
                eprintln!("  UNKNOWN: {:?} — {other:?}", vc.kind);
            }
        }
    }
    eprintln!("Safe: {sp} proved, {sf} failed, {su} unknown");

    // With guard propagation + dataflow tracking, the safe midpoint
    // results are now precise:
    // - Sub overflow FAILED: hi < lo is a real finding (needs #[requires(hi >= lo)])
    // - Add overflow PROVED: ay knows _5 = (hi-lo)/2 with hi >= lo, so lo + _5 <= max
    // The buggy midpoint Add overflow is always FAILED (no guards help).
    assert_eq!(bf, 1, "buggy midpoint must have exactly 1 failure (Add overflow)");
    assert_eq!(sf, 1, "safe midpoint must have exactly 1 failure (Sub overflow when hi < lo)");
    assert_eq!(sp, 1, "safe midpoint must have exactly 1 proof (Add overflow proved safe)");

    eprintln!("\n=== SUMMARY ===");
    eprintln!("Buggy: {bp}P / {bf}F / {bu}U");
    eprintln!("Safe:  {sp}P / {sf}F / {su}U");
}

#[test]
fn test_real_ay_direct_overflow_formula() {
    if !ay_available() {
        eprintln!("SKIP: ay not found by integration-test helper");
        return;
    }
    let ay = require_ay();

    let max_val = (1i128 << 64) - 1;
    let a = Formula::Var("a".into(), Sort::Int);
    let b = Formula::Var("b".into(), Sort::Int);
    let sum = Formula::Add(Box::new(a.clone()), Box::new(b.clone()));

    let formula = Formula::And(vec![
        Formula::Ge(Box::new(a.clone()), Box::new(Formula::Int(0))),
        Formula::Le(Box::new(a), Box::new(Formula::Int(max_val))),
        Formula::Ge(Box::new(b.clone()), Box::new(Formula::Int(0))),
        Formula::Le(Box::new(b), Box::new(Formula::Int(max_val))),
        Formula::Gt(Box::new(sum), Box::new(Formula::Int(max_val))),
    ]);

    let vc = VerificationCondition {
        kind: VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (Ty::usize(), Ty::usize()),
        },
        function: "midpoint".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation: None,
    };

    let result = ay.verify(&vc);
    eprintln!("Direct overflow formula result: {result:?}");
    assert!(result.is_failed(), "overflow formula must be SAT. Got: {result:?}");

    if let VerificationResult::Failed { counterexample: Some(cex), time_ms, .. } = &result {
        eprintln!("Solved in {time_ms}ms — Counterexample: {cex}");
        assert!(!cex.assignments.is_empty());
    }
}

#[test]
fn test_real_ay_direct_divzero_constant_safe() {
    if !ay_available() {
        eprintln!("SKIP: ay not found by integration-test helper");
        return;
    }
    let ay = require_ay();

    let formula = Formula::Eq(Box::new(Formula::Int(2)), Box::new(Formula::Int(0)));

    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "div_by_two".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation: None,
    };

    let result = ay.verify(&vc);
    eprintln!("Direct divzero-constant result: {result:?}");
    assert!(result.is_proved(), "2 == 0 must be UNSAT (proved safe). Got: {result:?}");
}
