// rung-F u32-bound (docs/design/2026-07-10-structural-fold-lane.md §1 last
// bullet): a u32-measure function's exact checked-arithmetic `NonTermination`
// VC must be refutable in the existing vc_refute lane — kernel-checked modulo
// the 3 foundational axioms — with NO gate-policy change and NO reliance on
// the downstream `augment_with_type_bounds` re-derivation. The bound conjoined
// at VC assembly is the type tautology `measure >= 0` for an UNSIGNED measure
// parameter. Raw fixed-width arithmetic is deliberately outside this lane:
// reinterpreting a wrapping step as mathematical Int can false-prove
// termination. This file pins:
//
//   1. the checked terminating u32 shape (`f(n) -> f(n - 1)`) REFUTES modulo 3;
//   2. raw fixed-width recursion DECLINES rather than importing wrapping math;
//   3. the SIGNED control (`i32` measure, no precondition) stays OPEN — a
//      fabricated `n >= 0` there would be a gate-weakening false-prove
//      (`f(n) -> f(-1) -> f(-1)` genuinely never terminates);
//   4. the genuinely NON-decreasing u32 recursion (`f(n) -> f(n)`) stays
//      OPEN — the bound must never mask a real non-termination witness.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use trust_clean::RefuteOutcome;
use trust_clean::vc_refute::check_refute_vc;
use trust_types::*;

/// `fn factorial(n: u32) -> u32 { if n == 0 { 1 } else { n * factorial(n - 1) } }`
/// — the same MIR shape as `trust-vcgen`'s termination unit fixture: the
/// recursive call block defines the temp `_3 = n - 1` and passes it.
fn recursive_u32_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "factorial".to_string(),
        def_path: "test::factorial".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: None },
                LocalDecl { index: 3, ty: Ty::u32(), name: None },
                LocalDecl { index: 4, ty: Ty::u32(), name: None },
                LocalDecl { index: 5, ty: Ty::u32(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    // Trust: 2026-08 admission audit — an unsigned literal must carry
                    // the compared local's own width (real MIR spells `n == 0u32` as
                    // `Uint(0, 32)`); the old `Uint(_, 64)` spelling collapses the
                    // whole function to MalformedTrustIr.
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(0, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(1, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(1, 32))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Sub,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(1, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Call {
                        is_unsafe_sig: false,
                        callee_identity: None,
                        is_foreign: false,
                        func: "test::factorial".to_string(),
                        args: vec![Operand::Copy(Place::local(3))],
                        dest: Place::local(4),
                        target: Some(BlockId(3)),
                        unwind: UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Mul,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(4)),
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
            arg_count: 1,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// The SIGNED control: exact recursion to the constant `-1` (no precondition).
fn recursive_i32_constant_function() -> VerifiableFunction {
    let mut func = recursive_u32_function();
    func.name = "recur_minus_one".to_string();
    func.def_path = "test::recur_minus_one".to_string();
    for idx in [0usize, 1, 3, 4, 5] {
        func.body.locals[idx].ty = Ty::i32();
    }
    func.body.return_ty = Ty::i32();
    // Trust: 2026-08 admission audit — a signed comparison/use carries the widthless
    // `ConstValue::Int` spelling in real MIR; keeping the base fixture's `Uint(_, 32)`
    // against the retyped i32 locals collapses the function to MalformedTrustIr.
    let Statement::Assign { rvalue: Rvalue::BinaryOp(_, _, cmp_rhs), .. } =
        &mut func.body.blocks[0].stmts[0]
    else {
        panic!("fixture guard block must open with the comparison");
    };
    *cmp_rhs = Operand::Constant(ConstValue::Int(0));
    let Statement::Assign { rvalue: Rvalue::Use(base_case), .. } =
        &mut func.body.blocks[1].stmts[0]
    else {
        panic!("fixture base case must be the constant return");
    };
    *base_case = Operand::Constant(ConstValue::Int(1));
    func.body.blocks[2].stmts.clear();
    let Terminator::Call { func: callee, args, .. } = &mut func.body.blocks[2].terminator else {
        panic!("fixture call block must end in Call");
    };
    *callee = "test::recur_minus_one".to_string();
    *args = vec![Operand::Constant(ConstValue::Int(-1))];
    func
}

#[test]
fn raw_u32_decreasing_recursion_emits_no_nontermination_vc() {
    let vcs = nontermination_vcs(&recursive_u32_function());
    assert!(
        vcs.is_empty(),
        "raw fixed-width n - 1 must not be reinterpreted as mathematical Int: {vcs:?}"
    );
}

#[test]
fn i32_constant_recursion_nontermination_vc_stays_open() {
    // Without a fabricated signed lower bound, n = -1 witnesses the real
    // self-cycle `f(-1) -> f(-1)`. Injecting `n >= 0` would make this exact
    // violation formula refute and would therefore be a false proof.
    let vc = the_nontermination_vc(&recursive_i32_constant_function());
    assert_eq!(
        check_refute_vc(&vc.formula),
        None,
        "signed measure with no precondition must stay open; formula: {:?}",
        vc.formula
    );
}

/// Genuinely non-decreasing u32 recursion: `fn spin_same(n: u32) { spin_same(n) }`.
fn recursive_same_arg_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "spin_same".to_string(),
        def_path: "test::spin_same".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        is_unsafe_sig: false,
                        callee_identity: None,
                        is_foreign: false,
                        func: "test::spin_same".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        unwind: UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// The single `NonTermination` VC of `func`, as emitted by the production
/// `generate_vcs` entry point (not a hand-built formula).
fn nontermination_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::NonTermination { .. }))
        .collect()
}

fn the_nontermination_vc(func: &VerifiableFunction) -> VerificationCondition {
    let mut vcs: Vec<_> = trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::NonTermination { .. }))
        .collect();
    assert_eq!(vcs.len(), 1, "fixture must yield exactly one NonTermination VC");
    vcs.pop().unwrap()
}

#[test]
fn non_decreasing_u32_recursion_nontermination_vc_stays_open() {
    // `spin_same(n) -> spin_same(n)`: the `measure_call >= measure_entry`
    // disjunct is `n >= n`, true at every n >= 0 — a real non-termination
    // witness the type bound must never mask.
    let vc = the_nontermination_vc(&recursive_same_arg_function());
    assert_eq!(
        check_refute_vc(&vc.formula),
        None,
        "genuinely non-decreasing u32 recursion must stay open; formula: {:?}",
        vc.formula
    );
}

/// The real `infer_implicit_n` MIR shape (debug/checked build): the decrement
/// is an overflow-checked op in the block BEFORE the call —
///   bb2: _3 = CheckedSub(n, 1); Assert(!_3.1, Overflow(Sub)) -> bb3
///   bb3: _4 = move (_3.0);      call rec_cs(_4)
/// Measured on the census dump (2026-07-11): the call-block-only def
/// extraction leaves `_3.0` free, so the VC stays SAT even though the u32
/// range fact `0 <= n <= u32::MAX` is ALREADY conjoined by the extraction's
/// audit-#6 parameter-range preconditions. The rung-F checked-chain
/// resolution substitutes the Assert-success value `n - 1` for the call
/// measure, making the VC self-containedly UNSAT.
fn recursive_checked_sub_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "rec_cs".to_string(),
        def_path: "test::rec_cs".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: None },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
                LocalDecl { index: 4, ty: Ty::u32(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(0, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(1, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Sub,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(1, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Move(Place {
                            local: 3,
                            projections: vec![Projection::Field(1)],
                        }),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Sub),
                        target: BlockId(3),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::Use(Operand::Move(Place {
                            local: 3,
                            projections: vec![Projection::Field(0)],
                        })),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Call {
                        is_unsafe_sig: false,
                        callee_identity: None,
                        is_foreign: false,
                        func: "test::rec_cs".to_string(),
                        args: vec![Operand::Move(Place::local(4))],
                        dest: Place::local(0),
                        target: Some(BlockId(4)),
                        unwind: UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn u32_checked_sub_recursion_nontermination_vc_refutes_modulo_3() {
    // Post checked-chain resolution the RAW VC's disjunction is
    // Or([n - 1 >= n, n < 0]) under the conjoined bound n >= 0 — both
    // branches close in the kernel.
    let vc = the_nontermination_vc(&recursive_checked_sub_function());
    assert_eq!(
        check_refute_vc(&vc.formula),
        Some(RefuteOutcome::RefutedModulo3),
        "checked-sub two-block decrement: the RAW NonTermination VC must be kernel-refutable; formula: {:?}",
        vc.formula
    );
}

#[test]
fn u32_checked_sub_two_preds_nontermination_vc_stays_open() {
    // A second in-edge into the call block bypasses the overflow Assert, so
    // the success-edge fact is not path-valid — the resolver must decline
    // and the remaining free-temp VC must stay open (fail-closed, no false-prove).
    let mut func = recursive_checked_sub_function();
    func.body.blocks[1].terminator = Terminator::Goto(BlockId(3));
    let vc = the_nontermination_vc(&func);
    assert_eq!(
        check_refute_vc(&vc.formula),
        None,
        "two-pred call block must stay open; formula: {:?}",
        vc.formula
    );
}

// --- LOOP-lane twins (rung-F loop-lane u32-bound parity; the gap NOTED in
// a82a7c83e4): the old raw LOOP lane reinterpreted fixed-width subtraction as
// mathematical Int, which was unsound in the presence of wraparound. Raw
// arithmetic now DECLINES. The exact checked-decrement lane retains the honest
// three-way split: terminating-u32 REFUTES modulo 3; signed measures decline;
// and a genuinely non-decreasing exact loop stays OPEN. The checked-decrement
// blindness is CLOSED: the recursion lane's checked-chain resolution is ported
// to the loop lane (`termination.rs::resolve_loop_checked_step_chain`) with
// loop-specific fail-closed guards — Assert-pred INSIDE this loop's
// body_blocks (an outside pred is a loop-INVARIANT step: a fabricated
// per-iteration decrease), step block != function entry block, two-pred /
// mutated-operand / non-Assign write channels all DECLINE. ---

/// `fn countdown(n: u32) { while n > 0 { n -= 1 } }`, release-shape step
/// `n = n - 1` in a single loop-body block:
/// ```text
///   bb0 (header): cond = n > 0; SwitchInt(cond) -> [1: bb1, otherwise: bb2]
///   bb1: n = n - 1; goto bb0   (back-edge)
///   bb2: return
/// ```
fn countdown_loop_u32_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "countdown".to_string(),
        def_path: "test::countdown".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("cond".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Gt,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(0, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(1, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Sub,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(1, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(0)), // back-edge
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// The SIGNED control: identical countdown loop over `i32`.
fn countdown_loop_i32_function() -> VerifiableFunction {
    let mut func = countdown_loop_u32_function();
    func.name = "countdown_i".to_string();
    func.def_path = "test::countdown_i".to_string();
    func.body.locals[1].ty = Ty::i32();
    // Trust: 2026-08 admission audit — the retyped i32 operands need the signed
    // widthless `ConstValue::Int` literal spelling real MIR carries; the inherited
    // `Uint(_, 32)` literals would collapse the function to MalformedTrustIr and make
    // the consuming test pass vacuously.
    let Statement::Assign { rvalue: Rvalue::BinaryOp(_, _, guard_rhs), .. } =
        &mut func.body.blocks[0].stmts[0]
    else {
        panic!("countdown guard block must open with the comparison");
    };
    *guard_rhs = Operand::Constant(ConstValue::Int(0));
    let Statement::Assign { rvalue: Rvalue::BinaryOp(_, _, step_rhs), .. } =
        &mut func.body.blocks[1].stmts[0]
    else {
        panic!("countdown step block must open with the decrement");
    };
    *step_rhs = Operand::Constant(ConstValue::Int(1));
    func
}

/// Genuinely non-decreasing u32 loop: `while n > 0 { n = n }`. The identity
/// step is exact in both the machine and mathematical-Int carriers, so the
/// inferred lane must emit an obligation and leave its real witness open.
fn same_value_loop_u32_function() -> VerifiableFunction {
    let mut func = countdown_loop_u32_function();
    func.name = "same_value_forever".to_string();
    func.def_path = "test::same_value_forever".to_string();
    func.body.blocks[1].stmts[0] = Statement::Assign {
        place: Place::local(1),
        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
        span: SourceSpan::default(),
    };
    func
}

/// The debug/checked-build countdown loop — the decrement is an
/// overflow-checked op in the step block's unique Assert-predecessor:
/// ```text
///   bb0 (header): cond = n > 0; SwitchInt(cond) -> [1: bb1, otherwise: bb3]
///   bb1: _3 = CheckedSub(n, 1); Assert(!_3.1, Overflow(Sub)) -> bb2
///   bb2: n = move (_3.0); goto bb0   (back-edge)
///   bb3: return
/// ```
/// Without the rung-F checked-chain resolution the step was the FREE `.0`
/// read — the landed lane declined the binding and emitted NO obligation
/// (the named gap). The loop-lane port resolves the step through the unique
/// in-loop Assert-predecessor to `n - 1`, so the VC now exists AND refutes.
fn countdown_loop_checked_sub_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "countdown_cs".to_string(),
        def_path: "test::countdown_cs".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("cond".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Gt,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(0, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(1, BlockId(1))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Sub,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(1, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Move(Place {
                            local: 3,
                            projections: vec![Projection::Field(1)],
                        }),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Sub),
                        target: BlockId(2),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Use(Operand::Move(Place {
                            local: 3,
                            projections: vec![Projection::Field(0)],
                        })),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(0)), // back-edge
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn raw_u32_countdown_loop_emits_no_nontermination_vc() {
    let vcs = nontermination_vcs(&countdown_loop_u32_function());
    assert!(
        vcs.is_empty(),
        "raw fixed-width n = n - 1 must not be reinterpreted as mathematical Int: {vcs:?}"
    );
}

#[test]
fn i32_countdown_loop_emits_no_nontermination_vc() {
    // SIGNED contract of the LANDED loop lane: a signed measure does not
    // bind, and a loop with an exit and no bindable measure yields NO
    // obligation (Unknown territory) — never a fabricated `n >= 0` bound.
    // Zero VCs is fail-closed here: nothing is emitted, nothing can be
    // falsely proven. (An alternate implementation emitted the VC and left
    // it open; both contracts are sound — this pin documents the landed
    // one. If a VC ever APPEARS here and refutes, a signed bound leaked —
    // a false-prove.)
    let vcs = nontermination_vcs(&countdown_loop_i32_function());
    assert!(
        vcs.is_empty(),
        "signed loop measure must yield no NonTermination obligation; got {:?}",
        vcs.iter().map(|vc| &vc.formula).collect::<Vec<_>>()
    );
}

#[test]
fn non_decreasing_u32_loop_nontermination_vc_stays_open() {
    // `while n > 0 { n = n }`: the `measure_after >= measure_before`
    // disjunct is `n >= n`, true at every n >= 0 — a real
    // non-termination witness the type bound must never mask.
    let vc = the_nontermination_vc(&same_value_loop_u32_function());
    assert_eq!(
        check_refute_vc(&vc.formula),
        None,
        "genuinely non-decreasing u32 loop must stay open; formula: {:?}",
        vc.formula
    );
}

#[test]
fn u32_checked_sub_loop_nontermination_vc_refutes_modulo_3() {
    // GAP CLOSED (this pin was `u32_checked_sub_loop_emits_no_nontermination_
    // vc_yet`, the named residual gap of a82a7c83e4): the recursion lane's
    // checked-chain resolution is ported to the loop lane
    // (`trust-vcgen/src/termination.rs::resolve_loop_checked_step_chain`).
    // The debug-shape decrement (`_3 = CheckedSub(n, 1); Assert(!_3.1) ->
    // n = _3.0`) resolves through the step block's unique IN-LOOP
    // Assert-predecessor — on the success edge `_3.0` IS the mathematical
    // `n - 1` — so the measure binds and the RAW VC is
    // And([n >= 0, Or([n - 1 >= n, n < 0])]), identical in shape to the
    // release-form countdown twin: both branches close in the kernel.
    let vc = the_nontermination_vc(&countdown_loop_checked_sub_function());
    assert_eq!(
        check_refute_vc(&vc.formula),
        Some(RefuteOutcome::RefutedModulo3),
        "checked-sub loop decrement: the RAW NonTermination VC must be kernel-refutable; formula: {:?}",
        vc.formula
    );
}

#[test]
fn u32_checked_sub_loop_two_preds_stays_no_vc_or_open() {
    // CONTROL (fail-closed): a second in-edge into the step block bypasses
    // the overflow Assert, so the success-edge fact `_3.0 = n - 1` is not
    // valid on every path into the step — the resolver must DECLINE. The
    // sound outcomes are NO obligation (the landed lane's behavior: no
    // binding + exit-ful loop => nothing emitted) or an obligation that
    // stays OPEN. A refutation here would be a false termination proof.
    let mut func = countdown_loop_checked_sub_function();
    let Terminator::SwitchInt { targets, .. } = &mut func.body.blocks[0].terminator else {
        panic!("header must be a SwitchInt");
    };
    targets.push((2, BlockId(2))); // second in-edge into the step block
    let vcs = nontermination_vcs(&func);
    for vc in &vcs {
        assert_eq!(
            check_refute_vc(&vc.formula),
            None,
            "two-pred step block must never refute; formula: {:?}",
            vc.formula
        );
    }
}

/// Outside-pred control shape: the checked op lives in a PREHEADER, outside
/// the loop —
/// ```text
///   bb0 (preheader): _3 = CheckedSub(n, 1); Assert(!_3.1, Overflow(Sub)) -> bb1
///   bb1 (header):    cond = n > 0; SwitchInt -> [1: bb2, otherwise: bb3]
///   bb2 (step):      n = move (_3.0); goto bb1   (back-edge)
///   bb3: return
/// ```
/// The checked op runs ONCE: every iteration re-assigns the SAME value
/// `n0 - 1`, so for `n0 >= 2` this loop genuinely NEVER terminates
/// (`n` stalls at `n0 - 1 > 0`). Resolving `n - 1` here would fabricate a
/// fresh decrease per iteration — the exact false-prove the
/// Assert-pred-INSIDE-body guard exists to prevent.
fn countdown_loop_checked_sub_preheader_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "countdown_cs_preheader".to_string(),
        def_path: "test::countdown_cs_preheader".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("cond".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Sub,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(1, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Move(Place {
                            local: 3,
                            projections: vec![Projection::Field(1)],
                        }),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Sub),
                        target: BlockId(1),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Gt,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(0, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(1, BlockId(2))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Use(Operand::Move(Place {
                            local: 3,
                            projections: vec![Projection::Field(0)],
                        })),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(1)), // back-edge
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn u32_checked_sub_loop_outside_assert_pred_stays_no_vc_or_open() {
    // CONTROL (fail-closed): loop-invariant step — see the fixture doc; this
    // loop genuinely never terminates for n >= 2, so any refutation here is
    // a false termination proof. Sound outcomes: NO obligation (landed lane:
    // the step's unique pred is the header SwitchInt, not an in-loop Assert,
    // so nothing binds and the exit-ful loop emits nothing) or an obligation
    // that stays OPEN.
    let func = countdown_loop_checked_sub_preheader_function();
    let vcs = nontermination_vcs(&func);
    for vc in &vcs {
        assert_eq!(
            check_refute_vc(&vc.formula),
            None,
            "loop-invariant checked step must never refute; formula: {:?}",
            vc.formula
        );
    }
}
