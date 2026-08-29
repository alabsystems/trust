// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 16 — the ARITY WIDENING's mutation battery (R3a).**
//!
//! `control_8` is R2's, at arity 1. This is the same battery at arity 2, and it
//! exists because the widening made three things load-bearing that were
//! previously constants and therefore untestable:
//!
//! 1. **which parameter the recursion descends on** — `measure_index`, read out
//!    of the emitted body's zero-test borrow;
//! 2. **which de Bruijn index a THREADED parameter renders at** — the
//!    `nat.param` row at a `Site` whose index is now a function of the arity;
//! 3. **the ORDER of the self-call's operands** — at arity 1 there was one
//!    operand and no order to get wrong.
//!
//! Side A is the REAL elaborated `dbl` (through
//! `trust_certify::clean_island::CleanIslandSession`, never a hand-built
//! mirror), and side B is the emitted-MIR contract traced BY HAND through
//! `ArmLowerer` — not rendered by the materializer, so a materializer defect
//! cannot make this control agree with itself.
//!
//! **`dbl` and not `addAcc` for every operand-order row.** `addAcc` computes
//! `a + b`, which is symmetric in its two parameters; a swap mutation on it
//! could pass on arithmetic rather than on the term, and the control would be
//! measuring nothing. `dbl a b = b * 2^a` is not symmetric — `dbl 3 1 = 8`,
//! `dbl 1 3 = 6` — and `r7_arity_widening_probes` q4 pins that the KERNEL
//! refuses the swapped values, which is what makes the swap rows below real.

#![allow(clippy::doc_markdown)]

use clean_kernel::{Environment, Name};
use trust_clean_origin::emit::{CleanOriginShape, plan_clean_origin_body};
use trust_clean_origin::{EmitRefusal, FaithfulnessMethod, admit_lowering};
use trust_types::admissible_body::{RecBodyExpr, WfRecBody, recognize_wf_nat_rec};
use trust_types::{
    BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
};

// ═══════════════════════════════════════════════════════════════════════════
// side A — the REAL session
// ═══════════════════════════════════════════════════════════════════════════

const DBL: &str = "def dbl (a b : Nat) : Nat := \
                   if h : 0 < a then dbl (a - 1) (b * 2) else b\n\
                   termination_by a";

fn island(source: &str) -> Result<Environment, String> {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&[source]);
    if batch.is_rejected() {
        let mut msgs: Vec<String> = batch
            .outcomes
            .iter()
            .flat_map(|o| o.errors.iter().map(|e| e.message.clone()))
            .collect();
        msgs.extend(batch.cycles.iter().map(|c| c.message.clone()));
        return Err(msgs.join(" | "));
    }
    Ok(session.environment().expect("an untainted session has an environment").clone())
}

fn dbl_env() -> Environment {
    island(DBL).expect("`dbl` must elaborate and kernel-check at this pin")
}

/// The planned quartet for `dbl`, in the vocabulary both sides use.
fn planned_shape() -> CleanOriginShape {
    CleanOriginShape::WellFoundedNatRec {
        zero_value: RecBodyExpr::Param(1),
        nonzero_value: RecBodyExpr::Rec,
        rec_args: vec![
            RecBodyExpr::Pred,
            RecBodyExpr::Mul(
                Box::new(RecBodyExpr::Param(1)),
                Box::new(RecBodyExpr::NatConst(2)),
            ),
        ],
        measure_index: 0,
        lowering: trust_clean_origin::WfLowering::OnParameter,
    }
}

fn recognised_body() -> WfRecBody {
    WfRecBody {
        zero_value: RecBodyExpr::Param(1),
        nonzero_value: RecBodyExpr::Rec,
        rec_args: vec![
            RecBodyExpr::Pred,
            RecBodyExpr::Mul(
                Box::new(RecBodyExpr::Param(1)),
                Box::new(RecBodyExpr::NatConst(2)),
            ),
        ],
        measure_index: 0,
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// side B — the emission, traced BY HAND through `ArmLowerer`
// ═══════════════════════════════════════════════════════════════════════════
//
// ```text
// _0,_1,_2,_5,_8,_9,_12,_13 : Nat   _3,_6,_7,_10,_11 : &Nat   _4 : bool
//                                   (_13 declared and dead — the root's temp)
// bb0: _3 = &_1;  is_zero(move _3) -> _4, bb1
// bb1: switchInt(move _4) [(0, bb3)] otherwise bb2
// bb2: _0 = move _2; goto bb8                                 // zero arm: `b`
// bb3: from_u64(const 1u64) -> _5, bb4                        // nonzero arm…
// bb4: _6 = &_1; _7 = &_5; sub(move _6, move _7) -> _8, bb5   //   a - 1
// bb5: from_u64(const 2u64) -> _9, bb6
// bb6: _10 = &_2; _11 = &_9; mul(move _10, move _11) -> _12, bb7  //   b * 2
// bb7: dbl(move _8, move _12) -> _0, bb8                      //   THE call
// bb8: return
// ```
//
// The MEASURE is readable straight out of bb0: the zero test borrows `_1`, so
// `measure_index = 0`. Mutation (e) moves exactly that borrow.

const DBL_SELF_PATH: &str = "clean_origin_wf_rec_arity::dbl";
const BIGNUM_SUB: &str = "trust_bignum::arith::<impl trust_bignum::Nat>::sub";
const BIGNUM_ADD: &str = "trust_bignum::arith::<impl trust_bignum::Nat>::add";
const BIGNUM_MUL: &str = "trust_bignum::arith::<impl trust_bignum::Nat>::mul";

fn nat_adt() -> Ty {
    Ty::adt("trust_bignum::Nat", Vec::new())
}

fn nat_local(index: usize) -> LocalDecl {
    LocalDecl { index, ty: nat_adt(), name: None }
}

fn nat_ref_local(index: usize) -> LocalDecl {
    LocalDecl { index, ty: Ty::Ref { mutable: false, inner: Box::new(nat_adt()) }, name: None }
}

fn borrow(place: usize, of: usize) -> Statement {
    Statement::Assign {
        place: Place::local(place),
        rvalue: Rvalue::Ref { mutable: false, place: Place::local(of) },
        span: SourceSpan::default(),
    }
}

fn call(callee: &str, args: Vec<Operand>, dest: usize, target: usize) -> Terminator {
    Terminator::Call {
        func: callee.into(),
        args,
        dest: Place::local(dest),
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        unwind: UnwindEdge::Continue,
        callee_identity: None,
    }
}

fn emitted_dbl() -> VerifiableFunction {
    let locals = vec![
        nat_local(0),
        nat_local(1),
        nat_local(2),
        nat_ref_local(3),
        LocalDecl { index: 4, ty: Ty::Bool, name: None },
        nat_local(5),
        nat_ref_local(6),
        nat_ref_local(7),
        nat_local(8),
        nat_local(9),
        nat_ref_local(10),
        nat_ref_local(11),
        nat_local(12),
        nat_local(13),
    ];
    let blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![borrow(3, 1)],
            terminator: call(
                "trust_bignum::Nat::is_zero",
                vec![Operand::Move(Place::local(3))],
                4,
                1,
            ),
        },
        BasicBlock {
            id: BlockId(1),
            stmts: Vec::new(),
            terminator: Terminator::SwitchInt {
                discr: Operand::Move(Place::local(4)),
                targets: vec![(0, BlockId(3))],
                otherwise: BlockId(2),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        },
        BasicBlock {
            id: BlockId(2),
            stmts: vec![Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::Use(Operand::Move(Place::local(2))),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Goto(BlockId(8)),
        },
        BasicBlock {
            id: BlockId(3),
            stmts: Vec::new(),
            terminator: call(
                "trust_bignum::Nat::from_u64",
                vec![Operand::Constant(ConstValue::Uint(1, 64))],
                5,
                4,
            ),
        },
        BasicBlock {
            id: BlockId(4),
            stmts: vec![borrow(6, 1), borrow(7, 5)],
            terminator: call(
                BIGNUM_SUB,
                vec![Operand::Move(Place::local(6)), Operand::Move(Place::local(7))],
                8,
                5,
            ),
        },
        BasicBlock {
            id: BlockId(5),
            stmts: Vec::new(),
            terminator: call(
                "trust_bignum::Nat::from_u64",
                vec![Operand::Constant(ConstValue::Uint(2, 64))],
                9,
                6,
            ),
        },
        BasicBlock {
            id: BlockId(6),
            stmts: vec![borrow(10, 2), borrow(11, 9)],
            terminator: call(
                BIGNUM_MUL,
                vec![Operand::Move(Place::local(10)), Operand::Move(Place::local(11))],
                12,
                7,
            ),
        },
        BasicBlock {
            id: BlockId(7),
            stmts: Vec::new(),
            terminator: call(
                DBL_SELF_PATH,
                vec![Operand::Move(Place::local(8)), Operand::Move(Place::local(12))],
                0,
                8,
            ),
        },
        BasicBlock { id: BlockId(8), stmts: Vec::new(), terminator: Terminator::Return },
    ];
    VerifiableFunction {
        name: "dbl".into(),
        def_path: DBL_SELF_PATH.into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: 2,
            return_ty: nat_adt(),
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
    }
}

/// Replace the callee of one block's `Call` terminator.
fn with_callee(mut body: VerifiableFunction, block: usize, callee: &str) -> VerifiableFunction {
    if let Terminator::Call { func, .. } = &mut body.body.blocks[block].terminator {
        *func = callee.into();
    }
    body
}

/// Replace the argument list of one block's `Call` terminator.
fn with_args(
    mut body: VerifiableFunction,
    block: usize,
    args: Vec<Operand>,
) -> VerifiableFunction {
    if let Terminator::Call { args: slot, .. } = &mut body.body.blocks[block].terminator {
        *slot = args;
    }
    body
}

fn gate_side_b(env: &Environment, body: &WfRecBody) -> Result<(), String> {
    let reflected = trust_clean_origin::reflect_wf::reflect_wf_functional(env, "dbl", body, trust_clean_origin::WfLowering::OnParameter)
        .map_err(|detail| format!("reflection refused: {detail}"))?;
    let plan = plan_clean_origin_body(env, "dbl").expect("dbl plans");
    trust_clean_origin::gate::check_faithful_wf_functional(
        env,
        "dbl",
        &reflected,
        plan.result_carrier(),
    )
    .map(|_| ())
    .map_err(|refusal| format!("gate refused: {}", refusal.note()))
}

// ═══════════════════════════════════════════════════════════════════════════
// THE ADMIT
// ═══════════════════════════════════════════════════════════════════════════

/// The whole route, at arity 2, against the REAL elaborated side A.
#[test]
fn control_16_the_two_parameter_emission_admits_end_to_end() {
    let env = dbl_env();
    assert!(env.get_const(&Name::from_string("Nat.mul")).is_some(), "`Nat.mul` must exist");

    let plan = plan_clean_origin_body(&env, "dbl").expect("`dbl` must plan");
    assert_eq!(plan.shape(), &planned_shape(), "zero arm `b`, self-call `(a - 1, b * 2)`");
    assert_eq!(plan.signature().arity(), 2);

    let extracted = emitted_dbl();
    assert_eq!(
        recognize_wf_nat_rec(&extracted),
        Some(recognised_body()),
        "the emitted-and-extracted body must read back as the planned recursion, with the \
         MEASURE read out of the zero test's own borrow"
    );

    let faithful =
        admit_lowering(&env, &plan, &extracted).expect("the emission must pass the F-layer gate");
    assert_eq!(faithful.name(), "dbl");
    assert_eq!(faithful.admitted_at(), &Ty::BignumNat);
    assert_eq!(faithful.method(), FaithfulnessMethod::WellFoundedFunctionalDefeq);
    eprintln!("CONTROL-16 admit | dbl (arity 2) FAITHFUL by WellFoundedFunctionalDefeq");
}

/// R2's arity-1 lane must be UNMOVED. Not a re-run of `control_8` — this
/// asserts the one fact the widening could most easily have broken silently:
/// that `countdownSum` still plans to the same trio, with a one-element
/// argument list and the measure at parameter 0.
#[test]
fn control_16_the_arity_one_lane_is_unmoved() {
    let env = island(
        "def countdownSum (n : Nat) : Nat := \
         if h : 0 < n then n + countdownSum (n - 1) else 0\n\
         termination_by n",
    )
    .expect("elaborates");
    let plan = plan_clean_origin_body(&env, "countdownSum").expect("plans");
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::WellFoundedNatRec {
            zero_value: RecBodyExpr::NatConst(0),
            nonzero_value: RecBodyExpr::Add(
                Box::new(RecBodyExpr::Decreasing),
                Box::new(RecBodyExpr::Rec),
            ),
            rec_args: vec![RecBodyExpr::Pred],
            measure_index: 0,
            lowering: trust_clean_origin::WfLowering::OnParameter,
        },
        "R2's baseline must read back exactly as it did before the widening"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// THE MUTATIONS — an ADMIT with no refused sibling is not a measurement
// ═══════════════════════════════════════════════════════════════════════════

/// (a) THE WRONG OPERATOR. The emitted body computes `+` where side A says `*`.
#[test]
fn control_16_a_wrong_operator_is_refused_at_both_layers() {
    let env = dbl_env();
    let plan = plan_clean_origin_body(&env, "dbl").expect("plans");

    let refusal = admit_lowering(&env, &plan, &with_callee(emitted_dbl(), 6, BIGNUM_ADD))
        .expect_err("`add` where the definition says `mul` must never emit");
    assert!(
        matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }),
        "expected the structural catch, got {refusal:?}"
    );
    assert!(refusal.is_compiler_defect(), "a wrong emission is a compiler defect");

    // The SAME mutation at the kernel, with the recognizer removed, so the
    // structural catch is never the only thing standing there.
    let wrong_reading = WfRecBody {
        rec_args: vec![
            RecBodyExpr::Pred,
            RecBodyExpr::Add(
                Box::new(RecBodyExpr::Param(1)),
                Box::new(RecBodyExpr::NatConst(2)),
            ),
        ],
        ..recognised_body()
    };
    assert!(
        gate_side_b(&env, &wrong_reading).is_err(),
        "the KERNEL must separate `Nat.add b 2` from side A's `HMul.hMul … b 2` inside the \
         self-call's threaded argument"
    );
    eprintln!("CONTROL-16 (a) add-for-mul | REFUSED structurally AND at the kernel");
}

/// (b) SWAPPED OPERANDS inside the threaded argument — `2 * b` for `b * 2`.
///
/// `Nat.mul`'s commutativity is a THEOREM in this kernel, not a definitional
/// identity, so defeq on the stuck `dite` separates the two orders. That is
/// what makes the operand order of the emitted call load-bearing rather than
/// incidental, and it is measured here at a THREADED position, which is new.
#[test]
fn control_16_b_swapped_operands_are_refused_at_both_layers() {
    let env = dbl_env();
    let plan = plan_clean_origin_body(&env, "dbl").expect("plans");

    let swapped = with_args(
        emitted_dbl(),
        6,
        vec![Operand::Move(Place::local(11)), Operand::Move(Place::local(10))],
    );
    assert!(
        matches!(
            admit_lowering(&env, &plan, &swapped),
            Err(EmitRefusal::LoweringShapeMismatch { .. })
        ),
        "`mul(&2, &b)` where the definition says `mul(&b, &2)` must not emit"
    );

    let swapped_reading = WfRecBody {
        rec_args: vec![
            RecBodyExpr::Pred,
            RecBodyExpr::Mul(
                Box::new(RecBodyExpr::NatConst(2)),
                Box::new(RecBodyExpr::Param(1)),
            ),
        ],
        ..recognised_body()
    };
    assert!(
        gate_side_b(&env, &swapped_reading).is_err(),
        "the gate must decide on the TERM, not on arithmetic: `Nat.mul 2 b` and \
         `Nat.mul b 2` are equal in VALUE and must still be separated"
    );
    eprintln!("CONTROL-16 (b) swapped operands | REFUSED (operand order is decided)");
}

/// (c) FORGED CALLEES. A table that accepted "anything ending in `::mul`" — or
/// a self-call authenticated by suffix rather than by `def_path` — is caught
/// here.
#[test]
fn control_16_c_forged_callees_are_refused() {
    let env = dbl_env();
    let plan = plan_clean_origin_body(&env, "dbl").expect("plans");

    for forged in [
        "my_crate::arith::<impl my_crate::Nat>::mul",
        "evil_bignum::Nat::mul",
        "trust_bignum::arith::<impl trust_bignum::Nat>::checked_mul",
    ] {
        assert!(
            matches!(
                admit_lowering(&env, &plan, &with_callee(emitted_dbl(), 6, forged)),
                Err(EmitRefusal::LoweringUnrecognised { .. })
            ),
            "`{forged}` must not authenticate as the runtime's `mul`"
        );
    }
    // THE SELF-CALL's callee, which at arity 2 is the one that carries the
    // threaded operand: a forged recursion is not this body's recursion.
    for forged in ["clean_origin_wf_rec_arity::dblish", "other_crate::dbl"] {
        assert!(
            matches!(
                admit_lowering(&env, &plan, &with_callee(emitted_dbl(), 7, forged)),
                Err(EmitRefusal::LoweringUnrecognised { .. })
            ),
            "`{forged}` must not authenticate as `dbl`'s own self-call"
        );
    }
    eprintln!("CONTROL-16 (c) forged callees | 5 near-misses REFUSED");
}

/// (d) **THE ARITY-SPECIFIC ROW: the SELF-CALL's operands, swapped.**
///
/// At arity 1 there was one operand and no order to get wrong. At arity 2 the
/// emitted `dbl(move _8, move _12)` could just as easily have been
/// `dbl(move _12, move _8)` — which computes a different function and, unlike
/// the arithmetic swap in (b), moves the DECREASING argument out of the
/// measure position. Both layers must refuse, and they refuse for different
/// reasons: the recognizer because `rec_args[measure_index]` is no longer the
/// predecessor, the kernel because side A's borrowed proof of
/// `Nat.lt (a - 1) a` cannot type at an argument of `b * 2`.
#[test]
fn control_16_d_swapped_self_call_operands_are_refused_at_both_layers() {
    let env = dbl_env();
    let plan = plan_clean_origin_body(&env, "dbl").expect("plans");

    let swapped = with_args(
        emitted_dbl(),
        7,
        vec![Operand::Move(Place::local(12)), Operand::Move(Place::local(8))],
    );
    assert_eq!(
        recognize_wf_nat_rec(&swapped),
        None,
        "a self-call whose MEASURE position is not the predecessor is outside the contract"
    );
    assert!(
        matches!(
            admit_lowering(&env, &plan, &swapped),
            Err(EmitRefusal::LoweringUnrecognised { .. })
        ),
        "the swapped self-call must not emit"
    );

    // The kernel half, with the recognizer removed.
    let swapped_reading = WfRecBody {
        rec_args: vec![
            RecBodyExpr::Mul(
                Box::new(RecBodyExpr::Param(1)),
                Box::new(RecBodyExpr::NatConst(2)),
            ),
            RecBodyExpr::Pred,
        ],
        ..recognised_body()
    };
    let refusal = gate_side_b(&env, &swapped_reading)
        .expect_err("side A's decrease proof cannot be borrowed for an argument of `b * 2`");
    eprintln!("CONTROL-16 (d) swapped self-call operands | REFUSED | {refusal}");
}

/// (e) THE WRONG MEASURE. The emitted zero test decides `b` where side A
/// descends on `a`. This is the row that makes `measure_index` a read fact
/// rather than a convention: the recognizer takes it from bb0's borrow, so
/// moving that borrow moves the whole reading — and then the `sub(&a, &1)`
/// predecessor no longer subtracts from the parameter the zero test decided.
#[test]
fn control_16_e_a_zero_test_on_the_wrong_parameter_is_refused() {
    let env = dbl_env();
    let plan = plan_clean_origin_body(&env, "dbl").expect("plans");

    let mut wrong_measure = emitted_dbl();
    wrong_measure.body.blocks[0].stmts = vec![borrow(3, 2)];
    assert_eq!(
        recognize_wf_nat_rec(&wrong_measure),
        None,
        "with the zero test on `b`, the `sub(&a, &1)` predecessor is a subtraction from a \
         parameter that is not `Decreasing`, and the arm walk fails closed"
    );
    assert!(
        matches!(
            admit_lowering(&env, &plan, &wrong_measure),
            Err(EmitRefusal::LoweringUnrecognised { .. })
        ),
        "a body that tests one parameter and decreases another must not emit"
    );
    eprintln!("CONTROL-16 (e) zero test on the wrong parameter | REFUSED");
}

/// (f) THE WRONG THREADED PARAMETER. The zero arm returns `a` where side A
/// returns `b` — one `Param` index apart, and nothing else changed. This is
/// the row the `nat.param` de Bruijn layout exists for: at arity 1 the
/// parameter site was a constant `bvar 2`, and a wrong index was
/// unrepresentable; at arity 2 it is a computed index and must be decided.
#[test]
fn control_16_f_the_wrong_parameter_index_is_refused_at_both_layers() {
    let env = dbl_env();
    let plan = plan_clean_origin_body(&env, "dbl").expect("plans");

    let mut wrong_param = emitted_dbl();
    wrong_param.body.blocks[2].stmts = vec![Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Use(Operand::Move(Place::local(1))),
        span: SourceSpan::default(),
    }];
    assert!(
        matches!(
            admit_lowering(&env, &plan, &wrong_param),
            Err(EmitRefusal::LoweringShapeMismatch { .. })
        ),
        "a zero arm returning the MEASURE where side A returns the threaded parameter must \
         not emit"
    );

    // The kernel half: `Decreasing` renders at `bvar 3`, `Param(1)` at
    // `bvar 1`, and side A's else arm is `#1`.
    let wrong_reading = WfRecBody { zero_value: RecBodyExpr::Decreasing, ..recognised_body() };
    assert!(
        gate_side_b(&env, &wrong_reading).is_err(),
        "the kernel must separate the two parameter binders — `r7` q3 measures that it \
         decides parameter order rather than tolerating it"
    );
    eprintln!("CONTROL-16 (f) wrong parameter index | REFUSED structurally AND at the kernel");
}

/// (g) THE SELF-CALL AT THE WRONG ARITY. One operand where the signature takes
/// two: the emitted body would not even compile, and the recognizer must not
/// read it as a recursion regardless.
#[test]
fn control_16_g_a_self_call_at_the_wrong_arity_is_refused() {
    let env = dbl_env();
    let plan = plan_clean_origin_body(&env, "dbl").expect("plans");

    let short_call = with_args(emitted_dbl(), 7, vec![Operand::Move(Place::local(8))]);
    assert_eq!(recognize_wf_nat_rec(&short_call), None, "one operand, two parameters");
    assert!(
        matches!(
            admit_lowering(&env, &plan, &short_call),
            Err(EmitRefusal::LoweringUnrecognised { .. })
        ),
        "a self-call the emitted signature could not accept must not emit"
    );
    eprintln!("CONTROL-16 (g) self-call at the wrong arity | REFUSED");
}

/// (h) THE ARMS SWAPPED. `control_8`'s polarity row, re-measured at arity 2:
/// the MIR's `is_zero` TRUE arm is the `dite`'s ELSE branch, and getting that
/// inversion backwards is the one-construct mistranslation the producer can
/// make. At arity 2 the two arms differ by more than a value — one holds the
/// self-call — so the swap is caught by the arm walk itself.
#[test]
fn control_16_h_swapped_arms_are_refused() {
    let env = dbl_env();
    let plan = plan_clean_origin_body(&env, "dbl").expect("plans");

    let mut swapped = emitted_dbl();
    swapped.body.blocks[1].terminator = Terminator::SwitchInt {
        discr: Operand::Move(Place::local(4)),
        targets: vec![(0, BlockId(2))],
        otherwise: BlockId(3),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    };
    assert_eq!(
        recognize_wf_nat_rec(&swapped),
        None,
        "a self-call in the arm the zero test selects for a ZERO parameter is not this contract"
    );
    assert!(
        matches!(
            admit_lowering(&env, &plan, &swapped),
            Err(EmitRefusal::LoweringUnrecognised { .. })
        ),
        "the swapped-arm emission must not emit"
    );
    eprintln!("CONTROL-16 (h) swapped arms | REFUSED");
}
