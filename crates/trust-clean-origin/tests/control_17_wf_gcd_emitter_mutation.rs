// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 17 — the GENERAL-SUBTRACTION shape's mutation battery (R3b).**
//!
//! `control_8` is R2's battery at arity 1, `control_16` is R3a's at arity 2.
//! This is R3b's, on the shape the widening exists for: the fuel-carried
//! branch-free subtractive Euclid
//!
//! ```text
//! def gcdF (f a b : Nat) : Nat :=
//!   if h : 0 < f then gcdF (f - 1) ((a - b) + (b - a)) (a - (a - b)) else a
//! termination_by f
//! ```
//!
//! whose step map is `T(a,b) = (|a-b|, min a b)` written in truncated `-` and
//! `+` alone. Three things became load-bearing here that no earlier battery
//! could test:
//!
//! 1. **operand ORDER at an arithmetic node is now observable by the kernel.**
//!    `+` and `*` are commutative at `Nat`, so `control_16`'s swap rows lean on
//!    `Nat.mul`'s commutativity being a THEOREM rather than a definitional
//!    identity. `Nat.sub` is not commutative at all — `gcd_route_probes` m1
//!    measures that `a - b = Nat.sub b a` is REFUSED — so row (b) below is a
//!    genuine refutation rather than a delicate one;
//! 2. **NESTED subtraction**, `a - (a - b)`, which is where a reader that
//!    pre-reduced `min` in Rust instead of rendering it dumbly would show up;
//! 3. **a parameter named FOUR times in one branch**, which is admitted now —
//!    every use is a shared borrow — and whose adversarial twin (a parameter
//!    handed to the self-call BY ITSELF and used again) must stay refused.
//!    Row (g) is that twin, and it is the only thing standing between the
//!    emitter and a borrow-after-move: the MIR reader accepts that body.
//!
//! Side A is the REAL elaborated `gcdF` through
//! `trust_certify::clean_island::CleanIslandSession`, never a hand-built
//! mirror. Side B is the emitted-MIR contract traced BY HAND through
//! `ArmLowerer`, so a materializer defect cannot make this control agree with
//! itself.
//!
//! **WHAT THIS FILE DOES NOT CLAIM.** It does not claim `gcd` is proved
//! correct. `Nat.gcd` is absent from the prelude (`gcd_final_probes` n1), so
//! there is nothing to state correctness against; what is measured is that a
//! genuinely recursive, genuinely gcd-computing Clean definition is emitted and
//! that every mutation of that emission is refused. The VALUES are pinned at
//! the kernel with refuting controls, in `gcd_final_probes` and in the run-pass
//! fixture `tests/ui/trust/clean_origin_wf_rec_gcd.rs`.

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

const GCDF: &str = "def gcdF (f a b : Nat) : Nat := \
                    if h : 0 < f then gcdF (f - 1) ((a - b) + (b - a)) (a - (a - b)) else a\n\
                    termination_by f";

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

fn gcdf_env() -> Environment {
    island(GCDF).expect("`gcdF` must elaborate and kernel-check at this pin")
}

fn param(index: usize) -> RecBodyExpr {
    RecBodyExpr::Param(index)
}

fn sub(left: RecBodyExpr, right: RecBodyExpr) -> RecBodyExpr {
    RecBodyExpr::Sub(Box::new(left), Box::new(right))
}

fn add(left: RecBodyExpr, right: RecBodyExpr) -> RecBodyExpr {
    RecBodyExpr::Add(Box::new(left), Box::new(right))
}

/// `(a - b) + (b - a)` — `|a - b|` in truncated `-`.
fn abs_diff() -> RecBodyExpr {
    add(sub(param(1), param(2)), sub(param(2), param(1)))
}

/// `a - (a - b)` — `min a b` in truncated `-`.
fn min_ab() -> RecBodyExpr {
    sub(param(1), sub(param(1), param(2)))
}

/// The planned quartet for `gcdF`, in the vocabulary both sides use.
fn planned_shape() -> CleanOriginShape {
    CleanOriginShape::WellFoundedNatRec {
        zero_value: param(1),
        nonzero_value: RecBodyExpr::Rec,
        rec_args: vec![RecBodyExpr::Pred, abs_diff(), min_ab()],
        measure_index: 0,
        lowering: trust_clean_origin::WfLowering::OnParameter,
    }
}

fn recognised_body() -> WfRecBody {
    WfRecBody {
        zero_value: param(1),
        nonzero_value: RecBodyExpr::Rec,
        rec_args: vec![RecBodyExpr::Pred, abs_diff(), min_ab()],
        measure_index: 0,
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// side B — the emission, traced BY HAND through `ArmLowerer`
// ═══════════════════════════════════════════════════════════════════════════
//
// ```text
// _0 _1 _2 _3 _6 _9 _12 _15 _18 _21 _24 _25 : Nat     _5 : bool
// _4 _7 _8 _10 _11 _13 _14 _16 _17 _19 _20 _22 _23    : &Nat
//                              (_25 declared and dead — the root call's temp)
// bb0:  _4 = &_1;   is_zero(move _4) -> _5, bb1
// bb1:  switchInt(move _5) [(0, bb3)] otherwise bb2
// bb2:  _0 = move _2; goto bb11                                 // zero arm: `a`
// bb3:  from_u64(const 1u64) -> _6, bb4
// bb4:  _7 = &_1;  _8 = &_6;   sub(move _7, move _8)  -> _9,  bb5   // f - 1
// bb5:  _10 = &_2; _11 = &_3;  sub(move _10, move _11) -> _12, bb6  // a - b
// bb6:  _13 = &_3; _14 = &_2;  sub(move _13, move _14) -> _15, bb7  // b - a
// bb7:  _16 = &_12; _17 = &_15; add(move _16, move _17) -> _18, bb8 // |a-b|
// bb8:  _19 = &_2; _20 = &_3;  sub(move _19, move _20) -> _21, bb9  // a - b
// bb9:  _22 = &_2; _23 = &_21; sub(move _22, move _23) -> _24, bb10 // min a b
// bb10: gcdF(move _9, move _18, move _24) -> _0, bb11               // THE call
// bb11: return
// ```
//
// **Read the borrows, because they are the whole argument for the refined
// duplication rule.** `_2` is borrowed at bb5, bb8 and bb9 and `_3` at bb5, bb6
// and bb8 — six shared borrows of two parameters, no clone, and the self-call
// at bb10 moves only TEMPS (`_9`, `_18`, `_24`). Nothing a parameter owns is
// moved, which is exactly why four uses of `a` are safe here and why the rule
// that refuses row (g) is about MOVES and not about counting.
//
// The MEASURE is readable straight out of bb0: the zero test borrows `_1`, so
// `measure_index = 0`. Mutation (e) moves exactly that borrow.

const GCDF_SELF_PATH: &str = "clean_origin_wf_rec_gcd::gcdF";
const BIGNUM_SUB: &str = "trust_bignum::arith::<impl trust_bignum::Nat>::sub";
const BIGNUM_ADD: &str = "trust_bignum::arith::<impl trust_bignum::Nat>::add";
const BIGNUM_MUL: &str = "trust_bignum::arith::<impl trust_bignum::Nat>::mul";

fn nat_adt() -> Ty {
    Ty::adt("trust_bignum::Nat", Vec::new())
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
        callee_key: None,
    }
}

fn mv(local: usize) -> Operand {
    Operand::Move(Place::local(local))
}

/// One `sub`/`add` block: two borrows, then the authenticated bignum call.
fn arith_block(
    id: usize,
    callee: &str,
    (left_ref, left): (usize, usize),
    (right_ref, right): (usize, usize),
    dest: usize,
    next: usize,
) -> BasicBlock {
    BasicBlock {
        id: BlockId(id),
        stmts: vec![borrow(left_ref, left), borrow(right_ref, right)],
        terminator: call(callee, vec![mv(left_ref), mv(right_ref)], dest, next),
    }
}

fn emitted_gcdf() -> VerifiableFunction {
    const REFS: [usize; 13] = [4, 7, 8, 10, 11, 13, 14, 16, 17, 19, 20, 22, 23];
    let locals = (0..26)
        .map(|index| LocalDecl {
            index,
            ty: if index == 5 {
                Ty::Bool
            } else if REFS.contains(&index) {
                Ty::Ref { mutable: false, inner: Box::new(nat_adt()) }
            } else {
                nat_adt()
            },
            name: None,
        })
        .collect();
    let blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![borrow(4, 1)],
            terminator: call("trust_bignum::Nat::is_zero", vec![mv(4)], 5, 1),
        },
        BasicBlock {
            id: BlockId(1),
            stmts: Vec::new(),
            terminator: Terminator::SwitchInt {
                discr: mv(5),
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
                rvalue: Rvalue::Use(mv(2)),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Goto(BlockId(11)),
        },
        BasicBlock {
            id: BlockId(3),
            stmts: Vec::new(),
            terminator: call(
                "trust_bignum::Nat::from_u64",
                vec![Operand::Constant(ConstValue::Uint(1, 64))],
                6,
                4,
            ),
        },
        arith_block(4, BIGNUM_SUB, (7, 1), (8, 6), 9, 5),
        arith_block(5, BIGNUM_SUB, (10, 2), (11, 3), 12, 6),
        arith_block(6, BIGNUM_SUB, (13, 3), (14, 2), 15, 7),
        arith_block(7, BIGNUM_ADD, (16, 12), (17, 15), 18, 8),
        arith_block(8, BIGNUM_SUB, (19, 2), (20, 3), 21, 9),
        arith_block(9, BIGNUM_SUB, (22, 2), (23, 21), 24, 10),
        BasicBlock {
            id: BlockId(10),
            stmts: Vec::new(),
            terminator: call(GCDF_SELF_PATH, vec![mv(9), mv(18), mv(24)], 0, 11),
        },
        BasicBlock { id: BlockId(11), stmts: Vec::new(), terminator: Terminator::Return },
    ];
    VerifiableFunction {
        name: "gcdF".into(),
        def_path: GCDF_SELF_PATH.into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: 3,
            return_ty: nat_adt(),
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
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
fn with_args(mut body: VerifiableFunction, block: usize, args: Vec<Operand>) -> VerifiableFunction {
    if let Terminator::Call { args: slot, .. } = &mut body.body.blocks[block].terminator {
        *slot = args;
    }
    body
}

/// The KERNEL half, with the MIR recognizer removed from the loop: reflect a
/// (possibly mutated) reading straight to side B and ask the gate.
fn gate_side_b(env: &Environment, body: &WfRecBody) -> Result<(), String> {
    let reflected = trust_clean_origin::reflect_wf::reflect_wf_functional(
        env,
        "gcdF",
        body,
        trust_clean_origin::WfLowering::OnParameter,
    )
    .map_err(|detail| format!("reflection refused: {detail}"))?;
    let plan = plan_clean_origin_body(env, "gcdF").expect("gcdF plans");
    trust_clean_origin::gate::check_faithful_wf_functional(
        env,
        "gcdF",
        &reflected,
        plan.result_carrier(),
    )
    .map(|_| ())
    .map_err(|refusal| format!("gate refused: {}", refusal.note()))
}

fn with_rec_args(args: Vec<RecBodyExpr>) -> WfRecBody {
    WfRecBody { rec_args: args, ..recognised_body() }
}

// ═══════════════════════════════════════════════════════════════════════════
// THE ADMIT
// ═══════════════════════════════════════════════════════════════════════════

/// The whole route, on the general-subtraction shape, against the REAL
/// elaborated side A.
#[test]
fn control_17_the_general_subtraction_emission_admits_end_to_end() {
    let env = gcdf_env();
    assert!(env.get_const(&Name::from_string("Nat.sub")).is_some(), "`Nat.sub` must exist");

    let plan = plan_clean_origin_body(&env, "gcdF").expect("`gcdF` must plan");
    assert_eq!(
        plan.shape(),
        &planned_shape(),
        "zero arm `a`, self-call `(f - 1, (a-b)+(b-a), a-(a-b))` — and the nested `Sub` must \
         be READ, never pre-reduced to a `min` the kernel never saw"
    );
    assert_eq!(plan.signature().arity(), 3);

    let extracted = emitted_gcdf();
    assert_eq!(
        recognize_wf_nat_rec(&extracted),
        Some(recognised_body()),
        "the emitted-and-extracted body must read back as the planned recursion. The \
         predecessor is the ONE `sub` that canonicalises to `Pred`; the other five stay \
         `Sub`, or one MIR position would have two side-B spellings"
    );

    let faithful =
        admit_lowering(&env, &plan, &extracted).expect("the emission must pass the F-layer gate");
    assert_eq!(faithful.name(), "gcdF");
    assert_eq!(faithful.admitted_at(), &Ty::BignumNat);
    assert_eq!(faithful.method(), FaithfulnessMethod::WellFoundedFunctionalDefeq);
    eprintln!("CONTROL-17 admit | gcdF FAITHFUL by WellFoundedFunctionalDefeq");
}

/// The earlier lanes must be UNMOVED by the `-` widening. The shared reader
/// `walk_structural_arm` serves R1 AND R2, so widening it widens both readings
/// and both must be re-measured — this is the R2 baseline, at the shape whose
/// `n - 1` is the one subtraction that still canonicalises to `Pred`.
#[test]
fn control_17_the_predecessor_still_canonicalises() {
    let env = island(
        "def countdownSum (n : Nat) : Nat := \
         if h : 0 < n then n + countdownSum (n - 1) else 0\n\
         termination_by n",
    )
    .expect("elaborates");
    assert_eq!(
        plan_clean_origin_body(&env, "countdownSum").expect("plans").shape(),
        &CleanOriginShape::WellFoundedNatRec {
            zero_value: RecBodyExpr::NatConst(0),
            nonzero_value: add(RecBodyExpr::Decreasing, RecBodyExpr::Rec),
            rec_args: vec![RecBodyExpr::Pred],
            measure_index: 0,
            lowering: trust_clean_origin::WfLowering::OnParameter,
        },
        "`n - 1` at the measure must still read as `Pred` and NOT as \
         `Sub(Decreasing, NatConst(1))` — two spellings for one position is the hazard the \
         canonicalisation exists to close, and it would make the gate's structural equality \
         fail on a correct body"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// THE MUTATIONS — an ADMIT with no refused sibling is not a measurement
// ═══════════════════════════════════════════════════════════════════════════

/// (a) THE WRONG OPERATOR. The emitted body computes `a + b` where side A says
/// `a - b`. This is the row `table.rs`'s `nat.sub` cites: it is the emitter-side
/// twin of `gcd_route_probes` m1's kernel mutation `a - b = Nat.add a b`.
#[test]
fn control_17_a_wrong_operator_is_refused_at_both_layers() {
    let env = gcdf_env();
    let plan = plan_clean_origin_body(&env, "gcdF").expect("plans");

    let refusal = admit_lowering(&env, &plan, &with_callee(emitted_gcdf(), 5, BIGNUM_ADD))
        .expect_err("`add` where the definition says `sub` must never emit");
    assert!(
        matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }),
        "expected the structural catch, got {refusal:?}"
    );
    assert!(refusal.is_compiler_defect(), "a wrong emission is a compiler defect");

    // `mul` too — the other bignum sibling, so this is not measuring "any
    // callee change is caught" via one lucky pair.
    assert!(
        admit_lowering(&env, &plan, &with_callee(emitted_gcdf(), 5, BIGNUM_MUL)).is_err(),
        "`mul` for `sub` must not emit either"
    );

    // The SAME mutation at the KERNEL, with the recognizer removed.
    let wrong = with_rec_args(vec![
        RecBodyExpr::Pred,
        add(add(param(1), param(2)), sub(param(2), param(1))),
        min_ab(),
    ]);
    assert!(
        gate_side_b(&env, &wrong).is_err(),
        "the KERNEL must separate `Nat.add a b` from side A's `HSub.hSub … a b` inside the \
         self-call's threaded argument"
    );
    eprintln!("CONTROL-17 (a) add-for-sub | REFUSED structurally AND at the kernel");
}

/// (b) **THE ROW THAT ONLY EXISTS AT THIS SHAPE: swapped `-` operands.**
///
/// `control_16`'s operand-order row is on `Nat.mul`, whose commutativity is a
/// theorem rather than a definitional identity — true, but delicate: it refutes
/// only because defeq on a stuck `dite` does not apply the theorem.
/// `Nat.sub b a` is not equal to `Nat.sub a b` at ALL, and
/// `gcd_route_probes` m1 measures the kernel refusing exactly that. So this row
/// is a genuine refutation, and it is the one that would catch a reflector or
/// materializer that transposed a binary node's operands.
///
/// It is also the mutation that MATTERS here: swapping `a - b` to `b - a`
/// turns `|a - b|` into itself but `min a b` into something that is not `min`,
/// so an unrefuted swap would emit a function that is not gcd.
#[test]
fn control_17_b_swapped_subtraction_operands_are_refused_at_both_layers() {
    let env = gcdf_env();
    let plan = plan_clean_origin_body(&env, "gcdF").expect("plans");

    // bb5 computes `a - b` as `sub(&_2, &_3)`; hand it `sub(&_3, &_2)`.
    let swapped = with_args(emitted_gcdf(), 5, vec![mv(11), mv(10)]);
    assert!(
        matches!(
            admit_lowering(&env, &plan, &swapped),
            Err(EmitRefusal::LoweringShapeMismatch { .. })
        ),
        "`sub(&b, &a)` where the definition says `sub(&a, &b)` must not emit"
    );

    // The kernel half. Unlike `control_16`'s `Nat.mul` row these two terms are
    // not even equal in VALUE, which is what makes `-` the operator this
    // battery is built around.
    let swapped_reading = with_rec_args(vec![
        RecBodyExpr::Pred,
        add(sub(param(2), param(1)), sub(param(2), param(1))),
        min_ab(),
    ]);
    assert!(
        gate_side_b(&env, &swapped_reading).is_err(),
        "the gate must separate `Nat.sub b a` from `Nat.sub a b`"
    );

    // …and the NESTED one, `a - (a - b)` mutated to `(a - b) - a`, which is the
    // transposition a reader that pre-reduced `min` in Rust would hide.
    let nested =
        with_rec_args(vec![RecBodyExpr::Pred, abs_diff(), sub(sub(param(1), param(2)), param(1))]);
    assert!(
        gate_side_b(&env, &nested).is_err(),
        "the NESTED subtraction's operand order must be decided too — `(a-b)-a` is 0, not \
         `min a b`, and a gate that admitted it would admit a body that is not gcd"
    );
    eprintln!("CONTROL-17 (b) swapped `-` operands | REFUSED (order is decided, twice)");
}

/// (c) **A WRONG THREADED INDEX.** `min a b` is `a - (a - b)`; the mutation
/// emits `b - (a - b)`, one parameter index off. Both operands are parameters
/// of the same carrier, so nothing but the INDEX distinguishes them — which is
/// the fact `r7_arity_widening_probes` q3 pins at the kernel (`sel a b = b`
/// closes, `sel a b = a` is refused).
#[test]
fn control_17_c_a_wrong_threaded_index_is_refused_at_both_layers() {
    let env = gcdf_env();
    let plan = plan_clean_origin_body(&env, "gcdF").expect("plans");

    // bb9 borrows `_2` (`a`) as the minuend of `a - (a - b)`; borrow `_3` (`b`).
    let mut wrong_index = emitted_gcdf();
    wrong_index.body.blocks[9].stmts = vec![borrow(22, 3), borrow(23, 21)];
    assert!(
        matches!(
            admit_lowering(&env, &plan, &wrong_index),
            Err(EmitRefusal::LoweringShapeMismatch { .. })
        ),
        "`b - (a - b)` where the definition says `a - (a - b)` must not emit"
    );

    let wrong_reading =
        with_rec_args(vec![RecBodyExpr::Pred, abs_diff(), sub(param(2), sub(param(1), param(2)))]);
    assert!(
        gate_side_b(&env, &wrong_reading).is_err(),
        "the kernel must decide WHICH parameter the minuend is; the two differ only in a \
         de Bruijn index"
    );
    eprintln!("CONTROL-17 (c) wrong threaded index | REFUSED at both layers");
}

/// (d) **THE SELF-CALL's operands, swapped.** Two flavours, because at arity 3
/// they fail for two different reasons:
///
/// * the two THREADED arguments transposed — `gcdF (f-1) (min a b) |a-b|` —
///   which the recognizer happily reads (it is a well-formed recursion) and
///   only the KERNEL separates;
/// * the measure moved out of position, which the recognizer itself refuses
///   because `rec_args[measure_index]` is no longer the predecessor.
#[test]
fn control_17_d_swapped_self_call_operands_are_refused() {
    let env = gcdf_env();
    let plan = plan_clean_origin_body(&env, "gcdF").expect("plans");

    // THREADED transposition: `gcdF(move _9, move _24, move _18)`.
    let threaded = with_args(emitted_gcdf(), 10, vec![mv(9), mv(24), mv(18)]);
    assert_eq!(
        recognize_wf_nat_rec(&threaded),
        Some(with_rec_args(vec![RecBodyExpr::Pred, min_ab(), abs_diff()])),
        "this mutation is READABLE — it is a well-formed recursion — so the recognizer is \
         not what refuses it, and saying so is the point of the row"
    );
    assert!(
        admit_lowering(&env, &plan, &threaded).is_err(),
        "…and it must still be refused, by the gate: it computes a different function"
    );
    assert!(
        gate_side_b(&env, &with_rec_args(vec![RecBodyExpr::Pred, min_ab(), abs_diff()])).is_err(),
        "the kernel half of the same transposition"
    );

    // MEASURE out of position: `gcdF(move _18, move _9, move _24)`.
    let measure_moved = with_args(emitted_gcdf(), 10, vec![mv(18), mv(9), mv(24)]);
    assert_eq!(
        recognize_wf_nat_rec(&measure_moved),
        None,
        "a self-call whose MEASURE position is not the predecessor is outside the contract"
    );
    assert!(
        matches!(
            admit_lowering(&env, &plan, &measure_moved),
            Err(EmitRefusal::LoweringUnrecognised { .. })
        ),
        "the swapped self-call must not emit"
    );
    eprintln!(
        "CONTROL-17 (d) swapped self-call operands | REFUSED (threaded: gate; measure: reader)"
    );
}

/// (e) **THE GUARD ON THE WRONG PARAMETER.** The emitted zero test decides `a`
/// where side A descends on `f`. `measure_index` is read out of bb0's own
/// borrow, so moving that borrow moves the whole reading — and R3b makes this
/// row sharper than it was, because the predecessor `sub(&_1, &1)` no longer
/// fails to READ under the moved measure (it reads as `Sub(Param(0), 1)`); what
/// refuses it is that `rec_args[measure_index]` is then not `Pred`.
#[test]
fn control_17_e_a_zero_test_on_the_wrong_parameter_is_refused() {
    let env = gcdf_env();
    let plan = plan_clean_origin_body(&env, "gcdF").expect("plans");

    let mut wrong_measure = emitted_gcdf();
    wrong_measure.body.blocks[0].stmts = vec![borrow(4, 2)];
    let read = recognize_wf_nat_rec(&wrong_measure);
    assert!(
        read.as_ref().is_none_or(|body| body.rec_args[body.measure_index] != RecBodyExpr::Pred),
        "a body that tests one parameter and decreases another must never read back as a \
         recursion whose measure argument is the predecessor; got {read:?}"
    );
    assert!(
        admit_lowering(&env, &plan, &wrong_measure).is_err(),
        "a body that tests one parameter and decreases another must not emit"
    );
    eprintln!("CONTROL-17 (e) zero test on the wrong parameter | REFUSED");
}

/// (f) FORGED CALLEES, on both the arithmetic and the self-call.
#[test]
fn control_17_f_forged_callees_are_refused() {
    let env = gcdf_env();
    let plan = plan_clean_origin_body(&env, "gcdF").expect("plans");

    for forged in [
        "my_crate::arith::<impl my_crate::Nat>::sub",
        "evil_bignum::Nat::sub",
        // The SIBLING in the very same `mod arith` impl block, sharing the
        // whole `<impl …>` prefix — and the one whose Rust realization returns
        // `Option` where Lean's `-` is total.
        "trust_bignum::arith::<impl trust_bignum::Nat>::checked_sub",
        "trust_bignum::arith::<impl trust_bignum::Nat>::div",
    ] {
        assert!(
            matches!(
                admit_lowering(&env, &plan, &with_callee(emitted_gcdf(), 5, forged)),
                Err(EmitRefusal::LoweringUnrecognised { .. })
            ),
            "`{forged}` must not authenticate as the runtime's `sub`"
        );
    }
    // …and the one path that LOOKS like a near-miss and is deliberately NOT
    // one. `saturating_sub` authenticates as `NatSub`, and this row records
    // that it was VERIFIED rather than assumed: `trust-bignum`'s
    // `saturating_sub` is `self.sub(other)` verbatim (arith.rs:81), and `sub`
    // is `checked_sub(..).unwrap_or(ZERO)` — which is exactly the truncation
    // `gcd_route_probes` m1 measured at the kernel (`1 - 3 = 0` ADMITS,
    // `1 - 3 = 1` REFUSED). On ℕ, saturating-at-zero and Lean's `Nat.sub` are
    // one function, so accepting both spellings is an alias, not a hole. If
    // `saturating_sub` ever stops being literally `sub`, this row fails and the
    // classifier must lose the alias.
    assert!(
        admit_lowering(
            &env,
            &plan,
            &with_callee(
                emitted_gcdf(),
                5,
                "trust_bignum::arith::<impl trust_bignum::Nat>::saturating_sub"
            ),
        )
        .is_ok(),
        "`saturating_sub` is a documented alias of `sub` in trust-bignum and must keep \
         authenticating — if this refuses, the alias was removed and the classifier's row \
         is now describing a function that does not exist"
    );
    for forged in ["clean_origin_wf_rec_gcd::gcdFish", "other_crate::gcdF"] {
        assert!(
            matches!(
                admit_lowering(&env, &plan, &with_callee(emitted_gcdf(), 10, forged)),
                Err(EmitRefusal::LoweringUnrecognised { .. })
            ),
            "`{forged}` must not authenticate as `gcdF`'s own self-call"
        );
    }
    eprintln!("CONTROL-17 (f) forged callees | 6 near-misses REFUSED");
}

/// (g) **THE ADVERSARIAL ROW THE REFINED DUPLICATION RULE MUST KEEP REFUSING.**
///
/// R3b replaced "no parameter twice in one branch" with a MOVE-aware rule,
/// because the old one refused `gcdF` (which names `a` four times, all
/// borrows). The one shape that must stay refused is a parameter handed to the
/// self-call BY ITSELF — the emitter's only move of a parameter's own local —
/// and used again in the same branch:
///
/// ```text
/// def scale (a b : Nat) : Nat := if h : 0 < a then b + scale (a - 1) b else 0
/// ```
///
/// `gcd_route_probes` m5 measured the MIR this would emit —
/// `SELF(move _9, move _2) -> _10` followed by `_11 = &_2` — a borrow of a
/// local the call has already moved. **The MIR reader ACCEPTS that body**, so
/// this plan rule is the only guard, and this row is the reason the refinement
/// had to be exact rather than a deletion.
///
/// Failing mutation: drop the `moved` condition from the rule (i.e. refuse only
/// on `uses > 1`, or accept everything). The first refuses `gcdF` and the admit
/// above fails; the second admits `scale` and this row fails.
#[test]
fn control_17_g_a_moved_parameter_used_twice_is_still_refused() {
    let env = island(
        "def scale (a b : Nat) : Nat := if h : 0 < a then b + scale (a - 1) b else 0\n\
         termination_by a",
    )
    .expect("`scale` must elaborate — the refusal has to be THIS compiler's, not clean's");

    let refusal = plan_clean_origin_body(&env, "scale").expect_err(
        "a parameter that is both moved into the self-call and borrowed after it \
                     has no emission",
    );
    assert!(!refusal.is_compiler_defect(), "a fragment boundary is a capability refusal");
    assert!(
        refusal.note().contains("BY ITSELF"),
        "the refusal must name the MOVE, not a use count — a user told 'you used `b` twice' \
         would go and bind it once, which does not help. got: {}",
        refusal.note()
    );
    // v7/D3: the refusal carries the fix, with options.
    assert!(
        refusal.note().contains("+ 0"),
        "…and must carry an actionable way out: {}",
        refusal.note()
    );
    eprintln!("CONTROL-17 (g) moved-then-borrowed parameter | REFUSED, with the fix");
}

/// (h) The honest pair to (g): the repetition that is now ADMITTED, stated as a
/// fact about the emission rather than a hope. Four uses of `a` and three of
/// `b` in one branch, every one a shared borrow.
#[test]
fn control_17_h_repeated_parameters_are_admitted_and_are_all_borrows() {
    let env = gcdf_env();
    let plan = plan_clean_origin_body(&env, "gcdF").expect("`gcdF` must plan");
    let CleanOriginShape::WellFoundedNatRec { rec_args, .. } = plan.shape() else {
        panic!("gcdF is a well-founded recursion");
    };
    let uses = |index: usize| -> usize {
        rec_args.iter().map(|argument| argument.parameter_uses(index, 0)).sum()
    };
    assert_eq!((uses(1), uses(2)), (4, 3), "the shape this row is about");

    // …and the emitted body moves NO parameter: every operand of the self-call
    // is a temp, and every appearance of `_2`/`_3` is a `&`.
    let body = emitted_gcdf();
    let Terminator::Call { args, .. } = &body.body.blocks[10].terminator else {
        panic!("bb10 is the self-call");
    };
    for operand in args {
        let Operand::Move(place) = operand else { panic!("self-call operands are moves") };
        assert!(
            place.local > 3,
            "the self-call must move only TEMPS — moving a parameter local (_1.._3) is the \
             borrow-after-move hazard row (g) is about, and it would be emitted here"
        );
    }
    for block in &body.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue: Rvalue::Use(Operand::Move(place)), .. } = stmt {
                assert!(
                    place.local != 1 && place.local != 3,
                    "only the zero arm's root may move a parameter, and it moves `_2`"
                );
            }
        }
    }
    eprintln!("CONTROL-17 (h) repeated parameters | ADMITTED, and every use is a borrow");
}
