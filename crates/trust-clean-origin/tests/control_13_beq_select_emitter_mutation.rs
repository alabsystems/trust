// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 13 — THE `==` SELECT EMITTER MUTATION FIXTURE (§6f landing 6).**
//!
//! `control_3` covers Projection, `control_5` WrappingBinOp, `control_6` the
//! parameter Select, `control_7` SelectLiteral and the structural recursion,
//! `control_8` the well-founded one, `control_9` the constant body and
//! `control_10` the general select; this is the SAME control for `SelectBeq`,
//! per the standing amendment that every shape lands with its own per-shape
//! mutation control.
//!
//! It is stated explicitly here for a reason narrower than C10's, and worth
//! naming: this landing's shape is the FIRST whose emitted body carries an
//! instruction that is not needed to compute the value. `_c = Eq(_d, const
//! true)` is a no-op arithmetically — `_d` already IS the branch condition —
//! and its entire job is to make the emitted bytes DETERMINE which of two
//! kernel terms the body is for. An instruction whose only purpose is
//! discrimination is exactly the instruction a future "simplification" deletes,
//! and deleting it does not change what the program computes. So the mutations
//! below concentrate on it: dropped, negated, mistyped, read from the wrong
//! local, and branched around.
//!
//! The route under test is `admit_beq_select_lowering`:
//!
//! ```text
//! emitted body (the TWO-STEP diamond)
//!   -> trust_types::recognize_select_beq                 (side B's reader, SEPARATE entry point)
//!   -> trust_clean_origin::reflect::producer_call_for_beq_select   (row selection)
//!   -> trust_spec_elab::admit_select_beq_function        (side B's producer, landing 5)
//!   -> check_faithful                                    (against side A's ite)
//! ```
//!
//! Mutations are injected into the EMITTED body only. Side B is frozen against
//! THIS lane the moment it lands; if a mutant ever passes, the defect is in the
//! emitter or the gate — never here.
//!
//! Side A comes from the REAL island elaborator throughout (`control_7`'s
//! precedent, and landings 3/5/6's method): a hand-built side A is a probe
//! fiction, and R2/C9 paid for that lesson once already.

use clean_kernel::Environment;
use trust_clean_origin::table::{MirShape, ladder_row};
use trust_clean_origin::{CleanOriginShape, EmitRefusal, admit_lowering, plan_clean_origin_body};
use trust_types::admissible_body::{
    ArithOperand, recognize_admissible_body, recognize_select_beq, recognize_select_general,
};
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

/// `def eqz (a b : UInt64) : UInt64 := if a == b then a else 0`, through the
/// pipeline `clean_origin_mir` really drives. A CONSTANT else-arm, on purpose:
/// with one arm a parameter and the other a numeral the two arms are DIFFERENT
/// INSTRUCTIONS, so a swapped `SwitchTargets` is a visibly different body
/// rather than two indices exchanged.
fn env_with_eqz() -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session
        .check_all(&["def eqz (a : UInt64) (b : UInt64) : UInt64 := if a == b then a else 0"]);
    assert!(!batch.is_rejected(), "the island must kernel-check: {batch:?}");
    session.environment().expect("an untainted session has an environment").clone()
}

fn plan(env: &Environment) -> trust_clean_origin::CleanOriginPlan {
    plan_clean_origin_body(env, "eqz").expect("`if a == b then a else 0` plans since landing 6")
}

/// The knobs every mutation turns. The DEFAULT is the faithful emission — every
/// field is what `materialize::beq_diamond_body` describes — so each mutant
/// differs from a passing body in exactly one construct and its refusal is
/// attributable to that construct.
struct Emission {
    /// The DECISION's comparison. Faithful: `Eq`.
    decision_op: BinOp,
    /// The decision's left operand local. Faithful: `1` (parameter `a`).
    decision_left: usize,
    /// The decision's right operand. Faithful: `Param(1)` (parameter `b`).
    decision_right: ArithOperand,
    /// Emit the `= Bool.true` LIFT at all. Faithful: `true`.
    emit_lift: bool,
    /// The lift's right-hand constant. Faithful: `Bool(true)`.
    lift_constant: ConstValue,
    /// The local the lift READS. Faithful: the decision temp, `4`.
    lift_reads: usize,
    /// The local the `SwitchInt` reads. Faithful: the lifted temp, `5`.
    switch_reads: usize,
    /// Swap the `SwitchInt`'s two targets. Faithful: `false`.
    swap_targets: bool,
    /// The THEN arm's value. Faithful: `Param(0)`.
    then_arm: ArithOperand,
    /// The ELSE arm's value. Faithful: `Const(0)`.
    else_arm: ArithOperand,
    /// The encoded width of an arm/comparison numeral. Faithful: `64`.
    numeral_width: u32,
}

impl Default for Emission {
    fn default() -> Self {
        Self {
            decision_op: BinOp::Eq,
            decision_left: 1,
            decision_right: ArithOperand::Param(1),
            emit_lift: true,
            lift_constant: ConstValue::Bool(true),
            lift_reads: 4,
            switch_reads: 5,
            swap_targets: false,
            then_arm: ArithOperand::Param(0),
            else_arm: ArithOperand::Const(0),
            numeral_width: 64,
        }
    }
}

/// The emitted TWO-STEP diamond, with `emission`'s knobs applied.
///
/// Locals: `_0` return, `_1`/`_2` the parameters, `_3` the select temp, `_4`
/// the DECISION bool, `_5` the LIFTED bool — the layout
/// `materialize::beq_diamond_body` describes.
fn emitted(emission: &Emission) -> VerifiableFunction {
    let ty = Ty::Int { width: 64, signed: false };
    let asn = |p: usize, rv: Rvalue| Statement::Assign {
        place: Place::local(p),
        rvalue: rv,
        span: SourceSpan::default(),
    };
    let operand = |o: ArithOperand| match o {
        ArithOperand::Param(index) => Operand::Copy(Place::local(index + 1)),
        ArithOperand::Const(value) => {
            Operand::Constant(ConstValue::Uint(value, emission.numeral_width))
        }
    };
    let mut entry_stmts = vec![asn(
        4,
        Rvalue::BinaryOp(
            emission.decision_op,
            Operand::Copy(Place::local(emission.decision_left)),
            operand(emission.decision_right),
        ),
    )];
    if emission.emit_lift {
        entry_stmts.push(asn(
            5,
            Rvalue::BinaryOp(
                BinOp::Eq,
                Operand::Copy(Place::local(emission.lift_reads)),
                Operand::Constant(emission.lift_constant.clone()),
            ),
        ));
    }
    let (zero_target, otherwise) =
        if emission.swap_targets { (BlockId(1), BlockId(2)) } else { (BlockId(2), BlockId(1)) };
    VerifiableFunction {
        name: "eqz".into(),
        def_path: "crate::m::eqz".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: None },
                LocalDecl { index: 2, ty: ty.clone(), name: None },
                LocalDecl { index: 3, ty: ty.clone(), name: None },
                LocalDecl { index: 4, ty: Ty::Bool, name: None },
                LocalDecl { index: 5, ty: Ty::Bool, name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: entry_stmts,
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(emission.switch_reads)),
                        targets: vec![(0, zero_target)],
                        otherwise,
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![asn(3, Rvalue::Use(operand(emission.then_arm)))],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![asn(3, Rvalue::Use(operand(emission.else_arm)))],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![asn(0, Rvalue::Use(Operand::Copy(Place::local(3))))],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: ty,
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// Assert the whole route REFUSES a mutant, naming the mutation. A refusal that
/// passes anonymously measures nothing.
fn refused(env: &Environment, emission: &Emission, what: &str) -> EmitRefusal {
    let body = emitted(emission);
    match admit_lowering(env, &plan(env), &body) {
        Ok(token) => panic!(
            "the `{what}` mutant was ADMITTED (got {token:?}); a one-construct-wrong emission \
             must be refused, or the ADMIT in half_0 is measuring a gate that admits everything"
        ),
        Err(refusal) => {
            assert!(
                !matches!(refusal, EmitRefusal::NoTotalCarrier { .. }),
                "`{what}`: the refusal must be about the BODY, not the carrier: {refusal:?}"
            );
            refusal
        }
    }
}

// ── half_0 — the FAITHFUL emission admits ───────────────────────────────────

/// The control every mutation below is a mutation OF. Without it the file
/// proves only that a gate refuses things.
#[test]
fn half_0_the_faithful_two_step_emission_admits() {
    let env = env_with_eqz();
    let plan = plan(&env);
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::SelectBeq {
            cmp_left: 0,
            cmp_right: ArithOperand::Param(1),
            then_arm: ArithOperand::Param(0),
            else_arm: ArithOperand::Const(0),
        }
    );
    assert_eq!(ladder_row(plan.shape()).expect("row").mir, MirShape::BoolDecisionBranch);
    admit_lowering(&env, &plan, &emitted(&Emission::default()))
        .expect("the faithful two-step emission must ADMIT");
}

// ── half_1 — THE LIFT IS NOT REMOVABLE ──────────────────────────────────────

/// **The mutation this file exists for.**
///
/// `_c = Eq(_d, const true)` computes nothing: `_d` is already the branch
/// condition, and a body that branches on `_d` directly runs the same program.
/// That is precisely why it is the instruction a future simplification deletes
/// — and deleting it turns the emitted body back into the ONE-step diamond,
/// which denotes `a = b` and not `a == b`. Landing 5 measured that the kernel
/// distinguishes those two and refuses `rfl` between them, so a deleted lift is
/// a body gated against the wrong declaration.
///
/// Three ways to lose it, all refused, and all refused BEFORE the kernel by
/// side B's reader — which is the strong form: the body is not a `==` body at
/// all, rather than a `==` body the kernel happens to dislike.
#[test]
fn half_1_the_lift_is_not_removable_by_any_route() {
    let env = env_with_eqz();

    // 1. the lift statement DELETED, and the switch reading the decision —
    //    i.e. exactly the one-step diamond, arrived at by simplification.
    let refusal = refused(
        &env,
        &Emission { emit_lift: false, switch_reads: 4, ..Emission::default() },
        "the lift deleted (the one-step diamond)",
    );
    assert!(
        matches!(refusal, EmitRefusal::LoweringUnrecognised { .. }),
        "a one-step body is not a `==` body and must be refused by the READER: {refusal:?}"
    );

    // 2. the lift EMITTED but BRANCHED AROUND — the switch reads the decision
    //    while the lift sits there dead. Computationally identical to (1), and
    //    the more insidious spelling because the statement is still visible.
    let refusal =
        refused(&env, &Emission { switch_reads: 4, ..Emission::default() }, "the lift bypassed");
    assert!(
        matches!(refusal, EmitRefusal::LoweringUnrecognised { .. }),
        "a body that branches on the DECISION rather than the LIFT is the one-step body \
         wearing a dead statement: {refusal:?}"
    );

    // 3. the lift reading the WRONG LOCAL — `Eq(_1, true)` rather than
    //    `Eq(_d, true)`. Ill-typed in real MIR (a `u64` against a `bool`), and
    //    the reader must not depend on the type checker having caught it.
    let refusal =
        refused(&env, &Emission { lift_reads: 1, ..Emission::default() }, "the lift reads a param");
    assert!(
        matches!(refusal, EmitRefusal::LoweringUnrecognised { .. }),
        "the lift must read the decision temp and nothing else: {refusal:?}"
    );
}

// ── half_2 — THE SCRUTINEE ──────────────────────────────────────────────────

/// **`Bool.false` for `Bool.true` is the COMPLEMENTARY function with every arm,
/// index and width still correct** — the mutation landing 5 named as the one
/// its producer had to refuse at the kernel, here as an EMISSION mutation.
///
/// It is refused by side B's reader (the constant is matched exactly), which is
/// deliberate: `Eq(_d, false)` is well-typed MIR that computes the negation, so
/// there is nothing structurally malformed about it and the only thing standing
/// between it and a wrong binary is that the reader does not accept it.
///
/// A non-boolean constant in that position is refused too, because the reader
/// keys on `ConstValue::Bool` rather than on "a constant".
#[test]
fn half_2_the_scrutinee_is_bool_true_and_nothing_else() {
    let env = env_with_eqz();
    for (constant, what) in [
        (ConstValue::Bool(false), "`Bool.false` for `Bool.true`"),
        (ConstValue::Uint(1, 8), "a one-byte integer for the boolean"),
        (ConstValue::Uint(1, 64), "a u64 one for the boolean"),
    ] {
        let refusal =
            refused(&env, &Emission { lift_constant: constant, ..Emission::default() }, what);
        assert!(
            matches!(refusal, EmitRefusal::LoweringUnrecognised { .. }),
            "`{what}` must be refused by side B's reader: {refusal:?}"
        );
    }
}

// ── half_3 — the DECISION ───────────────────────────────────────────────────

/// The decision itself is still a comparison, and every way of getting it wrong
/// is refused: the wrong comparison, swapped operands, and the wrong parameter.
///
/// The swapped-operand mutant is the interesting one. `a == b` and `b == a`
/// denote the same VALUE for every input — equality is symmetric — so no
/// evaluation could tell them apart; the kernel refuses it anyway, because the
/// two `ite`s are different TERMS and defeq is intensional on a stuck one. That
/// is the same reason the whole landing exists, one layer down.
#[test]
fn half_3_the_decision_is_the_comparison_the_declaration_names() {
    let env = env_with_eqz();

    // The wrong comparison: `<` where the declaration says `==`.
    let refusal =
        refused(&env, &Emission { decision_op: BinOp::Lt, ..Emission::default() }, "`<` for `==`");
    assert!(
        matches!(refusal, EmitRefusal::LoweringUnrecognised { .. }),
        "the `==` reader carries no comparison field at all, so a `<` decision is not this \
         shape: {refusal:?}"
    );

    // Swapped operands — a body that computes the same value, refused by the
    // KERNEL rather than by the reader.
    let refusal = refused(
        &env,
        &Emission {
            decision_left: 2,
            decision_right: ArithOperand::Param(0),
            ..Emission::default()
        },
        "`b == a` for `a == b`",
    );
    assert!(
        matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }),
        "swapped decision operands must be caught by the structural comparison against the \
         plan: {refusal:?}"
    );

    // The right operand as a NUMERAL where the declaration names a parameter.
    let refusal = refused(
        &env,
        &Emission { decision_right: ArithOperand::Const(0), ..Emission::default() },
        "a numeral for the compared parameter",
    );
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "{refusal:?}");
}

// ── half_4 — THE POLARITY TRAP ──────────────────────────────────────────────

/// `SwitchTargets::static_if(v, v_target, otherwise)` puts `v`'s target FIRST.
/// Getting the order wrong emits the ELSE arm where the island wrote THEN,
/// silently — and with one arm a parameter and the other a numeral the two arms
/// are different instructions, so the mutant is a visibly different body rather
/// than two indices exchanged.
///
/// Both spellings of the inversion are injected: swapping the TARGETS, and
/// swapping the ARM VALUES. They produce different bodies and are caught at
/// different layers, which is the point of injecting both.
#[test]
fn half_4_the_switch_polarity_and_the_arms() {
    let env = env_with_eqz();

    let refusal =
        refused(&env, &Emission { swap_targets: true, ..Emission::default() }, "swapped targets");
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "{refusal:?}");

    let refusal = refused(
        &env,
        &Emission {
            then_arm: ArithOperand::Const(0),
            else_arm: ArithOperand::Param(0),
            ..Emission::default()
        },
        "swapped arm values",
    );
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "{refusal:?}");

    // The wrong constant in the else arm — the value mutation, which no
    // structural check about SHAPES would catch on its own.
    let refusal = refused(
        &env,
        &Emission { else_arm: ArithOperand::Const(1), ..Emission::default() },
        "the wrong arm constant",
    );
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "{refusal:?}");

    // The wrong PARAMETER in the then arm.
    let refusal = refused(
        &env,
        &Emission { then_arm: ArithOperand::Param(1), ..Emission::default() },
        "the wrong arm parameter",
    );
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "{refusal:?}");
}

// ── half_5 — the WIDTH ANCHOR ───────────────────────────────────────────────

/// A width-skewed arm constant must not recognize at all. The anchor is the
/// emitted body's OWN unsigned return width — the same anchor landing 3 gave
/// the general select — so a `0_u32` arm in a `u64` body is not a narrower
/// value, it is not this shape.
#[test]
fn half_5_a_width_skewed_arm_constant_does_not_recognize() {
    let env = env_with_eqz();
    let refusal = refused(
        &env,
        &Emission { numeral_width: 32, ..Emission::default() },
        "a u32-encoded arm constant in a u64 body",
    );
    assert!(
        matches!(refusal, EmitRefusal::LoweringUnrecognised { .. }),
        "a width-skewed constant must fail the READER, not merely the kernel: {refusal:?}"
    );
}

// ── half_6 — the E6 containment, for the mutants too ────────────────────────

/// The gate-free kernel-import direction must be blind to this shape whether
/// the body is faithful or mutant. A reader widening that let a MUTANT through
/// `recognize_admissible_body` would be worse than one that let the faithful
/// body through: it would import a defining equation with no side A, no kernel
/// gate, and a wrong value.
#[test]
fn half_6_the_import_direction_never_reads_this_shape() {
    let faithful = emitted(&Emission::default());
    assert!(recognize_select_beq(&faithful).is_some(), "the CALL-lane reader reads it");
    for (body, what) in [
        (emitted(&Emission::default()), "the faithful body"),
        (emitted(&Emission { swap_targets: true, ..Emission::default() }), "swapped targets"),
        (
            emitted(&Emission { lift_constant: ConstValue::Bool(false), ..Emission::default() }),
            "the false scrutinee",
        ),
        (
            emitted(&Emission { then_arm: ArithOperand::Const(9), ..Emission::default() }),
            "a wrong arm",
        ),
    ] {
        assert!(
            recognize_admissible_body(&body).is_none(),
            "`{what}` must be invisible to the E6 kernel-import direction"
        );
        assert!(
            recognize_select_general(&body).is_none(),
            "`{what}` must be invisible to the ONE-step CALL-lane reader as well, or the same \
             bytes would have two readings"
        );
    }
}
