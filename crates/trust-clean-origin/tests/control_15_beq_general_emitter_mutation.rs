// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 15 — THE GENERAL `==` SELECT EMITTER MUTATION FIXTURE
//! (§6f landing 8).**
//!
//! `control_3` covers Projection, `control_5` WrappingBinOp, `control_6` the
//! parameter Select, `control_7` SelectLiteral and the structural recursion,
//! `control_8` the well-founded one, `control_9` the constant body,
//! `control_10` the general select and `control_13` the `==` one; this is the
//! SAME control for `SelectBeqGeneral`, per the standing amendment that every
//! shape lands with its own per-shape mutation control.
//!
//! # WHY THIS ONE IS STATED SEPARATELY FROM `control_13`
//!
//! Landing 8 widens the two-step diamond in the two places where a mistake is a
//! WRONG BINARY rather than a refusal, and they are different kinds of mistake:
//!
//! * **THE POLARITY.** The lift's constant is now `false` for
//!   `(a == b) = false`. Every arm, index, width and target stays right while
//!   the emitted body computes the COMPLEMENTARY function, and `l8_p2`
//!   measured that the kernel refuses `rfl` even between `(a == b) = false`
//!   with swapped arms and plain `==` — two terms that compute the same thing.
//!   So the polarity is decided by the kernel and only if the constant reaches
//!   it intact.
//! * **THE COMPUTED OPERAND.** A raw-binop statement now sits at the head of
//!   the entry block. It can be dropped, re-pointed at the wrong temp, given
//!   the wrong operator, left dead, or handed a divisor that PANICS where the
//!   Clean declaration is TOTAL — which is landing 7's soundness boundary, in a
//!   new position.
//!
//! The route under test is `admit_beq_general_select_lowering`:
//!
//! ```text
//! emitted body (the two-step diamond + computed operands)
//!   -> trust_types::recognize_select_beq_general              (side B's reader, SEPARATE entry point)
//!   -> trust_clean_origin::reflect::producer_call_for_beq_general_select
//!   -> trust_spec_elab::admit_select_beq_operands_function    (side B's producer, beside four)
//!   -> check_faithful                                         (against side A's ite)
//! ```
//!
//! Mutations are injected into the EMITTED body only. Side B is frozen against
//! THIS lane the moment it lands; if a mutant ever passes, the defect is in the
//! emitter or the gate — never here. Side A comes from the REAL island
//! elaborator throughout.

use clean_kernel::Environment;
use trust_clean_origin::table::{MirShape, ladder_row};
use trust_clean_origin::{
    CleanOriginPlan, CleanOriginShape, EmitRefusal, admit_lowering, plan_clean_origin_body,
};
use trust_types::admissible_body::{
    ArithOperand, BeqOperand, RawBinOpKind, recognize_admissible_body, recognize_select_beq,
    recognize_select_beq_general, recognize_select_general,
};
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

/// The two fixtures, both through the pipeline `clean_origin_mir` really
/// drives.
///
/// * `cmp`  — `if (a &&& 3) == 0 then a else 0`: the COMPUTED operand, with a
///   constant else-arm on purpose (with one arm a parameter and the other a
///   numeral the two arms are DIFFERENT INSTRUCTIONS, so a swapped
///   `SwitchTargets` is a visibly different body rather than two indices
///   exchanged — `control_10`'s reason, reused).
/// * `neg`  — `if (a == b) = false then a else 0`: the POLARITY.
fn env_with_fixtures() -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&[
        "def cmp (a : UInt64) (b : UInt64) : UInt64 := if (a &&& 3) == 0 then a else 0",
        "def neg (a : UInt64) (b : UInt64) : UInt64 := if (a == b) = false then a else 0",
    ]);
    assert!(!batch.is_rejected(), "the island must kernel-check: {batch:?}");
    session.environment().expect("an untainted session has an environment").clone()
}

fn plan(env: &Environment, name: &str) -> CleanOriginPlan {
    plan_clean_origin_body(env, name)
        .unwrap_or_else(|refusal| panic!("`{name}` must plan: {}", refusal.note()))
}

/// The knobs every mutation turns. The DEFAULT is the faithful emission of the
/// COMPUTED fixture — every field is what `materialize::beq_diamond_body`
/// describes — so each mutant differs from a passing body in exactly one
/// construct and its refusal is attributable to that construct.
struct Emission {
    /// Emit the computed-operand statement at all. Faithful: `true`.
    emit_prefix: bool,
    /// The computed statement's operator. Faithful: `BitAnd`.
    prefix_op: BinOp,
    /// The computed statement's left operand local. Faithful: `1` (`a`).
    prefix_left: usize,
    /// The computed statement's right operand. Faithful: `Const(3)`.
    prefix_right: ArithOperand,
    /// The local the computed statement WRITES. Faithful: `6`.
    prefix_writes: usize,
    /// The DECISION's left operand local. Faithful: `6`, the computed temp.
    decision_left: usize,
    /// The decision's right operand. Faithful: `Const(0)`.
    decision_right: ArithOperand,
    /// The lift's right-hand constant. Faithful: `Bool(true)` for `cmp`.
    lift_constant: ConstValue,
    /// Swap the `SwitchInt`'s two targets. Faithful: `false`.
    swap_targets: bool,
    /// The THEN arm's value. Faithful: `Param(0)`.
    then_arm: ArithOperand,
    /// The ELSE arm's value. Faithful: `Const(0)`.
    else_arm: ArithOperand,
    /// The declared type of the computed temp. Faithful: `u64`.
    prefix_temp_ty: Ty,
}

impl Default for Emission {
    fn default() -> Self {
        Self {
            emit_prefix: true,
            prefix_op: BinOp::BitAnd,
            prefix_left: 1,
            prefix_right: ArithOperand::Const(3),
            prefix_writes: 6,
            decision_left: 6,
            decision_right: ArithOperand::Const(0),
            lift_constant: ConstValue::Bool(true),
            swap_targets: false,
            then_arm: ArithOperand::Param(0),
            else_arm: ArithOperand::Const(0),
            prefix_temp_ty: Ty::Int { width: 64, signed: false },
        }
    }
}

impl Emission {
    /// The faithful emission of the POLARITY fixture: no computed operand, the
    /// decision over the two parameters, the lift against `false`.
    fn negated() -> Self {
        Self {
            emit_prefix: false,
            decision_left: 1,
            decision_right: ArithOperand::Param(1),
            lift_constant: ConstValue::Bool(false),
            ..Self::default()
        }
    }
}

/// The emitted diamond, with `emission`'s knobs applied.
///
/// Locals: `_0` return, `_1`/`_2` the parameters, `_3` the select temp, `_4`
/// the DECISION bool, `_5` the LIFTED bool, `_6` the COMPUTED temp — the layout
/// `materialize::beq_diamond_body` describes, with the computed temporary
/// APPENDED after landing 6's three.
fn emitted(name: &str, emission: &Emission) -> VerifiableFunction {
    let ty = Ty::Int { width: 64, signed: false };
    let asn = |p: usize, rv: Rvalue| Statement::Assign {
        place: Place::local(p),
        rvalue: rv,
        span: SourceSpan::default(),
    };
    let operand = |o: ArithOperand| match o {
        ArithOperand::Param(index) => Operand::Copy(Place::local(index + 1)),
        ArithOperand::Const(value) => Operand::Constant(ConstValue::Uint(value, 64)),
    };
    let mut entry_stmts = Vec::new();
    if emission.emit_prefix {
        entry_stmts.push(asn(
            emission.prefix_writes,
            Rvalue::BinaryOp(
                emission.prefix_op,
                Operand::Copy(Place::local(emission.prefix_left)),
                operand(emission.prefix_right),
            ),
        ));
    }
    entry_stmts.push(asn(
        4,
        Rvalue::BinaryOp(
            BinOp::Eq,
            Operand::Copy(Place::local(emission.decision_left)),
            operand(emission.decision_right),
        ),
    ));
    entry_stmts.push(asn(
        5,
        Rvalue::BinaryOp(
            BinOp::Eq,
            Operand::Copy(Place::local(4)),
            Operand::Constant(emission.lift_constant.clone()),
        ),
    ));
    let (zero_target, otherwise) =
        if emission.swap_targets { (BlockId(1), BlockId(2)) } else { (BlockId(2), BlockId(1)) };
    VerifiableFunction {
        name: name.into(),
        def_path: format!("crate::m::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: None },
                LocalDecl { index: 2, ty: ty.clone(), name: None },
                LocalDecl { index: 3, ty: ty.clone(), name: None },
                LocalDecl { index: 4, ty: Ty::Bool, name: None },
                LocalDecl { index: 5, ty: Ty::Bool, name: None },
                LocalDecl { index: 6, ty: emission.prefix_temp_ty.clone(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: entry_stmts,
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(5)),
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
fn refused(env: &Environment, def: &str, emission: &Emission, what: &str) -> EmitRefusal {
    let body = emitted(def, emission);
    match admit_lowering(env, &plan(env, def), &body) {
        Ok(token) => panic!(
            "the `{what}` mutant was ADMITTED (got {token:?}); a one-construct-wrong emission \
             must be refused, or the ADMITs in half_0 are measuring a gate that admits everything"
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

// ── half_0 — the FAITHFUL emissions admit ───────────────────────────────────

/// The control every mutation below is a mutation OF. Without it the file
/// proves only that a gate refuses things.
#[test]
fn half_0_both_faithful_general_emissions_admit() {
    let env = env_with_fixtures();

    let computed = plan(&env, "cmp");
    assert_eq!(
        computed.shape(),
        &CleanOriginShape::SelectBeqGeneral {
            scrutinee: true,
            cmp_left: BeqOperand::RawBin {
                op: RawBinOpKind::BitAnd,
                left: ArithOperand::Param(0),
                right: ArithOperand::Const(3),
            },
            cmp_right: BeqOperand::Const(0),
            then_arm: ArithOperand::Param(0),
            else_arm: ArithOperand::Const(0),
        }
    );
    // THE ROW DID NOT MOVE — landing 8 widens an operand vocabulary and a
    // polarity, both of which side B reads out of the bytes; the realization is
    // still the one landing 6 built and still realized by exactly one row.
    assert_eq!(ladder_row(computed.shape()).expect("row").name, "select.beq");
    assert_eq!(ladder_row(computed.shape()).expect("row").mir, MirShape::BoolDecisionBranch);
    admit_lowering(&env, &computed, &emitted("cmp", &Emission::default()))
        .expect("the faithful computed-operand emission must ADMIT");

    let negated = plan(&env, "neg");
    assert_eq!(
        negated.shape(),
        &CleanOriginShape::SelectBeqGeneral {
            scrutinee: false,
            cmp_left: BeqOperand::Param(0),
            cmp_right: BeqOperand::Param(1),
            then_arm: ArithOperand::Param(0),
            else_arm: ArithOperand::Const(0),
        }
    );
    admit_lowering(&env, &negated, &emitted("neg", &Emission::negated()))
        .expect("the faithful `= false` emission must ADMIT");
}

// ── half_1 — THE POLARITY IS NOT FLIPPABLE ──────────────────────────────────

/// **The mutation this file exists for, and the one with no arithmetic tell.**
///
/// `const false` for `const true` (and the converse) emits the COMPLEMENTARY
/// function with every arm, index, width and target still correct. It is
/// well-typed MIR that runs. The only thing between it and a shipped wrong
/// binary is that side B reads the constant and the kernel decides the term.
///
/// Both directions, because a control that only tested one would leave the
/// other lane's polarity unmeasured.
#[test]
fn half_1_the_lift_polarity_cannot_be_flipped_in_either_direction() {
    let env = env_with_fixtures();

    // `cmp` is planned with a `true` lift; emit `false`.
    refused(
        &env,
        "cmp",
        &Emission { lift_constant: ConstValue::Bool(false), ..Emission::default() },
        "`const false` where the declaration lifts against `true`",
    );

    // `neg` is planned with a `false` lift; emit `true`.
    refused(
        &env,
        "neg",
        &Emission { lift_constant: ConstValue::Bool(true), ..Emission::negated() },
        "`const true` where the declaration lifts against `false`",
    );

    // AND THE COMPENSATED SPELLING, which is the insidious one: flip the
    // polarity AND swap the arms, so the body computes exactly what the
    // declaration says. `l8_p2` measured the kernel refusing `rfl` between
    // those two terms; this is the same fact reached through the emitter.
    refused(
        &env,
        "neg",
        &Emission {
            lift_constant: ConstValue::Bool(true),
            then_arm: ArithOperand::Const(0),
            else_arm: ArithOperand::Param(0),
            ..Emission::negated()
        },
        "the polarity flipped AND the arms swapped — the SAME function, a different term",
    );

    // …and the `SwitchInt` flip, which is the other way to express a negation
    // without emitting one. Landing 6 refused it in advance; this measures it.
    refused(
        &env,
        "neg",
        &Emission {
            lift_constant: ConstValue::Bool(true),
            swap_targets: true,
            ..Emission::negated()
        },
        "the polarity expressed by swapping the `SwitchInt` targets",
    );
}

// ── half_2 — THE COMPUTED STATEMENT IS NOT REMOVABLE OR RE-POINTABLE ────────

/// The computed operand's statement is the only thing that makes the decision's
/// left operand what the declaration says it is. Five ways to lose it, all
/// refused.
#[test]
fn half_2_the_computed_statement_is_load_bearing() {
    let env = env_with_fixtures();

    // 1. DELETED, with the decision reading the parameter directly — i.e. the
    //    body for `if a == 0`, which is a different declaration.
    let refusal = refused(
        &env,
        "cmp",
        &Emission { emit_prefix: false, decision_left: 1, ..Emission::default() },
        "the computed statement deleted",
    );
    assert!(
        matches!(refusal, EmitRefusal::LoweringUnrecognised { .. }),
        "a body with no computed statement is not this shape at all: {refusal:?}"
    );

    // 2. EMITTED BUT DEAD — the decision reads the parameter while the computed
    //    temp sits there unused. Computationally identical to (1), and the more
    //    insidious spelling because the statement is still visible.
    refused(
        &env,
        "cmp",
        &Emission { decision_left: 1, ..Emission::default() },
        "the computed statement bypassed",
    );

    // 3. THE WRONG OPERATOR — `|` for `&`. Same shape, same locals, a different
    //    function.
    refused(
        &env,
        "cmp",
        &Emission { prefix_op: BinOp::BitOr, ..Emission::default() },
        "`|` for `&` in the computed operand",
    );

    // 4. THE WRONG LEAF — parameter `b` for parameter `a`.
    refused(
        &env,
        "cmp",
        &Emission { prefix_left: 2, ..Emission::default() },
        "the computed operand reads the wrong parameter",
    );

    // 5. THE WRONG NUMERAL — `2` for `3`, off by one and invisible in the
    //    shape.
    refused(
        &env,
        "cmp",
        &Emission { prefix_right: ArithOperand::Const(2), ..Emission::default() },
        "an off-by-one numeral in the computed operand",
    );
}

// ── half_3 — THE COMPUTED TEMP'S IDENTITY AND TYPE ──────────────────────────

/// A temporary the decision does not read, and a temporary at the wrong type.
///
/// The first is what a peephole pass produces when it re-numbers locals badly;
/// the second is what an emitter produces when it takes the type from the wrong
/// place. Both are refused by the READER, which is the strong form.
#[test]
fn half_3_the_computed_temp_must_be_the_one_the_decision_reads() {
    let env = env_with_fixtures();

    // The statement writes `_3` — the SELECT TEMP — while the decision still
    // reads `_6`. That clobbers the arm's destination and reads an undefined
    // local, and the reader must not need the type checker to have noticed.
    let refusal = refused(
        &env,
        "cmp",
        &Emission { prefix_writes: 3, ..Emission::default() },
        "the computed statement writes the select temp",
    );
    assert!(
        matches!(refusal, EmitRefusal::LoweringUnrecognised { .. }),
        "a computed statement that writes a live local is not this shape: {refusal:?}"
    );

    // The computed temp declared at `bool`. Its value is a carrier value and
    // the width anchor is what side B reads the leaves against.
    refused(
        &env,
        "cmp",
        &Emission { prefix_temp_ty: Ty::Bool, ..Emission::default() },
        "the computed temp declared at `bool`",
    );

    // The computed temp declared at the WRONG WIDTH — u32 in a u64 body.
    refused(
        &env,
        "cmp",
        &Emission { prefix_temp_ty: Ty::Int { width: 32, signed: false }, ..Emission::default() },
        "the computed temp declared at u32 in a u64 body",
    );
}

// ── half_4 — THE ARMS AND THE TARGETS, UNDER BOTH POLARITIES ────────────────

/// The arm and target mutations `control_13` runs against the `true` lift, run
/// again against the `false` one — because a polarity lane is exactly where an
/// arm mistake stops being visible by inspection.
#[test]
fn half_4_the_arms_and_targets_are_refused_under_the_false_polarity() {
    let env = env_with_fixtures();

    refused(
        &env,
        "neg",
        &Emission {
            then_arm: ArithOperand::Const(0),
            else_arm: ArithOperand::Param(0),
            ..Emission::negated()
        },
        "the arms swapped under a `false` lift",
    );
    refused(
        &env,
        "neg",
        &Emission { swap_targets: true, ..Emission::negated() },
        "the `SwitchInt` targets swapped under a `false` lift",
    );
    refused(
        &env,
        "neg",
        &Emission { then_arm: ArithOperand::Param(1), ..Emission::negated() },
        "the wrong parameter in the then-arm under a `false` lift",
    );
    refused(
        &env,
        "cmp",
        &Emission { swap_targets: true, ..Emission::default() },
        "the `SwitchInt` targets swapped under a computed operand",
    );
}

// ── half_5 — THE DECISION'S OWN RIGHT OPERAND ───────────────────────────────

/// The computed operand widening must not have loosened the positions that were
/// already tight.
#[test]
fn half_5_the_decisions_right_operand_is_still_exact() {
    let env = env_with_fixtures();
    refused(
        &env,
        "cmp",
        &Emission { decision_right: ArithOperand::Const(1), ..Emission::default() },
        "an off-by-one numeral on the decision's right",
    );
    refused(
        &env,
        "cmp",
        &Emission { decision_right: ArithOperand::Param(1), ..Emission::default() },
        "a parameter where the declaration compares against a numeral",
    );
}

// ── half_6 — E6 CONTAINMENT, on the MUTANTS as well ─────────────────────────

/// `l8_p5` measures containment on the FAITHFUL bodies. This measures it on the
/// mutants too, because a body that fails this lane's gate must not become
/// importable through the gate-free E6 direction as a consolation prize.
#[test]
fn half_6_no_general_beq_body_faithful_or_mutant_enters_the_e6_chain() {
    // `general` says whether the body IS a general one — a computed operand or
    // a `false` lift. The last row deliberately is NOT: emitting `const true`
    // for a `= false` declaration produces a body that IS a well-formed landing
    // 6 `==` body, for the WRONG declaration. `recognize_select_beq` reading it
    // is correct and is what makes half_1's refusal a KERNEL verdict rather
    // than a reader accident; asserting otherwise here would have been a
    // control demanding the wrong thing.
    let mutants = [
        ("cmp", Emission::default(), true),
        ("cmp", Emission { prefix_op: BinOp::BitOr, ..Emission::default() }, true),
        ("cmp", Emission { decision_left: 1, ..Emission::default() }, true),
        ("neg", Emission::negated(), true),
        ("neg", Emission { lift_constant: ConstValue::Bool(true), ..Emission::negated() }, false),
    ];
    for (def, emission, general) in &mutants {
        let body = emitted(def, emission);
        assert!(
            recognize_admissible_body(&body).is_none(),
            "`{def}`: a two-step diamond must never read back through the E6 chain, where a \
             recognized body becomes a defining equation with NO side A and NO gate"
        );
        assert!(
            recognize_select_general(&body).is_none(),
            "`{def}`: the ONE-step select reader must decline it"
        );
        if *general {
            assert!(
                recognize_select_beq(&body).is_none(),
                "`{def}`: landing 6's NARROW reader must decline a general body — that \
                 disjointness is what keeps one emitted body from having two readings"
            );
        } else {
            assert!(
                recognize_select_beq(&body).is_some(),
                "`{def}`: a `true`-lifted leaf-operand body IS landing 6's shape, and the \
                 narrow reader reading it is what makes half_1's refusal a KERNEL verdict \
                 (the body is well formed; it is for a different declaration)"
            );
            assert!(
                recognize_select_beq_general(&body).is_none(),
                "`{def}`: …and the general reader must decline it, so the two readers never \
                 both claim one body"
            );
        }
    }
    // …and the general reader DOES read the faithful ones, so the assertions
    // above are containment rather than a body nothing can read.
    assert!(recognize_select_beq_general(&emitted("cmp", &Emission::default())).is_some());
    assert!(recognize_select_beq_general(&emitted("neg", &Emission::negated())).is_some());
}
