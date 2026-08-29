// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 10 — THE GENERAL-SELECT EMITTER MUTATION FIXTURE (§6f landing
//! 3).**
//!
//! `control_3` covers Projection, `control_5` WrappingBinOp, `control_6` the
//! parameter Select, `control_7` SelectLiteral, `control_8` the well-founded
//! recursion and `control_9` the constant body; this is the SAME control for
//! `SelectOperands`, per the standing amendment that every shape lands with its
//! own per-shape mutation control. It is stated explicitly here for the same
//! reason C9's was: this widening touched **side B in two crates** — a new
//! `trust-spec-elab` admit route and a new `trust-types` reader entry point —
//! and that is exactly where a lane whose author wrote both sides goes soft
//! without adversarial controls.
//!
//! The route under test is `admit_general_select_lowering`:
//!
//! ```text
//! emitted body (the 4-block O0 diamond with OPERAND arms)
//!   -> trust_types::recognize_select_general           (side B's reader, SEPARATE entry point)
//!   -> trust_clean_origin::reflect::producer_call_for_general_select   (row selection)
//!   -> trust_spec_elab::admit_select_operands_function (side B, the NEW route)
//!   -> check_faithful                                  (against side A's ite)
//! ```
//!
//! Mutations are injected into the EMITTED body only. Side B is frozen against
//! THIS lane the moment it lands; if a mutant ever passes, the defect is in the
//! emitter or the gate — never here.
//!
//! Side A comes from the REAL island elaborator throughout (`control_7`'s
//! precedent, and landing 3's method): a hand-built side A is a probe fiction,
//! and R2/C9 paid for that lesson once already.

use clean_kernel::Environment;
use trust_clean_origin::table::{MirShape, ladder_row};
use trust_clean_origin::{CleanOriginShape, EmitRefusal, admit_lowering, plan_clean_origin_body};
use trust_types::admissible_body::{
    ArithOperand, SelectCmp, recognize_admissible_body, recognize_select_general,
};
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

/// `def clampz (a b : UInt64) : UInt64 := if a < b then a else 0`, through the
/// pipeline `clean_origin_mir` really drives.
fn env_with_clampz() -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session
        .check_all(&["def clampz (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else 0"]);
    assert!(!batch.is_rejected(), "the island must kernel-check: {batch:?}");
    session.environment().expect("an untainted session has an environment").clone()
}

/// The emitted four-block diamond with OPERAND arms. `cmp`, `cmp_right`,
/// `then_arm` and `else_arm` are the knobs the mutations turn.
fn emitted(
    cmp: BinOp,
    cmp_right: ArithOperand,
    then_arm: ArithOperand,
    else_arm: ArithOperand,
) -> VerifiableFunction {
    emitted_at(64, cmp, cmp_right, then_arm, else_arm)
}

fn emitted_at(
    bits: u32,
    cmp: BinOp,
    cmp_right: ArithOperand,
    then_arm: ArithOperand,
    else_arm: ArithOperand,
) -> VerifiableFunction {
    let ty = Ty::Int { width: bits, signed: false };
    let asn = |p: usize, rv: Rvalue| Statement::Assign {
        place: Place::local(p),
        rvalue: rv,
        span: SourceSpan::default(),
    };
    let operand = |o: ArithOperand| match o {
        ArithOperand::Param(index) => Operand::Copy(Place::local(index + 1)),
        ArithOperand::Const(value) => Operand::Constant(ConstValue::Uint(value, bits)),
    };
    VerifiableFunction {
        name: "clampz".into(),
        def_path: "crate::m::clampz".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: None },
                LocalDecl { index: 2, ty: ty.clone(), name: None },
                LocalDecl { index: 3, ty: ty.clone(), name: None },
                LocalDecl { index: 4, ty: Ty::Bool, name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![asn(
                        4,
                        Rvalue::BinaryOp(cmp, Operand::Copy(Place::local(1)), operand(cmp_right)),
                    )],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(4)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![asn(3, Rvalue::Use(operand(then_arm)))],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![asn(3, Rvalue::Use(operand(else_arm)))],
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
    }
}

/// The faithful emission for `clampz`.
fn faithful() -> VerifiableFunction {
    emitted(BinOp::Lt, ArithOperand::Param(1), ArithOperand::Param(0), ArithOperand::Const(0))
}

// ── the row preflight, on the fast lane ────────────────────────────────────

/// **H-H's obligation for the new rung, discharged here rather than by editing
/// `table_controls`.** The general select maps onto the SAME row the
/// bare-parameter select maps onto, at the same realization — which is the
/// landing's central claim, and the reason no row was added.
#[test]
fn half_0a_the_rung_selects_the_same_row_as_the_narrow_select() {
    let general = ladder_row(&CleanOriginShape::SelectOperands {
        cmp: SelectCmp::Lt,
        cmp_left: 0,
        cmp_right: ArithOperand::Param(1),
        then_arm: ArithOperand::Param(0),
        else_arm: ArithOperand::Const(0),
    })
    .expect("the general select rung must map onto a row");
    let narrow = ladder_row(&CleanOriginShape::Select {
        cmp: SelectCmp::Lt,
        cmp_left: 0,
        cmp_right: 1,
        then_param: 0,
        else_param: 1,
    })
    .expect("the narrow select rung maps onto a row");
    assert_eq!(
        general.name, narrow.name,
        "the two rungs must select ONE row: the kernel head is identical and only the arms \
         differ, and an arm is dataflow. If they ever select different rows, the table has \
         acquired a capability distinction the kernel does not make."
    );
    assert_eq!(
        general.mir,
        MirShape::ComparisonBranch(SelectCmp::Lt),
        "the realization is the same comparison diamond"
    );
    // …and at each comparison, so the mapping is not an accident of `Lt`.
    for (cmp, expected) in
        [(SelectCmp::Lt, "select.lt"), (SelectCmp::Le, "select.le"), (SelectCmp::Eq, "select.eq")]
    {
        let row = ladder_row(&CleanOriginShape::SelectOperands {
            cmp,
            cmp_left: 0,
            cmp_right: ArithOperand::Param(1),
            then_arm: ArithOperand::Const(1),
            else_arm: ArithOperand::Const(0),
        })
        .expect("row");
        assert_eq!(row.name, expected);
    }
}

#[test]
fn half_0b_the_plan_reads_the_const_arm_ite_as_the_exact_general_select() {
    let env = env_with_clampz();
    let plan = plan_clean_origin_body(&env, "clampz").expect("inside the landing 3 fragment");
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::SelectOperands {
            cmp: SelectCmp::Lt,
            cmp_left: 0,
            cmp_right: ArithOperand::Param(1),
            then_arm: ArithOperand::Param(0),
            else_arm: ArithOperand::Const(0),
        }
    );
    assert_eq!(plan.param_tys(), vec![Ty::u64(), Ty::u64()]);
}

#[test]
fn half_1_the_gate_admits_the_faithful_diamond() {
    let env = env_with_clampz();
    let plan = plan_clean_origin_body(&env, "clampz").expect("plan");
    let admitted =
        admit_lowering(&env, &plan, &faithful()).expect("the faithful diamond must admit");
    assert_eq!(admitted.admitted_at(), &Ty::u64());
}

// ── the mutations ──────────────────────────────────────────────────────────

#[test]
fn half_2_the_wrong_arm_constant_is_refused() {
    // THE LANDING-DISTINCTIVE MUTATION: the emitted arm constant off by one —
    // a body that agrees with the declaration on every input whose comparison
    // is TRUE and differs on every other. `l3_p2`'s paired mutation pins that
    // the KERNEL alone refuses it too, so neither layer is load-bearing alone.
    let env = env_with_clampz();
    let plan = plan_clean_origin_body(&env, "clampz").expect("plan");
    let wrong =
        emitted(BinOp::Lt, ArithOperand::Param(1), ArithOperand::Param(0), ArithOperand::Const(1));
    let refusal = admit_lowering(&env, &plan, &wrong)
        .expect_err("a 1-arm emission for a 0-arm declaration must be refused");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");
}

#[test]
fn half_3_swapped_arms_are_refused() {
    // The polarity trap in the arms the widening made ASYMMETRIC: before this
    // landing both arms were parameters and a swap moved an index; now a swap
    // moves a parameter past a constant, which is a different instruction in
    // each block.
    let env = env_with_clampz();
    let plan = plan_clean_origin_body(&env, "clampz").expect("plan");
    let wrong =
        emitted(BinOp::Lt, ArithOperand::Param(1), ArithOperand::Const(0), ArithOperand::Param(0));
    let refusal =
        admit_lowering(&env, &plan, &wrong).expect_err("a swapped-arm emission must be refused");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");
}

#[test]
fn half_4_a_parameter_arm_for_a_constant_arm_is_refused() {
    // The confusion the widening OPENS, and the one the narrow shapes could
    // not even express: the emitter copies a parameter where the declaration
    // says a numeral. The body recognizes fine — as a different value.
    let env = env_with_clampz();
    let plan = plan_clean_origin_body(&env, "clampz").expect("plan");
    let wrong =
        emitted(BinOp::Lt, ArithOperand::Param(1), ArithOperand::Param(0), ArithOperand::Param(1));
    let refusal = admit_lowering(&env, &plan, &wrong)
        .expect_err("a parameter arm for a constant arm must be refused");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");
}

#[test]
fn half_5_the_wrong_comparison_is_refused() {
    // Le for Lt. At a param-vs-param comparison the two differ exactly where
    // the operands are equal — and there the arms differ too, so this is a
    // REAL wrong binary, not an extensional coincidence. Defeq is intensional
    // on the stuck `ite` (probe_h's finding), so the kernel refuses it as well.
    let env = env_with_clampz();
    let plan = plan_clean_origin_body(&env, "clampz").expect("plan");
    let wrong =
        emitted(BinOp::Le, ArithOperand::Param(1), ArithOperand::Param(0), ArithOperand::Const(0));
    let refusal = admit_lowering(&env, &plan, &wrong)
        .expect_err("a Le emission for a Lt declaration must be refused");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");
}

#[test]
fn half_6_a_literal_comparison_emission_is_refused() {
    // The emitter compares `a < 10` where the island says `a < b`: the body
    // recognizes fine — with the wrong comparison operand.
    let env = env_with_clampz();
    let plan = plan_clean_origin_body(&env, "clampz").expect("plan");
    let wrong =
        emitted(BinOp::Lt, ArithOperand::Const(10), ArithOperand::Param(0), ArithOperand::Const(0));
    let refusal = admit_lowering(&env, &plan, &wrong)
        .expect_err("a literal-compare emission for a param-compare declaration must be refused");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");
}

#[test]
fn half_7_the_wrong_carrier_width_is_refused() {
    // Self-consistent u32 emission (locals, return type AND the arm constant's
    // encoded width all agree at u32): recognition and the domain derivation
    // both pass, and the truncation is seen only downstream — the reflected
    // side B mints at the u32 domain and the kernel comparison at the u64
    // result carrier refuses. THE ARM CONSTANT is the new surface here: it
    // carries an encoded width the narrow shapes' parameter arms did not.
    let env = env_with_clampz();
    let plan = plan_clean_origin_body(&env, "clampz").expect("plan");
    let wrong = emitted_at(
        32,
        BinOp::Lt,
        ArithOperand::Param(1),
        ArithOperand::Param(0),
        ArithOperand::Const(0),
    );
    let refusal =
        admit_lowering(&env, &plan, &wrong).expect_err("a truncating emission must be refused");
    assert!(refusal.is_compiler_defect());
    assert!(
        matches!(refusal, EmitRefusal::Gate(trust_clean_origin::GateRefusal::Disagreement { .. })),
        "the width mistake must be caught by the KERNEL comparison: {refusal:?}"
    );
}

#[test]
fn half_8_a_width_skewed_arm_constant_does_not_even_recognize() {
    // The half above emits a SELF-CONSISTENT wrong width. This one skews only
    // the ARM constant's encoded width against the body's own return width —
    // the forgery the new operand position makes possible — and it must fail
    // at side B's READER, before any producer or kernel is reached. That is
    // the same single-width anchor `select_literal_of_operand` applies to a
    // comparison literal, now applied to an arm.
    let mut skewed = faithful();
    let Statement::Assign { rvalue, .. } = &mut skewed.body.blocks[2].stmts[0] else {
        unreachable!("the else arm is an assignment");
    };
    *rvalue = Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32)));
    assert_eq!(
        recognize_select_general(&skewed),
        None,
        "an arm constant at a width the body does not return must not recognize; if it does, \
         the reflection could be minted at a domain the emitted scalar is not at"
    );

    let env = env_with_clampz();
    let plan = plan_clean_origin_body(&env, "clampz").expect("plan");
    let refusal = admit_lowering(&env, &plan, &skewed)
        .expect_err("a width-skewed arm constant must be refused");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringUnrecognised { .. }), "got {refusal:?}");
}

#[test]
fn half_9_a_non_select_body_is_refused_as_unrecognised() {
    // A projection emitted for a general-select plan.
    let env = env_with_clampz();
    let plan = plan_clean_origin_body(&env, "clampz").expect("plan");
    let wrong = VerifiableFunction {
        body: VerifiableBody {
            locals: (0..3).map(|index| LocalDecl { index, ty: Ty::u64(), name: None }).collect(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Move(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u64(),
            datatype_defs: Default::default(),
        },
        ..faithful()
    };
    let refusal = admit_lowering(&env, &plan, &wrong)
        .expect_err("a projection emission for a general-select plan must be refused");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringUnrecognised { .. }), "got {refusal:?}");
}

#[test]
fn half_10_the_wrong_arity_is_refused() {
    // The arity check the shared lane applies, restated on this route: a body
    // over one parameter for a two-parameter declaration. A call site passes
    // the declaration's arity, so an arity disagreement alone must refuse.
    let env = env_with_clampz();
    let plan = plan_clean_origin_body(&env, "clampz").expect("plan");
    let mut wrong = faithful();
    wrong.body.arg_count = 1;
    let refusal =
        admit_lowering(&env, &plan, &wrong).expect_err("an arity disagreement must be refused");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");
}

#[test]
fn half_11_the_e6_import_direction_stays_blind_to_every_mutant() {
    // **THE CONTAINMENT, over the whole mutation set.** The capability this
    // landing added lives outside `recognize_admissible_body`'s chain, which
    // also feeds `trust_certify::clean_island::admit_function_into` — the
    // kernel-import direction where a recognized body becomes a defining
    // equation with NO side A and NO kernel gate. Every const-arm body in this
    // file, faithful or mutant, must read back as `None` there.
    //
    // The converse is checked too: a body whose arms are both PARAMETERS still
    // recognizes through the chain exactly as it did, so the narrowing did not
    // quietly shrink E6 either.
    for (what, body) in [
        ("the faithful diamond", faithful()),
        (
            "the wrong-constant mutant",
            emitted(
                BinOp::Lt,
                ArithOperand::Param(1),
                ArithOperand::Param(0),
                ArithOperand::Const(1),
            ),
        ),
        (
            "the swapped-arm mutant",
            emitted(
                BinOp::Lt,
                ArithOperand::Param(1),
                ArithOperand::Const(0),
                ArithOperand::Param(0),
            ),
        ),
        (
            "both arms constant",
            emitted(
                BinOp::Lt,
                ArithOperand::Param(1),
                ArithOperand::Const(1),
                ArithOperand::Const(0),
            ),
        ),
        (
            "a constant arm under a literal comparison",
            emitted(
                BinOp::Lt,
                ArithOperand::Const(10),
                ArithOperand::Param(0),
                ArithOperand::Const(0),
            ),
        ),
    ] {
        assert!(
            recognize_select_general(&body).is_some(),
            "{what}: the general reader must see it"
        );
        assert_eq!(
            recognize_admissible_body(&body),
            None,
            "{what}: the E6 kernel-import direction must NOT see it. A `Some` here means the \
             landing stopped being CALL-only and widened what can become a defining equation \
             with no side A and no gate."
        );
    }

    // The narrowing did not shrink E6: a parameter-armed diamond still reads.
    let params =
        emitted(BinOp::Lt, ArithOperand::Param(1), ArithOperand::Param(0), ArithOperand::Param(1));
    assert!(
        recognize_admissible_body(&params).is_some(),
        "a bare-parameter select must still recognize through the chain; the general reader \
         is a widening of the CALL lane, never a narrowing of the import lane"
    );
}
