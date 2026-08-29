// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 6 — THE SELECT EMITTER MUTATION FIXTURE (R2/C5a).**
//!
//! `control_3` is the Projection emitter mutation control and `control_5` the
//! WrappingBinOp one; this is the SAME control for `Select`, per the standing
//! amendment that every shape lands with its own per-shape mutation control.
//! The route under test is `admit_lowering`'s Select arm:
//!
//! ```text
//! emitted body (the 4-block O0 diamond)
//!   -> trust_types::recognize_admissible_body   (recognize_select, frozen)
//!   -> trust_spec_elab::admit_select_function    (side B)
//!   -> check_faithful                            (against side A's ite)
//! ```
//!
//! Mutations are injected into the EMITTED body only. Side B is frozen; if a
//! mutant ever passes, the defect is in the emitter or the gate — never here.

use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name};
use trust_clean_origin::{CleanOriginShape, EmitRefusal, admit_lowering, plan_clean_origin_body};
use trust_types::admissible_body::SelectCmp;
use trust_types::{
    BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, VerifiableBody, VerifiableFunction,
};

fn uint64() -> Expr {
    Expr::const_(Name::from_string("UInt64"), vec![])
}

/// `def min2_isl (a b : UInt64) : UInt64 := if a < b then a else b`, as the
/// `ite` term `elab_if` mints, FULL-kernel-checked into `with_prelude()`.
fn env_with_min2() -> Environment {
    let mut env = Environment::with_prelude();
    let lt_prop = Expr::apps(
        Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
        [
            uint64(),
            Expr::const_(Name::from_string("instLTUInt64"), vec![]),
            Expr::bvar(1),
            Expr::bvar(0),
        ],
    );
    let dec_inst = Expr::apps(
        Expr::const_(Name::from_string("instDecidableUInt64Lt"), vec![]),
        [Expr::bvar(1), Expr::bvar(0)],
    );
    let ite_body = Expr::apps(
        Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
        [uint64(), lt_prop, dec_inst, Expr::bvar(1), Expr::bvar(0)],
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("min2_isl"),
        level_params: vec![],
        type_: Expr::arrow(uint64(), Expr::arrow(uint64(), uint64())),
        value: Expr::lam(
            BinderInfo::Default,
            uint64(),
            Expr::lam(BinderInfo::Default, uint64(), ite_body),
        ),
        is_reducible: true,
    })
    .expect("`min2_isl` must kernel-check");
    env
}

/// The emitted 4-block diamond. `cmp`, `then_src`, `else_src` are the knobs
/// the mutations turn (`then_src`/`else_src` are the PARAM LOCALS the arms
/// copy — 1-based).
fn emitted_select(cmp: BinOp, then_src: usize, else_src: usize) -> VerifiableFunction {
    let asn = |p: usize, rv: Rvalue| Statement::Assign {
        place: Place::local(p),
        rvalue: rv,
        span: SourceSpan::default(),
    };
    VerifiableFunction {
        name: "min2_isl".into(),
        def_path: "crate::m::min2_isl".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: None },
                LocalDecl { index: 2, ty: Ty::u64(), name: None },
                LocalDecl { index: 3, ty: Ty::u64(), name: None },
                LocalDecl { index: 4, ty: Ty::Bool, name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![asn(
                        4,
                        Rvalue::BinaryOp(
                            cmp,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
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
                    stmts: vec![asn(3, Rvalue::Use(Operand::Copy(Place::local(then_src))))],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![asn(3, Rvalue::Use(Operand::Copy(Place::local(else_src))))],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![asn(0, Rvalue::Use(Operand::Copy(Place::local(3))))],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::u64(),
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
    }
}

#[test]
fn half_0_the_plan_reads_the_ite_as_the_exact_select() {
    let env = env_with_min2();
    let plan = plan_clean_origin_body(&env, "min2_isl").expect("inside the C5a fragment");
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::Select {
            cmp: SelectCmp::Lt,
            cmp_left: 0,
            cmp_right: 1,
            then_param: 0,
            else_param: 1,
        }
    );
    assert_eq!(plan.param_tys(), vec![Ty::u64(), Ty::u64()]);
}

#[test]
fn half_1_the_gate_admits_the_faithful_diamond() {
    let env = env_with_min2();
    let plan = plan_clean_origin_body(&env, "min2_isl").expect("plan");
    let admitted = admit_lowering(&env, &plan, &emitted_select(BinOp::Lt, 1, 2))
        .expect("the faithful diamond must admit");
    assert_eq!(admitted.admitted_at(), &Ty::u64());
}

#[test]
fn half_2_swapped_arms_are_refused() {
    // The max2 emission for a min2 declaration — the SwitchTargets polarity
    // trap as it reads back post-extraction.
    let env = env_with_min2();
    let plan = plan_clean_origin_body(&env, "min2_isl").expect("plan");
    let refusal = admit_lowering(&env, &plan, &emitted_select(BinOp::Lt, 2, 1))
        .expect_err("a max emission for a min declaration must be refused");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");
}

#[test]
fn half_3_the_wrong_comparison_is_refused() {
    // Le for Lt: extensionally equal at min, structurally caught BEFORE the
    // kernel — and probe_h's mutation 2 proved the kernel alone would catch
    // it too (defeq is intensional on the stuck ite).
    let env = env_with_min2();
    let plan = plan_clean_origin_body(&env, "min2_isl").expect("plan");
    let refusal = admit_lowering(&env, &plan, &emitted_select(BinOp::Le, 1, 2))
        .expect_err("a Le emission for a Lt declaration must be refused");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");
}

#[test]
fn half_4_the_wrong_carrier_width_is_refused_by_the_kernel() {
    // Self-consistent u32 emission: recognition and the domain derivation
    // both pass, and only the kernel comparison at the u64 result carrier
    // sees the truncation.
    let env = env_with_min2();
    let plan = plan_clean_origin_body(&env, "min2_isl").expect("plan");
    let mut wrong = emitted_select(BinOp::Lt, 1, 2);
    wrong.body.return_ty = Ty::Int { width: 32, signed: false };
    for local in &mut wrong.body.locals {
        if local.ty == Ty::u64() {
            local.ty = Ty::Int { width: 32, signed: false };
        }
    }
    let refusal = admit_lowering(&env, &plan, &wrong)
        .expect_err("a truncating select emission must be refused");
    assert!(refusal.is_compiler_defect());
    assert!(
        matches!(refusal, EmitRefusal::Gate(trust_clean_origin::GateRefusal::Disagreement { .. })),
        "the width mistake must be caught by the KERNEL comparison: {refusal:?}"
    );
}

#[test]
fn half_5_a_non_select_body_is_refused_as_a_shape_mismatch() {
    // A projection emitted for a select plan.
    let env = env_with_min2();
    let plan = plan_clean_origin_body(&env, "min2_isl").expect("plan");
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
        ..emitted_select(BinOp::Lt, 1, 2)
    };
    let refusal = admit_lowering(&env, &plan, &wrong)
        .expect_err("a projection emission for a select plan must be refused");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");
}
