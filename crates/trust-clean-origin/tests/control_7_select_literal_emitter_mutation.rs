// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 7 — THE SELECT-vs-LITERAL EMITTER MUTATION FIXTURE (R2/C9).**
//!
//! `control_3` covers Projection, `control_5` WrappingBinOp, `control_6` the
//! parameter Select; this is the SAME control for `SelectLiteral`, per the
//! standing amendment that every shape lands with its own per-shape mutation
//! control — stated EXPLICITLY for C9, because its widening touched side B
//! (a new recognizer arm and a NEW admit route), which is exactly where a
//! same-lane-authors-both-sides gate goes soft without adversarial controls.
//! The route under test is `admit_lowering`'s SelectLiteral arm:
//!
//! ```text
//! emitted body (the 4-block O0 literal-compare diamond)
//!   -> trust_types::recognize_admissible_body     (recognize_select, literal case)
//!   -> trust_spec_elab::admit_select_literal_function  (side B, the NEW route)
//!   -> check_faithful                              (against side A's ite)
//! ```
//!
//! Mutations are injected into the EMITTED body only. Side B is frozen
//! against THIS lane the moment it lands; if a mutant ever passes, the defect
//! is in the emitter or the gate — never here.

use clean_kernel::{Environment, Expr, Name};
use trust_clean_origin::{CleanOriginShape, EmitRefusal, admit_lowering, plan_clean_origin_body};
use trust_types::admissible_body::SelectCmp;
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

fn uint64() -> Expr {
    Expr::const_(Name::from_string("UInt64"), vec![])
}

/// `def min10_isl (a b : UInt64) : UInt64 := if a < 10 then a else b`, as the
/// `ite` term `elab_if` mints — the comparison's right operand the SURFACE
/// numeral (`OfNat.ofNat UInt64 10 (instOfNatUInt64 10)`, what a real island
/// elaborates) — FULL-kernel-checked into `with_prelude()`.
fn env_with_min10() -> Environment {
    // The REAL island elaboration, not a hand-built guess: the C9 fixtures
    // measured (E0425 at the driver) that the elaborator resolves a literal
    // comparison's decidability through `instDecidableNatLt` over a `toNat`
    // projection chain — a spelling the original hand-built term missed.
    // probe_i3 pins the planner against this same real tree; this control
    // must exercise the SAME side A the compiler actually sees.
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&[
        "def min10_isl (a : UInt64) (b : UInt64) : UInt64 := if a < 10 then a else b",
    ]);
    assert!(!batch.is_rejected(), "the island must kernel-check: {batch:?}");
    session.environment().expect("an untainted session has an environment").clone()
}

/// The emitted 4-block literal-compare diamond. `cmp`, `lit`, `then_src`,
/// `else_src` are the knobs the mutations turn (`then_src`/`else_src` are the
/// PARAM LOCALS the arms copy — 1-based).
fn emitted_select_literal(
    cmp: BinOp,
    lit: u128,
    then_src: usize,
    else_src: usize,
) -> VerifiableFunction {
    let asn = |p: usize, rv: Rvalue| Statement::Assign {
        place: Place::local(p),
        rvalue: rv,
        span: SourceSpan::default(),
    };
    VerifiableFunction {
        name: "min10_isl".into(),
        def_path: "crate::m::min10_isl".into(),
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
                            Operand::Constant(ConstValue::Uint(lit, 64)),
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
fn half_0_the_plan_reads_the_literal_ite_as_the_exact_select_literal() {
    let env = env_with_min10();
    let plan = plan_clean_origin_body(&env, "min10_isl").expect("inside the C9 fragment");
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::SelectLiteral {
            cmp: SelectCmp::Lt,
            cmp_param: 0,
            literal: 10,
            then_param: 0,
            else_param: 1,
        }
    );
    assert_eq!(plan.param_tys(), vec![Ty::u64(), Ty::u64()]);
}

#[test]
fn half_1_the_gate_admits_the_faithful_diamond() {
    let env = env_with_min10();
    let plan = plan_clean_origin_body(&env, "min10_isl").expect("plan");
    let admitted = admit_lowering(&env, &plan, &emitted_select_literal(BinOp::Lt, 10, 1, 2))
        .expect("the faithful literal diamond must admit");
    assert_eq!(admitted.admitted_at(), &Ty::u64());
}

#[test]
fn half_2_the_wrong_literal_is_refused() {
    // THE C9-DISTINCTIVE MUTATION: the emitted threshold off by one — a body
    // that agrees with the declaration everywhere except `a = 10`. The
    // structural plan-vs-recognizer check catches it first
    // (LoweringShapeMismatch); probe_i's paired mutation pins that the KERNEL
    // alone refuses it too, so neither layer is load-bearing alone.
    let env = env_with_min10();
    let plan = plan_clean_origin_body(&env, "min10_isl").expect("plan");
    let refusal = admit_lowering(&env, &plan, &emitted_select_literal(BinOp::Lt, 11, 1, 2))
        .expect_err("an 11-threshold emission for a 10-threshold declaration must be refused");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");
}

#[test]
fn half_3_swapped_arms_are_refused() {
    // The `if a < 10 { b } else { a }` emission for the min10 declaration —
    // the SwitchTargets polarity trap as it reads back post-extraction.
    let env = env_with_min10();
    let plan = plan_clean_origin_body(&env, "min10_isl").expect("plan");
    let refusal = admit_lowering(&env, &plan, &emitted_select_literal(BinOp::Lt, 10, 2, 1))
        .expect_err("a swapped-arm emission must be refused");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");
}

#[test]
fn half_4_the_wrong_comparison_is_refused() {
    // Le for Lt: at a literal threshold the two differ exactly on the
    // boundary input `a = 10`, where the arms differ too — a REAL wrong
    // binary, not an extensional coincidence. Structurally caught before the
    // kernel; probe_i's mutation pins the kernel-alone catch.
    let env = env_with_min10();
    let plan = plan_clean_origin_body(&env, "min10_isl").expect("plan");
    let refusal = admit_lowering(&env, &plan, &emitted_select_literal(BinOp::Le, 10, 1, 2))
        .expect_err("a Le emission for a Lt declaration must be refused");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");
}

#[test]
fn half_5_a_param_compare_emission_is_refused() {
    // The emitter compares `a < b` where the island says `a < 10`: the body
    // recognizes fine — as the WRONG shape (`Select`, not `SelectLiteral`).
    let env = env_with_min10();
    let plan = plan_clean_origin_body(&env, "min10_isl").expect("plan");
    let mut wrong = emitted_select_literal(BinOp::Lt, 10, 1, 2);
    let Statement::Assign { rvalue: Rvalue::BinaryOp(_, _, opr), .. } =
        &mut wrong.body.blocks[0].stmts[0]
    else {
        unreachable!("the diamond's entry is the comparison");
    };
    *opr = Operand::Copy(Place::local(2));
    let refusal = admit_lowering(&env, &plan, &wrong)
        .expect_err("a param-compare emission for a literal-compare declaration must be refused");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");
}

#[test]
fn half_6_the_wrong_carrier_width_is_refused() {
    // Self-consistent u32 emission (locals, return type AND the constant's
    // encoded width all agree at u32): recognition and the domain derivation
    // both pass, and the truncation is seen only downstream — the reflected
    // side B mints at the u32 domain and the kernel comparison at the u64
    // result carrier refuses.
    let env = env_with_min10();
    let plan = plan_clean_origin_body(&env, "min10_isl").expect("plan");
    let mut wrong = emitted_select_literal(BinOp::Lt, 10, 1, 2);
    wrong.body.return_ty = Ty::Int { width: 32, signed: false };
    for local in &mut wrong.body.locals {
        if local.ty == Ty::u64() {
            local.ty = Ty::Int { width: 32, signed: false };
        }
    }
    let Statement::Assign { rvalue: Rvalue::BinaryOp(_, _, opr), .. } =
        &mut wrong.body.blocks[0].stmts[0]
    else {
        unreachable!("the diamond's entry is the comparison");
    };
    *opr = Operand::Constant(ConstValue::Uint(10, 32));
    let refusal = admit_lowering(&env, &plan, &wrong)
        .expect_err("a truncating select-literal emission must be refused");
    assert!(refusal.is_compiler_defect());
    assert!(
        matches!(refusal, EmitRefusal::Gate(trust_clean_origin::GateRefusal::Disagreement { .. })),
        "the width mistake must be caught by the KERNEL comparison: {refusal:?}"
    );
}

#[test]
fn half_7_a_non_select_body_is_refused_as_a_shape_mismatch() {
    // A projection emitted for a select-literal plan.
    let env = env_with_min10();
    let plan = plan_clean_origin_body(&env, "min10_isl").expect("plan");
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
        ..emitted_select_literal(BinOp::Lt, 10, 1, 2)
    };
    let refusal = admit_lowering(&env, &plan, &wrong)
        .expect_err("a projection emission for a select-literal plan must be refused");
    assert!(refusal.is_compiler_defect());
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");
}
