// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 25 — THE COMPARISON-TO-`Bool` EMITTER MUTATION FIXTURE**
//! (2026-09-13, W6 widening: a Rust program calling a Clean `def` whose body is
//! a comparison of two parameters returned as `Bool`).
//!
//! `def lt (a b : UInt64) : Bool := a < b` has the kernel body `decide (a < b)`
//! (`<`/`<=`) or `BEq.beq {C} … a b` (`==`). The emitter builds a one-block
//! `MirShape::ComparisonValue` — `_0 = <cmp>(l, r); return`, `_0` at the result
//! carrier `bool` — which side B reads back as
//! `trust_types::admissible_body::AdmissibleBody::ComparisonBool` and reflects
//! through the FROZEN `trust_spec_elab::admit_comparison_function`, minting
//! `Decidable.decide <prop> <inst>`. [`check_faithful`] then re-decides
//! definitional equality of that reflection against the untouched declaration.
//!
//! # WHY THIS IS SOUND — the recogniser is never trusted
//!
//! The two soundness-critical facts of a comparison are its POLARITY (which
//! operator) and its OPERAND ORDER (`a < b` is not `b < a`). A mistake in
//! either emits a body that DENOTES A DIFFERENT FUNCTION, whose reflection is
//! not definitionally equal to the declaration and is refused fail-closed by
//! the kernel gate — NEVER a silently wrong binary. This file measures exactly
//! those refusals, with side A taken from the REAL island elaborator and only
//! the EMITTED body hand-mutated:
//!
//! * the correct emission ADMITS (`a < b`, `a <= b`, `a == b`);
//! * a SWAPPED OPERATOR (`<=` for `<`) is REFUSED BY THE KERNEL GATE;
//! * SWAPPED OPERANDS (`b < a` for `a < b`) are REFUSED BY THE KERNEL GATE;
//! * `==` emitted as `<`, and `<` emitted as `==`, are REFUSED;
//! * a LITERAL operand (`a < 10 : Bool`) is refused BEFORE the gate — the
//!   recogniser admits only parameter operands, precisely because the literal's
//!   Nat-reduced Decidable instance is not definitionally equal to the frozen
//!   producer's carrier-instance mint (measured 2026-09-13).
//!
//! # DO NOT "FIX" A FAILURE HERE BY EDITING SIDE B'S PRODUCERS
//!
//! `trust_types::admissible_body` and `trust_spec_elab::admit_comparison_function`
//! are frozen against this lane, exactly as for control_3/control_13/control_24.
//! If a mutated body ever passes, the defect is in the emitter or the gate —
//! never here.

use clean_kernel::{Environment, Name};
use trust_clean_origin::materialize::{
    BodyTemplate, TemplateOperand, TemplateRvalue, TemplateTerminator, TemplateTy, body_template,
};
use trust_clean_origin::table::ladder_row;
use trust_clean_origin::{CleanOriginShape, EmitRefusal, admit_lowering, plan_clean_origin_body};
use trust_types::admissible_body::SelectCmp;
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

// ───────────────────── side A: the REAL island elaborator ─────────────────────

fn island(sources: &[&str]) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(sources);
    assert!(!batch.is_rejected(), "the island must kernel-check: {batch:?}");
    session.environment().expect("an untainted session has an environment").clone()
}

// ───────── the EMITTED body, hand-built at bool result / uN operands ─────────

/// A one-block comparison body `_0 = <cmp>(op(left), op(right)); return`, with
/// `_0 : bool` and every parameter local at `u{bits}`. This is what
/// `trust_mir_extract::extract_function` produces for `MirShape::ComparisonValue`
/// — restated here so a MUTATION can hand-build a body the real emitter never
/// would.
fn comparison_body(
    cmp: BinOp,
    left: Operand,
    right: Operand,
    bits: u32,
    arg_count: usize,
) -> VerifiableFunction {
    let uint = Ty::Int { width: bits, signed: false };
    let mut locals = vec![LocalDecl { index: 0, ty: Ty::Bool, name: None }];
    for index in 1..=arg_count {
        locals.push(LocalDecl { index, ty: uint.clone(), name: None });
    }
    VerifiableFunction {
        name: "probe".into(),
        def_path: "crate::m::probe".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(cmp, left, right),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count,
            return_ty: Ty::Bool,
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn copy(local: usize) -> Operand {
    Operand::Copy(Place::local(local))
}

fn plan_of(env: &Environment, name: &str) -> trust_clean_origin::CleanOriginPlan {
    plan_clean_origin_body(env, name)
        .unwrap_or_else(|refusal| panic!("`{name}` must plan: {refusal:?}"))
}

/// The REAL emitted body for `name`, rendered from the REAL `body_template`,
/// typed with `_0 : bool` and `u{bits}` operands (landing6's renderer types the
/// result at the operand width, which is wrong for a `Bool`-valued body).
fn plan_and_emit(
    env: &Environment,
    name: &str,
    bits: u32,
) -> (trust_clean_origin::CleanOriginPlan, VerifiableFunction) {
    let plan = plan_of(env, name);
    let selected = ladder_row(plan.shape())
        .unwrap_or_else(|| panic!("`{name}`'s shape selects no row: {:?}", plan.shape()));
    let template = body_template(selected, &plan)
        .unwrap_or_else(|refusal| panic!("`{name}`'s template: {refusal:?}"));
    (plan, render_bool_body(&template, bits))
}

/// Render a [`BodyTemplate`] whose result carrier is `bool` and whose
/// parameters are at `u{bits}`.
fn render_bool_body(template: &BodyTemplate, bits: u32) -> VerifiableFunction {
    let uint = Ty::Int { width: bits, signed: false };
    let local_ty = |ty: TemplateTy| match ty {
        TemplateTy::Result => Ty::Bool,
        TemplateTy::Param { .. } => uint.clone(),
        TemplateTy::Bool => Ty::Bool,
        other => panic!("W6 comparison probe: unexpected local type {other:?}"),
    };
    let operand = |operand: TemplateOperand| match operand {
        TemplateOperand::Copy(local) => Operand::Copy(Place::local(local)),
        TemplateOperand::Move(local) => Operand::Move(Place::local(local)),
        other => panic!("W6 comparison probe: unexpected operand {other:?}"),
    };
    let binop = |cmp: SelectCmp| match cmp {
        SelectCmp::Lt => BinOp::Lt,
        SelectCmp::Le => BinOp::Le,
        SelectCmp::Eq => BinOp::Eq,
    };
    let locals = template
        .locals
        .iter()
        .enumerate()
        .map(|(index, local)| LocalDecl { index, ty: local_ty(local.ty), name: None })
        .collect();
    let blocks = template
        .blocks
        .iter()
        .enumerate()
        .map(|(index, block)| BasicBlock {
            id: BlockId(index),
            stmts: block
                .stmts
                .iter()
                .map(|stmt| Statement::Assign {
                    place: Place::local(stmt.place),
                    rvalue: match stmt.rvalue {
                        TemplateRvalue::Compare { cmp, left, right } => {
                            Rvalue::BinaryOp(binop(cmp), operand(left), operand(right))
                        }
                        other => panic!("W6 comparison probe: unexpected rvalue {other:?}"),
                    },
                    span: SourceSpan::default(),
                })
                .collect(),
            terminator: match &block.terminator {
                TemplateTerminator::Return => Terminator::Return,
                other => panic!("W6 comparison probe: unexpected terminator {other:?}"),
            },
        })
        .collect();
    VerifiableFunction {
        name: "probe".into(),
        def_path: "crate::m::probe".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: template.arg_count,
            return_ty: Ty::Bool,
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

// ─────────────────────────── the measurements ───────────────────────────────

/// The REAL emitter's output ADMITS at `<`, `<=`, `==`, both operand orders and
/// every width. This is the positive control the mutations below are measured
/// against — a fixture whose "refused" cases pass only because NOTHING passes
/// is worthless.
#[test]
fn half_1_the_real_comparison_bodies_admit() {
    for (src, name) in [
        ("def f (a : UInt64) (b : UInt64) : Bool := a < b", "f"),
        ("def f (a : UInt64) (b : UInt64) : Bool := a <= b", "f"),
        ("def f (a : UInt64) (b : UInt64) : Bool := a == b", "f"),
        ("def f (a : UInt64) (b : UInt64) : Bool := b < a", "f"),
        ("def f (a : UInt8)  (b : UInt8)  : Bool := a < b", "f"),
        ("def f (a : UInt32) (b : UInt32) : Bool := a == b", "f"),
    ] {
        let env = island(&[src]);
        let bits = if src.contains("UInt8") {
            8
        } else if src.contains("UInt32") {
            32
        } else {
            64
        };
        let (plan, emitted) = plan_and_emit(&env, name, bits);
        assert!(
            matches!(plan.shape(), CleanOriginShape::DecideComparison { .. }),
            "`{src}` must plan as a DecideComparison, got {:?}",
            plan.shape()
        );
        admit_lowering(&env, &plan, &emitted)
            .unwrap_or_else(|refusal| panic!("`{src}` must ADMIT end to end: {refusal:?}"));
    }
}

/// **THE POLARITY MUTATION.** Side A is `a < b`; the emitted body computes
/// `a <= b`. The two denote different functions at `a == b`, so the kernel gate
/// refuses.
#[test]
fn half_2_a_swapped_operator_is_refused() {
    let env = island(&["def f (a : UInt64) (b : UInt64) : Bool := a < b"]);
    let plan = plan_of(&env, "f");
    let mutant = comparison_body(BinOp::Le, copy(1), copy(2), 64, 2);
    let refusal = admit_lowering(&env, &plan, &mutant)
        .expect_err("emitting `<=` for a `<` declaration must be REFUSED");
    // The mismatch is caught either at structural agreement or at the kernel
    // gate; both are fail-closed refusals, and the point is that NOTHING admits.
    let _ = refusal;
}

/// **THE OPERAND-ORDER MUTATION.** Side A is `a < b`; the emitted body computes
/// `b < a`. `admit_comparison_function` mints `decide (a < b)` from the read
/// operands, and `decide (b < a)` is not definitionally equal to `decide (a <
/// b)` — refused.
#[test]
fn half_3_swapped_operands_are_refused() {
    let env = island(&["def f (a : UInt64) (b : UInt64) : Bool := a < b"]);
    let plan = plan_of(&env, "f");
    let mutant = comparison_body(BinOp::Lt, copy(2), copy(1), 64, 2);
    admit_lowering(&env, &plan, &mutant)
        .expect_err("emitting `b < a` for an `a < b` declaration must be REFUSED");
}

/// **`==` EMITTED AS `<`.** Side A is `a == b` (`BEq.beq …`); the emitted body
/// computes `a < b`. Refused.
#[test]
fn half_4_equality_emitted_as_less_than_is_refused() {
    let env = island(&["def f (a : UInt64) (b : UInt64) : Bool := a == b"]);
    let plan = plan_of(&env, "f");
    let mutant = comparison_body(BinOp::Lt, copy(1), copy(2), 64, 2);
    admit_lowering(&env, &plan, &mutant)
        .expect_err("emitting `<` for an `==` declaration must be REFUSED");
}

/// **`<` EMITTED AS `==`.** The mirror of half_4.
#[test]
fn half_5_less_than_emitted_as_equality_is_refused() {
    let env = island(&["def f (a : UInt64) (b : UInt64) : Bool := a < b"]);
    let plan = plan_of(&env, "f");
    let mutant = comparison_body(BinOp::Eq, copy(1), copy(2), 64, 2);
    admit_lowering(&env, &plan, &mutant)
        .expect_err("emitting `==` for a `<` declaration must be REFUSED");
}

/// **THE LITERAL-OPERAND RESIDUAL.** `a < 10 : Bool` is refused BEFORE the
/// gate: the recogniser admits only parameter operands, precisely because the
/// literal comparison's Decidable instance is Nat-reduced
/// (`instDecidableNatLt (a.toNat…) 10`) rather than the carrier instance the
/// frozen `admit_comparison_function` mints, so the reflected term is not
/// definitionally equal to the declaration (measured 2026-09-13). The refusal
/// is the generic fragment refusal, which is the honest disposition until a
/// Nat-reduced-instance producer exists.
#[test]
fn half_literal_operand_refused() {
    let env = island(&["def f (a : UInt64) : Bool := a < 10"]);
    let refusal = plan_clean_origin_body(&env, "f")
        .expect_err("`a < 10 : Bool` is a residual and must be refused, not planned");
    assert!(
        matches!(refusal, EmitRefusal::NotEmittable { .. }),
        "the literal-operand comparison must be a clean NotEmittable refusal, got {refusal:?}"
    );
    let _ = Name::from_string("unused");
}
