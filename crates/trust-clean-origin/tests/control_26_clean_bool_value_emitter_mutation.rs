// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 26 — THE BOOLEAN-VALUE EMITTER MUTATION FIXTURE**
//! (2026-09-13, W6 widening: a Rust program calling a Clean `def` that is a
//! boolean negation or connective over `Bool` parameters).
//!
//! `def f (a b : Bool) : Bool := a && b` has the kernel body `and a b` (def-eq
//! to `Bool.and a b`); `not b` is `Bool.not b`; `a || b` is `or a b` (def-eq to
//! `Bool.or a b`). The emitter builds a one-block body — `_0 = UnaryOp(Not, p)`
//! for negation, `_0 = <BitAnd|BitOr>(l, r)` for the connectives, `_0` at the
//! `bool` result carrier — which side B reads back through the SEPARATE entry
//! point `recognize_bool_value` and reflects through the AUTHORED
//! `admit_bool_value_function` (`Bool.not`/`Bool.and`/`Bool.or`). The kernel
//! gate then re-decides definitional equality against the island term.
//!
//! # WHY THIS IS SOUND — the recogniser is never trusted
//!
//! The soundness-critical facts are the CONNECTIVE (`&&` is not `||`), the
//! OPERAND ORDER (`Bool.and a b` is NOT definitionally equal to `Bool.and b a`
//! — commutativity is a theorem, not a reduction rule), and that negation is
//! really a negation (`not b` is not `b`). A mistake in any of them emits a
//! body denoting a different function, refused fail-closed by the gate (or by
//! the structural-agreement check just before it) — never a silently wrong
//! binary. This file measures those refusals with side A from the REAL island.
//!
//! # DO NOT "FIX" A FAILURE HERE BY EDITING SIDE B
//!
//! `trust_types::admissible_body::recognize_bool_value` and
//! `trust_spec_elab::admit_bool_value_function` are frozen against this lane. If
//! a mutated body ever passes, the defect is in the emitter or the gate.

use clean_kernel::Environment;
use trust_clean_origin::{CleanOriginShape, admit_lowering, plan_clean_origin_body};
use trust_types::{
    BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, UnOp, VerifiableBody, VerifiableFunction,
};

fn island(sources: &[&str]) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(sources);
    assert!(!batch.is_rejected(), "the island must kernel-check: {batch:?}");
    session.environment().expect("an untainted session has an environment").clone()
}

fn plan_of(env: &Environment, name: &str) -> trust_clean_origin::CleanOriginPlan {
    plan_clean_origin_body(env, name)
        .unwrap_or_else(|refusal| panic!("`{name}` must plan: {refusal:?}"))
}

/// A one-block `bool`-result body over `arg_count` `bool` parameters, with the
/// given rvalue into `_0`.
fn bool_body(rvalue: Rvalue, arg_count: usize) -> VerifiableFunction {
    let mut locals = vec![LocalDecl { index: 0, ty: Ty::Bool, name: None }];
    for index in 1..=arg_count {
        locals.push(LocalDecl { index, ty: Ty::Bool, name: None });
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
                    rvalue,
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

/// The REAL emitted body for `name`, from the REAL materializer.
fn real_emit(
    env: &Environment,
    name: &str,
) -> (trust_clean_origin::CleanOriginPlan, VerifiableFunction) {
    use trust_clean_origin::materialize::{
        BodyTemplate, TemplateOperand, TemplateRvalue, TemplateTerminator, TemplateTy,
        body_template,
    };
    use trust_clean_origin::table::ladder_row;
    let plan = plan_of(env, name);
    let selected = ladder_row(plan.shape())
        .unwrap_or_else(|| panic!("`{name}` selects no row: {:?}", plan.shape()));
    let template: BodyTemplate = body_template(selected, &plan)
        .unwrap_or_else(|refusal| panic!("`{name}` template: {refusal:?}"));
    let operand = |o: TemplateOperand| match o {
        TemplateOperand::Copy(l) => Operand::Copy(Place::local(l)),
        TemplateOperand::Move(l) => Operand::Move(Place::local(l)),
        other => panic!("W6 probe: unexpected operand {other:?}"),
    };
    let rvalue = match template.blocks[0].stmts[0].rvalue {
        TemplateRvalue::RawBin { op, left, right } => {
            Rvalue::BinaryOp(op.mir_binop(), operand(left), operand(right))
        }
        TemplateRvalue::BoolNot(o) => Rvalue::UnaryOp(UnOp::Not, operand(o)),
        ref other => panic!("W6 probe: unexpected rvalue {other:?}"),
    };
    assert!(matches!(template.blocks[0].terminator, TemplateTerminator::Return));
    let arg_count = template.arg_count;
    // Confirm the template locals are all Bool (Result + Params).
    assert!(
        template
            .locals
            .iter()
            .all(|l| matches!(l.ty, TemplateTy::Result | TemplateTy::Param { .. }))
    );
    (plan, bool_body(rvalue, arg_count))
}

// ─────────────────────────── the measurements ───────────────────────────────

/// The REAL emitter's output ADMITS for `not`/`&&`/`||`.
#[test]
fn control_26_clean_bool_value_emitter_mutation() {
    for (src, expect) in [
        ("def f (b : Bool) : Bool := not b", "not"),
        ("def f (a : Bool) (b : Bool) : Bool := a && b", "and"),
        ("def f (a : Bool) (b : Bool) : Bool := a || b", "or"),
    ] {
        let env = island(&[src]);
        let (plan, emitted) = real_emit(&env, "f");
        match (expect, plan.shape()) {
            ("not", CleanOriginShape::BoolNot { .. }) => {}
            ("and" | "or", CleanOriginShape::BoolConnective { .. }) => {}
            other => panic!("`{src}` planned as the wrong shape: {other:?}"),
        }
        admit_lowering(&env, &plan, &emitted)
            .unwrap_or_else(|r| panic!("`{src}` must ADMIT end to end: {r:?}"));
    }

    // MUTATION: `not b` emitted as the IDENTITY (`_0 = b`). Side B reads a
    // projection, not a bool-value body, so `recognize_bool_value` declines and
    // the round trip refuses.
    {
        let env = island(&["def f (b : Bool) : Bool := not b"]);
        let plan = plan_of(&env, "f");
        let mutant = bool_body(Rvalue::Use(copy(1)), 1);
        admit_lowering(&env, &plan, &mutant)
            .expect_err("emitting the identity for `not b` must be REFUSED");
    }

    // MUTATION: `not b` emitted as `b && b` (computes `b`, not `!b`).
    {
        let env = island(&["def f (b : Bool) : Bool := not b"]);
        let plan = plan_of(&env, "f");
        let mutant = bool_body(Rvalue::BinaryOp(BinOp::BitAnd, copy(1), copy(1)), 1);
        admit_lowering(&env, &plan, &mutant)
            .expect_err("emitting `b && b` for `not b` must be REFUSED");
    }

    // MUTATION: `a && b` emitted as `a || b` (`&&` is not `||`).
    {
        let env = island(&["def f (a : Bool) (b : Bool) : Bool := a && b"]);
        let plan = plan_of(&env, "f");
        let mutant = bool_body(Rvalue::BinaryOp(BinOp::BitOr, copy(1), copy(2)), 2);
        admit_lowering(&env, &plan, &mutant).expect_err("emitting `||` for `&&` must be REFUSED");
    }

    // MUTATION: `a && b` emitted with SWAPPED operands (`b && a`).
    // `Bool.and b a` is not definitionally equal to `Bool.and a b`
    // (commutativity is a theorem, not a reduction), so this is refused —
    // caught at the structural-agreement check or the kernel gate.
    {
        let env = island(&["def f (a : Bool) (b : Bool) : Bool := a && b"]);
        let plan = plan_of(&env, "f");
        let mutant = bool_body(Rvalue::BinaryOp(BinOp::BitAnd, copy(2), copy(1)), 2);
        admit_lowering(&env, &plan, &mutant)
            .expect_err("emitting `b && a` for `a && b` must be REFUSED");
    }

    // MUTATION: `a || b` emitted as `a && b`.
    {
        let env = island(&["def f (a : Bool) (b : Bool) : Bool := a || b"]);
        let plan = plan_of(&env, "f");
        let mutant = bool_body(Rvalue::BinaryOp(BinOp::BitAnd, copy(1), copy(2)), 2);
        admit_lowering(&env, &plan, &mutant).expect_err("emitting `&&` for `||` must be REFUSED");
    }
}
