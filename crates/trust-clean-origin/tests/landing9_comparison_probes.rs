// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **W6 (Rust-calls-Clean) — a comparison of two parameters returned as `Bool`,
//! measured end to end.**
//!
//! `def lt (a b : UInt{N}) : Bool := a < b` compiles, gate-verifies and is
//! callable from Rust. Its kernel body is `decide (a < b)` (`<`/`<=`) or
//! `BEq.beq {C} (instBEqOfDecidableEq {C} instDecidableEq{C}) a b` (`==`),
//! measured 2026-09-13. The emitted MIR is a one-block
//! `MirShape::ComparisonValue` — `_0 = <cmp>(l, r); return`, `_0 : bool` — which
//! side B reads back as `AdmissibleBody::ComparisonBool` and reflects through
//! the FROZEN `trust_spec_elab::admit_comparison_function`, whose
//! `Decidable.decide <prop> <inst>` mint is definitionally equal to the
//! island's `decide`/`BEq.beq` (the `is_def_eq` the gate re-decides).
//!
//! Every side A here comes from `trust_certify::clean_island::CleanIslandSession`
//! — the exact pipeline `clean_origin_mir` drives — never from a hand-built
//! term, and each body is taken through the REAL `body_template` and the REAL
//! `admit_lowering` (side B's reader, side B's producer and the kernel gate) at
//! u8/u16/u32/u64.

use clean_kernel::{Environment, Name};
use trust_clean_origin::materialize::{
    BodyTemplate, TemplateOperand, TemplateRvalue, TemplateTerminator, TemplateTy, body_template,
};
use trust_clean_origin::table::ladder_row;
use trust_clean_origin::{
    CleanOriginPlan, CleanOriginShape, admit_lowering, plan_clean_origin_body,
};
use trust_types::admissible_body::SelectCmp;
use trust_types::{
    BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, VerifiableBody, VerifiableFunction,
};

const WIDTHS: [u32; 4] = [8, 16, 32, 64];

fn island(sources: &[&str]) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(sources);
    assert!(!batch.is_rejected(), "the island must kernel-check: {batch:?}");
    session.environment().expect("an untainted session has an environment").clone()
}

fn render_bool_body(template: &BodyTemplate, bits: u32) -> VerifiableFunction {
    let uint = Ty::Int { width: bits, signed: false };
    let local_ty = |ty: TemplateTy| match ty {
        TemplateTy::Result | TemplateTy::Bool => Ty::Bool,
        TemplateTy::Param { .. } => uint.clone(),
        other => panic!("W6 probe: unexpected local type {other:?}"),
    };
    let operand = |operand: TemplateOperand| match operand {
        TemplateOperand::Copy(local) => Operand::Copy(Place::local(local)),
        TemplateOperand::Move(local) => Operand::Move(Place::local(local)),
        other => panic!("W6 probe: unexpected operand {other:?}"),
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
                        other => panic!("W6 probe: unexpected rvalue {other:?}"),
                    },
                    span: SourceSpan::default(),
                })
                .collect(),
            terminator: match &block.terminator {
                TemplateTerminator::Return => Terminator::Return,
                other => panic!("W6 probe: unexpected terminator {other:?}"),
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

fn plan_and_emit(
    env: &Environment,
    name: &str,
    bits: u32,
) -> (CleanOriginPlan, VerifiableFunction) {
    let plan = plan_clean_origin_body(env, name)
        .unwrap_or_else(|refusal| panic!("`{name}` must plan: {refusal:?}"));
    let selected = ladder_row(plan.shape())
        .unwrap_or_else(|| panic!("`{name}`'s shape selects no row: {:?}", plan.shape()));
    let template = body_template(selected, &plan)
        .unwrap_or_else(|refusal| panic!("`{name}`'s template: {refusal:?}"));
    (plan, render_bool_body(&template, bits))
}

/// Drive `def f (a b : UInt{w}) : Bool := <op-src>` end to end at every width,
/// asserting it plans as a `DecideComparison` and `admit_lowering` ADMITS.
fn admits_at_every_width(op_src: &str) {
    for bits in WIDTHS {
        let src = format!("def f (a : UInt{bits}) (b : UInt{bits}) : Bool := {op_src}");
        let env = island(&[&src]);
        let (plan, emitted) = plan_and_emit(&env, "f", bits);
        assert!(
            matches!(plan.shape(), CleanOriginShape::DecideComparison { .. }),
            "`{src}` must plan as a DecideComparison, got {:?}",
            plan.shape()
        );
        admit_lowering(&env, &plan, &emitted)
            .unwrap_or_else(|refusal| panic!("`{src}` must ADMIT end to end: {refusal:?}"));
    }
    let _ = Name::from_string("unused");
}

#[test]
fn l9_p1_decide_lt_admits_end_to_end() {
    admits_at_every_width("a < b");
    // Operand order is a real degree of freedom, admitted in both directions.
    admits_at_every_width("b < a");
}

#[test]
fn l9_p2_decide_le_admits_end_to_end() {
    admits_at_every_width("a <= b");
    admits_at_every_width("b <= a");
}

#[test]
fn l9_p3_beq_eq_admits_end_to_end() {
    admits_at_every_width("a == b");
}
