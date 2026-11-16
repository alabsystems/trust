// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Trust (WS5.20, F-096): the standalone Lean lane's DECISION family — a
//! comparison of two parameters returned as `Bool` (`STANDALONE.p01`,
//! `a.lean.standalone.bool_cmp`) and a parameter select (`STANDALONE.p02`,
//! `a.lean.standalone.select`). The reader derives the comparison, its operands
//! and the arms from the ACTUAL SSA, hands that reading to the frozen
//! `trust_spec_elab` producer, and the kernel decides whole-term definitional
//! equality with the untouched declaration at the exact result carrier.

use clean_kernel::Name;
use trust_certify::lean_source_batch::{
    AcceptedLeanSourceContext, CheckedLeanSourceBatch, LeanSourceInput,
};
use trust_clean_ir_gate::standalone::admit_standalone_scalar;
use trust_clean_origin::CleanOriginShape;
use trust_clean_origin::emit::plan_standalone_clean_origin_body;
use trust_ir::ty::FuncTy;
use trust_ir::value::{FuncId, FuncTyId};
use trust_ir::{Function, ICmpOp, Inst, Producer};

fn checked(source: &str) -> CheckedLeanSourceBatch {
    let batch = CheckedLeanSourceBatch::check(
        vec![LeanSourceInput {
            module: "Decisions".to_owned(),
            path: "Decisions.lean".to_owned(),
            source: source.to_owned(),
        }],
        false,
    );
    assert!(batch.accepted_context().is_some(), "{:?}", batch.errors());
    batch
}

fn emitted(context: &AcceptedLeanSourceContext<'_>, name: &str) -> (Name, FuncTy, Function) {
    let plan = plan_standalone_clean_origin_body(context.environment(), name).unwrap();
    let signature = trust_clean_ir::trust_ir_func_ty(plan.signature()).unwrap();
    let function = trust_clean_ir::emit_standalone_clean_origin_function(
        &plan,
        FuncId::new(0),
        FuncTyId::new(0),
    )
    .unwrap();
    (Name::from_string(name), signature, function)
}

fn shape_of(context: &AcceptedLeanSourceContext<'_>, name: &str) -> CleanOriginShape {
    plan_standalone_clean_origin_body(context.environment(), name).unwrap().shape().clone()
}

fn admits(context: &AcceptedLeanSourceContext<'_>, name: &str) {
    let (decl, signature, function) = emitted(context, name);
    let token = admit_standalone_scalar(context, &decl, &signature, &function)
        .unwrap_or_else(|refusal| panic!("{name}: {refusal}"));
    assert_eq!(token.method_tag(), "definitional-equality");
    token.authenticate(context, &decl, &signature, &function).unwrap();
    let mut published = function.clone();
    published.id = FuncId::new(5);
    published.ty = FuncTyId::new(6);
    published.producer = Some(Producer::Clean);
    let relocated =
        token.authenticate_published(context, &decl, &signature, &function, &published).unwrap();
    assert_ne!(relocated.subject_digest(), token.subject_digest());
}

fn refusal_stage(
    context: &AcceptedLeanSourceContext<'_>,
    name: &str,
    mutate: impl FnOnce(&mut Function),
) -> &'static str {
    let (decl, signature, mut function) = emitted(context, name);
    mutate(&mut function);
    admit_standalone_scalar(context, &decl, &signature, &function)
        .map(|_| ())
        .expect_err("the mutant must be refused")
        .stage()
}

fn icmp_op(function: &mut Function) -> &mut ICmpOp {
    function.blocks[0]
        .body
        .iter_mut()
        .find_map(|node| match &mut node.inst {
            Inst::ICmp { op, .. } => Some(op),
            _ => None,
        })
        .expect("the decision body has an ICmp")
}

/// POSITIVE: every carrier, every relation the planner spells, and both the
/// comparison and the select read.
#[test]
fn comparisons_and_selects_mint_at_every_uint_carrier() {
    let mut source = String::new();
    for width in [8, 16, 32, 64] {
        let t = format!("UInt{width}");
        source.push_str(&format!("def lt{width} (a b : {t}) : Bool := a < b\n"));
        source.push_str(&format!("def le{width} (a b : {t}) : Bool := a <= b\n"));
        source.push_str(&format!("def eq{width} (a b : {t}) : Bool := a == b\n"));
        source.push_str(&format!("def min{width} (a b : {t}) : {t} := if a < b then a else b\n"));
        source.push_str(&format!("def max{width} (a b : {t}) : {t} := if a <= b then b else a\n"));
    }
    let batch = checked(&source);
    let context = batch.accepted_context().unwrap();
    for width in [8, 16, 32, 64] {
        for prefix in ["lt", "le", "eq"] {
            let name = format!("{prefix}{width}");
            assert!(
                matches!(shape_of(&context, &name), CleanOriginShape::DecideComparison { .. }),
                "{name}"
            );
            admits(&context, &name);
        }
        for prefix in ["min", "max"] {
            let name = format!("{prefix}{width}");
            assert!(matches!(shape_of(&context, &name), CleanOriginShape::Select { .. }), "{name}");
            admits(&context, &name);
        }
    }
}

/// The probe rows themselves, verbatim.
#[test]
fn the_part_a_probes_p01_and_p02_are_admitted() {
    let batch = checked(
        "def isLt (a b : UInt64) : Bool := a < b\n\
         def min2 (a b : UInt64) : UInt64 := if a < b then a else b\n",
    );
    let context = batch.accepted_context().unwrap();
    admits(&context, "isLt");
    admits(&context, "min2");
}

/// MUTATIONS: swapped select arms, a weakened relation and swapped operands
/// all reach the kernel and are refused there; `ult` respelled `slt` (a signed
/// predicate) and `!=` are refused by the reader before any mint.
#[test]
fn every_decision_mutant_is_refused_by_name() {
    let batch = checked(
        "def isLt (a b : UInt64) : Bool := a < b\n\
         def min2 (a b : UInt64) : UInt64 := if a < b then a else b\n",
    );
    let context = batch.accepted_context().unwrap();
    // Select arms swapped: the reflected term is `if a < b then b else a`.
    let stage = refusal_stage(&context, "min2", |function| {
        for node in &mut function.blocks[0].body {
            if let Inst::Select { then_val, else_val, .. } = &mut node.inst {
                std::mem::swap(then_val, else_val);
            }
        }
    });
    assert_eq!(stage, "kernel-disagreement");
    // `<` weakened to `<=`, in both shapes.
    for name in ["isLt", "min2"] {
        let stage = refusal_stage(&context, name, |function| *icmp_op(function) = ICmpOp::Ule);
        assert_eq!(stage, "kernel-disagreement", "{name}");
    }
    // Operands swapped.
    let stage = refusal_stage(&context, "isLt", |function| {
        for node in &mut function.blocks[0].body {
            if let Inst::ICmp { lhs, rhs, .. } = &mut node.inst {
                std::mem::swap(lhs, rhs);
            }
        }
    });
    assert_eq!(stage, "kernel-disagreement");
    // `ult` respelled as the SIGNED `slt`, and `!=`: no producer, no mint.
    for op in [ICmpOp::Slt, ICmpOp::Ne] {
        let stage = refusal_stage(&context, "isLt", |function| *icmp_op(function) = op);
        assert_eq!(stage, "instruction", "{op:?}");
    }
    // A decision whose result is not the comparison.
    let stage = refusal_stage(&context, "isLt", |function| {
        let parameter = function.blocks[0].params[0].0;
        let Inst::Return { values } = &mut function.blocks[0].body[1].inst else {
            panic!("Return")
        };
        values[0] = parameter;
    });
    assert_eq!(stage, "return", "the reader refuses a non-ICmp return before any mint");
}

/// `a > b` IS `b < a`: the reader maps `ugt b a` onto the producer's `<` with
/// the operands swapped, so the SAME relation spelled the other way is
/// admitted — and only with the operands swapped back.
#[test]
fn a_greater_than_spelling_of_the_same_relation_is_the_same_decision() {
    let batch = checked("def isLt (a b : UInt64) : Bool := a < b\n");
    let context = batch.accepted_context().unwrap();
    let (decl, signature, mut function) = emitted(&context, "isLt");
    for node in &mut function.blocks[0].body {
        if let Inst::ICmp { op, lhs, rhs, .. } = &mut node.inst {
            *op = ICmpOp::Ugt;
            std::mem::swap(lhs, rhs);
        }
    }
    admit_standalone_scalar(&context, &decl, &signature, &function)
        .unwrap_or_else(|refusal| panic!("`b > a` is `a < b`: {refusal}"));
    // Control: `ugt` WITHOUT the operand swap is `a > b`, a different function.
    let (_, _, mut control) = emitted(&context, "isLt");
    *icmp_op(&mut control) = ICmpOp::Ugt;
    let stage = admit_standalone_scalar(&context, &decl, &signature, &control)
        .map(|_| ())
        .expect_err("`a > b` is not `a < b`")
        .stage();
    assert_eq!(stage, "kernel-disagreement");
}
