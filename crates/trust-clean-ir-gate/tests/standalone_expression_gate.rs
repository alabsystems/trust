// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use clean_kernel::Name;
use trust_certify::lean_source_batch::{
    AcceptedLeanSourceContext, CheckedLeanSourceBatch, LeanSourceInput,
};
use trust_clean_ir_gate::standalone::{admit_standalone_scalar, admit_standalone_wrapping_binop};
use trust_clean_origin::CleanOriginShape;
use trust_clean_origin::emit::plan_standalone_clean_origin_body;
use trust_ir::node::InstrNode;
use trust_ir::proof::ProofAnnotation;
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{FuncId, FuncTyId, ValueId};
use trust_ir::{BinOp, CallingConv, Constant, Function, Inst, Module, Producer};
use trust_types::digest::canonical_json_sha256;

fn checked(source: &str) -> CheckedLeanSourceBatch {
    let batch = CheckedLeanSourceBatch::check(
        vec![LeanSourceInput {
            module: "Expressions".to_owned(),
            path: "Expressions.lean".to_owned(),
            source: source.to_owned(),
        }],
        false,
    );
    assert!(batch.accepted_context().is_some(), "{:?}", batch.errors());
    batch
}

fn emitted(context: &AcceptedLeanSourceContext<'_>, name: &str) -> (Name, FuncTy, Function) {
    let plan = plan_standalone_clean_origin_body(context.environment(), name).unwrap();
    assert!(matches!(plan.shape(), CleanOriginShape::Composed { .. }));
    let signature = trust_clean_ir::trust_ir_func_ty(plan.signature()).unwrap();
    let function = trust_clean_ir::emit_standalone_clean_origin_function(
        &plan,
        FuncId::new(0),
        FuncTyId::new(0),
    )
    .unwrap();
    (Name::from_string(name), signature, function)
}

fn node(inst: Inst, id: u32) -> InstrNode {
    InstrNode {
        inst,
        results: vec![ValueId::new(id)],
        proofs: vec![],
        span: None,
        proof_context: None,
        scope: None,
    }
}

#[test]
fn all_four_carriers_reflect_parameter_reuse_literals_and_operator_nesting() {
    let mut source = String::new();
    for width in [8, 16, 32, 64] {
        source.push_str(&format!(
            "def compose{width} (a b : UInt{width}) : UInt{width} := ((a + b) - a) * (b + 3)\n"
        ));
        source.push_str(&format!(
            "def repeat{width} (a b : UInt{width}) : UInt{width} := (a + b) + a\n"
        ));
        source.push_str(&format!(
            "def maxleaf{width} (a b : UInt{width}) : UInt{width} := (a + {}) - b\n",
            (1_u128 << width) - 1
        ));
    }
    let batch = checked(&source);
    let context = batch.accepted_context().unwrap();
    assert_eq!(context.owned_declarations().len(), 12);
    for width in [8, 16, 32, 64] {
        for prefix in ["compose", "repeat", "maxleaf"] {
            let (name, signature, function) = emitted(&context, &format!("{prefix}{width}"));
            let token = admit_standalone_scalar(&context, &name, &signature, &function).unwrap();
            assert_eq!(token.carrier_tag(), format!("UInt{width}"));
            assert_eq!(token.method_tag(), "definitional-equality");
            token.authenticate(&context, &name, &signature, &function).unwrap();
            assert!(
                admit_standalone_wrapping_binop(&context, &name, &signature, &function).is_err()
            );
            let mut published = function.clone();
            published.id = FuncId::new(7);
            published.ty = FuncTyId::new(9);
            published.producer = Some(Producer::Clean);
            let relocated = token
                .authenticate_published(&context, &name, &signature, &function, &published)
                .unwrap();
            assert_ne!(relocated.subject_digest(), token.subject_digest());
        }
    }
}

#[test]
fn wrong_operand_noncommutative_order_operator_and_source_refuse_fresh_kernel_mint() {
    let batch = checked("def composed (a b c : UInt8) : UInt8 := (a - b) * c");
    let context = batch.accepted_context().unwrap();
    let (name, signature, function) = emitted(&context, "composed");
    let token = admit_standalone_scalar(&context, &name, &signature, &function).unwrap();
    for mutation in 0..3 {
        let mut changed = function.clone();
        let Inst::BinOp { op, lhs, rhs, .. } = &mut changed.blocks[0].body[0].inst else {
            panic!()
        };
        match mutation {
            0 => *lhs = ValueId::new(1),
            1 => std::mem::swap(lhs, rhs),
            _ => *op = BinOp::Add,
        }
        assert_eq!(
            admit_standalone_scalar(&context, &name, &signature, &changed).unwrap_err().stage(),
            "kernel-disagreement"
        );
        assert!(token.authenticate(&context, &name, &signature, &changed).is_err());
    }
    let changed_source = checked("def composed (a b c : UInt8) : UInt8 := (b - a) * c");
    let changed_context = changed_source.accepted_context().unwrap();
    assert!(token.authenticate(&changed_context, &name, &signature, &function).is_err());
    assert_eq!(
        admit_standalone_scalar(&changed_context, &name, &signature, &function)
            .unwrap_err()
            .stage(),
        "kernel-disagreement"
    );
}

#[test]
fn entry_order_not_numeric_ssa_identity_determines_kernel_binders() {
    let batch = checked("def composed (a b c : UInt8) : UInt8 := (a - b) * c");
    let context = batch.accepted_context().unwrap();
    let (name, signature, function) = emitted(&context, "composed");
    let original = admit_standalone_scalar(&context, &name, &signature, &function).unwrap();
    let mut renamed = function.clone();
    let rename = |id: &mut ValueId| *id = ValueId::new(100 - id.index());
    for (id, _) in &mut renamed.blocks[0].params {
        rename(id);
    }
    for node in &mut renamed.blocks[0].body {
        for id in &mut node.results {
            rename(id);
        }
        match &mut node.inst {
            Inst::BinOp { lhs, rhs, .. } => {
                rename(lhs);
                rename(rhs);
            }
            Inst::Return { values } => {
                for id in values {
                    rename(id);
                }
            }
            _ => {}
        }
    }
    let token = admit_standalone_scalar(&context, &name, &signature, &renamed).unwrap();
    assert_ne!(token.subject_digest(), original.subject_digest());
    token.authenticate(&context, &name, &signature, &renamed).unwrap();
    assert!(original.authenticate(&context, &name, &signature, &renamed).is_err());
}

#[test]
fn dead_pure_invalid_or_effectful_instructions_never_disappear_behind_defeq() {
    let batch = checked("def composed (a b : UInt8) : UInt8 := (a + b) + a");
    let context = batch.accepted_context().unwrap();
    let (name, signature, function) = emitted(&context, "composed");
    for inst in [
        Inst::Const { ty: Ty::U8, value: Constant::Int(7) },
        Inst::Const { ty: Ty::U8, value: Constant::Int(256) },
        Inst::BinOp { op: BinOp::Sub, ty: Ty::U8, lhs: ValueId::new(0), rhs: ValueId::new(1) },
        Inst::Undef { ty: Ty::U8 },
    ] {
        let mut changed = function.clone();
        changed.blocks[0].body.insert(0, node(inst, 50));
        assert!(admit_standalone_scalar(&context, &name, &signature, &changed).is_err());
    }
    let mut changed = function.clone();
    changed.blocks[0].body.push(node(Inst::Undef { ty: Ty::U8 }, 50));
    assert!(admit_standalone_scalar(&context, &name, &signature, &changed).is_err());
    let mut changed = function.clone();
    let mut fence = node(Inst::Fence { ordering: trust_ir::inst::Ordering::SeqCst }, 50);
    fence.results.clear();
    changed.blocks[0].body.insert(0, fence);
    assert_eq!(
        admit_standalone_scalar(&context, &name, &signature, &changed).unwrap_err().stage(),
        "instruction"
    );
}

#[test]
fn computed_sharing_duplicate_definitions_forward_uses_and_bad_returns_refuse() {
    let batch = checked("def composed (a b : UInt8) : UInt8 := (a + b) + a");
    let context = batch.accepted_context().unwrap();
    let (name, signature, function) = emitted(&context, "composed");
    for mutation in 0..6 {
        let mut changed = function.clone();
        match mutation {
            0 => {
                let Inst::BinOp { rhs, .. } = &mut changed.blocks[0].body[1].inst else { panic!() };
                *rhs = ValueId::new(2);
            }
            1 => changed.blocks[0].body[1].results[0] = ValueId::new(2),
            2 => {
                let Inst::BinOp { lhs, .. } = &mut changed.blocks[0].body[0].inst else { panic!() };
                *lhs = ValueId::new(3);
            }
            3 => changed.blocks[0].params[1].0 = ValueId::new(0),
            4 => changed.blocks[0].body[2].inst = Inst::Return { values: vec![ValueId::new(0)] },
            _ => changed.blocks[0].body[2].results.push(ValueId::new(7)),
        }
        assert!(
            admit_standalone_scalar(&context, &name, &signature, &changed).is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn exact_carriers_canonical_literals_and_neutral_metadata_are_mandatory() {
    let batch = checked("def composed (a b : UInt8) : UInt8 := (a + 3) - b");
    let context = batch.accepted_context().unwrap();
    let (name, signature, function) = emitted(&context, "composed");
    for constant in [Constant::Int(-1), Constant::Int(256), Constant::U128(3)] {
        let mut changed = function.clone();
        changed.blocks[0].body[0].inst = Inst::Const { ty: Ty::U8, value: constant };
        assert!(admit_standalone_scalar(&context, &name, &signature, &changed).is_err());
    }
    let mut changed = function.clone();
    changed.blocks[0].body[0].inst = Inst::Const { ty: Ty::U8, value: Constant::Int(4) };
    assert_eq!(
        admit_standalone_scalar(&context, &name, &signature, &changed).unwrap_err().stage(),
        "kernel-disagreement"
    );
    for ty in [Ty::I8, Ty::U16, Ty::Bool] {
        let mut changed = function.clone();
        let Inst::BinOp { ty: actual, .. } = &mut changed.blocks[0].body[1].inst else { panic!() };
        *actual = ty;
        assert_eq!(
            admit_standalone_scalar(&context, &name, &signature, &changed).unwrap_err().stage(),
            "ir-carrier"
        );
    }
    let mut sig = signature.clone();
    let mut changed = function.clone();
    sig.params[1] = Ty::U16;
    changed.blocks[0].params[1].1 = Ty::U16;
    assert_eq!(
        admit_standalone_scalar(&context, &name, &sig, &changed).unwrap_err().stage(),
        "ir-carrier"
    );
    for mutation in 0..3 {
        let mut changed = function.clone();
        match mutation {
            0 => changed.calling_conv = CallingConv::C,
            1 => changed.blocks[0].body[0].proofs.push(ProofAnnotation::NoOverflow),
            _ => changed.blocks[0].body[0].scope = Some(0),
        }
        assert_eq!(
            admit_standalone_scalar(&context, &name, &signature, &changed).unwrap_err().stage(),
            "standalone-metadata"
        );
    }
}

#[test]
fn expression_domain_is_distinct_from_all_previous_scalar_domains() {
    let batch = checked("def composed (a b : UInt8) : UInt8 := (a + b) + a");
    let context = batch.accepted_context().unwrap();
    let (name, signature, function) = emitted(&context, "composed");
    let token = admit_standalone_scalar(&context, &name, &signature, &function).unwrap();
    let identity = token.identity();
    let root = canonical_json_sha256(&(
        "trust.clean.standalone-source-identity.v1",
        identity.source_closure_sha256(),
        identity.owned_declarations_sha256(),
        &name,
        identity.kernel_payload_sha256(),
    ))
    .unwrap();
    for (domain, expected) in [
        ("wrapping-expression", true),
        ("wrapping-binop", false),
        ("projection", false),
        ("constant-uint", false),
    ] {
        let mut module = Module::new(format!(
            "@trust-internal::clean-standalone-{domain}-gate-subject-v1::lean-identity-sha256={root}"
        ));
        module.func_types.push(signature.clone());
        module.functions.push(function.clone());
        assert_eq!(module.stable_digest() == token.subject_digest(), expected);
    }
}

#[test]
fn source_and_actual_ssa_operation_budget_are_independently_bounded() {
    let mut expression = "a".to_owned();
    for _ in 0..32 {
        expression = format!("({expression} + b)");
    }
    let batch = checked(&format!(
        "def atLimit (a b : UInt8) : UInt8 := {expression}\ndef tooDeep (a b : UInt8) : UInt8 := {expression} + b"
    ));
    let context = batch.accepted_context().unwrap();
    assert_eq!(context.owned_declarations().len(), 2);
    assert!(plan_standalone_clean_origin_body(context.environment(), "tooDeep").is_err());
    let (name, signature, function) = emitted(&context, "atLimit");
    admit_standalone_scalar(&context, &name, &signature, &function).unwrap();
    let mut changed = function.clone();
    let return_index = changed.blocks[0].body.len() - 1;
    let previous = changed.blocks[0].body[return_index - 1].results[0];
    changed.blocks[0].body.insert(
        return_index,
        node(Inst::BinOp { op: BinOp::Add, ty: Ty::U8, lhs: previous, rhs: ValueId::new(0) }, 100),
    );
    changed.blocks[0].body[return_index + 1].inst =
        Inst::Return { values: vec![ValueId::new(100)] };
    assert_eq!(
        admit_standalone_scalar(&context, &name, &signature, &changed).unwrap_err().stage(),
        "expression-bound"
    );
}

#[test]
fn branches_calls_and_unused_mixed_carriers_are_not_expression_grammar() {
    let batch = checked(
        "def branch8 (a b : UInt8) : UInt8 := if a < b then a else b\ndef helper8 (a b : UInt8) : UInt8 := a + b\ndef call8 (a b : UInt8) : UInt8 := helper8 a b\ndef mixed8 (a b : UInt8) (unused : UInt64) : UInt8 := (a + b) + a\ndef composed (a b : UInt8) : UInt8 := (a + b) + a",
    );
    let context = batch.accepted_context().unwrap();
    assert_eq!(context.owned_declarations().len(), 5);
    let (_, signature, function) = emitted(&context, "composed");
    for name in ["branch8", "call8", "mixed8"] {
        let mut changed = function.clone();
        changed.name = name.to_owned();
        assert!(
            admit_standalone_scalar(&context, &Name::from_string(name), &signature, &changed)
                .is_err()
        );
    }
}
