// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Trust (WS5.20, F-096): the standalone gate for the SCALAR vocabulary — a
//! connective of two comparisons (`STANDALONE.p20`), a `&&&`/`|||` tree
//! (`p15`) and Lean's TOTAL division (`p13`). Each reader derives everything
//! from the actual SSA; the frozen `trust_spec_elab` producers (or the
//! carrier's own `div`) mint the term; the kernel decides whole-term defeq with
//! the untouched declaration at the exact result carrier.

use clean_kernel::Name;
use trust_certify::lean_source_batch::{
    AcceptedLeanSourceContext, CheckedLeanSourceBatch, LeanSourceInput,
};
use trust_clean_ir_gate::standalone::admit_standalone_scalar;
use trust_clean_origin::emit::plan_standalone_scalar_body_for_name;
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{FuncId, FuncTyId, ValueId};
use trust_ir::{BinOp, Constant, Function, ICmpOp, Inst, Producer};

fn checked(source: &str) -> CheckedLeanSourceBatch {
    let batch = CheckedLeanSourceBatch::check(
        vec![LeanSourceInput {
            module: "Scalars".to_owned(),
            path: "Scalars.lean".to_owned(),
            source: source.to_owned(),
        }],
        false,
    );
    assert!(batch.accepted_context().is_some(), "{:?}", batch.errors());
    batch
}

fn emitted(context: &AcceptedLeanSourceContext<'_>, name: &str) -> (Name, FuncTy, Function) {
    let decl = Name::from_string(name);
    let plan = plan_standalone_scalar_body_for_name(context.environment(), &decl)
        .unwrap_or_else(|refusal| panic!("{name}: {refusal:?}"));
    let signature = trust_clean_ir::trust_ir_func_ty(plan.signature()).unwrap();
    let function =
        trust_clean_ir::emit_standalone_scalar_function(&plan, FuncId::new(0), FuncTyId::new(0))
            .unwrap();
    (decl, signature, function)
}

fn admits(context: &AcceptedLeanSourceContext<'_>, name: &str) -> (FuncTy, Function) {
    let (decl, signature, function) = emitted(context, name);
    let token = admit_standalone_scalar(context, &decl, &signature, &function)
        .unwrap_or_else(|refusal| panic!("{name}: {refusal}"));
    token.authenticate(context, &decl, &signature, &function).unwrap();
    let mut published = function.clone();
    published.id = FuncId::new(3);
    published.ty = FuncTyId::new(4);
    published.producer = Some(Producer::Clean);
    token.authenticate_published(context, &decl, &signature, &function, &published).unwrap();
    (signature, function)
}

fn stage_of(
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

fn run(function: &Function, ty: &Ty, args: &[u64]) -> InterpretValue {
    let args: Vec<_> =
        args.iter().map(|a| InterpretValue::int(ty.clone(), i128::from(*a)).unwrap()).collect();
    Interpreter::new().execute_function(function, args).unwrap().returns[0].clone()
}

/// POSITIVE: every UInt carrier, both connectives, and the probes verbatim.
#[test]
fn connectives_bitwise_trees_and_total_division_mint_at_every_carrier() {
    let mut source = String::new();
    for w in [8, 16, 32, 64] {
        let t = format!("UInt{w}");
        source.push_str(&format!("def both{w} (a b c : {t}) : Bool := a < b && b < c\n"));
        source.push_str(&format!("def either{w} (a b : {t}) : Bool := a == b || b <= a\n"));
        source.push_str(&format!("def mask{w} (a b : {t}) : {t} := (a &&& b) ||| 1\n"));
        source.push_str(&format!("def quot{w} (a b : {t}) : {t} := a / b\n"));
    }
    let batch = checked(&source);
    let context = batch.accepted_context().unwrap();
    for w in [8, 16, 32, 64] {
        for prefix in ["both", "either", "mask", "quot"] {
            admits(&context, &format!("{prefix}{w}"));
        }
    }
}

/// The emitted bodies compute Lean's values — in particular Lean's `x / 0 = 0`,
/// with `UDiv` never seeing a zero divisor.
#[test]
fn the_admitted_bodies_compute_the_lean_values() {
    let batch = checked(
        "def both (a b c : UInt64) : Bool := a < b && b < c\n\
         def mask (a b : UInt64) : UInt64 := (a &&& b) ||| 1\n\
         def quot (a b : UInt64) : UInt64 := a / b\n",
    );
    let context = batch.accepted_context().unwrap();
    let (_, both) = admits(&context, "both");
    assert_eq!(run(&both, &Ty::U64, &[3, 4, 5]).as_bool(), Some(true));
    assert_eq!(run(&both, &Ty::U64, &[3, 5, 4]).as_bool(), Some(false));
    let (_, mask) = admits(&context, "mask");
    assert_eq!(run(&mask, &Ty::U64, &[12, 10]).as_int().unwrap().as_unsigned(), 9);
    let (_, quot) = admits(&context, "quot");
    assert_eq!(run(&quot, &Ty::U64, &[7, 2]).as_int().unwrap().as_unsigned(), 3);
    assert_eq!(run(&quot, &Ty::U64, &[7, 0]).as_int().unwrap().as_unsigned(), 0);
    assert_eq!(
        run(&quot, &Ty::U64, &[u64::MAX, 3]).as_int().unwrap().as_unsigned(),
        u128::from(u64::MAX / 3)
    );
}

fn binop_of(function: &mut Function, index: usize) -> &mut BinOp {
    function.blocks[0]
        .body
        .iter_mut()
        .filter_map(|node| match &mut node.inst {
            Inst::BinOp { op, .. } => Some(op),
            _ => None,
        })
        .nth(index)
        .expect("the body has that BinOp")
}

/// MUTATIONS, per shape: a connective or bitwise operator swapped, a comparison
/// weakened, a literal changed — kernel disagreements; a dropped zero guard, a
/// swapped guard, `sdiv` for `udiv` and a signed comparison leaf — reader
/// refusals before any mint.
#[test]
fn every_scalar_mutant_is_refused_by_name() {
    let batch = checked(
        "def both (a b c : UInt64) : Bool := a < b && b < c\n\
         def mask (a b : UInt64) : UInt64 := (a &&& b) ||| 1\n\
         def quot (a b : UInt64) : UInt64 := a / b\n",
    );
    let context = batch.accepted_context().unwrap();
    // Connective: And -> Or.
    assert_eq!(stage_of(&context, "both", |f| *binop_of(f, 0) = BinOp::Or), "kernel-disagreement");
    // A comparison leaf weakened `<` -> `<=`.
    assert_eq!(
        stage_of(&context, "both", |f| {
            if let Inst::ICmp { op, .. } = &mut f.blocks[0].body[1].inst {
                *op = ICmpOp::Ule;
            }
        }),
        "kernel-disagreement"
    );
    // A signed comparison leaf: no producer, refused by the reader.
    assert_eq!(
        stage_of(&context, "both", |f| {
            if let Inst::ICmp { op, .. } = &mut f.blocks[0].body[0].inst {
                *op = ICmpOp::Slt;
            }
        }),
        "instruction"
    );
    // Bitwise: the inner `&&&` respelled `|||`.
    assert_eq!(stage_of(&context, "mask", |f| *binop_of(f, 0) = BinOp::Or), "kernel-disagreement");
    // Bitwise: the literal 1 -> 3.
    assert_eq!(
        stage_of(&context, "mask", |f| {
            for node in &mut f.blocks[0].body {
                if let Inst::Const { value: Constant::Int(v), .. } = &mut node.inst {
                    *v = 3;
                }
            }
        }),
        "kernel-disagreement"
    );
    // Bitwise: Xor is outside this reader.
    assert_eq!(stage_of(&context, "mask", |f| *binop_of(f, 1) = BinOp::Xor), "instruction");
    // Division: `sdiv` for `udiv`.
    assert_eq!(stage_of(&context, "quot", |f| *binop_of(f, 0) = BinOp::SDiv), "division-body");
    // Division: the zero guard's safe-divisor arms swapped.
    assert_eq!(
        stage_of(&context, "quot", |f| {
            if let Inst::Select { then_val, else_val, .. } = &mut f.blocks[0].body[3].inst {
                std::mem::swap(then_val, else_val);
            }
        }),
        "division-body"
    );
    // Division: the zero guard DROPPED — `q = udiv x y; ret q`.
    assert_eq!(
        stage_of(&context, "quot", |f| {
            let x = f.blocks[0].params[0].0;
            let y = f.blocks[0].params[1].0;
            let q = ValueId::new(9);
            f.blocks[0].body = vec![
                trust_ir::node::InstrNode::new(Inst::BinOp {
                    op: BinOp::UDiv,
                    ty: Ty::U64,
                    lhs: x,
                    rhs: y,
                })
                .with_results(vec![q]),
                trust_ir::node::InstrNode::new(Inst::Return { values: vec![q] }),
            ];
        }),
        "division-body"
    );
    // Division: operands swapped (y / x) passes the reader and fails the kernel.
    assert_eq!(
        stage_of(&context, "quot", |f| {
            let x = f.blocks[0].params[0].0;
            let y = f.blocks[0].params[1].0;
            for node in &mut f.blocks[0].body {
                match &mut node.inst {
                    Inst::BinOp { op: BinOp::UDiv, lhs, .. } => *lhs = y,
                    Inst::ICmp { lhs, .. } => *lhs = x,
                    Inst::Select { else_val, .. } if *else_val == y => *else_val = x,
                    _ => {}
                }
            }
        }),
        "kernel-disagreement"
    );
}
