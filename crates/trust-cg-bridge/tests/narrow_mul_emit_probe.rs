// narrow_mul_emit_probe.rs — SCRATCH DIAGNOSTIC (session 2026-08-31): the
// stage1 F1 lane refuses `fn pack(a: u8, b: u8) -> u16 { (b as u16) * 256 +
// (a as u16) }` with "verification emission produced no shippable object
// bytes" — the gate's early Unknown swallows emit_object's real error. This
// probe lowers the same narrow checked-mul shape and calls emit_object
// directly so the error is readable. Keep or fold into a real pin once the
// root cause lands.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![cfg(feature = "ay-proofs")]

use trust_cg_bridge::codegen_backend::{
    BridgeOptimizationLevel, TrustCgCodegenBackend, TrustCgTargetArch,
};
use trust_cg_bridge::module_to_lir::lower_module_to_lir;
use trust_ir::inst::{Inst, OverflowOp};
use trust_ir::node::InstrNode;
use trust_ir::ty::FuncTy;
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{Block, Constant, Function as IrFunction, Module, Ty};

#[test]
fn narrow_u16_checked_mul_emits_object_bytes() {
    // u16 checked mul idiom: %3,%4 = mul.overflow u16 %0, %2(const 256);
    // select/assert; ret %3 — the exact shape the producer emits for
    // `(b as u16) * 256` with overflow checks on.
    let mut module = Module::new("t");
    module.func_types.push(FuncTy {
        params: vec![Ty::U16, Ty::U16],
        returns: vec![Ty::U16],
        is_vararg: false,
    });
    let mut f = IrFunction::new(FuncId::new(0), "pack", FuncTyId::new(0), BlockId::new(0));
    let mut b0 = Block::new(BlockId::new(0));
    b0.params.push((ValueId::new(0), Ty::U16));
    b0.params.push((ValueId::new(1), Ty::U16));
    b0.body = vec![
        InstrNode::new(Inst::Const { ty: Ty::U16, value: Constant::Int(256) })
            .with_result(ValueId::new(2)),
        InstrNode::new(Inst::Overflow {
            op: OverflowOp::MulOverflow,
            ty: Ty::U16,
            lhs: ValueId::new(0),
            rhs: ValueId::new(2),
        })
        .with_results([ValueId::new(3), ValueId::new(4)]),
        InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(false) })
            .with_result(ValueId::new(5)),
        InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
            .with_result(ValueId::new(6)),
        InstrNode::new(Inst::Select {
            ty: Ty::Bool,
            cond: ValueId::new(4),
            then_val: ValueId::new(5),
            else_val: ValueId::new(6),
        })
        .with_result(ValueId::new(7)),
        InstrNode::new(Inst::Assert { cond: ValueId::new(7) }),
        InstrNode::new(Inst::Return { values: vec![ValueId::new(3)] }),
    ];
    f.blocks.push(b0);
    module.functions.push(f);

    let lir = lower_module_to_lir(&module, FuncId::new(0)).expect("narrow mul lowers to LIR");
    let backend =
        TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::AArch64, "aarch64-apple-darwin")
            .with_optimization_level(BridgeOptimizationLevel::O0);
    match backend.emit_object(&[lir]) {
        Ok(obj) => assert!(!obj.is_empty(), "object bytes must be non-empty"),
        Err(e) => panic!("emit_object failed on the u16 widened-mul LIR: {e:?}"),
    }
}

/// The REAL producer shape for `fn pack(a: u8, b: u8) -> u16 { (b as u16) *
/// 256 + (a as u16) }`: u8 params ZEXT'd to u16 (a NARROW-to-NARROW extend)
/// before the widened mul and the add.
#[test]
fn u8_to_u16_zext_mul_add_emits_object_bytes() {
    use trust_ir::inst::{BinOp, CastOp};
    let mut module = Module::new("t");
    module.func_types.push(FuncTy {
        params: vec![Ty::U8, Ty::U8],
        returns: vec![Ty::U16],
        is_vararg: false,
    });
    let mut f = IrFunction::new(FuncId::new(0), "pack8", FuncTyId::new(0), BlockId::new(0));
    let mut b0 = Block::new(BlockId::new(0));
    b0.params.push((ValueId::new(0), Ty::U8));
    b0.params.push((ValueId::new(1), Ty::U8));
    b0.body = vec![
        InstrNode::new(Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::U8,
            dst_ty: Ty::U16,
            operand: ValueId::new(1),
        })
        .with_result(ValueId::new(2)),
        InstrNode::new(Inst::Const { ty: Ty::U16, value: Constant::Int(256) })
            .with_result(ValueId::new(3)),
        InstrNode::new(Inst::Overflow {
            op: OverflowOp::MulOverflow,
            ty: Ty::U16,
            lhs: ValueId::new(2),
            rhs: ValueId::new(3),
        })
        .with_results([ValueId::new(4), ValueId::new(5)]),
        InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(false) })
            .with_result(ValueId::new(6)),
        InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
            .with_result(ValueId::new(7)),
        InstrNode::new(Inst::Select {
            ty: Ty::Bool,
            cond: ValueId::new(5),
            then_val: ValueId::new(6),
            else_val: ValueId::new(7),
        })
        .with_result(ValueId::new(8)),
        InstrNode::new(Inst::Assert { cond: ValueId::new(8) }),
        InstrNode::new(Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::U8,
            dst_ty: Ty::U16,
            operand: ValueId::new(0),
        })
        .with_result(ValueId::new(9)),
        InstrNode::new(Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ty: Ty::U16,
            lhs: ValueId::new(4),
            rhs: ValueId::new(9),
        })
        .with_results([ValueId::new(10), ValueId::new(11)]),
        InstrNode::new(Inst::Select {
            ty: Ty::Bool,
            cond: ValueId::new(11),
            then_val: ValueId::new(6),
            else_val: ValueId::new(7),
        })
        .with_result(ValueId::new(12)),
        InstrNode::new(Inst::Assert { cond: ValueId::new(12) }),
        InstrNode::new(Inst::Return { values: vec![ValueId::new(10)] }),
    ];
    f.blocks.push(b0);
    module.functions.push(f);

    let lir = lower_module_to_lir(&module, FuncId::new(0)).expect("u8->u16 shape lowers to LIR");
    let backend =
        TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::AArch64, "aarch64-apple-darwin")
            .with_optimization_level(BridgeOptimizationLevel::O0);
    match backend.emit_object(&[lir]) {
        Ok(obj) => assert!(!obj.is_empty(), "object bytes must be non-empty"),
        Err(e) => panic!("emit_object failed on the u8->u16 zext/mul/add LIR: {e:?}"),
    }
}
