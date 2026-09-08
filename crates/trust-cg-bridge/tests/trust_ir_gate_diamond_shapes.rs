// trust_ir_gate_diamond_shapes.rs — the IN-COMPILER trust-ir gate
// (`verify_trust_ir_output_preserved`, the exact entry
// `emit_trust_ir_module_object_verified` drives) over block-param DIAMONDS.
//
// PROVENANCE (2026-08-31): on the sealed toolchain, `-Ztrust-cg-frontend=
// trust-ir` REFUTES every `if c { x } else { y }` function as a MISCOMPILE
// while straight-line bodies prove clean — e.g. `pub fn pick(v: u32, hi: u32)
// -> u32 { if v > hi { hi } else { v } }` (ay counterexample, gate refusal at
// module emit). The byte-proof lane `module_to_lir_cfg_proven_output.rs`
// proves the SAME diamond shape with its own test-side path-merge, so the
// suspect is the gate's own obligation derivation, not the emitter.
//
// Two properties distinguish the refuted producer shape from the passing
// test-lane shape, and this file pins the 2x2:
//   * VALUE-ID ORDER — the THIR producer numbers the merge block-param (%2)
//     BELOW the cmp (%3); the test lane numbered the cmp first. An SSA walk
//     that assumes ids increase in program order mis-binds the merge.
//   * SIGNEDNESS/WIDTH — the refuted function is u32/Ugt; the test lane was
//     i32/Sgt.
//
// Whichever cell refutes on the working tree is the live bug; if all four
// prove, the sealed refutation was fixed between the seal and HEAD and a
// toolchain rebuild clears it.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![cfg(feature = "ay-proofs")]

use trust_cg_bridge::codegen_backend::{
    BridgeOptimizationLevel, TrustCgCodegenBackend, TrustCgTargetArch,
};
use trust_cg_bridge::verify_output::OutputVerdict;
use trust_cg_bridge::verify_output_trust_ir::{
    TrustIrGateSource, verify_trust_ir_output_preserved,
};
use trust_ir::inst::{ICmpOp, Inst};
use trust_ir::node::InstrNode;
use trust_ir::ty::FuncTy;
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{Block, Function as IrFunction, Module, Ty};

fn backend() -> TrustCgCodegenBackend {
    TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::AArch64, "aarch64-apple-darwin")
        .with_optimization_level(BridgeOptimizationLevel::O0)
}

/// Build `name(a, b) = if a <op> b { then_val } else { else_val }` as the
/// 4-block block-param diamond, with the VALUE-ID ORDER selectable:
///
///   bb0(a=%0, b=%1): %cmp = icmp <op> a, b ; condbr %cmp -> bb1 else bb2
///   bb1:             br bb3(b)     ; the producer's `pick` returns `hi` here
///   bb2:             br bb3(a)
///   bb3(m):          ret m
///
/// `producer_order` numbers the merge param %2 and the cmp %3 — exactly the
/// THIR producer's numbering for `pick` (merge BELOW cmp); otherwise the cmp
/// is %2 and the merge %3 (the historical test-lane numbering).
fn make_diamond(name: &str, ty: Ty, op: ICmpOp, producer_order: bool) -> TrustIrGateSource {
    let mut module = Module::new("diamond_gate");
    module.func_types.push(FuncTy {
        params: vec![ty.clone(), ty.clone()],
        returns: vec![ty.clone()],
        is_vararg: false,
    });
    let mut function = IrFunction::new(FuncId::new(0), name, FuncTyId::new(0), BlockId::new(0));

    let a = ValueId::new(0);
    let b = ValueId::new(1);
    let (m, cmp) = if producer_order {
        (ValueId::new(2), ValueId::new(3))
    } else {
        (ValueId::new(3), ValueId::new(2))
    };

    let mut bb0 = Block::new(BlockId::new(0));
    bb0.params.push((a, ty.clone()));
    bb0.params.push((b, ty.clone()));
    bb0.body
        .push(InstrNode::new(Inst::ICmp { op, ty: ty.clone(), lhs: a, rhs: b }).with_result(cmp));
    bb0.body.push(InstrNode::new(Inst::CondBr {
        cond: cmp,
        then_target: BlockId::new(1),
        then_args: vec![],
        else_target: BlockId::new(2),
        else_args: vec![],
    }));

    let mut bb1 = Block::new(BlockId::new(1));
    bb1.body.push(InstrNode::new(Inst::Br { target: BlockId::new(3), args: vec![b] }));

    let mut bb2 = Block::new(BlockId::new(2));
    bb2.body.push(InstrNode::new(Inst::Br { target: BlockId::new(3), args: vec![a] }));

    let mut bb3 = Block::new(BlockId::new(3));
    bb3.params.push((m, ty.clone()));
    bb3.body.push(InstrNode::new(Inst::Return { values: vec![m] }));

    function.blocks.push(bb0);
    function.blocks.push(bb1);
    function.blocks.push(bb2);
    function.blocks.push(bb3);
    module.functions.push(function);

    TrustIrGateSource { symbol: name.to_string(), module, func_id: FuncId::new(0) }
}

fn assert_gate_proves(source: &TrustIrGateSource) {
    let (verdict, _obj) = verify_trust_ir_output_preserved(source, &backend());
    match verdict {
        OutputVerdict::Proven { .. } => {}
        other => panic!(
            "gate did not prove `{}` (the block-param diamond): {other:?} — if this is \
             Refuted, the in-compiler trust-ir gate is refuting a correct diamond (the \
             sealed-toolchain symptom reproduced on the working tree); if Unknown, the \
             gate's modeled fragment silently lost CondBr/block-param support",
            source.symbol
        ),
    }
}

/// Diagnostic (not an assertion): print the gate's four obligation formulas
/// for the refuted diamond so the wrong side is readable directly.
#[test]
fn dump_diamond_obligation() {
    use trust_cg_bridge::verify_output_trust_ir::trust_ir_gate_obligation;
    let source = make_diamond("d_dump", Ty::U32, ICmpOp::Ugt, true);
    let (_verdict, obj) = verify_trust_ir_output_preserved(&source, &backend());
    let obj = obj.expect("emit succeeded");
    let obligation = trust_ir_gate_obligation(&source, &obj, TrustCgTargetArch::AArch64)
        .expect("obligation derivation succeeded");
    eprintln!("== spec_value ==\n{:?}", obligation.spec_value);
    eprintln!("== spec_reach ==\n{:?}", obligation.spec_reach);
    eprintln!("== machine_value ==\n{:?}", obligation.machine_value);
    eprintln!("== machine_reach ==\n{:?}", obligation.machine_reach);
    eprintln!("== out_width == {:?}", obligation.out_width);
}

#[test]
fn gate_proves_signed_diamond_legacy_value_order() {
    assert_gate_proves(&make_diamond("d_sgt_legacy", Ty::I32, ICmpOp::Sgt, false));
}

#[test]
fn gate_proves_signed_diamond_producer_value_order() {
    assert_gate_proves(&make_diamond("d_sgt_producer", Ty::I32, ICmpOp::Sgt, true));
}

#[test]
fn gate_proves_unsigned_diamond_legacy_value_order() {
    assert_gate_proves(&make_diamond("d_ugt_legacy", Ty::U32, ICmpOp::Ugt, false));
}

/// The exact sealed-toolchain refutation shape: u32, Ugt, merge param numbered
/// below the cmp — `pub fn pick(v: u32, hi: u32) -> u32 { if v > hi { hi }
/// else { v } }` as the producer emits it.
#[test]
fn gate_proves_unsigned_diamond_producer_value_order() {
    assert_gate_proves(&make_diamond("d_ugt_producer", Ty::U32, ICmpOp::Ugt, true));
}

/// A NINE-argument function whose result depends on the STACK-passed ninth
/// argument: `add9(a0..a8) = a0 + a8`. The spec binds parameter 9 to the
/// little-endian byte read of the initial memory at the ABI classifier's own
/// offset ([SP0 + 0]), under the well-formed-stack ambient, and the machine
/// side's `ldr` of the incoming slot builds the matching read.
///
/// HISTORY: before the stack-address select normalizer this was a frontier
/// pin — the obligation was correct but ay's QF_ABV lane did not converge on
/// the raw per-byte store chains (Unknown at 120s and 480s, never Refuted).
/// The normalizer resolves `Select(Store(m, SP+c1, v), SP+c2)` structurally
/// (pure modular arithmetic: adding the shared SP base is a bijection), and
/// the proof now CONVERGES — so this pin asserts `Proven` outright.
#[test]
fn gate_proves_nine_arg_function_with_stack_argument() {
    use trust_ir::inst::BinOp as IrBinOp;
    let mut module = Module::new("stack9");
    module.func_types.push(FuncTy {
        params: vec![Ty::U64; 9],
        returns: vec![Ty::U64],
        is_vararg: false,
    });
    let mut f = IrFunction::new(FuncId::new(0), "add9", FuncTyId::new(0), BlockId::new(0));
    let mut b0 = Block::new(BlockId::new(0));
    for i in 0..9u32 {
        b0.params.push((ValueId::new(i), Ty::U64));
    }
    b0.body = vec![
        InstrNode::new(Inst::BinOp {
            op: IrBinOp::Add,
            ty: Ty::U64,
            lhs: ValueId::new(0),
            rhs: ValueId::new(8),
        })
        .with_result(ValueId::new(9)),
        InstrNode::new(Inst::Return { values: vec![ValueId::new(9)] }),
    ];
    f.blocks.push(b0);
    module.functions.push(f);

    let source = TrustIrGateSource { symbol: "add9".to_string(), module, func_id: FuncId::new(0) };
    let (verdict, obj) = verify_trust_ir_output_preserved(&source, &backend());
    assert!(obj.is_some(), "the nine-arg function must lower and emit object bytes");
    assert!(
        matches!(verdict, OutputVerdict::Proven { .. }),
        "the stack-argument binding + select normalizer must PROVE add9 \
         (got {verdict:?})"
    );
}
