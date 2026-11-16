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
use trust_ir::inst::{BinOp, ICmpOp, Inst};
use trust_ir::node::InstrNode;
use trust_ir::ty::FuncTy;
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{Block, Constant, Function as IrFunction, Module, Ty};

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
        abi: None,
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

    TrustIrGateSource {
        abi_cross_check: None,
        symbol: name.to_string(),
        module: module.into(),
        func_id: FuncId::new(0),
    }
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

// ===========================================================================
// WS7.11 (F-114) — the COMPUTING-ARM diamond, and the refutation class it
// belonged to, as a PERMANENT fixture.
//
// PROVENANCE. The F1 scout probe `nl4.rs` (`#![no_core]` + minicore) defined
//
//     #[no_mangle] pub extern "C" fn sel(a: u64, b: u64) -> u64 {
//         if a == b { a ^ 1 } else { b }
//     }
//
// and on stale stage1 `06ce3dd35` (2026-08-30) the build failed with "REFUSED:
// function `sel` is a MISCOMPILE (Refuted) — emitted bytes do not equal the
// trust-ir semantics for fn `sel` (ay found a counterexample input —
// miscompile)". The probe lived in a session scratchpad, so nothing pinned it.
// The four cells above do not cover it: they compare with `Sgt`/`Ugt`, and
// their then-arm is a bare block argument. `sel` compares with `Eq`, and its
// then-arm COMPUTES (`xor` against a materialized constant) before the merge.
//
// RE-MEASURED 2026-09-19 against the gate at `4020807a91` (`make_sel_shape`
// is the IR the stage1 producer dumps for `sel` byte-for-byte, value ids
// included): `Proven`. So the 2026-08-30 refutation was fixed between that
// stage1 and HEAD, and these cells keep it fixed. The grade is ay-only: in the
// compiler (`kernel-recheck`) `sel` is `[VALIDATED]`, not `[PROVED]` — the
// kernel re-check covers no integer comparison yet — so the default strict
// gate still refuses it on GRADE; the run-make `trust-cg-f1-diamond-native`
// pins that refusal and the emitted object's native behaviour. Each cell here
// is paired with a mutated LOWERING of the same shape (swapped `Brif`
// targets, arm constant 1 -> 2) that must come back `Refuted` — never
// `Unknown` — so a regression that made the gate unable to say no on this
// shape fails here too.
// ===========================================================================

/// Build `name(a, b) = if a <op> b { a <arm> 1 } else { b }` — the `sel`
/// diamond, whose then-arm COMPUTES before the merge:
///
///   bb0(a=%0, b=%1): %c = icmp <op> a, b ; condbr %c -> bb1 else bb2
///   bb1:             %k = const 1 ; %r = <arm> a, %k ; br bb3(%r)
///   bb2:             br bb3(b)
///   bb3(m):          ret m
///
/// `producer_order` numbers exactly as the THIR producer does for `sel`
/// (`-Ztrust-dump=ir`): the merge param `%2` BELOW the cmp `%3`, then the
/// constant `%4` and the arm result `%5`. Otherwise program order: cmp `%2`,
/// constant `%3`, arm `%4`, merge `%5`.
fn make_diamond_with_arm_op(
    name: &str,
    ty: Ty,
    op: ICmpOp,
    arm: BinOp,
    producer_order: bool,
) -> TrustIrGateSource {
    let mut module = Module::new("diamond_gate");
    module.func_types.push(FuncTy {
        params: vec![ty.clone(), ty.clone()],
        returns: vec![ty.clone()],
        is_vararg: false,
        abi: None,
    });
    let mut function = IrFunction::new(FuncId::new(0), name, FuncTyId::new(0), BlockId::new(0));

    let a = ValueId::new(0);
    let b = ValueId::new(1);
    let (m, cmp, k, r) = if producer_order {
        (ValueId::new(2), ValueId::new(3), ValueId::new(4), ValueId::new(5))
    } else {
        (ValueId::new(5), ValueId::new(2), ValueId::new(3), ValueId::new(4))
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
    bb1.body.push(
        InstrNode::new(Inst::Const { ty: ty.clone(), value: Constant::Int(1) }).with_result(k),
    );
    bb1.body.push(
        InstrNode::new(Inst::BinOp { op: arm, ty: ty.clone(), lhs: a, rhs: k }).with_result(r),
    );
    bb1.body.push(InstrNode::new(Inst::Br { target: BlockId::new(3), args: vec![r] }));

    let mut bb2 = Block::new(BlockId::new(2));
    bb2.body.push(InstrNode::new(Inst::Br { target: BlockId::new(3), args: vec![b] }));

    let mut bb3 = Block::new(BlockId::new(3));
    bb3.params.push((m, ty.clone()));
    bb3.body.push(InstrNode::new(Inst::Return { values: vec![m] }));

    function.blocks.push(bb0);
    function.blocks.push(bb1);
    function.blocks.push(bb2);
    function.blocks.push(bb3);
    module.functions.push(function);

    TrustIrGateSource {
        abi_cross_check: None,
        symbol: name.to_string(),
        module: module.into(),
        func_id: FuncId::new(0),
    }
}

/// The exact F-114 probe function: `sel(a: u64, b: u64) -> u64 { if a == b {
/// a ^ 1 } else { b } }`, in the producer's own value order.
fn make_sel_shape() -> TrustIrGateSource {
    make_diamond_with_arm_op("sel", Ty::U64, ICmpOp::Eq, BinOp::Xor, true)
}

#[test]
fn gate_proves_sel_f114_probe_shape() {
    assert_gate_proves(&make_sel_shape());
}

#[test]
fn gate_proves_sel_shape_legacy_value_order() {
    assert_gate_proves(&make_diamond_with_arm_op(
        "sel_legacy",
        Ty::U64,
        ICmpOp::Eq,
        BinOp::Xor,
        false,
    ));
}

#[test]
fn gate_proves_eq_xor_arm_diamond_u32() {
    assert_gate_proves(&make_diamond_with_arm_op(
        "d_eq_xor_u32",
        Ty::U32,
        ICmpOp::Eq,
        BinOp::Xor,
        true,
    ));
}

#[test]
fn gate_proves_eq_xor_arm_diamond_u64() {
    assert_gate_proves(&make_diamond_with_arm_op(
        "d_eq_xor_u64",
        Ty::U64,
        ICmpOp::Eq,
        BinOp::Xor,
        true,
    ));
}

#[test]
fn gate_proves_eq_add_arm_diamond_u32() {
    assert_gate_proves(&make_diamond_with_arm_op(
        "d_eq_add_u32",
        Ty::U32,
        ICmpOp::Eq,
        BinOp::Add,
        true,
    ));
}

#[test]
fn gate_proves_eq_add_arm_diamond_u64() {
    assert_gate_proves(&make_diamond_with_arm_op(
        "d_eq_add_u64",
        Ty::U64,
        ICmpOp::Eq,
        BinOp::Add,
        true,
    ));
}

#[test]
fn gate_proves_ne_xor_arm_diamond_u32() {
    assert_gate_proves(&make_diamond_with_arm_op(
        "d_ne_xor_u32",
        Ty::U32,
        ICmpOp::Ne,
        BinOp::Xor,
        true,
    ));
}

#[test]
fn gate_proves_ne_xor_arm_diamond_u64() {
    assert_gate_proves(&make_diamond_with_arm_op(
        "d_ne_xor_u64",
        Ty::U64,
        ICmpOp::Ne,
        BinOp::Xor,
        true,
    ));
}

#[test]
fn gate_proves_ne_add_arm_diamond_u32() {
    assert_gate_proves(&make_diamond_with_arm_op(
        "d_ne_add_u32",
        Ty::U32,
        ICmpOp::Ne,
        BinOp::Add,
        true,
    ));
}

#[test]
fn gate_proves_ne_add_arm_diamond_u64() {
    assert_gate_proves(&make_diamond_with_arm_op(
        "d_ne_add_u64",
        Ty::U64,
        ICmpOp::Ne,
        BinOp::Add,
        true,
    ));
}

// ---------------------------------------------------------------------------
// The NEGATIVE TWINS: a WRONG lowering of the same shape, injected through the
// `test-hooks` lowering hook, must be REFUTED — never `Unknown`. `Unknown` would
// mean the gate cannot tell a miscompiled diamond from one it failed to model,
// which is exactly the ambiguity F-114 left open.
// ---------------------------------------------------------------------------

#[cfg(feature = "test-hooks")]
mod mutated_lowering {
    use trust_cg_bridge::module_to_lir::lower_module_to_lir;
    use trust_cg_bridge::verify_output_trust_ir::verify_trust_ir_output_preserved_with_lowering;
    use trust_cg_lower::function::Function as LirFunction;
    use trust_cg_lower::instructions::Opcode;

    use super::*;

    /// The shipping converter, unchanged: the hook's own CONTROL.
    fn shipping(module: &Module, func: FuncId) -> Result<LirFunction, String> {
        lower_module_to_lir(module, func).map_err(|e| format!("{e:?}"))
    }

    /// The shipping lowering with every `Brif`'s targets exchanged: the arms
    /// run under the opposite condition.
    fn swapped_brif(module: &Module, func: FuncId) -> Result<LirFunction, String> {
        let mut lir = shipping(module, func)?;
        let mut swapped = 0usize;
        for block in lir.blocks.values_mut() {
            for inst in &mut block.instructions {
                if let Opcode::Brif { then_dest, else_dest, .. } = &mut inst.opcode {
                    std::mem::swap(then_dest, else_dest);
                    swapped += 1;
                }
            }
        }
        assert_eq!(swapped, 1, "the diamond lowers to exactly one Brif; the mutation missed");
        Ok(lir)
    }

    /// The shipping lowering with the arm's constant `1` replaced by `2`.
    fn arm_constant_two(module: &Module, func: FuncId) -> Result<LirFunction, String> {
        let mut lir = shipping(module, func)?;
        let mut changed = 0usize;
        for block in lir.blocks.values_mut() {
            for inst in &mut block.instructions {
                if let Opcode::Iconst { imm, .. } = &mut inst.opcode
                    && *imm == 1
                {
                    *imm = 2;
                    changed += 1;
                }
            }
        }
        assert_eq!(changed, 1, "the arm constant `1` must appear exactly once in the LIR");
        Ok(lir)
    }

    fn verdict_with(
        source: &TrustIrGateSource,
        lower: fn(&Module, FuncId) -> Result<LirFunction, String>,
    ) -> OutputVerdict {
        let (verdict, obj) =
            verify_trust_ir_output_preserved_with_lowering(source, &backend(), lower);
        assert!(
            obj.is_some(),
            "`{}`: the (mutated) lowering must still emit an object",
            source.symbol
        );
        verdict
    }

    fn cells() -> Vec<TrustIrGateSource> {
        let mut cells = vec![make_sel_shape()];
        for (ty, tn) in [(Ty::U32, "u32"), (Ty::U64, "u64")] {
            for (op, on) in [(ICmpOp::Eq, "eq"), (ICmpOp::Ne, "ne")] {
                for (arm, an) in [(BinOp::Xor, "xor"), (BinOp::Add, "add")] {
                    cells.push(make_diamond_with_arm_op(
                        &format!("m_{on}_{an}_{tn}"),
                        ty.clone(),
                        op,
                        arm,
                        true,
                    ));
                }
            }
        }
        cells
    }

    /// CONTROL: the hook with the SHIPPING lowering must still prove — so a
    /// `Refuted` below is caused by the mutation, not by the hook path.
    #[test]
    fn hook_with_shipping_lowering_still_proves_sel() {
        let source = make_sel_shape();
        let verdict = verdict_with(&source, shipping);
        assert!(
            matches!(verdict, OutputVerdict::Proven { .. }),
            "the hook with the unmodified converter must agree with the production entry \
             point; got {verdict:?}"
        );
    }

    #[test]
    fn swapped_brif_lowering_of_computing_arm_diamond_is_refuted() {
        for source in cells() {
            let verdict = verdict_with(&source, swapped_brif);
            assert!(
                matches!(verdict, OutputVerdict::Refuted { .. }),
                "`{}`: a lowering with the Brif targets swapped computes the WRONG arm on \
                 every input and must be Refuted (never Unknown); got {verdict:?}",
                source.symbol
            );
        }
    }

    // -----------------------------------------------------------------------
    // Batch review: the OTHER half of F-114. The 2026-08-30 failure was the gate
    // REFUTING CORRECT CODE, so a twin that only ever demands `Refuted` cannot see
    // that class come back. These lowerings are rewritten but still CORRECT (or
    // correct on exactly the cells named), and the gate must PROVE them — it
    // compares semantics, not the shape of the shipping lowering.
    // -----------------------------------------------------------------------

    /// The compare negated (`Equal` <-> `NotEqual`) AND the `Brif` targets swapped:
    /// a different machine program with the same semantics on every input.
    fn negated_compare_swapped_targets(
        module: &Module,
        func: FuncId,
    ) -> Result<LirFunction, String> {
        use trust_cg_lower::instructions::IntCC;
        let mut lir = swapped_brif(module, func)?;
        let mut negated = 0usize;
        for block in lir.blocks.values_mut() {
            for inst in &mut block.instructions {
                if let Opcode::Icmp { cond } = &mut inst.opcode {
                    *cond = match *cond {
                        IntCC::Equal => IntCC::NotEqual,
                        IntCC::NotEqual => IntCC::Equal,
                        other => panic!("the diamond compares Eq/Ne only; got {other:?}"),
                    };
                    negated += 1;
                }
            }
        }
        assert_eq!(negated, 1, "the diamond lowers to exactly one Icmp; the mutation missed");
        Ok(lir)
    }

    /// The ELSE edge passes `a` where the source passes `b`. The else arm runs when
    /// the compare is FALSE: for an `Eq` diamond that is `a != b`, so the mutant returns
    /// the wrong operand; for a `Ne` diamond it is `a == b`, so the mutant is EQUIVALENT
    /// — which only a gate that reasons about the path condition can tell.
    fn else_edge_passes_a(module: &Module, func: FuncId) -> Result<LirFunction, String> {
        let mut lir = shipping(module, func)?;
        let entry = &lir.blocks[&lir.entry_block];
        let [(a, _), (b, _)] = entry.params[..] else {
            panic!("the diamond's entry block binds exactly (a, b): {:?}", entry.params)
        };
        let mut rewritten = 0usize;
        for block in lir.blocks.values_mut() {
            for inst in &mut block.instructions {
                if matches!(inst.opcode, Opcode::Copy) && inst.args == [b] {
                    inst.args = vec![a];
                    rewritten += 1;
                }
            }
        }
        assert_eq!(rewritten, 1, "exactly one edge copy forwards `b` (the else edge)");
        Ok(lir)
    }

    #[test]
    fn equivalent_rewrite_negated_compare_and_swapped_targets_is_proven() {
        for source in cells() {
            let verdict = verdict_with(&source, negated_compare_swapped_targets);
            assert!(
                matches!(verdict, OutputVerdict::Proven { .. }),
                "`{}`: negating the compare AND swapping the Brif targets is the same \
                 function; the gate must PROVE it (a Refuted here is the 2026-08-30 F-114 \
                 class — correct code refuted); got {verdict:?}",
                source.symbol
            );
        }
    }

    #[test]
    fn else_edge_operand_mutation_is_refuted_on_eq_and_proven_on_ne() {
        for source in cells() {
            let op = source.module.functions[0].blocks[0]
                .body
                .iter()
                .find_map(|n| match n.inst {
                    Inst::ICmp { op, .. } => Some(op),
                    _ => None,
                })
                .expect("the diamond compares");
            let verdict = verdict_with(&source, else_edge_passes_a);
            match op {
                ICmpOp::Eq => assert!(
                    matches!(verdict, OutputVerdict::Refuted { .. }),
                    "`{}`: on an Eq diamond the else arm runs when a != b, so returning `a` \
                     is wrong and must be Refuted (never Unknown); got {verdict:?}",
                    source.symbol
                ),
                ICmpOp::Ne => assert!(
                    matches!(verdict, OutputVerdict::Proven { .. }),
                    "`{}`: on a Ne diamond the else arm runs only when a == b, so returning \
                     `a` is EQUIVALENT and must be Proven, never Refuted; got {verdict:?}",
                    source.symbol
                ),
                other => panic!("unexpected compare {other:?}"),
            }
        }
    }

    #[test]
    fn arm_constant_mutated_lowering_of_computing_arm_diamond_is_refuted() {
        for source in cells() {
            let verdict = verdict_with(&source, arm_constant_two);
            assert!(
                matches!(verdict, OutputVerdict::Refuted { .. }),
                "`{}`: a lowering whose then-arm uses 2 instead of 1 is wrong whenever the \
                 then-arm runs and must be Refuted (never Unknown); got {verdict:?}",
                source.symbol
            );
        }
    }
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
        abi: None,
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

    let source = TrustIrGateSource {
        abi_cross_check: None,
        symbol: "add9".to_string(),
        module: module.into(),
        func_id: FuncId::new(0),
    };
    let (verdict, obj) = verify_trust_ir_output_preserved(&source, &backend());
    assert!(obj.is_some(), "the nine-arg function must lower and emit object bytes");
    assert!(
        matches!(verdict, OutputVerdict::Proven { .. }),
        "the stack-argument binding + select normalizer must PROVE add9 \
         (got {verdict:?})"
    );
}
