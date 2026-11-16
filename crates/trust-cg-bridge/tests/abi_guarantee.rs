// abi_guarantee.rs — O0, the ABI guarantee, on today's proven-output gates
// (increment-5 step 5.0, docs/design/2026-10-01-step2-inc5-real-calls-retarget.md).
//
// THE HOLE (design fact V1). Both gates read only the RETURN VALUE at a `RET`.
// Nothing checked that the bytes hand back what an AAPCS64 caller relies on —
// and on F1 every caller of a gated function is LLVM-built code. So bytes that
// clobbered X19, left SP unbalanced, or returned through a lost LR were
// certified as long as X0 was right; and the MIR bundle gate's PHASE 0 admitted
// such a callee for composition on value equality alone, while
// `model_local_call` ASSUMED it preserves X19-X29 and SP at every composed `bl`.
//
// THE OBLIGATION (O0). At every reachable `RET`, and at every relocated tail
// `b`: X19-X28, X29, SP and the low halves of D8-D15 equal their entry values;
// the return target equals the entry X30; on Darwin, X18 is never written.
//
// HOW THESE TESTS BITE. Each one takes REAL bytes trust-cg emitted, splices an
// ABI violation into them through the `test-hooks` text corruptor (machine
// side only — the spec is untouched), and demands `Refuted` naming the
// violated location. Every negative test has a CONTROL through the same splice
// harness that must stay Proven, so a refusal cannot be the harness breaking
// the object. On the code before step 5.0 every negative below was `Proven`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![cfg(all(feature = "ay-proofs", feature = "test-hooks"))]

use trust_cg_bridge::codegen_backend::{
    BridgeOptimizationLevel, TrustCgCodegenBackend, TrustCgTargetArch,
};
use trust_cg_bridge::verify_output::{
    EmitPolicy, OutputVerdict, VerifyError, bundle_gate_admitted_callees,
    emit_objects_verified_reported_with_backend, verify_output_preserved_with_backend,
    with_text_corruptor,
};
use trust_cg_bridge::verify_output_trust_ir::{
    TrustIrGateSource, verify_trust_ir_output_preserved,
};
use trust_disasm::{ControlFlow, Opcode, decode_aarch64};
use trust_ir::inst::{BinOp as IrBinOp, Inst};
use trust_ir::node::InstrNode;
use trust_ir::ty::FuncTy;
use trust_ir::value::{BlockId as IrBlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{Block, Constant, Function as IrFunction, Module, Producer, Ty as IrTy};
use trust_types::{
    BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, VerifiableBody, VerifiableFunction,
};

// ---------------------------------------------------------------------------
// Assembler-derived AArch64 words.
// ---------------------------------------------------------------------------

/// `nop` — the splice harness control.
const NOP: u32 = 0xD503_201F;
/// `movz x19, #0x1234` — clobbers a callee-saved register.
const MOVZ_X19: u32 = 0xD282_4693;
/// `str x19, [sp, #-16]!` / `ldr x19, [sp], #16` — a correct save/restore pair.
const SAVE_X19: u32 = 0xF81F_0FF3;
const RESTORE_X19: u32 = 0xF841_07F3;
/// `sub sp, sp, #16` — leaves SP unbalanced at the `RET`.
const SUB_SP_16: u32 = 0xD100_43FF;
/// `movz x18, #1` — writes the Darwin platform register.
const MOVZ_X18: u32 = 0xD280_0032;
/// `mov x18, x18` (`orr x18, xzr, x18`) — a value-preserving WRITE of X18.
const MOV_X18_X18: u32 = 0xAA12_03F2;
/// `fmov d8, x0` — overwrites the callee-saved low half of V8.
const FMOV_D8_X0: u32 = 0x9E67_0008;
/// `fmov d16, x0` — overwrites a caller-saved SIMD register (control).
const FMOV_D16_X0: u32 = 0x9E67_0010;

// ---------------------------------------------------------------------------
// Backends.
// ---------------------------------------------------------------------------

fn darwin() -> TrustCgCodegenBackend {
    TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::AArch64, "aarch64-apple-darwin")
        .with_optimization_level(BridgeOptimizationLevel::O0)
}

fn linux() -> TrustCgCodegenBackend {
    TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::AArch64, "aarch64-unknown-linux-gnu")
        .with_optimization_level(BridgeOptimizationLevel::O0)
}

// ---------------------------------------------------------------------------
// The splice harness.
// ---------------------------------------------------------------------------

fn word_at(code: &[u8], off: usize) -> u32 {
    u32::from_le_bytes(code[off..off + 4].try_into().expect("4-byte word"))
}

/// A readable listing of `code`, for failure messages.
fn listing(code: &[u8], base: u64) -> String {
    (0..code.len() / 4)
        .map(|i| {
            let pc = base + 4 * i as u64;
            let word = word_at(code, 4 * i);
            match decode_aarch64(&word.to_le_bytes(), pc) {
                Ok(insn) => format!("  {pc:#06x}: {word:08x} {:?}", insn.opcode),
                Err(_) => format!("  {pc:#06x}: {word:08x} <undecodable>"),
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Does `code` contain a `bl`? (Selects the caller in a two-function bundle.)
fn has_bl(code: &[u8]) -> bool {
    (0..code.len() / 4).any(|i| word_at(code, 4 * i) & 0xFC00_0000 == 0x9400_0000)
}

/// Insert `words` IMMEDIATELY BEFORE the first `RET` of a straight-line body.
///
/// Insertion keeps every original instruction in place and in order, so the
/// value the function computes is unchanged and any verdict change is the
/// spliced words' doing. It is only valid on a straight-line body (nothing
/// PC-relative to displace), which is CHECKED, not assumed.
fn splice_before_ret(code: &mut Vec<u8>, base: u64, words: &[u32]) {
    let mut off = 0usize;
    while off + 4 <= code.len() {
        let pc = base + off as u64;
        let insn = decode_aarch64(&word_at(code, off).to_le_bytes(), pc)
            .unwrap_or_else(|e| panic!("emitted text must decode at {pc:#x}: {e:?}"));
        if insn.opcode == Opcode::Ret {
            let bytes: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
            code.splice(off..off, bytes);
            return;
        }
        assert_eq!(
            insn.flow,
            ControlFlow::Fallthrough,
            "splice_before_ret needs a straight-line body; {:?} at {pc:#x} is not \
             Fallthrough:\n{}",
            insn.opcode,
            listing(code, base)
        );
        off += 4;
    }
    panic!("no RET in the emitted text:\n{}", listing(code, base));
}

/// A text corruptor splicing `words` before the `RET` of every LEAF text the
/// gate extracts (any text containing a `bl` is left alone).
fn leaf_splice(words: &'static [u32]) -> impl Fn(&mut Vec<u8>, u64) {
    move |code: &mut Vec<u8>, base: u64| {
        if !has_bl(code) {
            splice_before_ret(code, base, words);
        }
    }
}

// ---------------------------------------------------------------------------
// MIR-gate functions (`VerifiableFunction`).
// ---------------------------------------------------------------------------

fn wrap(name: &str, body: VerifiableBody) -> VerifiableFunction {
    VerifiableFunction {
        name: name.into(),
        def_path: format!("abi_guarantee::{name}"),
        span: SourceSpan::default(),
        body,
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// `fn add(a: i32, b: i32) -> i32 { a + b }` — a pure leaf PHASE 0 can admit.
fn add_fn(name: &str) -> VerifiableFunction {
    wrap(
        name,
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::i32(),
            datatype_defs: Default::default(),
        },
    )
}

/// `fn <name>(a: i32, b: i32) -> i32 { <callee>(a, b) }` — a real `bl`.
fn caller_fn(name: &str, callee: &str) -> VerifiableFunction {
    wrap(
        name,
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: callee.into(),
                        args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        unwind: trust_types::UnwindEdge::Unreachable,
                        is_foreign: false,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        callee_key: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::i32(),
            datatype_defs: Default::default(),
        },
    )
}

// ---------------------------------------------------------------------------
// F1-gate functions (trust-ir).
// ---------------------------------------------------------------------------

/// `pub fn f1_leaf(x: u64) -> u64 { x ^ 0x55 }`, alone in its module.
fn f1_leaf() -> TrustIrGateSource {
    let mut module = Module::new("abi_guarantee_f1");
    module.func_types.push(FuncTy {
        params: vec![IrTy::U64],
        returns: vec![IrTy::U64],
        is_vararg: false,
        abi: None,
    });
    let mut leaf = IrFunction::new(FuncId::new(0), "f1_leaf", FuncTyId::new(0), IrBlockId::new(0));
    leaf.producer = Some(Producer::TRust);
    let (x, mask, out) = (ValueId::new(0), ValueId::new(1), ValueId::new(2));
    let mut bb = Block::new(IrBlockId::new(0));
    bb.params.push((x, IrTy::U64));
    bb.body.push(
        InstrNode::new(Inst::Const { ty: IrTy::U64, value: Constant::Int(0x55) }).with_result(mask),
    );
    bb.body.push(
        InstrNode::new(Inst::BinOp { op: IrBinOp::Xor, ty: IrTy::U64, lhs: x, rhs: mask })
            .with_result(out),
    );
    bb.body.push(InstrNode::new(Inst::Return { values: vec![out] }));
    leaf.blocks.push(bb);
    module.functions.push(leaf);
    TrustIrGateSource {
        abi_cross_check: None,
        symbol: "f1_leaf".to_string(),
        module: module.into(),
        func_id: FuncId::new(0),
    }
}

fn f1_verdict(backend: &TrustCgCodegenBackend, words: &'static [u32]) -> OutputVerdict {
    let source = f1_leaf();
    with_text_corruptor(leaf_splice(words), || verify_trust_ir_output_preserved(&source, backend).0)
}

fn mir_leaf_verdict(words: &'static [u32]) -> OutputVerdict {
    let func = add_fn("abi_leaf");
    with_text_corruptor(leaf_splice(words), || {
        verify_output_preserved_with_backend(&func, &darwin())
    })
}

// ---------------------------------------------------------------------------
// Assertions.
// ---------------------------------------------------------------------------

/// The verdict is `Refuted` by O0, naming `slot`.
#[track_caller]
fn assert_abi_refuted(verdict: &OutputVerdict, slot: &str) {
    match verdict {
        OutputVerdict::Refuted { detail } => {
            assert!(
                detail.contains("ABI guarantee (O0)") && detail.contains(slot),
                "the refutation must be O0's and name {slot}: {detail}"
            );
        }
        other => panic!("an ABI violation of {slot} must be Refuted, never {other:?}"),
    }
}

/// A splice-harness control: the verdict is Proven, at kernel grade when the
/// kernel re-check is compiled in (the splice must not cost the grade).
#[track_caller]
fn assert_control_proven(verdict: &OutputVerdict, what: &str) {
    assert!(verdict.is_proven(), "{what}: the control must stay Proven, got {verdict:?}");
    #[cfg(feature = "kernel-recheck")]
    assert!(verdict.is_kernel_proved(), "{what}: the control must stay [PROVED], got {verdict:?}");
}

// ===========================================================================
// The six step-5.0 tests.
// ===========================================================================

/// PHASE 0 admits a callee only when its own verdict is Proven, and a Proven
/// verdict now includes O0 over the callee's bytes. A callee whose bytes compute
/// the right sum but clobber X19 is therefore EXCLUDED from the composition
/// environment, so no caller composes it on an assumption it breaks — and the
/// bundle is refused with the callee Refuted. Before step 5.0 the callee was
/// admitted on value equality alone (design fact V1).
#[test]
fn callee_clobbering_x19_is_excluded_from_the_env() {
    let backend = darwin();
    let funcs = vec![add_fn("add"), caller_fn("caller_add", "add")];

    // CONTROL: through the same harness, a NOP splice keeps `add` admitted and
    // the bundle clears the gate with both functions Proven.
    let admitted =
        with_text_corruptor(leaf_splice(&[NOP]), || bundle_gate_admitted_callees(&funcs, &backend));
    assert_eq!(admitted, vec!["add".to_string()], "control: the clean callee is admitted");
    let (objects, report) = with_text_corruptor(leaf_splice(&[NOP]), || {
        emit_objects_verified_reported_with_backend(&funcs, EmitPolicy::AllowUnknown, &backend)
    })
    .expect("control: the bundle with a clean callee clears the gate");
    assert_eq!(objects.len(), 2);
    assert_eq!(report.unknown, 0, "control: the caller is composed, not Unknown: {report}");

    // The X19-clobbering callee is not admitted...
    let admitted = with_text_corruptor(leaf_splice(&[MOVZ_X19]), || {
        bundle_gate_admitted_callees(&funcs, &backend)
    });
    assert!(admitted.is_empty(), "a callee that clobbers X19 must be excluded: {admitted:?}");

    // ...and the bundle is refused with the callee itself Refuted by O0.
    let result = with_text_corruptor(leaf_splice(&[MOVZ_X19]), || {
        emit_objects_verified_reported_with_backend(&funcs, EmitPolicy::AllowUnknown, &backend)
    });
    match result {
        Err(VerifyError::Refuted { function, detail }) => {
            assert_eq!(function, "add");
            assert!(detail.contains("ABI guarantee (O0)") && detail.contains("X19"), "{detail}");
        }
        other => panic!("the X19-clobbering callee must be Refuted, got {other:?}"),
    }
}

/// The `bl` writes X30 := pc+4 and AAPCS64 does not oblige the callee to hand
/// it back, so a caller must save and restore its own LR. Removing the restore
/// from REAL caller bytes (the `ldp x29, x30` epilogue keeps reloading X29 but
/// discards the X30 half into XZR) makes the `RET` return through a clobbered
/// LR: Refuted. Before step 5.0 the executor ignored X30 after a call and RET
/// read only X0, so this caller was certified.
#[test]
fn caller_without_lr_restore_is_refuted() {
    let backend = darwin();
    let funcs = vec![add_fn("add"), caller_fn("caller_add", "add")];

    // Rewrite the epilogue load of X30 (an LDP whose second register is X30)
    // so it loads into XZR instead. Applies to the caller only (it has the bl).
    let drop_lr_restore = |code: &mut Vec<u8>, base: u64| {
        if !has_bl(code) {
            return;
        }
        for off in (0..code.len()).step_by(4) {
            let word = word_at(code, off);
            let insn = decode_aarch64(&word.to_le_bytes(), base + off as u64).expect("decodes");
            if insn.opcode == Opcode::Ldp && (word >> 10) & 0x1F == 30 {
                let rewritten = word | (0x1F << 10);
                code[off..off + 4].copy_from_slice(&rewritten.to_le_bytes());
                return;
            }
        }
        panic!("the caller restores LR with no `ldp _, x30`:\n{}", listing(code, base));
    };

    // CONTROL: the unmodified caller clears the gate.
    let (_, report) =
        emit_objects_verified_reported_with_backend(&funcs, EmitPolicy::AllowUnknown, &backend)
            .expect("control: the real caller restores LR and clears the gate");
    assert_eq!(report.unknown, 0, "control: {report}");

    let result = with_text_corruptor(drop_lr_restore, || {
        emit_objects_verified_reported_with_backend(&funcs, EmitPolicy::AllowUnknown, &backend)
    });
    match result {
        Err(VerifyError::Refuted { function, detail }) => {
            assert_eq!(function, "caller_add");
            assert!(
                detail.contains("ABI guarantee (O0)") && detail.contains("return target"),
                "the refutation must name the lost return address: {detail}"
            );
        }
        other => panic!("a caller that does not restore LR must be Refuted, got {other:?}"),
    }
}

/// A `RET` that leaves SP 16 bytes below its entry value hands the LLVM-built
/// caller a corrupted stack. The return VALUE is unchanged, so before step 5.0
/// this was certified.
#[test]
fn ret_with_unbalanced_sp_is_refuted() {
    assert_control_proven(&mir_leaf_verdict(&[NOP]), "NOP splice");
    assert_abi_refuted(&mir_leaf_verdict(&[SUB_SP_16]), "SP");
}

/// The F1 gate, with no call anywhere: a leaf whose bytes clobber X19 is
/// Refuted. A splice that SAVES X19, clobbers it and RESTORES it computes the
/// same function and preserves X19, so it stays Proven at the same grade — the
/// obligation is the exit value, discharged structurally through the frame slot.
#[test]
fn f1_leaf_clobbering_x19_is_refuted() {
    let backend = darwin();
    assert_control_proven(&f1_verdict(&backend, &[NOP]), "NOP splice");
    assert_control_proven(
        &f1_verdict(&backend, &[SAVE_X19, MOVZ_X19, RESTORE_X19]),
        "save; clobber; restore of X19",
    );
    assert_abi_refuted(&f1_verdict(&backend, &[MOVZ_X19]), "X19");
}

/// Darwin reserves X18: it must never be WRITTEN, not merely be equal at the
/// `RET` — a value-preserving `mov x18, x18` is refused too. On the generic
/// AAPCS64 (ELF) platform X18 is an ordinary temporary, so the same write is
/// not an O0 violation there.
#[test]
fn darwin_x18_write_is_refuted() {
    let backend = darwin();
    assert_control_proven(&f1_verdict(&backend, &[NOP]), "NOP splice");
    assert_abi_refuted(&f1_verdict(&backend, &[MOVZ_X18]), "X18");
    assert_abi_refuted(&f1_verdict(&backend, &[MOV_X18_X18]), "X18");

    let elf = linux();
    assert_control_proven(&f1_verdict(&elf, &[NOP]), "ELF NOP splice");
    assert_control_proven(&f1_verdict(&elf, &[MOVZ_X18]), "X18 write on ELF");
}

/// AAPCS64 makes the low 64 bits of V8-V15 callee-saved. Overwriting D8 is
/// Refuted; overwriting D16 (caller-saved) is not an O0 violation.
#[test]
fn d8_low_half_clobber_is_refuted() {
    let backend = darwin();
    assert_control_proven(&f1_verdict(&backend, &[FMOV_D16_X0]), "D16 is caller-saved");
    assert_abi_refuted(&f1_verdict(&backend, &[FMOV_D8_X0]), "D8");
    // The same through the MIR gate.
    assert_abi_refuted(&mir_leaf_verdict(&[FMOV_D8_X0]), "D8");
}
