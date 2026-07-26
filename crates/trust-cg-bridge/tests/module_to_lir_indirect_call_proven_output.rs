// module_to_lir_indirect_call_proven_output.rs — the FIRST slice of the dispatch
// half of the Module -> LIR converter: lower a KNOWN-target INDIRECT call.
//
//     fn ir_addf(x: i32, y: i32) -> i32 { x + y }         // FuncId 1 (callee)
//     global ir_addf : ptr                                // the callee's symbol
//     fn ir_ci(a: i32, b: i32) -> i32 {                   // FuncId 0 (caller)
//         let f: fn(i32,i32)->i32 = &ir_addf;             //   GlobalAddr(ir_addf)
//         f(a, b)                                         //   CallIndirect(f, a, b)
//     }
//
// This is the OPPOSITE lowering of the direct real-call slice
// (`module_to_lir_real_call_proven_output.rs`). There, `add(a,b)` is a DIRECT
// `Inst::Call` -> `Opcode::Call` -> `Bl ir_add` + `ARM64_RELOC_BRANCH26`. Here,
// `f(a,b)` is `Inst::GlobalAddr(ir_addf)` + `Inst::CallIndirect(f, a, b)`:
//   * `GlobalAddr` -> `Opcode::GlobalRef { name: "ir_addf" }` -> `ADRP X, ir_addf@PAGE`
//     (`ARM64_RELOC_PAGE21`) + `ADD X, X, ir_addf@PAGEOFF` (`ARM64_RELOC_PAGEOFF12`);
//   * `CallIndirect` -> `Opcode::CallIndirect` -> `BLR X` — a genuine INDIRECT
//     branch through the fn-pointer register (NOT a direct `Bl`).
// This is the primitive closures / trait-object dispatch will build on.
//
// The proof MIRRORS the direct-call composition (`verify_output::model_local_call`),
// extended to trace an INDIRECT (BLR) target back to its GlobalRef symbol from the
// REAL emitted PAGE21/PAGEOFF12 relocations (never the IR's claim):
//   (1) decode the caller's OWN emitted bytes;
//   (2) at the `ADRP` carrying a PAGE21 reloc naming `S` into register `Rd`, tag
//       `Rd` as holding `SymbolAddr(S)`; the following `ADD` (PAGEOFF12, same reg)
//       confirms it; ANY other write to `Rd` INVALIDATES the tag (soundness);
//   (3) at the `BLR Xn`, if `Xn` is tagged `SymbolAddr(ir_addf)` — a KNOWN target
//       naming a local pure callee — SUBSTITUTE that callee's derived pure output
//       (`W0 = X0 + X1` trunc32) into X0 using the CURRENT arg registers, and
//   (4) HAVOC caller-saved registers X0..X18 + flags (the soundness-critical step).
// ay then proves the composed output equals `a + b` for ALL inputs (UNSAT of the
// negation). A MANDATORY SAT negative control (`a + b + 1`) proves it has teeth.
//
// SOUNDNESS (why composing the KNOWN indirect target is sound):
//   * the fn-pointer's symbol is read from the REAL PAGE21/PAGEOFF12 relocations
//     the LINKER resolves — the ADRP+ADD provably materialize `ir_addf`'s address,
//     so the `BLR` through that register provably jumps to `ir_addf`'s bytes. This
//     is byte-derived (the artifact + its relocations), NOT the IR's claim.
//   * `ir_addf` is itself in the single-register scalar-pure fragment (its bytes
//     are proven == `x + y` by the same proven-output machinery), so standing its
//     derived formula in for "what the resolved BLR computes" is exact — the SAME
//     composition the direct `Bl` case uses.
//   * havocing caller-saved registers means any post-call read of a register the
//     bytes wrongly assume survives becomes a FRESH variable ay refutes.
//   * FAIL-CLOSED: a BLR whose target register is NOT tagged with a known-symbol
//     address (an OPEN target — an incoming fn-pointer arg, a vtable-slot load, a
//     closure env field) is not composed; the executor errors. That is the future
//     havoc-only (vtable) slice, deliberately out of scope here.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![cfg(feature = "ay-proofs")]

use std::collections::HashMap;

use ay::{BigInt, Logic, Solver, Term};
use trust_cg_bridge::codegen_backend::{TrustCgCodegenBackend, TrustCgTargetArch};
use trust_cg_bridge::{lower_trust_ir_function_to_lir, lower_trust_ir_function_to_lir_real_calls};
use trust_disasm::{Instruction as DisasmInst, Opcode, Operand, decode_aarch64};
use trust_machine_sem::{Aarch64Semantics, Effect, Flags, MachineState, Semantics};
use trust_types::{Formula, Sort};

use trust_ir::inst::{BinOp, Inst};
use trust_ir::node::InstrNode;
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId, FuncTyId, GlobalId, ValueId};
use trust_ir::{Block, Constant, Function as IrFunction, Global, Linkage, Module};

// ---------------------------------------------------------------------------
// Build the KNOWN-target indirect-call module: ci(a,b) = (&ir_addf)(a,b).
// ---------------------------------------------------------------------------

fn make_indirect_module() -> Module {
    let mut module = Module::new("indirect_call_module");
    // FuncTy 0: caller(i32,i32)->i32 ; FuncTy 1: callee(i32,i32)->i32.
    module.func_types.push(FuncTy {
        params: vec![Ty::I32, Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    module.func_types.push(FuncTy {
        params: vec![Ty::I32, Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });

    // A module global whose NAME is the callee function symbol: its address is the
    // fn-pointer value. (This is exactly how a frontend lowers `&ir_addf`.)
    module.globals.push(Global {
        name: "ir_addf".to_string(),
        ty: Ty::Ptr,
        mutable: false,
        initializer: None,
        linkage: Linkage::External,
        tls: None,
    });

    // --- callee: ir_addf(x, y) = x + y  (FuncId 1) ---
    let mut add = IrFunction::new(FuncId::new(1), "ir_addf", FuncTyId::new(1), BlockId::new(0));
    let (x, y, s) = (ValueId::new(10), ValueId::new(11), ValueId::new(12));
    let mut ab = Block::new(BlockId::new(0));
    ab.params.push((x, Ty::I32));
    ab.params.push((y, Ty::I32));
    ab.body.push(
        InstrNode::new(Inst::BinOp { op: BinOp::Add, ty: Ty::I32, lhs: x, rhs: y }).with_result(s),
    );
    ab.body.push(InstrNode::new(Inst::Return { values: vec![s] }));
    add.blocks.push(ab);

    // --- caller: ci(a, b) = (let f = &ir_addf; f(a, b))  (FuncId 0) ---
    let mut caller = IrFunction::new(FuncId::new(0), "ir_ci", FuncTyId::new(0), BlockId::new(0));
    let (a, b, fptr, called) =
        (ValueId::new(0), ValueId::new(1), ValueId::new(2), ValueId::new(3));
    let mut cb = Block::new(BlockId::new(0));
    cb.params.push((a, Ty::I32));
    cb.params.push((b, Ty::I32));
    cb.body
        .push(InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(0) }).with_result(fptr));
    cb.body.push(
        InstrNode::new(Inst::CallIndirect {
            callee: fptr,
            sig: FuncTyId::new(1),
            args: vec![a, b],
            calling_conv: Default::default(),
        })
        .with_result(called),
    );
    cb.body.push(InstrNode::new(Inst::Return { values: vec![called] }));
    caller.blocks.push(cb);

    module.functions.push(caller);
    module.functions.push(add);
    module
}

// ---------------------------------------------------------------------------
// Emit / Mach-O helpers.
// ---------------------------------------------------------------------------

fn host_triple() -> String {
    if cfg!(target_vendor = "apple") {
        if cfg!(target_arch = "aarch64") {
            "aarch64-apple-darwin".to_string()
        } else {
            "x86_64-apple-darwin".to_string()
        }
    } else {
        TrustCgTargetArch::host().triple().to_string()
    }
}

fn backend() -> TrustCgCodegenBackend {
    TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::host(), host_triple())
}

/// Emit the CALLER (real indirect call) and return the FULL object bytes.
fn emit_caller_object(module: &Module) -> Vec<u8> {
    let caller = &module.functions[0];
    let lir = lower_trust_ir_function_to_lir_real_calls(module, caller)
        .expect("lower_trust_ir_function_to_lir_real_calls failed for indirect caller");
    backend().emit_object(&[lir]).expect("emit_object (caller) failed")
}

/// Emit the CALLEE alone and return the FULL object bytes.
fn emit_callee_object(module: &Module) -> Vec<u8> {
    let callee = &module.functions[1];
    let lir = lower_trust_ir_function_to_lir(module, callee)
        .expect("lower_trust_ir_function_to_lir failed for callee");
    backend().emit_object(&[lir]).expect("emit_object (callee) failed")
}

fn macho_text(obj: &[u8]) -> Option<(Vec<u8>, u64)> {
    let rd_u32 =
        |o: usize| -> Option<u32> { Some(u32::from_le_bytes(obj.get(o..o + 4)?.try_into().ok()?)) };
    let rd_u64 =
        |o: usize| -> Option<u64> { Some(u64::from_le_bytes(obj.get(o..o + 8)?.try_into().ok()?)) };
    if rd_u32(0)? != 0xfeed_facf {
        return None;
    }
    let ncmds = rd_u32(16)?;
    let mut cmd_off = 32usize;
    for _ in 0..ncmds {
        let cmd = rd_u32(cmd_off)?;
        let cmdsize = rd_u32(cmd_off + 4)? as usize;
        if cmd == 0x19 {
            let nsects = rd_u32(cmd_off + 64)?;
            let mut sec = cmd_off + 72;
            for _ in 0..nsects {
                let sname = &obj[sec..sec + 16];
                if sname.starts_with(b"__text\0") {
                    let addr = rd_u64(sec + 32)?;
                    let size = rd_u64(sec + 40)? as usize;
                    let offset = rd_u32(sec + 48)? as usize;
                    return Some((obj.get(offset..offset + size)?.to_vec(), addr));
                }
                sec += 80;
            }
        }
        cmd_off += cmdsize;
    }
    None
}

/// Whether the callee symbol appears in the object's symbol table.
fn object_defines_symbol(obj: &[u8], want: &str) -> bool {
    let rd_u32 =
        |o: usize| -> Option<u32> { Some(u32::from_le_bytes(obj.get(o..o + 4)?.try_into().ok()?)) };
    if rd_u32(0) != Some(0xfeed_facf) {
        return false;
    }
    let Some(ncmds) = rd_u32(16) else { return false };
    let mut cmd_off = 32usize;
    let (mut symoff, mut nsyms, mut stroff, mut strsize) = (0usize, 0u32, 0usize, 0usize);
    for _ in 0..ncmds {
        let Some(cmd) = rd_u32(cmd_off) else { return false };
        let Some(cmdsize) = rd_u32(cmd_off + 4) else { return false };
        if cmdsize == 0 {
            return false;
        }
        if cmd == 0x2 {
            symoff = rd_u32(cmd_off + 8).unwrap_or(0) as usize;
            nsyms = rd_u32(cmd_off + 12).unwrap_or(0);
            stroff = rd_u32(cmd_off + 16).unwrap_or(0) as usize;
            strsize = rd_u32(cmd_off + 20).unwrap_or(0) as usize;
        }
        cmd_off += cmdsize as usize;
    }
    for i in 0..nsyms as usize {
        let e = symoff + i * 16;
        let Some(strx) = rd_u32(e) else { continue };
        let start = stroff + strx as usize;
        let end = stroff + strsize;
        let mut p = start;
        let mut s = String::new();
        while p < end {
            let Some(&c) = obj.get(p) else { break };
            if c == 0 {
                break;
            }
            s.push(c as char);
            p += 1;
        }
        let s = s.strip_prefix('_').unwrap_or(&s);
        if s == want {
            return true;
        }
    }
    false
}

/// The relocation kinds the indirect-call tracer cares about, keyed by in-section
/// byte offset. Mirrors the gate's byte-derived-symbol discipline, extended for the
/// ADRP/ADD (PAGE21/PAGEOFF12) pair that materializes a fn-pointer.
#[derive(Clone, Debug, PartialEq, Eq)]
enum SymReloc {
    /// `ARM64_RELOC_PAGE21` (3) on an ADRP: the 4KB page of `symbol`.
    Page21(String),
    /// `ARM64_RELOC_PAGEOFF12` (4) on an ADD: the in-page offset of `symbol`.
    Pageoff12(String),
}

/// Parse the `__text` PAGE21 (type 3) + PAGEOFF12 (type 4) relocations: in-section
/// byte offset -> the `SymReloc` naming the symbol (leading `_` stripped). Only
/// external relocations to a defined symbol are recorded.
fn parse_page_relocs(obj: &[u8]) -> HashMap<u64, SymReloc> {
    let rd_u32 = |o: usize| -> u32 { u32::from_le_bytes(obj[o..o + 4].try_into().expect("u32")) };
    assert_eq!(rd_u32(0), 0xfeed_facf, "not a Mach-O 64 object");
    let ncmds = rd_u32(16);
    let mut cmd_off = 32usize;
    let (mut text_reloff, mut text_nreloc) = (0usize, 0u32);
    let (mut symoff, mut nsyms, mut stroff, mut strsize) = (0usize, 0u32, 0usize, 0usize);
    for _ in 0..ncmds {
        let cmd = rd_u32(cmd_off);
        let cmdsize = rd_u32(cmd_off + 4) as usize;
        if cmd == 0x19 {
            let nsects = rd_u32(cmd_off + 64);
            let mut sec = cmd_off + 72;
            for _ in 0..nsects {
                if obj[sec..sec + 16].starts_with(b"__text\0") {
                    text_reloff = rd_u32(sec + 56) as usize;
                    text_nreloc = rd_u32(sec + 60);
                }
                sec += 80;
            }
        } else if cmd == 0x2 {
            symoff = rd_u32(cmd_off + 8) as usize;
            nsyms = rd_u32(cmd_off + 12);
            stroff = rd_u32(cmd_off + 16) as usize;
            strsize = rd_u32(cmd_off + 20) as usize;
        }
        cmd_off += cmdsize;
    }
    let sym_name = |idx: u32| -> String {
        assert!(idx < nsyms, "reloc symbol index out of range");
        let e = symoff + idx as usize * 16;
        let strx = rd_u32(e) as usize;
        let (start, end) = (stroff + strx, stroff + strsize);
        let mut p = start;
        let mut s = String::new();
        while p < end {
            let c = obj[p];
            if c == 0 {
                break;
            }
            s.push(c as char);
            p += 1;
        }
        s.strip_prefix('_').unwrap_or(&s).to_string()
    };
    let mut map = HashMap::new();
    for i in 0..text_nreloc as usize {
        let e = text_reloff + i * 8;
        let r_address = rd_u32(e) as u64;
        let w1 = rd_u32(e + 4);
        let r_symbolnum = w1 & 0x00ff_ffff;
        let r_extern = (w1 >> 27) & 1;
        let r_type = (w1 >> 28) & 0xf;
        if r_extern != 1 {
            continue;
        }
        match r_type {
            3 => {
                map.insert(r_address, SymReloc::Page21(sym_name(r_symbolnum)));
            }
            4 => {
                map.insert(r_address, SymReloc::Pageoff12(sym_name(r_symbolnum)));
            }
            _ => {}
        }
    }
    map
}

fn decode_all(code: &[u8], base: u64) -> Vec<(u64, DisasmInst)> {
    let mut out = Vec::new();
    let mut pc = base;
    while (pc - base) as usize + 4 <= code.len() {
        let off = (pc - base) as usize;
        let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
        if let Ok(insn) = decode_aarch64(&bytes, pc) {
            out.push((pc, insn));
        }
        pc += 4;
    }
    out
}

fn count_blr(code: &[u8], base: u64) -> usize {
    decode_all(code, base).iter().filter(|(_, i)| i.opcode == Opcode::Blr).count()
}

fn count_bl_direct(code: &[u8], base: u64) -> usize {
    decode_all(code, base).iter().filter(|(_, i)| i.opcode == Opcode::Bl).count()
}

/// The destination GPR index of a decoded instruction (operand 0), if it is a
/// plain GPR write. Used to invalidate a stale symbol-address tag when the tracked
/// register is overwritten by anything other than the confirming ADD.
fn dst_gpr_index(insn: &DisasmInst) -> Option<u8> {
    match insn.operands().next() {
        Some(Operand::Reg(r)) if matches!(r.kind, trust_disasm::operand::RegKind::Gpr) => {
            Some(r.index)
        }
        _ => None,
    }
}

// ===========================================================================
// TRACING PATH-MERGING EXECUTOR — the machine-side model of a KNOWN-target BLR.
//
// Extends the direct-call executor with a symbol-address register tracer: an ADRP
// (PAGE21 reloc -> S) into Rd tentatively tags Rd = SymbolAddr(S); the following
// ADD (PAGEOFF12 reloc -> S, Rd == Rn) confirms it; ANY other write to a tracked
// register invalidates the tag (soundness). At a BLR, the target register must be
// tagged with a KNOWN local pure symbol, else FAIL CLOSED.
// ===========================================================================

/// `ir_addf`'s derived pure output over X0, X1: `trunc32(X0) + trunc32(X1)`,
/// zero-extended into the 64-bit return slot (the same formula the gate derives).
fn callee_add_output() -> Formula {
    let w = |n: u32| Formula::BvExtract {
        inner: Box::new(Formula::Var(format!("X{n}"), Sort::BitVec(64))),
        high: 31,
        low: 0,
    };
    let sum32 = Formula::BvAdd(Box::new(w(0)), Box::new(w(1)), 32);
    Formula::BvZeroExt(Box::new(sum32), 32)
}

fn substitute_var(f: &Formula, name: &str, replacement: &Formula) -> Formula {
    match f {
        Formula::Var(n, _) if n == name => replacement.clone(),
        leaf @ (Formula::Var(..) | Formula::SymVar(..)) => leaf.clone(),
        other => {
            other.clone().map_children(&mut |child| substitute_var(&child, name, replacement))
        }
    }
}

/// Symbolically execute the caller's emitted bytes, MODELING the `BLR` by tracing
/// its target register to a known GlobalRef symbol and composing that callee.
/// Returns W0 after RET. Panics (=> test failure) on any fail-closed condition, so
/// the composition can NEVER silently model an unknown target.
fn composed_indirect_output(
    code: &[u8],
    base: u64,
    relocs: &HashMap<u64, SymReloc>,
    known_pure: &str,
) -> Formula {
    let sem = Aarch64Semantics;
    let mut state = MachineState::symbolic();
    // Per-GPR symbol-address tag: reg index -> materialized symbol name.
    let mut sym_reg: HashMap<u8, String> = HashMap::new();
    let mut pc = base;
    let mut steps = 0u32;
    let mut call_tag = 0u32;
    // Assert we actually reached a composed BLR (no vacuous straight-line pass).
    let mut composed_a_blr = false;

    loop {
        let off = (pc - base) as usize;
        assert!(off + 4 <= code.len(), "ran past __text end without RET");
        let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
        let insn = decode_aarch64(&bytes, pc).expect("decode_aarch64 failed");
        let sec_off = pc - base;

        if insn.opcode == Opcode::Ret {
            break;
        }

        let effects =
            sem.effects(&state, &insn).unwrap_or_else(|e| panic!("effects failed at {pc:#x}: {e:?}"));
        let is_call = effects.iter().any(|e| matches!(e, Effect::Call { .. }));

        // ---- Symbol-address materialization tracer (ADRP + ADD). ----
        if insn.opcode == Opcode::Adrp {
            let rd = dst_gpr_index(&insn).expect("ADRP has a GPR destination");
            match relocs.get(&sec_off) {
                Some(SymReloc::Page21(sym)) => {
                    // Tentatively tag Rd with the symbol's page address.
                    sym_reg.insert(rd, sym.clone());
                }
                _ => {
                    // ADRP with no PAGE21 reloc: whatever it loads is not a tracked
                    // symbol. Invalidate any stale tag on Rd.
                    sym_reg.remove(&rd);
                }
            }
            // ADRP still advances the machine state (writes the bogus placeholder
            // page constant); apply its data-plane effects so a later non-composed
            // use is modeled, then continue.
            for e in &effects {
                match e {
                    Effect::PcUpdate { .. }
                    | Effect::Return { .. }
                    | Effect::Branch { .. }
                    | Effect::ConditionalBranch { .. } => {}
                    other => state.apply_effect(other).unwrap_or_else(|er| {
                        panic!("apply_effect rejected {:?} at {pc:#x}: {er:?}", insn.opcode)
                    }),
                }
            }
            steps += 1;
            assert!(steps < 1000, "decode loop runaway");
            pc += 4;
            continue;
        }
        if insn.opcode == Opcode::Add {
            let rd = dst_gpr_index(&insn).expect("ADD has a GPR destination");
            // A PAGEOFF12 reloc on this ADD CONFIRMS the symbol tag ONLY when the
            // tag on Rd already matches (i.e. this is `ADD Rd, Rd, sym@PAGEOFF`
            // following `ADRP Rd, sym@PAGE`). Any mismatch invalidates.
            match relocs.get(&sec_off) {
                Some(SymReloc::Pageoff12(sym)) => {
                    if sym_reg.get(&rd) != Some(sym) {
                        // The PAGEOFF12 does not confirm a matching PAGE21 tag on
                        // Rd — do not trust it; invalidate.
                        sym_reg.remove(&rd);
                    }
                    // else: tag on Rd confirmed; keep it.
                }
                _ => {
                    // A plain ADD overwrites Rd with a non-symbol value; invalidate.
                    sym_reg.remove(&rd);
                }
            }
            for e in &effects {
                match e {
                    Effect::PcUpdate { .. }
                    | Effect::Return { .. }
                    | Effect::Branch { .. }
                    | Effect::ConditionalBranch { .. } => {}
                    other => state.apply_effect(other).unwrap_or_else(|er| {
                        panic!("apply_effect rejected {:?} at {pc:#x}: {er:?}", insn.opcode)
                    }),
                }
            }
            steps += 1;
            assert!(steps < 1000, "decode loop runaway");
            pc += 4;
            continue;
        }

        // ---- BLR: compose the KNOWN target, or FAIL CLOSED. ----
        if is_call {
            assert_eq!(insn.opcode, Opcode::Blr, "the real call must be a BLR (indirect), got {:?}", insn.opcode);
            let target_reg = dst_gpr_index(&insn).expect("BLR has a GPR target operand");
            let sym = sym_reg.get(&target_reg).unwrap_or_else(|| {
                panic!(
                    "FAIL-CLOSED: BLR at {pc:#x} targets X{target_reg}, not tagged with a known \
                     symbol address (open/vtable target) — must not compose"
                )
            });
            assert_eq!(sym, known_pure, "the BLR must target the known local pure callee");
            composed_a_blr = true;

            // Substitute the callee's derived pure output with the CURRENT
            // (pre-clobber) argument registers X0, X1.
            let mut result = callee_add_output();
            for i in 0..2usize {
                let xi = state.gpr[i].clone();
                result = substitute_var(&result, &format!("X{i}"), &xi);
            }

            // HAVOC caller-saved registers X0..=X18 + flags (the soundness step).
            let tag = call_tag;
            call_tag += 1;
            for i in 0..=18usize {
                state.gpr[i] = Formula::Var(format!("CC_{tag}_X{i}"), Sort::BitVec(64));
            }
            state.flags = Flags {
                n: Formula::Var(format!("CC_{tag}_N"), Sort::Bool),
                z: Formula::Var(format!("CC_{tag}_Z"), Sort::Bool),
                c: Formula::Var(format!("CC_{tag}_C"), Sort::Bool),
                v: Formula::Var(format!("CC_{tag}_V"), Sort::Bool),
            };
            // The BLR itself does not survive its own target register as a
            // caller-saved reg (X19 here is callee-saved, so its symbol tag is
            // preserved — but we do not read it post-call). Install the result.
            state.gpr[0] = result;

            steps += 1;
            assert!(steps < 1000, "decode loop runaway");
            pc += 4;
            continue;
        }

        // ---- Any other instruction: apply data-plane effects, and invalidate a
        // stale symbol tag if it overwrites a tracked register. ----
        if let Some(rd) = dst_gpr_index(&insn) {
            sym_reg.remove(&rd);
        }
        for e in &effects {
            match e {
                Effect::PcUpdate { .. }
                | Effect::Return { .. }
                | Effect::Branch { .. }
                | Effect::ConditionalBranch { .. } => {}
                other => state.apply_effect(other).unwrap_or_else(|er| {
                    panic!("apply_effect rejected {:?} at {pc:#x}: {er:?}", insn.opcode)
                }),
            }
        }
        steps += 1;
        assert!(steps < 1000, "decode loop runaway (no RET)");
        pc += 4;
    }
    assert!(composed_a_blr, "executor never reached a composed BLR (vacuous proof)");
    state.read_gpr(0, 32)
}

// ---------------------------------------------------------------------------
// Formula -> ay::Term (QF_ABV). Same translation as the direct-call test.
// ---------------------------------------------------------------------------

fn var_term(solver: &mut Solver, name: &str, sort: &Sort) -> Term {
    match sort {
        Sort::BitVec(w) => solver.bv_var(name, *w),
        Sort::Bool => solver.bool_var(name),
        other => panic!("unexpected Var sort {name}: {other:?}"),
    }
}

fn formula_to_term(solver: &mut Solver, f: &Formula) -> Term {
    match f {
        Formula::Var(name, sort) => var_term(solver, name, sort),
        Formula::Bool(b) => solver.bool_const(*b),
        Formula::BitVec { value, width } => {
            solver.try_bv_const_bigint(&BigInt::from(*value), *width).expect("bv const")
        }
        Formula::BvAdd(a, b, _) => bin2(solver, a, b, Solver::try_bvadd),
        Formula::BvSub(a, b, _) => bin2(solver, a, b, Solver::try_bvsub),
        Formula::BvMul(a, b, _) => bin2(solver, a, b, Solver::try_bvmul),
        Formula::BvAnd(a, b, _) => bin2(solver, a, b, Solver::try_bvand),
        Formula::BvOr(a, b, _) => bin2(solver, a, b, Solver::try_bvor),
        Formula::BvXor(a, b, _) => bin2(solver, a, b, Solver::try_bvxor),
        Formula::BvShl(a, b, _) => bin2(solver, a, b, Solver::try_bvshl),
        Formula::BvLShr(a, b, _) => bin2(solver, a, b, Solver::try_bvlshr),
        Formula::BvAShr(a, b, _) => bin2(solver, a, b, Solver::try_bvashr),
        Formula::BvConcat(a, b) => bin2(solver, a, b, Solver::try_bvconcat),
        Formula::BvNot(a, _) => {
            let a = formula_to_term(solver, a);
            solver.try_bvnot(a).expect("bvnot")
        }
        Formula::BvZeroExt(a, bits) => {
            let a = formula_to_term(solver, a);
            solver.try_bvzeroext(a, *bits).expect("bvzeroext")
        }
        Formula::BvSignExt(a, bits) => {
            let a = formula_to_term(solver, a);
            solver.try_bvsignext(a, *bits).expect("bvsignext")
        }
        Formula::BvExtract { inner, high, low } => {
            let inner = formula_to_term(solver, inner);
            solver.try_bvextract(inner, *high, *low).expect("bvextract")
        }
        Formula::Eq(a, b) => bin2(solver, a, b, Solver::try_eq),
        Formula::Not(a) => {
            let a = formula_to_term(solver, a);
            solver.try_not(a).expect("not")
        }
        Formula::Ite(cond, then_v, else_v) => {
            let c = formula_to_term(solver, cond);
            let t = formula_to_term(solver, then_v);
            let e = formula_to_term(solver, else_v);
            solver.try_ite(c, t, e).expect("ite")
        }
        other => panic!("formula_to_term: unhandled variant: {other:?}"),
    }
}

fn bin2(
    solver: &mut Solver,
    a: &Formula,
    b: &Formula,
    op: fn(&mut Solver, Term, Term) -> Result<Term, ay::SolverError>,
) -> Term {
    let a = formula_to_term(solver, a);
    let b = formula_to_term(solver, b);
    op(solver, a, b).expect("binary op")
}

fn discharge_equal(machine_out: &Formula, ir_out: &Formula) -> bool {
    let mut solver = Solver::try_new(Logic::QfAbv).expect("ay Solver::try_new");
    let lhs = formula_to_term(&mut solver, machine_out);
    let rhs = formula_to_term(&mut solver, ir_out);
    let eq = solver.try_eq(lhs, rhs).expect("eq");
    let differ = solver.try_not(eq).expect("not");
    solver.try_assert_term(differ).expect("assert");
    let result = solver.check_sat();
    if result.is_unsat() {
        true
    } else if result.is_sat() {
        false
    } else {
        panic!("ay returned unknown: {result:?}");
    }
}

fn wn(n: u32) -> Formula {
    Formula::BvExtract {
        inner: Box::new(Formula::Var(format!("X{n}"), Sort::BitVec(64))),
        high: 31,
        low: 0,
    }
}

/// The intended spec: `ci(a,b) = a + b` (32-bit), then a `+k` variant for the
/// negative control.
fn add_const_spec(k: i128) -> Formula {
    Formula::BvAdd(
        Box::new(Formula::BvAdd(Box::new(wn(0)), Box::new(wn(1)), 32)),
        Box::new(Formula::BitVec { value: k, width: 32 }),
        32,
    )
}

// NOTE ON THE VALUE-DIFFERENTIAL: the pinned trust-ir reference interpreter models
// an indirect call ONLY when the callee value is a `Ty::Func`-typed `FnDef(FuncId)`
// (see `interpret.rs::execute_indirect_call`); it does NOT resolve a `GlobalAddr`
// (which yields a plain `ptr`) to a function. So the interpreter cannot run the
// `GlobalAddr + CallIndirect` fn-pointer shape this slice lowers, and there is no
// concrete-value oracle for it (the pinned IR is not modified). The verification is
// therefore the BYTE-DERIVED proven output below (ay UNSAT of the composed emitted
// bytes vs the `a + b` spec) plus the mandatory SAT negative control — exactly the
// evidence the task requires. The callee `ir_addf`'s OWN bytes are independently
// proven `== x + y` by `module_to_lir_real_call_proven_output.rs` / the inline
// slices, so composing its derived formula here is grounded.

// ===========================================================================
// TEST 1 — the real-calls entry point emits Opcode::GlobalRef + CallIndirect, and
// the emitted __text carries a REAL BLR (indirect branch) plus the PAGE21 +
// PAGEOFF12 relocations naming the callee symbol — and NO direct Bl.
// ===========================================================================

#[test]
fn indirect_caller_emits_globalref_callindirect_and_a_real_blr() {
    let module = make_indirect_module();

    let lir = lower_trust_ir_function_to_lir_real_calls(&module, &module.functions[0])
        .expect("indirect caller lowers");
    let mut saw_globalref = false;
    let mut saw_callindirect = false;
    for b in lir.blocks.values() {
        for inst in &b.instructions {
            match &inst.opcode {
                trust_cg_lower::instructions::Opcode::GlobalRef { name } if name == "ir_addf" => {
                    saw_globalref = true;
                }
                trust_cg_lower::instructions::Opcode::CallIndirect => {
                    saw_callindirect = true;
                    // args[0] is the fn-pointer Value; args[1..] the call args.
                    assert_eq!(inst.args.len(), 3, "CallIndirect must carry fnptr + 2 args");
                }
                _ => {}
            }
        }
    }
    assert!(saw_globalref, "must emit Opcode::GlobalRef {{ name: ir_addf }}");
    assert!(saw_callindirect, "must emit Opcode::CallIndirect");

    // Emitted __text: exactly ONE BLR (real indirect branch), ZERO direct Bl.
    let obj = emit_caller_object(&module);
    let (code, base) = macho_text(&obj).expect("caller __text");
    assert!(!code.is_empty(), "caller __text is empty");
    assert_eq!(
        count_blr(&code, base),
        1,
        "expected exactly ONE Blr (real indirect call), got {}",
        count_blr(&code, base)
    );
    assert_eq!(
        count_bl_direct(&code, base),
        0,
        "an indirect call must NOT emit a direct Bl (got {})",
        count_bl_direct(&code, base)
    );

    // The fn-pointer materialization must carry PAGE21 + PAGEOFF12 relocs to the
    // callee symbol (this is what the executor traces the BLR target through).
    let relocs = parse_page_relocs(&obj);
    assert!(
        relocs.values().any(|r| *r == SymReloc::Page21("ir_addf".to_string())),
        "no PAGE21 reloc to ir_addf found; got {relocs:?}"
    );
    assert!(
        relocs.values().any(|r| *r == SymReloc::Pageoff12("ir_addf".to_string())),
        "no PAGEOFF12 reloc to ir_addf found; got {relocs:?}"
    );
}

// ===========================================================================
// TEST 2 — the callee `ir_addf` is a real, separately emitted defined symbol.
// ===========================================================================

#[test]
fn callee_ir_addf_is_emitted_as_a_defined_symbol() {
    let module = make_indirect_module();
    let callee_obj = emit_callee_object(&module);
    let (code, base) = macho_text(&callee_obj).expect("callee __text");
    assert!(!code.is_empty(), "callee __text is empty");
    assert_eq!(count_blr(&code, base), 0, "callee has no calls of its own");
    assert_eq!(count_bl_direct(&code, base), 0, "callee has no calls of its own");
    assert!(
        object_defines_symbol(&callee_obj, "ir_addf"),
        "callee object must define the ir_addf symbol the BLR resolves to"
    );
}

// ===========================================================================
// TEST 3 — PROVEN OUTPUT (infinite domain): the emitted caller bytes, with the
// real BLR COMPOSED (callee traced via PAGE21/PAGEOFF12 relocs + substituted,
// caller-saved regs havoced), compute `a + b` for ALL inputs. ay UNSAT.
// ===========================================================================

#[test]
fn indirect_caller_bytes_compose_to_a_plus_b_for_all_inputs() {
    let module = make_indirect_module();

    let obj = emit_caller_object(&module);
    let (code, base) = macho_text(&obj).expect("caller __text");
    assert_eq!(count_blr(&code, base), 1, "the call must be a real BLR (indirect)");
    let relocs = parse_page_relocs(&obj);

    let machine_out = composed_indirect_output(&code, base, &relocs, "ir_addf");
    let spec = add_const_spec(0);

    let proven = discharge_equal(&machine_out, &spec);
    assert!(
        proven,
        "PROVEN-OUTPUT FAILED: ay did not prove the composed indirect-call bytes equal \
         a+b for all inputs.\n  machine_out = {machine_out:?}"
    );
}

// ===========================================================================
// TEST 4 — MANDATORY NEGATIVE CONTROL: the SAME composed bytes proven against an
// `a + b + 1` spec MUST be SAT. Otherwise the positive certificate is vacuous.
// ===========================================================================

#[test]
fn negative_control_indirect_caller_vs_a_plus_b_plus_1_is_sat() {
    let module = make_indirect_module();
    let obj = emit_caller_object(&module);
    let (code, base) = macho_text(&obj).expect("caller __text");
    let relocs = parse_page_relocs(&obj);

    let machine_out = composed_indirect_output(&code, base, &relocs, "ir_addf");
    let wrong = add_const_spec(1);

    let proven = discharge_equal(&machine_out, &wrong);
    assert!(
        !proven,
        "VACUITY CHECK FAILED: the composed bytes were 'proven' equal to a+b+1; \
         the indirect-call discharge has no teeth.\n  machine_out = {machine_out:?}"
    );
}

// ===========================================================================
// TEST 5 — FAIL-CLOSED (OPEN TARGET): a `CallIndirect` whose function pointer is
// NOT traceable to a concrete GlobalAddr'd symbol (here: an INCOMING fn-pointer
// argument — the exact shape a vtable-slot load or a closure-env field produces)
// MUST be rejected at lowering. It is not composable (a future havoc-only slice),
// so the converter refuses to emit a BLR the executor could not soundly model.
// ===========================================================================

#[test]
fn open_target_indirect_call_via_non_function_global_fails_closed() {
    use trust_cg_bridge::ModuleLirError;

    // The fn-pointer IS a GlobalAddr (so it is tracked in `global_addr_syms`), but
    // the named global is a DATA global that names NO function. This drives the
    // CallIndirect arm's fail-closed path directly: the traced symbol does not
    // resolve to a local pure function (`function_by_name` -> None), so the BLR is
    // refused. This is the shape a vtable-slot address or a data-symbol fn-pointer
    // would present — an OPEN target the executor could not compose.
    let mut module = Module::new("open_data_global_module");
    module.func_types.push(FuncTy {
        params: vec![Ty::I32, Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    module.func_types.push(FuncTy {
        params: vec![Ty::I32, Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    // A DATA global — NOT a function symbol.
    module.globals.push(Global {
        name: "some_data_table".to_string(),
        ty: Ty::Ptr,
        mutable: false,
        initializer: None,
        linkage: Linkage::External,
        tls: None,
    });

    let mut caller = IrFunction::new(FuncId::new(0), "ir_open", FuncTyId::new(0), BlockId::new(0));
    let (a, b, fptr, called) =
        (ValueId::new(0), ValueId::new(1), ValueId::new(2), ValueId::new(3));
    let mut cb = Block::new(BlockId::new(0));
    cb.params.push((a, Ty::I32));
    cb.params.push((b, Ty::I32));
    cb.body
        .push(InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(0) }).with_result(fptr));
    cb.body.push(
        InstrNode::new(Inst::CallIndirect {
            callee: fptr,
            sig: FuncTyId::new(1),
            args: vec![a, b],
            calling_conv: Default::default(),
        })
        .with_result(called),
    );
    cb.body.push(InstrNode::new(Inst::Return { values: vec![called] }));
    caller.blocks.push(cb);
    module.functions.push(caller);

    let result = lower_trust_ir_function_to_lir_real_calls(&module, &module.functions[0]);
    match result {
        Err(ModuleLirError::UnsupportedInst { inst, .. }) => {
            assert_eq!(inst, "CallIndirect", "must fail closed on the OPEN CallIndirect");
        }
        Err(other) => panic!("expected UnsupportedInst(CallIndirect), got {other:?}"),
        Ok(_) => panic!(
            "SOUNDNESS VIOLATION: an OPEN-target CallIndirect (GlobalAddr to a DATA \
             symbol naming no function) was lowered — the converter must fail closed"
        ),
    }
}

// ===========================================================================
// TEST 6 — FAIL-CLOSED (IMPURE KNOWN TARGET): a `GlobalAddr + CallIndirect` whose
// KNOWN callee is NOT in the single-register scalar-pure fragment (here: the
// callee writes through a pointer — impure) MUST be rejected. The executor could
// not soundly stand in a pure formula for an effectful callee, so the converter
// refuses to emit the BLR.
// ===========================================================================

#[test]
fn impure_known_target_indirect_call_fails_closed_at_lowering() {
    use trust_cg_bridge::ModuleLirError;
    use trust_ir::inst::UnOp;

    let mut module = Module::new("impure_indirect_module");
    module.func_types.push(FuncTy {
        params: vec![Ty::I32, Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    // callee sig: (i32, ptr) -> i32 — takes a pointer it writes through (impure).
    module.func_types.push(FuncTy {
        params: vec![Ty::I32, Ty::Ptr],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    module.globals.push(Global {
        name: "ir_impure".to_string(),
        ty: Ty::Ptr,
        mutable: false,
        initializer: None,
        linkage: Linkage::External,
        tls: None,
    });

    // callee: ir_impure(x, p) { *p = x; return x }  — the Store makes it impure.
    let mut callee =
        IrFunction::new(FuncId::new(1), "ir_impure", FuncTyId::new(1), BlockId::new(0));
    let (x, p) = (ValueId::new(10), ValueId::new(11));
    let mut kb = Block::new(BlockId::new(0));
    kb.params.push((x, Ty::I32));
    kb.params.push((p, Ty::Ptr));
    kb.body.push(InstrNode::new(Inst::Store {
        ty: Ty::I32,
        ptr: p,
        value: x,
        volatile: false,
        align: None,
    }));
    kb.body.push(InstrNode::new(Inst::Return { values: vec![x] }));
    callee.blocks.push(kb);

    // caller: ci2(a) { let f = &ir_impure; f(a, &local) } — but keep it simple:
    // the caller just needs a GlobalAddr(ir_impure) + CallIndirect to trip the
    // composability gate. We pass (a, a-cast-to-ptr-shaped) args of matching arity;
    // the gate rejects the callee BEFORE arg validation because it is impure.
    let mut caller = IrFunction::new(FuncId::new(0), "ir_ci2", FuncTyId::new(0), BlockId::new(0));
    let (a, b, fptr, pv, called) = (
        ValueId::new(0),
        ValueId::new(1),
        ValueId::new(2),
        ValueId::new(3),
        ValueId::new(4),
    );
    let mut cb = Block::new(BlockId::new(0));
    cb.params.push((a, Ty::I32));
    cb.params.push((b, Ty::I32));
    cb.body
        .push(InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(0) }).with_result(fptr));
    // A second GlobalAddr just to supply a ptr-typed second arg (arity match).
    cb.body.push(InstrNode::new(Inst::UnOp { op: UnOp::Neg, ty: Ty::I32, operand: b }).with_result(pv));
    cb.body.push(
        InstrNode::new(Inst::CallIndirect {
            callee: fptr,
            sig: FuncTyId::new(1),
            args: vec![a, pv],
            calling_conv: Default::default(),
        })
        .with_result(called),
    );
    cb.body.push(InstrNode::new(Inst::Return { values: vec![called] }));
    caller.blocks.push(cb);

    module.functions.push(caller);
    module.functions.push(callee);

    let result = lower_trust_ir_function_to_lir_real_calls(&module, &module.functions[0]);
    match result {
        Err(ModuleLirError::UnsupportedInst { inst, .. }) => {
            assert_eq!(inst, "CallIndirect", "must fail closed on the impure known target");
        }
        Err(other) => panic!("expected UnsupportedInst(CallIndirect), got {other:?}"),
        Ok(_) => panic!(
            "SOUNDNESS VIOLATION: an IMPURE known-target CallIndirect (callee writes \
             through a pointer) was lowered — the converter must fail closed"
        ),
    }
}

// ===========================================================================
// OPEN-TARGET (HAVOC-ONLY) CALL INDIRECT
//
//     fn open_ci(fp: fn()->i32) -> i32 {   // FuncId 0; fp is a Ptr ARGUMENT
//         fp();                            //   CallIndirect(fp) — OPEN, untraceable
//         7                                //   return a CONSTANT, independent of fp
//     }
//
// The fn-pointer `fp` is an INCOMING ARGUMENT — it does NOT trace to a
// `GlobalAddr`'d symbol, so the executor's ADRP/ADD symbol-address tracer never
// tags the BLR's target register. This is the exact shape trait-object /
// closure DYNAMIC dispatch produces: a fn-ptr loaded from a vtable slot or a
// closure-env field is likewise an opaque register value, not a link-resolved
// local symbol.
//
// The open call is dispatched HAVOC-ONLY: the executor models the arbitrary
// callee by making the RESULT (X0) and all CALLER-SAVED state (X0..X18, flags)
// FRESH, and — critically — HAVOCING MEMORY (a fresh symbolic MEM array), so any
// post-call load reads a fresh value. CALLEE-SAVED registers (X19..X28, SP, FP)
// are preserved per the AAPCS64 contract, which is what lets `open_ci`'s own
// frame survive the call. Because `open_ci`'s return is the CONSTANT 7 —
// independent of the call result and of post-call memory — ay proves the bytes
// equal 7 for ALL inputs DESPITE the havoc (the provable fragment).
// ===========================================================================

/// Build the OPEN-target module: `open_ci(fp) { fp(); 7 }`. `fp` is a `Ty::Ptr`
/// argument; the CallIndirect's sig is `() -> i32` (no args).
fn make_open_indirect_module() -> Module {
    let mut module = Module::new("open_indirect_call_module");
    // FuncTy 0: caller(ptr)->i32 ; FuncTy 1: the callee sig ()->i32.
    module.func_types.push(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    module.func_types.push(FuncTy { params: vec![], returns: vec![Ty::I32], is_vararg: false });

    // caller: open_ci(fp) { let _ = fp(); return 7 }
    let mut caller = IrFunction::new(FuncId::new(0), "open_ci", FuncTyId::new(0), BlockId::new(0));
    let (fp, called, seven) = (ValueId::new(0), ValueId::new(1), ValueId::new(2));
    let mut cb = Block::new(BlockId::new(0));
    cb.params.push((fp, Ty::Ptr));
    // The OPEN indirect call: BLR through the incoming fn-ptr argument.
    cb.body.push(
        InstrNode::new(Inst::CallIndirect {
            callee: fp,
            sig: FuncTyId::new(1),
            args: vec![],
            calling_conv: Default::default(),
        })
        .with_result(called),
    );
    // Return the CONSTANT 7 — independent of the (havoced) call.
    cb.body.push(InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(7) }).with_result(seven));
    cb.body.push(InstrNode::new(Inst::Return { values: vec![seven] }));
    caller.blocks.push(cb);
    module.functions.push(caller);
    module
}

/// Build the DEPENDENT-return OPEN module: `open_ci_dep(fp) { fp() }` — returns
/// the (havoced) call RESULT directly. Used to prove the havoc HAS TEETH: the
/// result must be genuinely fresh (NOT provably any specific constant).
fn make_open_indirect_dependent_module() -> Module {
    let mut module = Module::new("open_indirect_dependent_module");
    module.func_types.push(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    module.func_types.push(FuncTy { params: vec![], returns: vec![Ty::I32], is_vararg: false });

    let mut caller =
        IrFunction::new(FuncId::new(0), "open_ci_dep", FuncTyId::new(0), BlockId::new(0));
    let (fp, called) = (ValueId::new(0), ValueId::new(1));
    let mut cb = Block::new(BlockId::new(0));
    cb.params.push((fp, Ty::Ptr));
    cb.body.push(
        InstrNode::new(Inst::CallIndirect {
            callee: fp,
            sig: FuncTyId::new(1),
            args: vec![],
            calling_conv: Default::default(),
        })
        .with_result(called),
    );
    // Return the CALL RESULT — depends on the havoc.
    cb.body.push(InstrNode::new(Inst::Return { values: vec![called] }));
    caller.blocks.push(cb);
    module.functions.push(caller);
    module
}

fn emit_open_caller_object(module: &Module) -> Vec<u8> {
    let caller = &module.functions[0];
    let lir = lower_trust_ir_function_to_lir_real_calls(module, caller)
        .expect("lower_trust_ir_function_to_lir_real_calls failed for OPEN indirect caller");
    backend().emit_object(&[lir]).expect("emit_object (OPEN caller) failed")
}

/// Symbolically execute the caller's emitted bytes, modeling an OPEN (untraceable)
/// `BLR` by HAVOCING the caller-saved registers, flags, and MEMORY, while
/// PRESERVING callee-saved registers (X19..X28), SP, and FP. Returns W0 after RET.
///
/// This is the sound over-approximation of an ARBITRARY callee: everything the
/// AAPCS64 contract does NOT guarantee to survive a call is made fresh.
fn open_indirect_output(code: &[u8], base: u64, relocs: &HashMap<u64, SymReloc>) -> Formula {
    let sem = Aarch64Semantics;
    let mut state = MachineState::symbolic();
    // Per-GPR symbol-address tag (same tracer as the KNOWN path). An OPEN target's
    // BLR register is simply never tagged.
    let mut sym_reg: HashMap<u8, String> = HashMap::new();
    let mut pc = base;
    let mut steps = 0u32;
    let mut call_tag = 0u32;
    let mut havoced_a_blr = false;

    loop {
        let off = (pc - base) as usize;
        assert!(off + 4 <= code.len(), "ran past __text end without RET");
        let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
        let insn = decode_aarch64(&bytes, pc).expect("decode_aarch64 failed");
        let sec_off = pc - base;

        if insn.opcode == Opcode::Ret {
            break;
        }

        let effects = sem
            .effects(&state, &insn)
            .unwrap_or_else(|e| panic!("effects failed at {pc:#x}: {e:?}"));
        let is_call = effects.iter().any(|e| matches!(e, Effect::Call { .. }));

        // ---- Symbol-address materialization tracer (ADRP + ADD). ----
        // Kept identical to the KNOWN path so a caller that mixes an OPEN call with
        // a genuine GlobalAddr elsewhere is still tracked correctly. For this
        // OPEN-only caller no ADRP/ADD to a symbol appears.
        if insn.opcode == Opcode::Adrp {
            let rd = dst_gpr_index(&insn).expect("ADRP has a GPR destination");
            match relocs.get(&sec_off) {
                Some(SymReloc::Page21(sym)) => {
                    sym_reg.insert(rd, sym.clone());
                }
                _ => {
                    sym_reg.remove(&rd);
                }
            }
            for e in &effects {
                match e {
                    Effect::PcUpdate { .. }
                    | Effect::Return { .. }
                    | Effect::Branch { .. }
                    | Effect::ConditionalBranch { .. } => {}
                    other => state.apply_effect(other).unwrap_or_else(|er| {
                        panic!("apply_effect rejected {:?} at {pc:#x}: {er:?}", insn.opcode)
                    }),
                }
            }
            steps += 1;
            assert!(steps < 1000, "decode loop runaway");
            pc += 4;
            continue;
        }
        if insn.opcode == Opcode::Add {
            // A frame-setup `ADD SP, SP, #imm` (or any ADD whose destination is
            // not a plain GPR) is definitionally NOT a `sym@PAGEOFF12`
            // confirmation, so it cannot interact with the symbol tracer. Only a
            // GPR-destination ADD does the tag bookkeeping; the stack-slot Alloca
            // this memory-loaded slice emits produces exactly this SP-form ADD.
            if let Some(rd) = dst_gpr_index(&insn) {
                match relocs.get(&sec_off) {
                    Some(SymReloc::Pageoff12(sym)) => {
                        if sym_reg.get(&rd) != Some(sym) {
                            sym_reg.remove(&rd);
                        }
                    }
                    _ => {
                        sym_reg.remove(&rd);
                    }
                }
            }
            for e in &effects {
                match e {
                    Effect::PcUpdate { .. }
                    | Effect::Return { .. }
                    | Effect::Branch { .. }
                    | Effect::ConditionalBranch { .. } => {}
                    other => state.apply_effect(other).unwrap_or_else(|er| {
                        panic!("apply_effect rejected {:?} at {pc:#x}: {er:?}", insn.opcode)
                    }),
                }
            }
            steps += 1;
            assert!(steps < 1000, "decode loop runaway");
            pc += 4;
            continue;
        }

        // ---- BLR: an OPEN target MUST NOT be tagged with a known symbol. ----
        if is_call {
            assert_eq!(
                insn.opcode,
                Opcode::Blr,
                "the OPEN call must be a BLR (indirect), got {:?}",
                insn.opcode
            );
            let target_reg = dst_gpr_index(&insn).expect("BLR has a GPR target operand");
            assert!(
                sym_reg.get(&target_reg).is_none(),
                "TEST-INVARIANT: the OPEN target's BLR register X{target_reg} must NOT be tagged \
                 with a known symbol (it is an incoming fn-ptr argument, not a GlobalAddr)"
            );
            havoced_a_blr = true;

            // HAVOC caller-saved registers X0..=X18 + flags.
            let tag = call_tag;
            call_tag += 1;
            for i in 0..=18usize {
                state.gpr[i] = Formula::Var(format!("OPEN_{tag}_X{i}"), Sort::BitVec(64));
            }
            state.flags = Flags {
                n: Formula::Var(format!("OPEN_{tag}_N"), Sort::Bool),
                z: Formula::Var(format!("OPEN_{tag}_Z"), Sort::Bool),
                c: Formula::Var(format!("OPEN_{tag}_C"), Sort::Bool),
                v: Formula::Var(format!("OPEN_{tag}_V"), Sort::Bool),
            };
            // HAVOC MEMORY: a fresh symbolic array. Any post-call load reads a
            // fresh, unconstrained value (the open callee may have written anywhere).
            state.memory = Formula::Var(
                format!("OPEN_{tag}_MEM"),
                Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
            );
            // The result X0 is fresh (already covered by the X0 havoc above, but we
            // keep it explicit to mirror the callee's return-value semantics).
            state.gpr[0] = Formula::Var(format!("OPEN_{tag}_RESULT"), Sort::BitVec(64));

            // Callee-saved X19..X28, SP, FP are UNTOUCHED (AAPCS64 preserves them),
            // so the caller's own frame reload survives. We deliberately do NOT
            // write them here.
            steps += 1;
            assert!(steps < 1000, "decode loop runaway");
            pc += 4;
            continue;
        }

        // ---- Any other instruction: apply data-plane effects, invalidate stale tag. ----
        if let Some(rd) = dst_gpr_index(&insn) {
            sym_reg.remove(&rd);
        }
        for e in &effects {
            match e {
                Effect::PcUpdate { .. }
                | Effect::Return { .. }
                | Effect::Branch { .. }
                | Effect::ConditionalBranch { .. } => {}
                other => state.apply_effect(other).unwrap_or_else(|er| {
                    panic!("apply_effect rejected {:?} at {pc:#x}: {er:?}", insn.opcode)
                }),
            }
        }
        steps += 1;
        assert!(steps < 1000, "decode loop runaway (no RET)");
        pc += 4;
    }
    assert!(havoced_a_blr, "executor never reached a havoced OPEN BLR (vacuous proof)");
    state.read_gpr(0, 32)
}

/// A bare 32-bit constant spec: `open_ci(fp) == k` for all inputs.
fn const_spec(k: i128) -> Formula {
    Formula::BitVec { value: k, width: 32 }
}

// ===========================================================================
// TEST 7 — OPEN-target lowering SUCCEEDS (no longer fail-closes) and emits a
// real BLR through an untraceable (argument) fn-pointer, with NO PAGE21/PAGEOFF12
// reloc to any function symbol (the pointer is not a GlobalAddr).
// ===========================================================================

#[test]
fn open_target_indirect_call_lowers_and_emits_a_real_blr() {
    let module = make_open_indirect_module();

    // Lowering must SUCCEED (the OPEN case is admitted HAVOC-only now).
    let lir = lower_trust_ir_function_to_lir_real_calls(&module, &module.functions[0])
        .expect("OPEN indirect caller must lower (havoc-only)");
    let mut saw_callindirect = false;
    let mut saw_globalref = false;
    for b in lir.blocks.values() {
        for inst in &b.instructions {
            match &inst.opcode {
                trust_cg_lower::instructions::Opcode::CallIndirect => {
                    saw_callindirect = true;
                    // args[0] = the fn-ptr, no call args (sig is ()->i32).
                    assert_eq!(inst.args.len(), 1, "OPEN CallIndirect carries only the fn-ptr");
                }
                trust_cg_lower::instructions::Opcode::GlobalRef { .. } => saw_globalref = true,
                _ => {}
            }
        }
    }
    assert!(saw_callindirect, "must emit Opcode::CallIndirect for the OPEN call");
    assert!(!saw_globalref, "an OPEN (argument) fn-ptr must NOT materialize a GlobalRef");

    // Emitted __text: a REAL BLR (indirect branch) and NO direct Bl.
    let obj = emit_open_caller_object(&module);
    let (code, base) = macho_text(&obj).expect("OPEN caller __text");
    assert!(!code.is_empty(), "OPEN caller __text is empty");
    assert_eq!(count_blr(&code, base), 1, "expected exactly ONE Blr (OPEN indirect call)");
    assert_eq!(count_bl_direct(&code, base), 0, "an indirect call must NOT emit a direct Bl");

    // No PAGE21/PAGEOFF12 reloc naming a function symbol (the ptr is not a GlobalAddr).
    let relocs = parse_page_relocs(&obj);
    assert!(
        !relocs.values().any(|r| matches!(r, SymReloc::Page21(_) | SymReloc::Pageoff12(_))),
        "an OPEN (argument) fn-ptr caller must carry NO PAGE21/PAGEOFF12 fn-symbol relocs; got {relocs:?}"
    );
}

// ===========================================================================
// TEST 8 — PROVEN OUTPUT (infinite domain): the emitted OPEN-caller bytes, with
// the real BLR HAVOCED (caller-saved regs + flags + MEMORY all fresh, callee-saved
// preserved), compute the CONSTANT 7 for ALL inputs. ay UNSAT.
//
// This is the provable fragment: the return does not depend on the call result or
// post-call memory, so the havoc cannot break it.
// ===========================================================================

#[test]
fn open_indirect_caller_bytes_prove_constant_7_despite_havoc() {
    let module = make_open_indirect_module();
    let obj = emit_open_caller_object(&module);
    let (code, base) = macho_text(&obj).expect("OPEN caller __text");
    assert_eq!(count_blr(&code, base), 1, "the OPEN call must be a real BLR (indirect)");
    let relocs = parse_page_relocs(&obj);

    let machine_out = open_indirect_output(&code, base, &relocs);
    let spec = const_spec(7);

    let proven = discharge_equal(&machine_out, &spec);
    assert!(
        proven,
        "PROVEN-OUTPUT FAILED: ay did not prove the OPEN-havoc caller bytes equal the \
         constant 7 for all inputs.\n  machine_out = {machine_out:?}"
    );
}

// ===========================================================================
// TEST 9 — MANDATORY NEGATIVE CONTROL: the SAME havoced bytes proven against the
// constant 8 (= 7 + 1) MUST be SAT. Otherwise the positive certificate is vacuous.
// ===========================================================================

#[test]
fn negative_control_open_indirect_caller_vs_constant_8_is_sat() {
    let module = make_open_indirect_module();
    let obj = emit_open_caller_object(&module);
    let (code, base) = macho_text(&obj).expect("OPEN caller __text");
    let relocs = parse_page_relocs(&obj);

    let machine_out = open_indirect_output(&code, base, &relocs);
    let wrong = const_spec(8);

    let proven = discharge_equal(&machine_out, &wrong);
    assert!(
        !proven,
        "VACUITY CHECK FAILED: the havoced OPEN-caller bytes were 'proven' equal to 8; \
         the constant-7 discharge has no teeth.\n  machine_out = {machine_out:?}"
    );
}

// ===========================================================================
// TEST 10 — THE HAVOC HAS TEETH: a caller whose return DOES depend on the
// (havoced) call result — `open_ci_dep(fp) { fp() }` — must NOT be provable to
// ANY specific constant. The result is genuinely fresh, so for EVERY candidate k
// the discharge is SAT (the machine output can differ from k). We check a spread
// of constants; if any were UNSAT, the havoc would be leaking a fixed value.
// ===========================================================================

#[test]
fn open_indirect_dependent_return_is_not_provable_to_any_constant() {
    let module = make_open_indirect_dependent_module();
    let obj = emit_open_caller_object(&module);
    let (code, base) = macho_text(&obj).expect("OPEN dependent caller __text");
    assert_eq!(count_blr(&code, base), 1, "the OPEN call must be a real BLR (indirect)");
    let relocs = parse_page_relocs(&obj);

    let machine_out = open_indirect_output(&code, base, &relocs);

    for k in [0i128, 1, 7, 42, -1, i128::from(i32::MAX), i128::from(i32::MIN)] {
        let proven = discharge_equal(&machine_out, &const_spec(k));
        assert!(
            !proven,
            "HAVOC-HAS-TEETH FAILED: the dependent OPEN-call return was 'proven' equal to the \
             constant {k}; a havoced open-call result must be genuinely FRESH (unprovable to any \
             specific value).\n  machine_out = {machine_out:?}"
        );
    }
}

// ===========================================================================
// OPEN-TARGET (HAVOC-ONLY) CALL INDIRECT THROUGH A MEMORY-LOADED FN-POINTER
//
//     fn open_ci_mem() -> i32 {              // FuncId 0
//         let slot: *mut fn()->i32 = alloca; //   Alloca{ty:Ptr}  (a vtable-slot /
//                                            //     closure-env field on the stack)
//         let fp = *slot;                    //   Load{ty:Ptr, ptr:slot} — the fn-ptr
//                                            //     is READ FROM MEMORY, not a symbol
//         fp();                              //   CallIndirect(fp) — OPEN, untraceable
//         7                                  //   return a CONSTANT, independent of fp
//     }
//
// This is the memory-loaded shape real trait-object / closure DYNAMIC dispatch
// produces: the fn-ptr is not an incoming register argument (tests 7-10) and not
// a `GlobalAddr`'d symbol (tests 1-4) — it is a value READ OUT OF MEMORY (a
// vtable slot, a closure-env field). This slice is unblocked by admitting
// `Ty::Ptr` in `map_scalar_mem_ty` (module_to_lir.rs): before, an `Alloca{Ptr}`
// / `Load{Ptr}` fell to the `UnsupportedMemory` error and the whole function
// fail-closed; now the Ptr slot is an 8-byte `I64` scalar slot and the fn-ptr
// round-trips through it exactly like any other 64-bit scalar.
//
// The loaded fn-ptr's LIR result is NOT recorded in `global_addr_syms` (only
// `GlobalAddr` results are), so the following `CallIndirect` is a
// `global_addr_syms` MISS -> the ALREADY-PROVEN OPEN-target havoc BLR arm. The
// executor's ADRP/ADD symbol tracer likewise never tags the BLR target register
// (the fn-ptr came from an `Ldr`, not an ADRP+ADD symbol materialization), so
// the open-havoc path (havoc caller-saved regs + flags + MEMORY, preserve
// callee-saved) models the arbitrary callee. Because `open_ci_mem`'s return is
// the CONSTANT 7 — independent of the call result AND of post-call memory (which
// is itself havoced) — ay proves the bytes equal 7 for ALL inputs DESPITE the
// memory-loaded-fn-ptr open havoc.
//
// SOUNDNESS: the memory-loaded fn-ptr is the WEAKEST-known kind of target — its
// value is whatever happens to be in the (uninitialized, then havoc-clobbered)
// slot, so it is treated as fully opaque and dispatched havoc-only. Nothing about
// the constant-7 return depends on it, so the proof is exact; a dependent-return
// variant (test 14) is genuinely unprovable, confirming the havoc has teeth.
// ===========================================================================

/// Build the memory-loaded OPEN module: `open_ci_mem() { let s=alloca Ptr;
/// let fp=*s; fp(); return 7 }`. The fn-ptr is LOADED from an alloca-rooted Ptr
/// slot (a stack vtable-slot / env-field), NOT an incoming argument or a symbol.
fn make_open_indirect_mem_module() -> Module {
    let mut module = Module::new("open_indirect_mem_module");
    // FuncTy 0: caller()->i32 ; FuncTy 1: the callee sig ()->i32.
    module.func_types.push(FuncTy { params: vec![], returns: vec![Ty::I32], is_vararg: false });
    module.func_types.push(FuncTy { params: vec![], returns: vec![Ty::I32], is_vararg: false });

    let mut caller =
        IrFunction::new(FuncId::new(0), "open_ci_mem", FuncTyId::new(0), BlockId::new(0));
    let (slot, fp, called, seven) =
        (ValueId::new(0), ValueId::new(1), ValueId::new(2), ValueId::new(3));
    let mut cb = Block::new(BlockId::new(0));
    // A stack slot holding a fn-pointer (the vtable-slot / closure-env field).
    cb.body.push(
        InstrNode::new(Inst::Alloca { ty: Ty::Ptr, count: None, align: None }).with_result(slot),
    );
    // Read the fn-pointer OUT OF MEMORY (an uninitialized-slot / vtable-slot load).
    cb.body.push(
        InstrNode::new(Inst::Load { ty: Ty::Ptr, ptr: slot, volatile: false, align: None })
            .with_result(fp),
    );
    // The OPEN indirect call: BLR through the memory-loaded fn-ptr.
    cb.body.push(
        InstrNode::new(Inst::CallIndirect {
            callee: fp,
            sig: FuncTyId::new(1),
            args: vec![],
            calling_conv: Default::default(),
        })
        .with_result(called),
    );
    // Return the CONSTANT 7 — independent of the (havoced) call and memory.
    cb.body.push(
        InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(7) }).with_result(seven),
    );
    cb.body.push(InstrNode::new(Inst::Return { values: vec![seven] }));
    caller.blocks.push(cb);
    module.functions.push(caller);
    module
}

/// Build the DEPENDENT-return memory-loaded OPEN module: `open_ci_mem_dep() {
/// let s=alloca Ptr; let fp=*s; fp() }` — returns the (havoced) call RESULT.
/// Proves the memory-loaded-fn-ptr havoc HAS TEETH.
fn make_open_indirect_mem_dependent_module() -> Module {
    let mut module = Module::new("open_indirect_mem_dependent_module");
    module.func_types.push(FuncTy { params: vec![], returns: vec![Ty::I32], is_vararg: false });
    module.func_types.push(FuncTy { params: vec![], returns: vec![Ty::I32], is_vararg: false });

    let mut caller =
        IrFunction::new(FuncId::new(0), "open_ci_mem_dep", FuncTyId::new(0), BlockId::new(0));
    let (slot, fp, called) = (ValueId::new(0), ValueId::new(1), ValueId::new(2));
    let mut cb = Block::new(BlockId::new(0));
    cb.body.push(
        InstrNode::new(Inst::Alloca { ty: Ty::Ptr, count: None, align: None }).with_result(slot),
    );
    cb.body.push(
        InstrNode::new(Inst::Load { ty: Ty::Ptr, ptr: slot, volatile: false, align: None })
            .with_result(fp),
    );
    cb.body.push(
        InstrNode::new(Inst::CallIndirect {
            callee: fp,
            sig: FuncTyId::new(1),
            args: vec![],
            calling_conv: Default::default(),
        })
        .with_result(called),
    );
    // Return the CALL RESULT — depends on the havoc.
    cb.body.push(InstrNode::new(Inst::Return { values: vec![called] }));
    caller.blocks.push(cb);
    module.functions.push(caller);
    module
}

// ===========================================================================
// TEST 11 — MEMORY-LOADED OPEN-target lowering SUCCEEDS: `Alloca{Ptr}` +
// `Load{Ptr}` are now admitted (Ty::Ptr in map_scalar_mem_ty), and the loaded
// fn-ptr drives a real BLR through an untraceable (memory-derived) pointer with
// NO PAGE21/PAGEOFF12 reloc to any function symbol (the ptr is not a GlobalAddr).
// ===========================================================================

#[test]
fn open_target_mem_loaded_fnptr_lowers_and_emits_a_real_blr() {
    let module = make_open_indirect_mem_module();

    // Lowering must SUCCEED — the Alloca{Ptr}/Load{Ptr} are admitted, and the
    // memory-loaded fn-ptr routes to the open-havoc CallIndirect arm.
    let lir = lower_trust_ir_function_to_lir_real_calls(&module, &module.functions[0])
        .expect("memory-loaded OPEN indirect caller must lower (Alloca{Ptr}/Load{Ptr} admitted)");
    let mut saw_callindirect = false;
    let mut saw_globalref = false;
    for b in lir.blocks.values() {
        for inst in &b.instructions {
            match &inst.opcode {
                trust_cg_lower::instructions::Opcode::CallIndirect => {
                    saw_callindirect = true;
                    assert_eq!(inst.args.len(), 1, "OPEN CallIndirect carries only the fn-ptr");
                }
                trust_cg_lower::instructions::Opcode::GlobalRef { .. } => saw_globalref = true,
                _ => {}
            }
        }
    }
    assert!(saw_callindirect, "must emit Opcode::CallIndirect for the memory-loaded OPEN call");
    assert!(!saw_globalref, "a memory-loaded fn-ptr must NOT materialize a GlobalRef");

    // Emitted __text: exactly ONE real BLR (indirect branch) and ZERO direct Bl.
    let obj = emit_open_caller_object(&module);
    let (code, base) = macho_text(&obj).expect("memory-loaded OPEN caller __text");
    assert!(!code.is_empty(), "memory-loaded OPEN caller __text is empty");
    assert_eq!(
        count_blr(&code, base),
        1,
        "expected exactly ONE Blr (memory-loaded OPEN indirect call)"
    );
    assert_eq!(count_bl_direct(&code, base), 0, "an indirect call must NOT emit a direct Bl");

    // No PAGE21/PAGEOFF12 reloc naming a function symbol: the fn-ptr is
    // MEMORY-LOADED (an Ldr off a stack slot), not a GlobalAddr materialization.
    let relocs = parse_page_relocs(&obj);
    assert!(
        !relocs.values().any(|r| matches!(r, SymReloc::Page21(_) | SymReloc::Pageoff12(_))),
        "a memory-loaded fn-ptr caller must carry NO PAGE21/PAGEOFF12 fn-symbol relocs; got {relocs:?}"
    );
}

// ===========================================================================
// TEST 12 — PROVEN OUTPUT (infinite domain): the emitted memory-loaded OPEN
// caller bytes, with the real BLR HAVOCED (caller-saved regs + flags + MEMORY
// all fresh, callee-saved preserved), compute the CONSTANT 7 for ALL inputs.
// ay UNSAT — DESPITE the fn-ptr having been loaded from (havoc-clobbered) memory.
// ===========================================================================

#[test]
fn open_indirect_mem_loaded_bytes_prove_constant_7_despite_havoc() {
    let module = make_open_indirect_mem_module();
    let obj = emit_open_caller_object(&module);
    let (code, base) = macho_text(&obj).expect("memory-loaded OPEN caller __text");
    assert_eq!(count_blr(&code, base), 1, "the OPEN call must be a real BLR (indirect)");
    let relocs = parse_page_relocs(&obj);

    let machine_out = open_indirect_output(&code, base, &relocs);
    let spec = const_spec(7);

    let proven = discharge_equal(&machine_out, &spec);
    assert!(
        proven,
        "PROVEN-OUTPUT FAILED: ay did not prove the memory-loaded OPEN-havoc caller bytes equal \
         the constant 7 for all inputs.\n  machine_out = {machine_out:?}"
    );
}

// ===========================================================================
// TEST 13 — MANDATORY NEGATIVE CONTROL: the SAME memory-loaded havoced bytes
// proven against the constant 8 (= 7 + 1) MUST be SAT. Otherwise the positive
// certificate is vacuous.
// ===========================================================================

#[test]
fn negative_control_open_indirect_mem_loaded_vs_constant_8_is_sat() {
    let module = make_open_indirect_mem_module();
    let obj = emit_open_caller_object(&module);
    let (code, base) = macho_text(&obj).expect("memory-loaded OPEN caller __text");
    let relocs = parse_page_relocs(&obj);

    let machine_out = open_indirect_output(&code, base, &relocs);
    let wrong = const_spec(8);

    let proven = discharge_equal(&machine_out, &wrong);
    assert!(
        !proven,
        "VACUITY CHECK FAILED: the memory-loaded havoced bytes were 'proven' equal to 8; the \
         constant-7 discharge has no teeth.\n  machine_out = {machine_out:?}"
    );
}

// ===========================================================================
// TEST 14 — THE MEMORY-LOADED HAVOC HAS TEETH: a caller whose return DOES depend
// on the (havoced) memory-loaded call result — `open_ci_mem_dep() { let s; fp=*s;
// fp() }` — must NOT be provable to ANY specific constant. The result is
// genuinely fresh, so for EVERY candidate k the discharge is SAT.
// ===========================================================================

#[test]
fn open_indirect_mem_loaded_dependent_return_is_not_provable_to_any_constant() {
    let module = make_open_indirect_mem_dependent_module();
    let obj = emit_open_caller_object(&module);
    let (code, base) = macho_text(&obj).expect("memory-loaded OPEN dependent caller __text");
    assert_eq!(count_blr(&code, base), 1, "the OPEN call must be a real BLR (indirect)");
    let relocs = parse_page_relocs(&obj);

    let machine_out = open_indirect_output(&code, base, &relocs);

    for k in [0i128, 1, 7, 42, -1, i128::from(i32::MAX), i128::from(i32::MIN)] {
        let proven = discharge_equal(&machine_out, &const_spec(k));
        assert!(
            !proven,
            "HAVOC-HAS-TEETH FAILED: the dependent memory-loaded OPEN-call return was 'proven' \
             equal to the constant {k}; a havoced open-call result must be genuinely FRESH \
             (unprovable to any specific value).\n  machine_out = {machine_out:?}"
        );
    }
}
