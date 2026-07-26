// module_to_lir_real_call_proven_output.rs — the FIRST structural step toward
// cross-function calls in the Module -> LIR converter: emit a REAL (non-inlined)
// `Opcode::Call` to a LOCAL pure callee, and prove the composed machine output.
//
// This is the OPPOSITE capability of `module_to_lir_inline_proven_output.rs`.
// There, the call to `add` is INLINED and the emitted __text carries NO `Bl`.
// Here, `lower_trust_ir_function_to_lir_real_calls` lowers the SAME caller to a
// GENUINE `Opcode::Call { name: "ir_add" }`, which ISel lowers to a real
// `Bl ir_add` + an `ARM64_RELOC_BRANCH26` naming the callee symbol. The call
// survives as a cross-function edge — the foundation for closures / trait-object
// dispatch.
//
//     fn add(x: i32, y: i32) -> i32 { x + y }             // FuncId 1 (callee)
//     fn caller(a: i32, b: i32) -> i32 { add(a, b) + 1 }  // FuncId 0
//
// The proof MIRRORS the bundle gate's local-pure-callee composition
// (`verify_output::model_local_call`): the machine-side path-merge executor
//   (1) decodes the caller's OWN emitted bytes (arg setup, the `Bl`, the result
//       move, the `+1`) — the semantics are BYTE-DERIVED, never reconstructed;
//   (2) at the `Bl`, consults the EMITTED OBJECT's `ARM64_RELOC_BRANCH26`
//       relocation to identify the callee symbol (`ir_add`);
//   (3) SUBSTITUTES the callee's derived pure output (`W0 = X0 + X1` truncated to
//       32) into X0 using the CURRENT (pre-call) argument registers; and
//   (4) HAVOCS caller-saved registers X0..X18 + the flags to fresh variables (the
//       callee may clobber them) — the soundness-critical step.
// ay (QF_ABV) then proves the composed output equals `a + b + 1` for ALL inputs
// (UNSAT of the negation). A MANDATORY SAT negative control (`a + b + 2`) proves
// the discharge has teeth.
//
// SOUNDNESS (why composing the callee is sound):
//   * the callee symbol comes from the REAL relocation the LINKER will resolve,
//     not the IR's claim — the `Bl` provably jumps to `ir_add`'s bytes;
//   * `ir_add` is itself in the gate's single-register scalar-pure fragment
//     (its bytes are proven == `x + y` by the same proven-output machinery),
//     so standing its derived formula in for "what the resolved `bl` computes"
//     is exact;
//   * havocing caller-saved registers means any post-call read of a register the
//     bytes wrongly assume survives becomes a FRESH variable that ay refutes
//     against the (clobber-free) spec — composition cannot launder a caller-side
//     miscompile (only the call RESULT is substituted; arg setup + result move
//     stay byte-derived).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![cfg(feature = "ay-proofs")]

use std::collections::HashMap;

use ay::{BigInt, Logic, Solver, Term};
use trust_cg_bridge::codegen_backend::{TrustCgCodegenBackend, TrustCgTargetArch};
use trust_cg_bridge::{
    lower_trust_ir_function_to_lir, lower_trust_ir_function_to_lir_real_calls,
};
use trust_disasm::{Instruction as DisasmInst, Opcode, decode_aarch64};
use trust_machine_sem::{Aarch64Semantics, Effect, Flags, MachineState, Semantics};
use trust_types::{Formula, Sort};

use trust_ir::inst::{BinOp, Inst};
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::node::InstrNode;
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{Block, Constant, Function as IrFunction, Module};

// ---------------------------------------------------------------------------
// Build the same caller(a,b) = add(a,b) + k module as the inline test, so the
// ONLY difference is the converter entry point (real-calls vs inline).
// ---------------------------------------------------------------------------

fn make_caller_add_module(k: i128) -> Module {
    let mut module = Module::new("real_call_module");
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

    // --- callee: add(x, y) = x + y  (FuncId 1) ---
    let mut add = IrFunction::new(FuncId::new(1), "ir_add", FuncTyId::new(1), BlockId::new(0));
    let x = ValueId::new(10);
    let y = ValueId::new(11);
    let s = ValueId::new(12);
    let mut ab = Block::new(BlockId::new(0));
    ab.params.push((x, Ty::I32));
    ab.params.push((y, Ty::I32));
    ab.body.push(
        InstrNode::new(Inst::BinOp { op: BinOp::Add, ty: Ty::I32, lhs: x, rhs: y }).with_result(s),
    );
    ab.body.push(InstrNode::new(Inst::Return { values: vec![s] }));
    add.blocks.push(ab);

    // --- caller: caller(a, b) = add(a, b) + k  (FuncId 0) ---
    let mut caller =
        IrFunction::new(FuncId::new(0), "ir_caller", FuncTyId::new(0), BlockId::new(0));
    let a = ValueId::new(0);
    let b = ValueId::new(1);
    let called = ValueId::new(2);
    let kconst = ValueId::new(3);
    let out = ValueId::new(4);
    let mut cb = Block::new(BlockId::new(0));
    cb.params.push((a, Ty::I32));
    cb.params.push((b, Ty::I32));
    cb.body.push(
        InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![a, b] }).with_result(called),
    );
    cb.body.push(
        InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(k) }).with_result(kconst),
    );
    cb.body.push(
        InstrNode::new(Inst::BinOp { op: BinOp::Add, ty: Ty::I32, lhs: called, rhs: kconst })
            .with_result(out),
    );
    cb.body.push(InstrNode::new(Inst::Return { values: vec![out] }));
    caller.blocks.push(cb);

    module.functions.push(caller);
    module.functions.push(add);
    module
}

fn make_caller_inc_module() -> Module {
    make_caller_add_module(1)
}

// ---------------------------------------------------------------------------
// Emit the caller (with a REAL Call) to a Mach-O object; keep the WHOLE object
// so we can parse the BRANCH26 relocation, plus __text bytes + base.
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

/// Emit the CALLER alone (real Call) and return the FULL object bytes.
fn emit_caller_object(module: &Module) -> Vec<u8> {
    let caller = &module.functions[0];
    let lir = lower_trust_ir_function_to_lir_real_calls(module, caller)
        .expect("lower_trust_ir_function_to_lir_real_calls failed for real-call caller");
    backend().emit_object(&[lir]).expect("emit_object (caller) failed")
}

/// Emit the CALLEE alone and return the FULL object bytes — proof that the
/// callee is a real, separately emitted function (its symbol is what the
/// caller's `Bl` relocation resolves to at link time).
fn emit_callee_object(module: &Module) -> Vec<u8> {
    let callee = &module.functions[1];
    // The callee is call-free straight-line `x + y`; the inline entry point
    // lowers it (there is no call to inline), producing its object bytes.
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

/// Whether the callee symbol appears in the object's symbol table (proof it is a
/// defined function symbol, e.g. the callee's own object).
fn object_defines_symbol(obj: &[u8], want: &str) -> bool {
    let rd_u32 = |o: usize| -> Option<u32> {
        Some(u32::from_le_bytes(obj.get(o..o + 4)?.try_into().ok()?))
    };
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

/// Parse the `__text` `ARM64_RELOC_BRANCH26` (type 2) relocations: in-section
/// byte offset -> callee symbol name (leading `_` stripped). Mirrors the gate's
/// `verify_output::parse_text_branch26_relocs`. Only external, pcrel, len==2,
/// BRANCH26 relocations to a defined symbol are recorded.
fn parse_branch26_relocs(obj: &[u8]) -> HashMap<u64, String> {
    let rd_u32 = |o: usize| -> u32 {
        u32::from_le_bytes(obj[o..o + 4].try_into().expect("u32"))
    };
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
        let start = stroff + strx;
        let end = stroff + strsize;
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
        let r_pcrel = (w1 >> 24) & 1;
        let r_length = (w1 >> 25) & 3;
        let r_extern = (w1 >> 27) & 1;
        let r_type = (w1 >> 28) & 0xf;
        if r_type == 2 && r_extern == 1 && r_pcrel == 1 && r_length == 2 {
            map.insert(r_address, sym_name(r_symbolnum));
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

fn count_bl(code: &[u8], base: u64) -> usize {
    decode_all(code, base)
        .iter()
        .filter(|(_, i)| matches!(i.opcode, Opcode::Bl | Opcode::Blr))
        .count()
}

// ===========================================================================
// COMPOSING PATH-MERGING EXECUTOR — the machine-side model of the real Call.
// Mirrors verify_output::PathMergingExecutor::model_local_call: at a `Bl`, parse
// the BRANCH26 reloc -> callee symbol, substitute the callee's derived pure
// output into X0 using the CURRENT arg registers, then HAVOC caller-saved regs.
// This straight-line executor covers the (single-block, no-branch) caller shape;
// the caller's control flow is: arg-setup Orr's -> Bl -> result move -> +1 -> RET.
// ===========================================================================

/// The callee (`ir_add`)'s derived pure output over its argument registers
/// X0, X1: `add(x, y) = trunc32(X0) + trunc32(X1)` zero-extended into the 64-bit
/// return slot (W0 = low 32; the machine reads W0 back via read_gpr(0, 32)). This
/// is the SAME formula the gate's `derive_callee_pure` produces for `ir_add`.
fn callee_add_output() -> Formula {
    let w = |n: u32| Formula::BvExtract {
        inner: Box::new(Formula::Var(format!("X{n}"), Sort::BitVec(64))),
        high: 31,
        low: 0,
    };
    // 32-bit sum, then zero-extend into the 64-bit X0 slot (matches the AAPCS64
    // W-return write; read_gpr(0, 32) re-extracts the low half).
    let sum32 = Formula::BvAdd(Box::new(w(0)), Box::new(w(1)), 32);
    Formula::BvZeroExt(Box::new(sum32), 32)
}

fn substitute_var(f: &Formula, name: &str, replacement: &Formula) -> Formula {
    match f {
        Formula::Var(n, _) if n == name => replacement.clone(),
        leaf @ (Formula::Var(..) | Formula::SymVar(..)) => leaf.clone(),
        other => other
            .clone()
            .map_children(&mut |child| substitute_var(&child, name, replacement)),
    }
}

/// Symbolically execute the caller's emitted bytes, MODELING the `Bl` by
/// composing `ir_add`. Returns W0 after RET.
fn composed_machine_output(code: &[u8], base: u64, relocs: &HashMap<u64, String>) -> Formula {
    let sem = Aarch64Semantics;
    let mut state = MachineState::symbolic();
    let mut pc = base;
    let mut steps = 0u32;
    let mut call_tag = 0u32;

    loop {
        let off = (pc - base) as usize;
        assert!(off + 4 <= code.len(), "ran past __text end without RET");
        let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
        let insn = decode_aarch64(&bytes, pc).expect("decode_aarch64 failed");

        if insn.opcode == Opcode::Ret {
            break;
        }

        let effects = sem
            .effects(&state, &insn)
            .unwrap_or_else(|e| panic!("effects failed at {pc:#x}: {e:?}"));

        // Is this a call (BL/BLR)? Model it by composition.
        let is_call = effects.iter().any(|e| matches!(e, Effect::Call { .. }));
        if is_call {
            let sec_off = pc - base;
            let callee = relocs
                .get(&sec_off)
                .unwrap_or_else(|| panic!("no BRANCH26 reloc at bl {pc:#x} (sec_off {sec_off:#x})"));
            assert_eq!(callee, "ir_add", "the bl must target the local pure callee");

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
            // Install the call result in X0 (already 64-bit-slotted above).
            state.gpr[0] = result;

            steps += 1;
            assert!(steps < 1000, "decode loop runaway");
            pc += 4;
            continue;
        }

        // Non-call: apply the data-plane effects, skipping control/link effects.
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
    state.read_gpr(0, 32)
}

// ---------------------------------------------------------------------------
// Formula -> ay::Term (QF_ABV). Same translation as the inline test.
// ---------------------------------------------------------------------------

fn var_term(solver: &mut Solver, name: &str, sort: &Sort) -> Term {
    match sort {
        Sort::BitVec(w) => solver.bv_var(name, *w),
        Sort::Bool => solver.bool_var(name),
        Sort::Array(idx, elem) => {
            let (Sort::BitVec(iw), Sort::BitVec(ew)) = (idx.as_ref(), elem.as_ref()) else {
                panic!("unsupported array sort for Var {name}: {sort:?}");
            };
            solver.declare_const(name, ay::Sort::array(ay::Sort::bitvec(*iw), ay::Sort::bitvec(*ew)))
        }
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
        Formula::BvULt(a, b, _) => bin2(solver, a, b, Solver::try_bvult),
        Formula::BvULe(a, b, _) => bin2(solver, a, b, Solver::try_bvule),
        Formula::BvSLt(a, b, _) => bin2(solver, a, b, Solver::try_bvslt),
        Formula::BvSLe(a, b, _) => bin2(solver, a, b, Solver::try_bvsle),
        Formula::Eq(a, b) => bin2(solver, a, b, Solver::try_eq),
        Formula::Not(a) => {
            let a = formula_to_term(solver, a);
            solver.try_not(a).expect("not")
        }
        Formula::And(terms) => {
            let ts: Vec<Term> = terms.iter().map(|t| formula_to_term(solver, t)).collect();
            solver.try_and_many(&ts).expect("and")
        }
        Formula::Or(terms) => {
            let ts: Vec<Term> = terms.iter().map(|t| formula_to_term(solver, t)).collect();
            solver.try_or_many(&ts).expect("or")
        }
        Formula::Ite(cond, then_v, else_v) => {
            let c = formula_to_term(solver, cond);
            let t = formula_to_term(solver, then_v);
            let e = formula_to_term(solver, else_v);
            solver.try_ite(c, t, e).expect("ite")
        }
        Formula::Select(arr, idx) => {
            let a = formula_to_term(solver, arr);
            let i = formula_to_term(solver, idx);
            solver.try_select(a, i).expect("select")
        }
        Formula::Store(arr, idx, val) => {
            let a = formula_to_term(solver, arr);
            let i = formula_to_term(solver, idx);
            let v = formula_to_term(solver, val);
            solver.try_store(a, i, v).expect("store")
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

fn add_add_const_spec(k: i128) -> Formula {
    Formula::BvAdd(
        Box::new(Formula::BvAdd(Box::new(wn(0)), Box::new(wn(1)), 32)),
        Box::new(Formula::BitVec { value: k, width: 32 }),
        32,
    )
}

fn interpret_caller(module: &Module, a: i128, b: i128) -> i128 {
    let interp = Interpreter::with_module(module);
    let args = vec![
        InterpretValue::int(Ty::I32, a).expect("arg a"),
        InterpretValue::int(Ty::I32, b).expect("arg b"),
    ];
    let outcome = interp
        .execute_func(FuncId::new(0), args)
        .expect("interpreter execute_func failed");
    outcome.returns[0].as_int().expect("integer return").as_signed()
}

// ===========================================================================
// TEST 1 — the real-calls entry point emits a genuine LIR Call AND a real `Bl`
// in the emitted __text (the OPPOSITE of the inline slice's no-Bl assertion),
// carrying a BRANCH26 relocation to the callee symbol.
// ===========================================================================

#[test]
fn real_call_caller_emits_a_real_bl_with_branch26_reloc() {
    let module = make_caller_inc_module();

    // The lowered LIR MUST carry an Opcode::Call { name: "ir_add" } (NOT inlined).
    let lir = lower_trust_ir_function_to_lir_real_calls(&module, &module.functions[0])
        .expect("real-call caller lowers");
    let call_names: Vec<String> = lir
        .blocks
        .values()
        .flat_map(|b| b.instructions.iter())
        .filter_map(|inst| match &inst.opcode {
            trust_cg_lower::instructions::Opcode::Call { name } => Some(name.clone()),
            _ => None,
        })
        .collect();
    assert_eq!(
        call_names,
        vec!["ir_add".to_string()],
        "the real-call converter must emit exactly one Opcode::Call to ir_add"
    );

    // And the emitted __text must carry a REAL Bl (call was NOT inlined).
    let obj = emit_caller_object(&module);
    let (code, base) = macho_text(&obj).expect("caller __text");
    assert!(!code.is_empty(), "caller __text is empty");
    let bls = count_bl(&code, base);
    assert_eq!(bls, 1, "expected exactly ONE Bl (real cross-function call), got {bls}");

    // The Bl must carry a BRANCH26 relocation naming the callee symbol.
    let relocs = parse_branch26_relocs(&obj);
    assert!(
        relocs.values().any(|s| s == "ir_add"),
        "no BRANCH26 reloc to ir_add found; got relocs = {relocs:?}"
    );
}

// ===========================================================================
// TEST 2 — the callee `ir_add` is a real, separately emitted function whose
// symbol the caller's Bl resolves to.
// ===========================================================================

#[test]
fn callee_ir_add_is_emitted_as_a_defined_symbol() {
    let module = make_caller_inc_module();
    let callee_obj = emit_callee_object(&module);
    let (code, base) = macho_text(&callee_obj).expect("callee __text");
    assert!(!code.is_empty(), "callee __text is empty");
    // The callee body is call-free (no Bl in ITS bytes).
    assert_eq!(count_bl(&code, base), 0, "callee add has no calls of its own");
    // The callee's own object defines the `ir_add` symbol the caller Bl targets.
    assert!(
        object_defines_symbol(&callee_obj, "ir_add"),
        "callee object must define the ir_add symbol"
    );
}

// ===========================================================================
// TEST 3 — concrete value-differential: the Module interpreter (real call
// machinery) computes caller(a,b) = add(a,b) + 1.
// ===========================================================================

#[test]
fn module_interpreter_caller_inc_is_correct() {
    let module = make_caller_inc_module();
    assert_eq!(interpret_caller(&module, 2, 3), 6);
    assert_eq!(interpret_caller(&module, -1, 1), 1);
    assert_eq!(interpret_caller(&module, 0, 0), 1);
    assert_eq!(interpret_caller(&module, 40, 1), 42);
}

// ===========================================================================
// TEST 4 — PROVEN OUTPUT (infinite domain): the emitted caller bytes, with the
// real `Bl` COMPOSED (callee substituted at the reloc target, caller-saved regs
// havoced), compute `a + b + 1` for ALL inputs. ay UNSAT of the negation.
// ===========================================================================

#[test]
fn real_call_caller_bytes_compose_to_a_plus_b_plus_1_for_all_inputs() {
    let module = make_caller_inc_module();
    assert_eq!(interpret_caller(&module, 2, 3), 6, "value-differential precondition");

    let obj = emit_caller_object(&module);
    let (code, base) = macho_text(&obj).expect("caller __text");
    assert_eq!(count_bl(&code, base), 1, "the call must be a real Bl (not inlined)");
    let relocs = parse_branch26_relocs(&obj);

    let machine_out = composed_machine_output(&code, base, &relocs);
    let spec = add_add_const_spec(1);

    let proven = discharge_equal(&machine_out, &spec);
    assert!(
        proven,
        "PROVEN-OUTPUT FAILED: ay did not prove the composed real-call bytes equal \
         a+b+1 for all inputs.\n  machine_out = {machine_out:?}"
    );
}

// ===========================================================================
// TEST 5 — MANDATORY NEGATIVE CONTROL: the SAME composed bytes proven against an
// `a + b + 2` spec MUST be SAT. Otherwise the positive certificate is vacuous.
// ===========================================================================

#[test]
fn negative_control_real_call_caller_vs_a_plus_b_plus_2_is_sat() {
    let module = make_caller_inc_module();
    let obj = emit_caller_object(&module);
    let (code, base) = macho_text(&obj).expect("caller __text");
    let relocs = parse_branch26_relocs(&obj);

    let machine_out = composed_machine_output(&code, base, &relocs);
    let wrong = add_add_const_spec(2);

    let proven = discharge_equal(&machine_out, &wrong);
    assert!(
        !proven,
        "VACUITY CHECK FAILED: the composed bytes were 'proven' equal to a+b+2; \
         the real-call discharge has no teeth.\n  machine_out = {machine_out:?}"
    );
}
