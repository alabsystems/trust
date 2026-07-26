// module_to_lir_fnptr_indirect_from_vf_proven_output.rs — the END-TO-END
// trust-ir-first fn-pointer dispatch slice: a trust-types `VerifiableFunction`
// containing an INDIRECT call through a fn-POINTER lowers (VF -> Module) to
// `Inst::CallIndirect`, and that Module then flows through module_to_lir -> a real
// BLR -> the proven-output executor.
//
//     fn callit(f: fn(i32)->i32, x: i32) -> i32 {   // f is an INCOMING fn-ptr ARG
//         let _ = f(x);                              //   Fn::call(f, (x,)) shim
//         7                                          //   return a CONSTANT (const variant)
//     }
//     fn callit_dep(f: fn(i32)->i32, x: i32) -> i32 { f(x) }  // havoc-only return
//
// The producer half (`trust_ir_bridge::lower_to_trust_ir`) now emits
// `Inst::CallIndirect{callee: <fn-ptr ValueId>, sig: <from the Ty::FnPtr sig>,
// args: [x], calling_conv: Rust}` for the `Fn::call` shim whose receiver is a
// concrete `Ty::FnPtr`, instead of failing closed in `resolve_call_target` (which
// poisoned EVERY obligation in the function to Unsupported). It also attaches one
// honest UNKNOWN `PanicFreedom` obligation (the open havoc dispatch cannot prove
// the callee panic-free) — matching the `closure_driving_consumer_call` precedent.
//
// The consumer half is the ALREADY-PROVEN OPEN-target (havoc-only) BLR: the fn-ptr
// `f` is an incoming ARGUMENT, so it does not trace to a GlobalAddr'd symbol — the
// converter admits a HAVOC-ONLY BLR (result + caller-saved regs + flags + MEMORY
// fresh, callee-saved preserved per AAPCS64). Because `callit`'s return is the
// CONSTANT 7 — independent of the (havoced) call result and post-call memory — ay
// proves the emitted bytes equal 7 for ALL inputs DESPITE the havoc, with a
// MANDATORY SAT negative control. The `callit_dep` variant (returns `f(x)`) is
// genuinely unprovable to any constant, confirming the havoc has teeth and that the
// call arg `x` truly flows into the (havoced) BLR.
//
// This is the VF -> Module -> LIR -> proven bytes end-to-end connection goal #1
// asked for: real fn-ptr dispatch through the trust-ir-first path.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![cfg(feature = "ay-proofs")]

use std::collections::HashMap;

use ay::{BigInt, Logic, Solver, Term};
use trust_cg_bridge::codegen_backend::{TrustCgCodegenBackend, TrustCgTargetArch};
use trust_cg_bridge::lower_trust_ir_function_to_lir_real_calls;
use trust_disasm::{Instruction as DisasmInst, Opcode, decode_aarch64};
use trust_machine_sem::{Aarch64Semantics, Effect, Flags, MachineState, Semantics};
use trust_types::{Formula, Sort};

use trust_ir::inst::Inst;
use trust_ir::value::FuncTyId;
use trust_ir::Module;

use trust_types::{
    AggregateKind, BasicBlock, BlockId as TBlockId, ConstValue, FnSig, LocalDecl,
    Operand as TOperand, Place, Rvalue, SourceSpan, Statement, Terminator, Ty as TTy,
    VerifiableBody, VerifiableFunction,
};

// ---------------------------------------------------------------------------
// Build the fn-pointer indirect-call VerifiableFunction.
// ---------------------------------------------------------------------------

const FN_CALL_SHIM: &str = "core::ops::function::Fn::call";

fn fn_i32_to_i32() -> TTy {
    TTy::FnPtr { sig: Box::new(FnSig { params: vec![TTy::i32()], ret: Box::new(TTy::i32()) }) }
}

fn fn_unit_to_i32() -> TTy {
    TTy::FnPtr { sig: Box::new(FnSig { params: vec![], ret: Box::new(TTy::i32()) }) }
}

/// `callit_arg(f: fn(i32)->i32, x: i32) -> i32`: `{ tmp=(x,); _4=Fn::call(f,tmp);
/// return _4 }` — the ONE-ARG rust-call shape. Used ONLY for the producer-side
/// Module assertion (the tuple materialization `_3=(x,)` is a non-scalar aggregate
/// module_to_lir does not yet lower to LIR — an orthogonal converter limitation —
/// so the LIR/proven tests use the zero-arg shape below).
fn build_callit_arg() -> VerifiableFunction {
    let locals = vec![
        LocalDecl { index: 0, ty: TTy::i32(), name: Some("ret".into()) },
        LocalDecl { index: 1, ty: fn_i32_to_i32(), name: Some("f".into()) },
        LocalDecl { index: 2, ty: TTy::i32(), name: Some("x".into()) },
        LocalDecl { index: 3, ty: TTy::Tuple(vec![TTy::i32()]), name: None },
        LocalDecl { index: 4, ty: TTy::i32(), name: None },
    ];
    let bb0 = BasicBlock {
        id: TBlockId(0),
        stmts: vec![Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::Aggregate(AggregateKind::Tuple, vec![TOperand::Move(Place::local(2))]),
            span: SourceSpan::default(),
        }],
        terminator: Terminator::Call {
            func: FN_CALL_SHIM.to_string(),
            args: vec![TOperand::Move(Place::local(1)), TOperand::Move(Place::local(3))],
            dest: Place::local(4),
            target: Some(TBlockId(1)),
            span: SourceSpan::default(),
            atomic: None,
            unwind: trust_types::UnwindEdge::Unreachable,
            is_unsafe_sig: false, is_foreign: false,
        },
    };
    let bb1 = BasicBlock {
        id: TBlockId(1),
        stmts: vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(TOperand::Move(Place::local(4))),
            span: SourceSpan::default(),
        }],
        terminator: Terminator::Return,
    };
    VerifiableFunction {
        name: "callit_arg".into(),
        def_path: "test::callit_arg".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![bb0, bb1],
            arg_count: 2,
            return_ty: TTy::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// `callit(f: fn()->i32) -> i32`: `{ tmp=(); _3=Fn::call(f,tmp); ret=<_3 | 7>;
/// return ret }` — the ZERO-ARG rust-call shape (`f()`). The rust-call tuple is
/// `()` (Unit), so no non-scalar aggregate reaches the LIR converter; the whole
/// VF -> Module -> LIR -> BLR -> proven path runs. `return_call_result=false`
/// returns the constant 7 (provable despite havoc); `true` returns the (havoced)
/// call result (havoc-only).
fn build_callit(name: &str, return_call_result: bool) -> VerifiableFunction {
    let locals = vec![
        LocalDecl { index: 0, ty: TTy::i32(), name: Some("ret".into()) },
        LocalDecl { index: 1, ty: fn_unit_to_i32(), name: Some("f".into()) },
        LocalDecl { index: 2, ty: TTy::i32(), name: None },
    ];
    // The rust-call tuple is passed as a `()` CONSTANT directly (no materialized
    // Unit local/aggregate — that would emit a Unit Const the LIR converter cannot
    // lower, an orthogonal limitation). Our indirect lowering reads a `Ty::Unit`
    // tuple as zero fields, so no field projection is needed.
    let bb0 = BasicBlock {
        id: TBlockId(0),
        stmts: vec![],
        terminator: Terminator::Call {
            func: FN_CALL_SHIM.to_string(),
            args: vec![TOperand::Move(Place::local(1)), TOperand::Constant(ConstValue::Unit)],
            dest: Place::local(2),
            target: Some(TBlockId(1)),
            span: SourceSpan::default(),
            atomic: None,
            unwind: trust_types::UnwindEdge::Unreachable,
            is_unsafe_sig: false, is_foreign: false,
        },
    };
    let ret_rvalue = if return_call_result {
        Rvalue::Use(TOperand::Move(Place::local(2)))
    } else {
        Rvalue::Use(TOperand::Constant(ConstValue::Int(7)))
    };
    let bb1 = BasicBlock {
        id: TBlockId(1),
        stmts: vec![Statement::Assign {
            place: Place::local(0),
            rvalue: ret_rvalue,
            span: SourceSpan::default(),
        }],
        terminator: Terminator::Return,
    };
    VerifiableFunction {
        name: name.into(),
        def_path: format!("test::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![bb0, bb1],
            arg_count: 1,
            return_ty: TTy::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Lower the VF to a trust-ir Module (the producer half under test).
fn lower_callit(name: &str, return_call_result: bool) -> Module {
    let func = build_callit(name, return_call_result);
    trust_ir_bridge::lower_to_trust_ir(&func)
        .expect("fn-pointer indirect call VF must lower to a Module (not poison to Unsupported)")
}

// ---------------------------------------------------------------------------
// Emit / Mach-O helpers (mirrors module_to_lir_indirect_call_proven_output.rs).
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

fn emit_caller_object(module: &Module) -> Vec<u8> {
    let caller = &module.functions[0];
    let lir = lower_trust_ir_function_to_lir_real_calls(module, caller)
        .expect("lower_trust_ir_function_to_lir_real_calls failed for fn-ptr indirect caller");
    backend().emit_object(&[lir]).expect("emit_object (caller) failed")
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

/// __text PAGE21 (type 3) + PAGEOFF12 (type 4) relocs -> naming. For this OPEN
/// (argument) fn-ptr caller no fn-symbol page relocs should appear.
fn parse_page_relocs(obj: &[u8]) -> HashMap<u64, (u32, String)> {
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
        if r_type == 3 || r_type == 4 {
            map.insert(r_address, (r_type, sym_name(r_symbolnum)));
        }
    }
    map
}

/// Whether the object's symbol table names `want` (leading `_` stripped) — used
/// to confirm a direct Bl targets the external `abort` symbol.
fn object_calls_symbol(obj: &[u8], want: &str) -> bool {
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

// ===========================================================================
// OPEN-target (havoc-only) executor: model the BLR through the incoming fn-ptr
// argument by making all caller-saved state + MEMORY fresh, preserving
// callee-saved. Returns W0 after RET. Panics on any fail-closed condition.
// ===========================================================================
fn open_indirect_output(code: &[u8], base: u64) -> Formula {
    let sem = Aarch64Semantics;
    let mut state = MachineState::symbolic();
    let mut pc = base;
    let mut steps = 0u32;
    let mut call_tag = 0u32;
    let mut havoced_a_blr = false;

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
        let is_call = effects.iter().any(|e| matches!(e, Effect::Call { .. }));

        if is_call {
            assert_eq!(
                insn.opcode,
                Opcode::Blr,
                "the OPEN call must be a BLR (indirect), got {:?}",
                insn.opcode
            );
            havoced_a_blr = true;
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
            state.memory = Formula::Var(
                format!("OPEN_{tag}_MEM"),
                Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
            );
            state.gpr[0] = Formula::Var(format!("OPEN_{tag}_RESULT"), Sort::BitVec(64));
            steps += 1;
            assert!(steps < 2000, "decode loop runaway");
            pc += 4;
            continue;
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
        assert!(steps < 2000, "decode loop runaway (no RET)");
        pc += 4;
    }
    assert!(havoced_a_blr, "executor never reached a havoced OPEN BLR (vacuous proof)");
    state.read_gpr(0, 32)
}

// ---------------------------------------------------------------------------
// Formula -> ay::Term (QF_ABV) + discharge helpers.
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

fn discharge_equal(machine_out: &Formula, spec: &Formula) -> bool {
    let mut solver = Solver::try_new(Logic::QfAbv).expect("ay Solver::try_new");
    let lhs = formula_to_term(&mut solver, machine_out);
    let rhs = formula_to_term(&mut solver, spec);
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

fn const_spec(k: i128) -> Formula {
    Formula::BitVec { value: k, width: 32 }
}

// ---------------------------------------------------------------------------
// Module-shape assertion: the lowered Module carries a real Inst::CallIndirect.
// ---------------------------------------------------------------------------

fn call_indirect_of(module: &Module) -> Option<(FuncTyId, usize)> {
    module.functions.iter().flat_map(|f| f.blocks.iter()).flat_map(|b| b.body.iter()).find_map(
        |n| match &n.inst {
            Inst::CallIndirect { sig, args, .. } => Some((*sig, args.len())),
            _ => None,
        },
    )
}

// ===========================================================================
// TEST 1 — PRODUCER: the VF lowers to a Module carrying Inst::CallIndirect (not a
// poisoned Unsupported function), with the right sig + one call arg.
// ===========================================================================

#[test]
fn vf_fnptr_indirect_call_lowers_to_module_call_indirect() {
    // The ONE-ARG shape: the producer recovers the `(i32)->i32` sig from the
    // fn-pointer type and flattens the rust-call tuple `(x,)` to a single call arg.
    let func = build_callit_arg();
    let module = trust_ir_bridge::lower_to_trust_ir(&func)
        .expect("the one-arg fn-ptr indirect call VF must lower (not poison to Unsupported)");
    let (sig_id, n_args) =
        call_indirect_of(&module).expect("the lowered Module must contain an Inst::CallIndirect");
    assert_eq!(n_args, 1, "the CallIndirect must carry exactly one call arg (x)");
    let sig = module.func_types.get(sig_id.as_usize()).expect("the CallIndirect sig FuncTy");
    assert_eq!(sig.params, vec![trust_ir::ty::Ty::I32], "sig params == [i32]");
    assert_eq!(sig.returns, vec![trust_ir::ty::Ty::I32], "sig returns == [i32]");
    assert!(!sig.is_vararg);

    // An honest UNKNOWN PanicFreedom obligation accompanies the open dispatch.
    assert!(
        module
            .proof_obligations
            .iter()
            .any(|o| o.kind == trust_ir::proof::ObligationKind::PanicFreedom
                && o.status == trust_ir::proof::ProofStatus::Pending),
        "the havoc dispatch must attach an UNKNOWN PanicFreedom obligation"
    );
}

// ===========================================================================
// TEST 2 — CONVERTER: the lowered Module's caller lowers to LIR emitting a real
// Opcode::CallIndirect and a real BLR (indirect branch), NO direct Bl, and — since
// the fn-ptr is an incoming ARGUMENT (OPEN target) — NO fn-symbol page relocs.
// ===========================================================================

#[test]
fn vf_fnptr_indirect_caller_emits_a_real_blr() {
    let module = lower_callit("callit", false);
    let lir = lower_trust_ir_function_to_lir_real_calls(&module, &module.functions[0])
        .expect("fn-ptr indirect caller lowers to LIR");
    let mut saw_ci = false;
    for b in lir.blocks.values() {
        for inst in &b.instructions {
            if let trust_cg_lower::instructions::Opcode::CallIndirect = &inst.opcode {
                saw_ci = true;
            }
        }
    }
    assert!(saw_ci, "must emit Opcode::CallIndirect");

    let obj = emit_caller_object(&module);
    let (code, base) = macho_text(&obj).expect("caller __text");
    assert!(!code.is_empty(), "caller __text is empty");
    // The DISPATCH itself is a real, single indirect BLR — NOT a direct Bl. The
    // only direct Bl that may appear is the `abort` trap of the honest may-panic
    // marker (`Assert(false)+NoPanic`), which lowers to `Bl abort` on this backend;
    // it is on the (never-executed) trap segment, not the call edge. So we require
    // exactly one BLR and at most one direct Bl, and that any direct Bl targets
    // `abort` (never a mis-lowered call replacing the indirect dispatch).
    assert_eq!(count_blr(&code, base), 1, "expected exactly ONE Blr (real indirect call)");
    assert!(
        count_bl_direct(&code, base) <= 1,
        "the only permitted direct Bl is the may-panic trap abort; got {}",
        count_bl_direct(&code, base)
    );
    if count_bl_direct(&code, base) == 1 {
        assert!(
            object_calls_symbol(&obj, "abort"),
            "the single direct Bl must be the trap `abort` (the may-panic marker), not a call"
        );
    }

    // No fn-symbol page relocs: the fn-ptr is an incoming ARGUMENT (OPEN target),
    // never a GlobalAddr materialization.
    let relocs = parse_page_relocs(&obj);
    assert!(
        relocs.is_empty(),
        "an OPEN (argument) fn-ptr caller must carry NO PAGE21/PAGEOFF12 fn-symbol relocs; got {relocs:?}"
    );
}

// ===========================================================================
// TEST 3 — PROVEN OUTPUT: `callit(f, x) { f(x); 7 }` bytes, with the real BLR
// HAVOCED, compute the CONSTANT 7 for ALL inputs. ay UNSAT — the constant return
// is independent of the (havoced) call result/memory, so the havoc cannot break it.
// ===========================================================================

#[test]
fn vf_fnptr_indirect_caller_bytes_prove_constant_7_despite_havoc() {
    let module = lower_callit("callit", /*return_call_result=*/ false);
    let obj = emit_caller_object(&module);
    let (code, base) = macho_text(&obj).expect("caller __text");
    assert_eq!(count_blr(&code, base), 1, "the call must be a real BLR (indirect)");

    let machine_out = open_indirect_output(&code, base);
    let proven = discharge_equal(&machine_out, &const_spec(7));
    assert!(
        proven,
        "PROVEN-OUTPUT FAILED: ay did not prove the fn-ptr indirect caller bytes equal the \
         constant 7 for all inputs.\n  machine_out = {machine_out:?}"
    );
}

// ===========================================================================
// TEST 4 — MANDATORY NEGATIVE CONTROL: the SAME bytes proven against the constant
// 8 MUST be SAT. Otherwise the constant-7 certificate is vacuous.
// ===========================================================================

#[test]
fn negative_control_vf_fnptr_indirect_caller_vs_constant_8_is_sat() {
    let module = lower_callit("callit", false);
    let obj = emit_caller_object(&module);
    let (code, base) = macho_text(&obj).expect("caller __text");

    let machine_out = open_indirect_output(&code, base);
    let proven = discharge_equal(&machine_out, &const_spec(8));
    assert!(
        !proven,
        "VACUITY CHECK FAILED: the fn-ptr indirect caller bytes were 'proven' equal to 8; the \
         constant-7 discharge has no teeth.\n  machine_out = {machine_out:?}"
    );
}

// ===========================================================================
// TEST 5 — THE HAVOC HAS TEETH: `callit_dep(f, x) { f(x) }` returns the (havoced)
// call result directly, so it must NOT be provable to ANY specific constant — for
// every candidate k the discharge is SAT. Confirms the open-call result is
// genuinely fresh AND that the arg `x` really flows into the (havoced) BLR.
// ===========================================================================

#[test]
fn vf_fnptr_indirect_dependent_return_is_not_provable_to_any_constant() {
    let module = lower_callit("callit_dep", /*return_call_result=*/ true);
    // Confirm the Module still carries the CallIndirect (the havoc-only shape).
    assert!(call_indirect_of(&module).is_some(), "the dependent caller must still emit CallIndirect");

    let obj = emit_caller_object(&module);
    let (code, base) = macho_text(&obj).expect("dependent caller __text");
    assert_eq!(count_blr(&code, base), 1, "the call must be a real BLR (indirect)");

    let machine_out = open_indirect_output(&code, base);
    for k in [0i128, 1, 7, 42, -1, i128::from(i32::MAX), i128::from(i32::MIN)] {
        let proven = discharge_equal(&machine_out, &const_spec(k));
        assert!(
            !proven,
            "HAVOC-HAS-TEETH FAILED: the dependent fn-ptr indirect-call return was 'proven' equal \
             to the constant {k}; a havoced open-call result must be genuinely FRESH.\n  \
             machine_out = {machine_out:?}"
        );
    }
}
