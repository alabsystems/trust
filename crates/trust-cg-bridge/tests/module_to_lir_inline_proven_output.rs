// module_to_lir_inline_proven_output.rs — the "trust-ir first" codegen seam,
// extended to CALLS of local pure leaf functions via Module-level INLINING,
// proven over the real emitted bytes.
//
// GOAL: take a `trust_ir::Module` with TWO functions
//
//     fn add(x: i32, y: i32) -> i32 { x + y }            // FuncId 1 (callee)
//     fn caller(a: i32, b: i32) -> i32 { add(a, b) + 1 } // FuncId 0
//
// and lower `caller` to trust-cg LIR via `lower_trust_ir_function_to_lir`. The
// converter runs a Module-level INLINING PRE-PASS first: the `Call` to the
// local pure leaf `add` is spliced inline (params bound to args, the callee's
// `Return` routed to the call's result via a `Copy`), so the function the LIR
// converter sees is CALL-FREE straight-line code. The existing scalar
// converter + proof machinery then handle it with ZERO proof-executor changes.
//
// We prove the emitted machine bytes compute `a + b + 1` for ALL inputs:
//
//   (1) VALUE-DIFFERENTIAL (concrete): the trust-ir reference INTERPRETER
//       executes the Module on caller(2,3) = 6 and caller(-1,1) = 1 — the call
//       to `add` runs through the interpreter's real call machinery;
//   (2) NO-Bl / NO-Call: the emitted __text must contain NO `Bl` (AArch64 call)
//       — proof the call was INLINED, not emitted as a real call edge;
//   (3) PROVEN-OUTPUT (infinite domain): the emitted bytes are decoded into
//       machine effects (NOT reconstructed from the IR), path-merged into a
//       symbolic output Formula; ay (QF_BV) proves that Formula equals
//       `a + b + 1` for ALL 2^64 input pairs (UNSAT of the negation); and
//   (4) NEGATIVE CONTROL: the SAME emitted bytes proven against an `a + b + 2`
//       spec MUST be SAT — otherwise the discharge is vacuous.
//
// The machine output is BYTE-DERIVED (emit -> decode -> effects), NEVER
// reconstructed from the IR; a wrong inline (wrong arg binding, dropped call,
// wrong return routing) makes ay return a COUNTEREXAMPLE rather than silently
// passing — demonstrated by the mandatory SAT negative control.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![cfg(feature = "ay-proofs")]

use ay::{BigInt, Logic, Solver, Term};
use trust_cg_bridge::codegen_backend::{TrustCgCodegenBackend, TrustCgTargetArch};
use trust_cg_bridge::lower_trust_ir_function_to_lir;
use trust_disasm::{Opcode, decode_aarch64};
use trust_machine_sem::{Aarch64Semantics, MachineState, Semantics};
use trust_types::{Formula, Sort};

use trust_ir::inst::{BinOp, Inst};
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::node::InstrNode;
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{Block, Constant, Function as IrFunction, Module};

// ---------------------------------------------------------------------------
// Build a trust_ir::Module for caller(a,b) = add(a,b) + k, where `add` is a
// LOCAL pure leaf `add(x,y) = x + y`. The caller's body is a single `Call` plus
// a `+k`, which the inlining pre-pass turns into call-free straight-line code.
// ---------------------------------------------------------------------------

fn make_caller_add_module(k: i128) -> Module {
    let mut module = Module::new("inline_module");
    // ty 0: caller (i32,i32)->i32 ; ty 1: callee add (i32,i32)->i32.
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
    // %2 = call add(a, b)
    cb.body.push(
        InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![a, b] }).with_result(called),
    );
    // %3 = const k : i32
    cb.body.push(
        InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(k) }).with_result(kconst),
    );
    // %4 = add %2, %3
    cb.body.push(
        InstrNode::new(Inst::BinOp { op: BinOp::Add, ty: Ty::I32, lhs: called, rhs: kconst })
            .with_result(out),
    );
    cb.body.push(InstrNode::new(Inst::Return { values: vec![out] }));
    caller.blocks.push(cb);

    // FuncId 0 must be at index 0 (the caller) — the emitter lowers functions[0].
    module.functions.push(caller);
    module.functions.push(add);
    module
}

/// caller(a,b) = add(a,b) + 1.
fn make_caller_inc_module() -> Module {
    make_caller_add_module(1)
}

// ---------------------------------------------------------------------------
// Emit the Module-derived LIR (after inlining) to an object and extract __text.
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

fn emit_caller_text(module: &Module) -> (Vec<u8>, u64) {
    // Lower the CALLER (functions[0]); the inlining pre-pass splices `add`.
    let caller = &module.functions[0];
    let lir = lower_trust_ir_function_to_lir(module, caller)
        .expect("lower_trust_ir_function_to_lir failed for inlined caller");
    let triple = host_triple();
    let backend = TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::host(), triple);
    let obj = backend.emit_object(&[lir]).expect("emit_object failed");
    macho_text(&obj).expect("could not extract __text section from emitted object")
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

/// Decode every 4-byte word in __text and count `Bl` (AArch64 call) opcodes. An
/// INLINED call emits NONE; a real (un-inlined) call edge would emit one.
fn count_bl(code: &[u8], base: u64) -> usize {
    let mut bls = 0usize;
    let mut pc = base;
    while (pc - base) as usize + 4 <= code.len() {
        let off = (pc - base) as usize;
        let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
        if let Ok(insn) = decode_aarch64(&bytes, pc) {
            if matches!(insn.opcode, Opcode::Bl | Opcode::Blr) {
                bls += 1;
            }
        }
        pc += 4;
    }
    bls
}

// ===========================================================================
// SYMBOLIC EXECUTOR (straight-line). machine out = W0 after RET. Nothing about
// the source IR enters the Formula — the bytes are decoded and stepped.
// ===========================================================================

fn symbolic_machine_output(code: &[u8], base: u64) -> Formula {
    let sem = Aarch64Semantics;
    let mut state = MachineState::symbolic();
    let mut pc = base;
    let mut steps = 0u32;

    loop {
        let off = (pc - base) as usize;
        if off + 4 > code.len() {
            panic!("ran past end of __text without hitting RET");
        }
        let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
        let insn = decode_aarch64(&bytes, pc).expect("decode_aarch64 failed");
        let is_ret = insn.opcode == Opcode::Ret;

        let effects = sem
            .effects(&state, &insn)
            .unwrap_or_else(|e| panic!("Aarch64Semantics::effects failed at {pc:#x}: {e:?}"));
        state.apply_effects(&effects).unwrap_or_else(|e| {
            panic!(
                "apply_effects rejected an effect from emitted insn {:?} at {:#x}: {:?}",
                insn.opcode, pc, e
            )
        });

        steps += 1;
        if is_ret {
            break;
        }
        pc += 4;
        assert!(steps < 1000, "decode loop runaway (no RET)");
    }

    state.read_gpr(0, 32)
}

// ---------------------------------------------------------------------------
// Formula -> ay::Term translation (QF_BV).
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
        other => panic!("unexpected Var sort in machine output for {name}: {other:?}"),
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
        other => panic!(
            "formula_to_term: unhandled Formula variant in machine output: {other:?}\n\
             (the symbolic execution produced a shape this harness does not yet translate)"
        ),
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

/// Discharge `machine_out == ir_out` over ALL inputs via ay. UNSAT of the
/// negation == proven-equal.
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

// ---------------------------------------------------------------------------
// IR-spec helpers. W_n = low 32 bits of argument register X_n.
// ---------------------------------------------------------------------------

fn wn(n: u32) -> Formula {
    Formula::BvExtract {
        inner: Box::new(Formula::Var(format!("X{n}"), Sort::BitVec(64))),
        high: 31,
        low: 0,
    }
}

fn bv32(value: i128) -> Formula {
    Formula::BitVec { value, width: 32 }
}

/// a + b + k spec.
fn add_add_const_spec(k: i128) -> Formula {
    Formula::BvAdd(
        Box::new(Formula::BvAdd(Box::new(wn(0)), Box::new(wn(1)), 32)),
        Box::new(bv32(k)),
        32,
    )
}

// ---------------------------------------------------------------------------
// VALUE-DIFFERENTIAL: the trust-ir reference interpreter on the Module. The
// caller's `Call` to `add` runs through the interpreter's real call machinery.
// ---------------------------------------------------------------------------

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
// TEST 1 — the inlining pre-pass produces well-formed call-free LIR whose
// emitted __text carries NO `Bl` (the call was inlined, not emitted).
// ===========================================================================

#[test]
fn inlined_caller_emits_object_with_no_call() {
    let module = make_caller_inc_module();

    // The lowered LIR must carry no LIR Call opcode.
    let lir = lower_trust_ir_function_to_lir(&module, &module.functions[0])
        .expect("inlined caller lowers");
    for block in lir.blocks.values() {
        for inst in &block.instructions {
            assert!(
                !matches!(
                    inst.opcode,
                    trust_cg_lower::instructions::Opcode::Call { .. }
                        | trust_cg_lower::instructions::Opcode::CallIndirect
                ),
                "a LIR call opcode survived inlining: {:?}",
                inst.opcode
            );
        }
    }

    let (code, base) = emit_caller_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty for inlined caller");

    // No AArch64 `Bl` may appear: the call was inlined, not emitted.
    let bls = count_bl(&code, base);
    assert_eq!(bls, 0, "expected ZERO Bl/Blr (call inlined) in emitted bytes, got {bls}");
}

// ===========================================================================
// TEST 2 — concrete value-differential: the Module interpreter computes
// caller(a,b) = add(a,b) + 1 through the real call.
// ===========================================================================

#[test]
fn module_interpreter_caller_inc_is_correct() {
    let module = make_caller_inc_module();
    assert_eq!(interpret_caller(&module, 2, 3), 6); // add(2,3)+1
    assert_eq!(interpret_caller(&module, -1, 1), 1); // add(-1,1)+1
    assert_eq!(interpret_caller(&module, 0, 0), 1);
    assert_eq!(interpret_caller(&module, 40, 1), 42);
}

// ===========================================================================
// TEST 3 — PROVEN OUTPUT (infinite domain): the emitted bytes of the inlined
// caller compute `a + b + 1` for ALL inputs.
// ===========================================================================

#[test]
fn inlined_caller_bytes_compute_a_plus_b_plus_1_for_all_inputs() {
    let module = make_caller_inc_module();

    // Value-differential precondition before the symbolic proof.
    assert_eq!(interpret_caller(&module, 2, 3), 6, "value-differential precondition");

    let (code, base) = emit_caller_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty");
    assert_eq!(count_bl(&code, base), 0, "the call must be inlined (no Bl)");

    let machine_out = symbolic_machine_output(&code, base);
    let spec = add_add_const_spec(1);

    let proven = discharge_equal(&machine_out, &spec);
    assert!(
        proven,
        "PROVEN-OUTPUT FAILED: ay did not prove the inlined caller bytes equal \
         a+b+1 for all inputs.\n  machine_out = {machine_out:?}"
    );
}

// ===========================================================================
// TEST 4 — MANDATORY NEGATIVE CONTROL: the SAME caller bytes proven against an
// `a + b + 2` spec MUST be SAT. A non-SAT result would make the positive
// certificate vacuous (e.g. if the inlined add were silently dropped).
// ===========================================================================

#[test]
fn negative_control_inlined_caller_vs_a_plus_b_plus_2_is_sat() {
    let module = make_caller_inc_module();
    let (code, base) = emit_caller_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty");

    let machine_out = symbolic_machine_output(&code, base);
    let wrong = add_add_const_spec(2); // deliberately the WRONG spec.

    let proven = discharge_equal(&machine_out, &wrong);
    assert!(
        !proven,
        "VACUITY CHECK FAILED: the caller bytes were 'proven' equal to a+b+2; \
         the inline discharge has no teeth.\n  machine_out = {machine_out:?}"
    );
}
