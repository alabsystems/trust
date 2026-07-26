// module_to_lir_mem_proven_output.rs — the "trust-ir first" codegen seam,
// extended to MEMORY (Alloca / Store / Load over a scalar stack slot), proven
// over the real emitted bytes.
//
// GOAL: take a `trust_ir::Module` for
//
//     fn f(a: i32) -> i32 { let p: i32 = uninit; *p = a + 1; *p }
//
// represented as
//
//     bb0(a):  %1 = const 1 : i32
//              %2 = add a, %1 : i32        ; a + 1
//              %3 = alloca i32             ; a stack slot (Ptr)
//              store %2 -> *%3             ; write a+1 into the slot
//              %4 = load *%3 : i32         ; read it back
//              return %4
//
// lower it to trust-cg LIR via the EXTENDED `lower_trust_ir_function_to_lir`
// converter (Alloca -> StackAddr + a fresh StackSlotInfo; Store -> Store;
// Load -> Load), feed that LIR into the EXISTING verified
// `TrustCgCodegenBackend::emit_object` emitter, and prove the emitted machine
// bytes compute `a + 1` for ALL inputs four ways:
//
//   (1) VALUE-DIFFERENTIAL (concrete): the trust-ir reference INTERPRETER
//       executes the Module on f(5) = 6 (the value travels THROUGH stack
//       memory: Alloca -> Store -> Load);
//   (2) Ldr/Str-PRESENT: the emitted __text must contain a real `Str` AND a
//       real `Ldr` — proof that the store/load through memory survived to the
//       machine bytes and was not folded into a register-only `a+1`;
//   (3) PROVEN-OUTPUT (infinite domain): the emitted bytes are decoded into
//       machine effects (NOT reconstructed from the IR), the `Str`/`Ldr` become
//       array-theory `Store`/`Select` over the symbolic MEM, path-merged into a
//       symbolic output Formula; ay (QF_ABV) proves that Formula equals `a + 1`
//       for ALL 2^32 inputs (UNSAT of the negation); and
//   (4) NEGATIVE CONTROL: the SAME emitted bytes proven against an `a + 2` spec
//       MUST be SAT — otherwise the discharge is vacuous.
//
// The machine output is BYTE-DERIVED (emit -> decode -> effects -> array
// theory), NEVER reconstructed from the IR; a wrong memory lowering (store to
// the wrong slot, drop the store, wrong width) makes ay return a COUNTEREXAMPLE
// rather than silently passing — demonstrated by the mandatory SAT negative
// control and the Ldr/Str-present assertion.
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
use trust_ir::{Block, Function as IrFunction, Module};

// ---------------------------------------------------------------------------
// Build a trust_ir::Module for `f(a) = { let p; *p = a + k; *p }` (= a + k),
// where the value passes THROUGH a scalar i32 stack slot.
// ---------------------------------------------------------------------------

fn make_mem_add_module(name: &str, k: i128) -> Module {
    let mut module = Module::new("mem_module");
    module.func_types.push(FuncTy {
        params: vec![Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut function = IrFunction::new(FuncId::new(0), name, FuncTyId::new(0), BlockId::new(0));

    let a = ValueId::new(0);
    let kconst = ValueId::new(1);
    let sum = ValueId::new(2);
    let ptr = ValueId::new(3);
    let loaded = ValueId::new(4);

    let mut bb0 = Block::new(BlockId::new(0));
    bb0.params.push((a, Ty::I32));
    // %1 = const k : i32
    bb0.body.push(
        InstrNode::new(Inst::Const { ty: Ty::I32, value: trust_ir::Constant::Int(k) })
            .with_result(kconst),
    );
    // %2 = add a, %1 : i32
    bb0.body.push(
        InstrNode::new(Inst::BinOp { op: BinOp::Add, ty: Ty::I32, lhs: a, rhs: kconst })
            .with_result(sum),
    );
    // %3 = alloca i32
    bb0.body.push(
        InstrNode::new(Inst::Alloca { ty: Ty::I32, count: None, align: None }).with_result(ptr),
    );
    // store %2 -> *%3
    bb0.body.push(InstrNode::new(Inst::Store {
        ty: Ty::I32,
        ptr,
        value: sum,
        volatile: false,
        align: None,
    }));
    // %4 = load *%3 : i32
    bb0.body.push(
        InstrNode::new(Inst::Load { ty: Ty::I32, ptr, volatile: false, align: None })
            .with_result(loaded),
    );
    // return %4
    bb0.body.push(InstrNode::new(Inst::Return { values: vec![loaded] }));

    function.blocks.push(bb0);
    module.functions.push(function);
    module
}

/// f(a) = a + 1, routed through a stack slot.
fn make_mem_inc_module() -> Module {
    make_mem_add_module("ir_mem_inc", 1)
}

// ---------------------------------------------------------------------------
// Emit the Module-derived LIR to an object and extract __text.
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

fn emit_module_text(module: &Module) -> (Vec<u8>, u64) {
    let function = &module.functions[0];
    let lir = lower_trust_ir_function_to_lir(module, function)
        .expect("lower_module_to_lir failed for scalar memory inc");
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

/// Decode every 4-byte word in __text and count single-register `Str` / `Ldr`
/// opcodes (excluding the `Stp`/`Ldp` frame pair ops). The user store/load
/// through the stack slot lowers to one of each; a register-only fold would
/// emit neither.
fn count_single_ldr_str(code: &[u8], base: u64) -> (usize, usize) {
    let mut strs = 0usize;
    let mut ldrs = 0usize;
    let mut pc = base;
    while (pc - base) as usize + 4 <= code.len() {
        let off = (pc - base) as usize;
        let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
        if let Ok(insn) = decode_aarch64(&bytes, pc) {
            match insn.opcode {
                Opcode::Str | Opcode::Strb | Opcode::Strh => strs += 1,
                Opcode::Ldr | Opcode::Ldrb | Opcode::Ldrh | Opcode::Ldrsb | Opcode::Ldrsh
                | Opcode::Ldrsw => ldrs += 1,
                _ => {}
            }
        }
        pc += 4;
    }
    (strs, ldrs)
}

// ===========================================================================
// SYMBOLIC EXECUTOR (straight-line; mirrors proven_output_cfg_mem.rs). machine
// out = W0 after RET. The `Str`/`Ldr` effects thread through MachineState's
// symbolic MEM array; nothing about the source IR enters the Formula.
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
// Formula -> ay::Term translation (QF_ABV: bitvectors + arrays for MEM).
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
        // ---- Arrays (Ldr / Str) ----
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

/// Discharge `machine_out == ir_out` over ALL inputs via ay (QF_ABV: array
/// theory for the MEM round trip). UNSAT of the negation == proven-equal.
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
// IR-spec helpers. W_0 = low 32 bits of argument register X_0.
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

/// a + k spec.
fn add_const_spec(k: i128) -> Formula {
    Formula::BvAdd(Box::new(wn(0)), Box::new(bv32(k)), 32)
}

// ---------------------------------------------------------------------------
// VALUE-DIFFERENTIAL: the trust-ir reference interpreter on the Module. The
// value travels Alloca -> Store -> Load THROUGH stack memory.
// ---------------------------------------------------------------------------

fn interpret_mem(module: &Module, a: i128) -> i128 {
    let interp = Interpreter::with_module(module);
    let args = vec![InterpretValue::int(Ty::I32, a).expect("arg a")];
    let outcome = interp
        .execute_func(FuncId::new(0), args)
        .expect("interpreter execute_func failed");
    outcome.returns[0].as_int().expect("integer return").as_signed()
}

// ===========================================================================
// TEST 1 — the converter produces well-formed LIR with a stack slot that emits
// a non-empty object carrying a real Str AND a real Ldr.
// ===========================================================================

#[test]
fn module_to_lir_emits_object_with_real_store_and_load() {
    let module = make_mem_inc_module();
    // The converter must allocate exactly one stack slot for the i32 alloca.
    let lir =
        lower_trust_ir_function_to_lir(&module, &module.functions[0]).expect("lower");
    assert_eq!(lir.stack_slots.len(), 1, "expected exactly one i32 stack slot");
    assert_eq!(lir.stack_slots[0].size, 4, "i32 slot is 4 bytes");

    let (code, base) = emit_module_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty for Module-derived mem inc");

    // The store/load through the slot must survive to the machine bytes: at
    // least one Str and one Ldr (proof memory was not folded into a register
    // only `a+1`).
    let (strs, ldrs) = count_single_ldr_str(&code, base);
    assert!(strs >= 1, "expected >= 1 Str (the slot store) in emitted bytes, got {strs}");
    assert!(ldrs >= 1, "expected >= 1 Ldr (the slot load) in emitted bytes, got {ldrs}");
}

// ===========================================================================
// TEST 2 — concrete value-differential: the Module interpreter computes a+1
// with the value routed through stack memory.
// ===========================================================================

#[test]
fn module_interpreter_mem_inc_is_correct() {
    let module = make_mem_inc_module();
    assert_eq!(interpret_mem(&module, 5), 6);
    assert_eq!(interpret_mem(&module, 0), 1);
    assert_eq!(interpret_mem(&module, -1), 0);
    assert_eq!(interpret_mem(&module, 41), 42);
}

// ===========================================================================
// TEST 3 — PROVEN OUTPUT (infinite domain): the emitted bytes of the
// Module-derived store-then-load inc compute `a + 1` for ALL inputs. The MEM
// round trip is discharged by ay's array theory (Store then Select reduces to
// the stored value).
// ===========================================================================

#[test]
fn module_derived_mem_inc_bytes_compute_a_plus_1_for_all_inputs() {
    let module = make_mem_inc_module();

    // Value-differential precondition before the symbolic proof.
    assert_eq!(interpret_mem(&module, 5), 6, "value-differential precondition");

    let (code, base) = emit_module_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty");

    let machine_out = symbolic_machine_output(&code, base);
    let spec = add_const_spec(1);

    let proven = discharge_equal(&machine_out, &spec);
    assert!(
        proven,
        "PROVEN-OUTPUT FAILED: ay did not prove the Module-derived store-then-load \
         inc bytes equal a+1 for all inputs.\n  machine_out = {machine_out:?}"
    );
}

// ===========================================================================
// TEST 4 — MANDATORY NEGATIVE CONTROL: the SAME inc bytes proven against an
// `a + 2` spec MUST be SAT. A non-SAT result would make the positive
// certificate vacuous (e.g. if the store/load were silently dropped).
// ===========================================================================

#[test]
fn negative_control_mem_inc_bytes_vs_a_plus_2_is_sat() {
    let module = make_mem_inc_module();
    let (code, base) = emit_module_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty");

    let machine_out = symbolic_machine_output(&code, base);
    let wrong = add_const_spec(2); // deliberately the WRONG spec.

    let proven = discharge_equal(&machine_out, &wrong);
    assert!(
        !proven,
        "VACUITY CHECK FAILED: the inc bytes were 'proven' equal to a+2; \
         the memory discharge has no teeth.\n  machine_out = {machine_out:?}"
    );
}
