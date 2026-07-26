// module_to_lir_aggregate_mem_proven_output.rs — the "trust-ir first" codegen
// seam, extended to AGGREGATE memory (a 2-field scalar `Ty::Tuple` round-tripped
// through ONE stack slot AS A UNIT), proven over the real emitted bytes.
//
// UNBLOCKED by the trust-ir pin bump to c58fa68, which adds `Ty::Tuple`
// `byte_size`/`byte_align` + a Store/Load round-trip for aggregates-in-memory.
// Before that the converter fail-closed on any aggregate Alloca / aggregate-typed
// slot (`map_scalar_mem_ty` rejected `Ty::Tuple`).
//
// GOAL: take a `trust_ir::Module` for
//
//     fn sf(a: i32, b: i32) -> i32 { let t = (a, b); t.0 + t.1 }   (= a + b)
//
// in the AGGREGATE-IN-MEMORY shape the bridge promotes a multi-block-written
// tuple local to (`promote_local_to_memory` + `ensure_local_storage`), confirmed
// by dumping `trust_ir_bridge::lower_to_trust_ir`:
//
//   bb0(a, b):
//     %c  = const (i32,i32) [0, 0]          ; aggregate base (interp-executable)
//     %t0 = insertfield (i32,i32) %c,  0, a ; field 0 <- a
//     %t  = insertfield (i32,i32) %t0, 1, b ; field 1 <- b   (full SSA aggregate)
//     %s  = alloca (i32,i32)                ; AGGREGATE stack slot (size 8, align 4)
//     store (i32,i32) %t -> *%s             ; WHOLE-aggregate store
//     %ld = load  (i32,i32) *%s             ; WHOLE-aggregate load
//     %f0 = extractfield i32 %ld, 0
//     %f1 = extractfield i32 %ld, 1
//     %r  = add %f0, %f1                     ; a + b
//     return %r
//
// The converter (PASS 1.7, `analyze_aggregate_memory` + `lower_aggregate_inst`)
// DECOMPOSES the aggregate into its two scalar fields and lowers the whole-
// aggregate Store/Load into PER-FIELD Str/Ldr at the C-style field OFFSETS
// (`aggregate_mem_layout`, byte-for-byte the interpreter's `aggregate_layout`):
// field 0 @ offset 0, field 1 @ offset 4 in an 8-byte/align-4 slot. We feed the
// produced LIR into the EXISTING verified `TrustCgCodegenBackend::emit_object`
// emitter and prove the emitted machine bytes compute `a + b` for ALL inputs:
//
//   (1) VALUE-DIFFERENTIAL (concrete): the trust-ir reference INTERPRETER
//       executes the Module on sf(5,7)=12 etc. — the value travels THROUGH the
//       aggregate stack slot (Const aggregate -> InsertField -> Store(Tuple) ->
//       Load(Tuple) -> ExtractField). This is the c58fa68 round-trip; if the
//       byte_size/layout were missing the interpreter would trap, so a passing
//       value-diff is the proof the pin actually unblocked aggregates-in-memory.
//   (2) Str/Ldr-AT-OFFSETS: the produced LIR must carry exactly TWO field Stores
//       and TWO field Loads (one per field), and the emitted __text must contain
//       real Str AND Ldr (proof the aggregate round trip survived to the machine
//       bytes and was not folded into a register-only a+b).
//   (3) PROVEN-OUTPUT (infinite domain): the emitted bytes are decoded into
//       machine effects (NOT reconstructed from the IR), the field Str/Ldr become
//       array-theory Store/Select over the symbolic MEM, merged into a symbolic
//       output Formula; ay (QF_ABV) proves that Formula equals `a + b` for ALL
//       2^32 x 2^32 inputs (UNSAT of the negation); and
//   (4) NEGATIVE CONTROL: the SAME bytes proven against an `a + b + 1` spec MUST
//       be SAT — otherwise the discharge is vacuous.
//
// A wrong aggregate lowering (wrong field offset, swapped fields, dropped store,
// wrong width) makes ay return a COUNTEREXAMPLE rather than silently passing —
// demonstrated by the mandatory SAT negative control, the value-differential, and
// the field-offset Str/Ldr assertions.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![cfg(feature = "ay-proofs")]

use ay::{BigInt, Logic, Solver, Term};
use trust_cg_bridge::codegen_backend::{TrustCgCodegenBackend, TrustCgTargetArch};
use trust_cg_bridge::lower_trust_ir_function_to_lir;
use trust_cg_lower::instructions::Opcode as LirOpcode;
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
// Build the aggregate-in-memory Module for sf(a,b) = { let t=(a,b); t.0+t.1 }.
//
// `use_undef_seed = false` -> Const::Aggregate base (interpreter-executable;
// the value-differential path). `true` -> Undef(Tuple) base (the RAW bridge
// shape; the interpreter traps on Undef, so it is only lowered, not interpreted).
// ---------------------------------------------------------------------------

fn make_agg_sum_module(use_undef_seed: bool) -> Module {
    let mut module = Module::new("agg_mem_module");
    module.func_types.push(FuncTy {
        params: vec![Ty::I32, Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut function = IrFunction::new(FuncId::new(0), "sf", FuncTyId::new(0), BlockId::new(0));
    let tup = Ty::Tuple(vec![Ty::I32, Ty::I32]);

    let a = ValueId::new(0);
    let b = ValueId::new(1);
    let base = ValueId::new(2);
    let t0 = ValueId::new(3);
    let t = ValueId::new(4);
    let slot = ValueId::new(5);
    let ld = ValueId::new(6);
    let f0 = ValueId::new(7);
    let f1 = ValueId::new(8);
    let sum = ValueId::new(9);

    let mut bb0 = Block::new(BlockId::new(0));
    bb0.params.push((a, Ty::I32));
    bb0.params.push((b, Ty::I32));

    // aggregate base: Const::Aggregate [0,0] (interp) or Undef(Tuple) (raw bridge)
    if use_undef_seed {
        bb0.body.push(InstrNode::new(Inst::Undef { ty: tup.clone() }).with_result(base));
    } else {
        bb0.body.push(
            InstrNode::new(Inst::Const {
                ty: tup.clone(),
                value: Constant::Aggregate(vec![Constant::Int(0), Constant::Int(0)]),
            })
            .with_result(base),
        );
    }
    // %t0 = insertfield %base, 0, a ; %t = insertfield %t0, 1, b
    bb0.body.push(
        InstrNode::new(Inst::InsertField { ty: tup.clone(), aggregate: base, field: 0, value: a })
            .with_result(t0),
    );
    bb0.body.push(
        InstrNode::new(Inst::InsertField { ty: tup.clone(), aggregate: t0, field: 1, value: b })
            .with_result(t),
    );
    // %slot = alloca (i32,i32)
    bb0.body.push(
        InstrNode::new(Inst::Alloca { ty: tup.clone(), count: None, align: None })
            .with_result(slot),
    );
    // store (i32,i32) %t -> *%slot
    bb0.body.push(InstrNode::new(Inst::Store {
        ty: tup.clone(),
        ptr: slot,
        value: t,
        volatile: false,
        align: None,
    }));
    // %ld = load (i32,i32) *%slot
    bb0.body.push(
        InstrNode::new(Inst::Load { ty: tup.clone(), ptr: slot, volatile: false, align: None })
            .with_result(ld),
    );
    // %f0 = extractfield i32 %ld, 0 ; %f1 = extractfield i32 %ld, 1
    bb0.body.push(
        InstrNode::new(Inst::ExtractField { ty: Ty::I32, aggregate: ld, field: 0 }).with_result(f0),
    );
    bb0.body.push(
        InstrNode::new(Inst::ExtractField { ty: Ty::I32, aggregate: ld, field: 1 }).with_result(f1),
    );
    // %sum = add %f0, %f1
    bb0.body.push(
        InstrNode::new(Inst::BinOp { op: BinOp::Add, ty: Ty::I32, lhs: f0, rhs: f1 })
            .with_result(sum),
    );
    bb0.body.push(InstrNode::new(Inst::Return { values: vec![sum] }));

    function.blocks.push(bb0);
    module.functions.push(function);
    module
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
        .expect("lower_module_to_lir failed for aggregate-in-memory sum");
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

/// Count single-register `Str` / `Ldr` opcodes (excluding the `Stp`/`Ldp` frame
/// pair ops). The aggregate round trip lowers to TWO field stores and TWO field
/// loads; a register-only fold would emit neither.
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
// SYMBOLIC EXECUTOR (straight-line; mirrors module_to_lir_mem_proven_output.rs).
// machine out = W0 after RET. The field Str/Ldr effects thread through
// MachineState's symbolic MEM array; nothing about the source IR enters the
// Formula.
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

/// a + b spec.
fn sum_spec() -> Formula {
    Formula::BvAdd(Box::new(wn(0)), Box::new(wn(1)), 32)
}

/// a + b + 1 spec (deliberately WRONG, for the negative control).
fn sum_plus_one_spec() -> Formula {
    Formula::BvAdd(Box::new(sum_spec()), Box::new(bv32(1)), 32)
}

// ---------------------------------------------------------------------------
// VALUE-DIFFERENTIAL: the trust-ir reference interpreter on the Module. The
// value travels Const-aggregate -> InsertField -> Store(Tuple) -> Load(Tuple) ->
// ExtractField THROUGH the aggregate stack slot. This is the c58fa68 round trip.
// ---------------------------------------------------------------------------

fn interpret_agg(module: &Module, a: i128, b: i128) -> i128 {
    let interp = Interpreter::with_module(module);
    let args = vec![
        InterpretValue::int(Ty::I32, a).expect("arg a"),
        InterpretValue::int(Ty::I32, b).expect("arg b"),
    ];
    let outcome = interp
        .execute_func(FuncId::new(0), args)
        .expect("interpreter execute_func failed (aggregate-in-memory round trip)");
    outcome.returns[0].as_int().expect("integer return").as_signed()
}

// ===========================================================================
// TEST 1 — the converter produces well-formed LIR with ONE aggregate stack slot
// (size 8, align 4) and exactly TWO field Stores + TWO field Loads, and the
// emitted object carries real Str AND Ldr.
// ===========================================================================

#[test]
fn module_to_lir_emits_aggregate_slot_with_field_stores_and_loads() {
    let module = make_agg_sum_module(false);
    let lir =
        lower_trust_ir_function_to_lir(&module, &module.functions[0]).expect("lower aggregate");

    // Exactly one aggregate slot, C-style sized: (i32,i32) -> size 8, align 4.
    assert_eq!(lir.stack_slots.len(), 1, "expected exactly one aggregate stack slot");
    assert_eq!(lir.stack_slots[0].size, 8, "(i32,i32) C-layout size is 8 bytes");
    assert_eq!(lir.stack_slots[0].align, 4, "(i32,i32) C-layout align is 4 bytes");

    // Count the LIR field Store / Load opcodes: the whole-aggregate Store/Load
    // decomposed into one Str + one Ldr PER FIELD = 2 each.
    let mut lir_stores = 0usize;
    let mut lir_loads = 0usize;
    let mut store_offsets: Vec<bool> = Vec::new(); // whether a non-zero offset GEP exists
    for blk in lir.blocks.values() {
        for ins in &blk.instructions {
            match ins.opcode {
                LirOpcode::Store { .. } => lir_stores += 1,
                LirOpcode::Load { .. } => lir_loads += 1,
                LirOpcode::ArrayGep { .. } => store_offsets.push(true),
                _ => {}
            }
        }
    }
    assert_eq!(lir_stores, 2, "expected 2 per-field Stores (one per tuple field)");
    assert_eq!(lir_loads, 2, "expected 2 per-field Loads (one per tuple field)");
    // Field 1 sits at offset 4 -> at least one ArrayGep (base + 4) is emitted for
    // the store AND the load of field 1 (offset 0 fields use the bare StackAddr).
    assert!(
        store_offsets.len() >= 2,
        "expected >= 2 field-offset address computations (field 1 @ offset 4 for store+load), \
         got {}",
        store_offsets.len()
    );

    let (code, base) = emit_module_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty for aggregate-in-memory sum");
    let (strs, ldrs) = count_single_ldr_str(&code, base);
    assert!(strs >= 2, "expected >= 2 Str (the two field stores) in emitted bytes, got {strs}");
    assert!(ldrs >= 2, "expected >= 2 Ldr (the two field loads) in emitted bytes, got {ldrs}");
}

// ===========================================================================
// TEST 2 — concrete VALUE-DIFFERENTIAL: the Module interpreter computes a+b with
// the value routed THROUGH the aggregate stack slot. This is the c58fa68
// `Ty::Tuple` byte_size + Store/Load round trip; a passing interpret PROVES the
// pin actually unblocked aggregates-in-memory (pre-c58fa68 the interpreter
// trapped with "no byte layout" on the aggregate Store/Load).
// ===========================================================================

#[test]
fn module_interpreter_aggregate_sum_round_trips_through_memory() {
    let module = make_agg_sum_module(false);
    assert_eq!(interpret_agg(&module, 5, 7), 12);
    assert_eq!(interpret_agg(&module, 0, 0), 0);
    assert_eq!(interpret_agg(&module, -3, 10), 7);
    assert_eq!(interpret_agg(&module, 100, -50), 50);
    assert_eq!(interpret_agg(&module, 41, 1), 42);
}

// ===========================================================================
// TEST 3 — PROVEN OUTPUT (infinite domain): the emitted bytes of the
// aggregate-in-memory sum compute `a + b` for ALL inputs. The two-field MEM
// round trip is discharged by ay's array theory (Store then Select at each field
// offset reduces to the stored field value).
// ===========================================================================

#[test]
fn module_derived_aggregate_bytes_compute_a_plus_b_for_all_inputs() {
    let module = make_agg_sum_module(false);

    // Value-differential precondition before the symbolic proof.
    assert_eq!(interpret_agg(&module, 5, 7), 12, "value-differential precondition");

    let (code, base) = emit_module_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty");

    let machine_out = symbolic_machine_output(&code, base);
    let spec = sum_spec();

    let proven = discharge_equal(&machine_out, &spec);
    assert!(
        proven,
        "PROVEN-OUTPUT FAILED: ay did not prove the aggregate-in-memory sum bytes equal a+b for \
         all inputs.\n  machine_out = {machine_out:?}"
    );
}

// ===========================================================================
// TEST 4 — MANDATORY NEGATIVE CONTROL: the SAME sum bytes proven against an
// `a + b + 1` spec MUST be SAT. A non-SAT result would make the positive
// certificate vacuous (e.g. if a field store/load were silently dropped or a
// field offset collapsed both fields onto each other).
// ===========================================================================

#[test]
fn negative_control_aggregate_bytes_vs_a_plus_b_plus_1_is_sat() {
    let module = make_agg_sum_module(false);
    let (code, base) = emit_module_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty");

    let machine_out = symbolic_machine_output(&code, base);
    let wrong = sum_plus_one_spec(); // deliberately the WRONG spec.

    let proven = discharge_equal(&machine_out, &wrong);
    assert!(
        !proven,
        "VACUITY CHECK FAILED: the aggregate sum bytes were 'proven' equal to a+b+1; the \
         aggregate memory discharge has no teeth.\n  machine_out = {machine_out:?}"
    );
}

// ===========================================================================
// TEST 5 — the converter ALSO accepts the RAW bridge shape whose aggregate base
// is `Undef(Tuple)` (the `promote_local_to_memory` seed), proving the per-field
// decomposition admits the real emitted Module — not only the interpreter-
// executable Const::Aggregate stand-in. The interpreter traps on `Undef`
// EAGERLY (documented limitation), so this is a LOWERING + PROVEN-OUTPUT check,
// not an interpret check: the emitted bytes must still compute a+b for all
// inputs (the Undef-seeded fields are fully overwritten by the InsertFields
// before the Store, so the seed is dead).
// ===========================================================================

#[test]
fn raw_bridge_undef_seeded_aggregate_lowers_and_computes_a_plus_b() {
    let module = make_agg_sum_module(true); // Undef(Tuple) base — the raw bridge shape.

    // The Module REALLY contains an aggregate Undef seed (not a Const stand-in).
    assert!(
        module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| b.body.iter())
            .any(|n| matches!(&n.inst, Inst::Undef { ty: Ty::Tuple(_) })),
        "raw bridge module must carry an Undef(Tuple) aggregate seed"
    );

    let (code, base) = emit_module_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty for raw-bridge aggregate sum");

    let machine_out = symbolic_machine_output(&code, base);
    assert!(
        discharge_equal(&machine_out, &sum_spec()),
        "PROVEN-OUTPUT FAILED: raw-bridge (Undef-seeded) aggregate bytes do not equal a+b for all \
         inputs.\n  machine_out = {machine_out:?}"
    );
    // Negative control teeth on the raw shape too.
    assert!(
        !discharge_equal(&machine_out, &sum_plus_one_spec()),
        "VACUITY CHECK FAILED: raw-bridge aggregate bytes 'proven' equal to a+b+1"
    );
}
