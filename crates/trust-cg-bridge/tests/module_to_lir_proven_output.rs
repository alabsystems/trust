// module_to_lir_proven_output.rs — the "trust-ir first" codegen seam, end-to-end.
//
// GOAL: take a `trust_ir::Module` for `add(a: i32, b: i32) -> i32 { a + b }`,
// lower it to trust-cg LIR via the NEW `lower_module_to_lir` converter, feed
// that LIR into the EXISTING verified `TrustCgCodegenBackend::emit_object`
// emitter, and prove the emitted machine bytes are correct two ways:
//
//   (1) VALUE-DIFFERENTIAL (concrete): the trust-ir reference INTERPRETER
//       (`trust_ir::interpret::Interpreter`) executes the Module on add(2,3)=5;
//       and
//   (2) PROVEN-OUTPUT (infinite domain): the emitted bytes are decoded into
//       machine effects (NOT reconstructed from the IR) and ay proves the
//       resulting output Formula equals `a + b` for ALL 2^64 inputs.
//
// This is route (a)+(c) from the Step-1 plan, applied to a Module-SOURCED LIR
// rather than the VF->LIR path. The machine output comes from the ACTUAL
// emitted bytes of the Module-derived LIR, so the proof distinguishes correct
// from incorrect codegen — demonstrated by the mandatory negative control
// (`sub` Module proven against the `a+b` spec MUST be SAT).
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
// Build a trust_ir::Module for a 2-arg integer binop function.
//
// Convention matches the VF->Module adapter (trust-ir-bridge/src/lower.rs):
// argument value ids are ValueId(0)..ValueId(arg_count-1), so the entry block
// carries NO params; the body references the args by those ids directly.
// ---------------------------------------------------------------------------

fn make_binop_module(name: &str, op: BinOp) -> Module {
    let mut module = Module::new("test_module");

    // fn(i32, i32) -> i32
    let func_ty = FuncTy {
        params: vec![Ty::I32, Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    };
    module.func_types.push(func_ty);
    let func_ty_id = FuncTyId::new(0);

    let func_id = FuncId::new(0);
    let entry = BlockId::new(0);
    let mut function = IrFunction::new(func_id, name, func_ty_id, entry);

    // %0 = arg a (i32), %1 = arg b (i32) — carried as entry-block params
    // (the canonical well-formed shape the trust-ir reference interpreter
    // expects). %2 = op %0, %1; return %2.
    let arg_a = ValueId::new(0);
    let arg_b = ValueId::new(1);
    let sum = ValueId::new(2);

    let mut block = Block::new(entry);
    block.params.push((arg_a, Ty::I32));
    block.params.push((arg_b, Ty::I32));
    block.body.push(
        InstrNode::new(Inst::BinOp {
            op,
            ty: Ty::I32,
            lhs: arg_a,
            rhs: arg_b,
        })
        .with_result(sum),
    );
    block.body.push(InstrNode::new(Inst::Return { values: vec![sum] }));

    function.blocks.push(block);
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
        .expect("lower_module_to_lir failed for scalar add");
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

// ---------------------------------------------------------------------------
// Symbolic execution of the EMITTED BYTES (the established bridge pattern).
// ---------------------------------------------------------------------------

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
            panic!("apply_effects rejected emitted insn {:?} at {pc:#x}: {e:?}", insn.opcode)
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
// Formula -> ay::Term translation (only the shapes a scalar add/sub produce).
// ---------------------------------------------------------------------------

fn sort_width(sort: &Sort) -> u32 {
    match sort {
        Sort::BitVec(w) => *w,
        other => panic!("unexpected non-bitvector Var sort: {other:?}"),
    }
}

fn formula_to_term(solver: &mut Solver, f: &Formula) -> Term {
    match f {
        Formula::Var(name, sort) => solver.bv_var(name, sort_width(sort)),
        Formula::BitVec { value, width } => solver
            .try_bv_const_bigint(&BigInt::from(*value), *width)
            .expect("bv const"),
        Formula::BvAdd(a, b, _) => {
            let a = formula_to_term(solver, a);
            let b = formula_to_term(solver, b);
            solver.try_bvadd(a, b).expect("bvadd")
        }
        Formula::BvSub(a, b, _) => {
            let a = formula_to_term(solver, a);
            let b = formula_to_term(solver, b);
            solver.try_bvsub(a, b).expect("bvsub")
        }
        Formula::BvMul(a, b, _) => {
            let a = formula_to_term(solver, a);
            let b = formula_to_term(solver, b);
            solver.try_bvmul(a, b).expect("bvmul")
        }
        Formula::BvAnd(a, b, _) => {
            let a = formula_to_term(solver, a);
            let b = formula_to_term(solver, b);
            solver.try_bvand(a, b).expect("bvand")
        }
        Formula::BvOr(a, b, _) => {
            let a = formula_to_term(solver, a);
            let b = formula_to_term(solver, b);
            solver.try_bvor(a, b).expect("bvor")
        }
        Formula::BvNot(a, _) => {
            let a = formula_to_term(solver, a);
            solver.try_bvnot(a).expect("bvnot")
        }
        Formula::BvConcat(a, b) => {
            let a = formula_to_term(solver, a);
            let b = formula_to_term(solver, b);
            solver.try_bvconcat(a, b).expect("bvconcat")
        }
        Formula::BvZeroExt(a, bits) => {
            let a = formula_to_term(solver, a);
            solver.try_bvzeroext(a, *bits).expect("bvzeroext")
        }
        Formula::BvExtract { inner, high, low } => {
            let inner = formula_to_term(solver, inner);
            solver.try_bvextract(inner, *high, *low).expect("bvextract")
        }
        Formula::Eq(a, b) => {
            let a = formula_to_term(solver, a);
            let b = formula_to_term(solver, b);
            solver.try_eq(a, b).expect("eq")
        }
        Formula::Not(a) => {
            let a = formula_to_term(solver, a);
            solver.try_not(a).expect("not")
        }
        other => panic!("formula_to_term: unhandled Formula variant: {other:?}"),
    }
}

fn discharge_equal(machine_out: &Formula, ir_out: &Formula) -> bool {
    let mut solver = Solver::try_new(Logic::QfBv).expect("ay Solver::try_new");
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

/// The intended i32 spec: W0 + W1 (low 32 bits of the two argument registers).
fn ir_add_output() -> Formula {
    let w0 = Formula::BvExtract {
        inner: Box::new(Formula::Var("X0".into(), Sort::BitVec(64))),
        high: 31,
        low: 0,
    };
    let w1 = Formula::BvExtract {
        inner: Box::new(Formula::Var("X1".into(), Sort::BitVec(64))),
        high: 31,
        low: 0,
    };
    Formula::BvAdd(Box::new(w0), Box::new(w1), 32)
}

// ---------------------------------------------------------------------------
// (1) VALUE-DIFFERENTIAL: the trust-ir reference interpreter on the Module.
// ---------------------------------------------------------------------------

fn interpret_add(module: &Module, a: i128, b: i128) -> i128 {
    let interp = Interpreter::with_module(module);
    let args = vec![
        InterpretValue::int(Ty::I32, a).expect("arg a"),
        InterpretValue::int(Ty::I32, b).expect("arg b"),
    ];
    let outcome = interp
        .execute_func(FuncId::new(0), args)
        .expect("interpreter execute_func failed");
    outcome.returns[0]
        .as_int()
        .expect("integer return")
        .as_signed()
}

// ---------------------------------------------------------------------------
// TEST 1 — the converter produces well-formed LIR that emits a non-empty object.
// ---------------------------------------------------------------------------

#[test]
fn module_to_lir_emits_object_for_scalar_add() {
    let module = make_binop_module("ir_add", BinOp::Add);
    let (code, base) = emit_module_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty for Module-derived add");
    assert!(base == base);
}

// ---------------------------------------------------------------------------
// TEST 2 — concrete value-differential: Module interpreter says add(2,3) = 5.
// (Cross-checks that the Module we lowered is the add Module the proof is over.)
// ---------------------------------------------------------------------------

#[test]
fn module_interpreter_add_2_3_is_5() {
    let module = make_binop_module("ir_add", BinOp::Add);
    assert_eq!(interpret_add(&module, 2, 3), 5);
    assert_eq!(interpret_add(&module, -1, 1), 0);
    assert_eq!(interpret_add(&module, 100, 23), 123);
}

// ---------------------------------------------------------------------------
// TEST 3 — PROVEN OUTPUT (infinite domain): the emitted bytes of the
// Module-derived LIR compute a+b for ALL inputs (ay UNSAT of the negation).
// ---------------------------------------------------------------------------

#[test]
fn module_derived_add_bytes_compute_sum_for_all_inputs() {
    let module = make_binop_module("ir_add", BinOp::Add);

    // Cross-check the concrete interpreter agrees before the symbolic proof.
    assert_eq!(interpret_add(&module, 2, 3), 5, "value-differential precondition");

    let (code, base) = emit_module_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty");

    let machine_out = symbolic_machine_output(&code, base);
    let ir_out = ir_add_output();

    let proven = discharge_equal(&machine_out, &ir_out);
    assert!(
        proven,
        "PROVEN-OUTPUT FAILED: ay did not prove the Module-derived add() bytes equal \
         (a+b) for all inputs.\n  machine_out = {machine_out:?}"
    );
}

// ---------------------------------------------------------------------------
// TEST 4 — MANDATORY NEGATIVE CONTROL: a `sub` Module proven against the `a+b`
// spec MUST be SAT (counterexample). If this were UNSAT the discharge would be
// vacuous and the positive certificate meaningless.
// ---------------------------------------------------------------------------

#[test]
fn negative_control_module_sub_is_sat() {
    let module = make_binop_module("ir_sub", BinOp::Sub);
    let (code, base) = emit_module_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty");

    let machine_out = symbolic_machine_output(&code, base);
    let ir_out = ir_add_output(); // deliberately the WRONG spec for sub.

    let proven = discharge_equal(&machine_out, &ir_out);
    assert!(
        !proven,
        "VACUITY CHECK FAILED: emitted sub() bytes were 'proven' equal to (a+b); \
         the discharge has no teeth.\n  machine_out = {machine_out:?}"
    );
}
