// module_to_lir_cfg_proven_output.rs — the "trust-ir first" codegen seam,
// extended to CONTROL FLOW (multi-block + block-param merges), proven over the
// real emitted bytes.
//
// GOAL: take a `trust_ir::Module` for
//
//     fn max(a: i32, b: i32) -> i32 { if a > b { a } else { b } }
//
// represented as a MULTI-BLOCK SSA function with a block-param merge at the
// join, lower it to trust-cg LIR via the EXTENDED `lower_module_to_lir`
// converter (CondBr -> Brif, Br -> Jump, block-param args -> Copy + native LIR
// block params), feed that LIR into the EXISTING verified
// `TrustCgCodegenBackend::emit_object` emitter, and prove the emitted machine
// bytes compute max(a,b) for ALL inputs three ways:
//
//   (1) VALUE-DIFFERENTIAL (concrete): the trust-ir reference INTERPRETER
//       executes the Module on max(3,2)=3 and max(2,3)=3;
//   (2) PROVEN-OUTPUT (infinite domain): the emitted bytes are decoded into
//       machine effects (NOT reconstructed from the IR) and path-merged into a
//       symbolic output Formula; ay proves that Formula equals signed-max(a,b)
//       for ALL 2^64 inputs (UNSAT of the negation); and
//   (3) NEGATIVE CONTROL: the SAME emitted bytes proven against a MIN spec MUST
//       be SAT — otherwise the discharge is vacuous.
//
// SIGNEDNESS NOTE (load-bearing, identical to proven_output_condbr.rs): the i32
// `a > b` comparison lowers to a signed condition code; the byte-derived
// path-merge reduces to SIGNED max == (b <=s a) ? a : b. The MIN spec
// (a <=s b) ? a : b is the negative control — exactly the property that
// distinguishes the two, so a mis-merged Ite makes even the positive spec FAIL.
//
// The machine output is BYTE-DERIVED (emit -> decode -> effects -> path-merge),
// NEVER reconstructed from the IR; a wrong control-flow lowering (wrong branch,
// wrong block-arg Copy) makes ay return a COUNTEREXAMPLE rather than silently
// passing — demonstrated by the mandatory SAT negative control.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![cfg(feature = "ay-proofs")]

use ay::{BigInt, Logic, Solver, Term};
use trust_cg_bridge::codegen_backend::{TrustCgCodegenBackend, TrustCgTargetArch};
use trust_cg_bridge::lower_trust_ir_function_to_lir;
use trust_disasm::{Opcode, decode_aarch64};
use trust_machine_sem::{
    Aarch64Semantics, Effect, MachineState, Semantics, condition_to_formula,
};
use trust_types::{Formula, Sort};

use trust_ir::inst::{ICmpOp, Inst};
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::node::InstrNode;
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{Block, Function as IrFunction, Module};

// ---------------------------------------------------------------------------
// Build a trust_ir::Module for `max`/`min`-shaped multi-block functions.
//
//   bb0(a, b):  %cmp = icmp <op> a, b ; condbr %cmp -> bb1 else bb2
//   bb1:        br bb3(a)
//   bb2:        br bb3(b)
//   bb3(m):     return m
//
// The MERGE is the block-param `m` of bb3, fed by the per-edge args `a`/`b` on
// the two `br bb3(..)` terminators. This exercises:
//   * CondBr -> Brif (the cmp result drives the conditional branch),
//   * Br -> Jump with a block-arg (the Copy into bb3's param Value), and
//   * a native LIR block param at the join.
// ---------------------------------------------------------------------------

fn make_select_module(name: &str, op: ICmpOp) -> Module {
    let mut module = Module::new("cfg_module");
    module.func_types.push(FuncTy {
        params: vec![Ty::I32, Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let func_ty_id = FuncTyId::new(0);
    let mut function = IrFunction::new(FuncId::new(0), name, func_ty_id, BlockId::new(0));

    let a = ValueId::new(0);
    let b = ValueId::new(1);
    let cmp = ValueId::new(2);
    let m = ValueId::new(3);

    // bb0: cmp + condbr.
    let mut bb0 = Block::new(BlockId::new(0));
    bb0.params.push((a, Ty::I32));
    bb0.params.push((b, Ty::I32));
    bb0.body
        .push(InstrNode::new(Inst::ICmp { op, ty: Ty::I32, lhs: a, rhs: b }).with_result(cmp));
    bb0.body.push(InstrNode::new(Inst::CondBr {
        cond: cmp,
        then_target: BlockId::new(1),
        then_args: vec![],
        else_target: BlockId::new(2),
        else_args: vec![],
    }));

    // bb1: br bb3(a).
    let mut bb1 = Block::new(BlockId::new(1));
    bb1.body.push(InstrNode::new(Inst::Br { target: BlockId::new(3), args: vec![a] }));

    // bb2: br bb3(b).
    let mut bb2 = Block::new(BlockId::new(2));
    bb2.body.push(InstrNode::new(Inst::Br { target: BlockId::new(3), args: vec![b] }));

    // bb3(m): return m.
    let mut bb3 = Block::new(BlockId::new(3));
    bb3.params.push((m, Ty::I32));
    bb3.body.push(InstrNode::new(Inst::Return { values: vec![m] }));

    function.blocks.push(bb0);
    function.blocks.push(bb1);
    function.blocks.push(bb2);
    function.blocks.push(bb3);
    module.functions.push(function);
    module
}

/// max(a,b) = if a > b { a } else { b }.
fn make_max_module() -> Module {
    make_select_module("ir_max", ICmpOp::Sgt)
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
        .expect("lower_module_to_lir failed for multi-block select");
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

// ===========================================================================
// BOUNDED SYMBOLIC PATH-MERGING EXECUTOR (mirrors proven_output_condbr.rs).
//
// Decode the EMITTED BYTES. Execute straight-line effects through a symbolic
// MachineState until a RET (returns W0) or a ConditionalBranch (FORK). At a
// ConditionalBranch: path_cond = condition_to_formula(state, condition) over the
// CURRENT (post-Subs) flags; recurse on the taken-target state and the
// fallthrough state; MERGE as Ite(path_cond, taken, fallthrough). Loops / calls /
// atomics / indirect branches fail closed (the function is SKIPPED, never faked).
// ===========================================================================

const MAX_STEPS: u32 = 4096;
const MAX_DEPTH: u32 = 16;

#[derive(Debug, Clone, PartialEq, Eq)]
enum ExecError {
    Loop { at: u64 },
    BudgetExceeded,
    Unsupported(String),
    Decode(String),
}

struct Executor<'a> {
    sem: Aarch64Semantics,
    code: &'a [u8],
    base: u64,
    steps: u32,
}

impl<'a> Executor<'a> {
    fn new(code: &'a [u8], base: u64) -> Self {
        Executor { sem: Aarch64Semantics, code, base, steps: 0 }
    }

    fn decode_at(&self, pc: u64) -> Result<trust_disasm::Instruction, ExecError> {
        let off = pc
            .checked_sub(self.base)
            .ok_or_else(|| ExecError::Decode(format!("pc {pc:#x} below base")))?
            as usize;
        if off + 4 > self.code.len() {
            return Err(ExecError::Decode(format!("pc {pc:#x} past __text end")));
        }
        let bytes: [u8; 4] = self.code[off..off + 4].try_into().unwrap();
        decode_aarch64(&bytes, pc).map_err(|e| ExecError::Decode(format!("{e:?} at {pc:#x}")))
    }

    fn run(
        &mut self,
        mut pc: u64,
        mut state: MachineState,
        mut visited: Vec<u64>,
        depth: u32,
    ) -> Result<Formula, ExecError> {
        if depth > MAX_DEPTH {
            return Err(ExecError::BudgetExceeded);
        }
        loop {
            if visited.contains(&pc) {
                return Err(ExecError::Loop { at: pc });
            }
            visited.push(pc);

            self.steps += 1;
            if self.steps > MAX_STEPS {
                return Err(ExecError::BudgetExceeded);
            }

            let insn = self.decode_at(pc)?;
            let opcode = insn.opcode;

            let effects = self
                .sem
                .effects(&state, &insn)
                .map_err(|e| ExecError::Decode(format!("effects {opcode:?} at {pc:#x}: {e:?}")))?;

            if opcode == Opcode::Ret {
                return Ok(state.read_gpr(0, 32));
            }

            let mut cond_branch: Option<(_, Formula, Formula)> = None;
            let mut uncond_target: Option<Formula> = None;
            let mut plain: Vec<&Effect> = Vec::new();
            for e in &effects {
                match e {
                    Effect::ConditionalBranch { condition, target, fallthrough } => {
                        cond_branch = Some((*condition, target.clone(), fallthrough.clone()));
                    }
                    Effect::Branch { target } => uncond_target = Some(target.clone()),
                    Effect::PcUpdate { .. } => {}
                    Effect::Call { .. } => {
                        return Err(ExecError::Unsupported(format!("Call at {pc:#x}")));
                    }
                    Effect::Aarch64SyncBoundary { .. } | Effect::Aarch64AtomicAccess { .. } => {
                        return Err(ExecError::Unsupported(format!("atomic/sync at {pc:#x}")));
                    }
                    other => plain.push(other),
                }
            }

            for e in &plain {
                state
                    .apply_effect(e)
                    .map_err(|er| ExecError::Decode(format!("apply {e:?} at {pc:#x}: {er:?}")))?;
            }

            if let Some((condition, target, _fallthrough)) = cond_branch {
                let path_cond = condition_to_formula(&state, condition);
                let target_pc = const_addr(&target)
                    .ok_or_else(|| ExecError::Unsupported(format!("indirect bcond at {pc:#x}")))?;
                let fall_pc = pc + 4;
                if visited.contains(&target_pc) || visited.contains(&fall_pc) {
                    return Err(ExecError::Loop { at: pc });
                }
                let taken = self.run(target_pc, state.clone(), visited.clone(), depth + 1)?;
                let fall = self.run(fall_pc, state.clone(), visited.clone(), depth + 1)?;
                return Ok(Formula::Ite(Box::new(path_cond), Box::new(taken), Box::new(fall)));
            }

            if let Some(target) = uncond_target {
                let target_pc = const_addr(&target)
                    .ok_or_else(|| ExecError::Unsupported(format!("indirect b at {pc:#x}")))?;
                if visited.contains(&target_pc) {
                    return Err(ExecError::Loop { at: target_pc });
                }
                pc = target_pc;
                continue;
            }

            pc += 4;
        }
    }
}

fn const_addr(f: &Formula) -> Option<u64> {
    match f {
        Formula::BitVec { value, .. } => Some(*value as u64),
        _ => None,
    }
}

fn symbolic_machine_output(code: &[u8], base: u64) -> Result<Formula, ExecError> {
    let mut exec = Executor::new(code, base);
    let state = MachineState::symbolic();
    exec.run(base, state, Vec::new(), 0)
}

// ---------------------------------------------------------------------------
// Formula -> ay::Term translation.
// ---------------------------------------------------------------------------

fn var_term(solver: &mut Solver, name: &str, sort: &Sort) -> Term {
    match sort {
        Sort::BitVec(w) => solver.bv_var(name, *w),
        Sort::Bool => solver.bool_var(name),
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

/// signed-max(a,b) == (b <=s a) ? a : b.
fn signed_max_spec() -> Formula {
    Formula::Ite(
        Box::new(Formula::BvSLe(Box::new(wn(1)), Box::new(wn(0)), 32)),
        Box::new(wn(0)),
        Box::new(wn(1)),
    )
}

/// signed-min(a,b) == (a <=s b) ? a : b. The MIN spec is the negative control
/// for the MAX bytes (they differ whenever a != b).
fn signed_min_spec() -> Formula {
    Formula::Ite(
        Box::new(Formula::BvSLe(Box::new(wn(0)), Box::new(wn(1)), 32)),
        Box::new(wn(0)),
        Box::new(wn(1)),
    )
}

// ---------------------------------------------------------------------------
// VALUE-DIFFERENTIAL: the trust-ir reference interpreter on the Module.
// ---------------------------------------------------------------------------

fn interpret_select(module: &Module, a: i128, b: i128) -> i128 {
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
// TEST 1 — the converter produces well-formed multi-block LIR that emits a
// non-empty object with real branches.
// ===========================================================================

#[test]
fn module_to_lir_emits_object_for_multiblock_max() {
    let module = make_max_module();
    let (code, base) = emit_module_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty for Module-derived max");
    assert!(base == base);
    // The emitted text MUST contain at least one conditional branch — otherwise
    // the control-flow lowering collapsed to straight-line and the proof would
    // not exercise the merge.
    let mut saw_bcond = false;
    let mut pc = base;
    while (pc - base) as usize + 4 <= code.len() {
        let off = (pc - base) as usize;
        let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
        if let Ok(insn) = decode_aarch64(&bytes, pc) {
            if matches!(insn.opcode, Opcode::BCond) {
                saw_bcond = true;
                break;
            }
        }
        pc += 4;
    }
    assert!(saw_bcond, "expected a conditional branch in the emitted max() bytes");
}

// ===========================================================================
// TEST 2 — concrete value-differential: the Module interpreter computes max.
// ===========================================================================

#[test]
fn module_interpreter_max_is_correct() {
    let module = make_max_module();
    assert_eq!(interpret_select(&module, 3, 2), 3);
    assert_eq!(interpret_select(&module, 2, 3), 3);
    assert_eq!(interpret_select(&module, -5, -1), -1);
    assert_eq!(interpret_select(&module, 7, 7), 7);
}

// ===========================================================================
// TEST 3 — PROVEN OUTPUT (infinite domain): the emitted bytes of the
// Module-derived multi-block max() compute signed-max(a,b) for ALL inputs.
// ===========================================================================

#[test]
fn module_derived_max_bytes_compute_signed_max_for_all_inputs() {
    let module = make_max_module();

    // Value-differential precondition before the symbolic proof.
    assert_eq!(interpret_select(&module, 3, 2), 3, "value-differential precondition");
    assert_eq!(interpret_select(&module, 2, 3), 3, "value-differential precondition");

    let (code, base) = emit_module_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty");

    let machine_out = symbolic_machine_output(&code, base)
        .expect("path-merge of the max() bytes failed (loop/unsupported/budget)");
    let spec = signed_max_spec();

    let proven = discharge_equal(&machine_out, &spec);
    assert!(
        proven,
        "PROVEN-OUTPUT FAILED: ay did not prove the Module-derived multi-block max() bytes \
         equal signed-max(a,b) for all inputs.\n  machine_out = {machine_out:?}"
    );
}

// ===========================================================================
// TEST 4 — MANDATORY NEGATIVE CONTROL: the SAME max() bytes proven against the
// MIN spec MUST be SAT. A non-SAT result would make the positive certificate
// vacuous.
// ===========================================================================

#[test]
fn negative_control_max_bytes_vs_min_spec_is_sat() {
    let module = make_max_module();
    let (code, base) = emit_module_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty");

    let machine_out = symbolic_machine_output(&code, base)
        .expect("path-merge of the max() bytes failed");
    let wrong = signed_min_spec(); // deliberately the WRONG spec for max.

    let proven = discharge_equal(&machine_out, &wrong);
    assert!(
        !proven,
        "VACUITY CHECK FAILED: the max() bytes were 'proven' equal to signed-min; \
         the control-flow discharge has no teeth.\n  machine_out = {machine_out:?}"
    );
}
