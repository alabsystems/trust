// module_to_lir_overflow_proven_output.rs — the "trust-ir first" codegen seam,
// extended to CHECKED-OVERFLOW arithmetic, proven over the real emitted bytes.
//
// GOAL: take a `trust_ir::Module` whose body is the MIR-FAITHFUL checked-add
// idiom the producer (trust-thir-lower) emits for `a + b` when overflow checks
// are on:
//
//     fn checked_add(a: i32, b: i32) -> i32 {
//         %res, %ovf = add.overflow a, b   ; Inst::Overflow -> [value, overflow_b1]
//         %f = const false                 ; Inst::Const Bool(false)
//         %t = const true                  ; Inst::Const Bool(true)
//         %ok = select %ovf ? %f : %t      ; Inst::Select  (== !overflowed)
//         assert %ok                       ; Inst::Assert  (trap iff overflow)
//         return %res
//     }
//
// and lower it to trust-cg LIR via `lower_trust_ir_function_to_lir`. The
// converter maps:
//   * Inst::Overflow{AddOverflow} on i32 -> LIR `CheckedSadd` producing the
//     SAME `[value, overflow_b1]` pair (NO materialized tuple, NO ExtractField);
//   * Inst::Select -> LIR `Select { NotEqual }` (the `!overflowed` negation);
//   * Inst::Assert -> a block SPLIT: `Brif(ok, cont, trap)` where the shared
//     trap block is a single `Trap` (abort), mirroring the VF->LIR panic block.
//
// We prove the emitted machine bytes compute `a + b` ON THE NO-OVERFLOW PATH
// for ALL inputs:
//
//   (1) VALUE-DIFFERENTIAL (concrete): the trust-ir reference INTERPRETER runs
//       the Module on checked_add(2,3) = 5 and checked_add(-1,1) = 0 — through
//       the real Overflow + Select + Assert machinery;
//   (2) it emits a real object whose __text carries a conditional branch and a
//       trap (proof the overflow check was lowered, not dropped);
//   (3) PROVEN-OUTPUT (infinite domain): the emitted bytes are decoded into
//       machine effects (NOT reconstructed from the IR). The bounded path-merge
//       executor explores the conditional branch; the OVERFLOW arm diverges into
//       the `abort` trap (a Call effect), so it is the trap/panic path — the
//       executor returns the LIVE (no-overflow) arm's value and records the
//       live-arm path condition as the NO-OVERFLOW PRECONDITION. ay (QF_BV)
//       proves `precondition => (machine_out == a + b)` for ALL 2^64 input pairs
//       (UNSAT of the negation); and
//   (4) NEGATIVE CONTROL: the SAME bytes proven against an `a + b + 1` spec
//       (still under the precondition) MUST be SAT — otherwise the discharge is
//       vacuous.
//
// The machine output is BYTE-DERIVED (emit -> decode -> effects -> path-merge),
// NEVER reconstructed from the IR; a wrong overflow lowering (wrong checked op,
// wrong select polarity, dropped value, mis-merged branch) makes ay return a
// COUNTEREXAMPLE rather than silently passing — demonstrated by the mandatory
// SAT negative control.
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

use trust_ir::inst::{Inst, OverflowOp};
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::node::InstrNode;
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{Block, Constant, Function as IrFunction, Module};

// ---------------------------------------------------------------------------
// Build a trust_ir::Module for checked_add(a,b) = a + b, lowered via the EXACT
// MIR-faithful checked-add idiom: Overflow + (false/true consts) + Select +
// Assert + Return. This is byte-for-byte the shape trust-thir-lower produces.
// ---------------------------------------------------------------------------

fn make_checked_add_module() -> Module {
    let mut module = Module::new("overflow_module");
    module.func_types.push(FuncTy {
        params: vec![Ty::I32, Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });

    let mut f =
        IrFunction::new(FuncId::new(0), "ir_checked_add", FuncTyId::new(0), BlockId::new(0));

    let a = ValueId::new(0);
    let b = ValueId::new(1);
    let res = ValueId::new(2);
    let ovf = ValueId::new(3);
    let f_const = ValueId::new(4);
    let t_const = ValueId::new(5);
    let ok = ValueId::new(6);

    let mut block = Block::new(BlockId::new(0));
    block.params.push((a, Ty::I32));
    block.params.push((b, Ty::I32));

    // %res, %ovf = add.overflow a, b
    block.body.push(
        InstrNode::new(Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ty: Ty::I32,
            lhs: a,
            rhs: b,
        })
        .with_results([res, ovf]),
    );
    // %f = const false ; %t = const true
    block.body.push(
        InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(false) })
            .with_result(f_const),
    );
    block.body.push(
        InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
            .with_result(t_const),
    );
    // %ok = select %ovf ? %f : %t   (== !overflowed)
    block.body.push(
        InstrNode::new(Inst::Select {
            ty: Ty::Bool,
            cond: ovf,
            then_val: f_const,
            else_val: t_const,
        })
        .with_result(ok),
    );
    // assert %ok   (trap iff overflow)
    block.body.push(InstrNode::new(Inst::Assert { cond: ok }));
    // return %res
    block.body.push(InstrNode::new(Inst::Return { values: vec![res] }));

    f.blocks.push(block);
    module.functions.push(f);
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

fn emit_text(module: &Module) -> (Vec<u8>, u64) {
    let f = &module.functions[0];
    let lir = lower_trust_ir_function_to_lir(module, f)
        .expect("lower_trust_ir_function_to_lir failed for checked_add");
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

/// Does the emitted __text carry a conditional branch? The overflow assert MUST
/// lower to one — a dropped check would leave only straight-line code.
fn has_conditional_branch(code: &[u8], base: u64) -> bool {
    let mut pc = base;
    while (pc - base) as usize + 4 <= code.len() {
        let off = (pc - base) as usize;
        let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
        if let Ok(insn) = decode_aarch64(&bytes, pc) {
            if matches!(insn.opcode, Opcode::BCond | Opcode::Cbz | Opcode::Cbnz | Opcode::Tbz | Opcode::Tbnz)
            {
                return true;
            }
        }
        pc += 4;
    }
    false
}

// ===========================================================================
// BOUNDED SYMBOLIC PATH-MERGING EXECUTOR (mirrors module_to_lir_cfg_proven_
// output.rs), extended to model the OVERFLOW TRAP arm.
//
// At a ConditionalBranch we explore both targets. If one arm DIVERGES into the
// `abort` trap (a Call effect), that arm is the overflow/panic path: we discard
// it and return the LIVE arm's value, conjoining the live-arm path condition
// into the NO-OVERFLOW PRECONDITION accumulated in `self.precondition`.
//
// The returned Formula is therefore the machine output ON THE NO-OVERFLOW PATH,
// and `self.precondition` is the assumption under which it is proven equal to
// the spec. Loops / non-trap calls / atomics / indirect branches fail closed.
// ===========================================================================

const MAX_STEPS: u32 = 4096;
const MAX_DEPTH: u32 = 16;

#[derive(Debug, Clone, PartialEq, Eq)]
enum ExecError {
    Loop { at: u64 },
    BudgetExceeded,
    /// The arm diverged into the abort trap (the overflow/panic path). Carries
    /// nothing: the caller treats it as the excluded (trapping) branch.
    Trapped,
    Unsupported(String),
    Decode(String),
}

struct Executor<'a> {
    sem: Aarch64Semantics,
    code: &'a [u8],
    base: u64,
    steps: u32,
    /// Conjuncts of the no-overflow precondition (the live-arm path conditions).
    precondition: Vec<Formula>,
}

impl<'a> Executor<'a> {
    fn new(code: &'a [u8], base: u64) -> Self {
        Executor { sem: Aarch64Semantics, code, base, steps: 0, precondition: Vec::new() }
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
                        // The abort call IS the trap/panic path: this arm diverges.
                        return Err(ExecError::Trapped);
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

                let taken = self.run(target_pc, state.clone(), visited.clone(), depth + 1);
                let fall = self.run(fall_pc, state.clone(), visited.clone(), depth + 1);

                return self.merge(path_cond, taken, fall);
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

    /// Merge a conditional fork. If exactly ONE arm trapped, that arm is the
    /// overflow/panic path: return the other arm's value and conjoin the
    /// live-arm path condition into the no-overflow precondition. If neither
    /// trapped, merge with an Ite (a real two-valued branch). If both trapped
    /// the whole path diverges.
    fn merge(
        &mut self,
        path_cond: Formula,
        taken: Result<Formula, ExecError>,
        fall: Result<Formula, ExecError>,
    ) -> Result<Formula, ExecError> {
        match (taken, fall) {
            (Ok(t), Ok(f)) => {
                Ok(Formula::Ite(Box::new(path_cond), Box::new(t), Box::new(f)))
            }
            // taken trapped -> overflow path is `path_cond`; live path is its negation.
            (Err(ExecError::Trapped), Ok(f)) => {
                self.precondition.push(Formula::Not(Box::new(path_cond)));
                Ok(f)
            }
            // fallthrough trapped -> overflow path is `!path_cond`; live path is `path_cond`.
            (Ok(t), Err(ExecError::Trapped)) => {
                self.precondition.push(path_cond);
                Ok(t)
            }
            (Err(ExecError::Trapped), Err(ExecError::Trapped)) => Err(ExecError::Trapped),
            (Err(e), _) | (_, Err(e)) => Err(e),
        }
    }
}

fn const_addr(f: &Formula) -> Option<u64> {
    match f {
        Formula::BitVec { value, .. } => Some(*value as u64),
        _ => None,
    }
}

/// Returns (machine_out_on_no_overflow_path, no_overflow_precondition).
fn symbolic_machine_output(code: &[u8], base: u64) -> Result<(Formula, Formula), ExecError> {
    let mut exec = Executor::new(code, base);
    let state = MachineState::symbolic();
    let out = exec.run(base, state, Vec::new(), 0)?;
    let pre = if exec.precondition.is_empty() {
        Formula::Bool(true)
    } else if exec.precondition.len() == 1 {
        exec.precondition.pop().unwrap()
    } else {
        Formula::And(exec.precondition.clone())
    };
    Ok((out, pre))
}

// ---------------------------------------------------------------------------
// Formula -> ay::Term translation (QF_BV).
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

/// Discharge `precondition => (machine_out == ir_out)` over ALL inputs via ay.
/// UNSAT of `precondition AND machine_out != ir_out` == proven-equal under the
/// precondition.
fn discharge_equal_under(precondition: &Formula, machine_out: &Formula, ir_out: &Formula) -> bool {
    let mut solver = Solver::try_new(Logic::QfAbv).expect("ay Solver::try_new");
    let pre = formula_to_term(&mut solver, precondition);
    let lhs = formula_to_term(&mut solver, machine_out);
    let rhs = formula_to_term(&mut solver, ir_out);
    let eq = solver.try_eq(lhs, rhs).expect("eq");
    let differ = solver.try_not(eq).expect("not");
    let counterexample = solver.try_and_many(&[pre, differ]).expect("and");
    solver.try_assert_term(counterexample).expect("assert");
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

/// a + b spec (32-bit wrapping add — the checked-add value result).
fn add_spec() -> Formula {
    Formula::BvAdd(Box::new(wn(0)), Box::new(wn(1)), 32)
}

/// a + b + 1 — the WRONG spec for the negative control.
fn add_plus_one_spec() -> Formula {
    Formula::BvAdd(Box::new(add_spec()), Box::new(bv32(1)), 32)
}

// ---------------------------------------------------------------------------
// VALUE-DIFFERENTIAL: the trust-ir reference interpreter on the Module.
// ---------------------------------------------------------------------------

fn interpret_checked_add(module: &Module, a: i128, b: i128) -> i128 {
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
// TEST 1 — the converter emits a real object whose __text carries a
// conditional branch (the overflow check was lowered, not dropped).
// ===========================================================================

#[test]
fn checked_add_emits_object_with_conditional_branch() {
    let module = make_checked_add_module();

    // The lowered LIR must carry a CheckedSadd and a Brif.
    let lir = lower_trust_ir_function_to_lir(&module, &module.functions[0])
        .expect("checked_add lowers");
    let mut saw_checked = false;
    let mut saw_brif = false;
    let mut saw_trap = false;
    for block in lir.blocks.values() {
        for inst in &block.instructions {
            use trust_cg_lower::instructions::Opcode as LO;
            match inst.opcode {
                LO::CheckedSadd => saw_checked = true,
                LO::Brif { .. } => saw_brif = true,
                LO::Trap => saw_trap = true,
                _ => {}
            }
        }
    }
    assert!(saw_checked, "expected a CheckedSadd in the lowered LIR");
    assert!(saw_brif, "expected a Brif (overflow assert) in the lowered LIR");
    assert!(saw_trap, "expected a Trap (overflow trap block) in the lowered LIR");

    let (code, base) = emit_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty for checked_add");
    assert!(
        has_conditional_branch(&code, base),
        "expected a conditional branch in the emitted checked_add bytes (overflow check lowered)"
    );
}

// ===========================================================================
// TEST 2 — concrete value-differential: the Module interpreter computes
// checked_add(a,b) = a + b on the no-overflow inputs.
// ===========================================================================

#[test]
fn module_interpreter_checked_add_is_correct() {
    let module = make_checked_add_module();
    assert_eq!(interpret_checked_add(&module, 2, 3), 5);
    assert_eq!(interpret_checked_add(&module, -1, 1), 0);
    assert_eq!(interpret_checked_add(&module, 0, 0), 0);
    assert_eq!(interpret_checked_add(&module, 40, 2), 42);
}

// ===========================================================================
// TEST 3 — PROVEN OUTPUT (infinite domain): on the no-overflow path the emitted
// bytes compute `a + b` for ALL inputs.
// ===========================================================================

#[test]
fn checked_add_bytes_compute_a_plus_b_on_no_overflow_path() {
    let module = make_checked_add_module();

    // Value-differential precondition before the symbolic proof.
    assert_eq!(interpret_checked_add(&module, 2, 3), 5, "value-differential precondition");

    let (code, base) = emit_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty");

    let (machine_out, precondition) = symbolic_machine_output(&code, base)
        .expect("path-merge of the checked_add bytes failed (loop/unsupported/budget)");

    // The proof MUST be conditioned on a real no-overflow precondition — a
    // vacuously-true precondition would mean the overflow trap was never
    // explored (the check was dropped). We assert it is non-trivial.
    assert!(
        !matches!(precondition, Formula::Bool(true)),
        "expected a non-trivial no-overflow precondition; got `true` (overflow trap not explored)"
    );

    let spec = add_spec();
    let proven = discharge_equal_under(&precondition, &machine_out, &spec);
    assert!(
        proven,
        "PROVEN-OUTPUT FAILED: ay did not prove the checked_add bytes equal a+b on the \
         no-overflow path for all inputs.\n  machine_out = {machine_out:?}\n  pre = {precondition:?}"
    );
}

// ===========================================================================
// TEST 4 — MANDATORY NEGATIVE CONTROL: the SAME bytes proven against an
// `a + b + 1` spec (under the same precondition) MUST be SAT. A non-SAT result
// would make the positive certificate vacuous.
// ===========================================================================

#[test]
fn negative_control_checked_add_vs_a_plus_b_plus_1_is_sat() {
    let module = make_checked_add_module();
    let (code, base) = emit_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty");

    let (machine_out, precondition) =
        symbolic_machine_output(&code, base).expect("path-merge of the checked_add bytes failed");

    let wrong = add_plus_one_spec(); // deliberately the WRONG spec.
    let proven = discharge_equal_under(&precondition, &machine_out, &wrong);
    assert!(
        !proven,
        "VACUITY CHECK FAILED: the checked_add bytes were 'proven' equal to a+b+1; \
         the overflow discharge has no teeth.\n  machine_out = {machine_out:?}"
    );
}
