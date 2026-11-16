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
//     trap block is a single `Trap`, mirroring the VF->LIR panic block. Since
//     trust-cg b80b958f5 a LIR `Trap` selects to AArch64 `BRK #1` (as LLVM
//     does for llvm.trap), not a `call abort`.
//
// We prove the emitted machine bytes compute `a + b` ON THE NO-OVERFLOW PATH
// for ALL inputs:
//
//   (1) VALUE-DIFFERENTIAL (concrete): the trust-ir reference INTERPRETER runs
//       the Module on checked_add(2,3) = 5 and checked_add(-1,1) = 0 — through
//       the real Overflow + Select + Assert machinery;
//   (2) it emits a real object whose __text carries a conditional branch and a
//       trap (proof the overflow check was lowered, not dropped);
//   (3) PROVEN-OUTPUT (full symbolic input domain): the emitted bytes are
//       decoded into machine effects (NOT reconstructed from the IR). The
//       no-overflow PRECONDITION is an independent source-level signed-add
//       domain bound to the original argument registers, NOT read off emitted
//       control flow. At each conditional branch the executor omits an arm
//       only when ay proves its accumulated path condition UNSAT under that
//       domain; it never decodes an omitted arm, so the overflow `BRK` is
//       avoided only by proving it unreachable. ay (QF_BV) then proves
//       `precondition => (machine_out == a + b)` for ALL 2^64 input pairs
//       (UNSAT of the negation); and
//   (4) NEGATIVE CONTROL: the SAME bytes proven against an `a + b + 1` spec
//       (still under the precondition) MUST be SAT — otherwise the discharge is
//       vacuous; and
//   (5) REFUSAL AND DOMAIN CONTROLS: a FEASIBLE overflow (concrete or over the
//       unconstrained symbolic domain) still reaches the unchanged `BRK`
//       Semantics refusal; an arbitrary call is not a trap; the source domain
//       has exact signed boundaries; and an inverted overflow branch cannot
//       silently shrink the admitted input domain.
//
// These are bounded development solver checks, not kernel certificates.
//
// The machine output is BYTE-DERIVED (emit -> decode -> effects -> path-merge),
// NEVER reconstructed from the IR; a wrong overflow lowering (wrong checked op,
// wrong select polarity, dropped value, mis-merged branch) makes ay return a
// COUNTEREXAMPLE rather than silently passing — demonstrated by the mandatory
// SAT negative control.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// Trust (2026-09-30, plan §5 fail-open item 1): every shipping `module_to_lir`
// entry point now refuses an `Assert`-bearing body as
// `ModuleLirError::ImplicitPanicUnfaithful` — the `Brif`/`Trap` lowering this
// file proves is a bare `brk`, not Rust's panic. The proofs stay under test
// for plan §5 item P through the trap oracle, which exists only under the
// non-default `test-hooks` feature (never enabled by the compiler); this file
// moved from the `ay-proofs` lane to `test-hooks` with it (`test-hooks`
// implies `ay-proofs`).
#![cfg(feature = "test-hooks")]

use std::time::Duration;

use ay::{BigInt, Logic, Solver, SolverConfig, Term};
use trust_cg_bridge::codegen_backend::{TrustCgCodegenBackend, TrustCgTargetArch};
use trust_cg_bridge::module_to_lir::lower_trust_ir_function_to_lir_trap_assert_oracle;

/// The trap oracle under the name this file always used (see the note at the
/// top): `Assert` lowers to `Brif`/`Trap` here and is refused everywhere else.
fn lower_trust_ir_function_to_lir(
    module: &trust_ir::Module,
    function: &trust_ir::Function,
) -> Result<trust_cg_lower::function::Function, trust_cg_bridge::ModuleLirError> {
    lower_trust_ir_function_to_lir_trap_assert_oracle(module, function, false)
}
use trust_disasm::{Opcode, decode_aarch64};
use trust_ir::inst::{Inst, OverflowOp};
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::node::InstrNode;
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{Block, Constant, Function as IrFunction, Module};
use trust_machine_sem::{Aarch64Semantics, Effect, MachineState, Semantics, condition_to_formula};
use trust_types::{Formula, Sort};

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
        abi: None,
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
        InstrNode::new(Inst::Overflow { op: OverflowOp::AddOverflow, ty: Ty::I32, lhs: a, rhs: b })
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
    block.body.push(InstrNode::new(Inst::Assert {
        cond: ok,
        kind: trust_ir::AssertKind::Unspecified,
        site: None,
    }));
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
            if matches!(
                insn.opcode,
                Opcode::BCond | Opcode::Cbz | Opcode::Cbnz | Opcode::Tbz | Opcode::Tbnz
            ) {
                return true;
            }
        }
        pc += 4;
    }
    false
}

/// Decode all emitted words. Unknown words or a truncated instruction refuse
/// the structural check rather than being omitted from the call/trap counts.
fn count_opcode(code: &[u8], base: u64, wanted: &[Opcode]) -> usize {
    assert_eq!(code.len() % 4, 0, "AArch64 text must contain complete instructions");
    code.chunks_exact(4)
        .enumerate()
        .filter(|(index, bytes)| {
            let bytes: [u8; 4] = (*bytes).try_into().unwrap();
            let insn = decode_aarch64(&bytes, base + (*index * 4) as u64)
                .expect("every emitted word must decode for structural accounting");
            wanted.contains(&insn.opcode)
        })
        .count()
}

// ===========================================================================
// BOUNDED SYMBOLIC RETURN-PATH EXECUTOR (ported from
// module_to_lir_inline_multiblock_proven_output.rs, 7a1034b5c1).
//
// The arithmetic input assumption is supplied independently of emitted control
// flow and threaded as the path condition. At a ConditionalBranch an arm is
// omitted only when AY establishes that its accumulated path condition is
// UNSAT; an omitted arm is never decoded. Reachable BRK, calls, and unknown
// feasibility remain refusals; no trap semantics is invented. (This replaces
// the retired design in which the `call abort` trap arm surfaced as a Call
// effect, was classified `Trapped`, and its negation became the precondition:
// since trust-cg b80b958f5 the trap is `BRK #1`, which the machine semantics
// refuses fail-closed, and a Call is not evidence of divergence.)
//
// The returned Formula is the machine output on every feasible path under the
// precondition. Loops / calls / atomics / indirect branches fail closed.
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
        path_condition: Formula,
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
                        // A call is not evidence that this arm diverges: refuse.
                        return Err(ExecError::Unsupported(format!("call at {pc:#x}")));
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
                // A condition the machine model does not evaluate must REFUSE
                // this replay, not become an `always taken` path condition.
                let path_cond = condition_to_formula(&state, condition)
                    .map_err(|er| ExecError::Unsupported(format!("condition at {pc:#x}: {er}")))?;
                let target_pc = const_addr(&target)
                    .ok_or_else(|| ExecError::Unsupported(format!("indirect bcond at {pc:#x}")))?;
                let fall_pc = pc + 4;
                if visited.contains(&target_pc) || visited.contains(&fall_pc) {
                    return Err(ExecError::Loop { at: pc });
                }

                let taken_path = Formula::And(vec![path_condition.clone(), path_cond.clone()]);
                let fall_path = Formula::And(vec![
                    path_condition.clone(),
                    Formula::Not(Box::new(path_cond.clone())),
                ]);
                // Do not even decode an infeasible destination. In particular,
                // a BRK may only be avoided by proving its path impossible;
                // a feasible BRK still reaches the unchanged Semantics refusal.
                return match (path_is_feasible(&taken_path)?, path_is_feasible(&fall_path)?) {
                    (true, true) => {
                        let taken = self.run(
                            target_pc,
                            state.clone(),
                            visited.clone(),
                            depth + 1,
                            taken_path,
                        )?;
                        let fall = self.run(fall_pc, state, visited, depth + 1, fall_path)?;
                        Ok(Formula::Ite(Box::new(path_cond), Box::new(taken), Box::new(fall)))
                    }
                    (true, false) => self.run(target_pc, state, visited, depth + 1, taken_path),
                    (false, true) => self.run(fall_pc, state, visited, depth + 1, fall_path),
                    (false, false) => Err(ExecError::Unsupported("no feasible return path".into())),
                };
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

/// Unknown (including the finite solver deadline) is never an infeasibility
/// certificate. This is a test oracle, not a kernel-certified proof artifact.
fn path_is_feasible(path: &Formula) -> Result<bool, ExecError> {
    let config = SolverConfig::default().with_timeout(Duration::from_secs(30));
    let mut solver = Solver::try_new_with_config(Logic::QfAbv, config)
        .map_err(|e| ExecError::Unsupported(format!("feasibility solver: {e:?}")))?;
    let condition = formula_to_term(&mut solver, path);
    solver
        .try_assert_term(condition)
        .map_err(|e| ExecError::Unsupported(format!("feasibility assertion: {e:?}")))?;
    let result = solver.check_sat();
    if result.is_unsat() {
        Ok(false)
    } else if result.is_sat() {
        Ok(true)
    } else {
        Err(ExecError::Unsupported(format!("unknown branch feasibility: {result:?}")))
    }
}

fn const_addr(f: &Formula) -> Option<u64> {
    match f {
        Formula::BitVec { value, .. } => Some(*value as u64),
        _ => None,
    }
}

/// Returns (machine_out_on_no_overflow_path, no_overflow_precondition).
///
/// Bind the source precondition to the ORIGINAL argument registers before any
/// emitted instruction executes; decoded branches cannot redefine this domain.
fn symbolic_machine_output(code: &[u8], base: u64) -> Result<(Formula, Formula), ExecError> {
    let state = MachineState::symbolic();
    let pre = no_signed_i32_add_overflow(state.read_gpr(0, 32), state.read_gpr(1, 32));
    if !path_is_feasible(&pre)? {
        return Err(ExecError::Unsupported("empty input domain".into()));
    }
    let out = Executor::new(code, base).run(base, state, Vec::new(), 0, pre.clone())?;
    Ok((out, pre))
}

/// Symbolic replay over the UNCONSTRAINED input domain (path condition `true`).
/// Used only as a control: the overflow arm is then feasible, so the replay
/// must reach the BRK refusal rather than return a value.
fn unconstrained_symbolic_run(code: &[u8], base: u64) -> Result<Formula, ExecError> {
    let state = MachineState::symbolic();
    Executor::new(code, base).run(base, state, Vec::new(), 0, Formula::Bool(true))
}

/// Concrete replay: the argument registers hold constants, so every branch
/// condition is concrete and feasibility under those inputs prunes the
/// untaken side. Concrete inputs are NOT restricted to non-overflowing
/// arguments: an actual overflow must reach the unchanged BRK refusal.
fn concrete_run(code: &[u8], base: u64, a: i32, b: i32) -> Result<Formula, ExecError> {
    let mut state = MachineState::symbolic();
    state.gpr[0] = Formula::BitVec { value: i128::from(a) & 0xffff_ffff, width: 64 };
    state.gpr[1] = Formula::BitVec { value: i128::from(b) & 0xffff_ffff, width: 64 };
    Executor::new(code, base).run(base, state, Vec::new(), 0, Formula::Bool(true))
}

fn concrete_equals(out: &Formula, expected: i32) -> bool {
    let mut solver = Solver::try_new(Logic::QfAbv).expect("ay Solver::try_new");
    let lhs = formula_to_term(&mut solver, out);
    let rhs = formula_to_term(
        &mut solver,
        &Formula::BitVec { value: i128::from(expected) & 0xffff_ffff, width: 32 },
    );
    let eq = solver.try_eq(lhs, rhs).expect("eq");
    let differ = solver.try_not(eq).expect("not");
    solver.try_assert_term(differ).expect("assert");
    solver.check_sat().is_unsat()
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

/// The independent source-level domain of `checked_add`: the exact signed i32
/// addition fits iff its exact signed i64 sum lies in [i32::MIN, i32::MAX].
/// Two sign-extended i32 values cannot overflow i64.
fn no_signed_i32_add_overflow(a: Formula, b: Formula) -> Formula {
    let sum = Formula::BvAdd(
        Box::new(Formula::BvSignExt(Box::new(a), 32)),
        Box::new(Formula::BvSignExt(Box::new(b), 32)),
        64,
    );
    Formula::And(vec![
        Formula::BvSLe(
            Box::new(Formula::BitVec { value: i128::from(i32::MIN), width: 64 }),
            Box::new(sum.clone()),
            64,
        ),
        Formula::BvSLe(
            Box::new(sum),
            Box::new(Formula::BitVec { value: i128::from(i32::MAX), width: 64 }),
            64,
        ),
    ])
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
    let outcome =
        interp.execute_func(FuncId::new(0), args).expect("interpreter execute_func failed");
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
    let lir =
        lower_trust_ir_function_to_lir(&module, &module.functions[0]).expect("checked_add lowers");
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
    // The lowered `Trap` must survive into the bytes as exactly one BRK, and
    // the function must carry no call edge (the trap is no longer `call abort`).
    assert_eq!(
        count_opcode(&code, base, &[Opcode::Brk]),
        1,
        "emitted checked_add bytes must retain the overflow-trap BRK"
    );
    assert_eq!(
        count_opcode(&code, base, &[Opcode::Bl, Opcode::Blr]),
        0,
        "emitted checked_add bytes must carry no call edge"
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
// TEST 3 — PROVEN OUTPUT (full symbolic input domain): on the no-overflow path
// the emitted bytes compute `a + b` for ALL inputs.
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

    // The proof MUST be conditioned on a real no-overflow precondition. Its
    // premise changed with the retired `call abort` trap block: the
    // precondition is no longer read off the emitted trap arm, it is the
    // explicit independent source domain, so this asserts that domain is
    // present. That the overflow check was lowered (not dropped) and that the
    // trap stays reachable outside the domain is now checked directly by
    // `feasible_overflow_still_reaches_the_brk_refusal`; the domain's exact
    // boundaries and its immunity to a corrupted guard are checked below too.
    assert!(
        !matches!(precondition, Formula::Bool(true)),
        "expected the explicit independent source no-overflow domain; got `true`"
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

// ===========================================================================
// TEST 5 — REFUSAL CONTROLS: pruning may only drop a PROVABLY infeasible arm.
// A reachable BRK must still hit the exact, unchanged Semantics refusal — the
// executor never maps BRK to a trap outcome — and a call is not a trap.
// ===========================================================================

fn assert_brk_refused(result: Result<Formula, ExecError>) {
    assert!(
        matches!(result, Err(ExecError::Decode(ref message))
        if message.contains("effects Brk")
        && message.contains("aarch64-brk-debug-trap-not-proof-consumed")),
        "reachable BRK must remain the exact semantics refusal: {result:?}"
    );
}

#[test]
fn feasible_overflow_still_reaches_the_brk_refusal() {
    let (code, base) = emit_text(&make_checked_add_module());

    // Paired positives: concrete non-overflow inputs (including the exact
    // signed boundaries) prune the trap side and return the checked sum.
    for (a, b) in [(2, 3), (-1, 1), (i32::MAX, 0), (i32::MIN, 0), (i32::MAX, i32::MIN)] {
        let out = concrete_run(&code, base, a, b)
            .unwrap_or_else(|e| panic!("concrete non-overflow run {a} + {b} must return: {e:?}"));
        assert!(concrete_equals(&out, a + b), "concrete {a} + {b}: {out:?}");
    }

    // A feasible overflow, concrete or over the unconstrained symbolic domain,
    // must reach the BRK and be refused, never pruned or returned.
    assert_brk_refused(concrete_run(&code, base, i32::MAX, 1));
    assert_brk_refused(concrete_run(&code, base, i32::MIN, -1));
    assert_brk_refused(concrete_run(&code, base, i32::MIN, i32::MIN));
    assert_brk_refused(unconstrained_symbolic_run(&code, base));
    // A BRK on the entry path (no branch to prune) is refused as well.
    assert_brk_refused(concrete_run(&0xd4200020u32.to_le_bytes(), 0, 2, 3));
}

#[test]
fn arbitrary_call_is_not_treated_as_a_trap() {
    let result = concrete_run(&0x94000000u32.to_le_bytes(), 0, 2, 3);
    assert!(
        matches!(result, Err(ExecError::Unsupported(ref message))
        if message.starts_with("call at ")),
        "a call is not a proved diverging branch: {result:?}"
    );
}

// ===========================================================================
// TEST 6 — DOMAIN CONTROLS: the independent source domain has exact signed
// boundaries, and an inverted overflow branch in the bytes cannot silently
// shrink the admitted input domain (it exposes the BRK instead).
// ===========================================================================

#[test]
fn independent_no_overflow_domain_has_exact_signed_boundaries() {
    for (a, b, fits) in [
        (i32::MIN, 0, true),
        (i32::MIN, -1, false),
        (i32::MAX, 0, true),
        (i32::MAX, 1, false),
        (i32::MAX, i32::MIN, true),
        (i32::MIN, i32::MIN, false),
        (-1, 1, true),
        (-5, -7, true),
    ] {
        let predicate = no_signed_i32_add_overflow(bv32(i128::from(a)), bv32(i128::from(b)));
        assert_eq!(path_is_feasible(&predicate).unwrap(), fits, "domain for {a} + {b}");
    }
}

#[test]
fn corrupted_overflow_guard_cannot_shrink_the_input_domain() {
    let (mut code, base) = emit_text(&make_checked_add_module());
    let branches: Vec<_> = code
        .chunks_exact(4)
        .enumerate()
        .filter_map(|(index, bytes)| {
            let bytes: [u8; 4] = bytes.try_into().unwrap();
            (decode_aarch64(&bytes, base + (index * 4) as u64).unwrap().opcode == Opcode::BCond)
                .then_some(index * 4)
        })
        .collect();
    assert_eq!(branches.len(), 1, "fixture must have one actual overflow branch");
    let offset = branches[0];
    // Flip the condition's low bit: the branch polarity inverts (e.g. VS <-> VC).
    let word = u32::from_le_bytes(code[offset..offset + 4].try_into().unwrap()) ^ 1;
    code[offset..offset + 4].copy_from_slice(&word.to_le_bytes());
    assert_brk_refused(concrete_run(&code, base, 2, 3));
    assert_brk_refused(symbolic_machine_output(&code, base).map(|(out, _)| out));
}
