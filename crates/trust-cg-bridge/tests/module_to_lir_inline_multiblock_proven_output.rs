// module_to_lir_inline_multiblock_proven_output.rs — the "trust-ir first"
// codegen seam, extended to CALLS of a LOCAL pure leaf function whose body spans
// MORE THAN ONE basic block, via Module-level MULTI-BLOCK INLINING, proven over
// the REAL emitted bytes.
//
// GOAL: take a `trust_ir::Module` built by the REAL bridge from two
// VerifiableFunctions
//
//     fn add(a: i32, b: i32) -> i32 { a + b }   // FuncId 1, MULTI-BLOCK callee:
//                                               //   bb0: overflow + tuple + assert -> Br bb1
//                                               //   bb1: extractfield + return
//     fn cab(a: i32, b: i32) -> i32 { add(a, b) } // FuncId 0, the caller
//
// and lower `cab` to trust-cg LIR via `lower_trust_ir_function_to_lir`. The
// converter runs the Module-level INLINING PRE-PASS first: the `Inst::Call` to
// the local pure leaf `add` does NOT match the single-block inliner (add is a
// post-mono CHECKED-ARITH body of TWO blocks: `Inst::Overflow` + a tuple build +
// an overflow `Assert` -> a trap branch, then a value-extract return). The new
// MULTI-BLOCK inliner splices the callee's BLOCKS into the caller: the caller
// block is split at the call, the callee's blocks are cloned with FRESH BlockIds
// + ValueIds, params bound to args, and each callee `Return(v)` becomes a
// `Br -> cont, args=[v]` into a fresh continuation block whose single param is
// the call result. The existing scalar / checked-tuple / Assert-split / CFG
// machinery then lowers the result with ZERO proof-executor changes.
//
// We prove, over the no-overflow path, the emitted machine bytes compute
// `a + b` for ALL inputs:
//
//   (1) NO-Bl / NO-Call: the emitted __text must contain NO `Bl`/`Blr` (AArch64
//       call) — proof the multi-block callee was INLINED, not emitted as a call;
//   (2) PROVEN-OUTPUT (infinite domain): the emitted bytes are decoded into
//       machine effects (NOT reconstructed from the IR), path-merged (the
//       overflow trap arm is discarded, its negation conjoined into the
//       no-overflow PRECONDITION) into a symbolic output Formula; ay (QF_BV)
//       proves `precondition => (Formula == a + b)` for ALL inputs (UNSAT of the
//       negation); and
//   (3) NEGATIVE CONTROL: the SAME emitted bytes proven against an `a + b + 1`
//       spec (under the same precondition) MUST be SAT — otherwise the discharge
//       is vacuous (e.g. if the inlined add were silently dropped); and
//   (4) NON-TRIVIAL PRECONDITION: a vacuously-`true` precondition would mean the
//       overflow trap was never explored (the inlined check was dropped).
//
// The machine output is BYTE-DERIVED (emit -> decode -> effects), NEVER
// reconstructed from the IR; a wrong multi-block clone/redirect (wrong arg
// binding, dropped block, wrong return routing, stale BlockId/ValueId) makes ay
// return a COUNTEREXAMPLE rather than silently passing — demonstrated by the
// mandatory SAT negative control.
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

use trust_ir::Module;

// ---------------------------------------------------------------------------
// Source the REAL bridge Module from two trust-types VerifiableFunctions:
//   * add(a,b) = a + b — the canonical rustc `a + b` shape (a
//     `Rvalue::CheckedBinaryOp(Add, a, b)` into a `(i32, bool)` tuple, an
//     `Overflow(Add)` assert on `.1`, then `return _.0`) — a MULTI-BLOCK
//     checked-arith body once lowered through `lower_to_trust_ir_functions`;
//   * cab(a,b) = add(a, b) — a single `Terminator::Call` to `add` then return.
// The cab `Call` is the MULTI-BLOCK inline target.
// ---------------------------------------------------------------------------

fn make_bridge_cab_module() -> Module {
    use trust_types::{
        AssertMessage, BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan,
        Statement, Terminator, Ty as TtTy, VerifiableBody, VerifiableFunction,
    };

    // add(a, b) -> i32 { a + b }  (lowers to a 2-block checked-arith body).
    let add = VerifiableFunction {
        name: "add".to_string(),
        def_path: "m::add".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: TtTy::i32(), name: None },
                LocalDecl { index: 1, ty: TtTy::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: TtTy::i32(), name: Some("b".into()) },
                LocalDecl {
                    index: 3,
                    ty: TtTy::Tuple(vec![TtTy::i32(), TtTy::Bool]),
                    name: Some("checked".into()),
                },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(1),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: TtTy::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    // cab(a, b) -> i32 { add(a, b) }
    let cab = VerifiableFunction {
        name: "cab".to_string(),
        def_path: "m::cab".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: TtTy::i32(), name: None },
                LocalDecl { index: 1, ty: TtTy::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: TtTy::i32(), name: Some("b".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "add".to_string(),
                        args: vec![
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        unwind: trust_types::UnwindEdge::Unreachable,
                        is_unsafe_sig: false, is_foreign: false,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: TtTy::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    // cab MUST be functions[0] (the emitter lowers functions[0]); add is the
    // callee inlined into cab.
    trust_ir_bridge::lower_to_trust_ir_functions("m", &[cab, add])
        .expect("bridge lower_to_trust_ir_functions failed for cab/add")
}

// ---------------------------------------------------------------------------
// Emit the Module-derived LIR (after MULTI-BLOCK inlining) to an object and
// extract __text.
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

fn emit_cab_text(module: &Module) -> (Vec<u8>, u64) {
    emit_fn_text(module, 0)
}

/// Emit the LIR for `module.functions[idx]` (after the inlining pre-pass) and
/// return its __text. `idx == 0` is cab; `idx == 1` is the standalone callee
/// `add` (the inlining baseline).
fn emit_fn_text(module: &Module, idx: usize) -> (Vec<u8>, u64) {
    let f = &module.functions[idx];
    let lir = lower_trust_ir_function_to_lir(module, f)
        .expect("lower_trust_ir_function_to_lir failed");
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

/// Decode every 4-byte word in __text and count `Bl`/`Blr` (AArch64 call)
/// opcodes. An INLINED call emits NONE; a real (un-inlined) call edge emits one.
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

/// Does the emitted __text carry a conditional branch? The inlined overflow
/// assert MUST lower to one — a dropped check would leave only straight-line.
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

// ===========================================================================
// BOUNDED SYMBOLIC PATH-MERGING EXECUTOR (mirrors the checked-tuple harness):
// explores both targets at a ConditionalBranch; an arm that diverges into the
// `abort` trap (a Call effect) is the overflow/panic path — discarded, and the
// live arm's path condition is conjoined into the no-overflow PRECONDITION.
// ===========================================================================

const MAX_STEPS: u32 = 4096;
const MAX_DEPTH: u32 = 16;

#[derive(Debug, Clone, PartialEq, Eq)]
enum ExecError {
    Loop { at: u64 },
    BudgetExceeded,
    Trapped,
    Unsupported(String),
    Decode(String),
}

struct Executor<'a> {
    sem: Aarch64Semantics,
    code: &'a [u8],
    base: u64,
    steps: u32,
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

    fn merge(
        &mut self,
        path_cond: Formula,
        taken: Result<Formula, ExecError>,
        fall: Result<Formula, ExecError>,
    ) -> Result<Formula, ExecError> {
        match (taken, fall) {
            (Ok(t), Ok(f)) => Ok(Formula::Ite(Box::new(path_cond), Box::new(t), Box::new(f))),
            (Err(ExecError::Trapped), Ok(f)) => {
                self.precondition.push(Formula::Not(Box::new(path_cond)));
                Ok(f)
            }
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
/// UNSAT of `precondition AND machine_out != ir_out` == proven-equal.
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

/// cab(a,b) = add(a,b) = a + b.
fn add_spec() -> Formula {
    Formula::BvAdd(Box::new(wn(0)), Box::new(wn(1)), 32)
}

/// The WRONG spec a + b + 1, for the mandatory vacuity (negative) control.
fn add_plus_one_spec() -> Formula {
    Formula::BvAdd(Box::new(add_spec()), Box::new(bv32(1)), 32)
}

// ---------------------------------------------------------------------------
// CONCRETE byte oracle. The trust-ir reference interpreter cannot run the
// bridge's aggregate-undef tuple idiom (it reads the `(i32, bool)` Undef seed
// eagerly), so — as in the checked-tuple proven-output test — the value oracle
// is the EMITTED BYTES executed CONCRETELY by `trust_machine_sem`, the same
// machine semantics the symbolic proof uses but with constant arguments.
// ---------------------------------------------------------------------------

enum ConcreteOutcome {
    Trapped,
    Value(Formula),
}

fn concrete_run(code: &[u8], base: u64, a: i32, b: i32) -> ConcreteOutcome {
    let mut state = MachineState::symbolic();
    state.gpr[0] = Formula::BitVec { value: i128::from(a) & 0xffff_ffff, width: 64 };
    state.gpr[1] = Formula::BitVec { value: i128::from(b) & 0xffff_ffff, width: 64 };
    let mut exec = Executor::new(code, base);
    match exec.run(base, state, Vec::new(), 0) {
        Ok(out) => ConcreteOutcome::Value(out),
        Err(ExecError::Trapped) => ConcreteOutcome::Trapped,
        Err(e) => panic!("concrete run failed: {e:?}"),
    }
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

fn bytes_cab_equals(code: &[u8], base: u64, a: i32, b: i32, expected: i32) -> bool {
    match concrete_run(code, base, a, b) {
        ConcreteOutcome::Value(out) => concrete_equals(&out, expected),
        ConcreteOutcome::Trapped => false,
    }
}

// ===========================================================================
// TEST 0 — the MULTI-BLOCK callee was INLINED: the lowered LIR carries NO Call
// opcode, materializes NO tuple-in-memory (zero stack slots), and the inlined
// overflow check survives as a CheckedSadd + Brif + Trap + Icmp.
// ===========================================================================

#[test]
fn cab_multiblock_inlines_with_no_call_and_no_memory() {
    use trust_cg_lower::instructions::Opcode as LO;
    let module = make_bridge_cab_module();
    let lir = lower_trust_ir_function_to_lir(&module, &module.functions[0])
        .expect("multi-block-inlined cab lowers");

    // No LIR call opcode survives the inline.
    for block in lir.blocks.values() {
        for inst in &block.instructions {
            assert!(
                !matches!(inst.opcode, LO::Call { .. } | LO::CallIndirect),
                "a LIR call opcode survived multi-block inlining: {:?}",
                inst.opcode
            );
        }
    }

    // No tuple materialized in memory (the checked-arith tuple is decomposed).
    assert!(
        lir.stack_slots.is_empty(),
        "multi-block inline must materialize NO memory; got {} stack slots",
        lir.stack_slots.len()
    );

    // The inlined overflow check survives: CheckedSadd + Brif + Trap + Icmp.
    let mut checked = 0;
    let mut brif = 0;
    let mut trap = 0;
    let mut icmp = 0;
    for block in lir.blocks.values() {
        for inst in &block.instructions {
            match inst.opcode {
                LO::CheckedSadd => checked += 1,
                LO::Brif { .. } => brif += 1,
                LO::Trap => trap += 1,
                LO::Icmp { .. } => icmp += 1,
                _ => {}
            }
        }
    }
    assert_eq!(checked, 1, "one CheckedSadd from the inlined Overflow");
    assert_eq!(brif, 1, "one Brif (inlined overflow assert)");
    assert_eq!(trap, 1, "one Trap (shared trap block)");
    assert_eq!(icmp, 1, "one Icmp (ok = flag == false)");
}

// ===========================================================================
// TEST 1 — the inlined cab introduces NO call edge: its emitted __text has the
// SAME `Bl`/`Blr` count as the STANDALONE callee `add` (both carry exactly the
// one trap `Bl` to the abort runtime — the lowered overflow check — and NOTHING
// ELSE). A residual call to `add` would show as an EXTRA `Bl`. The inlined cab
// also carries a conditional branch (the inlined overflow check was lowered).
//
// NOTE: a checked-arith body's overflow `Assert` lowers to a `Trap` = a `Bl` to
// the abort runtime (a `Call` effect). So "the call was inlined" is NOT "zero
// `Bl`" — it is "no MORE `Bl` than the divergence the body itself contains",
// proven by the standalone-add baseline. The structural proof that NO call
// survived is TEST 0 (no LIR `Call` opcode); the path-merge proof (TEST 3)
// further shows the single `Bl` is the TRAP (it classifies as `Trapped`, i.e.
// a divergence, leaving a live no-overflow arm — a real call to `add` would
// trap EVERY path and the proof would have no live arm).
// ===========================================================================

#[test]
fn cab_introduces_no_call_edge_over_baseline_and_has_conditional_branch() {
    let module = make_bridge_cab_module();
    let (cab_code, cab_base) = emit_cab_text(&module);
    assert!(!cab_code.is_empty(), "emitted __text is empty for inlined cab");

    // Baseline: the standalone callee `add` (same checked-arith body, NOT
    // inlined into anything). Its only `Bl` is the trap.
    let (add_code, add_base) = emit_fn_text(&module, 1);
    let add_bls = count_bl(&add_code, add_base);
    assert_eq!(add_bls, 1, "standalone add carries exactly one trap Bl (the overflow abort)");

    let cab_bls = count_bl(&cab_code, cab_base);
    assert_eq!(
        cab_bls, add_bls,
        "inlined cab introduced a call edge: cab has {cab_bls} Bl vs the add baseline's {add_bls} \
         (an inlined call must add NO Bl beyond the body's own trap divergence)"
    );

    assert!(
        has_conditional_branch(&cab_code, cab_base),
        "expected a conditional branch in the emitted bytes (inlined overflow check lowered)"
    );
}

// ===========================================================================
// TEST 2 — concrete value-differential: the EMITTED BYTES compute cab(a,b)=a+b
// on no-overflow inputs (the byte oracle).
// ===========================================================================

#[test]
fn cab_emitted_bytes_are_correct() {
    let module = make_bridge_cab_module();
    let (code, base) = emit_cab_text(&module);
    assert!(bytes_cab_equals(&code, base, 2, 3, 5), "cab(2,3) == 5");
    assert!(bytes_cab_equals(&code, base, -1, 1, 0), "cab(-1,1) == 0");
    assert!(bytes_cab_equals(&code, base, 0, 0, 0), "cab(0,0) == 0");
    assert!(bytes_cab_equals(&code, base, 40, 2, 42), "cab(40,2) == 42");
    assert!(bytes_cab_equals(&code, base, -5, -7, -12), "cab(-5,-7) == -12 (no overflow)");
}

// ===========================================================================
// TEST 3 — PROVEN OUTPUT (infinite domain): on the no-overflow path the emitted
// bytes of the MULTI-BLOCK-inlined cab compute `a + b` for ALL inputs (UNSAT of
// the negation), under a NON-TRIVIAL no-overflow precondition.
// ===========================================================================

#[test]
fn cab_multiblock_inlined_bytes_compute_a_plus_b_on_no_overflow_path() {
    let module = make_bridge_cab_module();

    let (code, base) = emit_cab_text(&module);
    // Concrete byte-level value-differential precondition.
    assert!(bytes_cab_equals(&code, base, 2, 3, 5), "value-differential precondition");
    assert!(!code.is_empty(), "emitted __text is empty");
    // The multi-block call was inlined: cab introduces no `Bl` beyond the body's
    // own trap divergence (same count as the standalone-add baseline).
    let (add_code, add_base) = emit_fn_text(&module, 1);
    assert_eq!(
        count_bl(&code, base),
        count_bl(&add_code, add_base),
        "the multi-block call must be inlined (no extra Bl over the add baseline)"
    );

    let (machine_out, precondition) = symbolic_machine_output(&code, base)
        .expect("path-merge of the inlined cab bytes failed (loop/unsupported/budget)");

    // A vacuously-true precondition would mean the inlined overflow trap was
    // never explored (the check was dropped). Assert it is non-trivial.
    assert!(
        !matches!(precondition, Formula::Bool(true)),
        "expected a non-trivial no-overflow precondition; got `true` (overflow trap not explored)"
    );

    let spec = add_spec();
    let proven = discharge_equal_under(&precondition, &machine_out, &spec);
    assert!(
        proven,
        "PROVEN-OUTPUT FAILED: ay did not prove the multi-block-inlined cab bytes equal a+b on \
         the no-overflow path for all inputs.\n  machine_out = {machine_out:?}\n  pre = {precondition:?}"
    );
}

// ===========================================================================
// TEST 4 — MANDATORY NEGATIVE CONTROL: the SAME cab bytes proven against an
// `a + b + 1` spec (under the same precondition) MUST be SAT — a non-SAT result
// would make the positive certificate vacuous (e.g. if the inlined add body
// were silently dropped or the return mis-routed).
// ===========================================================================

#[test]
fn negative_control_cab_vs_a_plus_b_plus_1_is_sat() {
    let module = make_bridge_cab_module();
    let (code, base) = emit_cab_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty");

    let (machine_out, precondition) = symbolic_machine_output(&code, base)
        .expect("path-merge of the inlined cab bytes failed");

    let wrong = add_plus_one_spec();
    let proven = discharge_equal_under(&precondition, &machine_out, &wrong);
    assert!(
        !proven,
        "VACUITY CHECK FAILED: the multi-block-inlined cab bytes were 'proven' equal to a+b+1; \
         the inline discharge has no teeth.\n  machine_out = {machine_out:?}"
    );
}
