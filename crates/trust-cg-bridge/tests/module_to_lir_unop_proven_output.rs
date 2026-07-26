// module_to_lir_unop_proven_output.rs — the "trust-ir first" codegen seam,
// extended to INTEGER UNARY OPS (`!a` bitwise complement, `-a` negation on i32),
// proven over the REAL emitted bytes.
//
// GOAL: take a `trust_ir::Module` sourced from a REAL trust-types
// `VerifiableFunction` whose body is a bare `Rvalue::UnaryOp(Not|Neg, a)` — run
// through `trust_ir_bridge::lower_to_trust_ir`. That bridge emits a single BARE
// `Inst::UnOp { op: Not | Neg }` (confirmed by dumping the real bridge Module).
// The NEW thing is mapping it to the LIR integer-unary opcodes:
//   * `Not -> Bnot` (bitwise complement `~x`; AArch64 ISel -> MVN),
//   * `Neg -> Ineg` (WRAPPING two's-complement `0 - x`; AArch64 ISel -> NEG).
// The trust-ir semantics (`interpret::eval_int_unop`) are `!value.raw` for Not
// and `0u128.wrapping_sub(value.raw)` for Neg — WRAPPING, so at the value level
// `Neg` never traps (`i32::MIN` negates to `i32::MIN`). FAIL-CLOSED on i128
// Not/Neg (register-pair), CtPop, and all float unary ops.
//
// NEGATION-OVERFLOW GUARD. When Rust overflow checks are on, `-a` is preceded by
// an EXPLICIT `i32::MIN` guard: the producer emits
//   `_c = (a == i32::MIN); Assert { OverflowNeg } on _c`  (expected = false)
// which lowers through the SAME Const/ICmp/Assert(->Brif/Trap)/Br machinery the
// div/rem and shift guards use (the dumped Module shows exactly:
//   `%min=const MIN; %c=icmp eq a,%min; %neg=neg a; %f=const false;
//    %ok=icmp eq %c,%f; assert %ok [NoOverflow]; br bb1 ; bb1: ret %neg`).
// The guard is SEPARATE nodes surrounding the bare `UnOp { op: Neg }`; the
// converter already lowers them. We prove BOTH the guarded and the bare
// (wrapping, unguarded) Neg shapes.
//
// We prove the emitted machine bytes compute the unary op:
//   NOT  — FULLY SYMBOLIC (no guard): ay (QF_BV) proves `machine_out == ~a` for
//          ALL 2^32 values of the symbolic `a` (UNSAT of the negation). No
//          precondition — complement is total. + value-diffs (!0=-1, !5=-6).
//   NEG  — GUARDED: the trap arm (a == i32::MIN) diverges into the abort `Trap`,
//          so the executor records the no-trap precondition `a != i32::MIN` and
//          returns the live arm's value. ay proves `precondition =>
//          (machine_out == -a)` for ALL 2^32 values of `a` (UNSAT). + value-diffs
//          (neg(5)=-5, neg(-5)=5). + the guard survives (Brif+Trap in LIR, a
//          conditional branch in __text).
//        BARE (unguarded, WRAPPING): no precondition; ay proves the emitted
//          bytes compute the wrapping negation for ALL a, INCLUDING i32::MIN
//          (neg(i32::MIN) == i32::MIN — the two's-complement wrap).
//   Each op carries a MANDATORY NEGATIVE CONTROL: the SAME bytes proven against
//   `op(a) + 1` (under the same precondition) MUST be SAT, else the certificate
//   is vacuous.
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
// The kind of unary op being modeled.
// ---------------------------------------------------------------------------
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum UnKind {
    /// `!a` bitwise complement (`~a`), i32. No guard.
    Not,
    /// `-a` negation, i32, WITH the i32::MIN overflow guard (checked arith on).
    NegGuarded,
    /// `-a` negation, i32, BARE (no guard) — the wrapping negation.
    NegBare,
}

// ---------------------------------------------------------------------------
// Source the REAL bridge Module from a trust-types VerifiableFunction whose body
// is a bare `Rvalue::UnaryOp(Not|Neg, a)`, optionally preceded by the i32::MIN
// negation-overflow guard (a `Terminator::Assert { OverflowNeg }`).
// ---------------------------------------------------------------------------
fn make_bridge_unop_module(kind: UnKind) -> Module {
    use trust_types::{
        AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue,
        SourceSpan, Statement, Terminator, Ty as TtTy, UnOp, VerifiableBody, VerifiableFunction,
    };

    let i32t = TtTy::i32();
    // _0 ret (= unary result), _1 a (operand). NegGuarded adds _2 is_min:bool.
    let mut locals = vec![
        LocalDecl { index: 0, ty: i32t.clone(), name: None },
        LocalDecl { index: 1, ty: i32t.clone(), name: Some("a".into()) },
    ];

    let (mir_unop, name) = match kind {
        UnKind::Not => (UnOp::Not, "nt"),
        UnKind::NegGuarded | UnKind::NegBare => (UnOp::Neg, "ng"),
    };

    let blocks = match kind {
        // bb0: _0 = <unop> a ; Return    (bare, no guard)
        UnKind::Not | UnKind::NegBare => vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::UnaryOp(mir_unop, Operand::Copy(Place::local(1))),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        // bb0: _2 = (a == i32::MIN) ; _0 = -a ; Assert(!_2)[OverflowNeg] -> bb1
        // bb1: return _0
        //
        // The `_2` guard-flag DEFINITION (`Eq(a, i32::MIN)`) makes the assert's
        // condition a defined SSA value; `expected: false` means "trap iff _2",
        // so the no-trap precondition the byte executor records is `!(a == MIN)`
        // == `a != i32::MIN` — exactly the precondition under which `-a` does not
        // overflow.
        UnKind::NegGuarded => {
            locals.push(LocalDecl { index: 2, ty: TtTy::Bool, name: Some("is_min".into()) });
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Eq,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Int(i32::MIN as i128)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(1))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(2)),
                        expected: false,
                        msg: AssertMessage::OverflowNeg,
                        target: BlockId(1),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ]
        }
    };

    let vf = VerifiableFunction {
        name: name.to_string(),
        def_path: "unop::op".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody { locals, blocks, arg_count: 1, return_ty: i32t },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    trust_ir_bridge::lower_to_trust_ir(&vf).expect("bridge lower_to_trust_ir failed for unop")
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
        .expect("lower_trust_ir_function_to_lir failed for unop");
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

/// Does the emitted __text carry a conditional branch? The guarded-Neg case MUST
/// lower one — a dropped guard would leave only straight-line code, meaning the
/// emitted negate would wrap (return i32::MIN) where the source would panic.
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
// BOUNDED SYMBOLIC PATH-MERGING EXECUTOR (mirrors the shift/div-rem tests): the
// trapping guard arm (a `Trap`/abort call) diverges that arm, accumulating the
// no-trap precondition. For the unguarded shapes (Not, NegBare) there is no
// branch, so the precondition is trivially `true` (fully symbolic).
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
                    // The Assert trap block begins with `call abort`: the abort
                    // call IS the trap/panic path, so this arm diverges — the
                    // no-trap precondition excludes it.
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

/// Path-merge with X0 (== `a`, the unary operand) FULLY SYMBOLIC. For the
/// unguarded shapes the precondition is `true`; for the guarded Neg the trap arm
/// diverges and the executor records `a != i32::MIN`.
fn symbolic_machine_output(code: &[u8], base: u64) -> Result<(Formula, Formula), ExecError> {
    let state = MachineState::symbolic();
    run_machine_output(code, base, state)
}

fn run_machine_output(
    code: &[u8],
    base: u64,
    state: MachineState,
) -> Result<(Formula, Formula), ExecError> {
    let mut exec = Executor::new(code, base);
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
        Formula::BvUDiv(a, b, _) => bin2(solver, a, b, Solver::try_bvudiv),
        Formula::BvSDiv(a, b, _) => bin2(solver, a, b, Solver::try_bvsdiv),
        Formula::BvURem(a, b, _) => bin2(solver, a, b, Solver::try_bvurem),
        Formula::BvSRem(a, b, _) => bin2(solver, a, b, Solver::try_bvsrem),
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
    let mut solver = Solver::try_new(Logic::QfBv).expect("ay Solver::try_new");
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

/// The IR spec for the unary op on the symbolic operand `a` (== W0):
///   * Not      -> `~a`      (BvNot)
///   * Neg (any)-> `0 - a`   (BvSub of zero — the WRAPPING two's-complement
///                            negation the trust-ir `Neg` semantics compute;
///                            `Formula` has no `BvNeg`, and `0 - a` is exactly
///                            what the AArch64 NEG alias `SUB Xd,XZR,Xn` emits).
fn unop_spec(kind: UnKind) -> Formula {
    let a = Box::new(wn(0));
    match kind {
        UnKind::Not => Formula::BvNot(a, 32),
        UnKind::NegGuarded | UnKind::NegBare => Formula::BvSub(Box::new(bv32(0)), a, 32),
    }
}

/// `op(a) + 1` — the WRONG spec for the negative control.
fn unop_plus_one_spec(kind: UnKind) -> Formula {
    Formula::BvAdd(Box::new(unop_spec(kind)), Box::new(bv32(1)), 32)
}

// ---------------------------------------------------------------------------
// Concrete byte-execution oracle.
// ---------------------------------------------------------------------------

enum ConcreteOutcome {
    Trapped,
    Value(Formula),
}

fn concrete_run(code: &[u8], base: u64, a: i32) -> ConcreteOutcome {
    let mut state = MachineState::symbolic();
    state.gpr[0] = Formula::BitVec { value: i128::from(a) & 0xffff_ffff, width: 64 };
    let mut exec = Executor::new(code, base);
    match exec.run(base, state, Vec::new(), 0) {
        Ok(out) => ConcreteOutcome::Value(out),
        Err(ExecError::Trapped) => ConcreteOutcome::Trapped,
        Err(e) => panic!("concrete run failed: {e:?}"),
    }
}

fn concrete_equals(out: &Formula, expected: i32) -> bool {
    let mut solver = Solver::try_new(Logic::QfBv).expect("ay Solver::try_new");
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

fn bytes_value_equals(code: &[u8], base: u64, a: i32, expected: i32) -> bool {
    match concrete_run(code, base, a) {
        ConcreteOutcome::Value(out) => concrete_equals(&out, expected),
        ConcreteOutcome::Trapped => false,
    }
}

// ===========================================================================
// TEST 0 — LIR SHAPE: the unop lowers to the right Bnot/Ineg; the guarded Neg
// additionally carries a guard Brif + Trap, the bare/Not shapes do NOT, and
// none materialize memory.
// ===========================================================================

#[test]
fn unop_lir_shape_carries_right_opcode_and_guard() {
    use trust_cg_lower::instructions::Opcode as LO;
    // (kind, expected-unary-opcode predicate, expected guard-branch count).
    let cases: &[(UnKind, fn(&LO) -> bool, usize)] = &[
        (UnKind::Not, |o| matches!(o, LO::Bnot), 0),
        (UnKind::NegBare, |o| matches!(o, LO::Ineg), 0),
        (UnKind::NegGuarded, |o| matches!(o, LO::Ineg), 1),
    ];
    for &(kind, is_unop, want_brif) in cases {
        let module = make_bridge_unop_module(kind);
        let lir = lower_trust_ir_function_to_lir(&module, &module.functions[0])
            .expect("unop lowers");
        assert!(lir.stack_slots.is_empty(), "unop must materialize NO memory ({kind:?})");
        let mut unops = 0;
        let mut brif = 0;
        let mut trap = 0;
        for block in lir.blocks.values() {
            for inst in &block.instructions {
                if is_unop(&inst.opcode) {
                    unops += 1;
                }
                if matches!(inst.opcode, LO::Brif { .. }) {
                    brif += 1;
                }
                if matches!(inst.opcode, LO::Trap) {
                    trap += 1;
                }
            }
        }
        assert_eq!(unops, 1, "exactly one unary opcode ({kind:?})");
        assert_eq!(brif, want_brif, "guard Brif count ({kind:?})");
        assert_eq!(trap, want_brif, "guard Trap count ({kind:?})");
    }
}

// NEGATIVE control on the mapping itself: Not must map to Bnot (NOT Ineg), and
// Neg to Ineg (NOT Bnot). A swap would silently miscompile (~a vs -a differ by 1).
#[test]
fn unop_mapping_is_not_swapped() {
    use trust_cg_lower::instructions::Opcode as LO;
    let not_m = make_bridge_unop_module(UnKind::Not);
    let not_lir =
        lower_trust_ir_function_to_lir(&not_m, &not_m.functions[0]).expect("not lowers");
    let has_bnot = not_lir.blocks.values().any(|b| b.instructions.iter().any(|i| matches!(i.opcode, LO::Bnot)));
    let has_ineg_in_not =
        not_lir.blocks.values().any(|b| b.instructions.iter().any(|i| matches!(i.opcode, LO::Ineg)));
    assert!(has_bnot, "!a must be Bnot (bitwise complement)");
    assert!(!has_ineg_in_not, "!a must NOT be Ineg — that would compute -a, off by one");

    let neg_m = make_bridge_unop_module(UnKind::NegBare);
    let neg_lir =
        lower_trust_ir_function_to_lir(&neg_m, &neg_m.functions[0]).expect("neg lowers");
    let has_ineg = neg_lir.blocks.values().any(|b| b.instructions.iter().any(|i| matches!(i.opcode, LO::Ineg)));
    let has_bnot_in_neg =
        neg_lir.blocks.values().any(|b| b.instructions.iter().any(|i| matches!(i.opcode, LO::Bnot)));
    assert!(has_ineg, "-a must be Ineg (negation)");
    assert!(!has_bnot_in_neg, "-a must NOT be Bnot — that would compute ~a, off by one");
}

// ===========================================================================
// TEST 1 — the converter emits a real object; the guarded Neg's __text carries a
// conditional branch (the i32::MIN guard was lowered, not dropped); the
// unguarded shapes carry none.
// ===========================================================================

#[test]
fn unop_emits_object_and_guard_branch_only_when_guarded() {
    for kind in [UnKind::Not, UnKind::NegBare, UnKind::NegGuarded] {
        let module = make_bridge_unop_module(kind);
        let (code, base) = emit_text(&module);
        assert!(!code.is_empty(), "emitted __text is empty for {kind:?}");
        let has_branch = has_conditional_branch(&code, base);
        match kind {
            UnKind::NegGuarded => assert!(
                has_branch,
                "guarded -a must carry a conditional branch (guard lowered)"
            ),
            UnKind::Not | UnKind::NegBare => assert!(
                !has_branch,
                "unguarded {kind:?} must be straight-line (no guard)"
            ),
        }
    }
}

// ===========================================================================
// TEST 2 — concrete value-differential: the EMITTED BYTES compute the right
// unary value. !0=-1, !5=-6, neg(5)=-5, neg(-5)=5, and the WRAP neg(i32::MIN)=
// i32::MIN for the BARE (unguarded) neg. The GUARDED neg's TRAP-on-i32::MIN is
// covered by TEST 1 (the guard's conditional branch survives in __text) and
// TEST 3 (the proof carries the non-trivial `a != i32::MIN` no-trap precondition,
// i.e. the executor DID diverge the i32::MIN arm into the abort). The symbolic
// path-merge `concrete_run` merges the guard's two arms rather than reporting a
// single-input trap, so it is not the right oracle for "this input traps".
// ===========================================================================

#[test]
fn unop_emitted_bytes_values_are_correct() {
    // NOT: bitwise complement (~a == -a - 1).
    let (code, base) = emit_text(&make_bridge_unop_module(UnKind::Not));
    assert!(bytes_value_equals(&code, base, 0, -1), "!0 == -1");
    assert!(bytes_value_equals(&code, base, 5, -6), "!5 == -6");
    assert!(bytes_value_equals(&code, base, -1, 0), "!(-1) == 0");
    assert!(bytes_value_equals(&code, base, i32::MIN, i32::MAX), "!i32::MIN == i32::MAX");

    // NEG (bare, wrapping): -a for all a, INCLUDING i32::MIN which wraps to itself.
    let (code, base) = emit_text(&make_bridge_unop_module(UnKind::NegBare));
    assert!(bytes_value_equals(&code, base, 5, -5), "neg(5) == -5");
    assert!(bytes_value_equals(&code, base, -5, 5), "neg(-5) == 5");
    assert!(bytes_value_equals(&code, base, 0, 0), "neg(0) == 0");
    assert!(bytes_value_equals(&code, base, i32::MIN, i32::MIN), "neg(i32::MIN) wraps to i32::MIN");

    // NEG (guarded): -a on the no-trap inputs (the guard's i32::MIN trap is
    // covered by TEST 1 + TEST 3, see the test-section note above).
    let (code, base) = emit_text(&make_bridge_unop_module(UnKind::NegGuarded));
    assert!(bytes_value_equals(&code, base, 5, -5), "guarded neg(5) == -5");
    assert!(bytes_value_equals(&code, base, -5, 5), "guarded neg(-5) == 5");
    assert!(bytes_value_equals(&code, base, 100, -100), "guarded neg(100) == -100");
}

// ===========================================================================
// TEST 3 — PROVEN OUTPUT (FULLY SYMBOLIC, INFINITE DOMAIN): on the (no-trap)
// path the emitted bytes compute the unary op for ALL 2^32 values of `a`.
// UNSAT of the negation.
//   * Not / NegBare : precondition is `true` (fully symbolic, total).
//   * NegGuarded    : precondition is `a != i32::MIN` (the trap arm excluded).
// ===========================================================================

fn run_proven_output(kind: UnKind) {
    let module = make_bridge_unop_module(kind);
    let (code, base) = emit_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty");

    let (machine_out, precondition) = symbolic_machine_output(&code, base)
        .unwrap_or_else(|e| panic!("path-merge failed for {kind:?}: {e:?}"));

    // The unguarded shapes must be TOTAL (precondition `true` — the whole point is
    // that Not/wrapping-Neg never trap); the guarded Neg must carry the non-trivial
    // `a != i32::MIN` precondition (guard explored, trap arm excluded).
    match kind {
        UnKind::Not | UnKind::NegBare => assert!(
            matches!(precondition, Formula::Bool(true)),
            "expected a TOTAL (no-precondition) proof for {kind:?}; got {precondition:?}"
        ),
        UnKind::NegGuarded => assert!(
            !matches!(precondition, Formula::Bool(true)),
            "expected a non-trivial no-trap precondition for guarded neg; got `true` \
             (guard not explored — neg could wrap where source traps)"
        ),
    }

    let spec = unop_spec(kind);
    let proven = discharge_equal_under(&precondition, &machine_out, &spec);
    assert!(
        proven,
        "PROVEN-OUTPUT FAILED for {kind:?}: ay did not prove the emitted bytes equal the \
         unary spec for all a.\n  machine_out = {machine_out:?}\n  pre = {precondition:?}"
    );
}

#[test]
fn not_bytes_compute_bitwise_complement_for_all_a() {
    run_proven_output(UnKind::Not);
}

#[test]
fn bare_neg_bytes_compute_wrapping_negation_for_all_a() {
    run_proven_output(UnKind::NegBare);
}

#[test]
fn guarded_neg_bytes_compute_negation_on_no_trap_path() {
    run_proven_output(UnKind::NegGuarded);
}

// ===========================================================================
// TEST 4 — MANDATORY NEGATIVE CONTROL: the SAME bytes proven against `op(a) + 1`
// (under the same precondition) MUST be SAT — a non-SAT result would make the
// positive certificate vacuous.
// ===========================================================================

fn run_negative_control(kind: UnKind) {
    let module = make_bridge_unop_module(kind);
    let (code, base) = emit_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty");

    let (machine_out, precondition) = symbolic_machine_output(&code, base)
        .unwrap_or_else(|e| panic!("path-merge failed for {kind:?}: {e:?}"));
    let wrong = unop_plus_one_spec(kind);
    let proven = discharge_equal_under(&precondition, &machine_out, &wrong);
    assert!(
        !proven,
        "VACUITY CHECK FAILED for {kind:?}: the unop bytes were 'proven' equal to op(a)+1; \
         the discharge has no teeth.\n  machine_out = {machine_out:?}"
    );
}

#[test]
fn negative_control_not_vs_plus_one_is_sat() {
    run_negative_control(UnKind::Not);
}

#[test]
fn negative_control_bare_neg_vs_plus_one_is_sat() {
    run_negative_control(UnKind::NegBare);
}

#[test]
fn negative_control_guarded_neg_vs_plus_one_is_sat() {
    run_negative_control(UnKind::NegGuarded);
}
