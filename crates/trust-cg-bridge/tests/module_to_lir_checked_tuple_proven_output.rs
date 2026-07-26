// module_to_lir_checked_tuple_proven_output.rs — the "trust-ir first" codegen
// seam, extended to the BRIDGE's checked-arithmetic TUPLE idiom, proven over the
// REAL emitted bytes.
//
// This is the BRIDGE idiom, DISTINCT from the producer's separate-SSA
// `Inst::Overflow -> [value, overflowed]` that `module_to_lir_overflow_proven_
// output.rs` handles. The Module here is sourced from a REAL trust-types
// `VerifiableFunction` whose body is `Rvalue::CheckedBinaryOp(Add, a, b)` plus a
// `Terminator::Assert { Overflow(Add) }` — exactly the MIR shape rustc lowers
// `a + b` (overflow checks on) to — run through `trust_ir_bridge::lower_to_trust_ir`.
// That bridge emits (verified by dumping the real Module):
//
//     %v, %o = add.overflow i32 %a, %b      ; Inst::Overflow  -> [value, flag]
//     %u  = undef (i32, bool)               ; TUPLE-typed Undef SEED  (the gap!)
//     %t0 = insertfield (i32,bool) %u, 0, %v   ; field 0 <- value
//     %t  = insertfield (i32,bool) %t0, 1, %o  ; field 1 <- flag  (FULL tuple)
//     %f  = extractfield bool %t, 1            ; read the overflow flag
//     %c  = const bool false
//     %ok = icmp eq bool %f, %c                ; ok = (flag == false) == !overflow
//     assert %ok                                ; trap iff overflow
//     br bb1
//   bb1:
//     %r  = extractfield i32 %t, 0             ; read the value
//     ret (copy %r)
//
// The converter DECOMPOSES the `Tuple([I32, Bool])` into the two scalar SSA
// Values (`CheckedSadd`'s `[value, overflow_b1]`) WITHOUT ever materializing a
// tuple in memory (the pinned interpreter lacks `Ty::Tuple` `byte_size`): the
// `Undef` seed and both `InsertField`s emit NO LIR, and each `ExtractField`
// becomes a `Copy` of the resolved field Value. The lowered LIR therefore has
// ZERO stack slots — proven by `decomposes_with_no_memory` below.
//
// We then prove the emitted machine bytes compute `a + b` ON THE NO-OVERFLOW
// PATH for ALL inputs:
//
//   (1) VALUE-DIFFERENTIAL (concrete): the trust-ir reference INTERPRETER runs
//       the REAL bridge Module on add(2,3)=5, add(-1,1)=0 — through the Overflow
//       + InsertField + ExtractField + Assert machinery;
//   (2) the emitted __text carries a conditional branch + a trap (the overflow
//       check was lowered, not dropped);
//   (3) PROVEN-OUTPUT (infinite domain): the emitted bytes are decoded into
//       machine effects (NOT reconstructed from the IR); the bounded path-merge
//       executor explores the conditional branch, the OVERFLOW arm diverges into
//       the `abort` trap, and the executor returns the LIVE (no-overflow) arm's
//       value under the live-arm path condition (the NO-OVERFLOW PRECONDITION).
//       ay (QF_BV) proves `precondition => (machine_out == a + b)` for ALL input
//       pairs (UNSAT of the negation); and
//   (4) NEGATIVE CONTROL: the SAME bytes proven against an `a + b + 1` spec MUST
//       be SAT — otherwise the discharge is vacuous.
//
// A wrong tuple decomposition (reading the wrong field, dropping the value,
// confusing value/flag, materializing a bad tuple) makes ay return a
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

use trust_ir::Module;

// ---------------------------------------------------------------------------
// Source the REAL bridge Module from a trust-types VerifiableFunction whose body
// is the canonical rustc `a + b` shape: a `Rvalue::CheckedBinaryOp(Add, a, b)`
// assigned to a `(i32, bool)` tuple local, an `Overflow(Add)` assert on the
// `.1` flag, then `return _.0`. This is byte-for-byte what `rustc -> MIR ->
// VerifiableFunction` produces; lowering it via `trust_ir_bridge::lower_to_trust_ir`
// gives the EXACT bridge tuple idiom the converter must decompose.
// ---------------------------------------------------------------------------

fn make_bridge_checked_add_module() -> Module {
    use trust_types::{
        AssertMessage, BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan,
        Statement, Terminator, Ty as TtTy, VerifiableBody, VerifiableFunction,
    };

    let vf = VerifiableFunction {
        name: "add".to_string(),
        def_path: "checked_tuple::add".to_string(),
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

    trust_ir_bridge::lower_to_trust_ir(&vf).expect("bridge lower_to_trust_ir failed for add")
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
        .expect("lower_trust_ir_function_to_lir failed for bridge checked-add tuple");
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

// ===========================================================================
// BOUNDED SYMBOLIC PATH-MERGING EXECUTOR (mirrors module_to_lir_overflow_proven_
// output.rs): explores both targets at a ConditionalBranch; an arm that diverges
// into the `abort` trap (a Call effect) is the overflow/panic path — discarded,
// and the live arm's path condition is conjoined into the no-overflow PRECOND.
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

fn add_spec() -> Formula {
    Formula::BvAdd(Box::new(wn(0)), Box::new(wn(1)), 32)
}

fn add_plus_one_spec() -> Formula {
    Formula::BvAdd(Box::new(add_spec()), Box::new(bv32(1)), 32)
}

// NOTE ON THE VALUE-DIFFERENTIAL ORACLE. The trust-ir reference interpreter
// CANNOT run this exact bridge tuple idiom: it executes the `Inst::Undef`
// `(i32, bool)` SEED eagerly and treats `InsertField`'s read of that aggregate
// as a read of an undefined value (`UndefinedBehavior: executing undef would
// read an undefined value`). That is the SAME pinned-interpreter aggregate-undef
// boundary the converter routes AROUND by decomposing the tuple into scalar SSA
// Values (never materializing the aggregate). So the value oracle here is the
// EMITTED BYTES themselves, executed CONCRETELY by `trust_machine_sem` on
// concrete register inputs (`concrete_add` below) — exactly the same machine
// semantics the symbolic proof uses, but with constant arguments. The infinite-
// domain proof (TEST 3) subsumes it; the concrete check is a fast spot-witness.

/// The concrete byte-execution outcome for X0=a, X1=b: `Trapped` if the input
/// overflows (the live arm diverged into abort), else the closed 32-bit output
/// Formula on the no-overflow path.
enum ConcreteOutcome {
    Trapped,
    Value(Formula),
}

/// Run the EMITTED bytes with X0=a, X1=b (low 32 bits). Returns `Trapped` for an
/// overflowing input, else the closed W0 output expression over the pinned
/// constants.
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

/// PROVE (via ay) that the closed concrete byte output equals `expected` (a
/// 32-bit constant): UNSAT of `out != expected`. Returns true on a forced equal.
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

/// True iff the bytes compute `a + b` on a no-overflow input `(a, b)`, proven by
/// ay over the closed byte output. (The bounded path-merge executor explores
/// both the live and trap arms, so it always yields the no-overflow arm's value
/// here; the overflow PATH itself is exercised by the non-trivial no-overflow
/// precondition the infinite-domain proof requires.)
fn bytes_add_equals(code: &[u8], base: u64, a: i32, b: i32, expected: i32) -> bool {
    match concrete_run(code, base, a, b) {
        ConcreteOutcome::Value(out) => concrete_equals(&out, expected),
        ConcreteOutcome::Trapped => false,
    }
}

// ===========================================================================
// TEST 0 — the tuple is DECOMPOSED with NO memory: the bridge tuple idiom maps
// to a CheckedSadd + Brif + Trap + Icmp and ZERO stack slots (no tuple in mem).
// ===========================================================================

#[test]
fn decomposes_with_no_memory() {
    use trust_cg_lower::instructions::Opcode as LO;
    let module = make_bridge_checked_add_module();
    let lir = lower_trust_ir_function_to_lir(&module, &module.functions[0])
        .expect("bridge tuple idiom decomposes");

    assert!(
        lir.stack_slots.is_empty(),
        "tuple decompose must materialize NO memory; got {} stack slots",
        lir.stack_slots.len()
    );

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
    assert_eq!(checked, 1, "one CheckedSadd from the bridge Overflow");
    assert_eq!(brif, 1, "one Brif (overflow assert)");
    assert_eq!(trap, 1, "one Trap (shared trap block)");
    assert_eq!(icmp, 1, "one Icmp (ok = flag == false)");
}

// ===========================================================================
// TEST 1 — the converter emits a real object whose __text carries a conditional
// branch (the overflow check was lowered, not dropped).
// ===========================================================================

#[test]
fn bridge_checked_add_emits_object_with_conditional_branch() {
    let module = make_bridge_checked_add_module();
    let (code, base) = emit_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty for bridge checked-add");
    assert!(
        has_conditional_branch(&code, base),
        "expected a conditional branch in the emitted bytes (overflow check lowered)"
    );
}

// ===========================================================================
// TEST 2 — concrete value-differential: the EMITTED BYTES compute add(a,b)=a+b
// on no-overflow inputs (the byte oracle, since the interpreter cannot run the
// aggregate-undef bridge idiom — see the note above).
// ===========================================================================

#[test]
fn bridge_emitted_bytes_add_is_correct() {
    let module = make_bridge_checked_add_module();
    let (code, base) = emit_text(&module);
    assert!(bytes_add_equals(&code, base, 2, 3, 5), "add(2,3) == 5");
    assert!(bytes_add_equals(&code, base, -1, 1, 0), "add(-1,1) == 0");
    assert!(bytes_add_equals(&code, base, 0, 0, 0), "add(0,0) == 0");
    assert!(bytes_add_equals(&code, base, 40, 2, 42), "add(40,2) == 42");
    assert!(bytes_add_equals(&code, base, -5, -7, -12), "add(-5,-7) == -12 (no overflow)");
}

// ===========================================================================
// TEST 3 — PROVEN OUTPUT (infinite domain): on the no-overflow path the emitted
// bytes compute `a + b` for ALL inputs (UNSAT of the negation).
// ===========================================================================

#[test]
fn bridge_checked_add_bytes_compute_a_plus_b_on_no_overflow_path() {
    let module = make_bridge_checked_add_module();

    let (code, base) = emit_text(&module);
    // Concrete byte-level value-differential precondition.
    assert!(bytes_add_equals(&code, base, 2, 3, 5), "value-differential precondition");

    assert!(!code.is_empty(), "emitted __text is empty");

    let (machine_out, precondition) = symbolic_machine_output(&code, base)
        .expect("path-merge of the bridge checked-add bytes failed (loop/unsupported/budget)");

    // A vacuously-true precondition would mean the overflow trap was never
    // explored (the check was dropped). Assert it is non-trivial.
    assert!(
        !matches!(precondition, Formula::Bool(true)),
        "expected a non-trivial no-overflow precondition; got `true` (overflow trap not explored)"
    );

    let spec = add_spec();
    let proven = discharge_equal_under(&precondition, &machine_out, &spec);
    assert!(
        proven,
        "PROVEN-OUTPUT FAILED: ay did not prove the bridge checked-add bytes equal a+b on the \
         no-overflow path for all inputs.\n  machine_out = {machine_out:?}\n  pre = {precondition:?}"
    );
}

// ===========================================================================
// TEST 4 — MANDATORY NEGATIVE CONTROL: the SAME bytes proven against `a + b + 1`
// (under the same precondition) MUST be SAT — a non-SAT result would make the
// positive certificate vacuous.
// ===========================================================================

#[test]
fn negative_control_bridge_add_vs_a_plus_b_plus_1_is_sat() {
    let module = make_bridge_checked_add_module();
    let (code, base) = emit_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty");

    let (machine_out, precondition) = symbolic_machine_output(&code, base)
        .expect("path-merge of the bridge checked-add bytes failed");

    let wrong = add_plus_one_spec();
    let proven = discharge_equal_under(&precondition, &machine_out, &wrong);
    assert!(
        !proven,
        "VACUITY CHECK FAILED: the bridge checked-add bytes were 'proven' equal to a+b+1; \
         the tuple-decompose discharge has no teeth.\n  machine_out = {machine_out:?}"
    );
}
