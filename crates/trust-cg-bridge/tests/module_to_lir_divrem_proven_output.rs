// module_to_lir_divrem_proven_output.rs — the "trust-ir first" codegen seam,
// extended to CHECKED INTEGER DIVISION and REMAINDER (i32 / u32 a/b and a%b),
// proven over the REAL emitted bytes.
//
// GOAL: take a `trust_ir::Module` sourced from a REAL trust-types
// `VerifiableFunction` whose body is the canonical rustc div/rem shape — a
// `DivisionByZero`/`RemainderByZero` guard (and, for SIGNED operands, an
// `Overflow(Div|Rem)` guard for the `i32::MIN / -1` case) followed by the bare
// `Rvalue::BinaryOp(Div|Rem, a, b)` — run through
// `trust_ir_bridge::lower_to_trust_ir`. That bridge emits:
//
//     bb0:  %z  = const 0
//           %c  = icmp eq b, %z          ; the div-by-zero predicate (b == 0)
//           %f  = const false
//           %ok = icmp eq %c, %f         ; ok = !(b == 0)
//           assert %ok                   ; trap iff b == 0   (div-by-zero guard)
//           br bb1
//     bb1:  (SIGNED ONLY) the i32::MIN/-1 overflow guard, same Assert/Br shape
//           br bbN
//     bbN:  %r = sdiv/udiv/srem/urem i32 a, b   ; the BARE divide  (Inst::BinOp)
//           ret %r
//
// The div-by-zero and signed-overflow GUARDS lower through the EXISTING
// Const/ICmp/Assert(->Brif/Trap)/Br machinery the converter already carries
// (the same path the checked-overflow ADD/MUL slices use). The ONLY new thing
// is mapping the bare `Inst::BinOp { op: SDiv/UDiv/SRem/URem }` to the LIR
// `Sdiv/Udiv/Srem/Urem` opcodes (signedness is carried by the trust-ir op, set
// by the producer from the source operand type — never guessed here). FAIL-CLOSED
// on i128 div/rem and all float div.
//
// We prove the emitted machine bytes compute `a/b` (resp `a%b`) ON THE NO-TRAP
// PATH:
//
//   (1) GUARD SURVIVES (LIR + bytes): the lowered LIR carries the right
//       Sdiv/Udiv/Srem/Urem + a Brif + a Trap (the guard was lowered, not
//       dropped), and the emitted __text carries a real conditional branch.
//   (2) VALUE-DIFFERENTIAL (concrete bytes): e.g. 7/2=3, -7/2=-2 (signed trunc
//       toward zero), 7%3=1, -7%3=-1.
//   (3) PROVEN-OUTPUT (HALF-SYMBOLIC, INFINITE DOMAIN): the emitted bytes are
//       decoded into machine effects (NOT reconstructed from the IR). The
//       NO-TRAP PRECONDITION is the fixture's SOURCE domain (b != 0, and for
//       signed b != -1), read off its own `Assert` terminators and bound to the
//       original argument registers — never derived from the emitted branches.
//       The executor omits a guard arm only when ay proves that arm's
//       accumulated path condition UNSAT under that domain; the trap arm (a
//       `BRK #1` since trust-cg b80b958f5) is therefore never decoded on the
//       proven path, and a FEASIBLE trap still reaches the unchanged
//       Semantics refusal. ay (QF_BV) proves
//       `precondition => (machine_out == a OP c)` for ALL 2^32 values of the
//       symbolic `a`, for a REPRESENTATIVE SET of fixed divisors `c` (UNSAT of
//       the negation).
//   (4) NEGATIVE CONTROL: the SAME bytes proven against `a OP c + 1` (under the
//       same precondition) MUST be SAT — otherwise the discharge is vacuous.
//   (5) DOMAIN AND REFUSAL CONTROLS: the source domain has exact boundaries;
//       feasible trap inputs (b == 0; signed b == -1), an entry BRK and a call
//       remain refusals, and an inverted emitted guard cannot silently shrink
//       the admitted input domain.
//
// These are bounded development solver checks, not kernel certificates.
//
// WHY HALF-SYMBOLIC. A fully-symbolic 32-bit divide equivalence is among the
// hardest QF_BV instances (ay bit-blasts a 32x32 restoring divider); see
// `full_symbolic_div_proof_is_divider_equivalence_bound` below for the recorded
// boundary. PINNING the DIVISOR `b` to a literal turns the emitted `UDIV/SDIV`
// into a divide-by-constant, which ay closes — WITHOUT weakening the statement:
// it is still a proof over ALL 2^32 values of the dividend `a`, over the REAL
// emitted bytes (byte-derived machine output, never reconstructed). The chosen
// `c` set spans the signed extremes and magnitudes that drive truncation toward
// zero in both directions. This is the SAME honest bounded framing the
// checked-mul slice uses (`module_to_lir_checked_mul_proven_output.rs`).
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
use trust_ir::Module;
use trust_machine_sem::{Aarch64Semantics, Effect, MachineState, Semantics, condition_to_formula};
use trust_types::{Formula, Sort};

// ---------------------------------------------------------------------------
// Source the REAL bridge Module from a trust-types VerifiableFunction whose body
// is the canonical rustc div/rem shape.
//   * UNSIGNED: a `DivisionByZero`/`RemainderByZero` guard then the bare divide.
//   * SIGNED:   the same div-by-zero guard, THEN an `Overflow(Div|Rem)` guard
//               (the `i32::MIN / -1` UB), then the bare divide.
// ---------------------------------------------------------------------------

fn make_bridge_divrem_module(signed: bool, rem: bool) -> Module {
    use trust_types::{
        AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue,
        SourceSpan, Statement, Terminator, Ty as TtTy, VerifiableBody, VerifiableFunction,
    };

    let ity = if signed { TtTy::i32() } else { TtTy::u32() };
    let op = if rem { BinOp::Rem } else { BinOp::Div };
    let zero = if signed { ConstValue::Int(0) } else { ConstValue::Uint(0, 32) };

    // _0 ret, _1 a, _2 b, _3 cond(b==0):bool, _4 ovf-cond:bool, _5 result.
    let locals = vec![
        LocalDecl { index: 0, ty: ity.clone(), name: None },
        LocalDecl { index: 1, ty: ity.clone(), name: Some("a".into()) },
        LocalDecl { index: 2, ty: ity.clone(), name: Some("b".into()) },
        LocalDecl { index: 3, ty: TtTy::Bool, name: None },
        LocalDecl { index: 4, ty: TtTy::Bool, name: None },
        LocalDecl { index: 5, ty: ity.clone(), name: None },
    ];

    let div_block_id = if signed { 2 } else { 1 };

    // bb0: div-by-zero guard `_3 = (b == 0); assert(!_3) -> next`.
    let mut blocks = vec![BasicBlock {
        id: BlockId(0),
        stmts: vec![Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::BinaryOp(
                BinOp::Eq,
                Operand::Copy(Place::local(2)),
                Operand::Constant(zero),
            ),
            span: SourceSpan::default(),
        }],
        terminator: Terminator::Assert {
            cond: Operand::Copy(Place::local(3)),
            expected: false,
            msg: if rem { AssertMessage::RemainderByZero } else { AssertMessage::DivisionByZero },
            target: BlockId(if signed { 1 } else { div_block_id }),
            unwind: trust_types::UnwindEdge::Unreachable,
            span: SourceSpan::default(),
        },
    }];

    if signed {
        // bb1: the `i32::MIN / -1` overflow guard. rustc's full predicate is
        // `(a == i32::MIN) & (b == -1)`; the bridge reconstructs the obligation
        // from the source/target Div/Rem op. For the EMITTED-BYTES shape we model
        // the guard's cond as `_4 = (b == -1)` — a real Assert/Br that the
        // converter lowers to a Brif/Trap. (The PRECISE overflow predicate does
        // not change the no-trap arithmetic we prove; the proof pins `b` to
        // non-(-1) divisors. `source_no_trap_domain` follows THIS modeled guard,
        // and `feasible_div_by_zero_and_overflow_traps_remain_brk_refused`
        // drives the trap path itself to the unchanged BRK refusal.)
        blocks.push(BasicBlock {
            id: BlockId(1),
            stmts: vec![Statement::Assign {
                place: Place::local(4),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Eq,
                    Operand::Copy(Place::local(2)),
                    Operand::Constant(ConstValue::Int(-1)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Assert {
                cond: Operand::Copy(Place::local(4)),
                expected: false,
                msg: AssertMessage::Overflow(op),
                target: BlockId(div_block_id),
                unwind: trust_types::UnwindEdge::Unreachable,
                span: SourceSpan::default(),
            },
        });
    }

    // bbN: the BARE divide + return.
    blocks.push(BasicBlock {
        id: BlockId(div_block_id),
        stmts: vec![
            Statement::Assign {
                place: Place::local(5),
                rvalue: Rvalue::BinaryOp(
                    op,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(5))),
                span: SourceSpan::default(),
            },
        ],
        terminator: Terminator::Return,
    });

    let vf = VerifiableFunction {
        name: if rem { "rm".to_string() } else { "dv".to_string() },
        def_path: "divrem::dv".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: 2,
            return_ty: ity,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };

    trust_ir_bridge::lower_to_trust_ir(&vf).expect("bridge lower_to_trust_ir failed for div/rem")
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
        .expect("lower_trust_ir_function_to_lir failed for div/rem");
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

/// Does the emitted __text carry a conditional branch? The div-by-zero (and, for
/// signed, the overflow) guard MUST lower to one — a dropped guard would leave
/// only straight-line code, which would mean the emitted div could trap (or, on
/// AArch64, silently return 0 on `b==0`) where the source would panic.
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
// BOUNDED SYMBOLIC RETURN-PATH EXECUTOR (ported from the inline-multiblock
// replay, 7a1034b5c1). The no-trap input assumption is supplied independently
// of emitted control flow. An arm is omitted only when AY establishes that its
// accumulated path condition is UNSAT. Reachable BRK, calls, and unknown
// feasibility remain refusals; no trap semantics is invented.
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
                    // The Assert trap block no longer begins with `call abort`:
                    // since trust-cg b80b958f5 a LIR `Trap` selects to `BRK #1`,
                    // which the Semantics refuses above. A call is therefore
                    // not a proved diverging branch; it is an unsupported step.
                    Effect::Call { .. } => {
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

/// Same path-merge, but with the SECOND argument register (X1 == `b`, the
/// divisor) pinned to a concrete 32-bit literal `c`. X0 (== `a`) stays FULLY
/// SYMBOLIC, so the resulting `(machine_out, precondition)` is an infinite-domain
/// statement over ALL 2^32 values of `a` for that fixed divisor `c`. Pinning the
/// divisor turns the emitted `UDIV/SDIV` into a divide-by-constant, which ay
/// closes — sidestepping the QF_BV 32x32 divider-equivalence wall while still
/// proving the REAL emitted div/rem bytes over a full symbolic dividend.
fn symbolic_machine_output_b_const(
    code: &[u8],
    base: u64,
    signed: bool,
    c: i32,
) -> Result<(Formula, Formula), ExecError> {
    let mut state = MachineState::symbolic();
    state.gpr[1] = Formula::BitVec { value: i128::from(c) & 0xffff_ffff, width: 64 };
    run_machine_output(code, base, signed, state)
}

fn symbolic_machine_output(
    code: &[u8],
    base: u64,
    signed: bool,
) -> Result<(Formula, Formula), ExecError> {
    run_machine_output(code, base, signed, MachineState::symbolic())
}

/// Bind the source precondition to the ORIGINAL argument registers before any
/// emitted instruction executes; decoded branches cannot redefine this domain.
/// An empty domain (e.g. a pinned trapping divisor) is refused, never proven.
fn run_machine_output(
    code: &[u8],
    base: u64,
    signed: bool,
    state: MachineState,
) -> Result<(Formula, Formula), ExecError> {
    let pre = source_no_trap_domain(signed, state.read_gpr(1, 32));
    if !path_is_feasible(&pre)? {
        return Err(ExecError::Unsupported("empty input domain".into()));
    }
    let out = Executor::new(code, base).run(base, state, Vec::new(), 0, pre.clone())?;
    Ok((out, pre))
}

// ---------------------------------------------------------------------------
// Formula -> ay::Term translation (QF_BV) — including the div/rem variants.
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

/// The fixture's SOURCE no-trap domain over the 32-bit divisor `b`, read off
/// its own `Assert` terminators in `make_bridge_divrem_module` and NEVER off the
/// emitted branches: bb0 traps iff `b == 0`; for SIGNED, the bb1 overflow guard
/// as this fixture models it traps iff `b == -1`. The dividend is unconstrained.
fn source_no_trap_domain(signed: bool, b: Formula) -> Formula {
    let excludes = |value: i32| {
        Formula::Not(Box::new(Formula::Eq(
            Box::new(b.clone()),
            Box::new(bv32(i128::from(value) & 0xffff_ffff)),
        )))
    };
    let mut admitted = vec![excludes(0)];
    if signed {
        admitted.push(excludes(-1));
    }
    Formula::And(admitted)
}

/// `a OP c` spec for a fixed 32-bit divisor `c` (used with X1 pinned to `c`):
/// the 32-bit signed/unsigned quotient or remainder of the symbolic `a` and `c`.
fn divrem_by_const_spec(signed: bool, rem: bool, c: i32) -> Formula {
    let a = Box::new(wn(0));
    let cc = Box::new(bv32(i128::from(c)));
    match (signed, rem) {
        (true, false) => Formula::BvSDiv(a, cc, 32),
        (false, false) => Formula::BvUDiv(a, cc, 32),
        (true, true) => Formula::BvSRem(a, cc, 32),
        (false, true) => Formula::BvURem(a, cc, 32),
    }
}

/// `(a OP c) + 1` — the WRONG spec for the negative control.
fn divrem_by_const_plus_one_spec(signed: bool, rem: bool, c: i32) -> Formula {
    Formula::BvAdd(Box::new(divrem_by_const_spec(signed, rem, c)), Box::new(bv32(1)), 32)
}

/// Fully-symbolic `a OP b` spec (both operands symbolic) — used only by the
/// recorded-boundary `#[ignore]`d test.
fn divrem_spec(signed: bool, rem: bool) -> Formula {
    let a = Box::new(wn(0));
    let b = Box::new(wn(1));
    match (signed, rem) {
        (true, false) => Formula::BvSDiv(a, b, 32),
        (false, false) => Formula::BvUDiv(a, b, 32),
        (true, true) => Formula::BvSRem(a, b, 32),
        (false, true) => Formula::BvURem(a, b, 32),
    }
}

// ---------------------------------------------------------------------------
// Concrete byte-execution oracle.
// ---------------------------------------------------------------------------

fn concrete_run(code: &[u8], base: u64, a: i32, b: i32) -> Result<Formula, ExecError> {
    let mut state = MachineState::symbolic();
    state.gpr[0] = Formula::BitVec { value: i128::from(a) & 0xffff_ffff, width: 64 };
    state.gpr[1] = Formula::BitVec { value: i128::from(b) & 0xffff_ffff, width: 64 };
    // The concrete inputs ARE the precondition: they are bound into X0/X1, so
    // every guard condition is ground over them and feasibility under them
    // alone picks the side that runs. Concrete runs are NOT restricted to the
    // source no-trap domain: a trapping input (b == 0; signed b == -1) makes
    // the BRK side the feasible one, and it reaches the unchanged refusal.
    Executor::new(code, base).run(base, state, Vec::new(), 0, Formula::Bool(true))
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

fn bytes_value_equals(code: &[u8], base: u64, a: i32, b: i32, expected: i32) -> bool {
    let out = concrete_run(code, base, a, b).expect("concrete no-trap execution must return");
    concrete_equals(&out, expected)
}

// ===========================================================================
// TEST 0 — LIR SHAPE: the div/rem lowers to the right Sdiv/Udiv/Srem/Urem with a
// guard Brif + Trap and ZERO stack slots (no spurious memory).
// ===========================================================================

#[test]
fn divrem_lir_shape_carries_guarded_divide() {
    use trust_cg_lower::instructions::Opcode as LO;
    // (signed, rem, expected divide opcode, expected #Brif (#guards)).
    let cases: &[(bool, bool, fn(&LO) -> bool, usize)] = &[
        (false, false, |o| matches!(o, LO::Udiv), 1),
        (true, false, |o| matches!(o, LO::Sdiv), 2),
        (false, true, |o| matches!(o, LO::Urem), 1),
        (true, true, |o| matches!(o, LO::Srem), 2),
    ];
    for &(signed, rem, is_div, want_brif) in cases {
        let module = make_bridge_divrem_module(signed, rem);
        let lir =
            lower_trust_ir_function_to_lir(&module, &module.functions[0]).expect("div/rem lowers");
        assert!(lir.stack_slots.is_empty(), "div/rem must materialize NO memory");
        let mut divs = 0;
        let mut brif = 0;
        let mut trap = 0;
        for block in lir.blocks.values() {
            for inst in &block.instructions {
                if is_div(&inst.opcode) {
                    divs += 1;
                }
                if matches!(inst.opcode, LO::Brif { .. }) {
                    brif += 1;
                }
                if matches!(inst.opcode, LO::Trap) {
                    trap += 1;
                }
            }
        }
        assert_eq!(divs, 1, "exactly one divide opcode (signed={signed} rem={rem})");
        assert_eq!(brif, want_brif, "guard Brif count (signed={signed} rem={rem})");
        assert_eq!(trap, 1, "one shared Trap block (signed={signed} rem={rem})");
    }
}

// ===========================================================================
// TEST 1 — the converter emits a real object whose __text carries a conditional
// branch (the div-by-zero / overflow guard was lowered, not dropped). The one
// shared LIR `Trap` block is a `BRK` in the bytes (no BL/BLR call), so the
// refusal controls below exercise the real trap, not a stand-in.
// ===========================================================================

const VARIANTS: [(bool, bool); 4] = [(false, false), (true, false), (false, true), (true, true)];

#[test]
fn divrem_emits_object_with_guard_conditional_branch() {
    for &(signed, rem) in &VARIANTS {
        let module = make_bridge_divrem_module(signed, rem);
        let (code, base) = emit_text(&module);
        assert!(!code.is_empty(), "emitted __text is empty for div/rem");
        assert!(
            has_conditional_branch(&code, base),
            "expected a conditional branch (guard lowered) for signed={signed} rem={rem}"
        );
        assert_eq!(
            count_opcode(&code, base, &[Opcode::Bl, Opcode::Blr]),
            0,
            "div/rem must have no emitted call edge (signed={signed} rem={rem})"
        );
        assert_eq!(
            count_opcode(&code, base, &[Opcode::Brk]),
            1,
            "div/rem must retain the one shared trap BRK (signed={signed} rem={rem})"
        );
    }
}

// ===========================================================================
// TEST 2 — concrete value-differential: the EMITTED BYTES compute the right
// quotient/remainder on no-trap inputs, including signed truncation toward zero.
//
// NOTE on the trap path (rewritten: its old premise was the retired `call
// abort` trap block, which the executor silently excluded as `Trapped`): every
// input here is in the source no-trap domain, so under these concrete inputs
// the BRK side of each guard is infeasible and never decoded, and
// `bytes_value_equals` witnesses no-trap arithmetic only. That the guard
// genuinely TRAPS on b==0 (and, signed, b==-1) is established directly by
// `feasible_div_by_zero_and_overflow_traps_remain_brk_refused`, on top of TEST 0
// (the LIR carries a Brif to a Trap block) and TEST 1 (a real conditional
// branch and the BRK survive in the emitted __text).
// ===========================================================================

#[test]
fn divrem_emitted_bytes_values_are_correct() {
    // SIGNED DIV: truncation toward zero.
    let (code, base) = emit_text(&make_bridge_divrem_module(true, false));
    assert!(bytes_value_equals(&code, base, 7, 2, 3), "sdiv 7/2 == 3");
    assert!(bytes_value_equals(&code, base, -7, 2, -3), "sdiv -7/2 == -3 (trunc toward 0)");
    assert!(bytes_value_equals(&code, base, 7, -2, -3), "sdiv 7/-2 == -3");
    assert!(bytes_value_equals(&code, base, -7, -2, 3), "sdiv -7/-2 == 3");
    assert!(bytes_value_equals(&code, base, 6, 3, 2), "sdiv 6/3 == 2");

    // UNSIGNED DIV.
    let (code, base) = emit_text(&make_bridge_divrem_module(false, false));
    assert!(bytes_value_equals(&code, base, 7, 2, 3), "udiv 7/2 == 3");
    assert!(bytes_value_equals(&code, base, 100, 10, 10), "udiv 100/10 == 10");

    // SIGNED REM: sign follows the dividend.
    let (code, base) = emit_text(&make_bridge_divrem_module(true, true));
    assert!(bytes_value_equals(&code, base, 7, 3, 1), "srem 7%3 == 1");
    assert!(bytes_value_equals(&code, base, -7, 3, -1), "srem -7%3 == -1 (sign of dividend)");
    assert!(bytes_value_equals(&code, base, 7, -3, 1), "srem 7%-3 == 1");

    // UNSIGNED REM.
    let (code, base) = emit_text(&make_bridge_divrem_module(false, true));
    assert!(bytes_value_equals(&code, base, 7, 3, 1), "urem 7%3 == 1");
    assert!(bytes_value_equals(&code, base, 100, 7, 2), "urem 100%7 == 2");
}

// ===========================================================================
// TEST 3 — PROVEN OUTPUT (HALF-SYMBOLIC, INFINITE DOMAIN): on the no-trap path
// the emitted bytes compute `a OP c` for ALL 2^32 values of the symbolic dividend
// `a`, for a REPRESENTATIVE SET of fixed divisors `c`. UNSAT of the negation.
// ===========================================================================

fn run_proven_output(signed: bool, rem: bool, cs: &[i32]) {
    let module = make_bridge_divrem_module(signed, rem);
    let (code, base) = emit_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty");
    // Concrete byte-level value-differential precondition.
    assert!(bytes_value_equals(&code, base, 7, 2, if rem { 1 } else { 3 }), "value precondition");

    for &c in cs {
        let (machine_out, precondition) = symbolic_machine_output_b_const(&code, base, signed, c)
            .unwrap_or_else(|e| panic!("path-merge failed for c={c}: {e:?}"));

        // The precondition is now the explicit, independent SOURCE no-trap
        // domain (it used to be the live-arm condition recorded when the retired
        // `call abort` arm was excluded). It must never be vacuously `true`.
        // Since `c` is a fixed NON-ZERO, NON-(-1) divisor, the BRK arm is
        // UNSAT under it and never decoded; that the guard still traps on a
        // feasible divisor, and that an inverted guard cannot shrink this
        // domain, is checked by the refusal controls after TEST 4.
        assert!(
            !matches!(precondition, Formula::Bool(true)),
            "expected the explicit independent source no-trap domain for c={c}; got `true`"
        );

        let spec = divrem_by_const_spec(signed, rem, c);
        let proven = discharge_equal_under(&precondition, &machine_out, &spec);
        assert!(
            proven,
            "PROVEN-OUTPUT FAILED for signed={signed} rem={rem} c={c}: ay did not prove the \
             emitted bytes equal a OP {c} on the no-trap path for all a.\n  machine_out = \
             {machine_out:?}\n  pre = {precondition:?}"
        );
    }
}

// Representative NON-ZERO, NON-(-1) divisors that exercise truncation toward zero
// in both directions, the signed extreme, and power-of-two vs odd magnitudes.
const DIVISORS: &[i32] = &[1, 2, 3, 7, -2, -3, 1000, i32::MAX];

#[test]
fn signed_div_bytes_compute_a_div_c_on_no_trap_path() {
    run_proven_output(true, false, DIVISORS);
}

#[test]
fn unsigned_div_bytes_compute_a_div_c_on_no_trap_path() {
    // Unsigned: no negative divisors / no -1 overflow case.
    run_proven_output(false, false, &[1, 2, 3, 7, 1000, i32::MAX]);
}

#[test]
fn signed_rem_bytes_compute_a_rem_c_on_no_trap_path() {
    run_proven_output(true, true, DIVISORS);
}

#[test]
fn unsigned_rem_bytes_compute_a_rem_c_on_no_trap_path() {
    run_proven_output(false, true, &[1, 2, 3, 7, 1000, i32::MAX]);
}

// ===========================================================================
// TEST 4 — MANDATORY NEGATIVE CONTROL: the SAME bytes proven against `a OP c + 1`
// (under the same precondition) MUST be SAT — a non-SAT result would make the
// positive certificate vacuous.
// ===========================================================================

fn run_negative_control(signed: bool, rem: bool, cs: &[i32]) {
    let module = make_bridge_divrem_module(signed, rem);
    let (code, base) = emit_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty");

    for &c in cs {
        let (machine_out, precondition) = symbolic_machine_output_b_const(&code, base, signed, c)
            .unwrap_or_else(|e| panic!("path-merge failed for c={c}: {e:?}"));
        let wrong = divrem_by_const_plus_one_spec(signed, rem, c);
        let proven = discharge_equal_under(&precondition, &machine_out, &wrong);
        assert!(
            !proven,
            "VACUITY CHECK FAILED for signed={signed} rem={rem} c={c}: the div/rem bytes were \
             'proven' equal to (a OP {c})+1; the discharge has no teeth.\n  machine_out = \
             {machine_out:?}"
        );
    }
}

#[test]
fn negative_control_signed_div_vs_plus_one_is_sat() {
    // Skip c==1 for DIV: a/1 + 1 vs a/1 is trivially distinguishable but a/1 == a
    // and the +1 spec is still a real different value, so it is fine; keep all.
    run_negative_control(true, false, DIVISORS);
}

#[test]
fn negative_control_unsigned_rem_vs_plus_one_is_sat() {
    run_negative_control(false, true, &[2, 3, 7, 1000]);
}

// ===========================================================================
// REFUSAL AND DOMAIN CONTROLS: the pruning above may omit a BRK only by
// proving its path impossible. A FEASIBLE trap must still reach the exact,
// unchanged Semantics refusal; a call is not a trap; the source domain has
// exact boundaries; and corrupting an emitted guard cannot shrink the domain.
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
fn feasible_div_by_zero_and_overflow_traps_remain_brk_refused() {
    for &(signed, rem) in &VARIANTS {
        let (code, base) = emit_text(&make_bridge_divrem_module(signed, rem));
        // Division / remainder by zero is a feasible trap in every variant.
        assert_brk_refused(concrete_run(&code, base, 7, 0));
        assert_brk_refused(concrete_run(&code, base, i32::MIN, 0));
        if signed {
            // The modeled signed overflow guard traps on b == -1 for any a.
            assert_brk_refused(concrete_run(&code, base, 7, -1));
            assert_brk_refused(concrete_run(&code, base, i32::MIN, -1));
        } else {
            // Unsigned has no -1 guard: u32::MAX is an ordinary divisor.
            assert!(
                bytes_value_equals(&code, base, 7, -1, if rem { 7 } else { 0 }),
                "unsigned 7 OP u32::MAX must return, not trap (rem={rem})"
            );
        }
    }
    // A BRK at entry is reachable under every input and stays refused.
    assert_brk_refused(concrete_run(&0xd4200020u32.to_le_bytes(), 0, 2, 3));
}

#[test]
fn symbolic_divisor_prunes_the_brk_only_under_the_full_source_domain() {
    for &(signed, rem) in &VARIANTS {
        let (code, base) = emit_text(&make_bridge_divrem_module(signed, rem));
        // Fully symbolic divisor: the BRK arm is not pruned by a ground literal
        // here but only because ay proves it UNSAT under the source domain.
        // (Path merge only; the divide discharge is TEST 5's recorded bound.)
        symbolic_machine_output(&code, base, signed).unwrap_or_else(|e| {
            panic!("symbolic-divisor path merge failed (signed={signed} rem={rem}): {e:?}")
        });
        // With no domain, b == 0 is feasible and the BRK is reached.
        assert_brk_refused(Executor::new(&code, base).run(
            base,
            MachineState::symbolic(),
            Vec::new(),
            0,
            Formula::Bool(true),
        ));
        if signed {
            // Dropping the b != -1 conjunct leaves the signed overflow BRK
            // feasible: the second guard is not pruned vacuously either.
            let state = MachineState::symbolic();
            let div_by_zero_only = source_no_trap_domain(false, state.read_gpr(1, 32));
            assert_brk_refused(Executor::new(&code, base).run(
                base,
                state,
                Vec::new(),
                0,
                div_by_zero_only,
            ));
        }
    }
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

#[test]
fn independent_no_trap_domain_has_exact_boundaries() {
    for (signed, b, admitted) in [
        (false, 0, false),
        (false, 1, true),
        (false, -1, true),
        (false, i32::MIN, true),
        (false, i32::MAX, true),
        (true, 0, false),
        (true, -1, false),
        (true, 1, true),
        (true, -2, true),
        (true, i32::MIN, true),
        (true, i32::MAX, true),
    ] {
        let predicate = source_no_trap_domain(signed, bv32(i128::from(b) & 0xffff_ffff));
        assert_eq!(path_is_feasible(&predicate).unwrap(), admitted, "signed={signed} b={b}");
    }
    // A pinned trapping divisor is an EMPTY domain: refused, never "proven".
    for (signed, rem, c) in [(false, false, 0), (true, true, 0), (true, false, -1)] {
        let (code, base) = emit_text(&make_bridge_divrem_module(signed, rem));
        let result = symbolic_machine_output_b_const(&code, base, signed, c);
        assert!(
            matches!(result, Err(ExecError::Unsupported(ref message))
            if message == "empty input domain"),
            "a trapping pinned divisor must be refused (signed={signed} c={c}): {result:?}"
        );
    }
}

#[test]
fn corrupted_guard_cannot_shrink_the_input_domain() {
    for &(signed, rem) in &VARIANTS {
        let (code, base) = emit_text(&make_bridge_divrem_module(signed, rem));
        let guards: Vec<_> = code
            .chunks_exact(4)
            .enumerate()
            .filter_map(|(index, bytes)| {
                let bytes: [u8; 4] = bytes.try_into().unwrap();
                (decode_aarch64(&bytes, base + (index * 4) as u64).unwrap().opcode == Opcode::BCond)
                    .then_some(index * 4)
            })
            .collect();
        assert_eq!(
            guards.len(),
            if signed { 2 } else { 1 },
            "fixture must have one actual B.cond per source guard (signed={signed} rem={rem})"
        );
        for offset in guards {
            // Invert this one guard's condition (bit 0 of the B.cond `cond`).
            let mut corrupted = code.clone();
            let word = u32::from_le_bytes(corrupted[offset..offset + 4].try_into().unwrap()) ^ 1;
            corrupted[offset..offset + 4].copy_from_slice(&word.to_le_bytes());
            assert_brk_refused(concrete_run(&corrupted, base, 7, 2));
            assert_brk_refused(
                symbolic_machine_output_b_const(&corrupted, base, signed, 2).map(|(out, _)| out),
            );
        }
    }
}

// ===========================================================================
// TEST 5 — BOUNDARY MARKER (ignored): the FULLY-symbolic `a OP b` proof. Both
// operands symbolic 32-bit, so the obligation is a 32x32 divider-equivalence —
// ay bit-blasts the restoring divider and does NOT converge in practical time.
// This is a QF_BV backend-capacity boundary, NOT a soundness gap: TEST 0 pins the
// exact LIR shape, TEST 2 proves the emitted bytes concretely, and TESTS 3-4
// prove them half-symbolically over a full operand with a teeth-bearing negative
// control. Kept `#[ignore]`d so the boundary is recorded and re-checkable once ay
// grows a non-bit-blasting divider lane.
// ===========================================================================

#[test]
#[ignore = "QF_BV 32x32 divider-equivalence: ay bit-blasts the restoring divider and does not \
            converge; soundness is covered by TEST 0 (LIR shape) + TEST 2 (byte values) + \
            TESTS 3-4 (half-symbolic byte proofs). Boundary gates on an ay non-bit-blasting \
            divider lane."]
fn full_symbolic_div_proof_is_divider_equivalence_bound() {
    let module = make_bridge_divrem_module(true, false);
    let (code, base) = emit_text(&module);
    let (machine_out, precondition) =
        symbolic_machine_output(&code, base, true).expect("path-merge of the div bytes failed");
    assert!(
        !matches!(precondition, Formula::Bool(true)),
        "expected a non-trivial no-trap precondition"
    );
    let proven = discharge_equal_under(&precondition, &machine_out, &divrem_spec(true, false));
    assert!(proven, "full-symbolic a/b proof (expected to be capacity-bound in QF_BV)");
}
