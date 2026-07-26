// module_to_lir_shift_proven_output.rs — the "trust-ir first" codegen seam,
// extended to CHECKED INTEGER SHIFTS (`a << b`, `a >> b` on i32/u32),
// proven over the REAL emitted bytes.
//
// GOAL: take a `trust_ir::Module` sourced from a REAL trust-types
// `VerifiableFunction` whose body is the canonical rustc shift shape — the
// bare `Rvalue::BinaryOp(Shl|Shr, a, b)` guarded by a shift-amount-in-range
// `Assert { Overflow(Shl|Shr) }` (the `ShiftInRange` obligation, the exact
// shape `trust-ir-bridge::parity::shift_direct_*_amount` builds) — run through
// `trust_ir_bridge::lower_to_trust_ir`. That bridge emits:
//
//     bb0:  %r  = shl/lshr/ashr a, b        ; the BARE shift (Inst::BinOp)
//           %f  = const false
//           %ok = icmp eq in_range, %f       ; the guard flag != false machinery
//           assert %ok  [ShiftInRange]       ; trap iff amount out of range
//           br bb1
//     bb1:  ret %r
//
// The shift-amount-in-range GUARD lowers through the EXISTING
// Const/ICmp/Assert(->Brif/Trap)/Br machinery the converter already carries
// (the SAME path the div/rem and checked-overflow slices use). The ONLY new
// thing is mapping the bare `Inst::BinOp { op: Shl/LShr/AShr }` to the LIR
// `Ishl/Ushr/Sshr` opcodes:
//   * `Shl  -> Ishl`  (logical shift left; signedness irrelevant),
//   * `LShr -> Ushr`  (LOGICAL shift right, chosen when the shifted value is
//                      UNSIGNED — zero-filling),
//   * `AShr -> Sshr`  (ARITHMETIC shift right, chosen when the shifted value is
//                      SIGNED — sign-extending).
// The logical-vs-arithmetic distinction is carried by the trust-ir op, set by
// the producer from the shifted-value operand's signedness (`map_binop`:
// `Shr if signed => AShr` else `LShr`) — never guessed in the converter.
// FAIL-CLOSED on i128 shifts (multi-register) and all float ops.
//
// SOUNDNESS — the amount<width precondition. The AArch64 register-form variable
// shift (LSLV/LSRV/ASRV) MASKS the amount modulo the register width: the machine
// semantics (`trust-machine-sem::aarch64::sem_shift_var`) model it EXACTLY as
// `Rn <shift> (Rm & (width-1))`. trust-ir shift semantics instead TRAP when
// `amount >= width` (Rust `<<`/`>>` UB; interpreter `shift_amount`). The
// producer's `ShiftInRange` guard establishes the `amount < width` precondition
// on the no-trap path, and UNDER that precondition the mask is a NO-OP
// (`amount & (width-1) == amount`), so the AArch64-masked shift EQUALS the
// guarded (mathematical) shift. This is the same guard-lowers-then-precondition-
// holds argument the div/rem slice uses; we discharge it over the REAL emitted
// bytes below.
//
// We prove the emitted machine bytes compute `a << c` (resp `a >> c`) ON THE
// NO-TRAP PATH:
//
//   (1) GUARD SURVIVES (LIR + bytes): the lowered LIR carries the right
//       Ishl/Ushr/Sshr + a Brif + a Trap (the guard was lowered, not dropped),
//       and the emitted __text carries a real conditional branch.
//   (2) VALUE-DIFFERENTIAL (concrete bytes): e.g. 1<<4=16, -8>>1=-4 (arithmetic,
//       sign-preserving), 8u32>>1=4 (logical).
//   (3) PROVEN-OUTPUT (HALF-SYMBOLIC, INFINITE DOMAIN): the emitted bytes are
//       decoded into machine effects (NOT reconstructed from the IR). The bounded
//       path-merge executor explores the guard branch; the trapping arm diverges
//       into the abort `Trap`, so it is the excluded path — the executor returns
//       the LIVE (no-trap) arm's value and records the live-arm path condition as
//       the NO-TRAP PRECONDITION. ay (QF_BV) proves `precondition =>
//       (machine_out == a << c)` for ALL 2^32 values of the symbolic `a`, for a
//       REPRESENTATIVE SET of fixed shift amounts `c` {0,1,7,31} (UNSAT of the
//       negation).
//   (4) NEGATIVE CONTROL: the SAME bytes proven against `(a << c) + 1` (under the
//       same precondition) MUST be SAT — otherwise the discharge is vacuous.
//
// WHY HALF-SYMBOLIC. A fully-symbolic variable shift equivalence would require ay
// to reason about the register-form mask `a << (b & 31)` against the guarded
// `a << b` for a symbolic `b`; PINNING the AMOUNT `b` to a literal `c` turns the
// emitted `LSLV/LSRV/ASRV` into a shift-by-constant, which ay closes — WITHOUT
// weakening the statement: it is still a proof over ALL 2^32 values of the shifted
// value `a`, over the REAL emitted bytes (byte-derived machine output, never
// reconstructed). This is the SAME honest bounded framing the div/rem slice uses
// (pin the divisor) and the checked-mul slice uses.
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
// The kind of right shift being modeled. `Shl` is direction-agnostic.
// ---------------------------------------------------------------------------
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ShiftKind {
    /// `a << b`. Shifted value signedness is irrelevant (Ishl either way).
    Shl,
    /// `a >> b` with a SIGNED shifted value -> arithmetic (Sshr).
    AShr,
    /// `a >> b` with an UNSIGNED shifted value -> logical (Ushr).
    LShr,
}

// ---------------------------------------------------------------------------
// Source the REAL bridge Module from a trust-types VerifiableFunction whose body
// is the canonical rustc shift shape: the bare shift into `_0` (the return
// local), guarded by a shift-amount-in-range `Assert { Overflow(Shl|Shr) }`.
// The shifted-value type drives the arithmetic-vs-logical choice:
//   * Shl / AShr : signed i32 shifted value.
//   * LShr       : unsigned u32 shifted value.
// The shift AMOUNT is `u32` throughout (the Rust shift-amount type).
// ---------------------------------------------------------------------------
fn make_bridge_shift_module(kind: ShiftKind) -> Module {
    use trust_types::{
        AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue,
        SourceSpan, Statement, Terminator, Ty as TtTy, VerifiableBody, VerifiableFunction,
    };

    // Shifted-value type: signed for Shl/AShr, unsigned for LShr. The MIR-level
    // op is `Shl` for left, `Shr` for right; the bridge picks AShr vs LShr from
    // `lhs_ty.is_signed()`, so the shifted-value type IS the logical/arithmetic
    // selector.
    let (val_ty, mir_op) = match kind {
        ShiftKind::Shl => (TtTy::i32(), BinOp::Shl),
        ShiftKind::AShr => (TtTy::i32(), BinOp::Shr),
        ShiftKind::LShr => (TtTy::u32(), BinOp::Shr),
    };
    // Shift amount is u32 (Rust's shift-count type).
    let amt_ty = TtTy::u32();

    // _0 ret (= shift result), _1 a (shifted value), _2 b (amount),
    // _3 in_range:bool (the guard flag).
    let locals = vec![
        LocalDecl { index: 0, ty: val_ty.clone(), name: None },
        LocalDecl { index: 1, ty: val_ty.clone(), name: Some("a".into()) },
        LocalDecl { index: 2, ty: amt_ty, name: Some("b".into()) },
        LocalDecl { index: 3, ty: TtTy::Bool, name: Some("in_range".into()) },
    ];

    let blocks = vec![
        // bb0:
        //   _3 = (b >= 32)           ; the out-of-range predicate (u32 amount, 32-bit value)
        //   _0 = a <shift> b         ; the bare shift into the return local
        //   Assert(!_3) [Overflow]   ; trap iff amount out of range -> bb1
        //
        // The `_3` guard-flag DEFINITION (`Ge(b, 32)`) is what makes the assert's
        // condition a defined SSA value; the assert's `expected: false` means "trap
        // iff `_3`", so the no-trap precondition the byte executor records is
        // `!(b >= 32)` == `b < 32` — exactly the amount<width precondition under
        // which the AArch64-masked register shift equals the guarded shift.
        BasicBlock {
            id: BlockId(0),
            stmts: vec![
                Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Ge,
                        Operand::Copy(Place::local(2)),
                        Operand::Constant(ConstValue::Uint(32, 32)),
                    ),
                    span: SourceSpan::default(),
                },
                Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        mir_op,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                },
            ],
            terminator: Terminator::Assert {
                cond: Operand::Copy(Place::local(3)),
                expected: false,
                msg: AssertMessage::Overflow(mir_op),
                target: BlockId(1),
                unwind: trust_types::UnwindEdge::Unreachable,
                span: SourceSpan::default(),
            },
        },
        // bb1: return the shifted result (already in _0).
        BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
    ];

    let vf = VerifiableFunction {
        name: match kind {
            ShiftKind::Shl => "shl".to_string(),
            ShiftKind::AShr => "ashr".to_string(),
            ShiftKind::LShr => "lshr".to_string(),
        },
        def_path: "shift::op".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody { locals, blocks, arg_count: 2, return_ty: val_ty },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    trust_ir_bridge::lower_to_trust_ir(&vf).expect("bridge lower_to_trust_ir failed for shift")
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
        .expect("lower_trust_ir_function_to_lir failed for shift");
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

/// Does the emitted __text carry a conditional branch? The shift-amount-in-range
/// guard MUST lower to one — a dropped guard would leave only straight-line code,
/// which would mean the emitted shift could return the MASKED value (`a << (b &
/// 31)`) where the source would panic (`b >= 32`).
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
// BOUNDED SYMBOLIC PATH-MERGING EXECUTOR (mirrors the div/rem test): the
// trapping guard arm (a `Trap`/abort) diverges that arm, accumulating the
// no-trap precondition.
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

/// Path-merge with the SECOND argument register (X1 == `b`, the shift AMOUNT)
/// pinned to a concrete 32-bit literal `c`. X0 (== `a`, the shifted value) stays
/// FULLY SYMBOLIC, so the resulting `(machine_out, precondition)` is an
/// infinite-domain statement over ALL 2^32 values of `a` for that fixed amount
/// `c`. Pinning the amount turns the emitted `LSLV/LSRV/ASRV` into a
/// shift-by-constant, which ay closes — while still proving the REAL emitted
/// shift bytes over a full symbolic shifted value.
fn symbolic_machine_output_amt_const(
    code: &[u8],
    base: u64,
    c: u32,
) -> Result<(Formula, Formula), ExecError> {
    let mut state = MachineState::symbolic();
    state.gpr[1] = Formula::BitVec { value: i128::from(c) & 0xffff_ffff, width: 64 };
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
// Formula -> ay::Term translation (QF_BV) — including the shift variants.
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

/// `a <shift> c` spec for a fixed 32-bit shift amount `c` (used with X1 pinned to
/// `c`): the 32-bit shift of the symbolic `a` by the concrete `c`.
/// * Shl  -> `a << c`  (BvShl)
/// * AShr -> `a >> c`  arithmetic (BvAShr, sign-extending)
/// * LShr -> `a >> c`  logical (BvLShr, zero-filling)
fn shift_by_const_spec(kind: ShiftKind, c: u32) -> Formula {
    let a = Box::new(wn(0));
    let cc = Box::new(bv32(i128::from(c)));
    match kind {
        ShiftKind::Shl => Formula::BvShl(a, cc, 32),
        ShiftKind::AShr => Formula::BvAShr(a, cc, 32),
        ShiftKind::LShr => Formula::BvLShr(a, cc, 32),
    }
}

/// `(a <shift> c) + 1` — the WRONG spec for the negative control.
fn shift_by_const_plus_one_spec(kind: ShiftKind, c: u32) -> Formula {
    Formula::BvAdd(Box::new(shift_by_const_spec(kind, c)), Box::new(bv32(1)), 32)
}

// ---------------------------------------------------------------------------
// Concrete byte-execution oracle.
// ---------------------------------------------------------------------------

enum ConcreteOutcome {
    Trapped,
    Value(Formula),
}

fn concrete_run(code: &[u8], base: u64, a: i32, b: u32) -> ConcreteOutcome {
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

fn bytes_value_equals(code: &[u8], base: u64, a: i32, b: u32, expected: i32) -> bool {
    match concrete_run(code, base, a, b) {
        ConcreteOutcome::Value(out) => concrete_equals(&out, expected),
        ConcreteOutcome::Trapped => false,
    }
}

// ===========================================================================
// TEST 0 — LIR SHAPE: the shift lowers to the right Ishl/Ushr/Sshr with a guard
// Brif + Trap and ZERO stack slots (no spurious memory).
// ===========================================================================

#[test]
fn shift_lir_shape_carries_guarded_shift() {
    use trust_cg_lower::instructions::Opcode as LO;
    // (kind, predicate on the expected shift opcode).
    let cases: &[(ShiftKind, fn(&LO) -> bool)] = &[
        (ShiftKind::Shl, |o| matches!(o, LO::Ishl)),
        (ShiftKind::AShr, |o| matches!(o, LO::Sshr)),
        (ShiftKind::LShr, |o| matches!(o, LO::Ushr)),
    ];
    for &(kind, is_shift) in cases {
        let module = make_bridge_shift_module(kind);
        let lir = lower_trust_ir_function_to_lir(&module, &module.functions[0])
            .expect("shift lowers");
        assert!(lir.stack_slots.is_empty(), "shift must materialize NO memory ({kind:?})");
        let mut shifts = 0;
        let mut brif = 0;
        let mut trap = 0;
        for block in lir.blocks.values() {
            for inst in &block.instructions {
                if is_shift(&inst.opcode) {
                    shifts += 1;
                }
                if matches!(inst.opcode, LO::Brif { .. }) {
                    brif += 1;
                }
                if matches!(inst.opcode, LO::Trap) {
                    trap += 1;
                }
            }
        }
        assert_eq!(shifts, 1, "exactly one shift opcode ({kind:?})");
        assert_eq!(brif, 1, "exactly one guard Brif ({kind:?})");
        assert_eq!(trap, 1, "one shared Trap block ({kind:?})");
    }
}

// A NEGATIVE control on the mapping itself: the logical/arithmetic choice must be
// distinct. `a >> b` on a SIGNED value must NOT be Ushr, and on an UNSIGNED value
// must NOT be Sshr — a swap would silently miscompile sign behavior.
#[test]
fn right_shift_signedness_selects_arithmetic_vs_logical() {
    use trust_cg_lower::instructions::Opcode as LO;
    let signed = make_bridge_shift_module(ShiftKind::AShr);
    let lir_s = lower_trust_ir_function_to_lir(&signed, &signed.functions[0]).expect("ashr lowers");
    let has_sshr = lir_s.blocks.values().any(|b| b.instructions.iter().any(|i| matches!(i.opcode, LO::Sshr)));
    let has_ushr_in_signed =
        lir_s.blocks.values().any(|b| b.instructions.iter().any(|i| matches!(i.opcode, LO::Ushr)));
    assert!(has_sshr, "signed a>>b must be Sshr (arithmetic)");
    assert!(!has_ushr_in_signed, "signed a>>b must NOT be Ushr (logical) — sign miscompile");

    let unsigned = make_bridge_shift_module(ShiftKind::LShr);
    let lir_u =
        lower_trust_ir_function_to_lir(&unsigned, &unsigned.functions[0]).expect("lshr lowers");
    let has_ushr = lir_u.blocks.values().any(|b| b.instructions.iter().any(|i| matches!(i.opcode, LO::Ushr)));
    let has_sshr_in_unsigned =
        lir_u.blocks.values().any(|b| b.instructions.iter().any(|i| matches!(i.opcode, LO::Sshr)));
    assert!(has_ushr, "unsigned a>>b must be Ushr (logical)");
    assert!(!has_sshr_in_unsigned, "unsigned a>>b must NOT be Sshr (arithmetic) — sign miscompile");
}

// ===========================================================================
// TEST 1 — the converter emits a real object whose __text carries a conditional
// branch (the shift-amount-in-range guard was lowered, not dropped).
// ===========================================================================

#[test]
fn shift_emits_object_with_guard_conditional_branch() {
    for kind in [ShiftKind::Shl, ShiftKind::AShr, ShiftKind::LShr] {
        let module = make_bridge_shift_module(kind);
        let (code, base) = emit_text(&module);
        assert!(!code.is_empty(), "emitted __text is empty for {kind:?}");
        assert!(
            has_conditional_branch(&code, base),
            "expected a conditional branch (guard lowered) for {kind:?}"
        );
    }
}

// ===========================================================================
// TEST 2 — concrete value-differential: the EMITTED BYTES compute the right
// shifted value on no-trap inputs, including arithmetic (sign-preserving) vs
// logical (zero-filling) right shift.
// ===========================================================================

#[test]
fn shift_emitted_bytes_values_are_correct() {
    // LEFT SHIFT.
    let (code, base) = emit_text(&make_bridge_shift_module(ShiftKind::Shl));
    assert!(bytes_value_equals(&code, base, 1, 4, 16), "1 << 4 == 16");
    assert!(bytes_value_equals(&code, base, 3, 0, 3), "3 << 0 == 3");
    assert!(bytes_value_equals(&code, base, 1, 31, i32::MIN), "1 << 31 == i32::MIN");

    // ARITHMETIC RIGHT SHIFT (signed): sign bit fills, so negatives stay negative.
    let (code, base) = emit_text(&make_bridge_shift_module(ShiftKind::AShr));
    assert!(bytes_value_equals(&code, base, -8, 1, -4), "-8 >> 1 == -4 (arithmetic)");
    assert!(bytes_value_equals(&code, base, -1, 5, -1), "-1 >> 5 == -1 (sign fills)");
    assert!(bytes_value_equals(&code, base, 16, 2, 4), "16 >> 2 == 4");

    // LOGICAL RIGHT SHIFT (unsigned): zero fills.
    let (code, base) = emit_text(&make_bridge_shift_module(ShiftKind::LShr));
    assert!(bytes_value_equals(&code, base, 8, 1, 4), "8u32 >> 1 == 4 (logical)");
    // -1 as u32 == 0xFFFF_FFFF; >> 1 logical == 0x7FFF_FFFF == i32::MAX.
    assert!(bytes_value_equals(&code, base, -1, 1, i32::MAX), "0xFFFFFFFF >> 1 == 0x7FFFFFFF (zero fills)");
}

// ===========================================================================
// TEST 3 — PROVEN OUTPUT (HALF-SYMBOLIC, INFINITE DOMAIN): on the no-trap path
// the emitted bytes compute `a <shift> c` for ALL 2^32 values of the symbolic
// shifted value `a`, for a REPRESENTATIVE SET of fixed amounts `c` {0,1,7,31}.
// UNSAT of the negation.
// ===========================================================================

fn run_proven_output(kind: ShiftKind, cs: &[u32]) {
    let module = make_bridge_shift_module(kind);
    let (code, base) = emit_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty");

    for &c in cs {
        let (machine_out, precondition) = symbolic_machine_output_amt_const(&code, base, c)
            .unwrap_or_else(|e| panic!("path-merge failed for c={c}: {e:?}"));

        // The no-trap path must be GUARDED: a vacuously-true precondition would
        // mean the shift-in-range guard was never explored. The trap arm is
        // reachable only symbolically (`b`'s in-range check), so the executor
        // records the live-arm path condition.
        assert!(
            !matches!(precondition, Formula::Bool(true)),
            "expected a non-trivial no-trap precondition for c={c}; got `true` \
             (guard not explored — shift could mask differently than source traps)"
        );

        let spec = shift_by_const_spec(kind, c);
        let proven = discharge_equal_under(&precondition, &machine_out, &spec);
        assert!(
            proven,
            "PROVEN-OUTPUT FAILED for {kind:?} c={c}: ay did not prove the emitted bytes \
             equal a <shift> {c} on the no-trap path for all a.\n  machine_out = \
             {machine_out:?}\n  pre = {precondition:?}"
        );
    }
}

// Representative shift amounts spanning zero, one, an odd mid magnitude, and the
// max in-range amount for a 32-bit value.
const AMOUNTS: &[u32] = &[0, 1, 7, 31];

#[test]
fn left_shift_bytes_compute_a_shl_c_on_no_trap_path() {
    run_proven_output(ShiftKind::Shl, AMOUNTS);
}

#[test]
fn arithmetic_right_shift_bytes_compute_a_ashr_c_on_no_trap_path() {
    run_proven_output(ShiftKind::AShr, AMOUNTS);
}

#[test]
fn logical_right_shift_bytes_compute_a_lshr_c_on_no_trap_path() {
    run_proven_output(ShiftKind::LShr, AMOUNTS);
}

// ===========================================================================
// TEST 4 — MANDATORY NEGATIVE CONTROL: the SAME bytes proven against
// `(a <shift> c) + 1` (under the same precondition) MUST be SAT — a non-SAT
// result would make the positive certificate vacuous.
// ===========================================================================

fn run_negative_control(kind: ShiftKind, cs: &[u32]) {
    let module = make_bridge_shift_module(kind);
    let (code, base) = emit_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty");

    for &c in cs {
        let (machine_out, precondition) = symbolic_machine_output_amt_const(&code, base, c)
            .unwrap_or_else(|e| panic!("path-merge failed for c={c}: {e:?}"));
        let wrong = shift_by_const_plus_one_spec(kind, c);
        let proven = discharge_equal_under(&precondition, &machine_out, &wrong);
        assert!(
            !proven,
            "VACUITY CHECK FAILED for {kind:?} c={c}: the shift bytes were 'proven' equal to \
             (a <shift> {c})+1; the discharge has no teeth.\n  machine_out = {machine_out:?}"
        );
    }
}

#[test]
fn negative_control_left_shift_vs_plus_one_is_sat() {
    run_negative_control(ShiftKind::Shl, AMOUNTS);
}

#[test]
fn negative_control_arithmetic_right_shift_vs_plus_one_is_sat() {
    run_negative_control(ShiftKind::AShr, AMOUNTS);
}

#[test]
fn negative_control_logical_right_shift_vs_plus_one_is_sat() {
    run_negative_control(ShiftKind::LShr, AMOUNTS);
}
