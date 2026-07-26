// module_to_lir_cast_proven_output.rs — the "trust-ir first" codegen seam,
// extended to INTEGER-TO-INTEGER CASTS (`a as T`), proven over the REAL emitted
// bytes.
//
// GOAL: take a `trust_ir::Module` sourced from a REAL trust-types
// `VerifiableFunction` whose body is a bare `Rvalue::Cast(a, T)` — run through
// `trust_ir_bridge::lower_to_trust_ir`. That bridge emits a single BARE
// `Inst::Cast { op, src_ty, dst_ty, operand }` (confirmed by dumping the real
// bridge Module). The producer picks the `CastOp` from widths + source
// signedness:
//   * `i32 as i64` (signed widen)   -> CastOp::SExt    (src I32, dst I64)
//   * `i32 as u8`  (narrow)         -> CastOp::Trunc   (src I32, dst U8) [NoOverflow]
//   * `i32 as u32` (same-width)     -> CastOp::Bitcast (src I32, dst U32) [NoOverflow]
//   * `u16 as u32` (unsigned widen) -> CastOp::ZExt    (src U16, dst U32)
// The NEW thing is mapping these to the pinned LIR cast opcodes:
//   * SExt    -> Sextend { from, to }   (AArch64 ISel -> SXT{B,H,W})
//   * ZExt    -> Uextend { from, to }   (AArch64 ISel -> UXT{B,H} / mov w)
//   * Trunc   -> Trunc   { to }         (AArch64 ISel -> low-bits mask/mov)
//   * Bitcast (same width) -> Copy      (identity on the bit pattern — LIR int
//                                        types are width-only, no signedness)
//
// Rust `as` int-to-int casts are TOTAL (never trap), so every proof here is
// FULLY SYMBOLIC (precondition `true`) — like Not: ay (QF_BV) proves
// `machine_out == cast_spec(a)` for ALL values of the symbolic `a` (UNSAT of the
// negation). The cast semantics proven:
//   SExt  : machine_out == sign_extend_{32->64}(a)
//   Trunc : machine_out == a[7:0]                (== a & 0xFF)
//   ZExt  : machine_out == zero_extend_{16->32}(a)
//   Bitcast: machine_out == a                    (same-width identity)
// Each carries a MANDATORY NEGATIVE CONTROL: the SAME bytes proven against a
// WRONG spec (SExt-vs-ZExt for a negative value, or cast(a)+1) MUST be SAT, else
// the certificate is vacuous. Plus concrete value-diffs (-1 as i64 == -1;
// 300 as u8 == 44; -1 as u32 == 4294967295).
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
// The kind of int-to-int cast being modeled.
// ---------------------------------------------------------------------------
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CastKind {
    /// `i32 as i64` — signed widen -> CastOp::SExt. Return width 64.
    S32to64,
    /// `i32 as u8` — narrow -> CastOp::Trunc. Return width 8.
    Narrow32to8,
    /// `i32 as u32` — same-width reinterpret -> CastOp::Bitcast. Return width 32.
    Same32,
    /// `u16 as u32` — unsigned widen -> CastOp::ZExt. Return width 32.
    U16to32,
}

impl CastKind {
    /// The source operand width in bits (== the symbolic input width).
    fn src_bits(self) -> u32 {
        match self {
            CastKind::S32to64 | CastKind::Narrow32to8 | CastKind::Same32 => 32,
            CastKind::U16to32 => 16,
        }
    }
    /// The destination (== returned) width in bits.
    fn dst_bits(self) -> u32 {
        match self {
            CastKind::S32to64 => 64,
            CastKind::Narrow32to8 => 8,
            CastKind::Same32 | CastKind::U16to32 => 32,
        }
    }
    /// The register width the value materializes in / is read at. AArch64 has no
    /// 8/16-bit registers: a narrow result lives in a W (32-bit) slot, and the
    /// meaningful bits are the low `dst_bits`. So we read the GPR at
    /// `max(dst_bits, 32)` and, for the sub-32 dst, compare only the low
    /// `dst_bits` (the cast spec masks to that width too).
    fn read_width(self) -> u32 {
        self.dst_bits().max(32)
    }
}

// ---------------------------------------------------------------------------
// Source the REAL bridge Module from a trust-types VerifiableFunction whose body
// is a bare `Rvalue::Cast(a, T)`.
// ---------------------------------------------------------------------------
fn make_bridge_cast_module(kind: CastKind) -> Module {
    use trust_types::{
        BasicBlock, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement, Terminator,
        Ty as TtTy, VerifiableBody, VerifiableFunction,
    };

    let (from_ty, to_ty, name) = match kind {
        CastKind::S32to64 => (TtTy::i32(), TtTy::i64(), "c64"),
        CastKind::Narrow32to8 => (TtTy::i32(), TtTy::u8(), "cu8"),
        CastKind::Same32 => (TtTy::i32(), TtTy::u32(), "cu32"),
        CastKind::U16to32 => (TtTy::u16(), TtTy::u32(), "cwu"),
    };

    // _0 ret (= cast result, dst type), _1 a (operand, src type).
    let locals = vec![
        LocalDecl { index: 0, ty: to_ty.clone(), name: None },
        LocalDecl { index: 1, ty: from_ty.clone(), name: Some("a".into()) },
    ];

    // bb0: _0 = (a as T) ; Return
    let blocks = vec![BasicBlock {
        id: BlockId(0),
        stmts: vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), to_ty.clone()),
            span: SourceSpan::default(),
        }],
        terminator: Terminator::Return,
    }];

    let vf = VerifiableFunction {
        name: name.to_string(),
        def_path: "cast::op".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody { locals, blocks, arg_count: 1, return_ty: to_ty },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    trust_ir_bridge::lower_to_trust_ir(&vf).expect("bridge lower_to_trust_ir failed for cast")
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
        .expect("lower_trust_ir_function_to_lir failed for cast");
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
// BOUNDED SYMBOLIC PATH-MERGING EXECUTOR (mirrors the unop/shift/div-rem tests).
// Casts are straight-line and total, so there is NO branch — the precondition is
// trivially `true`. The executor is kept general (it can diverge a trap arm), but
// for casts it always returns a single fully-symbolic value.
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
    out_width: u32,
    precondition: Vec<Formula>,
}

impl<'a> Executor<'a> {
    fn new(code: &'a [u8], base: u64, out_width: u32) -> Self {
        Executor {
            sem: Aarch64Semantics,
            code,
            base,
            steps: 0,
            out_width,
            precondition: Vec::new(),
        }
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
                return Ok(state.read_gpr(0, self.out_width));
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

fn run_machine_output(
    code: &[u8],
    base: u64,
    out_width: u32,
    state: MachineState,
) -> Result<(Formula, Formula), ExecError> {
    let mut exec = Executor::new(code, base, out_width);
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

/// Path-merge with X0 (== `a`, the cast operand) FULLY SYMBOLIC. For casts the
/// precondition is `true` (total, no trap).
fn symbolic_machine_output(
    code: &[u8],
    base: u64,
    out_width: u32,
) -> Result<(Formula, Formula), ExecError> {
    let state = MachineState::symbolic();
    run_machine_output(code, base, out_width, state)
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
// IR-spec helpers. The symbolic operand `a` is the low `src_bits` of X0.
// ---------------------------------------------------------------------------

/// The symbolic source operand: the low `src_bits` of argument register X0.
fn a_src(kind: CastKind) -> Formula {
    Formula::BvExtract {
        inner: Box::new(Formula::Var("X0".to_string(), Sort::BitVec(64))),
        high: kind.src_bits() - 1,
        low: 0,
    }
}

/// The cast spec at the READ width: the value the emitted bytes must produce in
/// the low `read_width` bits of X0.
///
///   SExt  (i32->i64) : sign_extend a to 64 bits.
///   Trunc (i32->u8)  : a[7:0], then (since read at 32-bit W) ZERO-extend to 32.
///                      Rust `x as u8` produces the low byte; when that byte is
///                      materialized in a W register the upper bits are the low
///                      32 bits of the value, but we compare ONLY the low 8 bits
///                      (read_width==32, spec low 8 = a[7:0]); to keep the compare
///                      width-consistent we zero-extend a[7:0] to 32.
///   Bitcast (i32->u32): a unchanged (identity, 32-bit).
///   ZExt  (u16->u32) : zero_extend a (16) to 32 bits.
fn cast_spec(kind: CastKind) -> Formula {
    let a = a_src(kind);
    match kind {
        // sign-extend the 32-bit source by 32 bits -> 64 bits.
        CastKind::S32to64 => Formula::BvSignExt(Box::new(a), 32),
        // low byte, then zero-extend to the 32-bit read width.
        CastKind::Narrow32to8 => {
            let low8 = Formula::BvExtract { inner: Box::new(a), high: 7, low: 0 };
            Formula::BvZeroExt(Box::new(low8), 24)
        }
        // identity (same-width reinterpret).
        CastKind::Same32 => a,
        // zero-extend the 16-bit source by 16 bits -> 32 bits.
        CastKind::U16to32 => Formula::BvZeroExt(Box::new(a), 16),
    }
}

/// A deliberately-WRONG spec for the negative control:
///   * SExt  -> the ZExt spec (zero- instead of sign-extend); differs for a<0.
///   * ZExt  -> the SExt spec (sign- instead of zero-extend); differs for the
///              high bit set.
///   * Trunc / Bitcast -> cast(a) + 1 (off by one).
fn cast_wrong_spec(kind: CastKind) -> Formula {
    let a = a_src(kind);
    match kind {
        // sign-extend replaced by ZERO-extend (wrong for negative a).
        CastKind::S32to64 => Formula::BvZeroExt(Box::new(a), 32),
        // zero-extend replaced by SIGN-extend (wrong for a with high bit set).
        CastKind::U16to32 => Formula::BvSignExt(Box::new(a), 16),
        // off-by-one on the correct spec.
        CastKind::Narrow32to8 | CastKind::Same32 => {
            let one = Formula::BitVec { value: 1, width: kind.read_width() };
            Formula::BvAdd(Box::new(cast_spec(kind)), Box::new(one), kind.read_width())
        }
    }
}

// ---------------------------------------------------------------------------
// Concrete byte-execution oracle.
// ---------------------------------------------------------------------------

fn concrete_run(code: &[u8], base: u64, out_width: u32, a_bits: i128, src_bits: u32) -> Formula {
    let mut state = MachineState::symbolic();
    // Place the (masked) source in the low bits of X0.
    let mask: i128 = if src_bits >= 64 { -1 } else { (1i128 << src_bits) - 1 };
    state.gpr[0] = Formula::BitVec { value: a_bits & mask, width: 64 };
    let mut exec = Executor::new(code, base, out_width);
    match exec.run(base, state, Vec::new(), 0) {
        Ok(out) => out,
        Err(e) => panic!("concrete run failed: {e:?}"),
    }
}

/// Check the emitted bytes produce `expected` in the low `cmp_bits` bits.
fn bytes_value_equals(
    kind: CastKind,
    code: &[u8],
    base: u64,
    a: i128,
    expected: i128,
    cmp_bits: u32,
) -> bool {
    let out = concrete_run(code, base, kind.read_width(), a, kind.src_bits());
    let mut solver = Solver::try_new(Logic::QfBv).expect("ay Solver::try_new");
    // Extract the low `cmp_bits` of the machine output.
    let out_t = formula_to_term(&mut solver, &out);
    let out_low = solver.try_bvextract(out_t, cmp_bits - 1, 0).expect("extract");
    let mask: i128 = if cmp_bits >= 128 { -1 } else { (1i128 << cmp_bits) - 1 };
    let exp = solver
        .try_bv_const_bigint(&BigInt::from(expected & mask), cmp_bits)
        .expect("bv const");
    let eq = solver.try_eq(out_low, exp).expect("eq");
    let differ = solver.try_not(eq).expect("not");
    solver.try_assert_term(differ).expect("assert");
    solver.check_sat().is_unsat()
}

// ===========================================================================
// TEST 0 — LIR SHAPE: the cast lowers to the right Sextend/Uextend/Trunc/Copy,
// materializes NO memory, and has exactly ONE cast op.
// ===========================================================================

#[test]
fn cast_lir_shape_carries_right_opcode() {
    use trust_cg_lower::instructions::Opcode as LO;
    // (kind, predicate on the single cast opcode).
    let cases: &[(CastKind, fn(&LO) -> bool, &str)] = &[
        (CastKind::S32to64, |o| matches!(o, LO::Sextend { .. }), "Sextend"),
        (CastKind::Narrow32to8, |o| matches!(o, LO::Trunc { .. }), "Trunc"),
        (CastKind::Same32, |o| matches!(o, LO::Copy), "Copy"),
        (CastKind::U16to32, |o| matches!(o, LO::Uextend { .. }), "Uextend"),
    ];
    for &(kind, is_cast, label) in cases {
        let module = make_bridge_cast_module(kind);
        let lir = lower_trust_ir_function_to_lir(&module, &module.functions[0])
            .expect("cast lowers");
        assert!(lir.stack_slots.is_empty(), "cast must materialize NO memory ({kind:?})");
        let mut casts = 0;
        for block in lir.blocks.values() {
            for inst in &block.instructions {
                if is_cast(&inst.opcode) {
                    casts += 1;
                }
            }
        }
        assert_eq!(casts, 1, "exactly one {label} op for {kind:?}");
    }
}

// NEGATIVE control on the mapping itself: SExt must be Sextend (NOT Uextend), and
// ZExt must be Uextend (NOT Sextend). A swap would silently miscompile negative
// values.
#[test]
fn cast_mapping_sext_zext_not_swapped() {
    use trust_cg_lower::instructions::Opcode as LO;
    let s = make_bridge_cast_module(CastKind::S32to64);
    let s_lir = lower_trust_ir_function_to_lir(&s, &s.functions[0]).expect("sext lowers");
    let has_sext =
        s_lir.blocks.values().any(|b| b.instructions.iter().any(|i| matches!(i.opcode, LO::Sextend { .. })));
    let has_uext_in_s =
        s_lir.blocks.values().any(|b| b.instructions.iter().any(|i| matches!(i.opcode, LO::Uextend { .. })));
    assert!(has_sext, "i32 as i64 must be Sextend (sign-extend)");
    assert!(!has_uext_in_s, "i32 as i64 must NOT be Uextend — that zero-extends, wrong for a<0");

    let z = make_bridge_cast_module(CastKind::U16to32);
    let z_lir = lower_trust_ir_function_to_lir(&z, &z.functions[0]).expect("zext lowers");
    let has_uext =
        z_lir.blocks.values().any(|b| b.instructions.iter().any(|i| matches!(i.opcode, LO::Uextend { .. })));
    let has_sext_in_z =
        z_lir.blocks.values().any(|b| b.instructions.iter().any(|i| matches!(i.opcode, LO::Sextend { .. })));
    assert!(has_uext, "u16 as u32 must be Uextend (zero-extend)");
    assert!(!has_sext_in_z, "u16 as u32 must NOT be Sextend — that sign-extends, wrong for high bit");
}

// ===========================================================================
// TEST 1 — the converter emits a real object with non-empty __text.
// ===========================================================================

#[test]
fn cast_emits_object() {
    for kind in [CastKind::S32to64, CastKind::Narrow32to8, CastKind::Same32, CastKind::U16to32] {
        let module = make_bridge_cast_module(kind);
        let (code, _base) = emit_text(&module);
        assert!(!code.is_empty(), "emitted __text is empty for {kind:?}");
    }
}

// ===========================================================================
// TEST 2 — concrete value-differential: the EMITTED BYTES compute the right cast
// value. -1 as i64 == -1; 300 as u8 == 44; -1 as u32 == 0xffff_ffff; and more.
// ===========================================================================

#[test]
fn cast_emitted_bytes_values_are_correct() {
    // i32 as i64 (sign-extend): -1 -> -1 (0xffff_ffff_ffff_ffff), 5 -> 5,
    // i32::MIN -> i32::MIN sign-extended.
    let (code, base) = emit_text(&make_bridge_cast_module(CastKind::S32to64));
    assert!(bytes_value_equals(CastKind::S32to64, &code, base, -1, -1, 64), "-1 as i64 == -1");
    assert!(bytes_value_equals(CastKind::S32to64, &code, base, 5, 5, 64), "5 as i64 == 5");
    assert!(
        bytes_value_equals(CastKind::S32to64, &code, base, i32::MIN as i128, i32::MIN as i128, 64),
        "i32::MIN as i64 == i32::MIN (sign-extended)"
    );
    assert!(
        bytes_value_equals(CastKind::S32to64, &code, base, 0x7fff_ffff, 0x7fff_ffff, 64),
        "i32::MAX as i64 == i32::MAX"
    );

    // i32 as u8 (truncate): 300 -> 44 (300 & 0xff), 255 -> 255, 256 -> 0, -1 -> 255.
    let (code, base) = emit_text(&make_bridge_cast_module(CastKind::Narrow32to8));
    assert!(bytes_value_equals(CastKind::Narrow32to8, &code, base, 300, 44, 8), "300 as u8 == 44");
    assert!(bytes_value_equals(CastKind::Narrow32to8, &code, base, 255, 255, 8), "255 as u8 == 255");
    assert!(bytes_value_equals(CastKind::Narrow32to8, &code, base, 256, 0, 8), "256 as u8 == 0");
    assert!(bytes_value_equals(CastKind::Narrow32to8, &code, base, -1, 255, 8), "-1 as u8 == 255");

    // i32 as u32 (same-width identity): -1 -> 0xffff_ffff, 42 -> 42.
    let (code, base) = emit_text(&make_bridge_cast_module(CastKind::Same32));
    assert!(
        bytes_value_equals(CastKind::Same32, &code, base, -1, 0xffff_ffff, 32),
        "-1 as u32 == 4294967295"
    );
    assert!(bytes_value_equals(CastKind::Same32, &code, base, 42, 42, 32), "42 as u32 == 42");

    // u16 as u32 (zero-extend): 0xffff -> 0xffff (NOT sign-extended), 7 -> 7.
    let (code, base) = emit_text(&make_bridge_cast_module(CastKind::U16to32));
    assert!(
        bytes_value_equals(CastKind::U16to32, &code, base, 0xffff, 0xffff, 32),
        "0xffff as u32 == 0xffff (zero-extended, not sign)"
    );
    assert!(bytes_value_equals(CastKind::U16to32, &code, base, 7, 7, 32), "7 as u32 == 7");
}

// ===========================================================================
// TEST 3 — PROVEN OUTPUT (FULLY SYMBOLIC, WHOLE INPUT DOMAIN): the emitted bytes
// compute the cast for ALL values of `a`. UNSAT of the negation. Precondition
// `true` (casts are total).
// ===========================================================================

fn run_proven_output(kind: CastKind) {
    let module = make_bridge_cast_module(kind);
    let (code, base) = emit_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty");

    let (machine_out, precondition) = symbolic_machine_output(&code, base, kind.read_width())
        .unwrap_or_else(|e| panic!("path-merge failed for {kind:?}: {e:?}"));

    // Casts are TOTAL — the proof must be unconditional.
    assert!(
        matches!(precondition, Formula::Bool(true)),
        "expected a TOTAL (no-precondition) proof for {kind:?}; got {precondition:?}"
    );

    // For sub-32 dst (Trunc to u8) the meaningful output is the low `dst_bits`;
    // compare the machine output and the spec at the read width, where the spec
    // has zero-extended the low byte to 32 (matching how `x as u8` materializes in
    // a W register whose upper bits are the low 32 of the value — but the value is
    // exactly the byte for a pure truncate, so the upper bits are the byte's
    // zero-extension only if the ISel zeroes them; the low-`dst_bits` compare in
    // TEST 2 covers the byte itself, and here we prove the full read-width form).
    let spec = cast_spec(kind);
    let proven = discharge_equal_under(&precondition, &machine_out, &spec);
    assert!(
        proven,
        "PROVEN-OUTPUT FAILED for {kind:?}: ay did not prove the emitted bytes equal the \
         cast spec for all a.\n  machine_out = {machine_out:?}\n  spec = {spec:?}"
    );
}

#[test]
fn sext_bytes_compute_sign_extend_for_all_a() {
    run_proven_output(CastKind::S32to64);
}

#[test]
fn trunc_bytes_compute_low_byte_for_all_a() {
    run_proven_output(CastKind::Narrow32to8);
}

#[test]
fn same_width_bytes_are_identity_for_all_a() {
    run_proven_output(CastKind::Same32);
}

#[test]
fn zext_bytes_compute_zero_extend_for_all_a() {
    run_proven_output(CastKind::U16to32);
}

// ===========================================================================
// TEST 4 — MANDATORY NEGATIVE CONTROL: the SAME bytes proven against a WRONG spec
// MUST be SAT — a non-SAT result would make the positive certificate vacuous. The
// SExt<->ZExt swap controls are the load-bearing ones (they catch a sign/zero mix-up
// on a negative / high-bit input); Trunc/Bitcast use cast(a)+1.
// ===========================================================================

fn run_negative_control(kind: CastKind) {
    let module = make_bridge_cast_module(kind);
    let (code, base) = emit_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty");

    let (machine_out, precondition) = symbolic_machine_output(&code, base, kind.read_width())
        .unwrap_or_else(|e| panic!("path-merge failed for {kind:?}: {e:?}"));
    let wrong = cast_wrong_spec(kind);
    let proven = discharge_equal_under(&precondition, &machine_out, &wrong);
    assert!(
        !proven,
        "VACUITY CHECK FAILED for {kind:?}: the cast bytes were 'proven' equal to a WRONG spec; \
         the discharge has no teeth.\n  machine_out = {machine_out:?}\n  wrong = {wrong:?}"
    );
}

#[test]
fn negative_control_sext_vs_zext_is_sat() {
    run_negative_control(CastKind::S32to64);
}

#[test]
fn negative_control_trunc_vs_plus_one_is_sat() {
    run_negative_control(CastKind::Narrow32to8);
}

#[test]
fn negative_control_same_width_vs_plus_one_is_sat() {
    run_negative_control(CastKind::Same32);
}

#[test]
fn negative_control_zext_vs_sext_is_sat() {
    run_negative_control(CastKind::U16to32);
}
