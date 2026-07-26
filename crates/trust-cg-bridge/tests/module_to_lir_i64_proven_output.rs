// module_to_lir_i64_proven_output.rs — the "trust-ir first" codegen seam at the
// 64-bit WIDTH (i64 / u64), proven over the REAL emitted bytes.
//
// This is the 64-bit companion to the i32/u32 proven-output slices
// (`module_to_lir_overflow_proven_output.rs`, `..._checked_mul_...`,
// `..._divrem_...`, `..._shift_...`). It confirms that i64/u64 arithmetic
// converts AND proves through the ALREADY-EXISTING converter paths — with ZERO
// converter change:
//
//   * `map_scalar_int_ty`  maps `Ty::I64 | Ty::U64 -> LirType::I64` (width-native).
//   * `map_int_binop`       is width-agnostic (Iadd/Isub/Band/Bor/Bxor/S,Udiv/
//                           S,Urem/Ishl/Ushr/Sshr) — the ONLY width fail-close is
//                           i128 (div/rem libcall, shift multi-register). i64 is IN.
//   * `map_overflow_op`     routes i64 checked Mul to the FIRST-CLASS I64-native
//                           `CheckedSmul`/`CheckedUmul` (SMULH/UMULH high-half
//                           idiom) — NOT the i32 widening slice (that slice is
//                           intercepted only when `value_lir_ty == I32`). i64 add/
//                           sub route to `CheckedSadd`/`CheckedUadd`/`CheckedSsub`/
//                           `CheckedUsub` exactly as at i32, just at I64 operands.
//
// So at 64-bit the ONLY structural difference from the i32 slices is the WIDTH:
// the return value is a full 64-bit X-register (`read_gpr(0, 64)`), the operand
// registers are full X-registers (no W-extract), and the proof spec is 64-bit.
// checked-mul at i64 uses the FIRST-CLASS `CheckedSmul` (no widening), which is
// the headline "already-first-class" path this harness pins.
//
// HONEST BOUNDED FRAMING (mirrors the i32 slices' 32x32 multiplier/divider
// hardness). Over the REAL bridge Modules we prove `no-trap-precond =>
// bytes == a OP c` over the 64-bit domain:
//   * ADD / SUB: FULLY symbolic — both a and b range over all 2^64 values (a
//     64-bit adder/subtractor equivalence is trivial for QF_BV, no multiplier).
//   * MUL / DIV / SHIFT: pin ONE operand to representative i64 literals (turning
//     the emitted 64-bit MUL / SDIV / LSLV into a by-constant op ay closes),
//     still an infinite-domain statement over ALL 2^64 values of the other
//     operand — the SAME honest framing the i32 32x32 slices use for the
//     multiplier/divider QF_BV wall.
// Each proof is UNSAT of the negation, paired with a MANDATORY SAT negative
// control (`+ 1` spec) so no certificate is vacuous, plus concrete value diffs
// (i64: 3_000_000_000 + 1; a large mul; -7 / 2 = -3).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![cfg(feature = "ay-proofs")]

use ay::{BigInt, Logic, Solver, Term};
use trust_cg_bridge::codegen_backend::{TrustCgCodegenBackend, TrustCgTargetArch};
use trust_cg_bridge::lower_trust_ir_function_to_lir;
use trust_disasm::{Opcode, decode_aarch64};
use trust_machine_sem::{Aarch64Semantics, Effect, MachineState, Semantics, condition_to_formula};
use trust_types::{Formula, Sort};

use trust_ir::Module;

// ---------------------------------------------------------------------------
// Which 64-bit shape to build. Each is sourced from a REAL trust-types
// `VerifiableFunction` at i64/u64, run through `trust_ir_bridge::lower_to_trust_ir`.
// ---------------------------------------------------------------------------
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Shape {
    /// bare `a + b` (i64).                     -> LIR Iadd
    Add,
    /// checked `a - b` (i64), tuple idiom.     -> LIR CheckedSsub (+ overflow guard)
    CheckedSub,
    /// checked `a * b` (i64), tuple idiom.     -> LIR CheckedSmul (FIRST-CLASS, no widening)
    CheckedMul,
    /// signed `a / b` (i64), guarded.          -> LIR Sdiv (+ div-by-zero + overflow guards)
    SignedDiv,
    /// `a << b` (i64), guarded.                -> LIR Ishl (+ shift-in-range guard)
    Shl,
}

// ---------------------------------------------------------------------------
// Bridge Module builders (trust-types VerifiableFunction -> trust_ir Module).
// ---------------------------------------------------------------------------

fn make_bridge_module(shape: Shape) -> Module {
    use trust_types::{
        AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue,
        SourceSpan, Statement, Terminator, Ty as TtTy, VerifiableBody, VerifiableFunction,
    };

    let i64t = TtTy::i64;

    let (name, def_path, body) = match shape {
        // ---- bare `a + b` : _0 = a + b ; return _0. ----
        Shape::Add => {
            let locals = vec![
                LocalDecl { index: 0, ty: i64t(), name: None },
                LocalDecl { index: 1, ty: i64t(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: i64t(), name: Some("b".into()) },
            ];
            let blocks = vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }];
            (
                "add64".to_string(),
                "i64::add64".to_string(),
                VerifiableBody { locals, blocks, arg_count: 2, return_ty: i64t() },
            )
        }
        // ---- checked `a - b` / `a * b` : the MIR-faithful tuple idiom. ----
        Shape::CheckedSub | Shape::CheckedMul => {
            let op = if matches!(shape, Shape::CheckedMul) { BinOp::Mul } else { BinOp::Sub };
            let locals = vec![
                LocalDecl { index: 0, ty: i64t(), name: None },
                LocalDecl { index: 1, ty: i64t(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: i64t(), name: Some("b".into()) },
                LocalDecl {
                    index: 3,
                    ty: TtTy::Tuple(vec![i64t(), TtTy::Bool]),
                    name: Some("checked".into()),
                },
            ];
            let blocks = vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            op,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(op),
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
            ];
            let nm = if matches!(shape, Shape::CheckedMul) { "mul64" } else { "sub64" };
            (
                nm.to_string(),
                format!("i64::{nm}"),
                VerifiableBody { locals, blocks, arg_count: 2, return_ty: i64t() },
            )
        }
        // ---- signed `a / b` : div-by-zero guard, i64::MIN/-1 guard, bare sdiv. ----
        Shape::SignedDiv => {
            let locals = vec![
                LocalDecl { index: 0, ty: i64t(), name: None },
                LocalDecl { index: 1, ty: i64t(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: i64t(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: TtTy::Bool, name: None },
                LocalDecl { index: 4, ty: TtTy::Bool, name: None },
                LocalDecl { index: 5, ty: i64t(), name: None },
            ];
            let blocks = vec![
                // bb0: _3 = (b == 0); assert(!_3) -> bb1.
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Int(0)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(3)),
                        expected: false,
                        msg: AssertMessage::DivisionByZero,
                        target: BlockId(1),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                    },
                },
                // bb1: _4 = (b == -1); assert(!_4) -> bb2  (i64::MIN/-1 overflow guard).
                BasicBlock {
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
                        msg: AssertMessage::Overflow(BinOp::Div),
                        target: BlockId(2),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                    },
                },
                // bb2: _5 = a / b ; _0 = _5 ; return.
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
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
                },
            ];
            (
                "div64".to_string(),
                "i64::div64".to_string(),
                VerifiableBody { locals, blocks, arg_count: 2, return_ty: i64t() },
            )
        }
        // ---- `a << b` (i64): shift-amount-in-range guard, bare ishl. ----
        Shape::Shl => {
            // shifted value i64; amount is u32 (Rust shift-count type).
            let locals = vec![
                LocalDecl { index: 0, ty: i64t(), name: None },
                LocalDecl { index: 1, ty: i64t(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: TtTy::u32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: TtTy::Bool, name: Some("in_range".into()) },
            ];
            let blocks = vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        // _3 = (b >= 64)   (out-of-range predicate for a 64-bit value).
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Ge,
                                Operand::Copy(Place::local(2)),
                                Operand::Constant(ConstValue::Uint(64, 32)),
                            ),
                            span: SourceSpan::default(),
                        },
                        // _0 = a << b   (bare shift into the return local).
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Shl,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(3)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Shl),
                        target: BlockId(1),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ];
            (
                "shl64".to_string(),
                "i64::shl64".to_string(),
                VerifiableBody { locals, blocks, arg_count: 2, return_ty: i64t() },
            )
        }
    };

    let vf = VerifiableFunction {
        name,
        def_path,
        span: trust_types::SourceSpan::default(),
        body,
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    trust_ir_bridge::lower_to_trust_ir(&vf).expect("bridge lower_to_trust_ir failed (i64)")
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
        .expect("lower_trust_ir_function_to_lir failed (i64)");
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

/// Does the emitted __text carry a conditional branch? Every guarded shape
/// (checked add/sub/mul overflow, div-by-zero/overflow, shift-in-range) MUST
/// lower to one — a dropped guard would leave only straight-line code.
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
// BOUNDED SYMBOLIC PATH-MERGING EXECUTOR (identical to the i32 slices, but the
// Ret reads the full 64-bit X0). The trapping guard arm (a `Call` abort)
// diverges, accumulating the no-trap precondition.
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
                // 64-bit return: read the FULL X0 (this is the i64 slice).
                return Ok(state.read_gpr(0, 64));
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

/// FULLY symbolic (both operands range over all 2^64). Used for add/sub.
fn symbolic_machine_output(code: &[u8], base: u64) -> Result<(Formula, Formula), ExecError> {
    run_machine_output(code, base, MachineState::symbolic())
}

/// Path-merge with the SECOND argument register (X1 == `b`) pinned to a concrete
/// 64-bit literal `c`. X0 (== `a`) stays FULLY SYMBOLIC, so the result is an
/// infinite-domain statement over ALL 2^64 values of `a` for that fixed `c`.
/// Pinning turns the emitted 64-bit MUL / SDIV / LSLV into a by-constant op that
/// ay closes — still proving the REAL emitted 64-bit bytes over a full operand.
fn symbolic_machine_output_b_const(
    code: &[u8],
    base: u64,
    c: i64,
) -> Result<(Formula, Formula), ExecError> {
    let mut state = MachineState::symbolic();
    state.gpr[1] = Formula::BitVec { value: i128::from(c), width: 64 };
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
// Formula -> ay::Term translation (QF_BV / QF_ABV).
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

// ---------------------------------------------------------------------------
// SOUND constant-folder (identical to the i32 checked-mul slice, but 64-bit).
// The bounded executor wraps the pinned constant operand in
// BvExtract/BvZeroExt/BvSignExt/BvOr(0,.) bookkeeping, so ay does NOT recognize
// the multiply/divide as a by-LITERAL op and bit-blasts a full 64-bit
// multiplier/divider (which does not converge). This pass evaluates every
// FULLY-CONSTANT subterm to its literal `BitVec`, collapsing those layers.
// SOUNDNESS: a meaning-preserving rewrite that never touches a subterm
// containing a free variable, so the symbolic operand and the proof over ALL
// its values are unchanged; a wrong fold would surface as SAT on the positive
// proof (it does not) and the mandatory negative control stays SAT.
// ---------------------------------------------------------------------------

fn mask_to_width(v: i128, width: u32) -> i128 {
    if width >= 128 {
        v
    } else {
        let m: i128 = (1i128 << width) - 1;
        v & m
    }
}

fn as_signed(v: i128, width: u32) -> i128 {
    let v = mask_to_width(v, width);
    if width < 128 && (v & (1i128 << (width - 1))) != 0 {
        v - (1i128 << width)
    } else {
        v
    }
}

fn fold_consts(f: &Formula) -> Formula {
    match f {
        Formula::BitVec { .. } | Formula::Bool(_) | Formula::Var(..) => f.clone(),
        Formula::BvExtract { inner, high, low } => {
            let inner = fold_consts(inner);
            if let Formula::BitVec { value, width } = &inner {
                let bits = mask_to_width(*value, *width) as u128;
                let shifted = bits >> *low;
                let w = *high - *low + 1;
                let val = mask_to_width(shifted as i128, w);
                Formula::BitVec { value: val, width: w }
            } else {
                Formula::BvExtract { inner: Box::new(inner), high: *high, low: *low }
            }
        }
        Formula::BvZeroExt(a, bits) => {
            let a = fold_consts(a);
            if let Formula::BitVec { value, width } = &a {
                Formula::BitVec { value: mask_to_width(*value, *width), width: *width + *bits }
            } else {
                Formula::BvZeroExt(Box::new(a), *bits)
            }
        }
        Formula::BvSignExt(a, bits) => {
            let a = fold_consts(a);
            if let Formula::BitVec { value, width } = &a {
                let s = as_signed(*value, *width);
                Formula::BitVec { value: mask_to_width(s, *width + *bits), width: *width + *bits }
            } else {
                Formula::BvSignExt(Box::new(a), *bits)
            }
        }
        Formula::BvOr(a, b, w) => fold_bin(a, b, *w, |x, y| x | y, |a, b, w| Formula::BvOr(a, b, w)),
        Formula::BvAnd(a, b, w) => {
            fold_bin(a, b, *w, |x, y| x & y, |a, b, w| Formula::BvAnd(a, b, w))
        }
        Formula::BvXor(a, b, w) => {
            fold_bin(a, b, *w, |x, y| x ^ y, |a, b, w| Formula::BvXor(a, b, w))
        }
        Formula::BvAdd(a, b, w) => {
            fold_bin(a, b, *w, |x, y| x.wrapping_add(y), |a, b, w| Formula::BvAdd(a, b, w))
        }
        Formula::BvSub(a, b, w) => {
            fold_bin(a, b, *w, |x, y| x.wrapping_sub(y), |a, b, w| Formula::BvSub(a, b, w))
        }
        Formula::BvMul(a, b, w) => {
            fold_bin(a, b, *w, |x, y| x.wrapping_mul(y), |a, b, w| Formula::BvMul(a, b, w))
        }
        Formula::BvNot(a, w) => {
            let a = fold_consts(a);
            if let Formula::BitVec { value, width } = &a {
                Formula::BitVec { value: mask_to_width(!*value, *width), width: *width }
            } else {
                Formula::BvNot(Box::new(a), *w)
            }
        }
        Formula::Not(a) => Formula::Not(Box::new(fold_consts(a))),
        Formula::Eq(a, b) => Formula::Eq(Box::new(fold_consts(a)), Box::new(fold_consts(b))),
        Formula::And(ts) => Formula::And(ts.iter().map(fold_consts).collect()),
        Formula::Or(ts) => Formula::Or(ts.iter().map(fold_consts).collect()),
        Formula::Ite(c, t, e) => Formula::Ite(
            Box::new(fold_consts(c)),
            Box::new(fold_consts(t)),
            Box::new(fold_consts(e)),
        ),
        Formula::BvULt(a, b, w) => recurse_bin(a, b, *w, |a, b, w| Formula::BvULt(a, b, w)),
        Formula::BvULe(a, b, w) => recurse_bin(a, b, *w, |a, b, w| Formula::BvULe(a, b, w)),
        Formula::BvSLt(a, b, w) => recurse_bin(a, b, *w, |a, b, w| Formula::BvSLt(a, b, w)),
        Formula::BvSLe(a, b, w) => recurse_bin(a, b, *w, |a, b, w| Formula::BvSLe(a, b, w)),
        Formula::BvShl(a, b, w) => recurse_bin(a, b, *w, |a, b, w| Formula::BvShl(a, b, w)),
        Formula::BvLShr(a, b, w) => recurse_bin(a, b, *w, |a, b, w| Formula::BvLShr(a, b, w)),
        Formula::BvAShr(a, b, w) => recurse_bin(a, b, *w, |a, b, w| Formula::BvAShr(a, b, w)),
        Formula::BvUDiv(a, b, w) => recurse_bin(a, b, *w, |a, b, w| Formula::BvUDiv(a, b, w)),
        Formula::BvSDiv(a, b, w) => recurse_bin(a, b, *w, |a, b, w| Formula::BvSDiv(a, b, w)),
        Formula::BvURem(a, b, w) => recurse_bin(a, b, *w, |a, b, w| Formula::BvURem(a, b, w)),
        Formula::BvSRem(a, b, w) => recurse_bin(a, b, *w, |a, b, w| Formula::BvSRem(a, b, w)),
        Formula::BvConcat(a, b) => {
            Formula::BvConcat(Box::new(fold_consts(a)), Box::new(fold_consts(b)))
        }
        other => other.clone(),
    }
}

fn fold_bin(
    a: &Formula,
    b: &Formula,
    w: u32,
    op: impl Fn(i128, i128) -> i128,
    rebuild: impl Fn(Box<Formula>, Box<Formula>, u32) -> Formula,
) -> Formula {
    let a = fold_consts(a);
    let b = fold_consts(b);
    if let (Formula::BitVec { value: va, .. }, Formula::BitVec { value: vb, .. }) = (&a, &b) {
        Formula::BitVec { value: mask_to_width(op(*va, *vb), w), width: w }
    } else {
        rebuild(Box::new(a), Box::new(b), w)
    }
}

fn recurse_bin(
    a: &Formula,
    b: &Formula,
    w: u32,
    rebuild: impl Fn(Box<Formula>, Box<Formula>, u32) -> Formula,
) -> Formula {
    rebuild(Box::new(fold_consts(a)), Box::new(fold_consts(b)), w)
}

/// Discharge `precondition => (machine_out == ir_out)` over ALL inputs via ay
/// (fold-consts first, then the QF_BV/QF_ABV check). UNSAT == proven-equal.
fn discharge_equal_under(
    logic: Logic,
    precondition: &Formula,
    machine_out: &Formula,
    ir_out: &Formula,
) -> bool {
    let precondition = fold_consts(precondition);
    let machine_out = fold_consts(machine_out);
    let ir_out = fold_consts(ir_out);
    let mut solver = Solver::try_new(logic).expect("ay Solver::try_new");
    let pre = formula_to_term(&mut solver, &precondition);
    let lhs = formula_to_term(&mut solver, &machine_out);
    let rhs = formula_to_term(&mut solver, &ir_out);
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
// IR-spec helpers. At 64-bit each argument register X_n IS the full operand
// (no W-extract) and the value is 64 bits wide.
// ---------------------------------------------------------------------------

fn xn(n: u32) -> Formula {
    Formula::Var(format!("X{n}"), Sort::BitVec(64))
}

fn bv64(value: i128) -> Formula {
    Formula::BitVec { value, width: 64 }
}

// ---------------------------------------------------------------------------
// Concrete byte-execution oracle (the emitted bytes are the value oracle for the
// aggregate-undef checked idiom; run with concrete registers).
// ---------------------------------------------------------------------------

enum ConcreteOutcome {
    Trapped,
    Value(Formula),
}

fn concrete_run(code: &[u8], base: u64, a: i64, b: i64) -> ConcreteOutcome {
    let mut state = MachineState::symbolic();
    state.gpr[0] = Formula::BitVec { value: i128::from(a), width: 64 };
    state.gpr[1] = Formula::BitVec { value: i128::from(b), width: 64 };
    let mut exec = Executor::new(code, base);
    match exec.run(base, state, Vec::new(), 0) {
        Ok(out) => ConcreteOutcome::Value(out),
        Err(ExecError::Trapped) => ConcreteOutcome::Trapped,
        Err(e) => panic!("concrete run failed: {e:?}"),
    }
}

fn concrete_equals(out: &Formula, expected: i64) -> bool {
    let out = fold_consts(out);
    let mut solver = Solver::try_new(Logic::QfBv).expect("ay Solver::try_new");
    let lhs = formula_to_term(&mut solver, &out);
    let rhs = formula_to_term(&mut solver, &bv64(i128::from(expected)));
    let eq = solver.try_eq(lhs, rhs).expect("eq");
    let differ = solver.try_not(eq).expect("not");
    solver.try_assert_term(differ).expect("assert");
    solver.check_sat().is_unsat()
}

fn bytes_value_equals(code: &[u8], base: u64, a: i64, b: i64, expected: i64) -> bool {
    match concrete_run(code, base, a, b) {
        ConcreteOutcome::Value(out) => concrete_equals(&out, expected),
        ConcreteOutcome::Trapped => false,
    }
}

// ===========================================================================
// STEP-1 CONFIRMATION — LIR SHAPE. Each shape lowers to the RIGHT 64-bit
// opcode(s), with I64 operand types and (for the guarded/checked shapes) a
// Brif + Trap. The headline assertion: i64 checked MUL uses the FIRST-CLASS
// I64-native `CheckedSmul` (NOT the i32 widening slice — ZERO Sextend/Trunc).
// ===========================================================================

#[test]
fn i64_add_is_bare_iadd_at_i64() {
    use trust_cg_lower::instructions::Opcode as LO;
    use trust_cg_lower::types::Type as LT;
    let module = make_bridge_module(Shape::Add);
    let lir = lower_trust_ir_function_to_lir(&module, &module.functions[0]).expect("add64 lowers");
    assert!(lir.stack_slots.is_empty(), "bare i64 add must materialize NO memory");
    let mut iadd = 0;
    for block in lir.blocks.values() {
        for inst in &block.instructions {
            if matches!(inst.opcode, LO::Iadd) {
                iadd += 1;
                // Both operands carry the I64 LIR type.
                for v in &inst.args {
                    assert_eq!(
                        lir.value_types.get(v),
                        Some(&LT::I64),
                        "i64 add operand must be typed I64 in the LIR"
                    );
                }
            }
        }
    }
    assert_eq!(iadd, 1, "exactly one Iadd for the bare i64 add");
}

#[test]
fn i64_checked_mul_uses_first_class_checked_smul_no_widening() {
    use trust_cg_lower::instructions::Opcode as LO;
    use trust_cg_lower::types::Type as LT;
    let module = make_bridge_module(Shape::CheckedMul);
    let lir = lower_trust_ir_function_to_lir(&module, &module.functions[0])
        .expect("checked i64 mul lowers");
    assert!(lir.stack_slots.is_empty(), "i64 checked mul must materialize NO memory");

    let mut checked_smul = 0;
    let mut sextend = 0;
    let mut trunc = 0;
    let mut imul = 0;
    let mut brif = 0;
    let mut trap = 0;
    for block in lir.blocks.values() {
        for inst in &block.instructions {
            match inst.opcode {
                LO::CheckedSmul => {
                    checked_smul += 1;
                    // The FIRST-CLASS checked mul carries I64 operands.
                    for v in &inst.args {
                        assert_eq!(
                            lir.value_types.get(v),
                            Some(&LT::I64),
                            "CheckedSmul operand must be typed I64"
                        );
                    }
                }
                LO::Sextend { .. } => sextend += 1,
                LO::Trunc { .. } => trunc += 1,
                LO::Imul => imul += 1,
                LO::Brif { .. } => brif += 1,
                LO::Trap => trap += 1,
                _ => {}
            }
        }
    }
    // The headline: i64 mul is FIRST-CLASS CheckedSmul, NOT the i32 widening
    // slice (which would emit 2 Sextend + 1 Imul + 1 Trunc + range Icmps).
    assert_eq!(checked_smul, 1, "i64 checked mul MUST use the first-class CheckedSmul");
    assert_eq!(sextend, 0, "i64 checked mul must NOT widen (no Sextend)");
    assert_eq!(trunc, 0, "i64 checked mul must NOT widen (no Trunc)");
    assert_eq!(imul, 0, "i64 checked mul must NOT use a plain widened Imul");
    assert_eq!(brif, 1, "one Brif (overflow assert)");
    assert_eq!(trap, 1, "one Trap (shared trap block)");
}

#[test]
fn i64_checked_sub_uses_checked_ssub_at_i64() {
    use trust_cg_lower::instructions::Opcode as LO;
    use trust_cg_lower::types::Type as LT;
    let module = make_bridge_module(Shape::CheckedSub);
    let lir = lower_trust_ir_function_to_lir(&module, &module.functions[0])
        .expect("checked i64 sub lowers");
    let mut checked_ssub = 0;
    let mut brif = 0;
    let mut trap = 0;
    for block in lir.blocks.values() {
        for inst in &block.instructions {
            match inst.opcode {
                LO::CheckedSsub => {
                    checked_ssub += 1;
                    for v in &inst.args {
                        assert_eq!(
                            lir.value_types.get(v),
                            Some(&LT::I64),
                            "CheckedSsub operand must be typed I64"
                        );
                    }
                }
                LO::Brif { .. } => brif += 1,
                LO::Trap => trap += 1,
                _ => {}
            }
        }
    }
    assert_eq!(checked_ssub, 1, "i64 checked sub MUST use the first-class CheckedSsub");
    assert_eq!(brif, 1, "one Brif (overflow assert)");
    assert_eq!(trap, 1, "one Trap");
}

#[test]
fn i64_signed_div_is_sdiv_at_i64_with_guards() {
    use trust_cg_lower::instructions::Opcode as LO;
    use trust_cg_lower::types::Type as LT;
    let module = make_bridge_module(Shape::SignedDiv);
    let lir = lower_trust_ir_function_to_lir(&module, &module.functions[0])
        .expect("i64 signed div lowers");
    assert!(lir.stack_slots.is_empty(), "i64 div must materialize NO memory");
    let mut sdiv = 0;
    let mut brif = 0;
    let mut trap = 0;
    for block in lir.blocks.values() {
        for inst in &block.instructions {
            match inst.opcode {
                LO::Sdiv => {
                    sdiv += 1;
                    for v in &inst.args {
                        assert_eq!(
                            lir.value_types.get(v),
                            Some(&LT::I64),
                            "Sdiv operand must be typed I64"
                        );
                    }
                }
                LO::Brif { .. } => brif += 1,
                LO::Trap => trap += 1,
                _ => {}
            }
        }
    }
    assert_eq!(sdiv, 1, "exactly one i64 Sdiv");
    assert_eq!(brif, 2, "two guard Brif (div-by-zero + i64::MIN/-1 overflow)");
    assert_eq!(trap, 1, "one shared Trap");
}

#[test]
fn i64_shl_is_ishl_at_i64_with_guard() {
    use trust_cg_lower::instructions::Opcode as LO;
    use trust_cg_lower::types::Type as LT;
    let module = make_bridge_module(Shape::Shl);
    let lir = lower_trust_ir_function_to_lir(&module, &module.functions[0]).expect("i64 shl lowers");
    assert!(lir.stack_slots.is_empty(), "i64 shl must materialize NO memory");
    let mut ishl = 0;
    let mut brif = 0;
    let mut trap = 0;
    for block in lir.blocks.values() {
        for inst in &block.instructions {
            match inst.opcode {
                LO::Ishl => {
                    ishl += 1;
                    // The shifted VALUE operand is I64 (arg 0); the amount is
                    // the shift count. Assert the shifted value is I64.
                    assert_eq!(
                        lir.value_types.get(&inst.args[0]),
                        Some(&LT::I64),
                        "Ishl shifted-value operand must be typed I64"
                    );
                }
                LO::Brif { .. } => brif += 1,
                LO::Trap => trap += 1,
                _ => {}
            }
        }
    }
    assert_eq!(ishl, 1, "exactly one i64 Ishl");
    assert_eq!(brif, 1, "one guard Brif (shift-in-range)");
    assert_eq!(trap, 1, "one shared Trap");
}

// ===========================================================================
// The converter emits a real object whose __text carries a conditional branch
// for each guarded shape (guard lowered, not dropped).
// ===========================================================================

#[test]
fn i64_guarded_shapes_emit_conditional_branch() {
    for shape in [Shape::CheckedSub, Shape::CheckedMul, Shape::SignedDiv, Shape::Shl] {
        let module = make_bridge_module(shape);
        let (code, base) = emit_text(&module);
        assert!(!code.is_empty(), "emitted __text is empty for {shape:?}");
        assert!(
            has_conditional_branch(&code, base),
            "expected a conditional branch (guard lowered) for {shape:?}"
        );
    }
}

// ===========================================================================
// VALUE-DIFFERENTIAL (concrete bytes) — including the requested witnesses:
// i64 3_000_000_000 + 1 (a value that OVERFLOWS i32 but is exact in i64), a
// large i64 mul, and signed -7 / 2 = -3 (trunc toward zero).
// ===========================================================================

#[test]
fn i64_add_value_diffs() {
    let (code, base) = emit_text(&make_bridge_module(Shape::Add));
    // 3_000_000_000 + 1 : exceeds i32 range, exact in i64.
    assert!(
        bytes_value_equals(&code, base, 3_000_000_000, 1, 3_000_000_001),
        "add64(3e9, 1) == 3_000_000_001 (beyond i32 range)"
    );
    assert!(bytes_value_equals(&code, base, 2, 3, 5), "add64(2,3) == 5");
    assert!(bytes_value_equals(&code, base, -1, 1, 0), "add64(-1,1) == 0");
    // Large operands within i64.
    assert!(
        bytes_value_equals(&code, base, 5_000_000_000, 6_000_000_000, 11_000_000_000),
        "add64(5e9, 6e9) == 11e9"
    );
}

#[test]
fn i64_checked_mul_value_diffs() {
    let (code, base) = emit_text(&make_bridge_module(Shape::CheckedMul));
    // A large i64 product that would overflow i32 but is exact in i64.
    assert!(
        bytes_value_equals(&code, base, 3_000_000_000, 2, 6_000_000_000),
        "mul64(3e9, 2) == 6e9 (exact in i64, overflows i32)"
    );
    assert!(bytes_value_equals(&code, base, 6, 7, 42), "mul64(6,7) == 42");
    assert!(bytes_value_equals(&code, base, -4, 5, -20), "mul64(-4,5) == -20");
    // 2^31 * 2^31 == 2^62 (exact in i64; far beyond any i32 product).
    assert!(
        bytes_value_equals(&code, base, 1 << 31, 1 << 31, 1i64 << 62),
        "mul64(2^31, 2^31) == 2^62"
    );
}

#[test]
fn i64_signed_div_value_diffs() {
    let (code, base) = emit_text(&make_bridge_module(Shape::SignedDiv));
    // The requested -7 / 2 == -3 (trunc toward zero).
    assert!(bytes_value_equals(&code, base, -7, 2, -3), "div64(-7, 2) == -3 (trunc toward 0)");
    assert!(bytes_value_equals(&code, base, 7, 2, 3), "div64(7, 2) == 3");
    assert!(bytes_value_equals(&code, base, 7, -2, -3), "div64(7, -2) == -3");
    // A large i64 dividend.
    assert!(
        bytes_value_equals(&code, base, 9_000_000_000, 3, 3_000_000_000),
        "div64(9e9, 3) == 3e9"
    );
}

#[test]
fn i64_shl_value_diffs() {
    let (code, base) = emit_text(&make_bridge_module(Shape::Shl));
    assert!(bytes_value_equals(&code, base, 1, 40, 1i64 << 40), "1 << 40 (only valid at i64)");
    assert!(bytes_value_equals(&code, base, 1, 4, 16), "1 << 4 == 16");
    assert!(bytes_value_equals(&code, base, 1, 63, i64::MIN), "1 << 63 == i64::MIN");
}

// ===========================================================================
// PROVEN OUTPUT (UNSAT) — ADD / SUB fully symbolic; MUL / DIV / SHIFT pinned.
// ===========================================================================

/// bare `a + b` (i64) — FULLY symbolic, over ALL 2^64 pairs.
fn add_spec() -> Formula {
    Formula::BvAdd(Box::new(xn(0)), Box::new(xn(1)), 64)
}
/// checked `a - b` (i64) — FULLY symbolic.
fn sub_spec() -> Formula {
    Formula::BvSub(Box::new(xn(0)), Box::new(xn(1)), 64)
}

#[test]
fn i64_add_bytes_compute_a_plus_b_for_all_inputs() {
    let (code, base) = emit_text(&make_bridge_module(Shape::Add));
    let (machine_out, precondition) =
        symbolic_machine_output(&code, base).expect("add path-merge failed");
    // Bare add: no guard, so the precondition is trivially true (allowed here —
    // there is no trap arm to explore).
    let proven = discharge_equal_under(Logic::QfBv, &precondition, &machine_out, &add_spec());
    assert!(proven, "PROVEN-OUTPUT FAILED: i64 add bytes must equal a+b for ALL 2^64 pairs");
}

#[test]
fn i64_checked_sub_bytes_compute_a_minus_b_on_no_overflow_path() {
    let (code, base) = emit_text(&make_bridge_module(Shape::CheckedSub));
    let (machine_out, precondition) =
        symbolic_machine_output(&code, base).expect("sub path-merge failed");
    // The overflow guard must be explored: a non-trivial no-overflow precondition.
    assert!(
        !matches!(precondition, Formula::Bool(true)),
        "expected a non-trivial no-overflow precondition for checked i64 sub"
    );
    let proven = discharge_equal_under(Logic::QfBv, &precondition, &machine_out, &sub_spec());
    assert!(
        proven,
        "PROVEN-OUTPUT FAILED: i64 checked-sub bytes must equal a-b on the no-overflow path.\n\
         machine_out = {machine_out:?}\n  pre = {precondition:?}"
    );
}

/// `a * c` spec for a fixed 64-bit multiplier `c` (used with X1 pinned to `c`).
fn mul_by_const_spec(c: i64) -> Formula {
    Formula::BvMul(Box::new(xn(0)), Box::new(bv64(i128::from(c))), 64)
}
/// `a / c` (signed) spec for a fixed 64-bit divisor `c`.
fn sdiv_by_const_spec(c: i64) -> Formula {
    Formula::BvSDiv(Box::new(xn(0)), Box::new(bv64(i128::from(c))), 64)
}
/// `a << c` spec for a fixed shift amount `c`.
fn shl_by_const_spec(c: i64) -> Formula {
    Formula::BvShl(Box::new(xn(0)), Box::new(bv64(i128::from(c))), 64)
}

#[test]
fn i64_checked_mul_bytes_compute_a_times_c_on_no_overflow_path() {
    let (code, base) = emit_text(&make_bridge_module(Shape::CheckedMul));
    // Representative multipliers spanning zero, units, small, large-beyond-i32,
    // and the signed extremes (each exercises the CheckedSmul overflow check).
    let cs: &[i64] = &[0, 1, -1, 7, -6, 1_000_000, 3_000_000_000, i64::MAX, i64::MIN];
    for &c in cs {
        let (machine_out, precondition) = symbolic_machine_output_b_const(&code, base, c)
            .unwrap_or_else(|e| panic!("mul path-merge failed for c={c}: {e:?}"));
        // c==0 never overflows -> the executor may not record a trap arm; every
        // other c must be guarded (non-trivial no-overflow precondition).
        if c != 0 {
            assert!(
                !matches!(precondition, Formula::Bool(true)),
                "expected a non-trivial no-overflow precondition for c={c}; got `true`"
            );
        }
        // The pinned literal wraps in bookkeeping layers ay bit-blasts as a full
        // multiplier; QF_ABV + the const-fold (in discharge) collapses it to a
        // multiply-by-constant.
        let proven =
            discharge_equal_under(Logic::QfAbv, &precondition, &machine_out, &mul_by_const_spec(c));
        assert!(
            proven,
            "PROVEN-OUTPUT FAILED for c={c}: i64 CheckedSmul bytes must equal a*{c} on the \
             no-overflow path for all a.\n  machine_out = {machine_out:?}\n  pre = {precondition:?}"
        );
    }
}

#[test]
fn i64_signed_div_bytes_compute_a_div_c_on_no_trap_path() {
    let (code, base) = emit_text(&make_bridge_module(Shape::SignedDiv));
    // NON-ZERO, NON-(-1) divisors exercising truncation toward zero both ways,
    // plus a magnitude beyond i32 range and the signed extreme.
    let cs: &[i64] = &[1, 2, 3, 7, -2, -3, 3_000_000_000, i64::MAX];
    for &c in cs {
        let (machine_out, precondition) = symbolic_machine_output_b_const(&code, base, c)
            .unwrap_or_else(|e| panic!("div path-merge failed for c={c}: {e:?}"));
        assert!(
            !matches!(precondition, Formula::Bool(true)),
            "expected a non-trivial no-trap precondition for c={c}; got `true`"
        );
        let proven =
            discharge_equal_under(Logic::QfBv, &precondition, &machine_out, &sdiv_by_const_spec(c));
        assert!(
            proven,
            "PROVEN-OUTPUT FAILED for c={c}: i64 Sdiv bytes must equal a/{c} on the no-trap path \
             for all a.\n  machine_out = {machine_out:?}\n  pre = {precondition:?}"
        );
    }
}

#[test]
fn i64_shl_bytes_compute_a_shl_c_on_no_trap_path() {
    let (code, base) = emit_text(&make_bridge_module(Shape::Shl));
    // Amounts spanning zero, one, a mid magnitude, and the max in-range amount
    // for a 64-bit value (63) — the 40 case is only meaningful at i64.
    let cs: &[i64] = &[0, 1, 7, 40, 63];
    for &c in cs {
        let (machine_out, precondition) = symbolic_machine_output_b_const(&code, base, c)
            .unwrap_or_else(|e| panic!("shl path-merge failed for c={c}: {e:?}"));
        assert!(
            !matches!(precondition, Formula::Bool(true)),
            "expected a non-trivial no-trap precondition for c={c}; got `true`"
        );
        let proven =
            discharge_equal_under(Logic::QfBv, &precondition, &machine_out, &shl_by_const_spec(c));
        assert!(
            proven,
            "PROVEN-OUTPUT FAILED for c={c}: i64 Ishl bytes must equal a<<{c} on the no-trap path \
             for all a.\n  machine_out = {machine_out:?}\n  pre = {precondition:?}"
        );
    }
}

// ===========================================================================
// MANDATORY NEGATIVE CONTROLS (SAT) — the SAME bytes against a `+ 1` spec MUST
// be SAT under the same precondition, or the positive certificate is vacuous.
// ===========================================================================

fn plus_one(spec: Formula) -> Formula {
    Formula::BvAdd(Box::new(spec), Box::new(bv64(1)), 64)
}

#[test]
fn negative_control_i64_add_vs_plus_one_is_sat() {
    let (code, base) = emit_text(&make_bridge_module(Shape::Add));
    let (machine_out, precondition) =
        symbolic_machine_output(&code, base).expect("add path-merge failed");
    let proven =
        discharge_equal_under(Logic::QfBv, &precondition, &machine_out, &plus_one(add_spec()));
    assert!(!proven, "VACUITY CHECK FAILED: i64 add bytes were 'proven' equal to a+b+1");
}

#[test]
fn negative_control_i64_checked_sub_vs_plus_one_is_sat() {
    let (code, base) = emit_text(&make_bridge_module(Shape::CheckedSub));
    let (machine_out, precondition) =
        symbolic_machine_output(&code, base).expect("sub path-merge failed");
    let proven =
        discharge_equal_under(Logic::QfBv, &precondition, &machine_out, &plus_one(sub_spec()));
    assert!(!proven, "VACUITY CHECK FAILED: i64 sub bytes were 'proven' equal to a-b+1");
}

#[test]
fn negative_control_i64_checked_mul_vs_plus_one_is_sat() {
    let (code, base) = emit_text(&make_bridge_module(Shape::CheckedMul));
    let cs: &[i64] = &[1, -1, 7, -6, 1_000_000, 3_000_000_000, i64::MAX, i64::MIN];
    for &c in cs {
        let (machine_out, precondition) = symbolic_machine_output_b_const(&code, base, c)
            .unwrap_or_else(|e| panic!("mul path-merge failed for c={c}: {e:?}"));
        let proven = discharge_equal_under(
            Logic::QfAbv,
            &precondition,
            &machine_out,
            &plus_one(mul_by_const_spec(c)),
        );
        assert!(!proven, "VACUITY CHECK FAILED for c={c}: mul bytes 'proven' equal to a*{c}+1");
    }
}

#[test]
fn negative_control_i64_signed_div_vs_plus_one_is_sat() {
    let (code, base) = emit_text(&make_bridge_module(Shape::SignedDiv));
    let cs: &[i64] = &[2, 3, 7, -2, 3_000_000_000];
    for &c in cs {
        let (machine_out, precondition) = symbolic_machine_output_b_const(&code, base, c)
            .unwrap_or_else(|e| panic!("div path-merge failed for c={c}: {e:?}"));
        let proven = discharge_equal_under(
            Logic::QfBv,
            &precondition,
            &machine_out,
            &plus_one(sdiv_by_const_spec(c)),
        );
        assert!(!proven, "VACUITY CHECK FAILED for c={c}: div bytes 'proven' equal to a/{c}+1");
    }
}

#[test]
fn negative_control_i64_shl_vs_plus_one_is_sat() {
    let (code, base) = emit_text(&make_bridge_module(Shape::Shl));
    let cs: &[i64] = &[0, 1, 7, 40, 63];
    for &c in cs {
        let (machine_out, precondition) = symbolic_machine_output_b_const(&code, base, c)
            .unwrap_or_else(|e| panic!("shl path-merge failed for c={c}: {e:?}"));
        let proven = discharge_equal_under(
            Logic::QfBv,
            &precondition,
            &machine_out,
            &plus_one(shl_by_const_spec(c)),
        );
        assert!(!proven, "VACUITY CHECK FAILED for c={c}: shl bytes 'proven' equal to (a<<{c})+1");
    }
}
