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
// TRAP ARMS. Since trust-cg b80b958f5 a LIR `Trap` selects to AArch64 `BRK #1`
// (as LLVM does for llvm.trap), no longer `call abort`. The no-trap
// precondition is therefore NOT derived from which emitted arm reaches a trap:
// it is each shape's INDEPENDENT source domain (`source_domain`), bound to the
// original argument registers before any emitted instruction executes. The
// replay omits an arm only when ay proves its path condition UNSAT under that
// domain; a feasible BRK still reaches the unchanged Aarch64Semantics refusal,
// and a call is never read as a trap. The BRK / call / domain-boundary /
// corrupted-guard controls at the end of this file pin that behaviour.
// These are bounded development solver checks, not kernel certificates.
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
                VerifiableBody {
                    locals,
                    blocks,
                    arg_count: 2,
                    return_ty: i64t(),
                    datatype_defs: Default::default(),
                },
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
                VerifiableBody {
                    locals,
                    blocks,
                    arg_count: 2,
                    return_ty: i64t(),
                    datatype_defs: Default::default(),
                },
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
                VerifiableBody {
                    locals,
                    blocks,
                    arg_count: 2,
                    return_ty: i64t(),
                    datatype_defs: Default::default(),
                },
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
                VerifiableBody {
                    locals,
                    blocks,
                    arg_count: 2,
                    return_ty: i64t(),
                    datatype_defs: Default::default(),
                },
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
        tuple_layouts: Default::default(),
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
// BOUNDED SYMBOLIC RETURN-PATH EXECUTOR (the design of the inline-multiblock
// harness, 7a1034b5c1; here the Ret reads the full 64-bit X0). The arithmetic
// input assumption is supplied independently of emitted control flow, per
// shape. An arm is omitted only when AY establishes that its accumulated path
// condition is UNSAT. Reachable BRK, calls, and unknown feasibility remain
// refusals; no trap semantics is invented.
//
// This replaces a path-MERGING executor that read the Assert trap block's
// `call abort` (an `Effect::Call`) as "this arm diverges" and conjoined the
// other arm's condition into the precondition. That trap block is retired: a
// LIR `Trap` now emits `BRK #1`, which Aarch64Semantics refuses fail-closed
// (blocker_code=aarch64-brk-debug-trap-not-proof-consumed).
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
                    // A call is not a proved diverging branch. (The retired
                    // Assert trap block began with `call abort`; the trap is now
                    // a BRK, refused by the semantics above if reachable.)
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
/// The path is first put through the same meaning-preserving `fold_consts`
/// the discharge uses, so a pinned operand reaches ay as a literal (the
/// emitted SMULH is a 128-bit product; unfolded, the pinned constant stays
/// wrapped in extension bookkeeping and ay bit-blasts a full multiplier).
fn path_is_feasible(path: &Formula) -> Result<bool, ExecError> {
    let path = fold_consts(path);
    let config = SolverConfig::default().with_timeout(Duration::from_secs(30));
    let mut solver = Solver::try_new_with_config(Logic::QfAbv, config)
        .map_err(|e| ExecError::Unsupported(format!("feasibility solver: {e:?}")))?;
    let condition = formula_to_term(&mut solver, &path);
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

/// FULLY symbolic (both operands range over all 2^64). Used for add/sub.
/// `shape` names the source whose independent domain is the precondition.
fn symbolic_machine_output(
    code: &[u8],
    base: u64,
    shape: Shape,
) -> Result<(Formula, Formula), ExecError> {
    run_machine_output(code, base, shape, MachineState::symbolic())
}

/// Replay with the SECOND argument register (X1 == `b`) pinned to a concrete
/// 64-bit literal `c`. X0 (== `a`) stays FULLY SYMBOLIC, so the result is an
/// infinite-domain statement over ALL 2^64 values of `a` for that fixed `c`.
/// Pinning turns the emitted 64-bit MUL / SDIV / LSLV into a by-constant op that
/// ay closes — still proving the REAL emitted 64-bit bytes over a full operand.
fn symbolic_machine_output_b_const(
    code: &[u8],
    base: u64,
    shape: Shape,
    c: i64,
) -> Result<(Formula, Formula), ExecError> {
    let mut state = MachineState::symbolic();
    state.gpr[1] = Formula::BitVec { value: i128::from(c), width: 64 };
    run_machine_output(code, base, shape, state)
}

/// Bind the source precondition to the ORIGINAL argument registers (X0 == `a`,
/// X1 == `b`) before any emitted instruction executes; decoded branches cannot
/// redefine this domain.
fn run_machine_output(
    code: &[u8],
    base: u64,
    shape: Shape,
    state: MachineState,
) -> Result<(Formula, Formula), ExecError> {
    let pre = source_domain(shape, state.read_gpr(0, 64), state.read_gpr(1, 64));
    run_under_domain(code, base, state, pre)
}

/// The replay under an explicit domain. Only `run_machine_output` (the source
/// domain) and the BRK controls (a deliberately vacuous domain) call it.
fn run_under_domain(
    code: &[u8],
    base: u64,
    state: MachineState,
    pre: Formula,
) -> Result<(Formula, Formula), ExecError> {
    if !path_is_feasible(&pre)? {
        return Err(ExecError::Unsupported("empty input domain".into()));
    }
    let out = Executor::new(code, base).run(base, state, Vec::new(), 0, pre.clone())?;
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
    if width < 128 && (v & (1i128 << (width - 1))) != 0 { v - (1i128 << width) } else { v }
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
        Formula::BvOr(a, b, w) => {
            fold_bin(a, b, *w, |x, y| x | y, |a, b, w| Formula::BvOr(a, b, w))
        }
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
// INDEPENDENT SOURCE DOMAINS: the inputs on which each bridge body's own
// `Assert`s pass, read off the SOURCE (`make_bridge_module`), never off the
// emitted bytes. `a` / `b` are the 64-bit argument registers X0 / X1 as the
// caller left them. The exact-boundary control below pins each one.
// ---------------------------------------------------------------------------

fn sext128(v: Formula) -> Formula {
    Formula::BvSignExt(Box::new(v), 64)
}

/// A 128-bit two's-complement value lies in [i64::MIN, i64::MAX] iff it is the
/// sign extension of its own low 64 bits. This is the same set as the two
/// signed comparisons (`i64_range_predicates_agree` proves it for a free
/// 128-bit value), spelled so ay does not have to push 128-bit comparators
/// through the SMULH product: with the comparator spelling the checked-mul
/// trap arm is `Unknown` at the 30 s deadline for c = 1_000_000 / 3_000_000_000.
fn in_i64_range(v128: Formula) -> Formula {
    let low = Formula::BvExtract { inner: Box::new(v128.clone()), high: 63, low: 0 };
    Formula::Eq(Box::new(v128), Box::new(sext128(low)))
}

/// The textbook spelling of the same range, kept only as the reference the
/// `in_i64_range` spelling is proven equal to.
fn in_i64_range_by_comparison(v128: Formula) -> Formula {
    let bound = |value: i64| Formula::BitVec { value: i128::from(value), width: 128 };
    Formula::And(vec![
        Formula::BvSLe(Box::new(bound(i64::MIN)), Box::new(v128.clone()), 128),
        Formula::BvSLe(Box::new(v128), Box::new(bound(i64::MAX)), 128),
    ])
}

/// Checked i64 `a - b` passes its overflow assert iff the exact difference of
/// the sign-extended i128 operands lies in [i64::MIN, i64::MAX]. Two
/// sign-extended i64 values cannot overflow i128.
fn no_signed_i64_sub_overflow(a: Formula, b: Formula) -> Formula {
    in_i64_range(Formula::BvSub(Box::new(sext128(a)), Box::new(sext128(b)), 128))
}

/// Checked i64 `a * b` passes its overflow assert iff the exact product of the
/// sign-extended i128 operands lies in [i64::MIN, i64::MAX]. |a * b| <= 2^126
/// cannot overflow i128.
fn no_signed_i64_mul_overflow(a: Formula, b: Formula) -> Formula {
    in_i64_range(Formula::BvMul(Box::new(sext128(a)), Box::new(sext128(b)), 128))
}

/// The div body's two asserts exactly as written: `!(b == 0)` and `!(b == -1)`.
/// The second traps on `b == -1` for EVERY dividend, not only `i64::MIN`.
fn signed_div_guards_pass(b: Formula) -> Formula {
    Formula::And(vec![
        Formula::Not(Box::new(Formula::Eq(Box::new(b.clone()), Box::new(bv64(0))))),
        Formula::Not(Box::new(Formula::Eq(Box::new(b), Box::new(bv64(-1))))),
    ])
}

/// The shift amount `b` is a `u32` (Rust's shift-count type, passed in W1); the
/// body asserts `!(b >= 64)`, i.e. `b <u 64` over those 32 bits only.
fn shift_amount_in_range(b: Formula) -> Formula {
    let amount = Formula::BvExtract { inner: Box::new(b), high: 31, low: 0 };
    Formula::BvULt(Box::new(amount), Box::new(Formula::BitVec { value: 64, width: 32 }), 32)
}

fn source_domain(shape: Shape, a: Formula, b: Formula) -> Formula {
    match shape {
        // Bare wrapping add: the body has no assert, so every input is admitted.
        Shape::Add => Formula::Bool(true),
        Shape::CheckedSub => no_signed_i64_sub_overflow(a, b),
        Shape::CheckedMul => no_signed_i64_mul_overflow(a, b),
        Shape::SignedDiv => signed_div_guards_pass(b),
        Shape::Shl => shift_amount_in_range(b),
    }
}

// ---------------------------------------------------------------------------
// Concrete byte-execution oracle (the emitted bytes are the value oracle for the
// bridge's checked pair, one `make_aggregate` since BMC-LANE-1 and an `Undef`
// seed before it; run with concrete registers).
// ---------------------------------------------------------------------------

fn concrete_run(code: &[u8], base: u64, a: i64, b: i64) -> Result<Formula, ExecError> {
    let mut state = MachineState::symbolic();
    state.gpr[0] = Formula::BitVec { value: i128::from(a), width: 64 };
    state.gpr[1] = Formula::BitVec { value: i128::from(b), width: 64 };
    // The concrete inputs ARE the precondition: with constant argument
    // registers every branch condition is ground, so feasibility prunes exactly
    // the side these inputs do not take. Concrete runs are NOT restricted to the
    // source domain: a trapping input must reach the unchanged BRK refusal.
    Executor::new(code, base).run(base, state, Vec::new(), 0, Formula::Bool(true))
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

/// Every value witness below is a no-trap input, so its run must return. (It
/// used to report `false` on the retired `call abort` arm; a trapping input now
/// reaches the BRK refusal, which is a failure here, not a value.)
fn bytes_value_equals(code: &[u8], base: u64, a: i64, b: i64, expected: i64) -> bool {
    let out = concrete_run(code, base, a, b)
        .unwrap_or_else(|e| panic!("concrete no-trap run ({a}, {b}) must return: {e:?}"));
    concrete_equals(&out, expected)
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
    let lir =
        lower_trust_ir_function_to_lir(&module, &module.functions[0]).expect("i64 shl lowers");
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
        symbolic_machine_output(&code, base, Shape::Add).expect("add path-merge failed");
    // Bare add: no guard, so the precondition is trivially true (allowed here —
    // there is no trap arm to explore).
    let proven = discharge_equal_under(Logic::QfBv, &precondition, &machine_out, &add_spec());
    assert!(proven, "PROVEN-OUTPUT FAILED: i64 add bytes must equal a+b for ALL 2^64 pairs");
}

#[test]
fn i64_checked_sub_bytes_compute_a_minus_b_on_no_overflow_path() {
    let (code, base) = emit_text(&make_bridge_module(Shape::CheckedSub));
    let (machine_out, precondition) =
        symbolic_machine_output(&code, base, Shape::CheckedSub).expect("sub path-merge failed");
    // The precondition is now the explicit independent source no-overflow
    // domain (it used to be derived from the retired `call abort` trap arm); it
    // must be non-trivial. That the emitted guard is lowered, reachable, and
    // not weakened is checked by the BRK / boundary / corrupted-guard controls.
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
        let (machine_out, precondition) =
            symbolic_machine_output_b_const(&code, base, Shape::CheckedMul, c)
                .unwrap_or_else(|e| panic!("mul path-merge failed for c={c}: {e:?}"));
        // c==0 never overflows; every other c must be guarded (non-trivial
        // no-overflow precondition). The precondition is now the independent
        // source domain, not the retired `call abort` trap arm's negation.
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
        let (machine_out, precondition) =
            symbolic_machine_output_b_const(&code, base, Shape::SignedDiv, c)
                .unwrap_or_else(|e| panic!("div path-merge failed for c={c}: {e:?}"));
        // The independent source domain replaces the retired `call abort` trap
        // arm's negation. For a pinned in-domain divisor it is a ground formula
        // (so this is a syntactic check, as it was before); the BRK controls show
        // the div guards are really lowered and reachable.
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
        let (machine_out, precondition) =
            symbolic_machine_output_b_const(&code, base, Shape::Shl, c)
                .unwrap_or_else(|e| panic!("shl path-merge failed for c={c}: {e:?}"));
        // As for div: the independent source domain (ground for a pinned
        // amount) replaces the retired `call abort` trap arm's negation.
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
// be SAT under the same (independent source) precondition, or the positive
// check is vacuous.
// ===========================================================================

fn plus_one(spec: Formula) -> Formula {
    Formula::BvAdd(Box::new(spec), Box::new(bv64(1)), 64)
}

#[test]
fn negative_control_i64_add_vs_plus_one_is_sat() {
    let (code, base) = emit_text(&make_bridge_module(Shape::Add));
    let (machine_out, precondition) =
        symbolic_machine_output(&code, base, Shape::Add).expect("add path-merge failed");
    let proven =
        discharge_equal_under(Logic::QfBv, &precondition, &machine_out, &plus_one(add_spec()));
    assert!(!proven, "VACUITY CHECK FAILED: i64 add bytes were 'proven' equal to a+b+1");
}

#[test]
fn negative_control_i64_checked_sub_vs_plus_one_is_sat() {
    let (code, base) = emit_text(&make_bridge_module(Shape::CheckedSub));
    let (machine_out, precondition) =
        symbolic_machine_output(&code, base, Shape::CheckedSub).expect("sub path-merge failed");
    let proven =
        discharge_equal_under(Logic::QfBv, &precondition, &machine_out, &plus_one(sub_spec()));
    assert!(!proven, "VACUITY CHECK FAILED: i64 sub bytes were 'proven' equal to a-b+1");
}

#[test]
fn negative_control_i64_checked_mul_vs_plus_one_is_sat() {
    let (code, base) = emit_text(&make_bridge_module(Shape::CheckedMul));
    let cs: &[i64] = &[1, -1, 7, -6, 1_000_000, 3_000_000_000, i64::MAX, i64::MIN];
    for &c in cs {
        let (machine_out, precondition) =
            symbolic_machine_output_b_const(&code, base, Shape::CheckedMul, c)
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
        let (machine_out, precondition) =
            symbolic_machine_output_b_const(&code, base, Shape::SignedDiv, c)
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
        let (machine_out, precondition) =
            symbolic_machine_output_b_const(&code, base, Shape::Shl, c)
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

// ===========================================================================
// TRAP / DOMAIN CONTROLS. The replay above avoids a BRK only by proving its
// path UNSAT under the independent source domain. These pin that the pruning
// cannot swallow a reachable trap, invent a trap, or shrink the domain.
// ===========================================================================

const GUARDED: [Shape; 4] = [Shape::CheckedSub, Shape::CheckedMul, Shape::SignedDiv, Shape::Shl];

fn assert_brk_refused(result: Result<Formula, ExecError>) {
    assert!(
        matches!(result, Err(ExecError::Decode(ref message))
        if message.contains("effects Brk")
        && message.contains("aarch64-brk-debug-trap-not-proof-consumed")),
        "reachable BRK must remain the exact semantics refusal: {result:?}"
    );
}

/// The retired premise, pinned structurally: every guarded shape's shared trap
/// block is ONE `BRK #1` and nothing emits a call (the trap used to be a
/// `call abort`); the bare add carries no trap at all.
#[test]
fn i64_trap_block_is_one_brk_and_no_shape_emits_a_call() {
    for shape in [Shape::Add, Shape::CheckedSub, Shape::CheckedMul, Shape::SignedDiv, Shape::Shl] {
        let (code, base) = emit_text(&make_bridge_module(shape));
        assert_eq!(
            count_opcode(&code, base, &[Opcode::Bl, Opcode::Blr]),
            0,
            "{shape:?} must have no emitted call edge"
        );
        let brks = if shape == Shape::Add { 0 } else { 1 };
        assert_eq!(
            count_opcode(&code, base, &[Opcode::Brk]),
            brks,
            "{shape:?} must carry exactly {brks} BRK (its lowered trap block)"
        );
    }
}

/// A FEASIBLE trap is never pruned: each input that fails its body's assert
/// reaches the exact BRK refusal, as does a BRK at entry with no branch at all.
#[test]
fn feasible_trap_inputs_and_entry_brk_remain_refused() {
    let cases: [(Shape, &[(i64, i64)]); 4] = [
        (Shape::CheckedSub, &[(i64::MIN, 1), (i64::MAX, -1), (0, i64::MIN)]),
        (Shape::CheckedMul, &[(i64::MAX, 2), (i64::MIN, -1), (1 << 32, 1 << 31)]),
        (Shape::SignedDiv, &[(7, 0), (7, -1), (i64::MIN, -1)]),
        (Shape::Shl, &[(1, 64), (1, i64::from(u32::MAX))]),
    ];
    for (shape, inputs) in cases {
        let (code, base) = emit_text(&make_bridge_module(shape));
        for &(a, b) in inputs {
            assert!(
                !path_is_feasible(&source_domain(shape, bv64(a.into()), bv64(b.into()))).unwrap(),
                "fixture: ({a}, {b}) must be outside the {shape:?} source domain"
            );
            assert_brk_refused(concrete_run(&code, base, a, b));
        }
    }
    assert_brk_refused(concrete_run(&0xd420_0020u32.to_le_bytes(), 0, 2, 3));
}

/// The pruning is the independent domain's doing, not the executor's: the SAME
/// symbolic replays under the vacuous domain `true` admit trapping inputs, so
/// the BRK arm is feasible and must reach the refusal.
#[test]
fn symbolic_replay_without_the_source_domain_reaches_brk_refusal() {
    // (shape, pinned X1 or fully symbolic). Mul pins X1 so the query stays a
    // by-constant 128-bit product.
    for (shape, pinned_b) in [
        (Shape::CheckedSub, None),
        (Shape::CheckedMul, Some(2)),
        (Shape::SignedDiv, None),
        (Shape::Shl, None),
    ] {
        let (code, base) = emit_text(&make_bridge_module(shape));
        let mut state = MachineState::symbolic();
        if let Some(c) = pinned_b {
            state.gpr[1] = bv64(i128::from(c));
        }
        assert_brk_refused(
            run_under_domain(&code, base, state, Formula::Bool(true)).map(|(out, _)| out),
        );
    }
}

#[test]
fn arbitrary_call_is_not_treated_as_a_trap() {
    let result = concrete_run(&0x9400_0000u32.to_le_bytes(), 0, 2, 3);
    assert!(
        matches!(result, Err(ExecError::Unsupported(ref message))
        if message.starts_with("call at ")),
        "a call is not a proved diverging branch: {result:?}"
    );
}

#[test]
fn independent_source_domains_have_exact_boundaries() {
    let admits = |shape: Shape, a: i64, b: i64| {
        path_is_feasible(&source_domain(shape, bv64(a.into()), bv64(b.into()))).unwrap()
    };
    for (a, b, fits) in [
        (i64::MIN, 0, true),
        (i64::MIN, 1, false),
        (i64::MAX, 0, true),
        (i64::MAX, -1, false),
        (-1, i64::MAX, true),
        (-2, i64::MAX, false),
        (-1, i64::MIN, true),
        (0, i64::MIN, false),
    ] {
        assert_eq!(admits(Shape::CheckedSub, a, b), fits, "sub domain for {a} - {b}");
    }
    for (a, b, fits) in [
        (i64::MAX, 1, true),
        (i64::MAX, 2, false),
        (i64::MIN, 1, true),
        (i64::MIN, -1, false),
        (-1, i64::MIN, false),
        (0, i64::MIN, true),
        (1 << 31, 1 << 31, true),
        (1 << 32, 1 << 31, false),
        (-(1 << 32), 1 << 31, true),
        (3_000_000_000, 3_000_000_000, true),
        (3_100_000_000, 3_000_000_000, false),
    ] {
        assert_eq!(admits(Shape::CheckedMul, a, b), fits, "mul domain for {a} * {b}");
    }
    for (a, b, fits) in [
        (7, 0, false),
        (7, -1, false),
        (i64::MIN, -1, false),
        (i64::MIN, 1, true),
        (i64::MIN, -2, true),
        (-7, 2, true),
    ] {
        assert_eq!(admits(Shape::SignedDiv, a, b), fits, "div domain for {a} / {b}");
    }
    // Only W1 (the u32 amount) is read; upper X1 bits are the caller's garbage.
    for (b, fits) in
        [(0, true), (63, true), (64, false), (i64::from(u32::MAX), false), ((1 << 32) | 5, true)]
    {
        assert_eq!(admits(Shape::Shl, 1, b), fits, "shl domain for amount {b:#x}");
    }
    assert!(admits(Shape::Add, i64::MAX, 1), "bare add has no assert; it admits every input");
}

/// The sub/mul domains' `in_i64_range` is exactly the signed-comparison range:
/// equal for EVERY 128-bit value (UNSAT of their disagreement), and non-vacuous
/// at the four i64 boundary values on either side.
#[test]
fn i64_range_predicates_agree() {
    let v = Formula::Var("R128".into(), Sort::BitVec(128));
    let disagree = Formula::Not(Box::new(Formula::Eq(
        Box::new(in_i64_range(v.clone())),
        Box::new(in_i64_range_by_comparison(v)),
    )));
    assert!(!path_is_feasible(&disagree).unwrap(), "range spellings must agree everywhere");
    let min = i128::from(i64::MIN);
    let max = i128::from(i64::MAX);
    for (value, fits) in [(min, true), (min - 1, false), (max, true), (max + 1, false)] {
        let v = Formula::BitVec { value, width: 128 };
        assert_eq!(path_is_feasible(&in_i64_range(v)).unwrap(), fits, "in_i64_range({value})");
    }
}

/// Inverting an actual emitted guard must turn in-domain inputs into a
/// reachable BRK — never into a silently smaller admitted domain.
#[test]
fn corrupted_guard_cannot_shrink_the_input_domain() {
    // (shape, in-domain concrete (a, b), pinned X1 for the symbolic replay).
    let cases = [
        (Shape::CheckedSub, (2, 3), None),
        (Shape::CheckedMul, (6, 7), Some(7)),
        (Shape::SignedDiv, (7, 2), Some(2)),
        (Shape::Shl, (1, 4), Some(4)),
    ];
    assert_eq!(cases.map(|(shape, ..)| shape), GUARDED, "cover every guarded shape");
    for (shape, (a, b), pinned_b) in cases {
        let (code, base) = emit_text(&make_bridge_module(shape));
        assert!(concrete_run(&code, base, a, b).is_ok(), "{shape:?}: uncorrupted run returns");
        let guards: Vec<_> = code
            .chunks_exact(4)
            .enumerate()
            .filter_map(|(index, bytes)| {
                let bytes: [u8; 4] = bytes.try_into().unwrap();
                (decode_aarch64(&bytes, base + (index * 4) as u64).unwrap().opcode == Opcode::BCond)
                    .then_some(index * 4)
            })
            .collect();
        let expected = if shape == Shape::SignedDiv { 2 } else { 1 };
        assert_eq!(guards.len(), expected, "{shape:?} fixture: actual guard branch count");
        for offset in guards {
            let mut corrupted = code.clone();
            // Flip B.cond bit 0: the condition is inverted (NE <-> EQ).
            let word = u32::from_le_bytes(corrupted[offset..offset + 4].try_into().unwrap()) ^ 1;
            corrupted[offset..offset + 4].copy_from_slice(&word.to_le_bytes());
            assert_brk_refused(concrete_run(&corrupted, base, a, b));
            let symbolic = match pinned_b {
                None => symbolic_machine_output(&corrupted, base, shape),
                Some(c) => symbolic_machine_output_b_const(&corrupted, base, shape, c),
            };
            assert_brk_refused(symbolic.map(|(out, _)| out));
        }
    }
}
