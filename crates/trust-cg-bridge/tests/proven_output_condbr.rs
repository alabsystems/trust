// proven_output_condbr.rs — infinite-domain proven-output certificates for
// LOOP-FREE functions that lower to REAL CONTROL FLOW (Subs + BCond + B,
// multi-block), via a BOUNDED SYMBOLIC PATH-MERGING executor.
//
// This is the rung above proven_output_cfg_mem.rs. That suite proved the
// straight-line surface (scalar ALU, branchless Csinc/Ite select, store-load)
// and DEFERRED max/min/abs/clamp because they lower — per the empirical probe —
// to a REAL conditional branch (Subs + BCond + B), which the straight-line
// symbolic executor fails-closed on at the first Effect::ConditionalBranch.
//
// HERE we close that residual for LOOP-FREE (DAG-CFG) functions with a bounded
// path-merging executor:
//
//   * Execute straight-line via apply_effects until a ConditionalBranch.
//   * At a ConditionalBranch{condition, target, fallthrough}: compute the
//     path-condition Formula = condition_to_formula(state, condition) over the
//     CURRENT (post-Cmp/Subs) symbolic NZCV flags, then FORK — recurse on
//     (taken target PC, state.clone()) and (fallthrough PC, state.clone()).
//   * Each branch executes to its RET; we read W0 = read_gpr(0,32) at the RET.
//   * MERGE: the two results join as Formula::Ite(path_condition, taken, fall).
//   * Nested branches recurse, building nested Ite (handled by clamp if tractable).
//
// LOOP SAFETY (fail-closed, NEVER loop forever, NEVER fake a proof):
//   * A per-path visited-PC set detects revisited PCs and backedges (a branch
//     target at or before a PC already on the current path). On detection we
//     return Err(Unsupported) and the function is reported SKIPPED, not proven.
//   * Hard caps on total instruction steps and fork depth.
//   * Only forward-branch DAGs are provable; loops are explicitly deferred.
//
// ANTI-VACUITY (load-bearing): machine_out is BYTE-DERIVED (emit -> decode ->
// effects -> path-merge), NEVER reconstructed from the IR. The Ite merge
// condition IS the real machine branch condition (condition_to_formula over the
// REAL post-Subs flags), so a WRONG merge makes ay find a COUNTEREXAMPLE — it
// does not silently pass. EVERY positive certificate ships a NEGATIVE CONTROL:
// a wrong spec discharged against the SAME emitted bytes that ay must return SAT
// on. A non-SAT negative control is VACUOUS and the test fails loudly.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![cfg(feature = "ay-proofs")]

use ay::{BigInt, Logic, Solver, Term};
use trust_cg_bridge::codegen_backend::{TrustCgCodegenBackend, TrustCgTargetArch};
use trust_disasm::{Opcode, decode_aarch64};
use trust_machine_sem::{
    Aarch64Semantics, Effect, MachineState, Semantics, condition_to_formula,
};
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Rvalue, Sort,
    SourceSpan, Statement, Terminator, Ty, UnOp, VerifiableBody, VerifiableFunction,
};

// ---------------------------------------------------------------------------
// IR builders. These mirror the multi-block CFG bodies from
// isa_oracle_differential_cfg_mem.rs (already differentially VALIDATED against
// silicon there): cmp + SwitchInt(bool) -> trust-cg lowers to Subs + BCond + B.
// ---------------------------------------------------------------------------

fn sp() -> SourceSpan {
    SourceSpan::default()
}

fn wrap(name: &str, body: VerifiableBody) -> VerifiableFunction {
    VerifiableFunction {
        name: name.into(),
        def_path: format!("condbr::{name}"),
        span: sp(),
        body,
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// bb0: `cond = lhs <cmp> rhs; if cond != 0 -> then else -> else`.
fn cmp_branch_block(
    cmp: BinOp,
    lhs: usize,
    rhs: usize,
    cond_local: usize,
    then_blk: usize,
    else_blk: usize,
) -> BasicBlock {
    BasicBlock {
        id: BlockId(0),
        stmts: vec![Statement::Assign {
            place: Place::local(cond_local),
            rvalue: Rvalue::BinaryOp(
                cmp,
                Operand::Copy(Place::local(lhs)),
                Operand::Copy(Place::local(rhs)),
            ),
            span: sp(),
        }],
        terminator: Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(cond_local)),
            targets: vec![(0, BlockId(else_blk))], // cond == 0 -> else
            otherwise: BlockId(then_blk),          // cond != 0 -> then
            exhaustive_enum_unreachable: false,
            span: sp(),
        },
    }
}

/// `ret = local(src_local); return`.
fn ret_use_block(id: usize, src_local: usize) -> BasicBlock {
    BasicBlock {
        id: BlockId(id),
        stmts: vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(src_local))),
            span: sp(),
        }],
        terminator: Terminator::Return,
    }
}

/// max(a,b): if a>=b {a} else {b}.
fn author_max() -> VerifiableFunction {
    wrap(
        "cfg_max",
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::bool_ty(), name: None },
            ],
            blocks: vec![
                cmp_branch_block(BinOp::Ge, 1, 2, 3, 1, 2),
                ret_use_block(1, 1), // then: a
                ret_use_block(2, 2), // else: b
            ],
            arg_count: 2,
            return_ty: Ty::i32(),
        },
    )
}

/// min(a,b): if a<=b {a} else {b}.
fn author_min() -> VerifiableFunction {
    wrap(
        "cfg_min",
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::bool_ty(), name: None },
            ],
            blocks: vec![
                cmp_branch_block(BinOp::Le, 1, 2, 3, 1, 2),
                ret_use_block(1, 1), // then: a
                ret_use_block(2, 2), // else: b
            ],
            arg_count: 2,
            return_ty: Ty::i32(),
        },
    )
}

/// abs(x): if x < 0 { -x } else { x }.
fn author_abs() -> VerifiableFunction {
    wrap(
        "cfg_abs",
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::bool_ty(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(0)),
                        ),
                        span: sp(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(0, BlockId(2))], // c == 0 -> identity
                        otherwise: BlockId(1),          // c != 0 -> negate
                        exhaustive_enum_unreachable: false,
                        span: sp(),
                    },
                },
                // then: ret = -x
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(1))),
                        span: sp(),
                    }],
                    terminator: Terminator::Return,
                },
                ret_use_block(2, 1), // else: x
            ],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
    )
}

/// clamp(x, lo, hi): if x < lo { lo } else if x > hi { hi } else { x } — a
/// tree-structured (nested-branch) CFG. Provided to STRESS the nested-Ite merge.
fn author_clamp() -> VerifiableFunction {
    wrap(
        "cfg_clamp",
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("lo".into()) },
                LocalDecl { index: 3, ty: Ty::i32(), name: Some("hi".into()) },
                LocalDecl { index: 4, ty: Ty::bool_ty(), name: None },
                LocalDecl { index: 5, ty: Ty::bool_ty(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: sp(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(4)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: sp(),
                    },
                },
                ret_use_block(1, 2), // ret lo
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Gt,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(3)),
                        ),
                        span: sp(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(5)),
                        targets: vec![(0, BlockId(4))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: sp(),
                    },
                },
                ret_use_block(3, 3), // ret hi
                ret_use_block(4, 1), // ret x
            ],
            arg_count: 3,
            return_ty: Ty::i32(),
        },
    )
}

// ---------------------------------------------------------------------------
// Emit via trust-cg (host triple) + Mach-O __text extraction.
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

fn emit_text(func: &VerifiableFunction) -> (Vec<u8>, u64) {
    let triple = host_triple();
    let backend = TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::host(), triple);
    let lir = backend.lower_function(func).expect("lower_function failed");
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
                let name = &obj[sec..sec + 16];
                if name.starts_with(b"__text\0") {
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
// BOUNDED SYMBOLIC PATH-MERGING EXECUTOR.
//
// Decode the EMITTED BYTES. Execute straight-line effects through a symbolic
// MachineState until a RET (returns W0) or a ConditionalBranch (FORK). At a
// ConditionalBranch: path_cond = condition_to_formula(state, condition) over the
// CURRENT (post-Subs) flags; recurse on the taken-target state and the
// fallthrough state; MERGE as Ite(path_cond, taken, fallthrough).
//
// Loop-safety: a per-path visited-PC set + caps. Any backedge / revisited PC /
// cap breach returns Err(ExecError) — the function is then SKIPPED, never faked.
// ===========================================================================

const MAX_STEPS: u32 = 4096; // global instruction budget across all forks
const MAX_DEPTH: u32 = 16; // fork-depth cap (>= 2^16 leaves rejected earlier by steps)

#[derive(Debug, Clone, PartialEq, Eq)]
enum ExecError {
    /// A loop / backedge / revisited PC was detected on the current path.
    Loop { at: u64 },
    /// A bound (instruction count or fork depth) was exceeded.
    BudgetExceeded,
    /// An effect outside the modeled DAG-CFG surface (calls, atomics, indirect
    /// branch, etc.) was encountered — fail closed.
    Unsupported(String),
    /// Decode / out-of-range / semantics failure.
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

    /// Execute from `pc` carrying `state` and the set of PCs already `visited` on
    /// THIS path, returning the merged 32-bit W0 Formula at the reachable RET(s).
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
            // --- LOOP SAFETY: a revisited PC on this path is a backedge. ---
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

            // A RET ends this path; read W0 now.
            if opcode == Opcode::Ret {
                return Ok(state.read_gpr(0, 32));
            }

            // Scan for control-flow effects this instruction produced.
            let mut cond_branch: Option<(_, Formula, Formula)> = None;
            let mut uncond_target: Option<Formula> = None;
            let mut plain: Vec<&Effect> = Vec::new();
            for e in &effects {
                match e {
                    Effect::ConditionalBranch { condition, target, fallthrough } => {
                        cond_branch = Some((*condition, target.clone(), fallthrough.clone()));
                    }
                    Effect::Branch { target } => uncond_target = Some(target.clone()),
                    // PcUpdate that accompanies B/RET is folded into the control
                    // handling below; do NOT thread it as a plain effect.
                    Effect::PcUpdate { .. } => {}
                    Effect::Call { .. } => {
                        return Err(ExecError::Unsupported(format!("Call at {pc:#x}")));
                    }
                    Effect::Aarch64SyncBoundary { .. } | Effect::Aarch64AtomicAccess { .. } => {
                        return Err(ExecError::Unsupported(format!("atomic/sync at {pc:#x}")));
                    }
                    other => plain.push(other),
                }
            }

            // Thread the data-plane effects (RegWrite/FlagUpdate/Mem*) FIRST so the
            // branch condition sees the post-Subs flags.
            for e in &plain {
                state
                    .apply_effect(e)
                    .map_err(|er| ExecError::Decode(format!("apply {e:?} at {pc:#x}: {er:?}")))?;
            }

            if let Some((condition, target, _fallthrough)) = cond_branch {
                // path_cond is the REAL machine branch condition over the post-Subs
                // symbolic NZCV flags now in `state.flags`.
                let path_cond = condition_to_formula(&state, condition);

                // The branch target is a constant PC-relative address resolved by
                // trust-disasm. The fallthrough is, by AArch64 definition, pc+4 —
                // the effect's `fallthrough` Formula is `BvAdd(PC, 4)` over the
                // SYMBOLIC PC var, so we compute the concrete fallthrough directly.
                let target_pc = const_addr(&target)
                    .ok_or_else(|| ExecError::Unsupported(format!("indirect bcond at {pc:#x}")))?;
                let fall_pc = pc + 4;

                // --- LOOP SAFETY: a branch target at/below a PC already on this
                // path is a backedge; bail before recursing. ---
                if visited.contains(&target_pc) || visited.contains(&fall_pc) {
                    return Err(ExecError::Loop { at: pc });
                }

                let taken = self.run(target_pc, state.clone(), visited.clone(), depth + 1)?;
                let fall = self.run(fall_pc, state.clone(), visited.clone(), depth + 1)?;

                // MERGE. taken/fall are both BitVec(32); the Ite condition is the
                // real machine condition, so a wrong path assignment -> ay CEX.
                return Ok(Formula::Ite(Box::new(path_cond), Box::new(taken), Box::new(fall)));
            }

            if let Some(target) = uncond_target {
                let target_pc = const_addr(&target)
                    .ok_or_else(|| ExecError::Unsupported(format!("indirect b at {pc:#x}")))?;
                if visited.contains(&target_pc) {
                    return Err(ExecError::Loop { at: target_pc });
                }
                pc = target_pc; // follow the unconditional branch
                continue;
            }

            // Straight-line: advance to the next instruction.
            pc += 4;
        }
    }
}

/// Extract a constant 64-bit address from a branch-target Formula.
fn const_addr(f: &Formula) -> Option<u64> {
    match f {
        Formula::BitVec { value, .. } => Some(*value as u64),
        _ => None,
    }
}

/// Byte-derived machine output via path-merging. `Ok(formula)` for DAG-CFG
/// functions; `Err` (loops / unsupported / budget) -> the function is SKIPPED.
fn symbolic_machine_output(code: &[u8], base: u64) -> Result<Formula, ExecError> {
    let mut exec = Executor::new(code, base);
    let state = MachineState::symbolic();
    exec.run(base, state, Vec::new(), 0)
}

// ---------------------------------------------------------------------------
// Formula -> ay::Term translation (the cfg_mem translator, unchanged).
// ---------------------------------------------------------------------------

fn var_term(solver: &mut Solver, name: &str, sort: &Sort) -> Term {
    match sort {
        Sort::BitVec(w) => solver.bv_var(name, *w),
        Sort::Bool => solver.bool_var(name),
        Sort::Array(idx, elem) => {
            let (Sort::BitVec(iw), Sort::BitVec(ew)) = (idx.as_ref(), elem.as_ref()) else {
                panic!("unsupported array sort for Var {name}: {sort:?}");
            };
            solver
                .declare_const(name, ay::Sort::array(ay::Sort::bitvec(*iw), ay::Sort::bitvec(*ew)))
        }
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
        Formula::Select(arr, idx) => {
            let a = formula_to_term(solver, arr);
            let i = formula_to_term(solver, idx);
            solver.try_select(a, i).expect("select")
        }
        Formula::Store(arr, idx, val) => {
            let a = formula_to_term(solver, arr);
            let i = formula_to_term(solver, idx);
            let v = formula_to_term(solver, val);
            solver.try_store(a, i, v).expect("store")
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

/// Discharge `machine_out == ir_out` over ALL inputs via ay (QF_ABV).
fn discharge_equal(machine_out: &Formula, ir_out: &Formula) -> bool {
    let mut solver = Solver::try_new(Logic::QfAbv).expect("ay Solver::try_new");
    let lhs = formula_to_term(&mut solver, machine_out);
    let rhs = formula_to_term(&mut solver, ir_out);
    let eq = solver.try_eq(lhs, rhs).expect("eq");
    let differ = solver.try_not(eq).expect("not");
    solver.try_assert_term(differ).expect("assert");

    let result = solver.check_sat();
    if result.is_unsat() {
        true
    } else if result.is_sat() {
        false
    } else {
        panic!("ay returned unknown: {result:?}");
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Verdict {
    Proven,
    CounterExample,
    Skipped(ExecError),
}

fn prove_output_equiv(func: &VerifiableFunction, ir_spec: &Formula) -> Verdict {
    let (code, base) = emit_text(func);
    assert!(!code.is_empty(), "emitted __text is empty for {}", func.name);
    match symbolic_machine_output(&code, base) {
        Ok(machine_out) => {
            if discharge_equal(&machine_out, ir_spec) {
                Verdict::Proven
            } else {
                Verdict::CounterExample
            }
        }
        Err(e) => Verdict::Skipped(e),
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
// ===========================================================================
// CERTIFICATES. Each positive cert: machine_out == ir_spec discharged UNSAT
// (proven for ALL inputs). Each ships a NEGATIVE CONTROL ay must find SAT on.
//
// SIGNEDNESS NOTE (load-bearing, same as proven_output_cfg_mem.rs): trust-cg
// lowers i32 `>=`/`<=`/`<` to flag conditions whose BYTE-DERIVED reduction is an
// UNSIGNED predicate (Csinc over C/Z + a BCond.Ne on the resulting bool). We
// prove what the BYTES compute (the UNSIGNED min/max), and use the SIGNED
// variant as the negative control — which is exactly the property that
// distinguishes the two and proves the path-merge discharge has teeth. A
// MIS-MERGED Ite (wrong path condition) would make even the unsigned spec FAIL.
// ===========================================================================

// ---- max(a,b): byte-derived path-merge == SIGNED max == (b <=s a) ? a : b ----
//
// The i32 `a >= b` comparison now lowers to a SIGNED condition code (see the
// lower.rs cmp-signedness fix that also discharged abs): the Subs+Csinc bool is
// `a >=s b`, driving the BCond.Ne fork. The merge Ite(path_cond, a, b) reduces
// to signed max.
#[test]
fn cfg_max_proven_and_negctrl() {
    let f = author_max();
    let spec = Formula::Ite(
        Box::new(Formula::BvSLe(Box::new(wn(1)), Box::new(wn(0)), 32)), // b <=s a == a >=s b
        Box::new(wn(0)),
        Box::new(wn(1)),
    );
    assert_eq!(
        prove_output_equiv(&f, &spec),
        Verdict::Proven,
        "max: byte-derived path-merge was not proven == signed-max(a,b)"
    );
    // NEGATIVE CONTROL: the bytes are NOT unsigned-max (differ at a=-1,b=0:
    // signed-max=0, unsigned-max=-1). ay must find this SAT.
    let wrong = Formula::Ite(
        Box::new(Formula::BvULe(Box::new(wn(1)), Box::new(wn(0)), 32)),
        Box::new(wn(0)),
        Box::new(wn(1)),
    );
    assert_eq!(
        prove_output_equiv(&f, &wrong),
        Verdict::CounterExample,
        "VACUITY: max bytes were 'proven' equal to unsigned-max — discharge has no teeth"
    );
}

// ---- min(a,b): byte-derived path-merge == SIGNED min == (a <=s b) ? a : b ----
#[test]
fn cfg_min_proven_and_negctrl() {
    let f = author_min();
    let spec = Formula::Ite(
        Box::new(Formula::BvSLe(Box::new(wn(0)), Box::new(wn(1)), 32)),
        Box::new(wn(0)),
        Box::new(wn(1)),
    );
    assert_eq!(
        prove_output_equiv(&f, &spec),
        Verdict::Proven,
        "min: byte-derived path-merge was not proven == signed-min(a,b)"
    );
    // NEGATIVE CONTROL: the bytes are NOT unsigned-min.
    let wrong = Formula::Ite(
        Box::new(Formula::BvULe(Box::new(wn(0)), Box::new(wn(1)), 32)),
        Box::new(wn(0)),
        Box::new(wn(1)),
    );
    assert_eq!(
        prove_output_equiv(&f, &wrong),
        Verdict::CounterExample,
        "VACUITY: min bytes were 'proven' equal to unsigned-min"
    );
}

// ---- clamp(x,lo,hi): NESTED-branch path-merge == UNSIGNED clamp ----
//
// This is the tree-CFG cert: bb0 forks (x <u lo), the else-fork hits a SECOND
// ConditionalBranch (x >u hi), and the executor builds a nested Ite. It proves
// the path-merging executor composes nested branches correctly.
#[test]
fn cfg_clamp_proven_and_negctrl() {
    let f = author_clamp();
    // clamp = if x <s lo { lo } else if x >s hi { hi } else { x }.
    // The i32 `<`/`>` comparisons now lower to SIGNED condition codes (lower.rs
    // cmp-signedness fix), so the nested-Ite merge reduces to signed clamp.
    let spec = Formula::Ite(
        Box::new(Formula::BvSLt(Box::new(wn(0)), Box::new(wn(1)), 32)),
        Box::new(wn(1)), // lo
        Box::new(Formula::Ite(
            Box::new(Formula::BvSLt(Box::new(wn(2)), Box::new(wn(0)), 32)), // hi <s x == x >s hi
            Box::new(wn(2)),                                                // hi
            Box::new(wn(0)),                                                // x
        )),
    );
    assert_eq!(
        prove_output_equiv(&f, &spec),
        Verdict::Proven,
        "clamp: nested-branch path-merge was not proven == signed-clamp(x,lo,hi)"
    );
    // NEGATIVE CONTROL: clamp is NOT the identity (differs whenever x is out of range).
    assert_eq!(
        prove_output_equiv(&f, &wn(0)),
        Verdict::CounterExample,
        "VACUITY: clamp bytes were 'proven' equal to the identity"
    );
}

// ---- abs(x): byte-derived path-merge == two's-complement signed-abs ----
//
// Previously SKIPPED: trust-cg lowered `x < 0` (i32 vs the literal 0) with
// UNSIGNED semantics (Csinc over the `Cs`/C==1 flag of `Subs WZR, x, #0`),
// which is vacuously true for all x, leaving the negate block dead and the
// emitted bytes computing the IDENTITY rather than signed-abs.
//
// Root cause + fix: crates/trust-cg-bridge/src/lower.rs Rvalue::BinaryOp took
// `signed` from the destination local (a `bool`, hence unsigned) for relational
// ops. The signedness of a comparison must come from the OPERAND types. The fix
// derives `signed` via cmp_operand_ty(lhs, rhs) for Eq/Ne/Lt/Le/Gt/Ge, so
// `x < 0` (i32) now lowers to a SIGNED `<` (BvSLt). The negate block is live and
// the byte-derived machine_out computes two's-complement abs.
//
// Spec: signed-abs as two's-complement Ite(x < 0, 0 - x, x). At i32::MIN this
// wraps back to i32::MIN (UB-free), matching the CPU.
#[test]
fn cfg_abs_proven_and_negctrl() {
    let f = author_abs();
    let (code, base) = emit_text(&f);
    let machine_out = symbolic_machine_output(&code, base).expect("abs is loop-free; must execute");

    // PROVEN: byte-derived machine_out == two's-complement signed-abs, for ALL x.
    let neg = Formula::BvSub(Box::new(bv32(0)), Box::new(wn(0)), 32);
    let signed_abs = Formula::Ite(
        Box::new(Formula::BvSLt(Box::new(wn(0)), Box::new(bv32(0)), 32)),
        Box::new(neg),
        Box::new(wn(0)),
    );
    assert!(
        discharge_equal(&machine_out, &signed_abs),
        "abs bytes were NOT proven == two's-complement signed-abs (UNSAT expected)"
    );
    // NEGATIVE CONTROL (anti-vacuity): abs is NOT the identity — it differs on
    // every negative non-MIN input (e.g. x = -5 -> 5). ay must find this SAT.
    assert!(
        !discharge_equal(&machine_out, &wn(0)),
        "VACUITY: abs bytes were 'proven' equal to the identity"
    );
}

// ===========================================================================
// LOOP SAFETY — the executor fails CLOSED on loops, never loops forever, never
// fakes a proof. These exercise the path-merger's backedge detection directly on
// synthetic instruction images.
// ===========================================================================

// A self-branch (B #0) is a 1-instruction loop and MUST fail closed.
#[test]
fn loop_is_skipped_not_faked() {
    // 0x0000: 0x14000000  B #0  (backward branch to self).
    let code: Vec<u8> = vec![0x00, 0x00, 0x00, 0x14];
    let out = symbolic_machine_output(&code, 0);
    assert!(
        matches!(out, Err(ExecError::Loop { .. })),
        "a self-branch loop must FAIL CLOSED (ExecError::Loop), got {out:?}"
    );
}

// A forward-only branch image (B #4 then RET) is a DAG and must execute to RET —
// guards against over-eager backedge rejection.
#[test]
fn forward_branch_is_not_a_loop() {
    // 0x0000: 0x14000001  B #4 (forward to 0x0004)
    // 0x0004: 0xd65f03c0  RET
    let code: Vec<u8> = vec![0x01, 0x00, 0x00, 0x14, 0xc0, 0x03, 0x5f, 0xd6];
    let out = symbolic_machine_output(&code, 0);
    assert!(out.is_ok(), "forward B then RET must execute to RET, got {out:?}");
}
