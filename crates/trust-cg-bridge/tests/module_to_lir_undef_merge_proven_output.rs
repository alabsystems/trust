// module_to_lir_undef_merge_proven_output.rs — the "trust-ir first" codegen
// seam, proven over the REAL VF -> trust_ir::Module representation of a
// control-flow merge: the one the producer
// (`trust-ir-bridge::lower::lower_to_trust_ir_functions`) actually emits, which
// joins the two arms through a STACK SLOT seeded with `Inst::Undef` — NOT
// through block params.
//
// GOAL: take a `trust_ir::Module` for
//
//     fn mx(a: i32, b: i32) -> i32 { if a > b { a } else { b } }
//
// in the EXACT shape the VF->Module lowering produces for the diamond
// (confirmed by dumping `lower_to_trust_ir` on the corresponding MIR):
//
//   bb0(a, b):
//     %4 = undef i32                 ; the cross-block-merge SEED (poison)
//     %5 = alloca i32                ; the joined-local stack slot
//     store %4 -> *%5                ; seed store (poison; dead)
//     %6 = icmp sgt a, b
//     %7 = const true : bool
//     %8 = icmp eq %6, %7
//     condbr %8 -> bb1 else bb2
//   bb1:  %9  = copy a ; store %9  -> *%5 ; br bb3   ; OVERWRITES the slot
//   bb2:  %10 = copy b ; store %10 -> *%5 ; br bb3   ; OVERWRITES the slot
//   bb3:  %11 = load *%5 ; return %11               ; the join read
//
// The MERGE flows through MEMORY, and the slot is seeded with `Inst::Undef`.
// Under the RATIFIED trust-ir poison semantics (`ub-numerics-policy.md` §4:
// `Undef` is a poison value; only READING poison into a strict op or BRANCHING
// on it is UB), that seed is overwritten on every arm before the only `Load`,
// so it is a DEAD store — never observed. The converter's dead-Undef-seed
// analysis (`analyze_dead_undef_seeds`) proves exactly this and lowers the seed
// to a defined `Iconst 0` whose Store is dead; the merge value is the real
// loaded `a`/`b`.
//
// We prove the emitted machine bytes compute signed-max(a,b) for ALL inputs:
//
//   (1) the Module REALLY contains `Inst::Undef` (we are testing the real
//       VF->Module shape, not a block-param stand-in);
//   (2) PROVEN-OUTPUT (infinite domain): the emitted bytes are decoded into
//       machine effects (NOT reconstructed from the IR), the Str/Ldr through the
//       slot become array-theory Store/Select over the symbolic MEM, path-merged
//       at the B.cond into a symbolic output Formula; ay proves that Formula
//       equals signed-max(a,b) for ALL inputs (UNSAT of the negation);
//   (3) NEGATIVE CONTROL: the SAME bytes proven against a MIN spec MUST be SAT;
//   (4) BYTE-DERIVED VALUE-DIFFERENTIAL: pinning X0=3,X1=2 the machine output is
//       provably 3, and pinning X0=2,X1=5 it is provably 5 — a concrete check on
//       the REAL bytes. (The trust-ir reference interpreter CANNOT serve as the
//       value oracle here: it rejects `Inst::Undef` EAGERLY as UB — a documented
//       interpreter limitation, not a semantics relaxation — so it traps on this
//       Module regardless of input. The byte-derived check is the sound oracle.)
//   (5) a real B.cond is present in the emitted bytes.
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

use trust_ir::inst::{ICmpOp, Inst};
use trust_ir::node::InstrNode;
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{Block, Constant, Function as IrFunction, Module};

// ---------------------------------------------------------------------------
// Build the REAL VF->Module shape for `mx(a,b) = if a>b {a} else {b}`: the
// memory-merge form with an `Inst::Undef` slot seed. `op` selects the compare
// (Sgt for max). `eq_true` reproduces the producer's `icmp eq <cmp>, true`
// SwitchInt-discriminant idiom so the then-arm is taken exactly when `a > b`.
// ---------------------------------------------------------------------------

fn make_undef_merge_module(name: &str, op: ICmpOp) -> Module {
    let mut module = Module::new("undef_merge_module");
    module.func_types.push(FuncTy {
        params: vec![Ty::I32, Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut function = IrFunction::new(FuncId::new(0), name, FuncTyId::new(0), BlockId::new(0));

    let a = ValueId::new(0);
    let b = ValueId::new(1);
    let seed = ValueId::new(4); // %4 = undef i32
    let slot = ValueId::new(5); // %5 = alloca i32
    let cmp = ValueId::new(6); // %6 = icmp sgt a, b
    let tru = ValueId::new(7); // %7 = const true
    let disc = ValueId::new(8); // %8 = icmp eq %6, %7
    let then_v = ValueId::new(9); // %9 = copy a
    let else_v = ValueId::new(10); // %10 = copy b
    let loaded = ValueId::new(11); // %11 = load *%5

    // bb0: undef seed -> slot ; cmp ; condbr.
    let mut bb0 = Block::new(BlockId::new(0));
    bb0.params.push((a, Ty::I32));
    bb0.params.push((b, Ty::I32));
    bb0.body.push(InstrNode::new(Inst::Undef { ty: Ty::I32 }).with_result(seed));
    bb0.body.push(
        InstrNode::new(Inst::Alloca { ty: Ty::I32, count: None, align: None }).with_result(slot),
    );
    bb0.body.push(InstrNode::new(Inst::Store {
        ty: Ty::I32,
        ptr: slot,
        value: seed,
        volatile: false,
        align: None,
    }));
    bb0.body
        .push(InstrNode::new(Inst::ICmp { op, ty: Ty::I32, lhs: a, rhs: b }).with_result(cmp));
    bb0.body.push(
        InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) }).with_result(tru),
    );
    bb0.body.push(
        InstrNode::new(Inst::ICmp { op: ICmpOp::Eq, ty: Ty::Bool, lhs: cmp, rhs: tru })
            .with_result(disc),
    );
    bb0.body.push(InstrNode::new(Inst::CondBr {
        cond: disc,
        then_target: BlockId::new(1),
        then_args: vec![],
        else_target: BlockId::new(2),
        else_args: vec![],
    }));

    // bb1: %9 = copy a ; store %9 -> *%5 ; br bb3.
    let mut bb1 = Block::new(BlockId::new(1));
    bb1.body
        .push(InstrNode::new(Inst::Copy { ty: Ty::I32, operand: a }).with_result(then_v));
    bb1.body.push(InstrNode::new(Inst::Store {
        ty: Ty::I32,
        ptr: slot,
        value: then_v,
        volatile: false,
        align: None,
    }));
    bb1.body.push(InstrNode::new(Inst::Br { target: BlockId::new(3), args: vec![] }));

    // bb2: %10 = copy b ; store %10 -> *%5 ; br bb3.
    let mut bb2 = Block::new(BlockId::new(2));
    bb2.body
        .push(InstrNode::new(Inst::Copy { ty: Ty::I32, operand: b }).with_result(else_v));
    bb2.body.push(InstrNode::new(Inst::Store {
        ty: Ty::I32,
        ptr: slot,
        value: else_v,
        volatile: false,
        align: None,
    }));
    bb2.body.push(InstrNode::new(Inst::Br { target: BlockId::new(3), args: vec![] }));

    // bb3: %11 = load *%5 ; return %11.
    let mut bb3 = Block::new(BlockId::new(3));
    bb3.body.push(
        InstrNode::new(Inst::Load { ty: Ty::I32, ptr: slot, volatile: false, align: None })
            .with_result(loaded),
    );
    bb3.body.push(InstrNode::new(Inst::Return { values: vec![loaded] }));

    function.blocks.push(bb0);
    function.blocks.push(bb1);
    function.blocks.push(bb2);
    function.blocks.push(bb3);
    module.functions.push(function);
    module
}

/// max(a,b) = if a > b { a } else { b }, via the Undef-seeded memory merge.
fn make_undef_max_module() -> Module {
    make_undef_merge_module("ir_undef_max", ICmpOp::Sgt)
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

fn emit_module_text(module: &Module) -> (Vec<u8>, u64) {
    let function = &module.functions[0];
    let lir = lower_trust_ir_function_to_lir(module, function)
        .expect("lower_module_to_lir failed for the Undef-seeded memory merge");
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
// BOUNDED SYMBOLIC PATH-MERGING EXECUTOR over MEMORY (QF_ABV).
//
// Decode the EMITTED BYTES. Execute straight-line effects through a symbolic
// MachineState (whose MEM is a symbolic array) until a RET (returns W0) or a
// ConditionalBranch (FORK). Str/Ldr become array-theory Store/Select over MEM.
// Loops / calls / atomics / indirect branches fail closed.
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
                        return Err(ExecError::Unsupported(format!("Call at {pc:#x}")));
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
                let taken = self.run(target_pc, state.clone(), visited.clone(), depth + 1)?;
                let fall = self.run(fall_pc, state.clone(), visited.clone(), depth + 1)?;
                return Ok(Formula::Ite(Box::new(path_cond), Box::new(taken), Box::new(fall)));
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

fn const_addr(f: &Formula) -> Option<u64> {
    match f {
        Formula::BitVec { value, .. } => Some(*value as u64),
        _ => None,
    }
}

fn symbolic_machine_output(code: &[u8], base: u64) -> Result<Formula, ExecError> {
    let mut exec = Executor::new(code, base);
    let state = MachineState::symbolic();
    exec.run(base, state, Vec::new(), 0)
}

// ---------------------------------------------------------------------------
// Formula -> ay::Term translation (QF_ABV: includes array Store/Select).
// ---------------------------------------------------------------------------

fn var_term(solver: &mut Solver, name: &str, sort: &Sort) -> Term {
    match sort {
        Sort::BitVec(w) => solver.bv_var(name, *w),
        Sort::Bool => solver.bool_var(name),
        Sort::Array(idx, elem) => {
            let (Sort::BitVec(iw), Sort::BitVec(ew)) = (idx.as_ref(), elem.as_ref()) else {
                panic!("unsupported array sort for Var {name}: {sort:?}");
            };
            solver.declare_const(name, ay::Sort::array(ay::Sort::bitvec(*iw), ay::Sort::bitvec(*ew)))
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

/// Discharge `machine_out == ir_out` over ALL inputs via ay. UNSAT of the
/// negation == proven-equal.
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

/// signed-max(a,b) == (b <=s a) ? a : b.
fn signed_max_spec() -> Formula {
    Formula::Ite(
        Box::new(Formula::BvSLe(Box::new(wn(1)), Box::new(wn(0)), 32)),
        Box::new(wn(0)),
        Box::new(wn(1)),
    )
}

/// signed-min(a,b) == (a <=s b) ? a : b. The MIN spec is the negative control.
fn signed_min_spec() -> Formula {
    Formula::Ite(
        Box::new(Formula::BvSLe(Box::new(wn(0)), Box::new(wn(1)), 32)),
        Box::new(wn(0)),
        Box::new(wn(1)),
    )
}

// ===========================================================================
// TEST 0 — the Module REALLY contains `Inst::Undef` (we are testing the real
// VF->Module memory-merge shape, not a block-param stand-in).
// ===========================================================================

#[test]
fn module_uses_real_undef_seed_merge() {
    let module = make_undef_max_module();
    let f = &module.functions[0];
    let undefs = f
        .blocks
        .iter()
        .flat_map(|b| &b.body)
        .filter(|n| matches!(n.inst, Inst::Undef { .. }))
        .count();
    assert_eq!(undefs, 1, "the real VF->Module merge must seed the slot with exactly one Undef");
    // And the merge is through memory: an Alloca + >=2 Stores + a Load.
    let allocas = f.blocks.iter().flat_map(|b| &b.body).filter(|n| matches!(n.inst, Inst::Alloca { .. })).count();
    let stores = f.blocks.iter().flat_map(|b| &b.body).filter(|n| matches!(n.inst, Inst::Store { .. })).count();
    let loads = f.blocks.iter().flat_map(|b| &b.body).filter(|n| matches!(n.inst, Inst::Load { .. })).count();
    assert_eq!(allocas, 1, "one stack slot");
    assert_eq!(stores, 3, "seed store + two arm overwrites");
    assert_eq!(loads, 1, "one join load");
}

// ===========================================================================
// TEST 1 — the converter lowers the Undef-seeded merge and emits an object
// with a real conditional branch.
// ===========================================================================

#[test]
fn module_to_lir_emits_object_for_undef_merge_max() {
    let module = make_undef_max_module();
    let (code, base) = emit_module_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty for Undef-merge max");
    let mut saw_bcond = false;
    let mut pc = base;
    while (pc - base) as usize + 4 <= code.len() {
        let off = (pc - base) as usize;
        let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
        if let Ok(insn) = decode_aarch64(&bytes, pc) {
            if matches!(insn.opcode, Opcode::BCond) {
                saw_bcond = true;
                break;
            }
        }
        pc += 4;
    }
    assert!(saw_bcond, "expected a conditional branch in the emitted Undef-merge max() bytes");
}

// ===========================================================================
// TEST 2 — PROVEN OUTPUT (infinite domain): the emitted bytes of the
// Undef-seeded memory-merge max() compute signed-max(a,b) for ALL inputs.
// ===========================================================================

#[test]
fn undef_merge_max_bytes_compute_signed_max_for_all_inputs() {
    let module = make_undef_max_module();
    let (code, base) = emit_module_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty");

    let machine_out = symbolic_machine_output(&code, base)
        .expect("path-merge of the Undef-merge max() bytes failed (loop/unsupported/budget)");
    let spec = signed_max_spec();

    let proven = discharge_equal(&machine_out, &spec);
    assert!(
        proven,
        "PROVEN-OUTPUT FAILED: ay did not prove the Undef-seeded memory-merge max() bytes \
         equal signed-max(a,b) for all inputs.\n  machine_out = {machine_out:?}"
    );
}

// ===========================================================================
// TEST 3 — MANDATORY NEGATIVE CONTROL: the SAME max() bytes proven against the
// MIN spec MUST be SAT, or the positive certificate is vacuous.
// ===========================================================================

#[test]
fn negative_control_undef_merge_max_bytes_vs_min_spec_is_sat() {
    let module = make_undef_max_module();
    let (code, base) = emit_module_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty");

    let machine_out = symbolic_machine_output(&code, base)
        .expect("path-merge of the Undef-merge max() bytes failed");
    let wrong = signed_min_spec(); // deliberately the WRONG spec for max.

    let proven = discharge_equal(&machine_out, &wrong);
    assert!(
        !proven,
        "VACUITY CHECK FAILED: the Undef-merge max() bytes were 'proven' equal to signed-min; \
         the discharge has no teeth.\n  machine_out = {machine_out:?}"
    );
}

// ===========================================================================
// TEST 4 — BYTE-DERIVED VALUE-DIFFERENTIAL. The trust-ir reference interpreter
// rejects `Inst::Undef` eagerly as UB (a documented interpreter limitation; the
// ratified poison semantics treat this dead seed as harmless), so it cannot
// serve as the value oracle. We instead pin the argument registers to concrete
// inputs and prove the REAL machine output equals the expected value.
// ===========================================================================

/// Prove `machine_out == expected` when X0=`a`, X1=`b` (concrete), over the
/// 32-bit low words. UNSAT of `(X0==a AND X1==b AND machine_out != expected)`.
fn concrete_value_is(machine_out: &Formula, a: i64, b: i64, expected: i64) -> bool {
    let mut solver = Solver::try_new(Logic::QfAbv).expect("ay Solver::try_new");
    let out = formula_to_term(&mut solver, machine_out);

    let x0 = solver.bv_var("X0", 64);
    let x1 = solver.bv_var("X1", 64);
    let a_c = solver.try_bv_const_bigint(&BigInt::from(a), 64).expect("a const");
    let b_c = solver.try_bv_const_bigint(&BigInt::from(b), 64).expect("b const");
    let eq0 = solver.try_eq(x0, a_c).expect("eq x0");
    let eq1 = solver.try_eq(x1, b_c).expect("eq x1");

    let exp32 = solver.try_bv_const_bigint(&BigInt::from(expected), 32).expect("exp const");
    let out_eq = solver.try_eq(out, exp32).expect("eq out");
    let out_ne = solver.try_not(out_eq).expect("not");

    let conj = solver.try_and_many(&[eq0, eq1, out_ne]).expect("and");
    solver.try_assert_term(conj).expect("assert");
    solver.check_sat().is_unsat()
}

#[test]
fn undef_merge_max_bytes_concrete_value_differential() {
    let module = make_undef_max_module();
    let (code, base) = emit_module_text(&module);
    let machine_out = symbolic_machine_output(&code, base).expect("path-merge failed");

    // max(3, 2) = 3 ; max(2, 5) = 5 ; max(-5, -1) = -1.
    assert!(concrete_value_is(&machine_out, 3, 2, 3), "max(3,2) must be 3 in the real bytes");
    assert!(concrete_value_is(&machine_out, 2, 5, 5), "max(2,5) must be 5 in the real bytes");
    assert!(concrete_value_is(&machine_out, -5, -1, -1), "max(-5,-1) must be -1 in the real bytes");
}
