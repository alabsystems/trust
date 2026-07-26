// proven_output_autospec.rs — AUTO-DERIVED intended-semantics for proven-output.
//
// THE RUNG (M-POS / general-TV foundation): replace the N HAND-WRITTEN ir_spec
// Formulas in proven_output_suite.rs / _sweep.rs with ONE reusable symbolic
// interpreter, `trust_ir_semantics(func) -> Formula`, that COMPUTES the
// intended-semantics Formula directly from the IR (symbolically over the
// function's AAPCS64 argument registers). This consolidates N trust points into
// ONE checkable interpreter and is the prerequisite for running proven-output as
// an in-codegen GATE over arbitrary (supported-shape) functions.
//
// trust-ir's `interpret` module is CONCRETE (it evaluates a function on concrete
// InterpretValue inputs and returns concrete outputs). It does NOT produce
// Formulas. So this interpreter is a fresh, pure FORMULA BUILDER: it walks the
// VerifiableFunction's straight-line block, threading a symbolic machine state
// (local index -> Formula) through each Statement, and yields the return-value
// Formula over symbolic arg registers X0, X1, ... (W_n = low 32 bits of X_n).
//
// SOUNDNESS / ANTI-CIRCULARITY (load-bearing): the interpreter is now the
// "intended semantics" authority, so it must be VALIDATED. For EVERY op that was
// already proven against a TRUSTED HAND-WRITTEN spec (suite + sweep), we assert
//   trust_ir_semantics(func)  ay-EQUIVALENT  hand_spec      (UNSAT of NOT(==))
// This PINS the interpreter to the already-trusted specs: a wrong interpreter
// (signed/unsigned confusion, missing shift mask, wrong width) FAILS this check
// rather than silently passing. THEN we prove
//   emitted_bytes == trust_ir_semantics(func)                (UNSAT of NOT(==))
// i.e. proven-output now runs against the AUTO-derived intended semantics. A SAT
// negative control (emitted == a deliberately-wrong auto-spec, via a corrupted
// interpreter) confirms the discharge has teeth. Finally we demonstrate
// GENERALITY: prove a fresh function with NO pre-existing hand-spec purely via
// the auto-spec.
//
// SCOPE (honest): the interpreter under validation here is the LIVE LIBRARY
// interpreter `trust_cg_bridge::verify_output::trust_ir_semantics` (imported, not
// duplicated). The op coverage this file VALIDATES against trusted hand-specs is
// integer-only, straight-line scalar functions: BinOp add/sub/mul/and/or/xor/
// shl/shr/div, all ICmp signed+unsigned (Lt/Le/Gt/Ge/Eq/Ne), UnOp Neg, Cast
// SExt/ZExt/Trunc, Const, Use, Return. The library interpreter is a SUPERSET (it
// also handles DAG-CFG multi-block control flow via Ite-merging and deref
// store/load memory, plus a truncated-division Rem encoding) — those extensions
// are exercised by other proven_output_* suites, not re-validated here. The
// interpreter FAILS CLOSED (returns Err) on any shape it does not model (float
// ops, calls, loops/backedges, non-deref projections, etc.) — it never
// fabricates a Formula for a shape it does not model.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![cfg(feature = "ay-proofs")]

use ay::{BigInt, Logic, Solver, Term};
use trust_cg_bridge::codegen_backend::{TrustCgCodegenBackend, TrustCgTargetArch};
// THE INTERPRETER UNDER VALIDATION IS THE LIVE LIBRARY GATE INTERPRETER.
//
// This test file used to carry its OWN near-complete duplicate of the symbolic
// IR-semantics interpreter (`trust_ir_semantics` + eval_binop/eval_cast/
// eval_rvalue/eval_const/mask_shift/SymState/...). That duplicate PREDATED the
// promotion of the interpreter into the library (verify_output.rs) and had
// already DIVERGED (e.g. the library got the truncated-division Rem encoding
// `a - Ite(b==0,0,a/{s}b)*b` while the test copy still emitted native BvSRem),
// so the hand-spec validation below was pinning a STALE COPY, not the gate that
// `trustc` actually runs. The duplicate is now DELETED and we import the LIVE
// library interpreter, so the anti-vacuity / hand-spec validation evidence is
// load-bearing: it constrains exactly the function the in-compiler M-POS gate
// uses as its AUTO-SPEC authority.
use trust_cg_bridge::verify_output::trust_ir_semantics;
use trust_disasm::{Opcode, decode_aarch64};
use trust_machine_sem::{Aarch64Semantics, MachineState, Semantics};
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Rvalue, Sort,
    SourceSpan, Statement, Terminator, Ty, UnOp, VerifiableBody, VerifiableFunction,
};

fn b(f: Formula) -> Box<Formula> {
    Box::new(f)
}

/// Full 64-bit argument register `X_n`.
fn xn(n: u32) -> Formula {
    Formula::Var(format!("X{n}"), Sort::BitVec(64))
}

/// Low 32 bits of argument register `X_n` (i.e. `W_n`).
fn wn(n: u32) -> Formula {
    Formula::BvExtract { inner: b(xn(n)), high: 31, low: 0 }
}

// ===========================================================================
// PART 2 — EMIT + BYTE-DERIVED MACHINE OUTPUT (identical mechanics to suite/sweep).
// machine_out is derived ONLY from the EMITTED BYTES; nothing from the IR enters it.
// ===========================================================================

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

fn symbolic_machine_output(code: &[u8], base: u64, out_width: u32) -> Formula {
    let sem = Aarch64Semantics;
    let mut state = MachineState::symbolic();
    let mut pc = base;
    let mut steps = 0u32;
    loop {
        let off = (pc - base) as usize;
        if off + 4 > code.len() {
            panic!("ran past end of __text without hitting RET");
        }
        let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
        let insn = decode_aarch64(&bytes, pc).expect("decode_aarch64 failed");
        let is_ret = insn.opcode == Opcode::Ret;
        let effects = sem
            .effects(&state, &insn)
            .unwrap_or_else(|e| panic!("Aarch64Semantics::effects failed at {pc:#x}: {e:?}"));
        state.apply_effects(&effects).unwrap_or_else(|e| {
            panic!(
                "apply_effects rejected emitted insn {:?} at {:#x}: {:?}\n  effects = {:?}",
                insn.opcode, pc, e, effects
            )
        });
        steps += 1;
        if is_ret {
            break;
        }
        pc += 4;
        assert!(steps < 1000, "decode loop runaway (no RET)");
    }
    state.read_gpr(0, out_width)
}

// ===========================================================================
// PART 3 — Formula -> ay::Term translation + discharge (union of suite/sweep).
// ===========================================================================

fn var_term(solver: &mut Solver, name: &str, sort: &Sort) -> Term {
    match sort {
        Sort::BitVec(w) => solver.bv_var(name, *w),
        Sort::Bool => solver.bool_var(name),
        other => panic!("unexpected Var sort for {name}: {other:?}"),
    }
}

fn bin2(
    solver: &mut Solver,
    a: &Formula,
    c: &Formula,
    op: fn(&mut Solver, Term, Term) -> Result<Term, ay::SolverError>,
) -> Term {
    let a = formula_to_term(solver, a);
    let c = formula_to_term(solver, c);
    op(solver, a, c).expect("binary op")
}

fn formula_to_term(solver: &mut Solver, f: &Formula) -> Term {
    match f {
        Formula::Var(name, sort) => var_term(solver, name, sort),
        Formula::Bool(v) => solver.bool_const(*v),
        Formula::BitVec { value, width } => solver
            .try_bv_const_bigint(&BigInt::from(*value), *width)
            .expect("bv const"),
        Formula::BvAdd(a, c, _) => bin2(solver, a, c, Solver::try_bvadd),
        Formula::BvSub(a, c, _) => bin2(solver, a, c, Solver::try_bvsub),
        Formula::BvMul(a, c, _) => bin2(solver, a, c, Solver::try_bvmul),
        Formula::BvAnd(a, c, _) => bin2(solver, a, c, Solver::try_bvand),
        Formula::BvOr(a, c, _) => bin2(solver, a, c, Solver::try_bvor),
        Formula::BvXor(a, c, _) => bin2(solver, a, c, Solver::try_bvxor),
        Formula::BvShl(a, c, _) => bin2(solver, a, c, Solver::try_bvshl),
        Formula::BvLShr(a, c, _) => bin2(solver, a, c, Solver::try_bvlshr),
        Formula::BvAShr(a, c, _) => bin2(solver, a, c, Solver::try_bvashr),
        Formula::BvConcat(a, c) => bin2(solver, a, c, Solver::try_bvconcat),
        Formula::BvUDiv(a, c, _) => bin2(solver, a, c, Solver::try_bvudiv),
        Formula::BvSDiv(a, c, _) => bin2(solver, a, c, Solver::try_bvsdiv),
        Formula::BvURem(a, c, _) => bin2(solver, a, c, Solver::try_bvurem),
        Formula::BvSRem(a, c, _) => bin2(solver, a, c, Solver::try_bvsrem),
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
        Formula::BvULt(a, c, _) => bin2(solver, a, c, Solver::try_bvult),
        Formula::BvULe(a, c, _) => bin2(solver, a, c, Solver::try_bvule),
        Formula::BvSLt(a, c, _) => bin2(solver, a, c, Solver::try_bvslt),
        Formula::BvSLe(a, c, _) => bin2(solver, a, c, Solver::try_bvsle),
        Formula::Eq(a, c) => bin2(solver, a, c, Solver::try_eq),
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
        other => panic!("formula_to_term: unhandled Formula variant: {other:?}"),
    }
}

/// UNSAT of `(pre AND NOT(a == b))` => `a == b` for all inputs (PROVEN).
fn discharge_equal_pre(a: &Formula, c: &Formula, pre: Option<&Formula>) -> bool {
    let mut solver = Solver::try_new(Logic::QfBv).expect("ay Solver::try_new");
    let lhs = formula_to_term(&mut solver, a);
    let rhs = formula_to_term(&mut solver, c);
    let eq = solver.try_eq(lhs, rhs).expect("eq");
    let differ = solver.try_not(eq).expect("not");
    let goal = if let Some(p) = pre {
        let p = formula_to_term(&mut solver, p);
        solver.try_and(p, differ).expect("and")
    } else {
        differ
    };
    solver.try_assert_term(goal).expect("assert");
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
}

fn verdict(holds: bool) -> Verdict {
    if holds { Verdict::Proven } else { Verdict::CounterExample }
}

// ===========================================================================
// PART 4 — IR builders (mirrors of the suite/sweep builders).
// ===========================================================================

fn sp() -> SourceSpan {
    SourceSpan::default()
}

fn wrap(name: &str, body: VerifiableBody) -> VerifiableFunction {
    VerifiableFunction {
        name: name.into(),
        def_path: format!("autospec::{name}"),
        span: sp(),
        body,
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn binop_fn(name: &str, op: BinOp, ty: Ty) -> VerifiableFunction {
    wrap(
        name,
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: ty.clone(), name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        op,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: sp(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: ty,
        },
    )
}

fn cmp_fn(name: &str, op: BinOp, ty: Ty) -> VerifiableFunction {
    wrap(
        name,
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::bool_ty(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                LocalDecl { index: 2, ty, name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        op,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: sp(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::bool_ty(),
        },
    )
}

fn neg_fn(name: &str, ty: Ty) -> VerifiableFunction {
    wrap(
        name,
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(1))),
                    span: sp(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: ty,
        },
    )
}

fn cast_fn(name: &str, src: Ty, dst: Ty) -> VerifiableFunction {
    wrap(
        name,
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: dst.clone(), name: None },
                LocalDecl { index: 1, ty: src, name: Some("a".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), dst.clone()),
                    span: sp(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: dst,
        },
    )
}

fn madd_fn() -> VerifiableFunction {
    wrap(
        "autospec_madd",
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::i32(), name: Some("c".into()) },
                LocalDecl { index: 4, ty: Ty::i32(), name: Some("t".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Mul,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: sp(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(4)),
                            Operand::Copy(Place::local(3)),
                        ),
                        span: sp(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 3,
            return_ty: Ty::i32(),
        },
    )
}

// ===========================================================================
// HAND-SPEC helpers (copied from suite/sweep, the TRUSTED reference specs).
// ===========================================================================

fn bv(value: i128, width: u32) -> Formula {
    Formula::BitVec { value, width }
}
fn hand_cmp(op: fn(Box<Formula>, Box<Formula>, u32) -> Formula, a: Formula, c: Formula) -> Formula {
    op(b(a), b(c), 32)
}
fn hand_pred_to_i32(pred: Formula) -> Formula {
    Formula::Ite(b(pred), b(bv(1, 32)), b(bv(0, 32)))
}
fn hand_masked_shift_amt(n: u32) -> Formula {
    Formula::BvAnd(b(wn(n)), b(bv(31, 32)), 32)
}
fn hand_sgt(a: Formula, c: Formula) -> Formula {
    hand_cmp(Formula::BvSLt, c, a)
}
fn hand_sge(a: Formula, c: Formula) -> Formula {
    Formula::Not(b(hand_cmp(Formula::BvSLt, a, c)))
}
fn hand_ugt(a: Formula, c: Formula) -> Formula {
    hand_cmp(Formula::BvULt, c, a)
}
fn hand_uge(a: Formula, c: Formula) -> Formula {
    Formula::Not(b(hand_cmp(Formula::BvULt, a, c)))
}
fn hand_eq(a: Formula, c: Formula) -> Formula {
    Formula::Eq(b(a), b(c))
}

// ===========================================================================
// PART 5 — VALIDATION: auto-spec  ay-EQUIVALENT  hand-spec, for every hand-spec'd
// op. This pins the interpreter to the already-trusted specs. (Anti-circularity.)
// ===========================================================================

/// Assert the interpreter's auto-spec is ay-equivalent to the trusted hand-spec
/// (UNSAT of NOT(auto == hand)), under an optional precondition.
fn assert_auto_equiv_hand(
    func: &VerifiableFunction,
    hand: &Formula,
    pre: Option<&Formula>,
    label: &str,
) {
    let auto = trust_ir_semantics(func)
        .unwrap_or_else(|e| panic!("{label}: interpreter failed closed unexpectedly: {e}"));
    assert!(
        discharge_equal_pre(&auto, hand, pre),
        "{label}: AUTO-spec is NOT ay-equivalent to the trusted hand-spec \
         (interpreter is wrong for this op)\n  auto = {auto:?}\n  hand = {hand:?}"
    );
}

#[test]
fn validate_autospec_equivalent_to_handspecs() {
    // ---- Arithmetic / bitwise (i32), result == operand ----
    assert_auto_equiv_hand(
        &binop_fn("v_add", BinOp::Add, Ty::i32()),
        &Formula::BvAdd(b(wn(0)), b(wn(1)), 32),
        None,
        "add",
    );
    assert_auto_equiv_hand(
        &binop_fn("v_sub", BinOp::Sub, Ty::i32()),
        &Formula::BvSub(b(wn(0)), b(wn(1)), 32),
        None,
        "sub",
    );
    assert_auto_equiv_hand(
        &binop_fn("v_mul", BinOp::Mul, Ty::i32()),
        &Formula::BvMul(b(wn(0)), b(wn(1)), 32),
        None,
        "mul",
    );
    assert_auto_equiv_hand(
        &binop_fn("v_and", BinOp::BitAnd, Ty::i32()),
        &Formula::BvAnd(b(wn(0)), b(wn(1)), 32),
        None,
        "and",
    );
    assert_auto_equiv_hand(
        &binop_fn("v_or", BinOp::BitOr, Ty::i32()),
        &Formula::BvOr(b(wn(0)), b(wn(1)), 32),
        None,
        "or",
    );
    assert_auto_equiv_hand(
        &binop_fn("v_xor", BinOp::BitXor, Ty::i32()),
        &Formula::BvXor(b(wn(0)), b(wn(1)), 32),
        None,
        "xor",
    );
    // ---- Shifts: shl, ashr (i32), lshr (u32) — with masked shift amount ----
    assert_auto_equiv_hand(
        &binop_fn("v_shl", BinOp::Shl, Ty::i32()),
        &Formula::BvShl(b(wn(0)), b(hand_masked_shift_amt(1)), 32),
        None,
        "shl",
    );
    assert_auto_equiv_hand(
        &binop_fn("v_ashr", BinOp::Shr, Ty::i32()),
        &Formula::BvAShr(b(wn(0)), b(hand_masked_shift_amt(1)), 32),
        None,
        "i32 ashr",
    );
    assert_auto_equiv_hand(
        &binop_fn("v_lshr", BinOp::Shr, Ty::u32()),
        &Formula::BvLShr(b(wn(0)), b(hand_masked_shift_amt(1)), 32),
        None,
        "u32 lshr",
    );
    // ---- Neg (i32) ----
    assert_auto_equiv_hand(
        &neg_fn("v_neg", Ty::i32()),
        &Formula::BvSub(b(bv(0, 32)), b(wn(0)), 32),
        None,
        "neg",
    );
    // ---- Comparisons: signed (i32) and unsigned (u32), all 6 ----
    let cmp_cases: &[(&str, BinOp, Ty, Formula)] = &[
        ("i32 slt", BinOp::Lt, Ty::i32(), hand_cmp(Formula::BvSLt, wn(0), wn(1))),
        ("u32 ult", BinOp::Lt, Ty::u32(), hand_cmp(Formula::BvULt, wn(0), wn(1))),
        ("i32 sle", BinOp::Le, Ty::i32(), hand_cmp(Formula::BvSLe, wn(0), wn(1))),
        ("u32 ule", BinOp::Le, Ty::u32(), hand_cmp(Formula::BvULe, wn(0), wn(1))),
        ("i32 sgt", BinOp::Gt, Ty::i32(), hand_sgt(wn(0), wn(1))),
        ("u32 ugt", BinOp::Gt, Ty::u32(), hand_ugt(wn(0), wn(1))),
        ("i32 sge", BinOp::Ge, Ty::i32(), hand_sge(wn(0), wn(1))),
        ("u32 uge", BinOp::Ge, Ty::u32(), hand_uge(wn(0), wn(1))),
        ("i32 eq", BinOp::Eq, Ty::i32(), hand_eq(wn(0), wn(1))),
        ("u32 eq", BinOp::Eq, Ty::u32(), hand_eq(wn(0), wn(1))),
        ("i32 ne", BinOp::Ne, Ty::i32(), Formula::Not(b(hand_eq(wn(0), wn(1))))),
        ("u32 ne", BinOp::Ne, Ty::u32(), Formula::Not(b(hand_eq(wn(0), wn(1))))),
    ];
    for (label, op, ty, pred) in cmp_cases {
        assert_auto_equiv_hand(
            &cmp_fn("v_cmp", *op, ty.clone()),
            &hand_pred_to_i32(pred.clone()),
            None,
            label,
        );
    }
    // ---- Division (signed/unsigned) under divisor != 0 ----
    let pre_nonzero = Formula::Not(b(Formula::Eq(b(wn(1)), b(bv(0, 32)))));
    assert_auto_equiv_hand(
        &binop_fn("v_sdiv", BinOp::Div, Ty::i32()),
        &Formula::BvSDiv(b(wn(0)), b(wn(1)), 32),
        Some(&pre_nonzero),
        "i32 sdiv",
    );
    assert_auto_equiv_hand(
        &binop_fn("v_udiv", BinOp::Div, Ty::u32()),
        &Formula::BvUDiv(b(wn(0)), b(wn(1)), 32),
        Some(&pre_nonzero),
        "u32 udiv",
    );
    // ---- Casts: SExt / ZExt / Trunc ----
    let i8_low = Formula::BvExtract { inner: b(wn(0)), high: 7, low: 0 };
    assert_auto_equiv_hand(
        &cast_fn("v_i8_i32", Ty::i8(), Ty::i32()),
        &Formula::BvSignExt(b(i8_low.clone()), 24),
        None,
        "i8->i32 sext",
    );
    let u8_low = Formula::BvExtract { inner: b(wn(0)), high: 7, low: 0 };
    assert_auto_equiv_hand(
        &cast_fn("v_u8_u32", Ty::u8(), Ty::u32()),
        &Formula::BvZeroExt(b(u8_low), 24),
        None,
        "u8->u32 zext",
    );
    let i16_low = Formula::BvExtract { inner: b(xn(0)), high: 15, low: 0 };
    assert_auto_equiv_hand(
        &cast_fn("v_i16_i64", Ty::i16(), Ty::i64()),
        &Formula::BvSignExt(b(i16_low), 48),
        None,
        "i16->i64 sext",
    );
    let u16_low = Formula::BvExtract { inner: b(xn(0)), high: 15, low: 0 };
    assert_auto_equiv_hand(
        &cast_fn("v_u16_u64", Ty::u16(), Ty::u64()),
        &Formula::BvZeroExt(b(u16_low), 48),
        None,
        "u16->u64 zext",
    );
    assert_auto_equiv_hand(
        &cast_fn("v_i64_i32", Ty::i64(), Ty::i32()),
        &Formula::BvExtract { inner: b(xn(0)), high: 31, low: 0 },
        None,
        "i64->i32 trunc",
    );
    // ---- Composite madd: a*b + c ----
    assert_auto_equiv_hand(
        &madd_fn(),
        &Formula::BvAdd(b(Formula::BvMul(b(wn(0)), b(wn(1)), 32)), b(wn(2)), 32),
        None,
        "madd",
    );
}

/// NEGATIVE CONTROL for the validator: a deliberately WRONG interpreter (reads
/// signedness from the DESTINATION type instead of the operand — exactly the
/// trust-cg miscompile) must NOT be ay-equivalent to the trusted signed hand-spec.
/// If this "passes" equivalence, the validator has no teeth.
fn wrong_interpreter_signed_lt_as_unsigned() -> Formula {
    // Mimic the miscompiled lowering: i32 `<` emitted as UNSIGNED compare.
    hand_pred_to_i32(hand_cmp(Formula::BvULt, wn(0), wn(1)))
}

#[test]
fn validator_has_teeth_wrong_interpreter_fails_equiv() {
    // The CORRECT auto-spec for i32 `<`:
    let f = cmp_fn("neg_slt", BinOp::Lt, Ty::i32());
    let correct_auto = trust_ir_semantics(&f).expect("interpreter");
    let trusted_hand = hand_pred_to_i32(hand_cmp(Formula::BvSLt, wn(0), wn(1)));
    // sanity: correct auto IS equivalent to the trusted signed hand-spec.
    assert!(
        discharge_equal_pre(&correct_auto, &trusted_hand, None),
        "correct auto-spec should equal trusted signed hand-spec"
    );
    // A WRONG interpreter (unsigned for a signed `<`) must FAIL equivalence.
    let wrong = wrong_interpreter_signed_lt_as_unsigned();
    assert!(
        !discharge_equal_pre(&wrong, &trusted_hand, None),
        "VALIDATOR HAS NO TEETH: a wrong (unsigned-for-signed) interpreter was \
         'equivalent' to the trusted signed hand-spec"
    );
}

// ===========================================================================
// PART 6 — AUTO-SPEC PROVEN-OUTPUT: emitted bytes == trust_ir_semantics(func),
// over ALL inputs, for each op. Plus a SAT negative control per family.
// ===========================================================================

/// Prove emitted bytes == auto-derived intended semantics (UNSAT of NOT(==)),
/// optionally under a precondition. `out_width` is the return register width.
fn prove_auto(func: &VerifiableFunction, out_width: u32, pre: Option<&Formula>) -> Verdict {
    let auto = trust_ir_semantics(func)
        .unwrap_or_else(|e| panic!("{}: interpreter failed closed: {e}", func.name));
    let (code, base) = emit_text(func);
    assert!(!code.is_empty(), "emitted __text empty for {}", func.name);
    let machine_out = symbolic_machine_output(&code, base, out_width);
    verdict(discharge_equal_pre(&machine_out, &auto, pre))
}

/// SAT negative control: emitted bytes vs a deliberately-WRONG auto-spec
/// (signedness flipped via a corrupted clone of the func type). Must be CEX.
fn prove_against_formula(
    func: &VerifiableFunction,
    spec: &Formula,
    out_width: u32,
    pre: Option<&Formula>,
) -> Verdict {
    let (code, base) = emit_text(func);
    let machine_out = symbolic_machine_output(&code, base, out_width);
    verdict(discharge_equal_pre(&machine_out, spec, pre))
}

#[test]
fn autospec_proven_output_arith_bitwise() {
    for (label, op, neg) in [
        ("add", BinOp::Add, BinOp::Sub),
        ("sub", BinOp::Sub, BinOp::Add),
        ("mul", BinOp::Mul, BinOp::Add),
        ("and", BinOp::BitAnd, BinOp::BitOr),
        ("or", BinOp::BitOr, BinOp::BitAnd),
        ("xor", BinOp::BitXor, BinOp::BitAnd),
    ] {
        let f = binop_fn(&format!("auto_{label}"), op, Ty::i32());
        assert_eq!(
            prove_auto(&f, 32, None),
            Verdict::Proven,
            "{label}: emitted bytes != auto-spec"
        );
        // negative control: emitted bytes vs the auto-spec of a DIFFERENT op.
        let wrong = trust_ir_semantics(&binop_fn("wrong", neg, Ty::i32())).unwrap();
        assert_eq!(
            prove_against_formula(&f, &wrong, 32, None),
            Verdict::CounterExample,
            "VACUITY: {label} bytes 'proven' equal to a different op's auto-spec"
        );
    }
}

#[test]
fn autospec_proven_output_shifts_neg() {
    // shl
    let f = binop_fn("auto_shl", BinOp::Shl, Ty::i32());
    assert_eq!(prove_auto(&f, 32, None), Verdict::Proven, "shl != auto");
    // i32 ashr
    let f = binop_fn("auto_i32_shr", BinOp::Shr, Ty::i32());
    assert_eq!(prove_auto(&f, 32, None), Verdict::Proven, "i32 >> != auto (ashr)");
    let wrong = trust_ir_semantics(&binop_fn("w", BinOp::Shr, Ty::u32())).unwrap();
    assert_eq!(
        prove_against_formula(&f, &wrong, 32, None),
        Verdict::CounterExample,
        "VACUITY: i32 >> 'proven' equal to u32 >> auto-spec"
    );
    // u32 lshr
    let f = binop_fn("auto_u32_shr", BinOp::Shr, Ty::u32());
    assert_eq!(prove_auto(&f, 32, None), Verdict::Proven, "u32 >> != auto (lshr)");
    // neg
    let f = neg_fn("auto_neg", Ty::i32());
    assert_eq!(prove_auto(&f, 32, None), Verdict::Proven, "neg != auto");
}

#[test]
fn autospec_proven_output_comparisons() {
    // For each comparison: emitted bytes == auto-spec; negative control flips
    // signedness by emitting the auto-spec of the OPPOSITE-signedness function.
    let cases: &[(&str, BinOp, Ty, Ty)] = &[
        ("i32_slt", BinOp::Lt, Ty::i32(), Ty::u32()),
        ("u32_ult", BinOp::Lt, Ty::u32(), Ty::i32()),
        ("i32_sle", BinOp::Le, Ty::i32(), Ty::u32()),
        ("u32_ule", BinOp::Le, Ty::u32(), Ty::i32()),
        ("i32_sgt", BinOp::Gt, Ty::i32(), Ty::u32()),
        ("u32_ugt", BinOp::Gt, Ty::u32(), Ty::i32()),
        ("i32_sge", BinOp::Ge, Ty::i32(), Ty::u32()),
        ("u32_uge", BinOp::Ge, Ty::u32(), Ty::i32()),
    ];
    for (label, op, ty, opp) in cases {
        let f = cmp_fn(label, *op, ty.clone());
        assert_eq!(prove_auto(&f, 32, None), Verdict::Proven, "{label}: bytes != auto");
        // negative control: opposite-signedness auto-spec must be a CEX.
        let wrong = trust_ir_semantics(&cmp_fn("w", *op, opp.clone())).unwrap();
        assert_eq!(
            prove_against_formula(&f, &wrong, 32, None),
            Verdict::CounterExample,
            "VACUITY: {label} bytes 'proven' equal to opposite-signedness auto-spec"
        );
    }
    // Eq / Ne (signedness-agnostic): positive only + direction-flip negctrl.
    for (label, op, flip) in [("i32_eq", BinOp::Eq, BinOp::Ne), ("i32_ne", BinOp::Ne, BinOp::Eq)] {
        let f = cmp_fn(label, op, Ty::i32());
        assert_eq!(prove_auto(&f, 32, None), Verdict::Proven, "{label}: bytes != auto");
        let wrong = trust_ir_semantics(&cmp_fn("w", flip, Ty::i32())).unwrap();
        assert_eq!(
            prove_against_formula(&f, &wrong, 32, None),
            Verdict::CounterExample,
            "VACUITY: {label} bytes 'proven' equal to flipped predicate auto-spec"
        );
    }
}

#[test]
fn autospec_proven_output_div() {
    let pre = Formula::Not(b(Formula::Eq(b(wn(1)), b(bv(0, 32)))));
    // i32 sdiv
    let f = binop_fn("auto_sdiv", BinOp::Div, Ty::i32());
    assert_eq!(prove_auto(&f, 32, Some(&pre)), Verdict::Proven, "i32 / != auto (sdiv)");
    let wrong = trust_ir_semantics(&binop_fn("w", BinOp::Div, Ty::u32())).unwrap();
    assert_eq!(
        prove_against_formula(&f, &wrong, 32, Some(&pre)),
        Verdict::CounterExample,
        "VACUITY: i32 / 'proven' equal to u32 / auto-spec"
    );
    // u32 udiv
    let f = binop_fn("auto_udiv", BinOp::Div, Ty::u32());
    assert_eq!(prove_auto(&f, 32, Some(&pre)), Verdict::Proven, "u32 / != auto (udiv)");
}

#[test]
fn autospec_proven_output_casts() {
    // i8->i32 sext (32-bit return)
    let f = cast_fn("auto_i8_i32", Ty::i8(), Ty::i32());
    assert_eq!(prove_auto(&f, 32, None), Verdict::Proven, "i8->i32 != auto (sext)");
    let wrong = trust_ir_semantics(&cast_fn("w", Ty::u8(), Ty::u32())).unwrap();
    assert_eq!(
        prove_against_formula(&f, &wrong, 32, None),
        Verdict::CounterExample,
        "VACUITY: i8->i32 'proven' equal to u8->u32 auto-spec"
    );
    // u8->u32 zext
    let f = cast_fn("auto_u8_u32", Ty::u8(), Ty::u32());
    assert_eq!(prove_auto(&f, 32, None), Verdict::Proven, "u8->u32 != auto (zext)");
    // i16->i64 sext (64-bit return)
    let f = cast_fn("auto_i16_i64", Ty::i16(), Ty::i64());
    assert_eq!(prove_auto(&f, 64, None), Verdict::Proven, "i16->i64 != auto (sext)");
    // u16->u64 zext
    let f = cast_fn("auto_u16_u64", Ty::u16(), Ty::u64());
    assert_eq!(prove_auto(&f, 64, None), Verdict::Proven, "u16->u64 != auto (zext)");
    // i64->i32 trunc
    let f = cast_fn("auto_i64_i32", Ty::i64(), Ty::i32());
    assert_eq!(prove_auto(&f, 32, None), Verdict::Proven, "i64->i32 != auto (trunc)");
}

#[test]
fn autospec_proven_output_composite_madd() {
    let f = madd_fn();
    assert_eq!(prove_auto(&f, 32, None), Verdict::Proven, "madd != auto (a*b + c)");
}

// ===========================================================================
// PART 7 — GENERALITY: prove functions with NO pre-existing hand-spec, PURELY
// via the auto-spec. The interpreter derives the intended semantics from the IR;
// we never wrote a Formula by hand for these.
// ===========================================================================

/// `f(a, b) = (a & b) + (a ^ b)` — a multi-statement straight-line combination
/// that has no hand-spec anywhere in the suite. Locals: _3 = a&b, _4 = a^b,
/// _0 = _3 + _4.
fn novel_and_xor_sum() -> VerifiableFunction {
    wrap(
        "novel_and_xor_sum",
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::i32(), name: Some("t0".into()) },
                LocalDecl { index: 4, ty: Ty::i32(), name: Some("t1".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::BitAnd,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: sp(),
                    },
                    Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::BitXor,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: sp(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(3)),
                            Operand::Copy(Place::local(4)),
                        ),
                        span: sp(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::i32(),
        },
    )
}

/// `f(a, b) = (a - b) <s 0` — a subtraction feeding a SIGNED comparison against
/// a constant. Locals: _2 = a - b (i32), _0: bool = _2 < 0. Exercises operand
/// threading + signed compare against a constant, with no hand-spec.
fn novel_sub_is_negative() -> VerifiableFunction {
    wrap(
        "novel_sub_is_negative",
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::bool_ty(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::i32(), name: Some("d".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Sub,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: sp(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(3)),
                            Operand::Constant(ConstValue::Uint(0, 32)),
                        ),
                        span: sp(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::bool_ty(),
        },
    )
}

#[test]
fn autospec_generality_novel_functions_no_handspec() {
    // (a & b) + (a ^ b)
    let f = novel_and_xor_sum();
    let auto = trust_ir_semantics(&f).expect("interpreter on novel and_xor_sum");
    // (cross-check the auto-spec is the structurally expected thing — NOT a
    // trusted hand-spec, just a readability sanity check that it matches the IR.)
    assert_eq!(prove_auto(&f, 32, None), Verdict::Proven, "novel (a&b)+(a^b) != auto");
    // negative control: it is NOT a+b in general (well-known: (a&b)+(a^b)=a+b
    // is FALSE — the carry differs; (a&b)+(a^b) actually equals a^b + a&b, and
    // a+b = (a^b) + 2*(a&b)). So emitted bytes vs a+b auto-spec must be a CEX.
    let a_plus_b = trust_ir_semantics(&binop_fn("apb", BinOp::Add, Ty::i32())).unwrap();
    assert_eq!(
        prove_against_formula(&f, &a_plus_b, 32, None),
        Verdict::CounterExample,
        "VACUITY/SANITY: (a&b)+(a^b) bytes 'proven' equal to a+b (they differ by the carry term)"
    );
    let _ = auto;

    // (a - b) <s 0
    let f = novel_sub_is_negative();
    assert_eq!(prove_auto(&f, 32, None), Verdict::Proven, "novel (a-b)<0 != auto");
    // negative control: emitted bytes are NOT the UNSIGNED (a-b) < 0 (which is
    // false for all a,b since unsigned 0 is the minimum... so unsigned `< 0`
    // is constant false). emitted (signed) differs.
    let f_u = wrap(
        "novel_u",
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::bool_ty(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("d".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Sub,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: sp(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(3)),
                            Operand::Constant(ConstValue::Uint(0, 32)),
                        ),
                        span: sp(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::bool_ty(),
        },
    );
    let unsigned_auto = trust_ir_semantics(&f_u).expect("interpreter on unsigned variant");
    assert_eq!(
        prove_against_formula(&f, &unsigned_auto, 32, None),
        Verdict::CounterExample,
        "VACUITY: signed (a-b)<0 bytes 'proven' equal to the unsigned-compare auto-spec"
    );
}

// ===========================================================================
// PART 8 — FAIL-CLOSED: the interpreter must return Err on unsupported shapes,
// never fabricate a Formula.
// ===========================================================================

#[test]
fn interpreter_fails_closed_on_unsupported_shapes() {
    // LOOP / BACKEDGE -> Err. (NOTE: the LIBRARY interpreter is a SUPERSET of the
    // old test-local copy: it added DAG-CFG multi-block support — Goto follows,
    // SwitchInt merges as Ite — so "more than one block" is no longer an
    // unsupported shape by itself. The fail-closed boundary it MUST still hold is
    // a LOOP: a backedge / revisited block must never hang and never fabricate a
    // Formula; it returns Err. A self-Goto is the minimal loop.) This is the
    // honest, library-accurate restatement of the previous "multi-block -> Err"
    // assertion, which pinned the now-deleted single-block-only test copy.
    let mut self_loop = binop_fn("loop", BinOp::Add, Ty::i32());
    self_loop.body.blocks[0].terminator = Terminator::Goto(BlockId(0));
    assert!(
        trust_ir_semantics(&self_loop).is_err(),
        "interpreter must fail closed on a loop/backedge"
    );

    // A two-block backedge (bb0 -> bb1 -> bb0) is also a loop -> Err.
    let mut two_block_loop = binop_fn("loop2", BinOp::Add, Ty::i32());
    two_block_loop.body.blocks[0].terminator = Terminator::Goto(BlockId(1));
    two_block_loop.body.blocks.push(BasicBlock {
        id: BlockId(1),
        stmts: vec![],
        terminator: Terminator::Goto(BlockId(0)),
    });
    assert!(
        trust_ir_semantics(&two_block_loop).is_err(),
        "interpreter must fail closed on a multi-block backedge loop"
    );

    // Float f32/f64 `Add`/`Sub`/`Mul`/`Div` is now SOUNDLY modeled as bit-exact
    // FP (`FpAdd`/… `(RNE, eb/sb)` — see verify_output's BinaryOp arm), so it is
    // NO LONGER a fail-closed shape. Library-accurate restatement of the old
    // blanket "float -> Err" assertion, which predated FP support (mirrors the
    // multi-block -> loop restatement above).
    let float_add = wrap(
        "fadd",
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Float { width: 32 }, name: None },
                LocalDecl { index: 1, ty: Ty::Float { width: 32 }, name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::Float { width: 32 }, name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: sp(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::Float { width: 32 },
        },
    );
    assert!(
        trust_ir_semantics(&float_add).is_ok(),
        "f32 Add is soundly modeled as bit-exact FpAdd, not fail-closed"
    );

    // The fail-closed FLOAT boundary that MUST still hold: a NON-arith float op
    // (Rem / comparisons) is NOT wired to bit-exact FP semantics, so it fails
    // closed -- a wrong/approximate float result is never proven.
    let mut float_rem = float_add.clone();
    if let Statement::Assign { rvalue: Rvalue::BinaryOp(op, ..), .. } =
        &mut float_rem.body.blocks[0].stmts[0]
    {
        *op = BinOp::Rem;
    }
    assert!(
        trust_ir_semantics(&float_rem).is_err(),
        "float Rem is not wired to bit-exact FP semantics -> must fail closed"
    );
}
