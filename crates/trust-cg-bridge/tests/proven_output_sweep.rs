// proven_output_sweep.rs — SIGN-SENSITIVE OPERATION SURFACE SWEEP via proven-output.
//
// This rung systematically sweeps the operations where SIGNEDNESS matters in
// lowering — exactly where the signed-comparison miscompile hid (trust-cg
// lowered all signed relational comparisons as UNSIGNED, taking signedness
// from the bool destination instead of the operands; fixed at
// crates/trust-cg-bridge/src/lower.rs:2942-2947).
//
// For EACH sign-sensitive op we prove the BYTE-DERIVED machine output equals the
// CORRECT intended IR spec (correct signedness) for ALL inputs via ay:
//
//   * integer comparisons Lt/Le/Gt/Ge/Eq/Ne, BOTH i32-signed (BvSLt/BvSLe/...)
//     AND u32-unsigned (BvULt/BvULe/...) — confirm the fix made signed correct
//     AND unsigned still correct.
//   * AShr (i32 >>, arithmetic) vs LShr (u32 >>, logical).
//   * Neg (i32 two's-complement).
//   * SDiv/UDiv/SRem/URem (with a `b != 0` precondition; AArch64 div-by-zero is
//     modeled as 0, so the precondition isolates the signed/unsigned semantics).
//   * SExt/ZExt/Trunc casts (i8->i32, u8->u32, i16->i64, u16->u64, i64->i32).
//
// ANTI-VACUITY (load-bearing): machine_out is derived ONLY from the EMITTED
// BYTES (emit -> macho_text -> decode -> Aarch64Semantics::effects ->
// apply_effects -> read_gpr). We NEVER reconstruct it from the IR. EVERY
// positive certificate ships a NEGATIVE CONTROL — a WRONG spec (typically the
// opposite-signedness variant) discharged against the SAME emitted bytes that
// ay must return SAT on. A positive whose negctrl is not SAT is VACUOUS and
// the test fails loudly.
//
// PROTOCOL on a SAT vs the intended spec: that is a CANDIDATE miscompile and
// would require CPU confirmation (route-b link+execute) before being claimed.
// In this sweep, every intended-spec discharge that completed came back UNSAT
// (PROVEN); the negative controls (intentional SAT) are the only SAT results,
// and they are expected. NO sign-related trust-cg miscompile was found: the
// earlier signed-comparison fix is confirmed (all i32-signed comparisons prove
// against BvSLt/BvSLe/swapped-BvSLt specs) AND the unsigned variants still prove
// against BvULt/BvULe; shifts, neg, div, and casts all prove with the correct
// signedness.
//
// PROVER/SEMANTICS FIX MADE THIS RUNG (not a trust-cg miscompile): the i16->i64
// and u16->u64 cast certs initially FAILED with an ay SortMismatch (a BvOr over a
// 64-bit and an 80-bit term). Root cause was in trust-machine-sem
// (crates/trust-machine-sem/src/aarch64/mod.rs): `sem_sbfm`/`sem_ubfm` passed the
// full register `width` as the BvSignExt/BvZeroExt amount, but that field is the
// SMT-LIB number of bits ADDED, not the target width — so a 16-bit field extended
// "by 64" produced an 80-bit value. Fixed to `width - field_width` (the
// convention already used by reverse_bytes/load_le_bytes in the same file). After
// the fix both casts PROVE. This was a machine-semantics modeling defect, not a
// codegen miscompile.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![cfg(feature = "ay-proofs")]

use ay::{BigInt, Logic, Solver, Term};
use trust_cg_bridge::codegen_backend::{TrustCgCodegenBackend, TrustCgTargetArch};
use trust_disasm::{Opcode, decode_aarch64};
use trust_machine_sem::{Aarch64Semantics, MachineState, Semantics};
use trust_types::{
    BasicBlock, BinOp, BlockId, Formula, LocalDecl, Operand, Place, Rvalue, Sort, SourceSpan,
    Statement, Terminator, Ty, UnOp, VerifiableBody, VerifiableFunction,
};

// ---------------------------------------------------------------------------
// IR builders.
// ---------------------------------------------------------------------------

fn sp() -> SourceSpan {
    SourceSpan::default()
}

fn wrap(name: &str, body: VerifiableBody) -> VerifiableFunction {
    VerifiableFunction {
        name: name.into(),
        def_path: format!("sweep::{name}"),
        span: sp(),
        body,
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// `name(a: T, b: T) -> T { a <op> b }` — binary op, result type == operand type.
fn make_binop_fn(name: &str, op: BinOp, ty: Ty) -> VerifiableFunction {
    wrap(
        name,
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
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
            return_ty: ty_dummy(),
        },
    )
}

// Used only to fill return_ty; replaced per-call below. (return_ty is set
// explicitly in each builder; this is just a placeholder to keep one helper.)
fn ty_dummy() -> Ty {
    Ty::i32()
}

/// `name(a: T, b: T) -> bool { a <cmp> b }` — comparison, result bool (W0 = 0/1).
fn make_cmp_fn(name: &str, op: BinOp, ty: Ty) -> VerifiableFunction {
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

/// `name(a: T) -> T { -a }` — unary negation.
fn make_neg_fn(name: &str, ty: Ty) -> VerifiableFunction {
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

/// `name(a: SRC) -> DST { a as DST }` — int-to-int cast (extend or truncate).
fn make_cast_fn(name: &str, src: Ty, dst: Ty) -> VerifiableFunction {
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

// Fix up return_ty for the binop builder (it sets a dummy). We re-build with
// the real type via a thin wrapper to keep call sites readable.
fn binop_fn(name: &str, op: BinOp, ty: Ty) -> VerifiableFunction {
    let mut f = make_binop_fn(name, op, ty.clone());
    f.body.return_ty = ty;
    f
}

// ---------------------------------------------------------------------------
// Emit via trust-cg (host triple; Mach-O on apple).
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

// ---------------------------------------------------------------------------
// Symbolic execution of the EMITTED BYTES (straight-line; threads effects).
// ---------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------
// Formula -> ay::Term translation. Union of the suite + cfg_mem translators,
// EXTENDED with the division/remainder variants the div/rem semantics emit
// (BvSDiv/BvUDiv/BvSRem/BvURem) and the comparison + Ite shapes the
// comparison/div semantics emit.
// ---------------------------------------------------------------------------

fn sort_width(sort: &Sort) -> u32 {
    match sort {
        Sort::BitVec(w) => *w,
        other => panic!("unexpected non-bitvector Var sort in machine output: {other:?}"),
    }
}

fn var_term(solver: &mut Solver, name: &str, sort: &Sort) -> Term {
    match sort {
        Sort::BitVec(w) => solver.bv_var(name, *w),
        Sort::Bool => solver.bool_var(name),
        other => panic!("unexpected Var sort in machine output for {name}: {other:?}"),
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

fn formula_to_term(solver: &mut Solver, f: &Formula) -> Term {
    match f {
        Formula::Var(name, sort) => var_term(solver, name, sort),
        Formula::Bool(b) => solver.bool_const(*b),
        Formula::BitVec { value, width } => solver
            .try_bv_const_bigint(&BigInt::from(*value), *width)
            .expect("bv const"),
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
        // ---- Division / remainder (signed + unsigned) ----
        Formula::BvUDiv(a, b, _) => bin2(solver, a, b, Solver::try_bvudiv),
        Formula::BvSDiv(a, b, _) => bin2(solver, a, b, Solver::try_bvsdiv),
        Formula::BvURem(a, b, _) => bin2(solver, a, b, Solver::try_bvurem),
        Formula::BvSRem(a, b, _) => bin2(solver, a, b, Solver::try_bvsrem),
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
        // ---- Bitvector comparisons (result Bool) ----
        Formula::BvULt(a, b, _) => bin2(solver, a, b, Solver::try_bvult),
        Formula::BvULe(a, b, _) => bin2(solver, a, b, Solver::try_bvule),
        Formula::BvSLt(a, b, _) => bin2(solver, a, b, Solver::try_bvslt),
        Formula::BvSLe(a, b, _) => bin2(solver, a, b, Solver::try_bvsle),
        // ---- Boolean connectives ----
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

// ---------------------------------------------------------------------------
// Discharge `machine_out == ir_out` over ALL inputs (optionally under a
// precondition, e.g. divisor != 0) via ay.
//
//   - UNSAT of (precond AND NOT(machine==ir)) => equality holds for every input
//     satisfying precond => true (PROVEN).
//   - SAT                                     => a counterexample exists => false.
// ---------------------------------------------------------------------------

fn discharge_equal_pre(machine_out: &Formula, ir_out: &Formula, pre: Option<&Formula>) -> bool {
    let mut solver = Solver::try_new(Logic::QfBv).expect("ay Solver::try_new");
    let lhs = formula_to_term(&mut solver, machine_out);
    let rhs = formula_to_term(&mut solver, ir_out);
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

fn prove(func: &VerifiableFunction, ir_spec: &Formula, out_width: u32) -> Verdict {
    prove_pre(func, ir_spec, out_width, None)
}

fn prove_pre(
    func: &VerifiableFunction,
    ir_spec: &Formula,
    out_width: u32,
    pre: Option<&Formula>,
) -> Verdict {
    let (code, base) = emit_text(func);
    assert!(!code.is_empty(), "emitted __text is empty for {}", func.name);
    let machine_out = symbolic_machine_output(&code, base, out_width);
    if discharge_equal_pre(&machine_out, ir_spec, pre) {
        Verdict::Proven
    } else {
        Verdict::CounterExample
    }
}

// ---------------------------------------------------------------------------
// IR-spec helpers. W_n = low 32 bits of arg register X_n; X_n = full 64 bits.
// ---------------------------------------------------------------------------

fn xn(n: u32) -> Formula {
    Formula::Var(format!("X{n}"), Sort::BitVec(64))
}

fn wn(n: u32) -> Formula {
    Formula::BvExtract { inner: Box::new(xn(n)), high: 31, low: 0 }
}

fn bv(value: i128, width: u32) -> Formula {
    Formula::BitVec { value, width }
}

fn b(f: Formula) -> Box<Formula> {
    Box::new(f)
}

fn cmp(op: fn(Box<Formula>, Box<Formula>, u32) -> Formula, a: Formula, c: Formula) -> Formula {
    op(b(a), b(c), 32)
}

/// `if pred then 1bv32 else 0bv32` — comparison result lands in W0 as 0/1.
fn pred_to_i32(pred: Formula) -> Formula {
    Formula::Ite(b(pred), b(bv(1, 32)), b(bv(0, 32)))
}

/// AArch64 32-bit variable shift masks the amount to its low 5 bits: `amt & 31`.
fn masked_shift_amt(n: u32) -> Formula {
    Formula::BvAnd(b(wn(n)), b(bv(31, 32)), 32)
}

// Signed/unsigned greater-than & greater-or-equal in terms of the available
// Formula comparison variants (no BvSGt/BvSGe variants exist):
//   a >s b  <=>  b <s a              (swap)
//   a >=s b <=>  !(a <s b)
fn sgt(a: Formula, c: Formula) -> Formula {
    cmp(Formula::BvSLt, c, a)
}
fn sge(a: Formula, c: Formula) -> Formula {
    Formula::Not(b(cmp(Formula::BvSLt, a, c)))
}
fn ugt(a: Formula, c: Formula) -> Formula {
    cmp(Formula::BvULt, c, a)
}
fn uge(a: Formula, c: Formula) -> Formula {
    Formula::Not(b(cmp(Formula::BvULt, a, c)))
}

// ===========================================================================
// COMPARISONS — signed (i32) and unsigned (u32). Each comparison lands a 0/1
// in W0 via branchless Subs+Csinc; the byte-derived formula is an Ite over the
// post-Subs NZCV flags. We prove that Ite equals `pred_to_i32(correct spec)`,
// and use the OPPOSITE-SIGNEDNESS predicate as the negative control.
// ===========================================================================

macro_rules! cmp_cert {
    ($test:ident, $name:literal, $op:expr, $ty:expr, $spec:expr, $wrong:expr) => {
        #[test]
        fn $test() {
            let f = make_cmp_fn($name, $op, $ty);
            assert_eq!(
                prove(&f, &pred_to_i32($spec), 32),
                Verdict::Proven,
                concat!($name, ": emitted bytes were not proven to equal the intended (correct-signedness) comparison")
            );
            assert_eq!(
                prove(&f, &pred_to_i32($wrong), 32),
                Verdict::CounterExample,
                concat!("VACUITY: ", $name, " bytes were 'proven' equal to the wrong-signedness comparison")
            );
        }
    };
}

// ---- Lt ----
cmp_cert!(cmp_i32_slt, "i32_slt", BinOp::Lt, Ty::i32(), cmp(Formula::BvSLt, wn(0), wn(1)), cmp(Formula::BvULt, wn(0), wn(1)));
cmp_cert!(cmp_u32_ult, "u32_ult", BinOp::Lt, Ty::u32(), cmp(Formula::BvULt, wn(0), wn(1)), cmp(Formula::BvSLt, wn(0), wn(1)));

// ---- Le ----
cmp_cert!(cmp_i32_sle, "i32_sle", BinOp::Le, Ty::i32(), cmp(Formula::BvSLe, wn(0), wn(1)), cmp(Formula::BvULe, wn(0), wn(1)));
cmp_cert!(cmp_u32_ule, "u32_ule", BinOp::Le, Ty::u32(), cmp(Formula::BvULe, wn(0), wn(1)), cmp(Formula::BvSLe, wn(0), wn(1)));

// ---- Gt ----
cmp_cert!(cmp_i32_sgt, "i32_sgt", BinOp::Gt, Ty::i32(), sgt(wn(0), wn(1)), ugt(wn(0), wn(1)));
cmp_cert!(cmp_u32_ugt, "u32_ugt", BinOp::Gt, Ty::u32(), ugt(wn(0), wn(1)), sgt(wn(0), wn(1)));

// ---- Ge ----
cmp_cert!(cmp_i32_sge, "i32_sge", BinOp::Ge, Ty::i32(), sge(wn(0), wn(1)), uge(wn(0), wn(1)));
cmp_cert!(cmp_u32_uge, "u32_uge", BinOp::Ge, Ty::u32(), uge(wn(0), wn(1)), sge(wn(0), wn(1)));

// ---- Eq / Ne (signedness-AGNOSTIC: i32 and u32 compile to the same bytes) ----
// Positive: equality. Negative control: inequality. (No signedness flip exists
// for Eq/Ne; the negctrl flips the predicate direction instead.)
#[test]
fn cmp_i32_eq() {
    let f = make_cmp_fn("i32_eq", BinOp::Eq, Ty::i32());
    let spec = cmp_eq(wn(0), wn(1));
    assert_eq!(prove(&f, &pred_to_i32(spec), 32), Verdict::Proven, "i32 eq not proven");
    let wrong = Formula::Not(b(cmp_eq(wn(0), wn(1))));
    assert_eq!(prove(&f, &pred_to_i32(wrong), 32), Verdict::CounterExample, "VACUITY: i32 eq == ne");
}
#[test]
fn cmp_u32_eq() {
    let f = make_cmp_fn("u32_eq", BinOp::Eq, Ty::u32());
    let spec = cmp_eq(wn(0), wn(1));
    assert_eq!(prove(&f, &pred_to_i32(spec), 32), Verdict::Proven, "u32 eq not proven");
    let wrong = Formula::Not(b(cmp_eq(wn(0), wn(1))));
    assert_eq!(prove(&f, &pred_to_i32(wrong), 32), Verdict::CounterExample, "VACUITY: u32 eq == ne");
}
#[test]
fn cmp_i32_ne() {
    let f = make_cmp_fn("i32_ne", BinOp::Ne, Ty::i32());
    let spec = Formula::Not(b(cmp_eq(wn(0), wn(1))));
    assert_eq!(prove(&f, &pred_to_i32(spec), 32), Verdict::Proven, "i32 ne not proven");
    let wrong = cmp_eq(wn(0), wn(1));
    assert_eq!(prove(&f, &pred_to_i32(wrong), 32), Verdict::CounterExample, "VACUITY: i32 ne == eq");
}
#[test]
fn cmp_u32_ne() {
    let f = make_cmp_fn("u32_ne", BinOp::Ne, Ty::u32());
    let spec = Formula::Not(b(cmp_eq(wn(0), wn(1))));
    assert_eq!(prove(&f, &pred_to_i32(spec), 32), Verdict::Proven, "u32 ne not proven");
    let wrong = cmp_eq(wn(0), wn(1));
    assert_eq!(prove(&f, &pred_to_i32(wrong), 32), Verdict::CounterExample, "VACUITY: u32 ne == eq");
}

fn cmp_eq(a: Formula, c: Formula) -> Formula {
    Formula::Eq(b(a), b(c))
}

// ===========================================================================
// RIGHT SHIFTS — arithmetic (i32 AShr) vs logical (u32 LShr). The shift amount
// is masked to low 5 bits by AArch64. The signedness comes from the result
// (== operand) type, so i32 >> must be ASRV (arithmetic) and u32 >> LSRV.
// ===========================================================================

#[test]
fn shr_i32_ashr() {
    let f = binop_fn("i32_ashr", BinOp::Shr, Ty::i32());
    let spec = Formula::BvAShr(b(wn(0)), b(masked_shift_amt(1)), 32);
    assert_eq!(prove(&f, &spec, 32), Verdict::Proven, "i32 >> not proven arithmetic");
    // NEGCTRL: a logical right shift differs whenever the sign bit is set.
    let wrong = Formula::BvLShr(b(wn(0)), b(masked_shift_amt(1)), 32);
    assert_eq!(prove(&f, &wrong, 32), Verdict::CounterExample, "VACUITY: i32 >> == lshr");
}

#[test]
fn shr_u32_lshr() {
    let f = binop_fn("u32_lshr", BinOp::Shr, Ty::u32());
    let spec = Formula::BvLShr(b(wn(0)), b(masked_shift_amt(1)), 32);
    assert_eq!(prove(&f, &spec, 32), Verdict::Proven, "u32 >> not proven logical");
    // NEGCTRL: an arithmetic right shift differs whenever the high bit is set.
    let wrong = Formula::BvAShr(b(wn(0)), b(masked_shift_amt(1)), 32);
    assert_eq!(prove(&f, &wrong, 32), Verdict::CounterExample, "VACUITY: u32 >> == ashr");
}

// ===========================================================================
// NEG — two's-complement negation: `-a == 0 - a`.
// ===========================================================================

#[test]
fn neg_i32() {
    let f = make_neg_fn("i32_neg", Ty::i32());
    let spec = Formula::BvSub(b(bv(0, 32)), b(wn(0)), 32);
    assert_eq!(prove(&f, &spec, 32), Verdict::Proven, "i32 neg not proven (-a == 0 - a)");
    // NEGCTRL: negation is NOT the identity (differs for any a != 0).
    let wrong = wn(0);
    assert_eq!(prove(&f, &wrong, 32), Verdict::CounterExample, "VACUITY: neg == identity");
}

// ===========================================================================
// DIVISION / REMAINDER — signed (SDiv/SRem) vs unsigned (UDiv/URem).
// Precondition `b != 0` (AArch64 div-by-zero yields 0; the precondition isolates
// the signed/unsigned arithmetic). The byte-derived formula is
// `Ite(b==0, 0, BvSDiv/UDiv(a,b))`; under b != 0 it reduces to the divide.
// ===========================================================================

fn divisor_nonzero() -> Formula {
    Formula::Not(b(Formula::Eq(b(wn(1)), b(bv(0, 32)))))
}

#[test]
fn sdiv_i32() {
    let f = binop_fn("i32_sdiv", BinOp::Div, Ty::i32());
    let spec = Formula::BvSDiv(b(wn(0)), b(wn(1)), 32);
    let pre = divisor_nonzero();
    assert_eq!(prove_pre(&f, &spec, 32, Some(&pre)), Verdict::Proven, "i32 / not proven signed");
    // NEGCTRL: unsigned division differs for negative dividends. (Still under b != 0.)
    let wrong = Formula::BvUDiv(b(wn(0)), b(wn(1)), 32);
    assert_eq!(
        prove_pre(&f, &wrong, 32, Some(&pre)),
        Verdict::CounterExample,
        "VACUITY: signed div == unsigned div"
    );
}

#[test]
fn udiv_u32() {
    let f = binop_fn("u32_udiv", BinOp::Div, Ty::u32());
    let spec = Formula::BvUDiv(b(wn(0)), b(wn(1)), 32);
    let pre = divisor_nonzero();
    assert_eq!(prove_pre(&f, &spec, 32, Some(&pre)), Verdict::Proven, "u32 / not proven unsigned");
    let wrong = Formula::BvSDiv(b(wn(0)), b(wn(1)), 32);
    assert_eq!(
        prove_pre(&f, &wrong, 32, Some(&pre)),
        Verdict::CounterExample,
        "VACUITY: unsigned div == signed div"
    );
}

// REMAINDER — now PROVEN (was ignored: native BvSRem/BvURem timed out in ay).
//
// AArch64 lowers `a % b` as `sdiv/udiv` (quotient q) then `msub` (Rd = Ra-Rn*Rm),
// so the byte-derived machine output is `a - q*b` with `q = Ite(b==0,0,div(a,b))`.
// The auto-spec interpreter now ALSO encodes Rem as that exact truncated-division
// identity `a - div(a,b)*b` (see eval_binop in verify_output.rs) rather than as a
// native BvSRem/BvURem. Both sides then share the same structural shape, so ay
// discharges the equality syntactically (UNSAT in <1s) instead of having to prove
// the bit-blasted `bvsrem == a-(a/b)*b` identity that timed out.
//
// The spec/neg-control below mirror the machine's EXACT lowering shape so the
// positive proof is a syntactic `X == X` (UNSAT by congruence, no multiplier
// bit-blasting). The divide-quotient's SIGNEDNESS is load-bearing (it picks
// BvSDiv vs BvUDiv inside the Ite-guarded quotient), so flipping it is a genuine
// wrong-emission and the SAT negative control still fires Refuted.
// `rem_spec(signed)` builds `a - Ite(b==0, 0, a /signed b) * b`.
fn rem_spec(signed: bool) -> Formula {
    let zero = || bv(0, 32);
    let raw_q = if signed {
        Formula::BvSDiv(b(wn(0)), b(wn(1)), 32)
    } else {
        Formula::BvUDiv(b(wn(0)), b(wn(1)), 32)
    };
    let b_is_zero = Formula::Eq(b(wn(1)), b(zero()));
    let q = Formula::Ite(b(b_is_zero), b(zero()), b(raw_q));
    let prod = Formula::BvMul(b(q), b(wn(1)), 32);
    Formula::BvSub(b(wn(0)), b(prod), 32)
}

#[test]
fn srem_i32() {
    let f = binop_fn("i32_srem", BinOp::Rem, Ty::i32());
    let spec = rem_spec(true);
    let pre = divisor_nonzero();
    assert_eq!(prove_pre(&f, &spec, 32, Some(&pre)), Verdict::Proven, "i32 % not proven signed");
    // NEGCTRL: the unsigned-quotient remainder differs for negative dividends.
    // (Still under b != 0.) This is the wrong-signedness msub emission.
    let wrong = rem_spec(false);
    assert_eq!(
        prove_pre(&f, &wrong, 32, Some(&pre)),
        Verdict::CounterExample,
        "VACUITY: signed rem == unsigned rem"
    );
}

#[test]
fn urem_u32() {
    let f = binop_fn("u32_urem", BinOp::Rem, Ty::u32());
    let spec = rem_spec(false);
    let pre = divisor_nonzero();
    assert_eq!(prove_pre(&f, &spec, 32, Some(&pre)), Verdict::Proven, "u32 % not proven unsigned");
    // NEGCTRL: the signed-quotient remainder differs for high-bit-set dividends.
    let wrong = rem_spec(true);
    assert_eq!(
        prove_pre(&f, &wrong, 32, Some(&pre)),
        Verdict::CounterExample,
        "VACUITY: unsigned rem == signed rem"
    );
}

// ===========================================================================
// CASTS — sign-extending (SExt) vs zero-extending (ZExt) vs truncating (Trunc).
// The source byte lives in the low bits of W0 (the arg register); the cast must
// extend with the SOURCE signedness.
// ===========================================================================

// i8 -> i32: sign-extend low byte to 32 bits.
#[test]
fn cast_i8_i32_sext() {
    let f = make_cast_fn("i8_i32", Ty::i8(), Ty::i32());
    let low = Formula::BvExtract { inner: b(wn(0)), high: 7, low: 0 };
    let spec = Formula::BvSignExt(b(low.clone()), 24);
    assert_eq!(prove(&f, &spec, 32), Verdict::Proven, "i8->i32 not proven sign-extend");
    // NEGCTRL: zero-extending the low byte differs when bit 7 is set.
    let wrong = Formula::BvZeroExt(b(low), 24);
    assert_eq!(prove(&f, &wrong, 32), Verdict::CounterExample, "VACUITY: i8->i32 == zext");
}

// u8 -> u32: zero-extend low byte to 32 bits.
#[test]
fn cast_u8_u32_zext() {
    let f = make_cast_fn("u8_u32", Ty::u8(), Ty::u32());
    let low = Formula::BvExtract { inner: b(wn(0)), high: 7, low: 0 };
    let spec = Formula::BvZeroExt(b(low.clone()), 24);
    assert_eq!(prove(&f, &spec, 32), Verdict::Proven, "u8->u32 not proven zero-extend");
    let wrong = Formula::BvSignExt(b(low), 24);
    assert_eq!(prove(&f, &wrong, 32), Verdict::CounterExample, "VACUITY: u8->u32 == sext");
}

// i16 -> i64: sign-extend low 16 bits to 64 bits.
#[test]
fn cast_i16_i64_sext() {
    let f = make_cast_fn("i16_i64", Ty::i16(), Ty::i64());
    let low = Formula::BvExtract { inner: b(xn(0)), high: 15, low: 0 };
    let spec = Formula::BvSignExt(b(low.clone()), 48);
    assert_eq!(prove(&f, &spec, 64), Verdict::Proven, "i16->i64 not proven sign-extend");
    let wrong = Formula::BvZeroExt(b(low), 48);
    assert_eq!(prove(&f, &wrong, 64), Verdict::CounterExample, "VACUITY: i16->i64 == zext");
}

// u16 -> u64: zero-extend low 16 bits to 64 bits.
#[test]
fn cast_u16_u64_zext() {
    let f = make_cast_fn("u16_u64", Ty::u16(), Ty::u64());
    let low = Formula::BvExtract { inner: b(xn(0)), high: 15, low: 0 };
    let spec = Formula::BvZeroExt(b(low.clone()), 48);
    assert_eq!(prove(&f, &spec, 64), Verdict::Proven, "u16->u64 not proven zero-extend");
    let wrong = Formula::BvSignExt(b(low), 48);
    assert_eq!(prove(&f, &wrong, 64), Verdict::CounterExample, "VACUITY: u16->u64 == sext");
}

// i64 -> i32: truncate to low 32 bits (signedness-agnostic for truncation).
#[test]
fn cast_i64_i32_trunc() {
    let f = make_cast_fn("i64_i32", Ty::i64(), Ty::i32());
    let spec = Formula::BvExtract { inner: b(xn(0)), high: 31, low: 0 };
    assert_eq!(prove(&f, &spec, 32), Verdict::Proven, "i64->i32 not proven truncation");
    // NEGCTRL: the result is NOT the high 32 bits.
    let wrong = Formula::BvExtract { inner: b(xn(0)), high: 63, low: 32 };
    assert_eq!(prove(&f, &wrong, 32), Verdict::CounterExample, "VACUITY: i64->i32 == high half");
}
