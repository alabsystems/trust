// proven_output_cfg_mem.rs — proven-output certificates extending the scalar
// straight-line surface to (a) BRANCHLESS conditionals and (b) MEMORY
// store-then-load roundtrips.
//
// This reuses the proven_output_suite.rs prover MECHANICS verbatim
// (emit -> macho_text -> decode -> Aarch64Semantics effects -> apply_effects ->
// read_gpr(0,32) -> ay discharge of NOT(machine_out == ir_spec)), extending the
// Formula -> ay::Term translator with the variants the conditional/memory
// surface produces: Ite, Select, Store, And/Or (Vec connectives), Bool, the
// signed/unsigned bitvector comparisons, and Var of Bool / Array sort.
//
// SCOPE — what is FEASIBLE for a STRAIGHT-LINE symbolic executor:
//
//   * CONDITIONAL: a comparison `a <cmp> b -> bool` lowers (per recon probe) to
//     `Subs + Csinc` — a BRANCHLESS conditional-select. Csinc is modeled as
//     `Formula::Ite(flag_condition, rn, rm+1)` in Aarch64Semantics::sem_csinc,
//     so machine_out becomes an Ite over the post-Subs symbolic NZCV flags. This
//     is straight-line and dischargeable. We prove the byte-derived Ite equals
//     the matching `Ite(<bv-cmp>, 1, 0)` spec for ALL inputs.
//
//   * MEMORY: `*p = v; *p` (store-then-load roundtrip) lowers to `Str` then
//     `Ldr`, modeled as `Select(Store(MEM, addr, v_bytes), addr)`. ay's array
//     theory (QF_ABV) reduces `Select(Store(a,i,v),i)` to `v`. We prove the
//     loaded value equals the stored value `v` for ALL inputs and ALL initial
//     memories.
//
// DEFERRED — NOT feasible for a straight-line executor (honest residual):
//
//   * max / min / abs / clamp: the recon claimed these were branchless. The
//     empirical probe (probe_lowering.rs) DISPROVES that: with a `SwitchInt`
//     value-selection terminator, trust-cg lowers them to a REAL conditional
//     branch (`Subs + BCond + B`), NOT a Csel. A real CondBr needs symbolic
//     path-merging (join the two successor states with a select on the branch
//     condition), which this straight-line executor does not perform. Proving
//     them soundly is a separate rung; they are SKIPPED here, not faked.
//
// ANTI-VACUITY: machine_out is BYTE-DERIVED (emit -> decode -> effects -> apply),
// never reconstructed from the IR. EVERY positive certificate ships a NEGATIVE
// CONTROL — a WRONG spec discharged against the SAME emitted bytes that ay must
// return SAT on. A positive whose negative control is not SAT is VACUOUS and the
// test fails loudly.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![cfg(feature = "ay-proofs")]

use ay::{BigInt, Logic, Solver, Term};
use trust_cg_bridge::codegen_backend::{TrustCgCodegenBackend, TrustCgTargetArch};
use trust_disasm::{Opcode, decode_aarch64};
use trust_machine_sem::{Aarch64Semantics, MachineState, Semantics};
use trust_types::{
    BasicBlock, BinOp, BlockId, Formula, LocalDecl, Operand, Place, Projection, Rvalue, Sort,
    SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
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
        def_path: format!("cfgmem::{name}"),
        span: sp(),
        body,
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// `name(a: i32, b: i32) -> bool { a <cmp> b }` — a single straight-line block
/// whose terminator is `Return`. The comparison value lands in W0 (0 or 1).
/// trust-cg lowers this to a BRANCHLESS `Subs + Csinc` (verified by probe).
fn make_cmp_fn(name: &str, op: BinOp) -> VerifiableFunction {
    wrap(
        name,
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::bool_ty(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
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

/// `ptr_rw(p: *mut i32, v: i32) -> i32 { *p = v; *p }` — store-then-load
/// roundtrip. p lands in X0, v in W1. Lowers to `Str w1, [..]` then `Ldr w0, [..]`.
fn make_ptr_rw() -> VerifiableFunction {
    let ptr_ty = Ty::RawPtr { mutable: true, pointee: Box::new(Ty::i32()) };
    wrap(
        "mem_ptr_rw",
        VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: ptr_ty, name: Some("p".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("v".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place { local: 1, projections: vec![Projection::Deref] },
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: sp(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Deref],
                        })),
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

// ---------------------------------------------------------------------------
// Emit via trust-cg (host triple).
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

/// Extract the `__text` section bytes + vmaddr from a 64-bit Mach-O object.
fn macho_text(obj: &[u8]) -> Option<(Vec<u8>, u64)> {
    let rd_u32 = |o: usize| -> Option<u32> {
        Some(u32::from_le_bytes(obj.get(o..o + 4)?.try_into().ok()?))
    };
    let rd_u64 = |o: usize| -> Option<u64> {
        Some(u64::from_le_bytes(obj.get(o..o + 8)?.try_into().ok()?))
    };
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
// Symbolic execution of the EMITTED BYTES. Decode each instruction, thread its
// real machine-semantics Effects through a symbolic MachineState. machine_out is
// W0 after RET. Nothing about the source IR enters this Formula.
// ---------------------------------------------------------------------------

fn symbolic_machine_output(code: &[u8], base: u64) -> Formula {
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
                "apply_effects rejected an effect from emitted insn {:?} at {:#x}: {:?}",
                insn.opcode, pc, e
            )
        });

        steps += 1;
        if is_ret {
            break;
        }
        pc += 4;
        assert!(steps < 1000, "decode loop runaway (no RET)");
    }

    state.read_gpr(0, 32)
}

// ---------------------------------------------------------------------------
// Formula -> ay::Term translation. This is the proven_output_suite translator
// EXTENDED with the variants the conditional/memory surface produces:
//   * Ite                       (Csinc/Csel conditional-select)
//   * Select / Store            (Ldr / Str array theory)
//   * And(Vec) / Or(Vec) / Not  (flag-condition connectives)
//   * Bool                      (Al/Nv unconditional conditions)
//   * BvULt/BvULe/BvSLt/BvSLe   (flag-derived comparison predicates)
//   * Var of Bool / Array sort  (NZCV flags, MEM array)
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
        // ---- Bitvector comparisons (result sort Bool) ----
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
        // ---- Conditional (Csinc/Csel) ----
        Formula::Ite(cond, then_v, else_v) => {
            let c = formula_to_term(solver, cond);
            let t = formula_to_term(solver, then_v);
            let e = formula_to_term(solver, else_v);
            solver.try_ite(c, t, e).expect("ite")
        }
        // ---- Arrays (Ldr / Str) ----
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

/// Discharge `machine_out == ir_out` over ALL inputs via ay (QF_ABV, so array
/// theory is available for the memory certificate; pure-bitvector certificates
/// are unaffected).
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
}

fn prove_output_equiv(func: &VerifiableFunction, ir_spec: &Formula) -> Verdict {
    let (code, base) = emit_text(func);
    assert!(!code.is_empty(), "emitted __text is empty for {}", func.name);
    let machine_out = symbolic_machine_output(&code, base);
    if discharge_equal(&machine_out, ir_spec) {
        Verdict::Proven
    } else {
        Verdict::CounterExample
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

/// `if pred then 1bv32 else 0bv32`.
fn pred_to_i32(pred: Formula) -> Formula {
    Formula::Ite(Box::new(pred), Box::new(bv32(1)), Box::new(bv32(0)))
}

// ===========================================================================
// CONDITIONAL CERTIFICATES (branchless Subs + Csinc).
//
// Each comparison function returns 1 (true) or 0 (false) in W0. The emitted
// bytes derive the post-Subs symbolic NZCV flags and a Csinc Ite over them; we
// prove that Ite equals the matching bitvector-comparison spec for ALL inputs,
// with a negative control (the opposite-signedness or opposite-direction
// comparison) that ay must find SAT.
//
// NOTE on signedness: the probe shows trust-cg lowers `BinOp::Ge`/`Lt`/`Eq` on
// i32 via flag conditions that the byte-derived formula reduces to UNSIGNED
// comparisons (BvULt/BvULe etc.). We prove what the BYTES compute (the
// unsigned predicate); the signed predicate is used as the negative control,
// which is exactly the property that distinguishes the two and proves the
// discharge has teeth.
// ===========================================================================

// ---- GE: emitted bytes compute (a >=s b) ? 1 : 0 ----
#[test]
fn cmp_ge_proven_and_negctrl() {
    let f = make_cmp_fn("cfg_ge", BinOp::Ge);
    // PROVEN: byte-derived Csinc Ite == (a >=s b) ? 1 : 0, i.e. !(a <s b) ? 1 : 0.
    // i32 `>=` now lowers to a SIGNED condition code (lower.rs cmp-signedness fix).
    let spec = pred_to_i32(Formula::Not(Box::new(Formula::BvSLt(
        Box::new(wn(0)),
        Box::new(wn(1)),
        32,
    ))));
    assert_eq!(
        prove_output_equiv(&f, &spec),
        Verdict::Proven,
        "ge: emitted Subs+Csinc bytes were not proven to equal (a >=s b ? 1 : 0)"
    );
    // NEGATIVE CONTROL: the bytes are NOT unsigned-ge (differs at a=-1, b=0). SAT.
    let wrong = pred_to_i32(Formula::Not(Box::new(Formula::BvULt(
        Box::new(wn(0)),
        Box::new(wn(1)),
        32,
    ))));
    assert_eq!(
        prove_output_equiv(&f, &wrong),
        Verdict::CounterExample,
        "VACUITY: ge bytes were 'proven' equal to unsigned-ge — discharge has no teeth"
    );
}

// ---- LT: emitted bytes compute (a <s b) ? 1 : 0 ----
#[test]
fn cmp_lt_proven_and_negctrl() {
    let f = make_cmp_fn("cfg_lt", BinOp::Lt);
    // i32 `<` now lowers to a SIGNED condition code (lower.rs cmp-signedness fix).
    let spec = pred_to_i32(Formula::BvSLt(Box::new(wn(0)), Box::new(wn(1)), 32));
    assert_eq!(
        prove_output_equiv(&f, &spec),
        Verdict::Proven,
        "lt: emitted Subs+Csinc bytes were not proven to equal (a <s b ? 1 : 0)"
    );
    // NEGATIVE CONTROL: NOT unsigned-lt. SAT.
    let wrong = pred_to_i32(Formula::BvULt(Box::new(wn(0)), Box::new(wn(1)), 32));
    assert_eq!(
        prove_output_equiv(&f, &wrong),
        Verdict::CounterExample,
        "VACUITY: lt bytes were 'proven' equal to unsigned-lt"
    );
}

// ---- EQ: emitted bytes compute (a == b) ? 1 : 0 ----
#[test]
fn cmp_eq_proven_and_negctrl() {
    let f = make_cmp_fn("cfg_eq", BinOp::Eq);
    let spec = pred_to_i32(Formula::Eq(Box::new(wn(0)), Box::new(wn(1))));
    assert_eq!(
        prove_output_equiv(&f, &spec),
        Verdict::Proven,
        "eq: emitted Subs+Csinc bytes were not proven to equal (a == b ? 1 : 0)"
    );
    // NEGATIVE CONTROL: the bytes are NOT inequality (differs at a == b).
    let wrong = pred_to_i32(Formula::Not(Box::new(Formula::Eq(
        Box::new(wn(0)),
        Box::new(wn(1)),
    ))));
    assert_eq!(
        prove_output_equiv(&f, &wrong),
        Verdict::CounterExample,
        "VACUITY: eq bytes were 'proven' equal to (a != b)"
    );
}

// ===========================================================================
// MEMORY CERTIFICATE: store-then-load roundtrip (Str then Ldr).
//
// `*p = v; *p` lowers to `Str w1, [..]` then `Ldr w0, [..]`. The byte-derived
// machine_out is `Select(Store(MEM, p, v_bytes), p)` (with intervening
// SP-relative frame stores). ay's array theory must reduce this to `v` for ALL
// initial memories, ALL pointers p, and ALL values v. The negative control
// proves the loaded value is NOT v+1.
// ===========================================================================

#[test]
fn mem_store_load_roundtrip_proven_and_negctrl() {
    let f = make_ptr_rw();
    // PROVEN: the value loaded back equals the value stored (v = W1).
    let spec = wn(1);
    assert_eq!(
        prove_output_equiv(&f, &spec),
        Verdict::Proven,
        "mem: store-then-load roundtrip was not proven to return the stored value v for all inputs"
    );
    // NEGATIVE CONTROL: the loaded value is NOT v + 1.
    let wrong = Formula::BvAdd(Box::new(wn(1)), Box::new(bv32(1)), 32);
    assert_eq!(
        prove_output_equiv(&f, &wrong),
        Verdict::CounterExample,
        "VACUITY: store-then-load roundtrip was 'proven' equal to (v + 1)"
    );
}
