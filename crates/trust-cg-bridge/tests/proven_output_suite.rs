// proven_output_suite.rs — infinite-domain proven-output certificates for the
// scalar ALU surface, behind a REUSABLE prover.
//
// This generalizes add_proven_output.rs from one op (add) to the scalar ALU:
// sub, mul, and, or, xor, shl, shr (arithmetic), plus a COMPOSITE certificate
// (a*b + c) that exercises the symbolic executor across a real multi-instruction
// sequence.
//
// MECHANICS (identical to add_proven_output.rs):
//   VerifiableFunction --trust-cg--> object bytes --decode--> Instructions
//        --Aarch64Semantics::effects--> Effect[] --apply_effects-->
//        symbolic MachineState --> read_gpr(0,32) Formula --> ay discharge.
//
// ANTI-VACUITY (load-bearing): the machine-side output Formula is derived ONLY
// from the ACTUAL EMITTED BYTES (emit -> decode -> effects -> apply). We NEVER
// reconstruct the output from the IR. EVERY positive certificate ships a
// NEGATIVE CONTROL: we prove a WRONG spec against the same emitted bytes and
// require ay to return SAT (a counterexample). A positive certificate whose
// negative control is not SAT is VACUOUS and the test fails loudly.
//
// REGISTER MODEL: AArch64 i32 args land in W0, W1, W2, ... (low 32 bits of
// X0, X1, X2). `read_gpr(0, 32)` is the i32 return value. The IR-spec formulas
// below are written over the SAME Var names (X0, X1, X2) the machine output
// uses, so ay quantifies over the same free inputs on both sides.
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
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

// ---------------------------------------------------------------------------
// IR builders.
// ---------------------------------------------------------------------------

/// `name(a: i32, b: i32) -> i32 { a <op> b }`
fn make_binop_fn(name: &str, op: BinOp) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("test::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
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
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// `madd(a: i32, b: i32, c: i32) -> i32 { let t = a * b; t + c }`
///
/// Two statements, so the symbolic executor must COMPOSE across a real
/// multi-instruction sequence (the temp `t` is threaded through the machine
/// state). local(3) holds the product; local(0) holds the final sum.
fn make_madd() -> VerifiableFunction {
    VerifiableFunction {
        name: "proof_madd".to_string(),
        def_path: "test::proof_madd".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
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
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(4)),
                            Operand::Copy(Place::local(3)),
                        ),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 3,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

// ---------------------------------------------------------------------------
// Emit via trust-cg (host triple; Mach-O on apple, ELF on linux).
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
            // LC_SEGMENT_64
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
// Symbolic execution of the EMITTED BYTES.
//
// Decode each 4-byte instruction; obtain its Effects from Aarch64Semantics
// against the CURRENT (threaded) symbolic state, then apply them. The state
// after the loop holds, in W0, a Formula over the initial symbolic inputs
// (X0, X1, ...) that is a pure function of the emitted code — nothing about
// the source IR enters this Formula.
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

        // Effects are derived from the REAL decoded instruction via real machine
        // semantics — not from the IR. This is the anti-vacuity guarantee.
        let effects = sem
            .effects(&state, &insn)
            .unwrap_or_else(|e| panic!("Aarch64Semantics::effects failed at {pc:#x}: {e:?}"));

        // Thread the effects into the post-state. If apply_effects rejects an
        // emitted effect (Unmodeled / BadWidth), surface exactly which one and
        // stop — do NOT fake the result.
        state.apply_effects(&effects).unwrap_or_else(|e| {
            panic!(
                "apply_effects rejected an effect from emitted insn {:?} at {:#x}: {:?}\n  effects = {:?}",
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

    // W0 (low 32 bits of X0) is the AArch64 i32 return value.
    state.read_gpr(0, 32)
}

// ---------------------------------------------------------------------------
// Formula -> ay::Term translation.
//
// Translates whatever Formula the SYMBOLIC EXECUTION produced; it does not
// assume any particular shape. Extends add_proven_output.rs's translator with
// BvXor / BvLShr / BvAShr (needed for the bitwise/shift surface).
// ---------------------------------------------------------------------------

fn sort_width(sort: &Sort) -> u32 {
    match sort {
        Sort::BitVec(w) => *w,
        other => panic!("unexpected non-bitvector Var sort in machine output: {other:?}"),
    }
}

fn formula_to_term(solver: &mut Solver, f: &Formula) -> Term {
    match f {
        Formula::Var(name, sort) => solver.bv_var(name, sort_width(sort)),
        Formula::BitVec { value, width } => solver
            .try_bv_const_bigint(&BigInt::from(*value), *width)
            .expect("bv const"),
        Formula::BvAdd(a, b, _) => {
            let a = formula_to_term(solver, a);
            let b = formula_to_term(solver, b);
            solver.try_bvadd(a, b).expect("bvadd")
        }
        Formula::BvSub(a, b, _) => {
            let a = formula_to_term(solver, a);
            let b = formula_to_term(solver, b);
            solver.try_bvsub(a, b).expect("bvsub")
        }
        Formula::BvMul(a, b, _) => {
            let a = formula_to_term(solver, a);
            let b = formula_to_term(solver, b);
            solver.try_bvmul(a, b).expect("bvmul")
        }
        Formula::BvAnd(a, b, _) => {
            let a = formula_to_term(solver, a);
            let b = formula_to_term(solver, b);
            solver.try_bvand(a, b).expect("bvand")
        }
        Formula::BvOr(a, b, _) => {
            let a = formula_to_term(solver, a);
            let b = formula_to_term(solver, b);
            solver.try_bvor(a, b).expect("bvor")
        }
        Formula::BvXor(a, b, _) => {
            let a = formula_to_term(solver, a);
            let b = formula_to_term(solver, b);
            solver.try_bvxor(a, b).expect("bvxor")
        }
        Formula::BvNot(a, _) => {
            let a = formula_to_term(solver, a);
            solver.try_bvnot(a).expect("bvnot")
        }
        Formula::BvShl(a, b, _) => {
            let a = formula_to_term(solver, a);
            let b = formula_to_term(solver, b);
            solver.try_bvshl(a, b).expect("bvshl")
        }
        Formula::BvLShr(a, b, _) => {
            let a = formula_to_term(solver, a);
            let b = formula_to_term(solver, b);
            solver.try_bvlshr(a, b).expect("bvlshr")
        }
        Formula::BvAShr(a, b, _) => {
            let a = formula_to_term(solver, a);
            let b = formula_to_term(solver, b);
            solver.try_bvashr(a, b).expect("bvashr")
        }
        Formula::BvConcat(a, b) => {
            let a = formula_to_term(solver, a);
            let b = formula_to_term(solver, b);
            solver.try_bvconcat(a, b).expect("bvconcat")
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
        Formula::Eq(a, b) => {
            let a = formula_to_term(solver, a);
            let b = formula_to_term(solver, b);
            solver.try_eq(a, b).expect("eq")
        }
        Formula::Not(a) => {
            let a = formula_to_term(solver, a);
            solver.try_not(a).expect("not")
        }
        other => panic!(
            "formula_to_term: unhandled Formula variant in machine output: {other:?}\n\
             (the symbolic execution produced a shape this harness does not yet translate)"
        ),
    }
}

/// Discharge `machine_out == ir_out` over ALL inputs via ay.
///
///   - UNSAT of NOT(machine_out == ir_out) => equality holds for every input => true (PROVEN).
///   - SAT                                  => a counterexample input exists   => false (DISPROVEN).
fn discharge_equal(machine_out: &Formula, ir_out: &Formula) -> bool {
    let mut solver = Solver::try_new(Logic::QfBv).expect("ay Solver::try_new");

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
// THE REUSABLE PROVER.
//
// Verdict::Proven      <=> emitted bytes' output == ir_spec for ALL inputs.
// Verdict::CounterExample <=> some input makes them differ.
//
// `machine_out` is BYTE-DERIVED (emit -> macho_text -> decode -> threaded
// effects -> apply_effects -> read_gpr(0,32)). It is discharged against the
// caller-supplied `ir_spec` via ay. This is the single point where every
// certificate below routes through.
// ---------------------------------------------------------------------------

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

fn bin(op: fn(Box<Formula>, Box<Formula>, u32) -> Formula, a: Formula, b: Formula) -> Formula {
    op(Box::new(a), Box::new(b), 32)
}

/// AArch64 32-bit variable shifts mask the shift amount to its low 5 bits.
/// The IR spec models this with `amt & 31`.
fn masked_shift_amt(n: u32) -> Formula {
    Formula::BvAnd(
        Box::new(wn(n)),
        Box::new(Formula::BitVec { value: 31, width: 32 }),
        32,
    )
}

// ---------------------------------------------------------------------------
// POSITIVE CERTIFICATES + NEGATIVE CONTROLS, one (op, wrong-op) pair per ALU op.
//
// Each positive test proves the emitted bytes of `name(a,b) = a <op> b` compute
// the matching bitvector spec for ALL 2^64 inputs. Each negative control proves
// a WRONG spec against the SAME emitted bytes and requires SAT (a counterexample),
// confirming the discharge has teeth (non-vacuous).
// ---------------------------------------------------------------------------

// ---- SUB ----
#[test]
fn sub_proven_and_negctrl() {
    let f = make_binop_fn("proof_sub", BinOp::Sub);
    // PROVEN: emitted sub bytes == a - b.
    let spec = bin(Formula::BvSub, wn(0), wn(1));
    assert_eq!(
        prove_output_equiv(&f, &spec),
        Verdict::Proven,
        "sub: emitted bytes were not proven to equal (a - b) for all inputs"
    );
    // NEGATIVE CONTROL: emitted sub bytes are NOT a + b (must be SAT).
    let wrong = bin(Formula::BvAdd, wn(0), wn(1));
    assert_eq!(
        prove_output_equiv(&f, &wrong),
        Verdict::CounterExample,
        "VACUITY: sub bytes were 'proven' equal to (a + b) — discharge has no teeth"
    );
}

// ---- MUL ----
#[test]
fn mul_proven_and_negctrl() {
    let f = make_binop_fn("proof_mul", BinOp::Mul);
    let spec = bin(Formula::BvMul, wn(0), wn(1));
    assert_eq!(
        prove_output_equiv(&f, &spec),
        Verdict::Proven,
        "mul: emitted bytes were not proven to equal (a * b) for all inputs"
    );
    // NEGATIVE CONTROL: mul bytes are NOT a + b.
    let wrong = bin(Formula::BvAdd, wn(0), wn(1));
    assert_eq!(
        prove_output_equiv(&f, &wrong),
        Verdict::CounterExample,
        "VACUITY: mul bytes were 'proven' equal to (a + b)"
    );
}

// ---- AND ----
#[test]
fn and_proven_and_negctrl() {
    let f = make_binop_fn("proof_and", BinOp::BitAnd);
    let spec = bin(Formula::BvAnd, wn(0), wn(1));
    assert_eq!(
        prove_output_equiv(&f, &spec),
        Verdict::Proven,
        "and: emitted bytes were not proven to equal (a & b) for all inputs"
    );
    // NEGATIVE CONTROL: and bytes are NOT a | b.
    let wrong = bin(Formula::BvOr, wn(0), wn(1));
    assert_eq!(
        prove_output_equiv(&f, &wrong),
        Verdict::CounterExample,
        "VACUITY: and bytes were 'proven' equal to (a | b)"
    );
}

// ---- OR ----
#[test]
fn or_proven_and_negctrl() {
    let f = make_binop_fn("proof_or", BinOp::BitOr);
    let spec = bin(Formula::BvOr, wn(0), wn(1));
    assert_eq!(
        prove_output_equiv(&f, &spec),
        Verdict::Proven,
        "or: emitted bytes were not proven to equal (a | b) for all inputs"
    );
    // NEGATIVE CONTROL: or bytes are NOT a & b.
    let wrong = bin(Formula::BvAnd, wn(0), wn(1));
    assert_eq!(
        prove_output_equiv(&f, &wrong),
        Verdict::CounterExample,
        "VACUITY: or bytes were 'proven' equal to (a & b)"
    );
}

// ---- XOR ----
#[test]
fn xor_proven_and_negctrl() {
    let f = make_binop_fn("proof_xor", BinOp::BitXor);
    let spec = bin(Formula::BvXor, wn(0), wn(1));
    assert_eq!(
        prove_output_equiv(&f, &spec),
        Verdict::Proven,
        "xor: emitted bytes were not proven to equal (a ^ b) for all inputs"
    );
    // NEGATIVE CONTROL: xor bytes are NOT a & b.
    let wrong = bin(Formula::BvAnd, wn(0), wn(1));
    assert_eq!(
        prove_output_equiv(&f, &wrong),
        Verdict::CounterExample,
        "VACUITY: xor bytes were 'proven' equal to (a & b)"
    );
}

// ---- SHL (logical shift left) ----
//
// AArch64 LSLV masks the shift amount to its low 5 bits for 32-bit operands;
// the spec is `a << (b & 31)`. Args land in W0 (value) and W1 (amount).
#[test]
fn shl_proven_and_negctrl() {
    let f = make_binop_fn("proof_shl", BinOp::Shl);
    let spec = bin(Formula::BvShl, wn(0), masked_shift_amt(1));
    assert_eq!(
        prove_output_equiv(&f, &spec),
        Verdict::Proven,
        "shl: emitted bytes were not proven to equal (a << (b & 31)) for all inputs"
    );
    // NEGATIVE CONTROL: shl bytes are NOT an arithmetic right shift.
    let wrong = bin(Formula::BvAShr, wn(0), masked_shift_amt(1));
    assert_eq!(
        prove_output_equiv(&f, &wrong),
        Verdict::CounterExample,
        "VACUITY: shl bytes were 'proven' equal to (a >> (b & 31))"
    );
}

// ---- SHR (arithmetic shift right; i32 is signed) ----
//
// AArch64 ASRV (arithmetic, sign-extending) masks the shift amount to low 5
// bits; the spec is `a ashr (b & 31)`.
#[test]
fn shr_proven_and_negctrl() {
    let f = make_binop_fn("proof_shr", BinOp::Shr);
    let spec = bin(Formula::BvAShr, wn(0), masked_shift_amt(1));
    assert_eq!(
        prove_output_equiv(&f, &spec),
        Verdict::Proven,
        "shr: emitted bytes were not proven to equal (a ashr (b & 31)) for all inputs"
    );
    // NEGATIVE CONTROL: arithmetic shift right bytes are NOT a left shift.
    let wrong = bin(Formula::BvShl, wn(0), masked_shift_amt(1));
    assert_eq!(
        prove_output_equiv(&f, &wrong),
        Verdict::CounterExample,
        "VACUITY: shr bytes were 'proven' equal to (a << (b & 31))"
    );
}

// ---------------------------------------------------------------------------
// COMPOSITE CERTIFICATE: madd(a,b,c) = a*b + c.
//
// Two IR statements lower to a multi-instruction sequence; the symbolic
// executor must COMPOSE the product into the sum (threading temp `t` through
// the machine state). We prove the byte-derived output equals BvAdd(BvMul(a,b),c)
// for ALL inputs, with a negative control (a*b - c) that must be SAT.
// ---------------------------------------------------------------------------

#[test]
fn composite_madd_proven_and_negctrl() {
    let f = make_madd();
    // PROVEN: emitted bytes == (a * b) + c.
    let spec = bin(Formula::BvAdd, bin(Formula::BvMul, wn(0), wn(1)), wn(2));
    assert_eq!(
        prove_output_equiv(&f, &spec),
        Verdict::Proven,
        "composite: emitted madd bytes were not proven to equal (a*b + c) for all inputs"
    );
    // NEGATIVE CONTROL: the sequence is NOT (a * b) - c.
    let wrong = bin(Formula::BvSub, bin(Formula::BvMul, wn(0), wn(1)), wn(2));
    assert_eq!(
        prove_output_equiv(&f, &wrong),
        Verdict::CounterExample,
        "VACUITY: madd bytes were 'proven' equal to (a*b - c)"
    );
}
