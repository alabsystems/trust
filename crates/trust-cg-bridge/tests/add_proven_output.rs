// add_proven_output.rs — first INFINITE-DOMAIN proven-output-safety certificate.
//
// GOAL: prove that the machine-code bytes trust-cg emits for
//   add(a: i32, b: i32) -> i32 { a + b }
// compute exactly `a + b` for ALL 2^64 inputs (a, b), via the `ay` SMT solver —
// NOT by exhaustive execution. This is route-(a) carried to the infinite domain:
//
//   VerifiableFunction  --trust-cg-->  object bytes  --decode-->  Instructions
//        --Aarch64Semantics::effects-->  Effect[]  --apply_effects-->
//        symbolic MachineState  -->  output Formula  -->  ay discharge.
//
// ANTI-VACUITY (load-bearing): the machine-side output Formula is derived from
// the ACTUAL EMITTED BYTES — we decode each emitted instruction and obtain its
// Effects from trust-machine-sem's `Aarch64Semantics`, then thread those Effects
// through a symbolic `MachineState`. We NEVER reconstruct the output as
// `a + b` from the IR. The proof therefore DISTINGUISHES correct from incorrect
// codegen, which is demonstrated by the mandatory negative control
// (`negative_control_sub_is_sat`): emitting `sub(a, b)` and proving its emitted
// bytes compute `a + b` MUST yield SAT (a counterexample). If that negative
// control were UNSAT, the harness would be vacuous and is rejected.
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
// IR builders: add(i32,i32)->i32 { a+b } and sub(i32,i32)->i32 { a-b }.
// ---------------------------------------------------------------------------

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

fn make_add() -> VerifiableFunction {
    make_binop_fn("proof_add", BinOp::Add)
}

fn make_sub() -> VerifiableFunction {
    make_binop_fn("proof_sub", BinOp::Sub)
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
// the source IR's `a + b` enters this Formula.
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
// We build the ay Term directly with the Solver's term API, declaring each
// distinct `Var` once. This translates whatever Formula the SYMBOLIC EXECUTION produced;
// it does not assume any particular shape.
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
        Formula::BvNot(a, _) => {
            let a = formula_to_term(solver, a);
            solver.try_bvnot(a).expect("bvnot")
        }
        Formula::BvShl(a, b, _) => {
            let a = formula_to_term(solver, a);
            let b = formula_to_term(solver, b);
            solver.try_bvshl(a, b).expect("bvshl")
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
/// Asserts `NOT(machine_out == ir_out)` and checks satisfiability:
///   - UNSAT  => equality holds for every input  => `true` (PROVEN).
///   - SAT    => a counterexample input exists    => `false` (DISPROVEN).
///
/// Both formulas share the same free `Var`s (X0, X1, ...), and `bv_var`
/// returns the same Term for the same name, so the inputs are correctly
/// universally quantified across both sides.
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

/// IR-level i32 semantics of the two arguments: the 32-bit sum W0 + W1.
///
/// W0/W1 are the low 32 bits of the argument registers X0/X1 — exactly the
/// view `read_gpr(0/1, 32)` takes of `MachineState::symbolic()`. We build this
/// from the SAME `Var` names the machine output uses so the solver quantifies
/// over the same inputs.
fn ir_add_output() -> Formula {
    let w0 = Formula::BvExtract {
        inner: Box::new(Formula::Var("X0".into(), Sort::BitVec(64))),
        high: 31,
        low: 0,
    };
    let w1 = Formula::BvExtract {
        inner: Box::new(Formula::Var("X1".into(), Sort::BitVec(64))),
        high: 31,
        low: 0,
    };
    Formula::BvAdd(Box::new(w0), Box::new(w1), 32)
}

// ---------------------------------------------------------------------------
// POSITIVE CERTIFICATE: emitted add(a,b) bytes compute a+b for ALL inputs.
// ---------------------------------------------------------------------------

#[test]
fn add_emitted_bytes_compute_sum_for_all_inputs() {
    let (code, base) = emit_text(&make_add());
    assert!(!code.is_empty(), "emitted __text is empty");

    // machine_out is derived ONLY from the decoded emitted bytes + machine
    // semantics; nothing here references the IR's `a + b`.
    let machine_out = symbolic_machine_output(&code, base);
    let ir_out = ir_add_output();

    let proven = discharge_equal(&machine_out, &ir_out);
    assert!(
        proven,
        "INFINITE-DOMAIN PROOF FAILED: ay did not prove the emitted add() bytes \
         equal (a+b) for all inputs.\n  machine_out = {machine_out:?}"
    );
}

// ---------------------------------------------------------------------------
// MANDATORY NEGATIVE CONTROL: emitted sub(a,b) bytes are NOT a+b.
//
// We prove the SAME property (machine_out == a+b) against the emitted bytes of
// sub(a,b). Because sub computes a-b, this MUST be SAT (a counterexample). If
// this were UNSAT, the discharge would be tautological and the positive
// certificate above would be vacuous.
// ---------------------------------------------------------------------------

#[test]
fn negative_control_sub_is_sat() {
    let (code, base) = emit_text(&make_sub());
    assert!(!code.is_empty(), "emitted __text is empty");

    let machine_out = symbolic_machine_output(&code, base);
    let ir_out = ir_add_output(); // deliberately the WRONG spec for sub.

    let proven = discharge_equal(&machine_out, &ir_out);
    assert!(
        !proven,
        "VACUITY CHECK FAILED: emitted sub() bytes were 'proven' equal to (a+b). \
         The discharge has no teeth — the positive certificate is meaningless.\n  \
         machine_out = {machine_out:?}"
    );
}
