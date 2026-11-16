//! DROPPED-DEF WRITE VISIBILITY (shape "P1b"), pinned through the production
//! router.
//!
//! `extract_block_definitions_until_impl` deliberately DECLINES a definition
//! for several rvalues (bare wrapping `Mul`, unsigned non-constant `Rem`,
//! unsupported casts, FP arms, ...) — each refusal is individually sound as a
//! dropped HYPOTHESIS. But every version-map/kill gen-set derived its write
//! domain from the EXTRACTED defs, so each such `continue` also deleted the
//! WRITE from write visibility: downstream reads of the assigned place rendered
//! BARE, and every rename-exempt bare fact (preconditions, path guards,
//! semantic guards, arg type ranges) unified straight across the invisible
//! write.
//!
//! The fixture is the measured false-prove shape: `fn p1b(a: u64, b: u64)`
//! with precondition `b != 0`; bb0 writes the divisor via a DROPPED-def Mul
//! (`b = a * b`), then `Drop`s a guard with `unwind -> bb2`; the cleanup block
//! bb2 divides `a / b`. At runtime `p1b(0, 5)` sets `b = 0`, the drop panics,
//! and the cleanup path divides by zero — yet the DivisionByZero VC formula
//! was literally `(and (not (= b 0)) (= b 0))`: UNSAT, **Proved with proof
//! certificate**, on the strength of a precondition about the PRE-write `b`.
//!
//! The fix is the general write-visibility rule (`extend_with_assigned_place_dests`
//! unioned into every extracted-defs-derived gen-set, the raw-dest transport
//! kill in `v2_path_def_fixpoint`, and unwind-inclusive entry versions), NOT a
//! re-added def for the refused rvalue — the unbounded `dest == a*b` over Int
//! was a measured false-prover, which is why the def is dropped.
//!
//! PLANTED AND WATCHED: narrow the rule back — make
//! `extend_with_assigned_place_dests` a no-op — and both fixture tests here go
//! red with the false `Proved` verdicts restored (watched 2026-08-30, exit 101).

use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VcKind, VerifiableBody, VerifiableFunction, VerificationResult,
};

#[path = "support/test_router.rs"]
mod test_router;

fn load(name: &str) -> VerifiableFunction {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/");
    let text = std::fs::read_to_string(format!("{path}{name}.json"))
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

/// DivisionByZero verdicts through the production composition — the same
/// `generate_vcs` -> `Router` + in-process ay pairing `trustc` wires in
/// `trust_verify.rs` — plus the VC count, so laundering the obligation away
/// (no row emitted, or degraded to a different kind) cannot pass as "not
/// proved".
fn divzero_verdicts(func: &VerifiableFunction) -> Vec<VerificationResult> {
    let vcs: Vec<_> = trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::DivisionByZero))
        .collect();
    let router = test_router::deterministic_test_router();
    router.verify_all(&vcs).into_iter().map(|(_, verdict)| verdict).collect()
}

#[test]
fn a_dropped_def_mul_write_of_the_divisor_is_not_proved_across() {
    let func = load("dropped_def_mul_divisor_unwind");
    trust_vcgen::validate_function(&func).expect("the fixture must be VALID TrustIR");

    // ANTI-LAUNDERING (obligation side): the cleanup-path division must still
    // raise a DivisionByZero obligation. A fix that silences the row instead of
    // refuting it fails here.
    let verdicts = divzero_verdicts(&func);
    assert!(!verdicts.is_empty(), "the cleanup-path `a / b` must raise a DivisionByZero row");

    // THE PIN: `b` is written by a dropped-def Mul before the unwind edge, so
    // the entry precondition `b != 0` says nothing about the divisor the
    // cleanup block reads. `p1b(0, 5)` divides by zero at runtime; the row must
    // NOT be Proved (measured post-fix: `Failed` with the real counterexample
    // `b = 1` entry, `b#s0_0 = 0` post-write).
    for v in &verdicts {
        assert!(
            !matches!(v, VerificationResult::Proved { .. }),
            "false proof: the divisor write `b = a * b` (dropped-def Mul) was \
             invisible to the write domain and the entry precondition unified \
             across it: {v:?}"
        );
    }
}

#[test]
fn the_write_free_control_still_proves_and_the_fact_free_control_still_refutes() {
    // CONTROL 1 (no invisible write): with bb0's Mul removed, the precondition
    // `b != 0` genuinely guards the cleanup division on every path — Proved is
    // CORRECT, and a fix that over-nukes bare facts fails here.
    let mut write_free = load("dropped_def_mul_divisor_unwind");
    write_free.body.blocks[0].stmts.clear();
    let verdicts = divzero_verdicts(&write_free);
    assert!(!verdicts.is_empty(), "the control must still raise the DivisionByZero row");
    for v in &verdicts {
        assert!(
            matches!(v, VerificationResult::Proved { .. }),
            "the write-free control is genuinely guarded by `b != 0`; \
             widening write visibility must not demote it: {v:?}"
        );
    }

    // CONTROL 2 (no precondition): the violation must be refutable at all —
    // this is what makes control 1 and the pin above a measurement of the
    // precondition channel rather than of an unfalsifiable row.
    let mut fact_free = load("dropped_def_mul_divisor_unwind");
    fact_free.preconditions.clear();
    let verdicts = divzero_verdicts(&fact_free);
    assert!(!verdicts.is_empty());
    for v in &verdicts {
        assert!(
            !matches!(v, VerificationResult::Proved { .. }),
            "without the precondition nothing guards the divisor: {v:?}"
        );
    }
}

/// The PATH-DEF-MAP SIBLING (no precondition, no unwind): a VISIBLE ancestor
/// def (`d = 7`) must not survive a dropped-def Mul write of the same local
/// (`d = a * b`) into the division block — the fixpoint-threaded fact is
/// renamed WITH the body at the consumption point, so for this channel the
/// transport KILL (not the rename) is load-bearing. Measured at the pre-fix
/// HEAD: `q = a / d` shipped `(and (= d 7) (= d 7) (= d 0))`-shaped rows
/// Proved with certificate while `sib(0, b)` divides by zero.
fn sibling() -> VerifiableFunction {
    let span = SourceSpan::default;
    VerifiableFunction {
        name: "sib".to_string(),
        def_path: "probe::sib".to_string(),
        span: span(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: Some("ret".into()) },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::u64(), name: Some("d".into()) },
                LocalDecl { index: 4, ty: Ty::u64(), name: Some("q".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 64))),
                        span: span(),
                    }],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Mul,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: span(),
                    }],
                    terminator: Terminator::Goto(BlockId(2)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(3)),
                            ),
                            span: span(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(4))),
                            span: span(),
                        },
                    ],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::u64(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

#[test]
fn a_stale_visible_def_does_not_survive_a_dropped_def_write_of_its_subject() {
    let func = sibling();
    trust_vcgen::validate_function(&func).expect("the fixture must be VALID TrustIR");
    let verdicts = divzero_verdicts(&func);
    assert!(!verdicts.is_empty(), "`a / d` must raise a DivisionByZero row");
    for v in &verdicts {
        assert!(
            !matches!(v, VerificationResult::Proved { .. }),
            "false proof: bb0's `d == 7` survived bb1's dropped-def Mul write \
             of `d` into the division block: {v:?}"
        );
    }

    // CONTROL: with the invisible write removed, `d == 7` genuinely reaches the
    // division and Proved is correct.
    let mut no_write = sibling();
    no_write.body.blocks[1].stmts.clear();
    let verdicts = divzero_verdicts(&no_write);
    assert!(!verdicts.is_empty());
    for v in &verdicts {
        assert!(
            matches!(v, VerificationResult::Proved { .. }),
            "the write-free control is genuinely guarded by `d == 7`: {v:?}"
        );
    }
}
