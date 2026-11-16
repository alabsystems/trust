//! REAL-ARTIFACT regression guard for SELF-GUARDED-LITERAL-OPERAND-1: the
//! self-guarded statement-lane row over a LITERAL operand — the residue of the
//! family `self_guarded_const_operand_real_mir.rs` (a symbolic constant),
//! `negation_canary_real_mir.rs` and the `checked_vcs` real-MIR modules (a place)
//! guard.
//!
//! Every fixture loaded here is the compiler's OWN extracted verification input
//! (`-Ztrust-dump=mir`). The `literal_<fn>.json` dumps come from
//! `tests/data/literal_operand_arms.rs` (README, "Literal operand family"); the
//! three `*_dividend_*` ones from `divrem_projected_arms.rs`, where they were
//! already committed and only their OVERFLOW rows were checked; the
//! `literal_divisor_<fn>.json` ones from `tests/data/literal_divisor_arms.rs` (README,
//! "Literal divisor family").
//!
//! # What went wrong
//!
//! Two exact-binding suppressors refused a literal operand, so the statement-lane
//! row — which sits in the assert's target block under the assert's own
//! `AssertHolds` guard, UNSAT by construction — survived and shipped as a
//! `proved`, clean-kernel-CERTIFIED row at the span of an operation that panics.
//!
//! * A signed `Div`/`Rem` with a literal dividend (`100 / x`): the zero-divisor
//!   chain bound the intervening `Overflow` assert's `Eq(const 100, const
//!   i32::MIN)` conjunct with a binder that refuses a literal. MEASURED on the
//!   probe stage 1 (`46e9afaf95`): `div_lit(x: i32) { 100 / x }` read `divzero
//!   failed` beside `divzero proved` (clean-kernel, `Certified`,
//!   `KernelRechecked`) at one span.
//! * A literal negation under `#![allow(arithmetic_overflow)]` (`-i32::MIN`): the
//!   assert-lane builder refused every literal (proof gap), and the statement row,
//!   built at the i64 `operand_ty` gives `i32::MIN`, was the function's only
//!   `negation` row: `proved`, kernel-certified, for a negation that panics on
//!   every run. `-i128::MIN` the same at width 128.
//! * A LITERAL zero divisor under `#![allow(unconditional_panic)]` (`x / 0`, `a %
//!   0u8`, `100 / 0`; the literal-divisor follow-up, 2026-10-13): the zero assert's
//!   `Eq(const 0, const 0)` (and, signed, the chain's `Eq(const 0, const -1)`
//!   conjunct) went to a binder that refuses a literal. MEASURED on the
//!   `integ/wave25` stage 1 (`scratchpad/stage1-w25`): `x / 0` read `divzero failed`
//!   beside `divzero proved` (clean-kernel, `Certified`, `KernelRechecked`).
//!
//! # What each arm pins
//!
//! Every row is run through the in-process ay router and the clean-kernel
//! certifier. A check that panics must keep exactly ONE row, REFUTED, and no row
//! at its span may certify. The safe twins keep their one honest row.

use trust_types::{
    BinOp, ConstValue, Operand, Rvalue, Statement, VcKind, VerifiableFunction,
    VerificationCondition, VerificationResult,
};

#[path = "support/test_router.rs"]
mod test_router;

const DATA: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/");

fn load(name: &str) -> VerifiableFunction {
    // Straight from text: `literal_neg_min128` carries `Int: i128::MIN`, which a
    // `serde_json::Value` round-trip would widen to `f64`.
    let text = std::fs::read_to_string(format!("{DATA}{name}.json"))
        .unwrap_or_else(|e| panic!("real-MIR fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("real-MIR fixture `{name}` must deserialize: {e}"))
}

fn rows_of(func: &VerifiableFunction, pick: fn(&VcKind) -> bool) -> Vec<VerificationCondition> {
    trust_vcgen::generate_vcs(func).into_iter().filter(|vc| pick(&vc.kind)).collect()
}

fn zero_divisor(kind: &VcKind) -> bool {
    matches!(kind, VcKind::DivisionByZero | VcKind::RemainderByZero)
}

fn negation(kind: &VcKind) -> bool {
    matches!(kind, VcKind::NegationOverflow { .. })
}

fn proof_gap(kind: &VcKind) -> bool {
    matches!(
        kind,
        VcKind::UnsupportedMir { kind, detail }
            if kind.contains("RecognizedSafetyAssertProofGap")
                || detail.contains("RecognizedSafetyAssertProofGap")
    )
}

fn verdict(vc: &VerificationCondition) -> VerificationResult {
    let router = test_router::deterministic_test_router();
    let results = router.verify_all(std::slice::from_ref(vc));
    let (_, result) = results.into_iter().next().expect("one verdict per VC");
    result
}

/// THE PROPERTY for a check that panics: exactly one row, refuted, uncertified.
fn assert_one_refuted_uncertified(name: &str, rows: &[VerificationCondition]) {
    assert_eq!(
        rows.len(),
        1,
        "{name}: exactly ONE row — the assert lane's refutable one — and no self-guarded \
         statement-lane duplicate"
    );
    let vc = &rows[0];
    let result = verdict(vc);
    assert!(
        matches!(result, VerificationResult::Failed { .. }),
        "{name}: the row must be REFUTED — the operation panics. Got {result:?}\nformula: {}",
        vc.formula.to_smtlib()
    );
    assert!(
        trust_certify::certify_vc(vc).is_none(),
        "{name}: a row stating a check that fails must not kernel-certify: {}",
        vc.formula.to_smtlib()
    );
}

#[test]
fn a_literal_dividend_keeps_one_refuted_zero_divisor_row() {
    // Each divides by an unconstrained divisor, so each panics at divisor 0.
    // Before: two zero-divisor rows each, one of them vacuous and kernel-certified.
    for name in [
        "nonmin_const_dividend_div",
        "const_min_dividend_div",
        "const_min_dividend_rem",
        "literal_div_cast_divisor",
    ] {
        let func = load(name);
        assert_one_refuted_uncertified(name, &rows_of(&func, zero_divisor));
    }
}

#[test]
fn a_literal_zero_divisor_keeps_one_refuted_zero_divisor_row() {
    // The literal-DIVISOR follow-up (2026-10-13): each divides by a literal 0 under
    // `#![allow(unconditional_panic)]`, so each panics on every call. Before: two
    // zero-divisor rows each, the statement-lane one vacuous (`!(0 == 0) && 0 == 0`)
    // and kernel-certified.
    for name in [
        "literal_divisor_div_x0",
        "literal_divisor_rem_x0",
        "literal_divisor_rem_u8_0",
        "literal_divisor_div_u32_0",
        "literal_divisor_rem_cast_0",
        "literal_divisor_div_lit_lit0",
    ] {
        let func = load(name);
        assert_one_refuted_uncertified(name, &rows_of(&func, zero_divisor));
    }
}

#[test]
fn a_const_false_zero_check_beside_a_literal_zero_divisor_keeps_a_refuted_row() {
    // FORGED: `x / 0` and `a % 0u8` with the zero check rewritten to compare 2, not
    // the divisor's own 0. The assert then passes on every run and emits no row (its
    // failure is known false), so the statement-lane row — `0 == 0` under a guard
    // that HOLDS — is the one obligation, and it must stay and be refuted. A literal
    // identity that ignored the value would have suppressed it.
    for (name, forged) in [
        ("literal_divisor_div_x0", ConstValue::Int(2)),
        ("literal_divisor_rem_u8_0", ConstValue::Uint(2, 8)),
    ] {
        let mut func = load(name);
        let Statement::Assign { rvalue: Rvalue::BinaryOp(BinOp::Eq, l, _), .. } =
            &mut func.body.blocks[0].stmts[0]
        else {
            unreachable!("fixture drift: {name} bb0[0] is the zero check")
        };
        *l = Operand::Constant(forged);
        assert_one_refuted_uncertified(name, &rows_of(&func, zero_divisor));
    }
}

#[test]
fn a_literal_negation_that_overflows_keeps_one_refuted_row() {
    // `-i32::MIN`, `-i8::MIN`, `-i128::MIN`: each panics on every run.
    for name in ["literal_neg_min", "literal_neg_min8", "literal_neg_min128"] {
        let func = load(name);
        assert_one_refuted_uncertified(name, &rows_of(&func, negation));
        assert!(
            rows_of(&func, proof_gap).is_empty(),
            "{name}: the assert lane builds the row instead of leaving a proof gap"
        );
    }
}

#[test]
fn a_literal_negation_that_cannot_overflow_keeps_one_honest_row() {
    // `-i32::MAX` is total. Its one row is the assert lane's, and it is NOT
    // refuted: the surface must not shrink, and the identity must not invent a
    // failure.
    let name = "literal_neg_max";
    let func = load(name);
    let rows = rows_of(&func, negation);
    assert_eq!(rows.len(), 1, "{name}: one honest row");
    assert!(rows_of(&func, proof_gap).is_empty(), "{name}: no proof gap");
    let result = verdict(&rows[0]);
    assert!(
        matches!(result, VerificationResult::Proved { .. }),
        "{name}: `-i32::MAX` cannot overflow; got {result:?}"
    );
}
