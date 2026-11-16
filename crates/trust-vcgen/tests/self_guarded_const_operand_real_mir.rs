//! REAL-ARTIFACT regression guard for SELF-GUARDED-CONST-OPERAND-1: the
//! self-guarded statement-lane row over a CONSTANT operand that has a value
//! identity — a const-generic parameter `N`, or a keyed opaque scalar such as
//! `T::U` — the member of the family `negation_canary_real_mir.rs`,
//! `projected_shift_canary_real_mir.rs` and the `checked_vcs` real-MIR modules
//! guard for PLACE operands.
//!
//! Every fixture loaded here is the compiler's OWN extracted verification input,
//! captured verbatim (pretty-printed, nothing else edited; the spans are already
//! file-relative) with
//!
//! ```text
//! rustc --edition 2021 --crate-type lib -C debug-assertions=on \
//!       -Ztrust-dump=mir:<dir> const_operand_arms.rs
//! ```
//!
//! run inside `crates/trust-vcgen/tests/data/` by the stage 1 of `5911b1325f`
//! (`rustc 1.99.0-dev`, trust 0.10.0) on 2026-10-11. `const_operand_arms.rs` is
//! committed beside the dumps, and each `const_operand_<fn>.json` is the dump
//! whose `"name"` is `<fn>`.
//!
//! # What went wrong
//!
//! rustc does not fold a checked operation over a const generic. `-N` extracts as
//!
//! ```text
//! bb0: _1 = Eq(const N, const i32::MIN); assert(!_1, OverflowNeg) -> bb1
//! bb1: _0 = Neg(const N)
//! ```
//!
//! and `x / N`, `x % N`, `x << N`, `x / T::U` the same way with their own conds.
//! Every exact-binding suppressor asked for a PLACE: `v2_operands_structurally_equal`
//! had no arm for a const param or a keyed opaque scalar,
//! `v2_eq_def_binds_compared_value` took `const N` (the LEFT constant) for the
//! literal, and the assert-lane negation builder refused every constant. So the
//! statement-lane row — sitting in the assert's target block under its
//! `AssertHolds` guard, violation `NOT _1` beside `_1`'s own definition, UNSAT by
//! construction — was never suppressed. It shipped as a `proved`,
//! clean-kernel-CERTIFIED row at the span of a check that genuinely fails.
//! MEASURED on that stage 1 under `-Ztrust-policy=certify`: `neg_c` read `1
//! proved, 0 failed, 1 unknown … of which 1 kernel-certified` (the unknown being
//! the assert lane's `RecognizedSafetyAssertProofGap(OverflowNeg)`), so the
//! function's ONLY negation row was the vacuous one; `div_c` read `[divzero]
//! FAILED` beside a certified `divzero` row; `shl_c` read a generic `[overflow]
//! FAILED` beside a certified `shift:left` row.
//!
//! # What each arm pins
//!
//! The positive arms run every safety row of every fixture through the
//! in-process ay router and the clean-kernel certifier. Every one of these
//! functions panics for SOME instantiation, so the right answer for every row is
//! REFUTED, and no row may certify. Before the fix each fixture carried one
//! vacuous row that came back `Proved` and kernel-certified.
//!
//! The forged arms mutate one field of real input each, and each must leave BOTH
//! rows standing: a cond over a DIFFERENT const param or a DIFFERENT opaque key
//! is not this operation's check, and a SITE-placed opaque scalar (a runtime
//! value) has no value identity at all.

use trust_types::{BinOp, VcKind, VerifiableFunction, VerificationCondition, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

const DATA: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/");

fn load_json(name: &str) -> serde_json::Value {
    let text = std::fs::read_to_string(format!("{DATA}{name}.json"))
        .unwrap_or_else(|e| panic!("real-MIR fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("real-MIR fixture `{name}` must parse as JSON: {e}"))
}

fn from_value(name: &str, value: serde_json::Value) -> VerifiableFunction {
    serde_json::from_value(value)
        .unwrap_or_else(|e| panic!("real-MIR fixture `{name}` must deserialize: {e}"))
}

fn load(name: &str) -> VerifiableFunction {
    // STRAIGHT FROM TEXT, never through `serde_json::Value`: `neg_c128` carries
    // `Int: i128::MIN`, which `Value`'s number type widens to `f64` (see
    // `negation_canary_real_mir.rs`). Only the mutating arms take the `Value`
    // route, and none of them uses the i128 fixture.
    let text = std::fs::read_to_string(format!("{DATA}{name}.json"))
        .unwrap_or_else(|e| panic!("real-MIR fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("real-MIR fixture `{name}` must deserialize: {e}"))
}

/// Every row either lane can put at the span of a negation, a division, a
/// remainder or a shift, spelled as a short label. A shift that the binder
/// REFUSES shows up as the PAIR `ArithmeticOverflow(Shl)` + `ShiftOverflow(Shl)`
/// (the assert lane falls through to its generic row), so the label set — never
/// the `ShiftOverflow` count alone — is what separates bound from refused.
fn safety_label(vc: &VerificationCondition) -> Option<String> {
    match &vc.kind {
        VcKind::NegationOverflow { .. } => Some("negation".into()),
        VcKind::DivisionByZero => Some("divzero".into()),
        VcKind::RemainderByZero => Some("remzero".into()),
        VcKind::ShiftOverflow { op, .. } => Some(format!("shift({op:?})")),
        VcKind::ArithmeticOverflow { op, .. } => Some(format!("overflow({op:?})")),
        _ => None,
    }
}

fn safety_rows(func: &VerifiableFunction) -> Vec<(String, VerificationCondition)> {
    trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter_map(|vc| safety_label(&vc).map(|label| (label, vc)))
        .collect()
}

fn labels(func: &VerifiableFunction) -> Vec<String> {
    let mut out: Vec<String> = safety_rows(func).into_iter().map(|(label, _)| label).collect();
    out.sort();
    out
}

/// The assert lane's explicit "I could not build this row" marker.
fn proof_gaps(func: &VerifiableFunction) -> Vec<String> {
    trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter_map(|vc| match &vc.kind {
            VcKind::UnsupportedMir { kind, detail }
                if kind.contains("RecognizedSafetyAssertProofGap")
                    || detail.contains("RecognizedSafetyAssertProofGap") =>
            {
                Some(format!("{kind}: {detail}"))
            }
            _ => None,
        })
        .collect()
}

fn router() -> trust_router::Router {
    test_router::deterministic_test_router()
}

fn verdict(router: &trust_router::Router, vc: &VerificationCondition) -> VerificationResult {
    let results = router.verify_all(std::slice::from_ref(vc));
    let (_, result) = results.into_iter().next().expect("one verdict per VC");
    result
}

/// THE PROPERTY. Every function here panics for some instantiation, so every
/// safety row must be REFUTED by the solver and none may kernel-certify. A
/// self-guarded row is UNSAT for every program: it comes back `Proved` and
/// certifies, which is exactly what this rejects.
fn assert_every_row_refuted_and_none_certified(name: &str, func: &VerifiableFunction) {
    let router = router();
    let rows = safety_rows(func);
    assert!(!rows.is_empty(), "{name}: the fixture must carry its safety rows");
    for (label, vc) in &rows {
        let result = verdict(&router, vc);
        assert!(
            matches!(result, VerificationResult::Failed { .. }),
            "{name}: the `{label}` row must be REFUTED — the operation genuinely fails \
             for some instantiation, and a `Proved` row here is the self-guarded vacuity \
             (`NOT flag` beside `flag`'s own definition). Got {result:?}\nformula: {}",
            vc.formula.to_smtlib()
        );
        assert!(
            trust_certify::certify_vc(vc).is_none(),
            "{name}: the `{label}` row must not kernel-certify — it states a check that \
             genuinely fails. formula: {}",
            vc.formula.to_smtlib()
        );
    }
}

fn assert_exactly(name: &str, func: &VerifiableFunction, expected: &[&str]) {
    let mut want: Vec<String> = expected.iter().map(|s| (*s).to_string()).collect();
    want.sort();
    assert_eq!(
        labels(func),
        want,
        "{name}: each check must carry exactly ONE row — the assert lane's refutable \
         one — and no self-guarded statement-lane duplicate"
    );
    assert!(
        proof_gaps(func).is_empty(),
        "{name}: the assert lane must build the row, not leave a proof gap: {:?}",
        proof_gaps(func)
    );
}

// ---------------------------------------------------------------------------
// THE DEFECT, per operator. Each fixture is one real extraction.
// ---------------------------------------------------------------------------

#[test]
fn negation_of_a_const_param_keeps_one_refutable_row() {
    // THE HEADLINE. Before: one `negation` row, the vacuous one, kernel-certified,
    // beside the assert lane's proof gap — the function's ONLY negation claim was
    // the one that could never fail.
    let name = "const_operand_neg_c";
    let func = load(name);
    assert_every_row_refuted_and_none_certified(name, &func);
    assert_exactly(name, &func, &["negation"]);

    // …and the surviving row is THE overflow: its witness is `N == i32::MIN`.
    let (_, vc) = safety_rows(&func).into_iter().next().expect("one row");
    let VerificationResult::Failed { counterexample: Some(cex), .. } = verdict(&router(), &vc)
    else {
        panic!("{name}: the negation row must be refuted with a counterexample");
    };
    let witness = cex
        .assignments
        .iter()
        .find(|(var, _)| var.starts_with("__trust_constparam_0_N"))
        .map(|(_, value)| format!("{value:?}"));
    assert_eq!(
        witness.as_deref(),
        Some("Int(-2147483648)"),
        "{name}: the counterexample must instantiate N at i32::MIN: {cex:?}"
    );
}

#[test]
fn negation_width_sweep_keeps_one_refutable_row() {
    for name in ["const_operand_neg_c8", "const_operand_neg_c64"] {
        let func = load(name);
        assert_every_row_refuted_and_none_certified(name, &func);
        assert_exactly(name, &func, &["negation"]);
    }
}

#[test]
fn i128_negation_of_a_const_param_is_in_scope() {
    // The i128 exclusion is keyed on the BV constructor, not the width. A const
    // param has no BV rendering, so both lanes take the Int constructors and the
    // statement row is the same vacuity as below 128 (MEASURED before the fix:
    // `1 proved … of which 1 kernel-certified` + `1 unknown`). The place-operand
    // i128 member, where the lanes really do diverge, keeps both rows —
    // `negation_canary_real_mir::i128_negation_is_left_alone`.
    let name = "const_operand_neg_c128";
    let func = load(name);
    assert_every_row_refuted_and_none_certified(name, &func);
    assert_exactly(name, &func, &["negation"]);
}

#[test]
fn unsigned_division_by_a_const_param_keeps_one_refutable_row() {
    for (name, label) in [("const_operand_div_c", "divzero"), ("const_operand_rem_c", "remzero")] {
        let func = load(name);
        assert_every_row_refuted_and_none_certified(name, &func);
        assert_exactly(name, &func, &[label]);
    }
}

#[test]
fn signed_division_by_a_const_param_keeps_one_row_per_check() {
    // The signed chain: zero assert, then the intervening `Overflow(Div|Rem)`
    // assert whose `Eq(const N, const -1)` conjunct is a constant on BOTH sides.
    // Before: two pairs (`divzero` x2, `overflow(Div)` x2), one of each vacuous.
    for (name, expected) in [
        ("const_operand_sdiv_c", ["divzero", "overflow(Div)"]),
        ("const_operand_srem_c", ["remzero", "overflow(Rem)"]),
    ] {
        let func = load(name);
        assert_every_row_refuted_and_none_certified(name, &func);
        assert_exactly(name, &func, &expected);
    }
}

#[test]
fn a_const_param_dividend_keeps_one_overflow_row() {
    // `N / -1`: the const generic is the DIVIDEND, compared against INT_MIN in the
    // `Eq(const N, const MIN)` conjunct. The divisor `-1` is a nonzero literal, so
    // no zero-divisor row exists in either lane.
    let name = "const_operand_sdiv_c_dividend";
    let func = load(name);
    assert_every_row_refuted_and_none_certified(name, &func);
    assert_exactly(name, &func, &["overflow(Div)"]);
}

#[test]
fn a_shift_by_a_const_param_keeps_one_real_shift_row() {
    // Before: the PAIR signature — a generic `overflow(Shl)` from the assert lane
    // (its binder refused) and the vacuous `shift(Shl)` from the statement lane.
    for (name, label) in
        [("const_operand_shl_c", "shift(Shl)"), ("const_operand_shr_c", "shift(Shr)")]
    {
        let func = load(name);
        assert_every_row_refuted_and_none_certified(name, &func);
        assert_exactly(name, &func, &[label]);
    }
}

#[test]
fn division_by_a_keyed_opaque_scalar_keeps_one_refutable_row() {
    // `x / T::U`: the divisor is an `OpaqueScalar` with `OpaqueOrigin::Const`,
    // one value per key (OPAQUE-SCALAR-ID-1).
    let name = "const_operand_div_a";
    let func = load(name);
    assert_every_row_refuted_and_none_certified(name, &func);
    assert_exactly(name, &func, &["divzero"]);
}

// ---------------------------------------------------------------------------
// FORGED ARMS — one field of real input changed each. Every one takes the shape
// out of the exact binding, and BOTH rows must stand: duplicates over-report,
// they never under-report.
// ---------------------------------------------------------------------------

/// The `Eq(<compared>, <literal>)` comparison at `bb<block>.stmts[stmt]`.
fn eq_operands(v: &mut serde_json::Value, block: usize, stmt: usize) -> &mut serde_json::Value {
    let rvalue = &mut v["body"]["blocks"][block]["stmts"][stmt]["Assign"]["rvalue"]["BinaryOp"];
    assert_eq!(rvalue[0], "Eq", "fixture drift: bb{block}[{stmt}] must be the Eq comparison");
    rvalue
}

fn mutated(name: &str, mutate: impl FnOnce(&mut serde_json::Value)) -> VerifiableFunction {
    let mut value = load_json(name);
    mutate(&mut value);
    from_value(name, value)
}

#[test]
fn a_zero_check_over_a_different_const_param_keeps_both_rows() {
    // `assert(M == 0)` does not guard `x / N`. RED under: comparing a const param
    // by anything less than its whole `(index, name, ..)` identity.
    let func = mutated("const_operand_div_c", |v| {
        let param = &mut eq_operands(v, 0, 0)[1]["Constant"]["ConstParam"];
        assert_eq!(param["name"], "N", "fixture drift: bb0 must compare `N`");
        param["index"] = serde_json::json!(1);
        param["name"] = serde_json::json!("M");
    });
    assert_eq!(labels(&func), ["divzero", "divzero"]);
}

#[test]
fn a_zero_check_over_a_same_index_differently_named_param_keeps_both_rows() {
    // The NAME is part of the identity too; the index alone is not.
    let func = mutated("const_operand_div_c", |v| {
        eq_operands(v, 0, 0)[1]["Constant"]["ConstParam"]["name"] = serde_json::json!("M");
    });
    assert_eq!(labels(&func), ["divzero", "divzero"]);
}

#[test]
fn a_zero_check_over_a_different_opaque_key_keeps_both_rows() {
    // Two keyed constants with different keys are different values.
    let func = mutated("const_operand_div_a", |v| {
        let origin = &mut eq_operands(v, 0, 0)[1]["Constant"]["OpaqueScalar"]["origin"];
        let key = origin["Const"]["key"].as_str().expect("fixture drift: keyed opaque").to_string();
        origin["Const"]["key"] = serde_json::json!(format!("{key}_other"));
    });
    assert_eq!(labels(&func), ["divzero", "divzero"]);
}

#[test]
fn site_placed_opaque_scalars_keep_both_rows() {
    // THE NEGATIVE CONTROL. With the key stripped, each opaque scalar is placed at
    // its own SITE on load (`VerifiableBody::place_opaque_values`): two sites may
    // hold two different runtime values, so no site origin is ever an identity —
    // not even the same spelling at two locations.
    let func = mutated("const_operand_div_a", |v| {
        let mut stripped = 0;
        for (block, stmt, side) in [(0, 0, 1), (1, 0, 2)] {
            let operand = &mut v["body"]["blocks"][block]["stmts"][stmt]["Assign"]["rvalue"]["BinaryOp"]
                [side]["Constant"]["OpaqueScalar"];
            let object = operand.as_object_mut().expect("fixture drift: opaque scalar operand");
            stripped += usize::from(object.remove("origin").is_some());
        }
        assert_eq!(stripped, 2, "fixture drift: both occurrences must be keyed");
    });
    assert_eq!(labels(&func), ["divzero", "divzero"]);
}

#[test]
fn a_second_entry_into_the_division_block_keeps_both_rows() {
    // The sole-entry rule holds for a constant operand exactly as for a place: a
    // block another edge reaches is not covered by the surviving assert row.
    let func = mutated("const_operand_div_c", |v| {
        let blocks = v["body"]["blocks"].as_array_mut().expect("blocks array");
        let id = blocks.len();
        blocks.push(serde_json::json!({ "id": id, "stmts": [], "terminator": { "Goto": 1 } }));
    });
    assert_eq!(labels(&func), ["divzero", "divzero"]);
}

#[test]
fn a_shift_guard_over_a_different_const_param_keeps_both_lanes() {
    // `assert(M < 32)` does not guard `x << N`: the assert lane falls through to
    // its generic row and the statement row stays — the refused PAIR.
    let func = mutated("const_operand_shl_c", |v| {
        let rvalue = &mut v["body"]["blocks"][0]["stmts"][0]["Assign"]["rvalue"]["BinaryOp"];
        assert_eq!(rvalue[0], "Lt", "fixture drift: bb0 must be the `Lt` guard");
        rvalue[1]["Constant"]["ConstParam"]["index"] = serde_json::json!(1);
        rvalue[1]["Constant"]["ConstParam"]["name"] = serde_json::json!("M");
    });
    assert_eq!(labels(&func), ["overflow(Shl)", "shift(Shl)"]);
}

#[test]
fn a_negation_guard_over_a_different_const_param_keeps_the_statement_row() {
    // `assert(M != MIN)` does not guard `-N`. The assert lane declines (an
    // explicit proof gap) and the statement row survives — and is REFUTABLE, since
    // its guard is about a different value.
    let name = "const_operand_neg_c";
    let func = mutated(name, |v| {
        let param = &mut eq_operands(v, 0, 0)[1]["Constant"]["ConstParam"];
        param["index"] = serde_json::json!(1);
        param["name"] = serde_json::json!("M");
    });
    assert_eq!(labels(&func), ["negation"]);
    assert_eq!(proof_gaps(&func).len(), 1, "the assert lane must decline with a visible gap");
    let (_, vc) = safety_rows(&func).into_iter().next().expect("one row");
    assert!(
        matches!(verdict(&router(), &vc), VerificationResult::Failed { .. }),
        "{name}: the surviving statement row must stay refutable: {}",
        vc.formula.to_smtlib()
    );
}

#[test]
fn the_literal_constant_surface_is_untouched() {
    // A literal is not a symbolic constant: `i32::MIN / y`'s `Eq(const MIN, const
    // MIN)` conjunct binds under the divrem rule exactly as before, and nothing
    // here may have moved it.
    let func = load("const_min_dividend_div");
    assert_eq!(
        safety_rows(&func)
            .iter()
            .filter(|(_, vc)| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Div, .. }))
            .count(),
        1
    );
}
