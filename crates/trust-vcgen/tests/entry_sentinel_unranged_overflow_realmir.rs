//! REAL-ARTIFACT precision guard for the lane where the entry sentinel `n#e` is
//! UNRANGED — so the solver picks an out-of-type-range value for a `u32` parameter's
//! pre-write read and FALSELY REFUTES safe code.
//!
//! Fixture: the compiler's own extracted input for
//! `tests/data/entry_sentinel_unranged_overflow.rs`,
//!
//! ```text
//! pub fn h(mut n: u32, b: bool, c: bool) -> u32 {
//!     let s = String::new();
//!     n /= 3;
//!     let mut t: u32 = 0;
//!     if b { t = 1; } else { t = 2; }
//!     let r = if c && t > 0 { n * 3 } else { 0 };
//!     drop(s);
//!     r
//! }
//! ```
//!
//! Safe for every `u32`: `u32::MAX / 3 * 3 == 4294967295` exactly.
//!
//! # The cost this pins
//!
//! `conjoin_arg_type_ranges` bounded every integer parameter by its BARE name only.
//! Its two siblings — `conjoin_local_type_ranges_excluding` and
//! `conjoin_datatype_field_ranges_excluding` — walk the FORMULA's var names, strip
//! the `#…` token, and constrain the EXACT versioned symbol; the parameter arm never
//! got that repair, and nothing else covers it (`local_scalar_range_map` explicitly
//! skips `1..=arg_count`). So `n#e` floated free on `Sort::Int`.
//!
//! Usually invisible, because the tie `Eq(n#e, n)` transfers the bare name's bound.
//! When this was measured (pre 2026-08-29), the `String` removed it: the cleanup
//! blocks it creates (`bb9 Resume`, `bb10 Drop unwind=Terminate`) have an EMPTY
//! entry-version map, and the tie's then-mint-side clause — a WHOLE-FUNCTION
//! `entry_map_covers` quantifier — refused the tie for the whole function. The
//! diamond then weakens the bare-read sibling def away, leaving the pinned
//! `n#s0_5 == n#e / 3` as the only carrier.
//!
//! MEASURED with the in-process ay, range repair disabled:
//!   `Failed`, counterexample `n#e = 4294967298` — three above `u32::MAX`.
//!
//! RE-DERIVED 2026-08-29: the quantifier is retired. `#e` entry-denotation is now
//! ENFORCED AT THE MINT SITE (`full_graph_union_is_entry_only` in
//! `pin_in_place_update_reads` — the mint here is bb0, whose unwind-inclusive
//! reaching union is the entry seed `{e}`, so `#e` is still minted), and the
//! cleanup cluster no longer vetoes: this fixture now legitimately TIES. The range
//! repair this file pins is therefore no longer isolated by tie-absence — the
//! isolation is the DIRECT bound assertion on the sentinel spelling itself.
//!
//! # Honest scope
//!
//! The row does NOT become `Proved`, and this test must not claim it does. The
//! residual obstacle is the solver's integer-division reasoning: the tie-bearing
//! control (`entry_sentinel_unranged_overflow_tied_control`, identical code without
//! the `String`, `n#e` fully connected) is `Unknown` too. What this pins is that the
//! row is no longer REFUTED. Same caveat `join_weakened_entry_sentinel_realmir`
//! states for its own row.

use trust_types::{Formula, VcKind, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

fn load(stem: &str) -> VerifiableFunction {
    let path = format!("{}/tests/data/{stem}.json", env!("CARGO_MANIFEST_DIR"));
    let text = std::fs::read_to_string(&path).expect("fixture must be readable");
    serde_json::from_str(&text).expect("fixture must deserialize")
}

fn mul_overflow_rows(func: &VerifiableFunction) -> Vec<trust_types::VerificationCondition> {
    trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. }))
        .collect()
}

/// `lo <= Var(sym)` and `Var(sym) <= hi` against integer literals — the shape
/// `rust_type_range_constraint` emits.
fn range_bounds_on(f: &Formula, sym: &str) -> (bool, bool) {
    fn walk(f: &Formula, sym: &str, lo: &mut bool, hi: &mut bool) {
        match f {
            Formula::Le(l, r) => {
                if matches!(&**l, Formula::Int(_)) && r.var_name() == Some(sym) {
                    *lo = true;
                }
                if l.var_name() == Some(sym) && matches!(&**r, Formula::Int(_)) {
                    *hi = true;
                }
            }
            Formula::Ge(l, r) => {
                if l.var_name() == Some(sym) && matches!(&**r, Formula::Int(_)) {
                    *lo = true;
                }
                if matches!(&**l, Formula::Int(_)) && r.var_name() == Some(sym) {
                    *hi = true;
                }
            }
            _ => {}
        }
        for c in f.children() {
            walk(c, sym, lo, hi);
        }
    }
    let (mut lo, mut hi) = (false, false);
    walk(f, sym, &mut lo, &mut hi);
    (lo, hi)
}

fn has_entry_tie(f: &Formula) -> bool {
    if let Formula::Eq(l, r) = f
        && let (Some(a), Some(b)) = (l.var_name(), r.var_name())
        && a == format!("{b}#e")
    {
        return true;
    }
    f.children().iter().any(|c| has_entry_tie(c))
}

fn verdict(vc: &trust_types::VerificationCondition) -> VerificationResult {
    let router = test_router::deterministic_test_router();
    let results = router.verify_all(std::slice::from_ref(vc));
    results.into_iter().next().expect("one verdict per VC").1
}

/// The load-bearing direction. WATCHED FAILING: with the versioned-parameter range
/// pass removed from `conjoin_arg_type_ranges`, this is
/// `Failed { counterexample: n#e = 4294967298 }`.
#[test]
fn the_unranged_entry_sentinel_row_is_no_longer_falsely_refuted() {
    let func = load("entry_sentinel_unranged_overflow");
    let rows = mul_overflow_rows(&func);
    assert!(!rows.is_empty(), "the `n * 3` overflow obligation must exist");
    for vc in &rows {
        let result = verdict(vc);
        assert!(
            !matches!(result, VerificationResult::Failed { .. }),
            "safe code must not be REFUTED: `u32::MAX / 3 * 3` is exactly \
             `u32::MAX`, so the only way to refute this row is to give the \
             entry-valued read of `n` a value outside `u32`.\n  verdict: \
             {result:?}\n  formula: {:?}",
            vc.formula
        );
    }
}

/// MECHANISM + LAUNDERING CONTROL, asserted together so neither can pass vacuously.
///
/// A "fix" that simply DROPPED the pinned def would also silence the refutation and
/// would be wrong, so `n#e` must still be FREE in the formula. And the bound must sit
/// on the SENTINEL ITSELF — asserted directly, which is what keeps the range repair
/// isolated now that the tie is present too.
///
/// RE-DERIVED 2026-08-29: this used to assert `!has_entry_tie`, because the
/// whole-function quantifier refused the tie on every drop-bearing body and the
/// tie's absence was what isolated the range repair. The quantifier is retired;
/// the mint (bb0, unwind-inclusive union `{e}`) is gate-admitted and this fixture
/// now legitimately ties — asserted POSITIVE below so a regression toward the
/// quantifier (tie vanishing again on drop-bearing bodies) is loud.
#[test]
fn the_bound_is_on_the_sentinel_itself_and_the_pinned_fact_survives() {
    let func = load("entry_sentinel_unranged_overflow");
    for vc in &mul_overflow_rows(&func) {
        assert!(
            vc.formula.free_variables().iter().any(|v| v == "n#e"),
            "the pinned in-place-update fact must still be present — dropping it \
             would silence the refutation by deleting the hypothesis"
        );
        assert_eq!(
            range_bounds_on(&vc.formula, "n#e"),
            (true, true),
            "the entry sentinel must carry BOTH its `u32` bounds directly; \
             formula: {:?}",
            vc.formula
        );
        assert!(
            has_entry_tie(&vc.formula),
            "the mint gate admits `#e` here (bb0's full-graph union is the entry \
             seed), so the tie must be present; its absence means the mint gate \
             or the consumer clause regressed toward the retired whole-function \
             veto. formula: {:?}",
            vc.formula
        );
    }
}

/// THE RECOVERY, re-derived 2026-08-29 from `the_precondition_side_gap_is_still_open`
/// — the ledger row that used to assert its own cost (`Failed`, counterexample
/// `n#e = 30, n = 0`: the authored `requires(n < 30)` constrained a symbol the goal
/// never used).
///
/// `tests/data/entry_sentinel_precondition_gap.rs` is `join_weakened_entry_sentinel`
/// plus a droppable local:
///
/// ```text
/// #[trust::requires(n < 30)]
/// pub fn h(mut n: u32, a: &[u8; 10], b: bool, c: bool) -> u8 {
///     let s = String::new();
///     n /= 3;
///     let mut t: u32 = 0;
///     if b { t = 1; } else { t = 2; }
///     let r = if c && t > 0 { a[n as usize] } else { 0 };
///     drop(s);
///     r
/// }
/// ```
///
/// The gap: the tie `Eq(n#e, n)` — the only connector between the `Fact::entry`
/// bucket (preconditions, bare names) and the pinned only-carrier
/// `n#s0_6 == n#e / 3` — was refused by the whole-function `entry_map_covers`
/// quantifier because the `String`'s cleanup cluster (bb10/bb11/bb12, reachable only
/// across unwind edges) has an empty v2 entry map. With entry-denotation ENFORCED AT
/// THE MINT SITE (bb0's unwind-inclusive union is the entry seed `{e}`), the
/// cleanup blocks no longer veto, the consumer versions `n` (token `s0_6`), the tie
/// is conjoined, and the chain closes: `n < 30` and the bare `u32` range reach
/// `n#e`, the pinned def forces `n#s0_6 <= 9`, and the recorded counterexample
/// (`n#e = 30`) is killed.
///
/// # Honest ceiling: `Unknown`, NOT `Proved`
///
/// MEASURED: in-process ay COMPUTES UNSAT but mandatory strict certification
/// rejects the integer-division step ("step t1 uses unverified trust rule") and
/// publishes `Unknown { reason: "… incomplete self-check-rejected" }` — the same
/// ceiling as the tied control and `join_weakened_entry_sentinel`. Calling this row
/// `Proved` would be a relabel, not a recovery; both directions are pinned below,
/// and if certification ever improves, re-derive toward `Proved`.
///
/// # The one remaining cost this row still records
///
/// Bare `n` IS range-bounded while `n#e` is NOT, even post-recovery. MECHANISM
/// (unchanged): `safety.rs`'s `if bounds_kind && count_back_edges(func) == 0
/// { continue; }` skips the whole range battery for a bounds VC in a back-edge-free
/// function, and this fixture is back-edge-free. The skip sits AFTER the
/// precondition conjoin, so it never starved the tie — and with the tie present the
/// bare bounds now reach `n#e` SEMANTICALLY, making the missing literal
/// `rust_type_range_constraint` spelling on `n#e` verdict-irrelevant here. Pinned so
/// a change to the skip is noticed and re-derived, not rediscovered.
#[test]
fn the_precondition_gap_row_recovers_through_the_tie() {
    let func = load("entry_sentinel_precondition_gap");
    let rows: Vec<_> = trust_vcgen::generate_vcs(&func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck))
        .collect();
    assert_eq!(rows.len(), 1, "the `a[n as usize]` bounds obligation must exist");
    for vc in &rows {
        assert!(
            vc.formula.free_variables().iter().any(|v| v == "n#e"),
            "the pinned entry-sentinel read must be present, or this ledger entry \
             is recording the wrong row — and a \"fix\" that dropped the pinned def \
             would silence the refutation by deleting the hypothesis"
        );
        assert!(
            has_entry_tie(&vc.formula),
            "the tie is the RECOVERY's mechanism; without it the precondition \
             cannot reach `n#e` and the false refutation returns. formula: {:?}",
            vc.formula
        );
        // The remaining range-position cost (see the doc comment above).
        assert_eq!(
            (range_bounds_on(&vc.formula, "n"), range_bounds_on(&vc.formula, "n#e")),
            ((true, true), (false, false)),
            "bare `n` bounded, `n#e` literal-unbounded is the measured state (the \
             back-edge-free bounds-lane range skip). If `n#e` is now bounded here, \
             the range battery reaches this lane — re-derive this pin."
        );
        let result = verdict(vc);
        assert!(
            !matches!(result, VerificationResult::Failed { .. }),
            "safe code must not be REFUTED: with the tie conjoined, `n < 30` \
             reaches `n#e` and kills the `n#e = 30, n = 0` counterexample. \
             verdict: {result:?}"
        );
        assert!(
            !matches!(result, VerificationResult::Proved { .. }),
            "MEASURED `Unknown` (ay computes UNSAT; strict certification rejects \
             the division step). If this became `Proved`, the certification \
             ceiling moved — re-derive this pin and the header's scope note: \
             {result:?}"
        );
    }
}

/// NEGATIVE CONTROL: the tie path is provably untouched, and this is the honest
/// ceiling — an `n#e` connected by the tie is `Unknown` too, so `Unknown` (not
/// `Proved`) is all the range repair can deliver on the sibling fixture.
#[test]
fn the_tied_control_row_is_unchanged_and_is_also_only_unknown() {
    let func = load("entry_sentinel_unranged_overflow_tied_control");
    let rows = mul_overflow_rows(&func);
    assert!(!rows.is_empty(), "the control's overflow obligation must exist");
    for vc in &rows {
        assert!(
            has_entry_tie(&vc.formula),
            "the control exists to exercise the TIE path; without a tie it is not \
             a control. formula: {:?}",
            vc.formula
        );
        let result = verdict(vc);
        assert!(
            !matches!(result, VerificationResult::Failed { .. }),
            "the tied control must not be refuted: {result:?}"
        );
        assert!(
            !matches!(result, VerificationResult::Proved { .. }),
            "MEASURED `Unknown` — if this became `Proved` the solver's division \
             reasoning improved and the ceiling claim in this file's header (and \
             in `join_weakened_entry_sentinel_realmir`) must be re-derived: \
             {result:?}"
        );
    }
}
