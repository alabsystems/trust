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
//! The `String` removes it: the cleanup blocks it creates (`bb9 Resume`,
//! `bb10 Drop unwind=Terminate`) have an EMPTY entry-version map, so
//! `entry_sentinel_tie_is_sound`'s MINT-SIDE clause refuses the tie for the whole
//! function. The diamond then weakens the bare-read sibling def away, leaving the
//! pinned `n#s0_5 == n#e / 3` as the only carrier.
//!
//! MEASURED with the in-process ay, range repair disabled:
//!   `Failed`, counterexample `n#e = 4294967298` — three above `u32::MAX`.
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
    let router = trust_router::Router::deterministic_in_process_ay(30_000);
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
/// on the SENTINEL ITSELF, not be smuggled in through a tie — this MIR is exactly the
/// drop-bearing shape the mint-side clause refuses, so `tie` must stay false.
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
            !has_entry_tie(&vc.formula),
            "this fixture's cleanup blocks make the mint-side clause refuse the \
             tie; if a tie appears the fixture no longer isolates the RANGE, and \
             the guard is measuring the tie instead"
        );
    }
}

/// KNOWN COST, recorded so it is not rediscovered: ranging the sentinel is NECESSARY
/// BUT NOT SUFFICIENT.
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
/// MEASURED both with and without the range repair: `Failed`, counterexample
/// `n#e = 30`. That value is INSIDE `u32`, so even a ranged `n#e` is satisfied by it
/// — this row needs the PRECONDITION `n < 30` to reach `n#e`, and only the tie
/// carries that. Preconditions, path guards and semantic guards are all conjoined as
/// `Fact::entry` and are deliberately EXEMPT from the version rename, so all three
/// name the BARE place only.
///
/// This must NOT be closed by conjoining `n < 30` onto `n#e`: that is a
/// point-dependent value fact, exactly the unsound point-to-point assertion the tie's
/// refusals exist to prevent. A type range is point-INDEPENDENT, which is the whole
/// reason the repair above needs no refusal of its own.
///
/// # A SECOND, independent cost this row also records
///
/// MEASURED here: on this row bare `n` IS range-bounded but `n#e` is NOT, even with
/// the repair in place. The versioned pass is FORMULA-DRIVEN — it bounds the
/// versioned spellings actually present when `conjoin_arg_type_ranges` runs — while
/// the bare loop is signature-driven and deliberately unconditional, precisely
/// because "a parameter that reaches the VC only through a cross-block definition is
/// conjoined onto this formula only later, after this point" (that loop's own
/// docstring). In this bounds lane the pinned `n#s0_6 == n#e / 3` arrives AFTER, so
/// the versioned symbol is not yet visible and gets no bound.
///
/// That is a real limitation of the repair, not a property of this fixture: it fires
/// where the pinned def is already present (the overflow lane, as in the sibling
/// fixture) and misses where the def is conjoined later. It was left unfixed rather
/// than papered over — closing it means running the pass at a later position or at
/// several, which is a larger change than the one measured here, and the corpus shows
/// the current repair is verdict-neutral everywhere else.
///
/// So this row is `Failed` for TWO independent reasons, and the range repair
/// addresses NEITHER. If it ever stops being `Failed`, re-derive both.
#[test]
fn the_precondition_side_gap_is_still_open() {
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
             is recording the wrong row"
        );
        // The SECOND cost, pinned as a measurement rather than left as prose.
        // MECHANISM, found by an adversarial re-read and stated exactly because a
        // plausible-but-wrong reason in a comment is the defect this file exists to
        // catch: `safety.rs`'s `if bounds_kind && count_back_edges(func) == 0
        // { continue; }` skips the whole conjoin for a bounds VC in a back-edge-free
        // function, and this fixture is back-edge-free. It is NOT that the
        // versioned pass fails to reach `n#e` — given the chance it would.
        assert_eq!(
            (range_bounds_on(&vc.formula, "n"), range_bounds_on(&vc.formula, "n#e")),
            ((true, true), (false, false)),
            "bare `n` bounded but `n#e` unbounded is the measured state. If `n#e` is \
             now bounded here, the versioned pass reaches this lane and the \
             limitation documented above has been closed — re-derive it."
        );
        assert!(
            matches!(verdict(vc), VerificationResult::Failed { .. }),
            "this row is the recorded KNOWN COST of the precondition-side gap; if it \
             now passes, re-derive this test and the scope note in this file's header"
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
