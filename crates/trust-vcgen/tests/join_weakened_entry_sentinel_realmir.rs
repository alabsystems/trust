//! REAL-ARTIFACT precision guard for the lane where the entry-sentinel `n#e` is the
//! ONLY carrier of an in-place update — so leaving it a free variable FALSELY
//! REFUTES safe code.
//!
//! Fixture: the compiler's own extracted input for
//! `tests/data/join_weakened_entry_sentinel.rs`,
//!
//! ```text
//! #[trust::requires(n < 30)]
//! pub fn h(mut n: u32, a: &[u8; 10], b: bool, c: bool) -> u8 {
//!     n /= 3;
//!     let mut t: u32 = 0;
//!     if b { t = 1; } else { t = 2; }
//!     if c && t > 0 { a[n as usize] } else { 0 }
//! }
//! ```
//!
//! `n /= 3` is `bb0[0]: _1 = Div(copy _1, 3)`. `pin_in_place_update_reads` pins the
//! rhs read to the explicit entry token, shipping `n#s0_0 == n#e / 3` with the
//! subject bare — correct, and the reason no recurrence is minted.
//!
//! # The cost this pins
//!
//! `#e` is never minted as a name suffix anywhere else in the crate, so `n#e`
//! unifies with NOTHING. Usually that is invisible, because the semantic-guard map
//! carries an establish-versioned SIBLING (`n#s0_0 == n / 3`, read BARE) that keeps
//! the precondition connected. The diamond `if b { t = 1 } else { t = 2 }` removes
//! it: the guard BFS re-reaches the join with different accumulated guards, replaces
//! the whole inherited set with `[true]`, and skips the successors — while the
//! path-def INTERSECTION keeps the pinned fact. `n#e` is then a free variable
//! occurring once, `n < 30` and `0 <= n` speak about a different symbol, and the
//! bounds row is SATISFIED by `n#e = 300`.
//!
//! MEASURED with the in-process ay: the row was `Failed` — a false refutation of
//! genuinely safe code, which under strict verification is a build error.
//!
//! The repair is the tie `Eq(n#e, n)`, conjoined in the same bucket as the
//! preconditions (where a bare place name IS the entry value). It is an identity
//! between two spellings of one value, not a new hypothesis.
//!
//! HONEST SCOPE: the row does not become `Proved`. The residual obstacle is the
//! solver's integer-division reasoning, not a missing hypothesis — the sibling-
//! bearing variant of this same function (no diamond) is `Unknown` too. What this
//! test pins is that the row is no longer REFUTED, and that the tie is present.

use trust_types::{Formula, VcKind, VerifiableFunction, VerificationResult};

fn load() -> VerifiableFunction {
    let text = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/data/join_weakened_entry_sentinel.json"
    ))
    .expect("fixture must be readable");
    serde_json::from_str(&text).expect("fixture must deserialize")
}

fn bounds_rows(func: &VerifiableFunction) -> Vec<trust_types::VerificationCondition> {
    trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck))
        .collect()
}

fn contains_entry_tie(f: &Formula) -> bool {
    if let Formula::Eq(l, r) = f
        && let (Some(a), Some(b)) = (l.var_name(), r.var_name())
        && a == format!("{b}#e")
    {
        return true;
    }
    f.children().iter().any(|c| contains_entry_tie(c))
}

/// The load-bearing direction: the entry sentinel must be CONNECTED, so the bounds
/// row stops being satisfiable by an arbitrary `n#e`.
#[test]
fn the_join_weakened_bounds_row_is_no_longer_falsely_refuted() {
    let func = load();
    let rows = bounds_rows(&func);
    assert!(!rows.is_empty(), "the `a[n as usize]` bounds obligation must exist");
    let router = trust_router::Router::deterministic_in_process_ay(30_000);
    for vc in &rows {
        let results = router.verify_all(std::slice::from_ref(vc));
        let (_, result) = results.into_iter().next().expect("one verdict per VC");
        assert!(
            !matches!(result, VerificationResult::Failed { .. }),
            "safe code must not be REFUTED: the entry-valued read of `n` is a free \
             symbol, so the solver picks it out of range.\n  verdict: {result:?}\n  \
             formula: {:?}",
            vc.formula
        );
    }
}

/// The mechanism, asserted directly: a version of the repair that merely DROPPED
/// the pinned fact would also stop the refutation, and would be wrong.
#[test]
fn the_pinned_fact_survives_and_its_entry_read_is_tied() {
    let func = load();
    let rows = bounds_rows(&func);
    for vc in &rows {
        assert!(
            contains_entry_tie(&vc.formula),
            "the entry sentinel must be tied to the bare (entry-valued) name; \
             formula: {:?}",
            vc.formula
        );
        assert!(
            vc.formula.free_variables().iter().any(|v| v.ends_with("#e")),
            "the pinned in-place-update fact itself must still be present — \
             dropping it would silence the refutation by deleting the hypothesis"
        );
    }
}

/// Laundering control: the repair must cost nothing in obligations.
#[test]
fn the_fixture_still_carries_its_bounds_obligation_and_no_recurrence() {
    let func = load();
    let vcs = trust_vcgen::generate_vcs(&func);
    assert!(
        !vcs.iter().any(|vc| matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
            if kind == "SelfReferentialDefinition")),
        "no obligation may be degraded by the recurrence backstop: {:?}",
        vcs.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );
    assert!(!bounds_rows(&func).is_empty(), "the bounds row must not be laundered away");
}
