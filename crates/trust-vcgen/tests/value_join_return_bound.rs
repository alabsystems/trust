//! A same-crate helper's return bound from the value-join interval
//! (`generate::callee_summaries::local_value_const_interval`), over REAL extracted MIR.
//!
//! Source of the fixture: the compiler's OWN whole-crate summary extraction
//! (`mir_drops_elaborated_and_const_checked`, written by `TRUST_RETURN_SUMMARY_DEBUG=<dir>`
//! on a stage 1 of Trust main as merged 2026-10-03), i.e. exactly the bodies the summaries
//! are computed over in a real compile. Its `for` receivers are spelled through a
//! reborrow (`_11 = &mut iter; _10 = &mut (*_11); next(_10)`), which is why this lane
//! also needed the reborrow hop in `iterator_yield`'s range trace and conduit gate.
//!
//! ```text
//! fn argmax_abs(v: [f64; 3]) -> usize {           // best ∈ {0} ∪ (1..3)  =>  [0, 2]
//!     let mut best = 0;
//!     for k in 1..3 { if v[k].abs() > v[best].abs() { best = k; } }
//!     best
//! }
//! fn argmax4(v: [f64; 4]) -> usize { ... for k in 1..4 ... }   // [0, 3]: d[3] stays refuted
//! fn rec(n: usize) -> usize { if n == 0 { 0 } else { rec(n - 1) } }   // recursion: no summary
//! fn arith(n: u32) -> usize { let mut b = 0usize; for k in 0..2usize { if n > 3 { b = k + 1; } } b }
//!                                                  // arithmetic definition: no summary
//! fn reseat(..)          // `let r = &mut it; *r = 1..100;` before `for k in it`: no bound < 99
//! fn reborrow_reseat(..) // `let rr = &mut *r; *rr = 1..100; while let Some(k) = rr.next()`
//! ```
//!
//! Before this lane `argmax_abs` had no return summary (its return local is assigned
//! twice, which the single-assignment chain refuses), so `d[argmax_abs(v)]` on a
//! `[f64; 3]` stayed an unknown row (docs/issues/2026-10-03-alab-level0-precision-gaps-ranked.md).
use trust_types::VerifiableFunction;

fn funcs() -> Vec<VerifiableFunction> {
    serde_json::from_str(include_str!("fixtures/value_join_return_bound_funcs.json"))
        .expect("the captured MIR fixture must deserialize")
}

#[test]
fn a_loop_assigned_return_is_bounded_by_its_value_join() {
    let funcs = funcs();
    let upper = trust_vcgen::compute_return_bound_summaries(&funcs);
    let lower = trust_vcgen::compute_return_lower_bound_summaries(&funcs);
    assert_eq!(upper.get("vj::argmax_abs"), Some(&2));
    assert_eq!(lower.get("vj::argmax_abs"), Some(&0));
    // The bound is the join, not a guess: one more iteration widens it to 3, which
    // does NOT discharge an index into a `[_; 3]`.
    assert_eq!(upper.get("vj::argmax4"), Some(&3));
}

#[test]
fn recursion_and_arithmetic_definitions_get_no_summary() {
    let funcs = funcs();
    let upper = trust_vcgen::compute_return_bound_summaries(&funcs);
    let lower = trust_vcgen::compute_return_lower_bound_summaries(&funcs);
    for f in ["vj::rec", "vj::arith"] {
        assert_eq!(upper.get(f), None, "{f}: upper");
        assert_eq!(lower.get(f), None, "{f}: lower");
    }
}

#[test]
fn an_iterator_reseated_through_a_borrow_or_a_reborrow_gets_no_tight_bound() {
    let funcs = funcs();
    let upper = trust_vcgen::compute_return_bound_summaries(&funcs);
    for f in ["vj::reseat", "vj::reborrow_reseat"] {
        let bound = upper.get(f).copied();
        assert!(
            bound.is_none() || bound >= Some(99),
            "{f}: the iterator was reseated to `1..100`, so a bound below 99 is false; got {bound:?}"
        );
    }
}
