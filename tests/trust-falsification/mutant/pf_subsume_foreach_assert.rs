#![crate_type = "lib"]
// MUTANT (FALSE PROOF regression, 2026-08-14 — the `for`-over-array shape).
//
// `f(&[200, 0, 0, 0])` panics. The verifier MUST refuse this (exit 1).
//
// The whole-function `assertion:panic-freedom:0` aggregate is the ONLY row this
// function publishes (the `for &x in a` loop over a fixed-size array emits no
// bounds or overflow obligation, and `t ^= x` cannot overflow), so the
// structural-subsumption lane discharged it from an EMPTY conjunction —
// `all()` over no rows is vacuously true. Closed first by the non-empty-
// conjunction guard, and now by removing the lane outright: the aggregate
// covers a diverging `assert!` Call that has no per-site row, so no conjunction
// over sibling rows can ever entail it.
pub fn f(a: &[u8; 4]) -> u8 {
    let mut t = 0u8;
    for &x in a {
        assert!(x != 200);
        t ^= x;
    }
    t
}
