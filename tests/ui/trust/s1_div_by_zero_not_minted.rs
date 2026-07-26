//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ check-fail
//! Sealed-authority S1 — FAIL-CLOSED on a real safety bug. `x / d` has a genuine
//! division-by-zero obligation (`d` may be `0`); its violation formula is
//! satisfiable, so the gate's re-solve returns `Failed` and mints nothing. The
//! div-by-zero stays a refutation and the build MUST fail — the S1 mint only
//! ever ADDS authority to obligations the gate independently re-proves, never to
//! a genuine violation.
pub fn div(x: u32, d: u32) -> u32 {
    //~^ ERROR Level 0 safety verification incomplete
    //~| ERROR strict verification failed
    x / d
}
