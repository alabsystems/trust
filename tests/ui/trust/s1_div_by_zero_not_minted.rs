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
//!
//! WENT FULLY SILENT ON 2026-08-28 — CLOSED THE SAME DAY. Measured on stage1
//! `e845462a8`, this file compiled with EXIT 0: two warnings, no error, the
//! div-by-zero row reported as `runtime-checked` rather than refuted. The S1
//! mint was not implicated (nothing is minted here either way); the refutation
//! itself was gone, because the generic bridge's caller-entry grounding gate
//! could not see `_3 == (d == 0)` inside a nested `And`. Full write-up: the
//! header of `tests/ui/trust/wrapping_div_zero_false_proof.rs`.
pub fn div(x: u32, d: u32) -> u32 {
    //~^ ERROR Level 0 safety verification incomplete
    //~| ERROR strict verification failed
    x / d
}
