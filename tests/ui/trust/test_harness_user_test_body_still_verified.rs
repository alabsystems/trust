//@ needs-trust-verify
//@ compile-flags: --test -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Trust (CB4): excluding the libtest harness never excuses a test's OWN body.
//! The runner closure and the harness `main` are excluded, but `overflows` is
//! user code and is verified: its `x + 100` is REFUTED (MEASURED before CB4 on
//! `unitfail`: `overflows#1` FAILED with counterexample `x = 156`).
//!
//! The annotations name the full backticked path of the USER function
//! (`overflows#1` — the descriptor const took `#0`), so neither can be
//! satisfied by an error on the runner closure `overflows::{closure#0}`. Before
//! CB4 this file also raised unannotated errors on that closure and on `main`.
//!
//! MEASURED on the Track B stage 1 (2026-09-28): both headlines, on `overflows#1`,
//! are the only errors, and the closure and `main` raise none.

#[test]
fn overflows() {
    //~^ ERROR Trust Level 0 safety verification incomplete for `test_harness_user_test_body_still_verified::overflows#1`
    //~| ERROR Trust strict verification failed for `test_harness_user_test_body_still_verified::overflows#1`
    let x: u8 = core::hint::black_box(200);
    let _y = x + 100;
}
