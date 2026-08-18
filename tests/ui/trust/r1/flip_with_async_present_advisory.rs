//@ edition: 2021
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: -Ztrust-policy=advisory
//@ compile-flags: --crate-type=lib
//@ check-pass
//@ dont-check-compiler-stderr
// R1 REGRESSION PIN (the observable half). Sibling of
// `flip_with_async_present.rs`, which pins the strict coroutine REFUSAL. That
// refusal is a hard error, and it aborts the run before `scaled` is ever
// verified — so the strict file cannot see whether R1 survived the `async fn`.
// This file runs the same crate under `-Ztrust-policy=advisory`, where the
// coroutine refusal is a warning, the run continues, and `scaled` is reached.
//
// THE PIN: exactly ONE diagnostic, the coroutine's. `scaled`'s `x / divisor`
// must be DISCHARGED by R1 caller coverage (`api` establishes `divisor = 4`),
// which requires the crate-wide caller scan to have read the coroutine body
// through `optimized_mir` instead of the already-stolen elaborated `Steal`.
// FALSIFIED 2026-08-15: with `scaled(x, x)` in place of `scaled(x, 4)` this
// file emits a SECOND warning, `... incomplete for `..::scaled``, and fails —
// the same shape an R1-poisoned scan produces.
fn scaled(x: u32, divisor: u32) -> u32 {
    x / divisor
}

#[inline]
pub fn api(x: u32) -> u32 {
    scaled(x, 4)
}

pub async fn helper(x: u32) -> u32 {
    //~^ WARN Trust Level 0 safety verification incomplete
    x
}
