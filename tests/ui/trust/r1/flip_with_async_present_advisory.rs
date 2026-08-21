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
// RE-PIN 2026-08-20 (D2). THE R1 DISCRIMINATION IS INTACT AND IS WHY THIS FILE
// EXISTS: `scaled` must emit NOTHING. An R1-poisoned scan makes `scaled`'s
// `x / divisor` undischarged, which emits a warning this file does not expect
// and therefore FAILS — exactly as before. The coroutine's own WARN pin moved to
// the RAW assumption pin below (its "1 obligation(s)" count described a vanished
// inventory; see the assumption-rows siblings), so the discrimination now rests
// on "no diagnostic from `scaled`" plus a positive pin on the coroutine's
// assumption row, rather than on counting the coroutine's own warning.
fn scaled(x: u32, divisor: u32) -> u32 {
    x / divisor
}

#[inline]
pub fn api(x: u32) -> u32 {
    scaled(x, 4)
}

pub async fn helper(x: u32) -> u32 {
    x
}
//~? RAW Trust: ASSUMPTION [coroutine]
