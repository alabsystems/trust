//@ edition: 2021
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: -Ztrust-policy=advisory
//@ compile-flags: --crate-type=lib
//@ check-pass
//@ dont-check-compiler-stderr
// R1 REGRESSION PIN (the observable half). Sibling of
// `flip_with_async_present.rs`, which pins the strict coroutine REFUSAL. That
// refusal is a hard error and nothing downstream of the coroutine body is
// verified after it — so the strict file cannot see whether R1 survived the
// `async fn`. This file runs the same crate under `-Ztrust-policy=advisory`,
// where the coroutine refusal is a warning, the run continues, and `scaled` is
// reached.
//
// THE PIN: exactly ONE diagnostic that demands an annotation, the coroutine's
// warning. `scaled`'s `x / divisor` must be DISCHARGED by R1 caller coverage
// (`api` establishes `divisor = 4`), which requires the crate-wide caller scan to
// have read the coroutine body through `optimized_mir` instead of the
// already-stolen elaborated `Steal`.
//
// RE-PINNED 2026-08-22 for `0e9090f03b` ("D2"), which made `PublishContractRow`
// unreachable under strict and restored the ASSUMPTION row here. MEASURED on
// stage2 `ec4783d80` with this file's own flags: exit 0, ONE warning (the
// coroutine's, pinned below), a raw `Trust: ASSUMPTION [coroutine]` row (pinned
// below), and for `scaled` an R1 ADMITTED FLIP (visible under `TRUST_R1_TRACE=1`)
// whose note reads "2 proved, 0 failed ... out of 2 obligation(s)". The text this
// replaces claimed a `CONTRACT [coroutine-resume-state]` row and ZERO warnings;
// neither is true at this HEAD.
//
// THE R1 GUARD, RE-FALSIFIED AT THIS HEAD: with `scaled(x, x)` in place of
// `scaled(x, 4)` this file emits a SECOND warning, `... incomplete for
// `..::scaled``, on a line no annotation here covers — so it fails the file,
// which is exactly the shape an R1-poisoned scan produces.
fn scaled(x: u32, divisor: u32) -> u32 {
    x / divisor
}

#[inline]
pub fn api(x: u32) -> u32 {
    scaled(x, 4)
}

pub async fn helper(x: u32) -> u32 {
    // RE-PINNED 2026-09-14: advisory reports the conditional rows in a NOTE, not the
    // Level-0 incomplete WARN.
    x
}
//~? RAW Trust: ASSUMPTION [coroutine] `flip_with_async_present_advisory::helper::{closure#0}`
