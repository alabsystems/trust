// Trust (assumption ledger, Stage 1): the FALSIFIABLE half of
// `refutation_not_swallowed.rs`. That sibling puts the refutation in a SEPARATE
// non-async item and reads it on the advisory lane, where a refuted Level 0
// obligation and a merely runtime-checked one emit the SAME warning text
// ("N obligation(s) were not proved"). Measured 2026-08-15: rewriting its `a / b` to
// `a / (b | 1)` deletes the refutation ("Level 0 summary: 0 failed") and the sibling
// still passes — so it cannot witness a swallowed refutation.
//
// This guard closes that. The unguarded division lives INSIDE the coroutine body, so
// it is the demotion's own item, and the strict lane separates the two outcomes by
// diagnostic KIND: refuted -> `ERROR ... verification incomplete` ("Level 0 summary:
// 1 failed"), swallowed/runtime-checked -> the same text as a WARN with the build
// error coming only from the protocol premise. If the coroutine assumption ever
// absorbs a real data-safety refutation, the pinned ERROR below becomes a WARN and
// this test fails. check-fail because the verify pass runs on the metadata-encoded
// coroutine body at check time.
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ edition: 2021
//@ check-fail
//@ dont-check-compiler-stderr
pub async fn helper(a: u64, b: u64) -> u64 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR coroutine executor-protocol premise is unproved
    //~| ERROR obligation(s) were not fully verified
    a / b
}
//~? RAW Trust: ASSUMPTION [coroutine]
