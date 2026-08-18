// Trust (assumption ledger, Stage 1): the assumption demotion must never
// swallow a genuine refutation. The async fn records a coroutine assumption
// row, but the unguarded division in `mid` is refuted and still fails the
// report under the nonfatal lame policy (division panics regardless of overflow-checks,
// so this refutation needs no extra flags). build-pass: the verify pass runs
// when codegen demands optimized_mir, so a non-generic body's refutation
// fires at BUILD time (the check build passes — only metadata-encoded bodies
// like the async closure are visited there).
//
// RE-PINNED 2026-08-15 for upstream 983bc1a3b6 (merged here as f1182b2285), which
// REMOVED the whole-function panic-freedom subsumption as a false proof. THE GUARD
// STILL HOLDS AND WAS RE-MEASURED: `mid` is still refuted with a live model
// ("[divzero] FAILED (ay-in-process); counterexample: a = 0, b = 0", "Level 0 summary:
// 1 failed"), so no refutation is swallowed. The ONLY new diagnostic is on `helper`'s
// coroutine body, whose `assertion:panic-freedom:0` aggregate is that item's sole row:
// the deleted lane discharged it from an EMPTY conjunction, and without that authority
// the row reports runtime-checked (NOT proved). STRONGER-OR-EQUAL: the added warning
// is one MORE unproved obligation surfaced next to an unchanged refutation.
//@ edition: 2021
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: -Ztrust-policy=advisory --crate-type=lib
//@ build-pass
//@ dont-check-compiler-stderr
pub async fn helper(x: u32) -> u32 {
    //~^ WARN Trust Level 0 safety verification incomplete for `refutation_not_swallowed::helper::{closure#0}`: 1 obligation(s) were not proved
    x
}
pub fn mid(a: u64, b: u64) -> u64 {
    //~^ WARN Trust Level 0 safety verification incomplete for `refutation_not_swallowed::mid`: 1 obligation(s) were not proved
    a / b
}
//~? RAW Trust: ASSUMPTION [coroutine]
