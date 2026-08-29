//@ edition: 2021
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
// R1 REGRESSION PIN, strict lane, with a coroutine body present in the crate.
//
// An `async fn`'s coroutine body (`helper::{closure#0}`) has its elaborated MIR
// stolen at ANALYSIS phase — computing the coroutine's layout forces
// `optimized_mir(coroutine)`, whose first act is that steal. When the scan read
// every fn-like body through the elaborated `Steal`, the coroutine came back
// stolen and POISONED the whole crate: R1 was silently disabled for every crate
// containing an `async fn`. The scan now routes coroutine bodies by IDENTITY
// through `optimized_mir`, the steal consumer.
//
// RE-PINNED 2026-08-22 for `0e9090f03b` ("D2"), which made `PublishContractRow`
// unreachable under strict and so restored the coroutine refusal on this lane.
// MEASURED on stage2 `ec4783d80` with this file's own flags: exit 1 and THREE
// errors, all on `helper::{closure#0}`, alongside a raw
// `Trust: ASSUMPTION [coroutine]` row. The text this replaces had retargeted the
// file onto a `CONTRACT [coroutine-resume-state]` row and a passing lane; at this
// HEAD the compiler emits neither. All three errors and the assumption row are
// pinned below, so a silent compiler still fails this file.
//
// THE R1 ARM IS NOT OBSERVABLE ON THIS LANE — RECORDED, NOT PAPERED OVER.
// MEASURED falsification: with `scaled(x, x)` in place of `scaled(x, 4)` the
// strict output does not mention `scaled` anywhere — the same three coroutine
// errors, exit 1, and nothing to tell a poisoned scan from a healthy one. Nothing
// downstream of the coroutine body gets verified here. The live R1
// discrimination is therefore the advisory sibling
// `flip_with_async_present_advisory.rs`, where that same poisoned variant DOES
// emit a second warning naming `scaled` (measured). What this file still pins is
// the strict refusal in the R1 crate shape: an `async fn` sitting next to
// R1-eligible code is fail-closed, never silent.
fn scaled(x: u32, divisor: u32) -> u32 {
    x / divisor
}

#[inline]
pub fn api(x: u32) -> u32 {
    scaled(x, 4)
}

// The poison trigger: mere PRESENCE of a coroutine body in the crate.
pub async fn helper(x: u32) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete for `flip_with_async_present::helper::{closure#0}`
    //~| ERROR Trust strict verification failed for `flip_with_async_present::helper::{closure#0}`: coroutine executor-protocol premise is unproved
    //~| ERROR Trust strict verification failed for `flip_with_async_present::helper::{closure#0}`: 3 obligation(s) were not fully verified
    x
}
//~? RAW Trust: ASSUMPTION [coroutine] `flip_with_async_present::helper::{closure#0}`
