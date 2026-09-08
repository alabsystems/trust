// Trust (assumption ledger, Stage 1): the assumption demotion must never
// swallow a genuine refutation. The async fn records a coroutine assumption
// row, but the unguarded division in `mid` is refuted and still fails the
// report under the nonfatal lame policy (division panics regardless of overflow-checks,
// so this refutation needs no extra flags). build-pass: the verify pass runs
// when codegen demands optimized_mir, so a non-generic body's refutation
// fires at BUILD time (the check build passes — only metadata-encoded bodies
// like the async closure are visited there).
//
// RE-PINNED 2026-08-22 for D2 (0e9090f03b): the coroutine premise is published as an
// ASSUMPTION row again, not as the `CONTRACT [coroutine-resume-state]` row that
// `ca53846043` had substituted in every lane. THE GUARD THIS FILE OWNS IS UNTOUCHED AND
// WAS RE-MEASURED on stage2 ec4783d80 with this file's own flags: `mid` is still refuted
// with a live model ("[divzero] FAILED (ay-in-process); counterexample: _3 = true, a = 0,
// b = 0", "Level 0 summary: 1 failed") and still emits the warning pinned on it below.
//
// What the same run emits for the coroutine body — the raw row and the warning are now
// pinned rather than left unmatched; the `note:` summary is quoted here, not pinned:
//
//     Trust: ASSUMPTION [coroutine] `refutation_not_swallowed::helper::{closure#0}`
//     note: Trust verification: 1 conditionally discharged (NOT proved), 2 failed,
//         0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 5 obligation(s)
//     warning: ... `refutation_not_swallowed::helper::{closure#0}`: 3 obligation(s)
//         were not proved
//
// Both warnings survive to the human surface side by side, which is the whole point: the
// demotion did not absorb `mid`. The falsifiable half lives in the sibling
// `refutation_not_swallowed_strict.rs`, which puts the division INSIDE the coroutine body
// and separates the two outcomes by diagnostic kind.
//
// RE-MEASURED 2026-08-30 on stage1 at fb48832dc9. THE GUARD THIS FILE OWNS STILL HOLDS:
// `mid` is refuted with a live model — "[divzero] FAILED (ay-in-process); counterexample:
// _3 = true, a = 0, b = 0", "1 failed" — and its warning below is unchanged. The
// coroutine body's count moved 3 -> 1: the two sentinel-family rows that measured FAILED
// on ec4783d80 decide UNSAT under the exactly-grounded resume-state entry premise and
// report as CONDITIONALLY DISCHARGED (NOT proved) — "3 conditionally discharged (NOT
// proved), 0 failed, ... 1 runtime-checked, 1 skipped out of 5". Root cause:
// trust-vcgen's 2026-08-28 assert-refutation grounding family (e7a2860143 and siblings).
// The demotion still absorbed nothing: divzero refutations ride a kind the bridge's
// assertion-polarity hold does not touch.
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
//~? RAW Trust: ASSUMPTION [coroutine] `refutation_not_swallowed::helper::{closure#0}`
