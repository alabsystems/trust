//@ needs-trust-verify
//@ edition: 2021
// `aux-crate`: the aux's crate NAME is its file stem, `core`.
//@ aux-crate: fakecore=core.rs
//@ compile-flags: --crate-type lib -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! ARGS-FINGERPRINT-READ-1 round 2 (2026-10-07) — A `RangeFull` FROM A CRATE NAMED
//! `core` IS NOT THE REAL ONE, THOUGH IT RENDERS THE SAME.
//!
//! The extractor's display printer stamps no crate identity inside a callee's generic
//! arguments, so `v.drain(fakecore::ops::range::RangeFull)` renders
//! `alloc::vec::Vec::<u32>::drain::<core::ops::range::RangeFull>`, the real `..`'s
//! spelling, plus the duplicate-crate-name argument fingerprint. Round 1 of this fix
//! read past that fingerprint and granted the cannot-panic `RangeFull` carve-out: the
//! `Call::drain::panic-freedom-unverified` refutation disappeared for a drain that
//! panics ("range start index 1000 out of range for slice of length 3" as a binary,
//! measured by the round-1 review). Round 2: the producer tags a call exactly when an
//! argument names a crate whose name does not identify it, and the `RangeFull` reader
//! declines on a tagged call.
//!
//! The real `..` in this graph is refused too: `core` itself is the duplicated name,
//! so its `RangeFull` cannot be told from the forged one by the display (fail-closed).
//!
//! MEASURED 2026-10-07 by hand on the same source (`-Ztrust-verify=on`): the preview3
//! stage 1 (main `7be75e9a80`) and the stage 1 of round 2 (`aee521e4b0` + this change)
//! both report `1 failed` (the drain refutation) and `2 obligation(s) were not proved`
//! for each function; the round-1 stage 1 reported the forged drain with no failed row
//! (review: SUMMARY failed 1 -> 0).

pub fn forged(v: &mut Vec<u32>) -> usize {
    //~^ NOTE 0 proved, 1 failed
    //~| ERROR Trust Level 0 safety verification incomplete for `drain_range_full_from_forged_core::forged`: 2 obligation(s) were not proved
    let r = fakecore::ops::range::RangeFull;
    v.drain(r).count()
}

pub fn real(v: &mut Vec<u32>) -> usize {
    //~^ NOTE 0 proved, 1 failed
    v.drain(..).count()
}
