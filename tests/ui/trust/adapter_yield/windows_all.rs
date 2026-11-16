//@ revisions: on off
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[off] compile-flags: -Ztrust-no-adapter-yield
//@[on] check-pass
//@[off] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! D2 tier 1 (2026-09-24): the `ADAPTER_YIELD` modeled fact on the shape of
//! ordinary-rust sweep `s23` and idiomatic sample `i13`
//! (`v.windows(2).all(|w| w[0] <= w[1])`).
//!
//! `Iterator::all` over `<[T]>::windows(2)` invokes the closure only on
//! sub-slices of length 2 (std's contract; docs/TCB.md, "Modeled-fact axioms").
//! The compiler traces the receiver to the constant-size `windows` call and the
//! closure to its single by-value use, and installs the premise; vcgen conjoins
//! `w__slice_len == 2` and both bounds rows prove.
//!
//! BEFORE (stage-1 snapshot of main 4e9fe36bf, which has no premise; the `off`
//! revision is that behaviour): rc=1, the closure root refused with
//! `0 proved, 2 failed` — `[slice] FAILED … w__slice_len = 1` and `= 0`. The
//! parent carries one runtime-checked `[assert]` row (a warning, unchanged).
//!
//! The `on` NOTE pins are the mechanism: the proved count on the closure and
//! the disclosure naming the fact. Without the premise the closure is an error.

pub fn is_sorted(v: &[u32]) -> bool {
    v.windows(2).all(|w| w[0] <= w[1])
    //[on]~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 2 obligation(s)
    //[on]~| NOTE Trust modeled fact ADAPTER_YIELD: core `Iterator::all` over `<[T]>::windows(2)` invokes this closure only on items it yields; assumed: item parameter `_2` has slice length 2
    //[off]~^^^ ERROR Trust Level 0 safety verification incomplete for `windows_all::is_sorted::{closure#0}`: 2 obligation(s) were not proved
    //[off]~^^^^ ERROR Trust strict verification failed for `windows_all::is_sorted::{closure#0}`: 2 obligation(s) were not fully verified
    //[off]~^^^^^ NOTE [slice] FAILED
}
