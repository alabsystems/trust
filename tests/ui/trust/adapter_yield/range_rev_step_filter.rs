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
//! D2 tier 1 (2026-09-24): `ADAPTER_YIELD` over a constant `Range` under
//! `Iterator::rev` and `Iterator::step_by`, and through `filter` (item behind
//! `&`). A resolved call may land on a core OVERRIDE (`Rev::try_fold`,
//! `StepBy<Range<usize>>`'s specialization, which repurposes `end` as a
//! remaining-count, `Filter::count`); the adapter is authenticated by the
//! resolved instance's TRAIT ITEM, so core's overrides are admitted and every
//! one of them still applies the closure only to items of the inner range.
//!
//! BEFORE (stage-1 snapshot 4e9fe36bf = the `off` revision): every closure is
//! refused with `[bounds] FAILED … i = 8` (the `filter` one reads `_2* = 8`).

// ZERO-ROW-GATE (2026-10-10) refused this zero-row body in both revisions. Re-pinned
// 2026-10-15 (the merge of 2026-10-14, DECISION_QUEUE D103): in `on` the gate now reads
// the drive-only consumer lane's decision for the `all` call
// (VERIFIED-CALLABLE-ZERO-ROW-PARITY) and every function builds; in `off` the bundled
// `all` carries a `runtime_checked` aggregate (a default-policy warning) and the
// closure is refused on its own row below.
pub fn rev_all(a: &[u8; 8]) -> bool {
    (0..8).rev().all(|i| a[i] == 0)
    //[on]~^ NOTE Trust modeled fact ADAPTER_YIELD: core `Iterator::all` over `(0..8).rev(..)`
    //[off]~^^ ERROR Trust Level 0 safety verification incomplete for `range_rev_step_filter::rev_all::{closure#0}`
    //[off]~^^^ ERROR Trust strict verification failed for `range_rev_step_filter::rev_all::{closure#0}`
    //[off]~^^^^ NOTE [bounds] FAILED
}

pub fn step_by_any(a: &[u8; 8]) -> bool {
    (0..8).step_by(3).any(|i| a[i] == 7)
    //[on]~^ NOTE Trust modeled fact ADAPTER_YIELD: core `Iterator::any` over `(0..8).step_by(..)`
    //[off]~^^ ERROR Trust Level 0 safety verification incomplete for `range_rev_step_filter::step_by_any::{closure#0}`
    //[off]~^^^ ERROR Trust strict verification failed for `range_rev_step_filter::step_by_any::{closure#0}`
    //[off]~^^^^ NOTE [bounds] FAILED
}

pub fn filter_count(a: &[u8; 8]) -> usize {
    (0..8usize).filter(|&i| a[i] > 0).count()
    //[on]~^ NOTE Trust modeled fact ADAPTER_YIELD: core `Iterator::filter` over `0..8` invokes this closure only on items it yields; assumed: item parameter `*_2` has value in [0, 8)
    //[off]~^^ ERROR Trust Level 0 safety verification incomplete for `range_rev_step_filter::filter_count::{closure#0}`
    //[off]~^^^ ERROR Trust strict verification failed for `range_rev_step_filter::filter_count::{closure#0}`
    //[off]~^^^^ NOTE [bounds] FAILED
}
