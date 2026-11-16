//@ needs-trust-verify
//@ edition: 2021
//@ revisions: default opt certify guarded_loss controls
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[opt] compile-flags: -Copt-level=3
//@[certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[default] check-fail
//@[opt] check-fail
//@[certify] check-fail
//@[guarded_loss] check-fail
//@[controls] check-pass
//! **The stable `core::range` iterators are charged like their `core::ops` twins
//! (NEW-RANGE-ITER-UNCHARGED-1; docs/KNOWN_HAZARDS.md, "FIX PREPARED 2026-10-11 … the
//! stable `core::range` iterators"; docs/DECISION_QUEUE.md, NEW-RANGE-ITER-UNCHARGED-1).**
//!
//! `core::range::{RangeFrom, Range, RangeInclusive}` (stable since 1.95/1.96) are
//! `IntoIterator`; `.into_iter()` gives `core::range::iter::{RangeFromIter, RangeIter,
//! RangeInclusiveIter}`. `RangeFromIter::{next, nth}` call `Step::forward`, which panics
//! past `MAX` ("overflow in `Step::forward`" for `char`, the overflow check for an
//! integer), in every consumer that advances it; `RangeIter::count` and
//! `RangeInclusiveIter::count` forward to the legacy range's `count`, which panics "count
//! overflowed usize". The numeric value-panic family (`generate::numeric_panic`, the
//! ruled class of the CLOSED 2026-09-25 entry and `1f3b181649`) read only the
//! `core::ops::range` types, so the same calls through the new iterators got no row: the
//! iteration sibling of UTF8-CORE-RANGE-INDEX-1 (`core_range_index_charged.rs`).
//!
//! # Before (stage 1 of `1213387e6d`, `scratchpad/stage1-w24probe`, measured 2026-10-11
//! with exactly these revisions' flags plus `--cfg <revision> --emit=metadata`)
//!
//! `default` and `opt` built rc=0 with 18 warnings: each of the eight functions got
//! "Trust Level 0 safety verification incomplete … 1 runtime-checked" (the generic
//! panic-freedom row; `two_from_u8` and `position` also the bundled member's advisory), so
//! every annotated error was missing. `certify` built rc=1 (18 errors; it refuses the
//! runtime-checked row already). `guarded_loss` and `controls` built rc=0. The witness
//! `new_range_iter_step_charged_run.rs` (verification OFF) exits 101 on every body here,
//! at `-O0` and `-O3`, with the same exit codes and messages as stock rustc 1.97.1
//! (`8bab26f4f`, run by path): a false accept, not a miscompile.
//!
//! # After (predicted, not built)
//!
//! `numeric_panic::range_self` reads `core::range::iter::{RangeIter, RangeFromIter,
//! RangeInclusiveIter}<T>` (an authenticated root, the exact type token, `&mut` peeled) as
//! the families `Range`, `RangeFrom` and `RangeInclusive`. Every advancing `RangeFromIter`
//! call then takes the fail-closed `range-from-step-overflow-unmodeled` row its `core::ops`
//! twin `(c..)` takes, and a `count` whose element can overflow `usize` takes
//! `range-count-overflow-unmodeled` (its receiver is an `into_iter` call result, whose bounds
//! are not traced). `default` and `opt` are refused with every annotated error; `certify`
//! is unchanged; `controls` stays rc=0. Predicted from
//! `crates/trust-vcgen/tests/std_numeric_family_realmir.rs` on these bodies' real MIR
//! (dumped by the BEFORE compiler) and from the `core::ops` twins, refused on that compiler.
//!
//! `guarded_loss` pins the cost (rc=0 before, predicted refused after): a guarded new-range
//! `count` over `u64` cannot panic but is refused, while its `core::ops` twin in `controls`
//! keeps its PROVED count row (measured on the BEFORE compiler: `assertion: Iterator::count:
//! count overflowed usize`, proved); and a single `next()` cannot panic at `char::MAX`
//! (core's `exhausted` flag), as for the `core::ops` twin, which is refused the same way.

#![allow(unused)]
use core::range::{Range, RangeFrom, RangeInclusive};
use std::hint::black_box;

// ---- `RangeFromIter`: `Step::forward` past `MAX` in `next`/`nth` and every consumer ----

#[cfg(any(default, opt, certify))]
pub fn two_from(c: char) -> Option<char> {
    //[default,opt,certify]~^ ERROR `new_range_iter_step_charged::two_from`
    let mut it = RangeFrom::from(c..).into_iter();
    it.next();
    it.next()
}

#[cfg(any(default, opt, certify))]
pub fn nth_from(c: char, n: usize) -> Option<char> {
    //[default,opt,certify]~^ ERROR `new_range_iter_step_charged::nth_from`
    RangeFrom::from(c..).into_iter().nth(n)
}

#[cfg(any(default, opt, certify))]
pub fn find_from(c: char) -> Option<char> {
    //[default,opt,certify]~^ ERROR `new_range_iter_step_charged::find_from`
    RangeFrom::from(c..).into_iter().find(|&d| d == 'z')
}

#[cfg(any(default, opt, certify))]
pub fn position(c: char) -> Option<usize> {
    //[default,opt,certify]~^ ERROR `new_range_iter_step_charged::position`
    RangeFrom::from(c..).into_iter().position(|d| d == 'z')
}

// The explicit `&mut` reborrow: `<&mut RangeFromIter<char> as Iterator>::next`.
#[cfg(any(default, opt, certify))]
pub fn byref_next(c: char) -> Option<char> {
    //[default,opt,certify]~^ ERROR `new_range_iter_step_charged::byref_next`
    let mut it = RangeFrom::from(c..).into_iter();
    let r = &mut it;
    r.next();
    r.next()
}

#[cfg(any(default, opt, certify))]
pub fn two_from_u8(x: u8) -> Option<u8> {
    //[default,opt,certify]~^ ERROR `new_range_iter_step_charged::two_from_u8`
    let mut it = RangeFrom::from(x..).into_iter();
    it.next();
    it.next()
}

// ---- `RangeInclusiveIter`/`RangeIter`: "count overflowed usize" ----

#[cfg(any(default, opt, certify))]
pub fn incl_count(a: u64, b: u64) -> usize {
    //[default,opt,certify]~^ ERROR `new_range_iter_step_charged::incl_count`
    RangeInclusive::from(a..=b).into_iter().count()
}

#[cfg(any(default, opt, certify))]
pub fn excl_count(a: u128, b: u128) -> usize {
    //[default,opt,certify]~^ ERROR `new_range_iter_step_charged::excl_count`
    Range::from(a..b).into_iter().count()
}

// ---- guarded_loss: the recorded over-refusal (DECISION_QUEUE NEW-RANGE-ITER-UNCHARGED-1) ----

// A guarded count cannot panic. Its `core::ops` twin (`ops_guarded_u64_incl_count`, in
// `controls`) keeps a PROVED count row, because the bounds of `a..=b` are traced; the new
// iterator's receiver is an `into_iter` call result, whose bounds are not, so it is refused.
#[cfg(guarded_loss)]
pub fn guarded_incl_count(a: u64, b: u64) -> usize {
    //[guarded_loss]~^ ERROR `new_range_iter_step_charged::guarded_incl_count`
    if a <= b && b - a < 1000 { RangeInclusive::from(a..=b).into_iter().count() } else { 0 }
}

// A single `next()` at `char::MAX` does not panic (core's `exhausted` flag), as for the
// `core::ops` twin `(c..).next()`, which is refused the same way.
#[cfg(guarded_loss)]
pub fn single_next_from(c: char) -> Option<char> {
    //[guarded_loss]~^ ERROR `new_range_iter_step_charged::single_next_from`
    RangeFrom::from(c..).into_iter().next()
}

// ---- controls: must stay accepted ----

#[cfg(controls)]
pub fn ops_for_u8(n: u8) {
    for i in 0..n {
        black_box(i);
    }
}

#[cfg(controls)]
pub fn ops_for_usize(n: usize) {
    for i in 0..n {
        black_box(i);
    }
}

#[cfg(controls)]
pub fn ops_for_char() {
    for c in 'a'..='z' {
        black_box(c);
    }
}

#[cfg(controls)]
pub fn ops_char_count() -> usize {
    ('a'..='z').count()
}

#[cfg(controls)]
pub fn ops_u32_incl_count(a: u32, b: u32) -> usize {
    (a..=b).count()
}

#[cfg(controls)]
pub fn ops_guarded_u64_incl_count(a: u64, b: u64) -> usize {
    if a <= b && b - a < 1000 { (a..=b).count() } else { 0 }
}

#[cfg(controls)]
pub fn new_for_u8(n: u8) {
    for x in Range::from(0u8..n) {
        black_box(x);
    }
}

#[cfg(controls)]
pub fn new_char_incl_count(a: char, b: char) -> usize {
    RangeInclusive::from(a..=b).into_iter().count()
}

#[cfg(controls)]
pub fn new_u32_incl_count(a: u32, b: u32) -> usize {
    RangeInclusive::from(a..=b).into_iter().count()
}

#[cfg(controls)]
pub fn new_char_incl_nth(a: char, b: char, n: usize) -> Option<char> {
    RangeInclusive::from(a..=b).into_iter().nth(n)
}

// A lazy adaptor advances nothing at its own call.
#[cfg(controls)]
pub fn new_from_take(c: char) -> impl Iterator<Item = char> {
    RangeFrom::from(c..).into_iter().take(3)
}
