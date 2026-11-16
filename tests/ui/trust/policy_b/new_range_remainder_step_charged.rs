//@ needs-trust-verify
//@ edition: 2021
//@ revisions: rem opt certify controls
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[opt] compile-flags: -Copt-level=3
//@[certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[rem] check-fail
//@[opt] check-fail
//@[certify] check-fail
//@[controls] check-pass
//! **`RangeFromIter::remainder` is charged (NEW-RANGE-REMAINDER-UNCHARGED-1, the wave-24
//! review of NEW-RANGE-ITER-UNCHARGED-1; docs/KNOWN_HAZARDS.md and
//! docs/DECISION_QUEUE.md, NEW-RANGE-REMAINDER-UNCHARGED-1).**
//!
//! The nightly inherent `core::range::iter::RangeFromIter::<A>::remainder`
//! (`new_range_remainder`, `#[rustc_inherit_overflow_checks]`) returns
//! `RangeFrom { start: Step::forward(self.start, 1) }` when the iterator is EXHAUSTED: a
//! `next()` that yields `MAX` sets `exhausted` instead of panicking, so the remainder of
//! an iterator that reached `MAX` panics ("overflow in `Step::forward`" for `char`, the
//! add-overflow check for an integer). It is no `Iterator` method, so the fix of
//! NEW-RANGE-ITER-UNCHARGED-1 (`numeric_panic::range_self`) never saw it. Core's
//! `ops::RangeFrom` has no such method: the route exists only on the new iterators.
//!
//! # Before (stage 1 of `51eac007f3`, `scratchpad/stage1-w24`, measured 2026-10-12 with
//! exactly these revisions' flags plus `--cfg <revision> --emit=metadata`)
//!
//! `rem` and `opt` built rc=0: each function got only "Trust Level 0 safety verification
//! incomplete … 1 runtime-checked", so every annotated error was missing. `certify` built
//! rc=1 (it refuses the runtime-checked rows already). `controls` built rc=0. The witness
//! `new_range_remainder_step_charged_run.rs` (verification OFF) exits 101 at `char::MAX`
//! and `u8::MAX`, as stock nightly rustc does: a false accept, not a miscompile.
//!
//! # After (stage 1 of `046ef49e3e`, `scratchpad/stage1-w24r`, measured 2026-10-12)
//!
//! `rem` and `opt` exit 1 with 6 errors (every function refused, every annotation lands);
//! `certify` exits 1 (8 errors); `controls` exits 0.
//!
//! `numeric_panic::range_from_iter_remainder_elem` reads
//! `core::range::iter::RangeFromIter::<int|char>::remainder` (an authenticated root, the
//! exact type token) and the call takes the fail-closed `range-from-step-overflow-
//! unmodeled` row an advancing `RangeFrom` call takes. Whether the iterator is exhausted
//! is the caller's loop-carried state, so an unexhausted iterator's `remainder` is
//! refused too (the recorded over-refusal, DECISION_QUEUE). The other iterators'
//! `remainder` moves its fields and is total (`controls`).

#![allow(unused)]
#![feature(new_range_remainder)]
use core::range::{Range, RangeFrom, RangeFromIter, RangeInclusive};

#[cfg(any(rem, opt, certify))]
pub fn rem_param(it: RangeFromIter<char>) -> RangeFrom<char> {
    //[rem,opt,certify]~^ ERROR `new_range_remainder_step_charged::rem_param`
    it.remainder()
}

#[cfg(any(rem, opt, certify))]
pub fn rem_char(c: char) -> RangeFrom<char> {
    //[rem,opt,certify]~^ ERROR `new_range_remainder_step_charged::rem_char`
    let mut it = RangeFrom::from(c..).into_iter();
    it.by_ref().take(1).for_each(drop);
    it.remainder()
}

#[cfg(any(rem, opt, certify))]
pub fn rem_u8(x: u8) -> RangeFrom<u8> {
    //[rem,opt,certify]~^ ERROR `new_range_remainder_step_charged::rem_u8`
    let mut it = RangeFrom::from(x..).into_iter();
    it.by_ref().take(1).for_each(drop);
    it.remainder()
}

// ---- controls: the other iterators' `remainder` moves the fields, and cannot panic ----

#[cfg(controls)]
pub fn rem_range(a: u8, b: u8) -> Range<u8> {
    let mut it = Range::from(a..b).into_iter();
    it.by_ref().take(1).for_each(drop);
    it.remainder()
}

#[cfg(controls)]
pub fn rem_incl(a: char, b: char) -> Option<RangeInclusive<char>> {
    let mut it = RangeInclusive::from(a..=b).into_iter();
    it.by_ref().take(1).for_each(drop);
    it.remainder()
}
