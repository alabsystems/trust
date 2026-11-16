//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ revisions: two_from two_from_opt nth_from find_from two_from_u8 incl_count excl_count
//@ compile-flags: -Ztrust-verify=off
//@[two_from_opt] compile-flags: -Copt-level=3
//@[two_from] error-pattern: overflow in `Step::forward`
//@[two_from_opt] error-pattern: overflow in `Step::forward`
//@[nth_from] error-pattern: overflow in `Step::forward`
//@[find_from] error-pattern: overflow in `Step::forward`
//@[two_from_u8] error-pattern: attempt to add with overflow
//@[incl_count] error-pattern: count overflowed usize
//@[excl_count] error-pattern: count overflowed usize
//@ ignore-emscripten no processes
//! The WITNESS for `new_range_iter_step_charged.rs` (NEW-RANGE-ITER-UNCHARGED-1): its
//! check-fail bodies, built with verification OFF, each called with the panicking value.
//! Every revision exits 101 with core's own message, before and after the fix, which
//! changes only whether the VERIFIED build of the same bodies is accepted (it was, rc=0,
//! on the stage 1 of `1213387e6d`).
//!
//! Measured 2026-10-11 on the stage 1 of `1213387e6d` (`scratchpad/stage1-w24probe`), this
//! file's flags plus `--cfg <revision>`: `two_from(char::MAX)` (also at `-Copt-level=3`),
//! `nth_from('a', usize::MAX)` and `find_from('{')` exit 101 at
//! `library/core/src/iter/range.rs:93:45` "overflow in `Step::forward`";
//! `two_from_u8(u8::MAX)` exits 101 at `range.rs:438:1` "attempt to add with overflow";
//! `incl_count(0, u64::MAX)` and `excl_count(0, u128::MAX)` exit 101 at `range.rs:1419:14`
//! and `range.rs:1000:59` "count overflowed usize". Stock rustc 1.97.1 (`8bab26f4f`, run by
//! path) gives the same exit codes and messages.

#![allow(unused)]
use core::range::{Range, RangeFrom, RangeInclusive};
use std::hint::black_box;

#[inline(never)]
fn two_from(c: char) -> Option<char> {
    let mut it = RangeFrom::from(c..).into_iter();
    it.next();
    it.next()
}

#[inline(never)]
fn nth_from(c: char, n: usize) -> Option<char> {
    RangeFrom::from(c..).into_iter().nth(n)
}

#[inline(never)]
fn find_from(c: char) -> Option<char> {
    RangeFrom::from(c..).into_iter().find(|&d| d == 'z')
}

#[inline(never)]
fn two_from_u8(x: u8) -> Option<u8> {
    let mut it = RangeFrom::from(x..).into_iter();
    it.next();
    it.next()
}

#[inline(never)]
fn incl_count(a: u64, b: u64) -> usize {
    RangeInclusive::from(a..=b).into_iter().count()
}

#[inline(never)]
fn excl_count(a: u128, b: u128) -> usize {
    Range::from(a..b).into_iter().count()
}

fn main() {
    #[cfg(any(two_from, two_from_opt))]
    black_box(two_from(black_box(char::MAX)));
    #[cfg(nth_from)]
    black_box(nth_from(black_box('a'), black_box(usize::MAX)));
    #[cfg(find_from)]
    black_box(find_from(black_box('{')));
    #[cfg(two_from_u8)]
    black_box(two_from_u8(black_box(u8::MAX)));
    #[cfg(incl_count)]
    black_box(incl_count(black_box(0), black_box(u64::MAX)));
    #[cfg(excl_count)]
    black_box(excl_count(black_box(0), black_box(u128::MAX)));
}
