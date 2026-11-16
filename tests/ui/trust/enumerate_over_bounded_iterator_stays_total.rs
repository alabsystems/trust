//@ needs-trust-verify
//@ only-64bit
//@ revisions: certify strict
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[strict] compile-flags: -Ztrust-policy=strict
//@ rustc-env:TRUST_PF_REG_TRACE=1
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! HONEST CONTROLS for DC-1 (see `enumerate_counter_overflow_not_credited.rs`).
//!
//! `total_std_iterator_ty` now admits `Enumerate<I>` only when `I` provably yields
//! at most `usize::MAX` items. Every inner iterator below does, so its counter
//! (`count`, and `count + n` in an `nth` that returns `Some`) is the index of an item
//! the inner really yielded and cannot overflow: each function must stay registered
//! panic-free under both policies.
//!
//! * `skip_enumerate_u32`: `Range<u32>` holds at most `2^32 - 1` items (the lead's
//!   own control; credited before the fix as well).
//! * `skip_enumerate_u64`: `Range<u64>` holds at most `2^64 - 1 = usize::MAX` items
//!   on a 64-bit target (hence `only-64bit`; on a 32-bit target it is over-long).
//! * `enumerate_take_u128`: `Take` bounds any inner by its `usize` count.
//! * `enumerate_slice`: a slice iterator yields one item per element.
//! * `range_u128`: a bare `Range<u128>` does not count, so it is unaffected.
//! * `position_of`, `last_index`: the everyday `for (i, x) in ….enumerate()` loops
//!   over a slice and over a `u32` range.
use std::iter::{Enumerate, Skip, Take};
use std::ops::Range;

pub fn skip_enumerate_u32(it: &mut Skip<Enumerate<Range<u32>>>) -> Option<usize> {
    match it.next() {
        Some((i, _)) => Some(i),
        None => None,
    }
}

pub fn skip_enumerate_u64(it: &mut Skip<Enumerate<Range<u64>>>) -> Option<usize> {
    match it.next() {
        Some((i, _)) => Some(i),
        None => None,
    }
}

pub fn enumerate_take_u128(it: &mut Enumerate<Take<Range<u128>>>) -> Option<usize> {
    match it.next() {
        Some((i, _)) => Some(i),
        None => None,
    }
}

pub fn enumerate_slice(it: &mut Enumerate<std::slice::Iter<'_, u8>>) -> Option<usize> {
    match it.next() {
        Some((i, _)) => Some(i),
        None => None,
    }
}

pub fn range_u128(it: &mut Range<u128>) -> Option<u128> {
    it.next()
}

pub fn position_of(s: &[u8], b: u8) -> Option<usize> {
    for (i, &x) in s.iter().enumerate() {
        if x == b {
            return Some(i);
        }
    }
    None
}

pub fn last_index(n: u32) -> Option<usize> {
    let mut last = None;
    for (i, _) in (0..n).enumerate() {
        last = Some(i);
    }
    last
}

//~? RAW [PF_REG] fn=enumerate_over_bounded_iterator_stays_total::skip_enumerate_u32 established=true
//~? RAW [PF_REG] fn=enumerate_over_bounded_iterator_stays_total::skip_enumerate_u64 established=true
//~? RAW [PF_REG] fn=enumerate_over_bounded_iterator_stays_total::enumerate_take_u128 established=true
//~? RAW [PF_REG] fn=enumerate_over_bounded_iterator_stays_total::enumerate_slice established=true
//~? RAW [PF_REG] fn=enumerate_over_bounded_iterator_stays_total::range_u128 established=true
//~? RAW [PF_REG] fn=enumerate_over_bounded_iterator_stays_total::position_of established=true
//~? RAW [PF_REG] fn=enumerate_over_bounded_iterator_stays_total::last_index established=true
