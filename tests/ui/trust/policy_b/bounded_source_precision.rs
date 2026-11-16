//@ needs-trust-verify
//@ edition: 2021
//@ revisions: bounded charged
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[bounded] check-pass
//@[charged] check-fail
//! Precision follow-ups to `docs/DECISION_QUEUE.md` D12 option (a) (review round 56):
//! the bounded-source capacity grant now walks `zip`/`fuse`/`skip_while`/`map_while`,
//! sizes a fat reference at 16 bytes, and models `BinaryHeap::extend`. The `charged`
//! revision keeps what the axiom still requires: a destination item more than twice
//! the source's, and `peekable`, whose lower bound after a peek exceeds a str view's
//! `+ 1`.
#![allow(dead_code)]
use std::collections::BinaryHeap;

/// ordsweep2 iterators/c15: `zip` yields at most its receiver's count.
#[cfg(bounded)]
pub fn gaps(xs: &[i32]) -> Vec<u32> {
    xs.iter().zip(xs.iter().skip(1)).map(|(&a, &b)| a.abs_diff(b)).collect()
}

/// A `&str` item is a 16-byte fat reference, so 24-byte `String`s fit.
#[cfg(bounded)]
pub fn owned(w: &[&str]) -> Vec<String> {
    w.iter().map(|s| s.to_string()).collect()
}

#[cfg(bounded)]
pub fn tail_after(v: &[u32]) -> Vec<u32> {
    v.iter().copied().fuse().skip_while(|&x| x < 3).collect()
}

#[cfg(bounded)]
pub fn heap_extend(h: &mut BinaryHeap<u32>, v: &[u32]) {
    h.extend(v.iter().copied())
}

/// Two bytes in, sixteen bytes out per item: a factor of 16.
#[cfg(charged)]
pub fn zip_wide(a: &[u8], b: &[u8]) -> Vec<(u64, u64)> {
    //[charged]~^ ERROR Trust Level 0 safety verification incomplete for `bounded_source_precision::zip_wide`
    a.iter().zip(b).map(|(&x, &y)| (x as u64, y as u64)).collect()
}

#[cfg(charged)]
pub fn peeked(v: &[u32]) -> Vec<u32> {
    //[charged]~^ ERROR Trust Level 0 safety verification incomplete for `bounded_source_precision::peeked`
    v.iter().copied().peekable().collect()
}
