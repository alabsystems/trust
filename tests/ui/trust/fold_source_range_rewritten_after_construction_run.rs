//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ revisions: field param fnitem swap mutref slice_inclusive_escape
//@ revisions: closure_field closure_whole inclusive_escape duration_closure duration_mutref
//@ compile-flags: -Ztrust-verify=off -Coverflow-checks=on
//@[field] error-pattern: attempt to add with overflow
//@[param] error-pattern: attempt to add with overflow
//@[fnitem] error-pattern: attempt to add with overflow
//@[swap] error-pattern: attempt to add with overflow
//@[mutref] error-pattern: attempt to add with overflow
//@[slice_inclusive_escape] error-pattern: range end index 100 out of range for slice of length 4
//@[closure_field] error-pattern: attempt to add with overflow
//@[closure_whole] error-pattern: attempt to add with overflow
//@[inclusive_escape] error-pattern: attempt to add with overflow
//@[duration_closure] error-pattern: adding durations should not exceed
//@[duration_mutref] error-pattern: adding durations should not exceed
//@ ignore-emscripten no processes
//! The WITNESS for `fold_source_range_rewritten_after_construction.rs`
//! (CL-FOLD-LOCALDEF-1): the same bodies, built with verification OFF. Each one
//! panics (exit 101), before and after the fix, which changes only whether the
//! VERIFIED build of the same body is accepted. On the stage 1 of `2bf0ad72e3`
//! (`scratchpad/stage1-w22probe`, 2026-10-11) the verified builds all exited 0, with
//! the overflow (or slice, or `Duration`) row `proved`.

#![allow(unused_mut)]

use core::ops::Range;
use std::time::Duration;

#[cfg(field)]
fn f() -> u8 {
    let mut r = 0u8..4;
    r.end = 200;
    r.sum::<u8>()
}

#[cfg(param)]
fn f() -> u8 {
    fn g(n: u8) -> u8 {
        let mut r = 0u8..4;
        r.end = n;
        r.sum::<u8>()
    }
    g(std::hint::black_box(200))
}

#[cfg(fnitem)]
fn widen(q: &mut Range<u8>) {
    q.end = 200;
}

#[cfg(fnitem)]
fn f() -> u8 {
    let mut r = 0u8..4;
    widen(&mut r);
    r.sum::<u8>()
}

#[cfg(swap)]
fn f() -> u8 {
    let mut r = 0u8..4;
    let mut big = 0u8..200;
    core::mem::swap(&mut r, &mut big);
    r.sum::<u8>()
}

#[cfg(mutref)]
fn f() -> u8 {
    let mut r = 0u8..4;
    let p = &mut r;
    p.end = 200;
    r.sum::<u8>()
}

#[cfg(slice_inclusive_escape)]
fn f() -> usize {
    fn g(v: &[u8]) -> usize {
        let mut r = 0usize..=0;
        let p = &mut r;
        *p = 0..=100;
        if v.len() > 0 { v[r].len() } else { 0 }
    }
    g(std::hint::black_box(&[1, 2, 3, 4]))
}

#[cfg(closure_field)]
fn f() -> u8 {
    let mut r = 0u8..4;
    let mut g = || r.end = 200;
    g();
    r.sum::<u8>()
}

#[cfg(closure_whole)]
fn f() -> u8 {
    let mut r = 0u8..4;
    let mut g = || r = 0..200;
    g();
    r.sum::<u8>()
}

#[cfg(inclusive_escape)]
fn f() -> u8 {
    let mut r = 0u8..=3;
    let p = &mut r;
    *p = 0..=200;
    r.sum::<u8>()
}

#[cfg(duration_closure)]
fn f() -> Duration {
    let mut d = Duration::from_secs(1);
    let mut g = || d = Duration::MAX;
    g();
    d + Duration::from_secs(2)
}

#[cfg(duration_mutref)]
fn f() -> Duration {
    let mut d = Duration::from_secs(1);
    let p = &mut d;
    *p = Duration::MAX;
    d + Duration::from_secs(2)
}

fn main() {
    println!("{:?}", f());
}
