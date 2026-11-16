//@ needs-trust-verify
//@ edition: 2021
//@ revisions: raw_const raw_mut
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
#![allow(dead_code, unused_mut)]
//! INT-RAWCONST-HAVOC-1 (docs/KNOWN_HAZARDS.md, docs/DECISION_QUEUE.md): a `&raw const`
//! escape is a write channel. The two revisions differ ONLY in the borrow
//! (`raw!(x)` is `&raw const x` or `&raw mut x`), and each body writes through the
//! pointer before reading the local again.
//!
//! vcgen's general havoc list counted `&mut` and `&raw mut` borrows only, so under
//! `raw_const` the fact `x == 5` (`i == 1`) survived the write. Measured BEFORE the fix
//! on the stage 1 at `scratchpad/stage1-w17` (2026-10-06), with these flags: under
//! `raw_const` the overflow rows of `atomic_store` and `cast_store` were `proved`
//! (trust-full-verifier, clean-kernel certified; TRUST_ELIDE elided both checks) and
//! the bounds row of `index_store` was `proved` (ay-in-process); the build failed only
//! on the unrelated `[hardened_unsafe_operation]` rows. Under `raw_mut` all three rows
//! were already FAILED. The NOTE annotations below pin the three rows FAILED in both
//! revisions.
//!
//! The run twin, which shows the elided check changing the program's output, is
//! `raw_const_escape_havoc_run.rs`.

use std::sync::atomic::{AtomicU8, AtomicUsize, Ordering};

#[cfg(raw_const)]
macro_rules! raw {
    ($x:ident) => {
        &raw const $x
    };
}
#[cfg(raw_mut)]
macro_rules! raw {
    ($x:ident) => {
        &raw mut $x
    };
}

pub fn atomic_store(k: u8) -> u8 {
    //~^ ERROR safety verification incomplete
    //~| NOTE [overflow:add] FAILED
    let mut x: u8 = 5;
    let p = raw!(x);
    let a = unsafe { AtomicU8::from_ptr(p as *mut u8) };
    a.store(k, Ordering::Relaxed);
    x + 1
}

pub fn cast_store(k: u8) -> u8 {
    //~^ ERROR safety verification incomplete
    //~| NOTE [overflow:add] FAILED
    let mut x: u8 = 5;
    let p = raw!(x);
    unsafe {
        *(p as *mut u8) = k;
    }
    x + 1
}

pub fn index_store(k: usize) -> u8 {
    //~^ ERROR safety verification incomplete
    //~| NOTE [bounds] FAILED
    let a: [u8; 4] = [1, 2, 3, 4];
    let mut i: usize = 1;
    let p = raw!(i);
    let at = unsafe { AtomicUsize::from_ptr(p as *mut usize) };
    at.store(k, Ordering::Relaxed);
    a[i]
}
