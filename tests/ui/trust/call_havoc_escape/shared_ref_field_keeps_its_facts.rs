//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Cpanic=abort --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ forbid-output: FAILED
//! P1 precision (2026-10-06; CALL-HAVOC-ESCAPE-1 rule (b) widened): a `&mut self`
//! PARAMETER whose pointee holds a SHARED reference to pointer-free `Freeze` data (TINV
//! P1's `Parser { b: &[u8], i: usize }`) keeps its facts across a call whose arguments
//! grant no write, here the nullary `poke()`, which writes a static. `*self`'s bytes
//! (including `b`'s address and length) are under the parameter's protector for the
//! whole call, so the guard on `self.i` and `self.b.len()` still holds after `poke()`:
//! the index's bounds row and the subtraction's overflow row must be PROVED (no row may
//! FAIL). Before the widening the coarse rule havocked `*self` at `poke()` and both rows
//! were refuted (`[slice] FAILED` on a fresh `self*.0__slice_len#s1_t`); the index also
//! needs the dest-only arm's read-only `&raw const` admission (its bounds check takes
//! `&raw const (*self.b)`).
//!
//! Default policy, not certify: the native trust-ir lane has no summary for a call that
//! touches a static (`UnsupportedDirectCallSummary`), so each function's retained
//! panic-freedom `[assert]` row is runtime-checked whatever the havoc decides.

use core::sync::atomic::{AtomicU32, Ordering};

static TICKS: AtomicU32 = AtomicU32::new(0);

#[inline(never)]
fn poke() {
    TICKS.store(7, Ordering::Relaxed);
}

pub struct Parser<'a> {
    b: &'a [u8],
    i: usize,
}

impl<'a> Parser<'a> {
    // `self.b.len()` read before the call (the guard) and after it (the bounds check).
    pub fn at(&mut self) -> u8 {
        if self.i < self.b.len() {
            poke();
            return self.b[self.i];
        }
        0
    }

    // `self.b.len()` read again after the call as a value: `n - self.i` cannot underflow.
    pub fn remaining(&mut self) -> usize {
        if self.i <= self.b.len() {
            poke();
            let n = self.b.len();
            return n - self.i;
        }
        0
    }
}
