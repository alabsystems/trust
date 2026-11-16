//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Cpanic=abort --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! P1 precision (2026-10-06; CALL-HAVOC-ESCAPE-1 rule (b) widened) — the adversarial
//! review's counterexample to keeping facts BEHIND a shared-reference field. `drive`
//! stores raw-pointer bits into `p.b` with `ptr::write` (a field is never retagged, so
//! that value never becomes a `SharedReadOnly`/`Frozen` reference), and `poke()` writes
//! the same buffer through a `static mut` pointer: defined under Stacked and Tree
//! Borrows (as reported by the review; not re-run under Miri here). After the call
//! `p.b[0]` reads 9 and `a[9]` panics, so the index row of `a[..]` in `f` must NOT be
//! proved. The widening keeps only `*p`'s own bytes (`p.i`, `p.b`'s address and length)
//! and havocs `p*.0*`.
//!
//! MEASURED (2026-10-06): this verdict does NOT yet depend on the havoc. On the stage 1
//! of `3f7e24ef0b` (before CALL-HAVOC-ESCAPE-2) and after it, the index row is
//! `[bounds] FAILED`, and it is also FAILED with no call at all: every `p.b[0]` loads
//! `p.b` into a fresh deref temp, and no fact ties one temp's pointee to the next. The
//! kill-list rails in `crates/trust-vcgen/src/generate/escape_havoc_tests.rs` are what
//! pin the havoc; this file pins the program's verdict for when the reads do connect.

use core::ptr;

static mut BUF: [u8; 4] = [0; 4];
static mut W: *mut u8 = ptr::null_mut();

#[inline(never)]
fn poke() {
    unsafe {
        if !W.is_null() {
            *W = 9;
        }
    }
}

pub struct P<'a> {
    b: &'a [u8],
    i: usize,
}

pub fn f(p: &mut P<'_>) -> u8 {
    //~^ NOTE [bounds] FAILED
    if p.b[0] < 4 {
        poke();
        let a = [0u8; 4];
        a[p.b[0] as usize]
    } else {
        0
    }
}

pub fn drive() -> u8 {
    unsafe {
        let base = &raw mut BUF as *mut u8;
        W = base;
        let mut p = P { b: &[], i: 0 };
        ptr::write(&raw mut p.b as *mut *const [u8], ptr::slice_from_raw_parts(base, 4));
        f(&mut p)
    }
}
