//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Cpanic=abort --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! CALL-HAVOC-ESCAPE-2 (2026-10-06): a reference STORED IN MEMORY (a field `p.b`) is
//! never retagged, so it can carry raw-pointer bits with write permission
//! (`ptr::write` of a `*const [u8]`). Facts about the bytes BEHIND it (`p*.0*[k]`) must
//! not survive a call, whatever the root's kind: here `p` is a SHARED reference
//! parameter, which no havoc list ever named.
//!
//! * `via_static`: `poke()` writes the buffer through a `static mut` pointer;
//! * `via_shared_arg`: `peek(&p.b)` receives `&&[u8]` and writes through the inner
//!   reference's raw-pointer bits (no static involved).
//!
//! The drivers show the callers; after the call `p.b[0]` is 9 and `a[9]` panics, so the
//! index row must NOT be proved.
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

#[inline(never)]
fn peek(b: &&[u8]) {
    unsafe { *(*(b as *const &[u8] as *const *mut u8)) = 9 }
}

pub struct P<'a> {
    b: &'a [u8],
    i: usize,
}

pub fn via_static(p: &P<'_>) -> u8 {
    //~^ NOTE [bounds] FAILED
    if p.b[0] < 4 {
        poke();
        let a = [0u8; 4];
        a[p.b[0] as usize]
    } else {
        0
    }
}

pub fn via_shared_arg(p: &P<'_>) -> u8 {
    //~^ NOTE [bounds] FAILED
    if p.b[0] < 4 {
        peek(&p.b);
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
        via_static(&p) + via_shared_arg(&p)
    }
}
