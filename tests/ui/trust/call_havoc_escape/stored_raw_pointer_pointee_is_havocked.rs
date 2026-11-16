//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Cpanic=abort --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! CALL-HAVOC-ESCAPE-2, review of `d1697fccf6` (finding 1): a RAW pointer stored in a
//! field (`p.q`) carries whatever permission its bits have, whatever its pointee type.
//! `s = &*p.q` is a retagged borrow, but its facts and a raw re-read of `*p.q` both fold
//! to `p*.0*`; `drive` keeps a copy of the same raw pointer in a `static mut`, so
//! `poke()`'s write through it is defined (it invalidates only `s`'s own tag) and the
//! re-read `*p.q` sees 9: `a[9]` panics. The index row must NOT be proved.
//!
//! MEASURED (2026-10-06): this verdict does NOT depend on the havoc. On the stage 1 of
//! `d1697fccf6` (before the fix) and after it, `f` fails verification with the index's
//! `[assert]` row runtime-checked / UNKNOWN (the raw deref is an unsupported read), not
//! proved. The kill-list rail is `escape_havoc_tests::
//! a_raw_pointer_stored_in_a_field_is_havocked_behind_whatever_its_pointee`.

static mut BUF: u8 = 0;
static mut W: *mut u8 = core::ptr::null_mut();

#[inline(never)]
fn poke() {
    unsafe {
        if !W.is_null() {
            *W = 9;
        }
    }
}

pub struct S {
    q: *const u8,
}

pub fn f(p: &S) -> u8 {
    //~^ ERROR Trust strict verification failed for `stored_raw_pointer_pointee_is_havocked::f`
    unsafe {
        let s: &u8 = &*p.q;
        if *s < 4 {
            poke();
            let a = [0u8; 4];
            return a[*p.q as usize];
        }
    }
    0
}

pub fn drive() -> u8 {
    unsafe {
        let base = &raw mut BUF;
        W = base;
        let p = S { q: base as *const u8 };
        f(&p)
    }
}
