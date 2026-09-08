//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-UPK): the upvar read decides by CAPTURE KIND, not by a type
//! equality that `Ty::Ptr` makes unanswerable.
//!
//! `by_ref_pointer_capture` is the WITNESS of a live wrong-value bug this wave
//! fixes. Before it, BOTH bodies reported `clean=true` and the closure returned
//! the ENV FIELD — the address of the caller's own stack slot, a `&&i32` — as
//! the `&i32` result, with the `Load` through it MISSING; the caller then did
//! `load i32` on a slot holding an 8-byte pointer, so `f(&5)` yielded the low
//! half of a stack address instead of 5.
//!
//! `by_value_pointer_capture` is the minimal pair that makes the root cause
//! unmistakable: it emits a BYTE-IDENTICAL closure body and was always CORRECT,
//! because a by-VALUE capture really does carry the value in the field. `map_ty`
//! erases indirection, so both spell `Ty::Ptr` and no type test can separate
//! them — only `tcx.closure_captures`' `UpvarCapture` can.
//!
//! `run-pass` is the point: these values are checked against real execution, so
//! a regression to the identity branch fails here rather than merely changing a
//! count.

/// The witness: a by-REF capture of a `&i32` local. The env field is a `&&i32`
/// and the read MUST `Load` through it.
pub fn by_ref_pointer_capture(x: &i32) -> i32 {
    let r: &i32 = x;
    let c = || r;
    let q: &i32 = c();
    *q
}

/// The minimal pair: a by-VALUE capture of the same type. The field IS the
/// value; the identity read is correct here and must stay.
pub fn by_value_pointer_capture(x: &i32) -> i32 {
    let r: &i32 = x;
    let c = move || r;
    let q: &i32 = c();
    *q
}

/// A by-ref capture of a plain scalar — the ordinary case the `Load` arm always
/// handled, kept so the wave cannot silently narrow it.
pub fn by_ref_scalar_capture(n: i32) -> i32 {
    let c = || n;
    c()
}

/// A by-value capture of a plain scalar.
pub fn by_value_scalar_capture(n: i32) -> i32 {
    let c = move || n;
    c()
}

fn main() {
    let five = 5;
    assert_eq!(by_ref_pointer_capture(&five), 5);
    assert_eq!(by_value_pointer_capture(&five), 5);
    assert_eq!(by_ref_scalar_capture(7), 7);
    assert_eq!(by_value_scalar_capture(9), 9);
}
