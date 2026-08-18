//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! `*const [T; N] -> *const T` re-points at an element. It creates no vtable, so
//! it must not poison the case split.
//!
//! ## WHY THIS IS A FAILING TEST AND NOT A `check-pass`
//!
//! An element-projection cast only appears in USER code via a raw pointer, and a
//! raw pointer cast raises `hardened_unsafe_operation`, which this file cannot and
//! should not discharge. So one obligation survives no matter what, and the
//! assertion has to be the COUNT:
//!
//! ```text
//! before the element-projection arm   2 obligation(s)   <- unsafe op + POISONED dyn site
//! after it                            1 obligation(s)   <- unsafe op only
//! ```
//!
//! The `1 obligation(s)` in the annotations below is therefore the whole test. It
//! was measured failing at `2 obligation(s)` before the arm existed. If it ever
//! reads 2 again, the poison is back; if it reads 0, something has started
//! discharging an unsafe operation and that is a bigger problem than this file.
//!
//! ## THE DOUBLE CAST IS THE ASSERTION — DELETING `p` GUTS THE TEST
//!
//! Before the arm, ANY cast whose target type merely NESTED a trait object refused
//! the trait: `*const &dyn Emit` nests one, so `Emit` was poisoned bundle-wide and
//! `d.emit()` — an unrelated site with a complete enumeration — lost its discharge.
//! That was the same error made with array-to-slice unsizing, one arm over: keying
//! on "the target type CONTAINS a `dyn`" when the question is "does this operation
//! CREATE one".
//!
//! ## WHAT MUST NOT HAPPEN TO THIS ARM
//!
//! The narrow shape is the point: array-or-slice pointee, element type IDENTICAL.
//! NOT "the source already mentions this principal somewhere" — that admits
//! `*const (&dyn Emit, usize) -> *const &dyn Emit`, which can forge a vtable from
//! the integer's bytes. `dyn_dispatch_reliance_cast_forged_vtable_stays_closed.rs`
//! is that counterexample and must keep its poison. The two files are a pair: one
//! says what is admitted, the other says what admitting it must not drag in.
#![no_std]
#![allow(dead_code)]

pub trait Emit {
    fn emit(&self) -> u32;
}

pub struct A;

impl Emit for A {
    // Provably panic-free: a constant, no panic-capable construct.
    fn emit(&self) -> u32 {
        1
    }
}

pub fn total() -> u32 {
    //~^ ERROR 1 obligation(s) were not proved
    //~| ERROR 1 obligation(s) were not fully verified
    let a = A;
    // The one vtable minted in this bundle. Enumeration: `{A}`.
    let d: &dyn Emit = &a;
    let arr: [&dyn Emit; 2] = [d, d];
    // Element projection. Re-types a pointer; mints nothing. The
    // `hardened_unsafe_operation` obligation it raises is the one that survives.
    let p = &arr as *const [&dyn Emit; 2] as *const &dyn Emit;
    let _ = p as usize;
    // Must DISCHARGE against `<A as Emit>::emit`, leaving only the unsafe-op row.
    d.emit()
}
