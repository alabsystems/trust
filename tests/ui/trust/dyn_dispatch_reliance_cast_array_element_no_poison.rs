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
//! should not discharge. Since cd4faf5cfa the `p as usize` expose below adds a
//! SECOND surviving row: trust-mir-extract now lowers a
//! `PointerExposeProvenance` result to the better-typed
//! `ConstValue::OpaqueScalar`, and trust-vcgen's operand collector (4ca0cb0eac)
//! fail-closes on an identity-less opaque scalar as proof input
//! ("`identity-less opaque unsigned 64-bit scalar cannot be used as proof
//! input`", an UnsupportedMir -> Unknown row). That row is fail-closed
//! tightening, not poison — measured 2026-08-30 (stage1, main tip): the report
//! shows exactly `[hardened_unsafe_operation] FAILED` plus that `[unknown]`
//! OpaqueScalar row, and NO dyn-site panic-freedom row, i.e. `d.emit()` still
//! discharges. So the baseline is two obligations and the assertion is still
//! the COUNT:
//!
//! ```text
//! before the element-projection arm   3 obligation(s)   <- unsafe op + expose row + POISONED dyn site
//! after it                            2 obligation(s)   <- unsafe op + expose row only
//! ```
//!
//! The `2 obligation(s)` in the annotations below is therefore the whole test.
//! If it ever reads 3 again, the poison is back; if it reads 1, either
//! something has started discharging an unsafe operation (a bigger problem
//! than this file) or expose-casts became modeled (§5 allocation-identity,
//! 0e831c4100 onward) and the expose row legitimately retired — check the
//! report before touching the count.
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
    //~^ ERROR 2 obligation(s) were not proved
    //~| ERROR 2 obligation(s) were not fully verified
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
