//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A cast that could FORGE a vtable must keep the trait refused, even when the
//! principal already appears somewhere in the source type.
//!
//! ## THIS FILE EXISTS TO KILL ONE SPECIFIC "SIMPLIFICATION"
//!
//! `is_array_element_projection` admits `*const [T; N] -> *const T` because that
//! re-points at an element of a sequence whose members were each minted by a
//! witnessed coercion. The tempting generalization is to replace that shape test
//! with a SET test — "poison only the principals NEW in the target relative to the
//! source" — which accepts every case measured so far and is shorter to write.
//!
//! It is unsound, and this is the counterexample:
//!
//! ```text
//! *const (&dyn Emit, usize)  ->  *const &dyn Emit
//! ```
//!
//! Source principals `{Emit}`. Target principals `{Emit}`. Set difference EMPTY, so
//! a set rule skips the poison and lets the case split stand. But the cast can be
//! aimed at the `usize` and reinterpret `0xdead` as a fat pointer — a forged vtable
//! for a principal admitted only because it happened to appear elsewhere in the
//! source layout. Dereferencing that is unsafe, and Trust verifies unsafe bodies,
//! so this rule is the thing standing between a forged vtable and a discharge.
//!
//! A tuple is not an array, so the element-projection arm never fires here and the
//! poison stands. That is the assertion. If this file ever starts PASSING, the arm
//! has been widened into a predicate about sets rather than a claim about the
//! operation, and forged vtables are being admitted.
//!
//! Measured before the element-projection arm existed, and required to be
//! unchanged after it: `C-FLOW declined: trait Emit poisoned` — the
//! `hardened_unsafe_operation` the raw cast raises, PLUS the `dyn` site that
//! the poison keeps. Since cd4faf5cfa the `p as usize` expose adds a third
//! fail-closed row (trust-mir-extract lowers the expose result to
//! `ConstValue::OpaqueScalar`; trust-vcgen's 4ca0cb0eac operand collector
//! refuses an identity-less opaque scalar as proof input — an
//! UnsupportedMir -> Unknown row), so the pinned total is `3 obligation(s)`.
//! Measured 2026-08-30 (stage1, main tip): the report shows
//! `[hardened_unsafe_operation] FAILED`, the `[unknown]` OpaqueScalar row, AND
//! the `[assert] runtime-checked` dyn-site panic-freedom row the poison keeps
//! — the refusal did NOT open. The COUNT is the assertion, and 3 is the number
//! that must not move: if the arm is ever widened into the set rule, this
//! tuple would discharge its dyn row and the count would drop to 2. The
//! verdict must be identical either side of the arm landing — a fixture whose
//! behavior moves when the arm lands would be testing the arm rather than the
//! refusal.
//!
//! The companion positive case is
//! `dyn_dispatch_reliance_cast_array_element_no_poison.rs`: same crate shape with an
//! ARRAY instead of a tuple, which must drop to `2 obligation(s)` (unsafe op +
//! expose row, no dyn row). The pair is the boundary — this file alone would be
//! satisfied by a rule that poisons everything.
#![no_std]
#![allow(dead_code)]

pub trait Emit {
    fn emit(&self) -> u32;
}

pub struct A;

impl Emit for A {
    fn emit(&self) -> u32 {
        1
    }
}

pub fn total() -> u32 {
    //~^ ERROR 3 obligation(s) were not proved
    //~| ERROR 3 obligation(s) were not fully verified
    let a = A;
    let d: &dyn Emit = &a;
    // The principal appears in the source type — but in a TUPLE, alongside an
    // integer whose bytes a re-aimed pointer could serve up as a vtable.
    let pair: (&dyn Emit, usize) = (d, 0xdead);
    let p = &pair as *const (&dyn Emit, usize) as *const &dyn Emit;
    let _ = p as usize;
    d.emit()
}
