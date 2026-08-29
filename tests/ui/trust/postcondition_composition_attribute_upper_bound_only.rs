//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Trust (postcondition composition — the ATTRIBUTE spelling's VACUITY guard).
//!
//! Byte-for-byte the caller of
//! `postcondition_composition_attribute_at_call_site.rs`, including the
//! `if x > 0` arm that DISCHARGES the callee's `requires`. Only the attribute
//! `ensures` changes: it is weakened to a clause that says nothing about how
//! negative the result can be.
//!
//! So the antecedent is discharged, the guarded fact fires, the caller really
//! does learn `y <= 1000000` — and `y * 3` is STILL a real underflow at large
//! negative `y`, so it must still FAIL.
//!
//! Without this file the positive test cannot tell "the caller USED the
//! attribute-spelled postcondition" from "the caller-side lane stopped emitting
//! the obligation". That distinction is the whole content of this fix: the
//! defect it repairs was invisible precisely because a dropped clause and a
//! never-emitted obligation look identical from a summary line.
#![feature(contracts)]
#![allow(incomplete_features)]

#[core::contracts::ensures(move |ret: &i32| *ret <= 1000000)]
pub fn positive_part(x: i32) -> i32
    requires x > 0
{
    if x > 1000000 { 1000000 } else { x }
}

pub fn triple(x: i32) -> i32 {
//~^ ERROR Trust Level 0 safety verification incomplete for `postcondition_composition_attribute_upper_bound_only::triple`
//~| ERROR Trust strict verification failed for `postcondition_composition_attribute_upper_bound_only::triple`
    if x > 0 {
        let y = positive_part(x);
        if y < 100 { y * 3 } else { 0 }
    } else {
        0
    }
}
