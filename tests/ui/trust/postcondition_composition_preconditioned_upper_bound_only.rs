//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Trust (postcondition composition, slice 2 — the VACUITY guard).
//!
//! Byte-for-byte the caller of
//! `postcondition_composition_preconditioned_at_call_site.rs`, including the
//! `if x > 0` arm that DISCHARGES the callee's `requires`. Only the `ensures`
//! changes: it is weakened to a clause that says nothing about how negative the
//! result can be.
//!
//! So the antecedent is discharged, the guarded fact fires, the caller really
//! does learn `y <= 1000000` — and `y * 3` is STILL a real underflow at large
//! negative `y`, so it must still FAIL.
//!
//! Without this file the positive test cannot tell "the caller USED the
//! postcondition" from "the caller-side lane stopped emitting the obligation".
//! Composition that proves regardless of what the clause SAYS is not
//! composition, it is suppression — and a guarded lane can suppress in one more
//! way than an unguarded one, because it touches the injection site itself.

pub fn positive_part(x: i32) -> i32
    requires x > 0
    ensures result <= 1000000
{
    if x > 1000000 { 1000000 } else { x }
}

pub fn triple(x: i32) -> i32 {
//~^ ERROR Trust Level 0 safety verification incomplete for `postcondition_composition_preconditioned_upper_bound_only::triple`
//~| ERROR Trust strict verification failed for `postcondition_composition_preconditioned_upper_bound_only::triple`
    if x > 0 {
        let y = positive_part(x);
        if y < 100 { y * 3 } else { 0 }
    } else {
        0
    }
}
