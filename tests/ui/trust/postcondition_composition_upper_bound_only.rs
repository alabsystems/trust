//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Trust (postcondition composition — the VACUITY guard on the positive test).
//!
//! Byte-for-byte the bodies of `postcondition_composition_at_call_site.rs`,
//! with the callee's `ensures` weakened to its UPPER half. `clamp_low` still
//! proves its own (weaker) postcondition, and the caller still assumes it — but
//! `result <= 1000000` says nothing about how negative `y` can be, so `y * 3`
//! is still a real underflow and must still FAIL.
//!
//! Without this file, the positive test cannot distinguish "the caller USED the
//! postcondition" from "the caller-side lane stopped emitting the obligation".
//! Composition that proves regardless of what the clause SAYS is not
//! composition, it is suppression.

pub fn clamp_low(x: i32) -> i32
    ensures result <= 1000000
{
    if x < 0 {
        0
    } else if x > 1000000 {
        1000000
    } else {
        x
    }
}

pub fn triple(x: i32) -> i32 {
//~^ ERROR Trust Level 0 safety verification incomplete for `postcondition_composition_upper_bound_only::triple`
//~| ERROR Trust strict verification failed for `postcondition_composition_upper_bound_only::triple`
    let y = clamp_low(x);
    if y < 100 { y * 3 } else { 0 }
}
