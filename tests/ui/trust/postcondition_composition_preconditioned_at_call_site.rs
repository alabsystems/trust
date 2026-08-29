//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=strict --crate-type lib
//@ check-pass
//! Trust (postcondition composition, slice 2): a callee that ALSO declares a
//! `requires` can have its `ensures` assumed at a call site — but only where
//! the caller discharges that `requires`.
//!
//! Slice 1 refused every preconditioned callee outright, so this program failed
//! `arithmetic overflow (Mul)`: `y < 100` leaves `y` unbounded BELOW and
//! `y * 3` underflows at large negative `y`. The fact that closes it —
//! `result > 0` — had been proved one function away and could not travel
//! because it travelled without its guard.
//!
//! It now travels WITH its guard. The clause reaches the caller as the
//! implication the callee actually proved, `x > 0 -> y > 0`, instantiated at
//! this call site; the `if x > 0` arm discharges the antecedent, so `y > 0`
//! becomes available and `y * 3` proves.
//!
//! Both halves are pinned by companions, and both must keep failing:
//!  * `postcondition_composition_preconditioned_needs_discharge.rs` — same
//!    bodies with the `if x > 0` arm REMOVED, so the antecedent cannot be
//!    discharged. It has a runtime witness (`triple(i32::MIN)` underflows),
//!    which is what makes it the load-bearing half.
//!  * `postcondition_composition_preconditioned_upper_bound_only.rs` — same
//!    guard, `ensures` weakened so it no longer implies what the caller needs.
//!    Without it this file cannot distinguish "the caller USED the clause"
//!    from "the caller-side lane stopped emitting the obligation".

pub fn positive_part(x: i32) -> i32
    requires x > 0
    ensures result > 0
{
    x
}

pub fn triple(x: i32) -> i32 {
    if x > 0 {
        let y = positive_part(x);
        if y < 100 { y * 3 } else { 0 }
    } else {
        0
    }
}
