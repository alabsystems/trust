//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=strict --crate-type lib
//@ check-pass
//! Trust (postcondition composition): a callee's `ensures` must be ASSUMED at
//! the caller, not merely CHECKED on the callee.
//!
//! Before this lane, `clamp_low` verified and `triple` failed with
//! `arithmetic overflow (Mul)`: the caller learned nothing about `y` from the
//! call, and the `y < 100` guard leaves `y` unbounded BELOW, so `y * 3`
//! underflows at large negative `y`. The obligation is genuinely unprovable
//! without the postcondition — see
//! `postcondition_composition_upper_bound_only.rs`, which keeps this exact
//! body and weakens the `ensures` to the upper half, and still fails.
//!
//! The caller-side assumption is minted only when THIS compilation has already
//! discharged the callee's own postcondition obligation
//! (`callee_postconditions_are_reusable` in `trust_verify.rs`); the companion
//! `postcondition_composition_needs_proved_ensures.rs` is the negative half.

pub fn clamp_low(x: i32) -> i32
    ensures result >= 0 && result <= 1000000
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
    let y = clamp_low(x);
    if y < 100 { y * 3 } else { 0 }
}
