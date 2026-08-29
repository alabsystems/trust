//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-profile=unix_hardened --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Trust (B2 negative half (b)): a preconditioned callee called OUT OF CONTRACT
//! must not hand its `ensures` to the HARDENED twin either.
//!
//! This is `postcondition_composition_preconditioned_needs_discharge.rs` under
//! `-Ztrust-verify-profile=unix_hardened`. A contract postcondition is
//! guaranteed only WHERE THE PRECONDITION HELD: the callee discharges
//! `requires -> ensures`, never `ensures` alone. The call-site lane therefore
//! threads the IMPLICATION, and a caller that cannot discharge the antecedent
//! gets nothing from it.
//!
//! `positive_part` requires `x > 0`. `triple` here has the `if x > 0` arm of
//! `hardened_composition_at_call_site.rs` REMOVED, so the antecedent is not
//! discharged, `result > 0` is unavailable, and `y * 3` underflows at large
//! negative `y`. It has a runtime witness — `triple(i32::MIN)` underflows —
//! which is what makes this the load-bearing negative: if it ever passes, the
//! hardened lane has been taught to assume a clause nobody proved AT THIS CALL
//! SITE, and a real panic has been proved away.
//!
//! `triple` must fail its precondition row AND its `Overflow(Mul)` rows.

pub fn positive_part(x: i32) -> i32
    requires x > 0
    ensures result > 0
{
    x
}

pub fn triple(x: i32) -> i32 {
//~^ ERROR Trust
    let y = positive_part(x);
    if y < 100 { y * 3 } else { 0 }
}
