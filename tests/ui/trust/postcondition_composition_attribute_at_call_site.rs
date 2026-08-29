//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=strict --crate-type lib
//@ check-pass
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Trust (postcondition composition — the ATTRIBUTE spelling composes too).
//!
//! Postcondition composition landed for the GRAMMAR spelling only. This file is
//! the same program as
//! `postcondition_composition_preconditioned_at_call_site.rs` with one token
//! changed — `ensures result > 0` becomes
//! `#[core::contracts::ensures(move |ret: &i32| *ret > 0)]` — and before the fix
//! it FAILED `arithmetic overflow (Mul)` while its grammar twin passed.
//!
//! That mattered out of proportion to how it looked: the grammar spelling is
//! SYNTAX, so it cannot be `cfg_attr`-stripped for a stable stage0, and every
//! real in-tree crate therefore writes contracts as attributes. The whole
//! composition lane was reachable only from a spelling those crates cannot use.
//!
//! The cause was a NAME, not the contract. `#[ensures]` lowering mints a `__ret`
//! binding whose `var_debug_info` row copy-propagation parks on the parameter
//! local; `mir_param_names` took the LAST row per local, so the callee's formal
//! was called `__ret` instead of `x`. `param_names` is the namespace the
//! contract formulas are bound in, so the guard `x > 0` had no bindable
//! variable, `summary_postconditions_ride_with_their_guard` refused, and the
//! proved `ensures` was dropped at every call site — silently. See
//! `mir_param_names` in `trust_verify.rs`.
//!
//! The precondition-free case never showed it: a postcondition's only free
//! variable is the result symbol `_0`, which needs no parameter name. That is
//! why the symptom read as "attribute `ensures` does not compose" rather than as
//! a naming bug, and why the negative companions below are all PRECONDITIONED.
//!
//! Companions, and all three must keep FAILING:
//!  * `postcondition_composition_attribute_needs_discharge.rs` — the `if x > 0`
//!    arm removed, so the antecedent cannot be discharged. It has a runtime
//!    witness (`triple(i32::MIN)` underflows).
//!  * `postcondition_composition_attribute_upper_bound_only.rs` — same guard,
//!    clause weakened so it no longer implies what the caller needs.
//!  * `postcondition_composition_attribute_needs_proved_ensures.rs` — a FALSE
//!    attribute `ensures`, which must not travel at all.
#![feature(contracts)]
#![allow(incomplete_features)]

#[core::contracts::ensures(move |ret: &i32| *ret > 0)]
pub fn positive_part(x: i32) -> i32
    requires x > 0
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
