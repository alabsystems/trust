//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Trust (postcondition composition — the LAUNDERING channel, ATTRIBUTE
//! spelling, kept shut).
//!
//! A caller may assume a callee's `ensures` ONLY IF the callee's own
//! postcondition obligation was DISCHARGED. Assuming a declared-but-unproved
//! `ensures` is not a completeness nicety, it is a false-PROVE generator: the
//! callee writes any proposition it likes and every caller inherits it. Making
//! the `#[core::contracts::ensures]` spelling compose must not open a second
//! door onto that room, so both lanes are pinned here.
//!
//! Each `ensures` below is FALSE (`bad(0) == 0`, `bad_pre(5) == 5`, neither is
//! `>= 1000`), so each callee's own postcondition rows come back unproved and
//! neither clause may travel.
//!
//!  * `bad`/`caller` — precondition-FREE, the lane that already worked.
//!  * `bad_pre`/`caller_pre` — PRECONDITIONED, and the load-bearing half: this
//!    is the lane the attribute fix newly opens. Its caller DISCHARGES the
//!    antecedent (`if x > 0`), so the guard is satisfied and the only thing left
//!    standing between this file and a false prove is the callee's own verdict.
//!
//! Both callers are shaped `if y < 100 { y * 3 }` rather than a plain `y * 3`
//! for the same reason: had either inherited `y >= 1000`, the guard would be
//! contradictory and the `Mul` would prove VACUOUSLY — a green row about an
//! unreachable path, with no symptom anywhere. The caller errors, not the callee
//! errors, are the assertion that the fact never travelled.
#![feature(contracts)]
#![allow(incomplete_features)]

#[core::contracts::ensures(move |ret: &i32| *ret >= 1000)]
pub fn bad(x: i32) -> i32 {
//~^ ERROR Trust strict verification failed for `postcondition_composition_attribute_needs_proved_ensures::bad`
    x
}

pub fn caller(x: i32) -> i32 {
//~^ ERROR Trust Level 0 safety verification incomplete for `postcondition_composition_attribute_needs_proved_ensures::caller`
//~| ERROR Trust strict verification failed for `postcondition_composition_attribute_needs_proved_ensures::caller`
    let y = bad(x);
    if y < 100 { y * 3 } else { 0 }
}

#[core::contracts::ensures(move |ret: &i32| *ret >= 1000)]
pub fn bad_pre(x: i32) -> i32
//~^ ERROR Trust strict verification failed for `postcondition_composition_attribute_needs_proved_ensures::bad_pre`
    requires x > 0
{
    x
}

pub fn caller_pre(x: i32) -> i32 {
//~^ ERROR Trust Level 0 safety verification incomplete for `postcondition_composition_attribute_needs_proved_ensures::caller_pre`
//~| ERROR Trust strict verification failed for `postcondition_composition_attribute_needs_proved_ensures::caller_pre`
    if x > 0 {
        let y = bad_pre(x);
        if y < 100 { y * 3 } else { 0 }
    } else {
        0
    }
}
