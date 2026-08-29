//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Trust (postcondition composition — the LAUNDERING channel, kept shut).
//!
//! A caller may assume a callee's `ensures` ONLY IF the callee's own
//! postcondition obligation was discharged. Assuming a DECLARED-but-unproved
//! `ensures` is not a completeness nicety, it is a false-PROVE generator: the
//! callee writes any proposition it likes and every caller inherits it.
//!
//! `bad`'s `ensures` is false — `bad(0) == 0`, not `>= 1000` — so its own
//! postcondition rows come back unproved. This file pins BOTH halves of the
//! consequence:
//!
//!  * `bad` itself must fail (the first expected error), and
//!  * `caller` must STILL fail its `Mul` obligation (the second).
//!
//! The second is the load-bearing one, and it is why the body is shaped this
//! way rather than as a plain `y * 3`. If `caller` had inherited `y >= 1000`,
//! the guard `y < 100` would be contradictory and the `y * 3` obligation would
//! prove VACUOUSLY — a green row about an unreachable path, with no symptom
//! anywhere. A `check-fail` on `bad` alone would not have seen that; the
//! `caller` error is the assertion that the fact never travelled.

pub fn bad(x: i32) -> i32
//~^ ERROR Trust strict verification failed for `postcondition_composition_needs_proved_ensures::bad`
    ensures result >= 1000
{
    x
}

pub fn caller(x: i32) -> i32 {
//~^ ERROR Trust Level 0 safety verification incomplete for `postcondition_composition_needs_proved_ensures::caller`
//~| ERROR Trust strict verification failed for `postcondition_composition_needs_proved_ensures::caller`
    let y = bad(x);
    if y < 100 { y * 3 } else { 0 }
}
