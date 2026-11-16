//~ NOTE "proved":0,"failed":0,"unknown":0,"timed_out":0,"skipped":0,"runtime_checked":1,"cached":0,"total":1}
//~| NOTE "proved":0,"failed":1,"unknown":0,"timed_out":0,"skipped":0,"runtime_checked":1,"cached":0,"total":2}
//~| NOTE "proved":0,"failed":1,"unknown":0,"timed_out":0,"skipped":0,"runtime_checked":1,"cached":0,"total":2}
//@ revisions: advisory strict certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//@[strict] check-fail
//@[certify] check-fail
//! ADVISORY-REQUIRES-INSTANCE (KNOWN_HAZARDS, CLOSED 2026-10-04; DECISION_QUEUE OD-1,
//! "L0 refutation rows"): a trait impl method's `requires` is charged to no call —
//! every route names the TRAIT's item — yet the native callee closure bundled the
//! impl as a member with that clause ASSUMED at its entry. Under
//! `-Ztrust-policy=advisory` (targo's `--allow-l0-gaps`), where the impl itself is
//! not refused, `Bad.m(0)` and `f::<Bad>` reaching `Bad::m` published the caller's
//! panic-freedom row PROVED (the `x = 0` path was infeasible under the assumed
//! clause), and a caller of that caller was PROVED with no failed row anywhere.
//! Strict and certify published the same rows beside the impl's refusal. Measured
//! on stage 1 of `1177c327fa`. The impl is now never bundled as a member; each call
//! keeps the absent-callee may-panic row, so no caller's panic-freedom is proved
//! through it in any lane. The line-1 pins are the per-function JSON summaries:
//! `direct` and `caller_of_caller` (`runtime_checked` 1 of 1; before: `proved` 1 of
//! 1) and `through_generic` (its `runtime_checked` row beside the `failed`
//! discharge row; before: `proved` 1, `failed` 1). No other body here publishes
//! either shape, before or after.
//!
//! Re-pinned 2026-10-15 (the merge of 2026-10-14): `direct` now publishes the
//! `through_generic` shape (`failed` 1, `runtime_checked` 1 of 2). Its call to `Bad.m(0)`
//! is CHARGED the impl's `requires` at the call site (the requires-charging fix of
//! 94890dd44b6), and that row is refuted (`x = 0`), beside the absent-callee row; so line 1
//! now pins `caller_of_caller` (1 of 1) and lines 2 and 3 pin `direct` and
//! `through_generic`. Still nothing is proved through the impl.

pub trait Td {
    fn m(&self, x: u32) -> u32;
}

pub struct Bad;

impl Td for Bad {
    fn m(&self, x: u32) -> u32
    //[strict,certify]~^ ERROR a `requires` on a trait impl method is charged to no caller
    requires x != 0
    {
        100 / x
    }
}

/// A statically resolved trait call violating the impl's clause.
pub fn direct() -> u32 {
    //[strict,certify]~^ ERROR Trust strict verification failed for `trait_impl_requires_reached_through_instance::direct`
    //[certify]~| ERROR Trust Level 0 safety verification incomplete for `trait_impl_requires_reached_through_instance::direct`
    Bad.m(0)
}

/// An open dispatch (an OD-1 instance-hypothesis site).
pub fn f<T: Td>(t: &T) -> u32 {
    //[certify]~^ ERROR Trust certify verification failed for `trait_impl_requires_reached_through_instance::f`
    t.m(0)
}

/// The instance `f::<Bad>`: its discharge row fails, and its panic-freedom row must
/// not be proved either.
pub fn through_generic() -> u32 {
    //[strict,certify]~^ ERROR Trust instance discharge not established for `trait_impl_requires_reached_through_instance::through_generic`
    //[strict,certify]~| ERROR Trust strict verification failed for `trait_impl_requires_reached_through_instance::through_generic`
    //[certify]~| ERROR Trust Level 0 safety verification incomplete for `trait_impl_requires_reached_through_instance::through_generic`
    f(&Bad)
}

/// A caller of the caller: before the fix its only row was a PROVED panic-freedom.
pub fn caller_of_caller() -> u32 {
    //[strict,certify]~^ ERROR Trust strict verification failed for `trait_impl_requires_reached_through_instance::caller_of_caller`
    //[certify]~| ERROR Trust Level 0 safety verification incomplete for `trait_impl_requires_reached_through_instance::caller_of_caller`
    through_generic()
}
