//@ revisions: default certify memsafe advisory
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[memsafe] compile-flags: -Ztrust-policy=memory-safe
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[default] check-fail
//@[certify] check-fail
//@[memsafe] check-fail
//@[advisory] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//! CITE-ENSURES-SUBSTRING-1: an unsupported-`requires` marker is never an
//! ensures-clause stand-in, whatever the function's def path is called.
//!
//! Each `f` below has a `requires` the native lane cannot lower (a quantifier),
//! so it leaves a fail-closed `trust.contract::unsupported` marker whose
//! contract id is `trust-contract:<def path>:requires:0`, and a cited `ensures`
//! the kernel discharges. `is_ensures_clause_obligation` also accepted any
//! marker whose detail CONTAINED `:ensures:`, so when the def path had an
//! `ensures` segment (`mod ensures`, a fn named `ensures`) the `requires`
//! marker was taken as the ensures clause: the E9 lane stamped the kernel proof
//! of the ensures goal onto it, the wire relabelled it a Certified
//! postcondition, and the strict, certify and memory-safe builds of
//! `ensures::f` and `by_fn_name::ensures` were green ("3 proved, 0 failed,
//! 0 unknown") while the byte-identical `other::f` failed on its unknown
//! `requires` row (advisory builds all three, and warned only for `other::f`).
//! The clause kind is now read only from the exact final `contract_id`, so all
//! three functions are reported the same way under every policy.

clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => @Nat.le.refl (UInt64.toNat x)
}

pub mod ensures {
    pub fn f(x: u64) -> u64
    //~^ WARN `#[trust::requires]` on `f` is not assumed for body verification
    //[default,certify]~| ERROR Trust Level 0 safety verification incomplete for `e9_unsupported_requires_marker_not_retired_in_ensures_module::ensures::f`
    //[default,certify]~| ERROR Trust strict verification failed for `e9_unsupported_requires_marker_not_retired_in_ensures_module::ensures::f`
    //[memsafe,advisory]~| WARN Trust Level 0 safety verification incomplete for `e9_unsupported_requires_marker_not_retired_in_ensures_module::ensures::f`
    //[memsafe]~| ERROR Trust memory-safe verification failed for `e9_unsupported_requires_marker_not_retired_in_ensures_module::ensures::f`
        requires forall i: u64, i < x ==> i < 100
        ensures result >= x by u64_ge_refl
    {
        x
    }
}

// CONTROL: identical text in a module whose name has no `ensures` segment.
// This one already failed closed before the fix.
pub mod other {
    pub fn f(x: u64) -> u64
    //~^ WARN `#[trust::requires]` on `f` is not assumed for body verification
    //[default,certify]~| ERROR Trust Level 0 safety verification incomplete for `e9_unsupported_requires_marker_not_retired_in_ensures_module::other::f`
    //[default,certify]~| ERROR Trust strict verification failed for `e9_unsupported_requires_marker_not_retired_in_ensures_module::other::f`
    //[memsafe,advisory]~| WARN Trust Level 0 safety verification incomplete for `e9_unsupported_requires_marker_not_retired_in_ensures_module::other::f`
    //[memsafe]~| ERROR Trust memory-safe verification failed for `e9_unsupported_requires_marker_not_retired_in_ensures_module::other::f`
        requires forall i: u64, i < x ==> i < 100
        ensures result >= x by u64_ge_refl
    {
        x
    }
}

// The same trigger through the FUNCTION name: the contract id is
// `…::by_fn_name::ensures:requires:0`.
pub mod by_fn_name {
    pub fn ensures(x: u64) -> u64
    //~^ WARN `#[trust::requires]` on `ensures` is not assumed for body verification
    //[default,certify]~| ERROR Trust Level 0 safety verification incomplete for `e9_unsupported_requires_marker_not_retired_in_ensures_module::by_fn_name::ensures`
    //[default,certify]~| ERROR Trust strict verification failed for `e9_unsupported_requires_marker_not_retired_in_ensures_module::by_fn_name::ensures`
    //[memsafe,advisory]~| WARN Trust Level 0 safety verification incomplete for `e9_unsupported_requires_marker_not_retired_in_ensures_module::by_fn_name::ensures`
    //[memsafe]~| ERROR Trust memory-safe verification failed for `e9_unsupported_requires_marker_not_retired_in_ensures_module::by_fn_name::ensures`
        requires forall i: u64, i < x ==> i < 100
        ensures result >= x by u64_ge_refl
    {
        x
    }
}
