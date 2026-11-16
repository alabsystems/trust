//@ revisions: default certify memsafe advisory
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[memsafe] compile-flags: -Ztrust-policy=memory-safe
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//! CITE-PRIME-NONASCII-1: the `p'` -> `p` collapse for an immutable by-value
//! parameter must match `p` only where it is the WHOLE identifier token rustc
//! lexed. `rewrite_by_value_prime` decided the boundary on bytes
//! (`is_ascii_alphanumeric() || b'_'`), so the UTF-8 continuation byte of `é`
//! in `éa'` counted as a boundary: the pass for the immutable `a` rewrote the
//! post-state of `mut éa` to its entry value, turning the false clause
//! `éa' >= éa` into the tautology `éa >= éa`, and `u64_ge_refl` (reflexivity)
//! kernel-certified it. The body sets `éa = 0`, so the clause is false for
//! every `éa > 0`; before the fix both functions below built clean under the
//! default, certify, memory-safe and advisory policies with the postcondition
//! rows reported Certified/KernelRechecked.
//!
//! After the fix, both functions fail closed exactly like the ASCII
//! `e2_mut_by_value_prime_undischarged.rs`: the mutable binding's prime stays
//! in the clause and the citation is refused as outside the statement
//! fragment (a hard error under every policy, advisory included). `step` is
//! the realistic spelling of the same lie (`δx` is the step, `x` the immutable
//! input).

#![allow(mixed_script_confusables)]

clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => Nat.le.refl (UInt64.toNat x)
}

pub fn bad(a: u64, mut éa: u64) -> u64
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `e2_mut_by_value_prime_non_ascii_undischarged::bad`
    //[default,certify]~| ERROR Trust strict verification failed for `e2_mut_by_value_prime_non_ascii_undischarged::bad`
    //[memsafe,advisory]~^^^ WARN Trust Level 0 safety verification incomplete for `e2_mut_by_value_prime_non_ascii_undischarged::bad`
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `e2_mut_by_value_prime_non_ascii_undischarged::bad`
    ensures éa' >= éa by u64_ge_refl
    //~^ ERROR citation `u64_ge_refl` cannot be validated because this clause is outside the exact statement fragment
{
    éa = 0;
    éa + a
}

pub fn step(x: u64, mut δx: u64) -> u64
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `e2_mut_by_value_prime_non_ascii_undischarged::step`
    //[default,certify]~| ERROR Trust strict verification failed for `e2_mut_by_value_prime_non_ascii_undischarged::step`
    //[memsafe,advisory]~^^^ WARN Trust Level 0 safety verification incomplete for `e2_mut_by_value_prime_non_ascii_undischarged::step`
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `e2_mut_by_value_prime_non_ascii_undischarged::step`
    ensures δx' >= δx by u64_ge_refl
    //~^ ERROR citation `u64_ge_refl` cannot be validated because this clause is outside the exact statement fragment
{
    δx = 0;
    x / 2 + δx
}
