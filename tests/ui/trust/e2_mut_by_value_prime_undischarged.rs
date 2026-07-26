//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//! A mutable by-value binding has a genuine post-state. Rewriting `x'` to the
//! entry value `x` would turn this false clause into the tautology `x >= x` and
//! could let an unrelated reflexivity theorem fabricate proof credit. The
//! two-state binding therefore remains fail-closed until exact post-state
//! transport is authenticated end to end.

clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => Nat.le.refl (UInt64.toNat x)
}

pub fn bad(mut x: u64) -> u64
    //~^ ERROR Trust Level 0 safety verification incomplete for `e2_mut_by_value_prime_undischarged::bad`
    //~| ERROR Trust strict verification failed for `e2_mut_by_value_prime_undischarged::bad`
    ensures x' >= x by u64_ge_refl
    //~^ ERROR citation `u64_ge_refl` cannot be validated because this clause is outside the exact statement fragment
{
    x = 0;
    x
}

fn main() {}
