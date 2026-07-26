//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//! Falsification pair of `e2_by_value_prime_discharge`: a prime on a `&mut`
//! DEREF post-state (`*p'`) is genuine two-state — its value can differ from
//! entry — so it is NOT the by-value slice and stays fail-closed until the deep
//! two-state lane (entry snapshot + prophecy) lands.

clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => Nat.le.refl (UInt64.toNat x)
}

pub fn bump(p: &mut u64)
    //~^ ERROR Trust Level 0 safety verification incomplete for `e2_mut_prime_undischarged::bump`
    //~| ERROR Trust strict verification failed for `e2_mut_prime_undischarged::bump`
    ensures *p' >= *p by u64_ge_refl
    //~^ ERROR citation `u64_ge_refl`
{ *p += 1; }

fn main() {}
