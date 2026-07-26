//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//! Falsification pair (negative): the SAME arbitrary body as the positive
//! sibling, but with a clause whose truth DEPENDS on `result`'s denotation,
//! fails closed. The multi-statement xor body is no recognized kernel-import
//! shape, so `result` has no kernel defining equation and cannot be grounded;
//! `result >= x` is therefore NOT provable (it is not universally valid — only
//! the body's `result == x` makes it hold), and the cited reflexivity theorem
//! `u64_ge_refl : forall v, v <= v` does not statement-match the two-variable
//! clause. The citation must fail the strict Clean statement/certification
//! audit rather than fabricate a discharge.
//!
//! A reflexive `result >= result` is not a probe for this case: it is a valid
//! tautology the native BV lane can prove without denoting `result`.
clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => Nat.le.refl (UInt64.toNat x)
}
pub fn busy(x: u64) -> u64
    //~^ ERROR Trust strict verification failed for
    ensures result >= x by u64_ge_refl
    //~^ ERROR citation `u64_ge_refl` failed the strict Clean statement/certification audit
{
    let a = x ^ 3;
    let b = a ^ 3;
    b
}

fn main() {}
