//@ needs-trust-verify
//@ revisions: on off
//@[on] compile-flags: -Ztrust-verify=on
//@[off] compile-flags: -Ztrust-verify=off
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: ERROR
//! E9-ODT-FACE-SELF-CALL-1, MUTANT of `e9_field_projection_discharge`'s
//! `degree_bound`: the body returns the OTHER field. The rebuilt self-call
//! `trust_import_degree_bound (TrustOdt.k….mk d k)` reduces to `k`, so the goal
//! is `∀ d k, k <= d`, which `degree_le_self` does not prove, and the citation
//! must stay a hard error.
//!
//! The pin is the long head on purpose: it says the goal WAS built through the
//! face constructor and then refused by the kernel audit. The pre-fix refusal,
//! "the postcondition goal could not be built (admitted `…degree_bound` has
//! arity 1 but is applied to 2 argument(s))", does not match it.
//!
//! `dont-require-annotations: ERROR` tolerates only the secondary
//! strict-verification errors of the `on` revision; the primary refusal is
//! pinned by its explicit ERROR annotation in both revisions.

clean {
    theorem degree_le_self : forall (d : UInt64) (k : UInt64),
        Nat.le (UInt64.toNat d) (UInt64.toNat d) :=
        fun d k => @Nat.le.refl (UInt64.toNat d)
}

pub struct Cst {
    pub degree: u64,
    pub coeff: u64,
}

pub fn degree_bound(c: Cst) -> u64
    ensures result <= c.degree by degree_le_self
    //~^ ERROR citation `degree_le_self` failed the strict Clean statement/certification audit against this postcondition with `result` bound to the imported definition of `degree_bound`
{
    c.coeff
}

fn main() {}
