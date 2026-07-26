//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//! The load-bearing pair of `e9_postcondition_citation_discharge`: the SAME
//! clause on the SAME function, with the `by` citation REMOVED — no kernel
//! discharge, so the unproved postcondition stays a strict-verification build
//! error. Also pins the falsification cases: a `>=` theorem cited on a strict
//! `>` clause does NOT discharge (wrong statement), and an unknown theorem
//! fails closed.

clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => Nat.le.refl (UInt64.toNat x)
}

pub fn no_citation(x: u64) -> u64
    //~^ ERROR Trust strict verification failed for
    ensures x >= x
{ x }

pub fn wrong_statement(x: u64) -> u64
    //~^ ERROR Trust strict verification failed for
    ensures x > x by u64_ge_refl
    //~^ ERROR citation `u64_ge_refl` failed the strict Clean statement/certification audit
{ x }

pub fn unknown_theorem(x: u64) -> u64
    //~^ ERROR Trust strict verification failed for
    ensures x >= x by no_such_theorem
    //~^ ERROR cited theorem `no_such_theorem` is not registered
{ x }

fn main() {}
