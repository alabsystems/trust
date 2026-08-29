//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//! Companion of `e9_postcondition_citation_discharge`. What it STILL pins, all
//! measured at HEAD (stage2 ec4783d80): a `>=` theorem cited on a strict `>`
//! clause does NOT discharge — the clause stays unproved ("0 proved, 0 failed,
//! 2 unknown") and the citation is a hard statement/certification-audit error —
//! and an unknown theorem fails closed with its own hard error.
//!
//! What it NO LONGER pins is `no_citation`. With the `by` token removed the
//! clause still reports "2 proved, 0 failed, 0 unknown, 0 timed out, 0
//! runtime-checked out of 2 obligation(s)", "of which 1 kernel-certified by the
//! clean CIC kernel"; the JSON lane grades that row `ay-in-process` with a
//! `clean-cic:v2:` proof term, KernelRechecked, Empty axiom closure. `x >= x`
//! is a reflexivity tautology and the kernel now closes it unaided, so dropping
//! the citation no longer changes the verdict. `unknown_theorem` behaves the
//! same way: the bogus citation is STILL a hard error, but the clause itself
//! now proves, so only the citation error remains pinned on it.
//!
//! Measured on this same binary, non-tautological uncited clauses still fail
//! strict verification — `x != x`, `x < x`, `x >= 5`, and `result > x` on a
//! body returning `x` — so this is a stronger kernel, not a weakened gate. The
//! `by`-token pass/fail delta itself is no longer demonstrated by this pair.

clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => Nat.le.refl (UInt64.toNat x)
}

pub fn no_citation(x: u64) -> u64
    ensures x >= x
{ x }

pub fn wrong_statement(x: u64) -> u64
    //~^ ERROR Trust strict verification failed for
    ensures x > x by u64_ge_refl
    //~^ ERROR citation `u64_ge_refl` failed the strict Clean statement/certification audit
{ x }

pub fn unknown_theorem(x: u64) -> u64
    ensures x >= x by no_such_theorem
    //~^ ERROR cited theorem `no_such_theorem` is not registered
{ x }

fn main() {}
