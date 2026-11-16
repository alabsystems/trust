//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: ERROR
//! CLOSE NEGATIVE TWINS of `e9_cited_island_def_discharge`. Admitting an island
//! definition into a CITED clause decides only which kernel constant the name
//! denotes; it proves nothing. Each function below differs from the positive
//! `add2` in exactly one respect, and each MUST stay a hard citation error with
//! its rows unproved. A twin that starts compiling is a soundness incident, not
//! a fixture to re-bless.
//!
//! The island is the positive fixture's plus `wmul`/`wmul_self`, so a refusal
//! here can never be the incidental "the island did not elaborate" kind: every
//! declaration below is one the positive fixture (or `wmul`, its exact
//! structural copy) kernel-checks.
//!
//! `dont-require-annotations: ERROR` tolerates only the SECONDARY
//! strict-verification / Level-0 errors each function also raises; the primary
//! refusal of every twin is pinned by its own explicit ERROR annotation.
//! (Spelled out rather than quoted: compiletest parses an annotation marker out
//! of ANY line, prose included, so quoting one here would mint a second,
//! unsatisfiable expectation.)

clean {
    def wadd (a b : UInt64) : UInt64 := a + b
    theorem wadd_self : forall (a b : UInt64), wadd a b = wadd a b := fun a b => rfl

    def wmul (a b : UInt64) : UInt64 := a * b
    theorem wmul_self : forall (a b : UInt64), wmul a b = wmul a b := fun a b => rfl
}

// TWIN 1 — MUTATED BODY (the wrong theorem for THIS function). The clause and
// the citation are the positive fixture's, byte for byte; the body subtracts.
// The goal is `∀ a b, <import of sub_body> a b = wadd a b`, and `wadd_self`
// proves `wadd a b = wadd a b`, which is a different proposition.
pub fn sub_body(a: u64, b: u64) -> u64
    //~^ ERROR Trust strict verification failed for
    ensures result == wadd(a, b) by wadd_self
    //~^ ERROR citation `wadd_self` failed the strict Clean statement/certification audit
{
    a.wrapping_sub(b)
}

// TWIN 2 — A THEOREM ABOUT A DIFFERENT DEFINITION. The body is CORRECT and the
// clause is TRUE; only the citation is wrong. `wmul_self` is a perfectly good
// kernel-checked theorem — about `wmul`. A lane that accepted "some certified
// theorem was cited" instead of "the cited theorem proves THIS goal" passes it.
pub fn other_theorem(a: u64, b: u64) -> u64
    //~^ ERROR Trust strict verification failed for
    ensures result == wadd(a, b) by wmul_self
    //~^ ERROR citation `wmul_self` failed the strict Clean statement/certification audit
{
    a.wrapping_add(b)
}

// TWIN 3 — THE RIGHT THEOREM ON A CLAUSE NAMING A DIFFERENT DEFINITION. The
// body adds; the clause claims it multiplies. `wmul_self` is "about the
// definition the clause names", so a check that only matched the theorem to
// the CLAUSE's callee (and not to the function's import) passes it.
pub fn other_definition(a: u64, b: u64) -> u64
    //~^ ERROR Trust strict verification failed for
    ensures result == wmul(a, b) by wmul_self
    //~^ ERROR citation `wmul_self` failed the strict Clean statement/certification audit
{
    a.wrapping_add(b)
}

fn main() {
    let _ = (sub_body(1, 2), other_theorem(1, 2), other_definition(1, 2));
}
