//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! E9 POSITIVE fixture: a CITED `ensures` clause may name a Clean island
//! DEFINITION. This is the conversion idiom `ensures result == spec(x) by
//! impl_correct` — the Lean definition says WHAT the function computes, the
//! Lean theorem says WHY the body agrees with it.
//!
//! Before this lane only the UNCITED island-defeq route admitted island
//! definitions into a clause's facet table, so the identical clause with a
//! `by` token was refused as "no diagnostic E6 facet record exists for `wadd`".
//! All three cited consumers (in-walk discharge, deferred post-walk discharge,
//! diagnostic sweep) now offer the clause's island definitions to a
//! CLAUSE-LOCAL table through the same certification-audited admitter
//! (`admit_certified_island_definition`). The admission decides only which
//! kernel constant `wadd` denotes; the cited theorem must still prove the
//! resulting goal under the full certification audit.
//!
//! `check-pass` is NOT vacuous here: `-Ztrust-verify=on` is strict, and a
//! clause that calls an island definition is outside every solver lane's
//! vocabulary (its rows are fail-closed `SpecEnsuresUnparseable` sentinels),
//! so the ONLY thing that can close `add2`'s rows is the kernel citation
//! discharge this fixture exists for. The close negative twins live in
//! `e9_cited_island_def_undischarged.rs`.

clean {
    def wadd (a b : UInt64) : UInt64 := a + b
    theorem wadd_self : forall (a b : UInt64), wadd a b = wadd a b := fun a b => rfl

    def min2 (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
    theorem min2_le_left (a b : UInt64) : min2 a b <= a := by
      unfold min2
      split <;> omega
}

// `result`-binding clause: the goal is `∀ a b, <import of add2> a b = wadd a b`,
// which `wadd_self` proves because the E6 import of `a.wrapping_add(b)` is
// definitionally `wadd a b`.
pub fn add2(a: u64, b: u64) -> u64
    ensures result == wadd(a, b) by wadd_self
    //~^ NOTE citation `wadd_self` kernel-discharges this postcondition statement
{
    a.wrapping_add(b)
}

// `result`-free clause: a fact about the island definition itself. It holds for
// ANY body, so it needs no E6 import of `bound_fact` — only the island admission.
pub fn bound_fact(a: u64, b: u64) -> u64
    ensures min2(a, b) <= a by min2_le_left
    //~^ NOTE citation `min2_le_left` kernel-discharges this postcondition statement
{
    if a < b { a } else { b }
}

fn main() {
    let _ = (add2(1, 2), bound_fact(1, 2));
}
