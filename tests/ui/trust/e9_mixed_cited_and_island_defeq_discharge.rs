//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! E9 POSITIVE fixture: a MIXED postcondition surface — an UNCITED clause that
//! kernel-discharges by definitional equality against a Clean island definition
//! and a CITED clause, on ONE function. This is the natural conversion idiom:
//! "the result IS the Lean spec, and by a Lean theorem about that spec it
//! satisfies a bound".
//!
//! Each clause always verified ALONE; together they were refused, silently
//! (`TRUST_E9_DEBUG BAIL=partially-cited` was the only trace), and the uncited
//! clause's rows stayed `unknown`.
//!
//! WHY THIS IS SOUND. A verdict row is not attributed to a single clause, so
//! kernel-crediting a function's clause rows needs the WHOLE postcondition
//! conjunction kernel-proven — the conjunction rule. That rule is unchanged;
//! what changed is who may prove an uncited clause. A cited theorem is one
//! kernel route to a clause, and island defeq (the SAME `elaborate_ensures`
//! goal, judged by the kernel's own `Eq.refl` check) is the other. The cited
//! lane grades the cited clauses and discharges NOTHING on a mixed surface; it
//! hands the certified theorem list to the island-defeq lane, which discharges
//! the function only if EVERY uncited clause also kernel-discharges. A clause
//! with neither route declines the whole function, as before — see
//! `e9_mixed_cited_and_island_defeq_undischarged.rs`.
//!
//! `check-pass` is NOT vacuous: the `result == min2(a, b)` rows are
//! `SpecEnsuresUnparseable` sentinels no solver lane can close, and
//! `-Ztrust-verify=on` is strict.

clean {
    def min2 (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
    theorem min2_le_left (a b : UInt64) : min2 a b <= a := by
      unfold min2
      split <;> omega
}

// Uncited first, cited second.
pub fn rmin(a: u64, b: u64) -> u64
    ensures result == min2(a, b)
    //~^ NOTE island definition `min2` kernel-discharges this postcondition by definitional equality
    ensures result <= a by min2_le_left
    //~^ NOTE citation `min2_le_left` kernel-discharges this postcondition statement
{
    if a < b { a } else { b }
}

// The same surface in the other authored order: clause order is not authority.
pub fn rmin_cited_first(a: u64, b: u64) -> u64
    ensures result <= a by min2_le_left
    //~^ NOTE citation `min2_le_left` kernel-discharges this postcondition statement
    ensures result == min2(a, b)
    //~^ NOTE island definition `min2` kernel-discharges this postcondition by definitional equality
{
    if a < b { a } else { b }
}

fn main() {
    let _ = (rmin(1, 2), rmin_cited_first(1, 2));
}
