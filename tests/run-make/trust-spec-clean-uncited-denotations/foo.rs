#![allow(dead_code)]

//! Schema-v2 spec-clean subject. Uncited function clauses are denotations,
//! never proof evidence; a cited clause remains on the independently graded
//! goal lane and must not be duplicated as a denotation.

// This theorem is available before the body walk. A later import-bearing island
// still forces EVERY cited postcondition in the crate through one authoritative
// post-walk adjudication, preventing a later rejected suffix from leaving an
// earlier Certified grade alive.
clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => @Nat.le.refl (UInt64.toNat x)
}

// The import-bearing declaration makes this island and its authored suffix
// genuinely deferred until the complete Rust admission table exists.
clean {
    theorem min2_import_thm : forall (a : UInt64) (b : UInt64),
        Nat.le
            (UInt64.toNat (trust_import_spec_clean_uncited_denotations__min2 a b))
            (UInt64.toNat a) :=
        fun a b => Decidable.casesOn
            (motive := fun (d : Decidable (LT.lt a b)) =>
                Nat.le (UInt64.toNat (Decidable.casesOn (motive := fun _ => UInt64)
                    d (fun _ => b) (fun _ => a))) (UInt64.toNat a))
            (instDecidableUInt64Lt a b)
            (fun h => Iff.mp (Nat.not_lt (UInt64.toNat a) (UInt64.toNat b)) h)
            (fun h => @Nat.le.refl (UInt64.toNat a))
}

pub fn min2(a: u64, b: u64) -> u64 {
    if a < b { a } else { b }
}

/// The repeated comparisons pin dense query indices even when canonical
/// propositions are byte-identical. The variable-divisor clauses retain a
/// query-owned typed tree, but division by a non-literal is outside the Clean
/// term fragment: they must remain counted refusal rows rather than disappear.
pub fn uncited(x: u64) -> u64
    requires x <= x
    requires x <= x
    requires x / x == x
    ensures x >= x
    ensures x >= x
    ensures x / x == x
{
    x
}

/// The precondition is an uncited denotation. The postcondition is the
/// two `ensures` are cited, remain goal-only, and deliberately use distinct
/// theorems from before/inside the deferred partition. Their dense identities
/// catch both row loss and duplicate publication.
pub fn cited_and_uncited(x: u64, y: u64) -> u64
    requires x <= x
    ensures x >= x by u64_ge_refl
    ensures min2(x, y) <= x by min2_import_thm
{
    x
}
