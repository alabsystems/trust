//! Blob-equivalence BEFORE side — the reader's PROPOSED clauses.
//!
//! The `ensures` PREDICATES below are the tippy mapper's machine-applied
//! output for ../pearlite/src/lib.rs (lint `trust_creusot_spec_sugar`; the
//! rewrite is pinned by the lint's rustfix ui test, and the harness test
//! `proposed_side_carries_the_mapper_output` keeps this file in lockstep).
//! Nothing in this file is an independent authorship of the property — that
//! is ../native/'s job, and keeping the two authorships separate is the point
//! of the gate (adversarial verdict 2026-08-21, defect 1: the mapper must not
//! co-author both sides).
//!
//! HARNESS FURNITURE, byte-identical to ../native/: the `clean { .. }` island
//! and the `by u64_ge_refl` citations. They exist because the v1 spec-emit
//! artifact renders goal rows for CITED ensures clauses only (the cited-only
//! walk — verdict defect 2; uncited denotation rows are a deferred producer
//! extension). Because the furniture is identical on both sides, it cancels
//! in the comparison: the only content that can differ is the predicate.

clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => Nat.le.refl (UInt64.toNat x)
}

pub fn observe(x: u64) -> u64
    ensures x >= x by u64_ge_refl
{
    x
}

pub fn keep(lo: u64) -> u64
    ensures lo <= lo by u64_ge_refl
{
    lo
}
