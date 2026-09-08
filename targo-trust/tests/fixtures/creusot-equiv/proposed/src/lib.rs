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
//! There is deliberately no `clean { .. }` theorem or `by` citation here.
//! Schema-v2 spec-clean emits this ordinary uncited clause's canonical
//! denotation with `authority: none`, so the harness compares the mapper's
//! actual proposal instead of comparing shared proof furniture.

pub fn observe(x: u64) -> u64
    ensures x >= x
{
    x
}

pub fn keep(lo: u64) -> u64
    ensures lo <= lo
{
    lo
}
