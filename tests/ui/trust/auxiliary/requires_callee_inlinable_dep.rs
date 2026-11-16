//@ compile-flags: --crate-type=rlib -Ztrust-verify=on -Copt-level=3
//@ edition: 2021
//@ no-prefer-dynamic
//! A dependency VERIFIED on the default policy, whose `#[inline]` `add1` exports
//! its `optimized_mir` for a downstream MIR inliner. `add1` is verified UNDER
//! `requires x < 100`: its `x + 1` overflow row is kernel-certified with the clause
//! as the entry hypothesis, so the exported body has that overflow check ELIDED.
//! A downstream caller is charged a `Precondition` row for the clause only at a
//! call that names `add1` (read from this crate's exported contract set); the
//! `dep_*` revisions of `requires_callee_erased_by_mir_inliner.rs` are what happens
//! when an explicit `-Zmir-opt-level=2` inliner copies this body instead.
//! `#[inline]` makes the export deterministic; without it, `-Copt-level=3`'s
//! automatic cross-crate inlinability exports the same leaf body (measured).

#[inline]
pub fn add1(x: u32) -> u32
    requires x < 100
{
    x + 1
}
