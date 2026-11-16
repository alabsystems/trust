//@ needs-trust-verify
//@ aux-build: policy_b_unverified_dep.rs
//@ compile-flags: -Ztrust-verify=on -Copt-level=0 --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! Refuted 2026-09-16 (allocator lens, resumed): no `#[global_allocator]` is in
//! this graph, so the global-alloc contract "discharged vacuously for `Global`" —
//! while `Box<i32, dep::DepAlloc>`'s drop calls `<DepAlloc as Allocator>::
//! deallocate`, verify-off user code. The field-less foreign `A` sat as a DIRECT
//! field of the container and the bridge's audited std-owner walk accepted it as
//! structural; the caller's panic-freedom row PROVED. The audited shape is now
//! declined when an allocator-parameterized container carries a non-std ADT as a
//! direct field, and the drop falls to the fail-closed lane.
#![feature(allocator_api)]
extern crate policy_b_unverified_dep as dep;

pub fn consume(b: Box<i32, dep::DepAlloc>) {
    let _ = b;
}
