//@ edition: 2021
//@ aux-build: seal_dep_inl_c0.rs
//@ compile-flags: --crate-type=rlib -Copt-level=0 -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! Crate B of `clean_island_seal_inlined_unsafe.rs` and its `_holds` twin,
//! built without optimization: NO `unsafe` in its source. Sound.
extern crate seal_dep_inl_c0 as cc;
use cc::Make;
/// Runs C's swap: C's `unsafe` (inlined here at -O), not B's.
pub fn go_small<M: Make>(a: &mut M::Out, b: &mut M::Out) { cc::swap_small::<M>(a, b) }
/// Compares the holders safely, and calls C's `noise`, which never sees them.
pub fn go_noise<M: Make>(a: &mut M::Out, b: &mut M::Out) -> bool {
    let pa: *mut M::Out = a; let pb: *mut M::Out = b;
    (pa == pb) || cc::noise() == 0
}
