//@ edition: 2021
//@ aux-build: seal_dep_inl_c.rs
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! Crate B of `clean_island_seal_inlined_unsafe.rs` and its `_holds` twin,
//! built with optimization (the MIR inliner puts `swap_small` and `noise` into crate B's fns): NO `unsafe` in its source. Sound.
extern crate seal_dep_inl_c as cc;
use cc::Make;
/// Runs C's swap: C's `unsafe` (inlined here at -O), not B's.
pub fn go_small<M: Make>(a: &mut M::Out, b: &mut M::Out) { cc::swap_small::<M>(a, b) }
/// Compares the holders safely, and calls C's `noise`, which never sees them.
pub fn go_noise<M: Make>(a: &mut M::Out, b: &mut M::Out) -> bool {
    let pa: *mut M::Out = a; let pb: *mut M::Out = b;
    (pa == pb) || cc::noise() == 0
}
