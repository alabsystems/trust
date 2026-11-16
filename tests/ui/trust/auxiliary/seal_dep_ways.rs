//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_ways.rs`: two ways to one body that
//! swaps two values. `Make` hides the type a caller's marker makes behind an
//! associated type, so that no type argument of these fns holds a sealed
//! value: what they do is read in their bodies. Safe to call, and sound.

pub trait Make {
    type Out;
}

#[inline(never)]
pub fn swapper<M: Make>(a: &mut M::Out, b: &mut M::Out) {
    std::mem::swap(a, b)
}

#[inline(never)]
pub fn left<M: Make>(a: &mut M::Out, b: &mut M::Out) {
    swapper::<M>(a, b)
}

#[inline(never)]
pub fn right<M: Make>(a: &mut M::Out, b: &mut M::Out) {
    swapper::<M>(a, b)
}
