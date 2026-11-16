//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_linked_params.rs` and `_linked_params_holds.rs`:
//! fns generic over a parameter whose associated type they swap, overwrite or swap
//! through, safe and (one) `unsafe`; and a driver that runs a trait method its type
//! argument picks. Sound.

pub trait Make {
    type Out;
}
/// Swaps two values of `M::Out`, in `unsafe` code (sound: two `&mut` do not overlap).
pub fn direct<M: Make>(a: &mut M::Out, b: &mut M::Out) {
    unsafe { core::ptr::swap_nonoverlapping(a, b, 1) }
}
pub fn swap_out<M: Make>(a: &mut M::Out, b: &mut M::Out) {
    core::mem::swap(a, b)
}
pub fn put<M: Make>(slot: &mut M::Out, v: M::Out) {
    *slot = v
}
pub fn swap_deref<P: core::ops::DerefMut>(a: &mut P, b: &mut P)
where
    P::Target: Sized,
{
    core::mem::swap(&mut **a, &mut **b)
}
pub trait Sw {
    type Item;
    fn sw(a: &mut Self::Item, b: &mut Self::Item);
}
/// Runs the method its type argument picks.
pub fn run<K: Sw>(a: &mut K::Item, b: &mut K::Item) {
    K::sw(a, b)
}
