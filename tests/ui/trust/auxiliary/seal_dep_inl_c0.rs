//@ edition: 2021
//@ compile-flags: --crate-type=rlib -Copt-level=0 -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! Crate C of `clean_island_seal_inlined_unsafe.rs` and its `_holds` twin,
//! built without optimization. Sound: `swap_small` swaps the bytes of two distinct places of one
//! type; `noise` reads its OWN local through a raw pointer.
pub trait Make { type Out; }
pub union Pun<T> { pub t: *mut T, pub b: *mut ::core::mem::MaybeUninit<u8> }
#[inline(always)]
pub fn swap_small<M: Make>(a: &mut M::Out, b: &mut M::Out) {
    let pa: *mut M::Out = a; let pb: *mut M::Out = b;
    unsafe { ::core::ptr::swap_nonoverlapping(Pun::<M::Out> { t: pa }.b, Pun::<M::Out> { t: pb }.b, ::core::mem::size_of::<M::Out>()) }
}
#[inline(always)]
pub fn noise() -> u8 { let k = 7u8; unsafe { ::core::ptr::read_volatile(&k as *const u8) } }
