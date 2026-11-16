//@ edition: 2021
//@ aux-build: seal_dep_inl_c.rs
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A crate of `clean_island_seal_inlined_unsafe.rs` and its `_holds` twin,
//! built with optimization (the MIR inliner puts `swap_small` and `noise` into crate B's fns): a nested fn with `unsafe` on its own local, inlined (at -O) into
//! the fn it is declared in, which handles the holders safely. Sound.
extern crate seal_dep_inl_c as cc;
pub fn nested_unrelated<M: cc::Make>(a: &mut M::Out, b: &mut M::Out) -> bool {
    fn peek(k: &u8) -> u8 { unsafe { ::core::ptr::read_volatile(k as *const u8) } }
    let k = 7u8;
    let pa: *mut M::Out = a; let pb: *mut M::Out = b;
    (pa == pb) || peek(&k) == 0
}
