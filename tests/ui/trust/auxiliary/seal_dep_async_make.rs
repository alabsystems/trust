//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_lowering.rs` (crate B): hands out an
//! `async` closure over two places of the caller's type (behind an
//! associated type, so that no type argument names the caller's), which
//! swaps them. Safe, and sound.
#![forbid(unsafe_code)]

pub trait Make {
    type Out;
}

pub fn later<'a, M: Make>(a: &'a mut M::Out, b: &'a mut M::Out) -> impl AsyncFnOnce() + 'a {
    async move || std::mem::swap(a, b)
}
