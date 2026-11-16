//@ edition: 2021
//@ aux-build: seal_dep_chain_03.rs
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! Crate 2 of 20 of `clean_island_seal_crate_sets.rs` and its `_holds`
//! twin: `t` and `u` each call the next crate's `t` and `u` (the last calls
//! none). Safe, and sound.
#![forbid(unsafe_code)]

extern crate seal_dep_chain_03;

use std::ops::DerefMut;

#[inline(never)]
pub fn t<T>(x: &mut T) {
    seal_dep_chain_03::t::<T>(x);
    seal_dep_chain_03::u::<&mut T>(&mut &mut *x);
}

#[inline(never)]
pub fn u<R: DerefMut>(r: &mut R)
where
    R::Target: Sized,
{
    seal_dep_chain_03::t::<R::Target>(&mut **r);
    seal_dep_chain_03::u::<R>(r);
}
