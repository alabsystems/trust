//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! Crate 20 of 20 of `clean_island_seal_crate_sets.rs` and its `_holds`
//! twin: `t` and `u` each call the next crate's `t` and `u` (the last calls
//! none). Safe, and sound.
#![forbid(unsafe_code)]

use std::ops::DerefMut;

#[inline(never)]
pub fn t<T>(x: &mut T) {
    let _ = x;
}

#[inline(never)]
pub fn u<R: DerefMut>(r: &mut R)
where
    R::Target: Sized,
{
    let _ = r;
}
