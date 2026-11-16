//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_anchored.rs` and `_anchored_holds.rs`:
//! `seal_dep_b::keep`, whose whole path ends the path of `seal_dep_a`'s
//! `seal_dep_b::keep`. Safe, and sound.
#![forbid(unsafe_code)]

pub fn keep<T>(v: &mut Vec<T>, x: T) {
    v.push(x)
}
