//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_anchored.rs` and `_anchored_holds.rs`:
//! a module named after another crate (a vendored copy, say), so that
//! `seal_dep_a::seal_dep_b::keep` ends as `seal_dep_b::keep` does. Safe,
//! and sound.
#![forbid(unsafe_code)]

pub mod seal_dep_b {
    pub fn keep<T>(v: &mut Vec<T>, x: T) {
        v.push(x)
    }
}
