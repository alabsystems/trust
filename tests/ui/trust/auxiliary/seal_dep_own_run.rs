//@ edition: 2021
//@ aux-build: seal_dep_own_visit.rs
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_own_crates.rs` and its twin (crate A),
//! built with optimization: B's `drive` is inlined into `run`. Safe, and sound.
#![forbid(unsafe_code)]

extern crate seal_dep_own_visit;

pub fn run<T>(a: &mut seal_dep_own_visit::Pair<T>, b: &mut seal_dep_own_visit::Pair<T>) -> usize {
    seal_dep_own_visit::drive(a, b)
}
