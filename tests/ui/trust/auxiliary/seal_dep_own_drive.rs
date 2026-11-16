//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_own_crates.rs` and its twin (crate B):
//! a visitor trait and a driver that runs whatever impl it is handed (it did
//! not choose it). Safe, and sound.
#![forbid(unsafe_code)]

pub trait Visit {
    fn visit(&mut self, other: &mut Self) -> usize;
}

pub fn drive<T: Visit>(a: &mut T, b: &mut T) -> usize {
    a.visit(b)
}
