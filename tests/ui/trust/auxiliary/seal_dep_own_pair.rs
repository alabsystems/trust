//@ edition: 2021
//@ aux-build: seal_dep_own_drive.rs
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_own_crates.rs` and its twin (crate A):
//! its own pair, its own impl of B's trait for it (it only measures), and a
//! fn that runs B's driver on it. Safe, and sound.
#![forbid(unsafe_code)]

extern crate seal_dep_own_drive;

pub struct Pair<T>(pub T);
impl<T> seal_dep_own_drive::Visit for Pair<T> {
    fn visit(&mut self, other: &mut Self) -> usize {
        std::mem::size_of_val(&self.0) + std::mem::size_of_val(&other.0)
    }
}

pub fn run<T>(a: &mut Pair<T>, b: &mut Pair<T>) -> usize {
    seal_dep_own_drive::drive(a, b)
}
