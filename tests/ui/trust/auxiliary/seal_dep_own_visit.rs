//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_own_crates.rs` and its twin (crate B):
//! a trait, ITS OWN impl of it for its own pair (it only measures), and a
//! driver that runs whatever impl it is handed. Safe, and sound.
#![forbid(unsafe_code)]

pub trait Visit {
    fn visit(&mut self, other: &mut Self) -> usize;
}
pub struct Pair<T>(pub T);
impl<T> Visit for Pair<T> {
    fn visit(&mut self, other: &mut Self) -> usize {
        std::mem::size_of_val(&self.0) + std::mem::size_of_val(&other.0)
    }
}

pub fn drive<T: Visit>(a: &mut T, b: &mut T) -> usize {
    a.visit(b)
}
