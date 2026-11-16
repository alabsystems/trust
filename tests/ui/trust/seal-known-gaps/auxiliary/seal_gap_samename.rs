//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `r6_dyn_f1_entry_path_collapses_same_named_adts.rs` (review 6
//! of the review-14 build). Rust names each of these methods apart: a trait
//! implemented, in ONE module (the crate root), for std's `Vec` (it only
//! measures) and for this crate's own `stack::Vec` (it swaps two elements);
//! and two types named `Pair` in two modules, whose inherent methods are
//! written in one module `ops` (`a::Pair::touch` only reads, `b::Pair::touch`
//! swaps). Safe and sound.
#![forbid(unsafe_code)]
pub mod stack {
    pub struct Vec<T> { pub items: std::vec::Vec<T> }
}
pub trait Visit { fn visit(&mut self) -> usize; }
impl<T> Visit for std::vec::Vec<T> {
    fn visit(&mut self) -> usize { self.len() }
}
impl<T> Visit for stack::Vec<T> {
    fn visit(&mut self) -> usize {
        if self.items.len() >= 2 { self.items.swap(0, 1); }
        self.items.len()
    }
}
pub mod a { pub struct Pair<T> { pub x: T, pub y: T } }
pub mod b { pub struct Pair<T> { pub x: T, pub y: T } }
mod ops {
    impl<T> crate::a::Pair<T> {
        pub fn touch(&mut self) -> usize { core::mem::size_of_val(&self.x) }
    }
    impl<T> crate::b::Pair<T> {
        pub fn touch(&mut self) -> usize { core::mem::swap(&mut self.x, &mut self.y); 0 }
    }
}
