//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_standing.rs` and `_standing_holds.rs`:
//! items whose paths, where they are defined, end as std's and another
//! dependency's do. Safe, and sound.
#![forbid(unsafe_code)]

/// A stack named `Vec`, at `seal_dep_stack::stack::Vec`: `push` only adds.
pub mod stack {
    pub struct Vec<T> {
        items: std::vec::Vec<T>,
    }
    impl<T> Vec<T> {
        pub fn new() -> Self {
            Vec { items: std::vec::Vec::new() }
        }
        pub fn push(&mut self, value: T) {
            self.items.push(value)
        }
    }
}

/// At `seal_dep_stack::util::keep`: swaps what it is handed (a value over
/// another).
pub mod util {
    pub fn keep<T>(a: &mut T, b: &mut T) -> usize {
        std::mem::swap(a, b);
        0
    }
}
