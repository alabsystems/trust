//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_anchored.rs` and `_anchored_holds.rs`,
//! standing in for crates.io `hashbrown`: a crate of the SAME NAME as the
//! standard library's own `hashbrown`, with its map at the same path,
//! `hashbrown::map::HashMap`. A toy map over a `Vec`: safe, and sound.
#![forbid(unsafe_code)]

pub mod map {
    pub struct HashMap<K, V> {
        items: Vec<(K, V)>,
    }
    impl<K: PartialEq, V> HashMap<K, V> {
        pub fn new() -> Self {
            HashMap { items: Vec::new() }
        }
        pub fn insert(&mut self, k: K, v: V) -> bool {
            if self.items.iter().any(|(key, _)| *key == k) {
                return false;
            }
            self.items.push((k, v));
            true
        }
        pub fn len(&self) -> usize {
            self.items.len()
        }
    }
}
pub use map::HashMap;
