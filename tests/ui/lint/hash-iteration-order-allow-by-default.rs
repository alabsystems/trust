// The trust-only `hash_iteration_order` lint is ALLOW by default: a crate that does
// not turn it on iterates a `RandomState` map without a word, exactly as upstream
// Rust compiles it. `hash-iteration-order.rs` checks what it reports once enabled.

//@ check-pass
//@ edition: 2024

use std::collections::{HashMap, HashSet};

fn main() {
    let map: HashMap<u32, u32> = HashMap::from([(1, 2), (3, 4)]);
    let set: HashSet<u32> = map.keys().copied().collect();
    for (key, value) in &map {
        assert!(set.contains(key) && *value > *key);
    }
}
