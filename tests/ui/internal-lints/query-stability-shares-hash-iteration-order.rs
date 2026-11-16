// `rustc::potential_query_instability` (compiler-internal) and the trust-only
// `hash_iteration_order` lint share one detector. The internal lint reports every
// use of an item marked `#[rustc_lint_query_instability]`; `hash_iteration_order`
// reports the same uses only for a std hash collection whose hasher can change the
// order between runs, so a hasher builder with no state is the internal lint's alone.

//@ compile-flags: -Z unstable-options
//@ edition: 2024

#![deny(hash_iteration_order, rustc::potential_query_instability)]

use std::collections::HashMap;
use std::collections::hash_map::DefaultHasher;
use std::hash::BuildHasherDefault;

fn main() {
    let random: HashMap<u32, u32> = HashMap::new();
    for _ in &random {}
    //~^ ERROR iterating a `HashMap` with `into_iter` follows its hash order
    //~| ERROR using `into_iter` can result in unstable query results
    let _ = random.keys();
    //~^ ERROR iterating a `HashMap` with `keys` follows its hash order
    //~| ERROR using `keys` can result in unstable query results
    // Through a callee's `IntoIterator` bound: `Vec::extend` iterates the map.
    let mut pairs: Vec<(&u32, &u32)> = Vec::new();
    pairs.extend(&random);
    //~^ ERROR iterating a `HashMap` with `into_iter` follows its hash order
    //~| ERROR using `into_iter` can result in unstable query results

    let stateless: HashMap<u32, u32, BuildHasherDefault<DefaultHasher>> = HashMap::default();
    for _ in &stateless {}
    //~^ ERROR using `into_iter` can result in unstable query results
    let mut copied = Vec::new();
    copied.extend(stateless.keys().copied());
    //~^ ERROR using `keys` can result in unstable query results
    let _: Vec<u32> = copied;
}
