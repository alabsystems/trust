// Checks the trust-only `hash_iteration_order` lint. Iterating a std `HashMap` or
// `HashSet` is reported when its hasher can order the same entries differently in
// another run: a hasher builder that carries state (`RandomState`, a seeded builder)
// or one the lint cannot see (a type parameter). An ordered collection, a hasher
// builder with no state (a zero-sized type), and a lookup are not reported, and
// `#[allow(hash_iteration_order)]` scopes a site whose order cannot reach output.
//
// The lint is ALLOW by default, as `env_mutation` is and for the same reason (a
// default-on level of any severity changes the stderr of every upstream test that
// iterates a `HashMap`), so the `#![deny]` below is what turns it on for this file.
// `hash-iteration-order-allow-by-default.rs` checks the default.

//@ edition: 2024

#![deny(hash_iteration_order)]

use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::hash::{BuildHasher, BuildHasherDefault, Hasher};

// RandomState, the default hasher: each process draws new keys.
fn random_state(mut map: HashMap<u32, u32>, set: HashSet<u32>, other: HashSet<u32>) {
    for _ in &map {}
    //~^ ERROR iterating a `HashMap` with `into_iter` follows its hash order
    let _ = map.iter();
    //~^ ERROR iterating a `HashMap` with `iter` follows its hash order
    let _ = map.keys();
    //~^ ERROR iterating a `HashMap` with `keys` follows its hash order
    let _ = map.values();
    //~^ ERROR iterating a `HashMap` with `values` follows its hash order
    for value in map.values_mut() {
        //~^ ERROR iterating a `HashMap` with `values_mut` follows its hash order
        *value += 1;
    }
    map.retain(|_, value| *value > 1);
    //~^ ERROR iterating a `HashMap` with `retain` follows its hash order
    let _ = set.union(&other);
    //~^ ERROR iterating a `HashSet` with `union` follows its hash order
    // Handed to a callee's `IntoIterator` bound: `Vec::extend` iterates the set.
    let mut ordered_by_hash: Vec<u32> = Vec::new();
    ordered_by_hash.extend(&set);
    //~^ ERROR iterating a `HashSet` with `into_iter` follows its hash order
    for _ in map.drain() {}
    //~^ ERROR iterating a `HashMap` with `drain` follows its hash order
    for _ in set {}
    //~^ ERROR iterating a `HashSet` with `into_iter` follows its hash order
}

// A hasher builder that carries state is reported, whatever seeds it.
struct Seeded(u64);

impl BuildHasher for Seeded {
    type Hasher = DefaultHasher;
    fn build_hasher(&self) -> DefaultHasher {
        let mut hasher = DefaultHasher::new();
        hasher.write_u64(self.0);
        hasher
    }
}

fn seeded(map: &HashMap<u32, u32, Seeded>) {
    for _ in map {}
    //~^ ERROR iterating a `HashMap` with `into_iter` follows its hash order
}

// A hasher builder the lint cannot see is reported: it may be `RandomState`.
fn generic<S: BuildHasher>(set: &HashSet<u32, S>) {
    for _ in set.iter() {}
    //~^ ERROR iterating a `HashSet` with `iter` follows its hash order
}

// A hasher builder with no state builds the same hasher in every process.
#[derive(Default)]
struct Fixed;

impl BuildHasher for Fixed {
    type Hasher = DefaultHasher;
    fn build_hasher(&self) -> DefaultHasher {
        DefaultHasher::new()
    }
}

fn stateless(map: &HashMap<u32, u32, Fixed>, set: &HashSet<u32, BuildHasherDefault<DefaultHasher>>) {
    for _ in map {}
    let _ = map.keys();
    for _ in set {}
}

fn stateless_generic<H: Hasher + Default>(set: &HashSet<u32, BuildHasherDefault<H>>) {
    for _ in set {}
}

// Ordered collections, and lookups, are not iteration in hash order.
fn ordered(map: &BTreeMap<u32, u32>, set: &BTreeSet<u32>) {
    for _ in map {}
    for _ in set.iter() {}
}

fn lookups(map: &HashMap<u32, u32>, set: &HashSet<u32>) -> bool {
    map.contains_key(&1) && map.get(&2).is_some() && set.contains(&3) && map.len() == set.len()
}

// A scoped allow is how a site whose order cannot reach output says so.
#[allow(hash_iteration_order)]
fn order_insensitive(map: &HashMap<u32, u32>) -> u32 {
    // A sum of integers is the same in every visit order.
    map.values().sum()
}

fn main() {
    random_state(HashMap::new(), HashSet::new(), HashSet::new());
    seeded(&HashMap::with_hasher(Seeded(7)));
    generic(&HashSet::<u32>::new());
    stateless(&HashMap::default(), &HashSet::default());
    stateless_generic::<DefaultHasher>(&HashSet::default());
    ordered(&BTreeMap::new(), &BTreeSet::new());
    let _ = lookups(&HashMap::new(), &HashSet::new());
    let _ = order_insensitive(&HashMap::new());
}
