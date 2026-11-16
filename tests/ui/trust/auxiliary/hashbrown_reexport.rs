//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! A verify-off dependency that names the SYSROOT `hashbrown` directly under
//! `rustc_private` and hands its values to its consumer. The consumer never names
//! `hashbrown` itself, so the loader does NOT record a direct load and std's
//! `HashMap` keeps its credit there — which is exactly why a hashbrown value the
//! consumer obtains this way must not be credited at the consumer's own call
//! sites. Consumed by `hashbrown_reexport_dep_not_vanilla.rs`.
#![feature(rustc_private)]
extern crate hashbrown;

pub use hashbrown::HashMap as RawMap;

/// A hashbrown table over foundational types, as the consumer sees it.
pub type Map = hashbrown::HashMap<u32, u32, std::hash::RandomState>;

pub fn make() -> Map {
    hashbrown::HashMap::with_hasher(std::hash::RandomState::new())
}

pub fn with_map<R>(f: impl FnOnce(&mut Map) -> R) -> R {
    let mut m = make();
    f(&mut m)
}
