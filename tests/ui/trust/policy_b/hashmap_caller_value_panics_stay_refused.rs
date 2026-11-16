//@ needs-trust-verify
//@ edition: 2021
//@ revisions: index disjoint disjoint_print cap cap_hasher set_cap_hasher reserve collect_range_print extend_range_print zst_collect_print zst_from_iter ext_repeat_take ext_repeat_take_map ext_cycle ext_repeat_n_ufcs ext_pathbuf_map zst_src_from_iter_ref zst_src_enumerate extend_reserve tuple_extend unzip
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! W4 HASHMAP (2026-09-25, redo) — the PANICS a `HashMap`/`HashSet` call can
//! reach on a CALLER-SUPPLIED value stay refused now that `hashbrown` (the crate
//! behind std's tables, by structural identity) is credited.
//!
//! EVERY REVISION MUST STAY REFUSED. Each program panics at runtime for some
//! input. Fix the compiler, never this file.
//!
//! The vanilla class tolerates an absent sysroot callee's panic as "std's own
//! defined behaviour reacting to the environment". A panic about the CALLER's
//! own value is not that; before hashbrown was credited every one of these was
//! refused merely because `HashMap` was non-foundational (baseline: main,
//! stage-1 `7c7e46061`, all rc=1). What keeps each refused now:
//!
//!   * `index` — `m[&k]`: vcgen's `map-index-key-presence` row.
//!   * `disjoint` / `disjoint_print` — `get_disjoint_mut([&a, &b])` panics
//!     "duplicate keys found" when `a == b`; the family is excluded from the
//!     class by identity (`callee_is_hash_table_caller_value_panic`, since round
//!     2 against the pinned hashbrown panic census; its key-equivalence siblings
//!     are pinned in `hashmap_key_equivalence_and_bucket_layout_refused.rs`).
//!     `disjoint_print` puts a tolerated `println!` first, so the refusal cannot
//!     ride on the fold's representative.
//!   * `cap` / `cap_hasher` / `set_cap_hasher` / `reserve` — "Hash table capacity
//!     overflow" at `usize::MAX`: vcgen's `[unbounded_allocation]` row
//!     (`with_capacity_and_hasher` joined its recognizer with the first attempt).
//!   * `collect_range_print` / `extend_range_print` / `zst_collect_print` /
//!     `zst_from_iter` — a bulk insert from a huge or zero-sized source: the
//!     allocation lane (F1-F3 on main) charges the `collect`/`extend`.
//!
//! The revisions below `zst_from_iter` are the FALSE ACCEPTS the first attempt
//! (`w4-hashmap`, stage-1 `f828ea3d9`) built rc=0 and that then exited 101 (its
//! prober's classes 1 and 2, plus two found by this redo); each is refused on
//! this build:
//!
//!   * `ext_repeat_take` / `ext_repeat_take_map` / `ext_cycle` /
//!     `ext_repeat_n_ufcs` / `ext_pathbuf_map` — `extend` from a source whose
//!     `size_hint().0` is huge (`repeat().take(n)`, `cycle()` over a slice,
//!     `repeat_n`); hashbrown reserves it up front. The F2 `extend` sink.
//!   * `zst_src_from_iter_ref` / `zst_src_enumerate` — a ZERO-SIZED SOURCE
//!     (`&[()]` of `2^61` units, no memory) into a non-zero-sized table: the F3
//!     source rule.
//!   * `extend_reserve` — nightly `Extend::extend_reserve(m, n)`: added to vcgen's
//!     bulk-allocation recognizer by this redo.
//!   * `tuple_extend` / `unzip` — core's tuple `Extend` (and `Iterator::unzip`,
//!     which is built on it) reserves `size_hint().0` in EVERY half: vcgen now
//!     charges a tuple receiver holding a reserving collection, and `unzip`, as
//!     allocation sinks (this redo; the `Vec` twins were pre-existing false accepts
//!     on main, pinned in `tuple_extend_unzip_capacity_charged.rs`).
#![cfg_attr(extend_reserve, feature(extend_one))]

use std::collections::{HashMap, HashSet};
#[allow(unused_imports)]
use std::net::Ipv4Addr;
#[allow(unused_imports)]
use std::path::PathBuf;

#[cfg(index)]
pub fn index(m: &HashMap<u32, u32>, k: u32) -> u32 {
    //[index]~^ ERROR Trust strict verification failed for `hashmap_caller_value_panics_stay_refused::index`
    //[index]~| NOTE map-index-key-presence
    m[&k]
}

#[cfg(disjoint)]
pub fn disjoint(m: &mut HashMap<u32, u32>, a: u32, b: u32) {
    //[disjoint]~^ ERROR Trust strict verification failed for `hashmap_caller_value_panics_stay_refused::disjoint`
    if let [Some(x), Some(y)] = m.get_disjoint_mut([&a, &b]) {
        std::mem::swap(x, y);
    }
}

#[cfg(disjoint_print)]
pub fn disjoint_print(m: &mut HashMap<u32, u32>, a: u32, b: u32) {
    //[disjoint_print]~^ ERROR Trust strict verification failed for `hashmap_caller_value_panics_stay_refused::disjoint_print`
    println!("swapping");
    if let [Some(x), Some(y)] = m.get_disjoint_mut([&a, &b]) {
        std::mem::swap(x, y);
    }
}

#[cfg(cap)]
pub fn cap(n: usize) -> HashMap<u32, u32> {
    //[cap]~^ ERROR Trust strict verification failed for `hashmap_caller_value_panics_stay_refused::cap`
    //[cap]~| NOTE [unbounded_allocation] FAILED
    HashMap::with_capacity(n)
}

#[cfg(cap_hasher)]
pub fn cap_hasher(n: usize) -> HashMap<u32, u32> {
    //[cap_hasher]~^ ERROR Trust strict verification failed for `hashmap_caller_value_panics_stay_refused::cap_hasher`
    //[cap_hasher]~| NOTE [unbounded_allocation] FAILED
    HashMap::with_capacity_and_hasher(n, std::hash::RandomState::new())
}

#[cfg(set_cap_hasher)]
pub fn set_cap_hasher(n: usize) -> HashSet<u32> {
    //[set_cap_hasher]~^ ERROR Trust strict verification failed for `hashmap_caller_value_panics_stay_refused::set_cap_hasher`
    //[set_cap_hasher]~| NOTE [unbounded_allocation] FAILED
    HashSet::with_capacity_and_hasher(n, std::hash::RandomState::new())
}

#[cfg(reserve)]
pub fn reserve(m: &mut HashMap<u32, u32>, n: usize) {
    //[reserve]~^ ERROR Trust strict verification failed for `hashmap_caller_value_panics_stay_refused::reserve`
    //[reserve]~| NOTE [unbounded_allocation] FAILED
    m.reserve(n)
}

#[cfg(collect_range_print)]
pub fn collect_range_print(n: usize) -> HashSet<usize> {
    //[collect_range_print]~^ ERROR Trust strict verification failed for `hashmap_caller_value_panics_stay_refused::collect_range_print`
    println!("collecting {n}");
    (0..n).collect()
}

#[cfg(extend_range_print)]
pub fn extend_range_print(s: &mut HashSet<usize>, n: usize) {
    //[extend_range_print]~^ ERROR Trust strict verification failed for `hashmap_caller_value_panics_stay_refused::extend_range_print`
    println!("extending by {n}");
    s.extend(0..n)
}

#[cfg(zst_collect_print)]
pub fn zst_collect_print(n: usize) -> HashSet<()> {
    //[zst_collect_print]~^ ERROR Trust strict verification failed for `hashmap_caller_value_panics_stay_refused::zst_collect_print`
    println!("collecting {n} units");
    vec![(); n].into_iter().collect()
}

#[cfg(zst_from_iter)]
pub fn zst_from_iter(v: &[()]) -> HashSet<()> {
    //[zst_from_iter]~^ ERROR Trust strict verification failed for `hashmap_caller_value_panics_stay_refused::zst_from_iter`
    HashSet::from_iter(v.iter().copied())
}

#[cfg(ext_repeat_take)]
pub fn ext_repeat_take(s: &mut HashSet<Ipv4Addr>, n: usize) {
    //[ext_repeat_take]~^ ERROR Trust strict verification failed for `hashmap_caller_value_panics_stay_refused::ext_repeat_take`
    s.extend(std::iter::repeat(Ipv4Addr::LOCALHOST).take(n));
}

#[cfg(ext_repeat_take_map)]
pub fn ext_repeat_take_map(m: &mut HashMap<Ipv4Addr, u8>, n: usize) {
    //[ext_repeat_take_map]~^ ERROR Trust strict verification failed for `hashmap_caller_value_panics_stay_refused::ext_repeat_take_map`
    m.extend(std::iter::repeat((Ipv4Addr::LOCALHOST, 0u8)).take(n));
}

#[cfg(ext_cycle)]
pub fn ext_cycle(s: &mut HashSet<Ipv4Addr>, v: &[Ipv4Addr]) {
    //[ext_cycle]~^ ERROR Trust strict verification failed for `hashmap_caller_value_panics_stay_refused::ext_cycle`
    s.extend(v.iter().copied().cycle());
}

#[cfg(ext_repeat_n_ufcs)]
pub fn ext_repeat_n_ufcs(s: &mut HashSet<Ipv4Addr>, n: usize) {
    //[ext_repeat_n_ufcs]~^ ERROR Trust strict verification failed for `hashmap_caller_value_panics_stay_refused::ext_repeat_n_ufcs`
    Extend::extend(s, std::iter::repeat_n(Ipv4Addr::LOCALHOST, n));
}

#[cfg(ext_pathbuf_map)]
pub fn ext_pathbuf_map(m: &mut HashMap<PathBuf, u64>, p: &PathBuf, n: usize) {
    //[ext_pathbuf_map]~^ ERROR Trust strict verification failed for `hashmap_caller_value_panics_stay_refused::ext_pathbuf_map`
    m.extend(std::iter::repeat((p.clone(), 0u64)).take(n));
}

#[cfg(zst_src_from_iter_ref)]
pub fn zst_src_from_iter_ref(v: &[()]) -> HashSet<&()> {
    //[zst_src_from_iter_ref]~^ ERROR Trust strict verification failed for `hashmap_caller_value_panics_stay_refused::zst_src_from_iter_ref`
    HashSet::from_iter(v.iter())
}

#[cfg(zst_src_enumerate)]
pub fn zst_src_enumerate(v: &[()]) -> HashMap<usize, ()> {
    //[zst_src_enumerate]~^ ERROR Trust strict verification failed for `hashmap_caller_value_panics_stay_refused::zst_src_enumerate`
    HashMap::from_iter(v.iter().copied().enumerate())
}

#[cfg(extend_reserve)]
pub fn extend_reserve(m: &mut HashMap<u32, u32>, n: usize) {
    //[extend_reserve]~^ ERROR Trust strict verification failed for `hashmap_caller_value_panics_stay_refused::extend_reserve`
    <HashMap<u32, u32> as Extend<(u32, u32)>>::extend_reserve(m, n);
}

#[cfg(tuple_extend)]
pub fn tuple_extend(pair: &mut (HashSet<u32>, Vec<u8>), n: usize) {
    //[tuple_extend]~^ ERROR Trust strict verification failed for `hashmap_caller_value_panics_stay_refused::tuple_extend`
    pair.extend(std::iter::repeat((1u32, 1u8)).take(n));
}

#[cfg(unzip)]
pub fn unzip(n: usize) -> (HashSet<u32>, Vec<u8>) {
    //[unzip]~^ ERROR Trust strict verification failed for `hashmap_caller_value_panics_stay_refused::unzip`
    std::iter::repeat((1u32, 1u8)).take(n).unzip()
}
