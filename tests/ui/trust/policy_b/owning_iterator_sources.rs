//@ needs-trust-verify
//@ edition: 2021
//@ no-prefer-dynamic
//@ aux-build:dropglue_bomb_dep.rs
//@ revisions: bounded refused bounded_hashset bounded_hashset_release_std
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[bounded] check-pass
//@[refused] check-fail
//@[bounded_hashset] check-fail
//@[bounded_hashset] needs-std-debug-assertions (pinned by `bounded_hashset_release_std`)
//@[bounded_hashset_release_std] check-pass
//@[bounded_hashset_release_std] ignore-std-debug-assertions (pinned by `bounded_hashset`)
//! Owning std iterators (`vec::IntoIter`, `vec::Drain`, `array::IntoIter`, the hash
//! and btree-set `IntoIter`s) are drop-audited: their `Drop` drops the remaining
//! elements and frees the buffer, nothing else. Without that, review round 64 measured
//! `d.extend(v.into_iter().map(..))` failing the default build once round 62 required
//! the source to be drop-total. A user `Drop` element still fails closed.
//!
//! CAPABILITY LOSS measured 2026-10-18 (the 1.101 toolchain migration;
//! docs/DECISION_QUEUE.md): `from_set` moved to its own `bounded_hashset`
//! revision, refused. hashbrown 0.17's `RawIterRange::new` carries
//! `debug_assert_ne!(len, 0)` / `debug_assert_eq!(ctrl % WIDTH, 0)` whose
//! operands the sysroot panic census cannot decide from the callee alone
//! (its summaries are value-independent), so `HashSet::into_iter` is no
//! longer census-total and the zero-obligation gate refuses the body. The
//! program is correct; the refusal is not a refutation.
//!
//! Trust (2026-10-19, std-config pin): measured under BOTH std configurations on the a7c37f9f0ee5
//! pin. The pre-existing pin was measured under a debug-assertions std; under the canonical
//! release std (debug-assertions-std=false) the verdict flips, so each configuration has its
//! own revision (KNOWN_HAZARDS, the debug-assertions std entry).
//! The refusing asserts are `debug_assert*!`, so under a release std they are
//! absent, `into_iter` is census-total again, and `bounded_hashset_release_std`
//! pins check-pass.
#![allow(dead_code)]
use std::collections::{BTreeSet, HashSet};

#[cfg(bounded)]
pub fn halves(v: Vec<u8>, d: &mut BTreeSet<u8>) {
    d.extend(v.into_iter().map(|x| x / 2));
}

#[cfg(bounded)]
pub fn kept(v: Vec<u8>, d: &mut BTreeSet<u8>) {
    d.extend(v.into_iter().filter(|x| *x > 2));
}

#[cfg(bounded)]
pub fn drained(v: &mut Vec<u8>, d: &mut BTreeSet<u8>) {
    d.extend(v.drain(..));
}

#[cfg(any(bounded_hashset, bounded_hashset_release_std))]
pub fn from_set(v: HashSet<u8>, d: &mut BTreeSet<u8>) {
    d.extend(v.into_iter());
}

#[cfg(bounded)]
pub fn from_array(v: [u8; 4], d: &mut Vec<u8>) {
    d.extend(v.into_iter().map(|x| x + 0));
}

#[cfg(refused)]
extern crate dropglue_bomb_dep;

#[cfg(refused)]
pub fn bombs(v: Vec<dropglue_bomb_dep::Bomb>, d: &mut Vec<u8>) {
    //[refused]~^ ERROR Trust strict verification failed for `owning_iterator_sources::bombs`
    d.extend(
        v.into_iter()
            .map(|b| {
                let n = b.0 as u8;
                std::mem::forget(b);
                n
            })
            .take(1),
    );
}
