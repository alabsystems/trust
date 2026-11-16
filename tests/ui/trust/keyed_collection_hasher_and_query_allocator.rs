//@ revisions: hashmap_insert_drop_hasher hashmap_insert_drop_hasher_certify
//@ revisions: hashmap_insert_drop_hasher_opt3
//@ revisions: hashmap_get_drop_hasher hashmap_get_drop_hasher_certify
//@ revisions: hashmap_extend_drop_hasher hashmap_collect_drop_hasher
//@ revisions: hashset_insert_drop_hasher
//@ revisions: hashset_remove_drop_hasher hashset_remove_drop_hasher_certify
//@ revisions: hashset_remove_drop_hasher_opt3
//@ revisions: hashmap_insert_dealloc_bomb hashmap_insert_dealloc_bomb_certify
//@ revisions: hashmap_insert_dealloc_bomb_opt3
//@ revisions: hashset_insert_dealloc_bomb hashmap_insert_alloc_bomb hashmap_entry_alloc_bomb
//@ revisions: hashmap_entry_alloc_bomb_certify hashmap_insert_string_key_dealloc_bomb
//@ revisions: hashset_collect_bad_hasher hashset_collect_bad_hasher_certify
//@ revisions: hashset_extend_bad_hasher hashset_contains_bad_hasher
//@ revisions: hash_u32_box_bad_hasher hash_u32_box_bad_hasher_certify
//@ revisions: hashmap_extend_dealloc_bomb
//@ revisions: hashmap_insert_u32 hashmap_insert_u32_certify
//@ revisions: hashmap_get_default_hasher hashset_collect_default_hasher
//@ revisions: hashset_extend_default_hasher
//@ revisions: hash_u32_default_hasher hash_u32_box_default_hasher
//@ revisions: hashmap_insert_local_hasher_cost
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: keyed_hasher_alloc_unverified_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[hashmap_insert_drop_hasher_certify] compile-flags: -Ztrust-policy=certify
//@[hashmap_insert_drop_hasher_opt3] compile-flags: -Ztrust-policy=certify -Copt-level=3 -Cdebuginfo=2
//@[hashmap_get_drop_hasher_certify] compile-flags: -Ztrust-policy=certify
//@[hashset_remove_drop_hasher_certify] compile-flags: -Ztrust-policy=certify
//@[hashset_remove_drop_hasher_opt3] compile-flags: -Ztrust-policy=certify -Copt-level=3 -Cdebuginfo=2
//@[hashmap_insert_dealloc_bomb_certify] compile-flags: -Ztrust-policy=certify
//@[hashmap_insert_dealloc_bomb_opt3] compile-flags: -Ztrust-policy=certify -Copt-level=3 -Cdebuginfo=2
//@[hashset_collect_bad_hasher_certify] compile-flags: -Ztrust-policy=certify
//@[hash_u32_box_bad_hasher_certify] compile-flags: -Ztrust-policy=certify
//@[hashmap_insert_u32_certify] compile-flags: -Ztrust-policy=certify
//@[hashmap_entry_alloc_bomb_certify] compile-flags: -Ztrust-policy=certify
//@[hashmap_insert_drop_hasher] check-fail
//@[hashmap_insert_drop_hasher_certify] check-fail
//@[hashmap_insert_drop_hasher_opt3] check-fail
//@[hashmap_get_drop_hasher] check-fail
//@[hashmap_get_drop_hasher_certify] check-fail
//@[hashmap_extend_drop_hasher] check-fail
//@[hashmap_collect_drop_hasher] check-fail
//@[hashset_insert_drop_hasher] check-fail
//@[hashset_remove_drop_hasher] check-fail
//@[hashset_remove_drop_hasher_certify] check-fail
//@[hashset_remove_drop_hasher_opt3] check-fail
//@[hashmap_insert_dealloc_bomb] check-fail
//@[hashmap_insert_dealloc_bomb_certify] check-fail
//@[hashmap_insert_dealloc_bomb_opt3] check-fail
//@[hashset_insert_dealloc_bomb] check-fail
//@[hashmap_insert_alloc_bomb] check-fail
//@[hashmap_entry_alloc_bomb] check-fail
//@[hashmap_entry_alloc_bomb_certify] check-fail
//@[hashmap_insert_string_key_dealloc_bomb] check-fail
//@[hashset_collect_bad_hasher] check-fail
//@[hashset_collect_bad_hasher_certify] check-fail
//@[hashset_extend_bad_hasher] check-fail
//@[hashset_contains_bad_hasher] check-fail
//@[hash_u32_box_bad_hasher] check-fail
//@[hash_u32_box_bad_hasher_certify] check-fail
//@[hashmap_extend_dealloc_bomb] check-fail
//@[hashmap_insert_local_hasher_cost] check-fail
//@[hashmap_insert_u32] check-pass
//@[hashmap_insert_u32_certify] check-pass
//@[hashmap_get_default_hasher] check-pass
//@[hashset_collect_default_hasher] check-fail
//@[hashset_extend_default_hasher] check-fail
//@[hash_u32_default_hasher] check-pass
//@[hash_u32_box_default_hasher] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! SP-1 review: the hash arms of the keyed-collect / collection-extend / hash-query
//! TOTAL sentinel (`is_total_keyed_collect_call`, `is_total_collection_extend_call`,
//! `is_total_hash_map_query_call`) and the primitive-hash sentinel
//! (`apply_total_primitive_hash_sentinel`) in trust-mir-extract rewrite the call to
//! `__trust_total_clone`, which the bridge models as total. Two kinds of code the
//! erased call runs were not asked:
//!  * the HASHER's type arguments. Each gate bound only the hasher's OUTER ADT to the
//!    sysroot. `BuildHasherDefault<H>` is a sysroot type whose `hash_one` builds an
//!    `H`, writes the key into it, finishes it and DROPS it, inside every hash; `Box<H>`
//!    is a sysroot `Hasher` that forwards `write_*` to `H`. With `H` a dependency's
//!    type, all of that is the dependency's unverified code (`DropHasher::drop`,
//!    `BadHasher::write`).
//!  * the ALLOCATOR of a hash query. `insert` on a full table runs hashbrown's
//!    `reserve_rehash`, which allocates through `A` and frees the old table through
//!    `A`. The extend gate asked `audited_container_allocators_are_sysroot`; the query
//!    gate did not (`hashmap_extend_dealloc_bomb` was refused before and after).
//!
//! BEFORE (stage 1 of `0a525e155ab`, the SP-1 commit; the same functions compiled
//! with `-Ztrust-verify=on --crate-type lib` against a verify-off dependency): every
//! shape revision built exit 0 with no Verification Report, the `_certify` ones under
//! certify too, and a `-Ztrust-dump=mir` of `insert_dh`, `get_dh`, `insert_db` and
//! `collect_bh` shows each call as `__trust_total_clone`. A certify rlib holding the
//! shapes, linked into a verify-off `main` that arms the dependency, panicked inside
//! each std call, exit 101: `DropHasher::drop` < `BuildHasherDefault::hash_one` <
//! hashbrown `insert`/`get`/`extend`/`remove` (the collect too);
//! `DeallocBomb::deallocate` < hashbrown's `prepare_resize` guard < `reserve_rehash`
//! < `HashMap::insert`/`HashSet::insert` (the table pre-filled with three entries);
//! `AllocBomb::allocate` < `reserve_rehash` < `HashMap::insert`; `BadHasher::write` <
//! `hash_one` < `HashSet` collect/`extend`/`contains`, and < `<Box<BadHasher> as
//! Hasher>::write_u32` < `<u32 as Hash>::hash`. The `BadHasher` collect is the SP-2
//! entry's open hasher residual (docs/KNOWN_HAZARDS.md).
//!
//! AFTER: every hasher gate asks `hasher_ty_is_sysroot_throughout` (the hasher and
//! every type argument at any depth a real-sysroot ADT), and the hash query gate asks
//! `audited_container_allocators_are_sysroot`. Each shape keeps its real callee and is
//! refused (the annotations). The controls stay accepted with no report: std's
//! `RandomState`, `BuildHasherDefault<DefaultHasher>`, `DefaultHasher` and
//! `Box<DefaultHasher>`.
//!
//! COST (docs/DECISION_QUEUE.md SP-1-DROPS): a hasher with a LOCAL type argument
//! (`BuildHasherDefault<LocalHasher>`, `hashmap_insert_local_hasher_cost`; before, it was
//! accepted with a report of the local `write`'s own row) loses the sentinel too.
//!
//! Ordinary Rust programs: the auxiliary is a plain verify-off dependency
//! (`auxiliary/keyed_hasher_alloc_unverified_dep.rs`); this crate names the
//! allocator-carrying maps only through its aliases, so it needs no feature gate.
//!
//! RE-PINNED 2026-10-15 (the merge of 2026-10-14; DECISION_QUEUE D103): `hashset_collect_default_hasher`, `hashset_extend_default_hasher`
//! now REFUSED (`check-fail`), measured on the merged stage 1. Each was accepted on
//! main through a grant the merge conjoined with the soundness line's fail-closed gate
//! for the same call, and that gate refuses it: the bounded-source capacity grant
//! also needs D93 (a)'s upfront-reservation fit on the per-allocation axiom (a hash
//! table or a widening destination over a slice, a `BTreeMap`/`LinkedList` source held
//! in many allocations, and `extend` into a live hash table are charged:
//! `bounded-source-destination-may-overflow` / `count-not-derivable`), a tuple
//! receiver is not a receiver whose length memory bounds (`receiver-length-not-bounded`),
//! and an `Arc` or a local `Drop` key in a bundled std body keeps its drop-glue row.
//! A capability loss of the conjunction, recorded; each is a correct program, and none
//! of these refusals is a refutation.

extern crate keyed_hasher_alloc_unverified_dep as dep;

#[allow(unused_imports)]
use dep::{BadBuild, BadHasher, DeallocMap, DeallocSet, DropBuild};
#[allow(unused_imports)]
use std::collections::{HashMap, HashSet};
#[allow(unused_imports)]
use std::hash::{BuildHasherDefault, DefaultHasher, Hash, Hasher};

// ---- the hasher instance `BuildHasherDefault<H>` builds and drops in every hash ----

#[cfg(any(
    hashmap_insert_drop_hasher,
    hashmap_insert_drop_hasher_certify,
    hashmap_insert_drop_hasher_opt3
))]
pub fn insert_dh(m: &mut HashMap<u32, u8, DropBuild>, k: u32) -> Option<u8> {
    //[hashmap_insert_drop_hasher,hashmap_insert_drop_hasher_certify,hashmap_insert_drop_hasher_opt3]~^ ERROR Trust strict verification failed for `keyed_collection_hasher_and_query_allocator::insert_dh`
    m.insert(k, 0)
}

#[cfg(any(hashmap_get_drop_hasher, hashmap_get_drop_hasher_certify))]
pub fn get_dh(m: &HashMap<u32, u8, DropBuild>, k: &u32) -> Option<u8> {
    //[hashmap_get_drop_hasher,hashmap_get_drop_hasher_certify]~^ ERROR Trust strict verification failed for `keyed_collection_hasher_and_query_allocator::get_dh`
    m.get(k).copied()
}

#[cfg(hashmap_extend_drop_hasher)]
pub fn extend_dh(m: &mut HashMap<u32, u8, DropBuild>, k: u32) {
    //[hashmap_extend_drop_hasher]~^ ERROR Trust strict verification failed for `keyed_collection_hasher_and_query_allocator::extend_dh`
    m.extend([(k, 0u8)]);
}

#[cfg(hashmap_collect_drop_hasher)]
pub fn collect_dh(a: u8, b: u8) -> HashMap<u32, u8, DropBuild> {
    //[hashmap_collect_drop_hasher]~^ ERROR verification failed for `keyed_collection_hasher_and_query_allocator::collect_dh`
    [(1u32, a), (2u32, b)].into_iter().collect()
}

#[cfg(hashset_insert_drop_hasher)]
pub fn insert_set_dh(s: &mut HashSet<u32, DropBuild>, k: u32) -> bool {
    //[hashset_insert_drop_hasher]~^ ERROR Trust strict verification failed for `keyed_collection_hasher_and_query_allocator::insert_set_dh`
    s.insert(k)
}

#[cfg(any(
    hashset_remove_drop_hasher,
    hashset_remove_drop_hasher_certify,
    hashset_remove_drop_hasher_opt3
))]
pub fn remove_set_dh(s: &mut HashSet<u32, DropBuild>, k: &u32) -> bool {
    //[hashset_remove_drop_hasher,hashset_remove_drop_hasher_certify,hashset_remove_drop_hasher_opt3]~^ ERROR Trust strict verification failed for `keyed_collection_hasher_and_query_allocator::remove_set_dh`
    s.remove(k)
}

// ---- the allocator a growing table allocates and frees through (query arm) ----

// `HashMap::insert`/`entry` over a dependency allocator: the query gate keeps the real
// callee, and the C2 std-map stamp (`authenticate_total_std_map`) now requires std's
// `Global` allocator too, so the bridge's stamp discharge
// (`is_std_total_hash_eq_key_map_insert_absent_callee`) no longer takes it and the call
// keeps its absent-callee row, as `HashSet::insert` does (KNOWN_HAZARDS, FIXED
// 2026-10-10: on the stage 1 of `dcac671f946` these built exit 0 with no diagnostic).
#[cfg(any(
    hashmap_insert_dealloc_bomb,
    hashmap_insert_dealloc_bomb_certify,
    hashmap_insert_dealloc_bomb_opt3
))]
pub fn insert_db(m: &mut DeallocMap, k: u32) -> Option<u8> {
    //[hashmap_insert_dealloc_bomb,hashmap_insert_dealloc_bomb_certify,hashmap_insert_dealloc_bomb_opt3]~^ ERROR Trust strict verification failed for `keyed_collection_hasher_and_query_allocator::insert_db`
    m.insert(k, 0)
}

#[cfg(hashmap_insert_alloc_bomb)]
pub fn insert_ab(m: &mut dep::AllocMap, k: u32) -> Option<u8> {
    //[hashmap_insert_alloc_bomb]~^ ERROR Trust strict verification failed for `keyed_collection_hasher_and_query_allocator::insert_ab`
    m.insert(k, 0)
}

#[cfg(any(hashmap_entry_alloc_bomb, hashmap_entry_alloc_bomb_certify))]
pub fn entry_ab(m: &mut dep::AllocMap, k: u32) -> u8 {
    //[hashmap_entry_alloc_bomb,hashmap_entry_alloc_bomb_certify]~^ ERROR Trust strict verification failed for `keyed_collection_hasher_and_query_allocator::entry_ab`
    *m.entry(k).or_insert(0)
}

// Trust (2026-10-10, CALL-REACH-1 design §4.3; written, not yet run): a `String` key
// passes the C2 key gate exactly as `u32` does, so the stamp's allocator conjunct is
// what refuses it, and CALL-REACH-1's deny arm would refuse it again in the bridge.
#[cfg(hashmap_insert_string_key_dealloc_bomb)]
pub fn insert_sdb(m: &mut dep::DeallocStringMap, k: String) -> Option<u8> {
    //[hashmap_insert_string_key_dealloc_bomb]~^ ERROR Trust strict verification failed for `keyed_collection_hasher_and_query_allocator::insert_sdb`
    m.insert(k, 0)
}

#[cfg(hashset_insert_dealloc_bomb)]
pub fn insert_set_db(s: &mut DeallocSet, k: u32) -> bool {
    //[hashset_insert_dealloc_bomb]~^ ERROR Trust strict verification failed for `keyed_collection_hasher_and_query_allocator::insert_set_db`
    s.insert(k)
}

// ---- the hasher's `write` (the SP-2 entry's open residual) ----

#[cfg(any(hashset_collect_bad_hasher, hashset_collect_bad_hasher_certify))]
pub fn collect_bh(w: &[u32]) -> HashSet<u32, BadBuild> {
    //[hashset_collect_bad_hasher,hashset_collect_bad_hasher_certify]~^ ERROR verification failed for `keyed_collection_hasher_and_query_allocator::collect_bh`
    w.iter().copied().collect()
}

#[cfg(hashset_extend_bad_hasher)]
pub fn extend_bh(s: &mut HashSet<u32, BadBuild>, w: &[u32]) {
    //[hashset_extend_bad_hasher]~^ ERROR Trust strict verification failed for `keyed_collection_hasher_and_query_allocator::extend_bh`
    s.extend(w.iter().copied());
}

#[cfg(hashset_contains_bad_hasher)]
pub fn contains_bh(s: &HashSet<u32, BadBuild>, k: &u32) -> bool {
    //[hashset_contains_bad_hasher]~^ ERROR Trust strict verification failed for `keyed_collection_hasher_and_query_allocator::contains_bh`
    s.contains(k)
}

// ---- `Box<H>` forwards `write_*` to `H` (the primitive-hash sentinel) ----

#[cfg(any(hash_u32_box_bad_hasher, hash_u32_box_bad_hasher_certify))]
pub fn hash_box_bh(x: &u32, s: &mut Box<BadHasher>) {
    //[hash_u32_box_bad_hasher,hash_u32_box_bad_hasher_certify]~^ ERROR Trust strict verification failed for `keyed_collection_hasher_and_query_allocator::hash_box_bh`
    x.hash(s)
}

// ---- guard: the extend twin asked the allocator already (refused before and after) ----

#[cfg(hashmap_extend_dealloc_bomb)]
pub fn extend_db(m: &mut DeallocMap, k: u32) {
    //[hashmap_extend_dealloc_bomb]~^ ERROR Trust strict verification failed for `keyed_collection_hasher_and_query_allocator::extend_db`
    m.extend([(k, 0u8)]);
}

// ---- controls that stay accepted: std's hashers all the way down ----

#[cfg(any(hashmap_insert_u32, hashmap_insert_u32_certify))]
pub fn insert_u32(m: &mut HashMap<u32, u8>, k: u32) -> Option<u8> {
    m.insert(k, 0)
}

#[cfg(hashmap_get_default_hasher)]
pub fn get_default(m: &HashMap<u32, u8, BuildHasherDefault<DefaultHasher>>, k: &u32) -> Option<u8> {
    m.get(k).copied()
}

#[cfg(hashset_collect_default_hasher)]
pub fn collect_default(w: &[u32]) -> HashSet<u32, BuildHasherDefault<DefaultHasher>> {
    w.iter().copied().collect()
}

#[cfg(hashset_extend_default_hasher)]
pub fn extend_default(s: &mut HashSet<u32, BuildHasherDefault<DefaultHasher>>, w: &[u32]) {
    s.extend(w.iter().copied());
}

#[cfg(hash_u32_default_hasher)]
pub fn hash_default(x: &u32, s: &mut DefaultHasher) {
    x.hash(s)
}

#[cfg(hash_u32_box_default_hasher)]
pub fn hash_box_default(x: &u32, s: &mut Box<DefaultHasher>) {
    x.hash(s)
}

// ---- cost: a hasher with a LOCAL type argument loses the sentinel ----

#[cfg(hashmap_insert_local_hasher_cost)]
#[derive(Default)]
pub struct LocalHasher(u64);

#[cfg(hashmap_insert_local_hasher_cost)]
impl Hasher for LocalHasher {
    fn write(&mut self, bytes: &[u8]) {
        for b in bytes {
            self.0 = self.0.wrapping_mul(31).wrapping_add(*b as u64);
        }
    }
    fn finish(&self) -> u64 {
        self.0
    }
}

#[cfg(hashmap_insert_local_hasher_cost)]
pub fn insert_local(m: &mut HashMap<u32, u8, BuildHasherDefault<LocalHasher>>, k: u32) -> Option<u8> {
    //[hashmap_insert_local_hasher_cost]~^ ERROR Trust strict verification failed for `keyed_collection_hasher_and_query_allocator::insert_local`
    m.insert(k, 0)
}
