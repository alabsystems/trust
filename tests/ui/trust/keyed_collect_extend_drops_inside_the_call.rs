//@ revisions: btreemap_extend_bomb_value btreemap_extend_bomb_value_certify
//@ revisions: hashmap_extend_bomb_value hashmap_extend_bomb_value_certify
//@ revisions: btreemap_collect_bomb_value btreemap_collect_bomb_value_certify
//@ revisions: hashmap_collect_bomb_value hashmap_collect_bomb_value_certify
//@ revisions: btreemap_extend_box_value hashmap_collect_box_value
//@ revisions: string_extend_bomb_str string_extend_bomb_str_certify
//@ revisions: btreeset_extend_box_key hashset_insert_box_key hashmap_remove_box_key
//@ revisions: btreeset_extend_dep_key hashset_extend_dep_key hashmap_insert_dep_key
//@ revisions: btreemap_insert_caller_drop
//@ revisions: btreemap_extend_u8_value btreemap_extend_u8_value_certify hashmap_extend_u8_value
//@ revisions: btreemap_extend_string_value hashmap_collect_string_value
//@ revisions: btreeset_extend_local_key hashset_insert_u32 hashmap_remove_u32
//@ revisions: string_extend_string vec_extend_bomb_value
//@ revisions: btreeset_extend_local_drop_key_cost btreeset_extend_local_drop_key_cost_release_std btreemap_extend_arc_value_cost
//@ revisions: btreeset_extend_local_drop_key_cost_certify btreemap_extend_arc_value_cost_certify
//@ revisions: btreemap_extend_arc_bomb_value btreeset_extend_local_skip_drop_key
//@ revisions: btreeset_extend_local_panicking_drop_key
//@ revisions: string_extend_cow_cost
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: keyed_drop_unverified_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[btreemap_extend_bomb_value_certify] compile-flags: -Ztrust-policy=certify
//@[hashmap_extend_bomb_value_certify] compile-flags: -Ztrust-policy=certify
//@[btreemap_collect_bomb_value_certify] compile-flags: -Ztrust-policy=certify
//@[hashmap_collect_bomb_value_certify] compile-flags: -Ztrust-policy=certify
//@[string_extend_bomb_str_certify] compile-flags: -Ztrust-policy=certify
//@[btreemap_extend_u8_value_certify] compile-flags: -Ztrust-policy=certify
//@[btreeset_extend_local_drop_key_cost_certify] compile-flags: -Ztrust-policy=certify
//@[btreemap_extend_arc_value_cost_certify] compile-flags: -Ztrust-policy=certify
//@[btreemap_extend_bomb_value] check-fail
//@[btreemap_extend_bomb_value_certify] check-fail
//@[hashmap_extend_bomb_value] check-fail
//@[hashmap_extend_bomb_value_certify] check-fail
//@[btreemap_collect_bomb_value] check-fail
//@[btreemap_collect_bomb_value_certify] check-fail
//@[hashmap_collect_bomb_value] check-fail
//@[hashmap_collect_bomb_value_certify] check-fail
//@[btreemap_extend_box_value] check-fail
//@[hashmap_collect_box_value] check-fail
//@[string_extend_bomb_str] check-fail
//@[string_extend_bomb_str_certify] check-fail
//@[btreeset_extend_box_key] check-fail
//@[hashset_insert_box_key] check-fail
//@[hashmap_remove_box_key] check-fail
//@[btreeset_extend_dep_key] check-fail
//@[hashset_extend_dep_key] check-fail
//@[hashmap_insert_dep_key] check-fail
//@[btreemap_insert_caller_drop] check-fail
//@[btreeset_extend_local_drop_key_cost_certify] check-fail
//@[btreemap_extend_arc_value_cost_certify] check-fail
//@[btreemap_extend_arc_bomb_value] check-fail
//@[btreeset_extend_local_skip_drop_key] check-fail
//@[btreeset_extend_local_panicking_drop_key] check-fail
//@[string_extend_cow_cost] check-fail
//@[btreemap_extend_u8_value] check-pass
//@[btreemap_extend_u8_value_certify] check-pass
//@[hashmap_extend_u8_value] check-fail
//@[btreemap_extend_string_value] check-pass
//@[hashmap_collect_string_value] check-fail
//@[btreeset_extend_local_key] check-pass
//@[hashset_insert_u32] check-pass
//@[hashmap_remove_u32] check-pass
//@[string_extend_string] check-pass
//@[vec_extend_bomb_value] check-fail
//@[btreeset_extend_local_drop_key_cost] check-pass
//@[btreeset_extend_local_drop_key_cost] needs-std-debug-assertions (pinned by `btreeset_extend_local_drop_key_cost_release_std`)
//@[btreeset_extend_local_drop_key_cost_release_std] check-fail
//@[btreeset_extend_local_drop_key_cost_release_std] ignore-std-debug-assertions (pinned by `btreeset_extend_local_drop_key_cost`)
//@[btreemap_extend_arc_value_cost] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! SP-1: the keyed-collect / collection-extend TOTAL sentinel erased the DROPS the
//! std call performs. `is_total_keyed_collect_call`, `is_total_collection_extend_call`
//! and `is_total_hash_map_query_call` (trust-mir-extract) rewrite the call to
//! `__trust_total_clone`, which the bridge models as total, after asking the KEY's
//! `Ord` or `Hash`/`Eq`, the hasher, the allocators and (SP-2) the source. None of them
//! asked about the values std DROPS inside the call:
//!  * a keyed `insert` (hence `extend`) that hits an existing key drops the old VALUE
//!    (map) and the passed KEY;
//!  * `BTreeMap`/`BTreeSet` `from_iter` drops the earlier of two equal keys, with its
//!    value (`DedupSortedIter`); the hash family's `from_iter` is `extend`;
//!  * `HashMap::remove`/`HashSet::remove` drop the stored KEY;
//!  * `String::extend` drops every owned item it appends.
//! The drop check on the caller's own MIR cannot see these: the drop is std's, inside
//! the call (compare `btreemap_insert_caller_drop`, where `insert` returns the old
//! `Bomb` and the CALLER drops it: refused before and after).
//!
//! BEFORE (stage 1 of `bbe56348e46`, compiled as compiletest does): the four
//! `*_bomb_value` shapes, `btreemap_extend_box_value`, `hashmap_collect_box_value` and
//! `string_extend_bomb_str` built exit 0 with no Verification Report, the `_certify`
//! revisions under certify too; a `-Ztrust-dump=mir` of `put_b` and `push_strs` shows
//! the call as `__trust_total_clone`. A certify rlib holding those seven functions,
//! linked into a verify-off `main` that arms the auxiliary's destructors, panicked
//! inside each std call (`Bomb::drop` < `BTreeMap::extend` / hashbrown `extend` /
//! `DedupSortedIter::next`; `DeallocBomb::deallocate` < the `Box` drop < `extend` or
//! `<String as Extend<Box<str, A>>>::extend`), exit 101. The cost revision
//! `btreeset_extend_local_drop_key_cost` built exit 0 with no report (the `Arc` and
//! `Cow` cost revisions were added later and measured with the new conjuncts made
//! vacuous: exit 0, no report). The `*_box_key` and `*_dep_key` guards were already
//! refused: the sentinel does not fire for those keys (the MIR dump of `ins_hs` keeps
//! `HashSet::insert`; a dependency's derived impls are not `is_builtin_derived`).
//!
//! AFTER: each gate also asks `tcx_drop_is_total` (the drop stamp's predicate: no user
//! `Drop` in the owned tree, audited std owners at sysroot allocators) of the key and,
//! for a map, the value (`keyed_collection_drops_are_total`); the hash query arm asks
//! it of the key for `insert`/`remove`; the `String` arm asks it of the item. Each shape
//! keeps its real callee and is refused (the annotations). The controls stay accepted
//! with no report: `u8` and `String` values, a local derived key, `u32` hash
//! `insert`/`remove`, `String` extend from `String` items, and `Vec` extend of a `Bomb`
//! (a `Vec` moves its items in and drops none). MUTATION: with the four new conjuncts
//! made vacuous (`true || ...`) and the compiler rebuilt, all twelve shape revisions
//! and the three cost revisions built exit 0 with no report again, the guards and
//! controls kept their verdicts, and the certify rlib built and panicked as above.
//!
//! COST (docs/DECISION_QUEUE.md SP-1-DROPS): a key or value whose drop runs any user
//! `Drop`, a local and total one included (`btreeset_extend_local_drop_key_cost`), or a
//! std owner outside the audited drop list (`Arc`, `btreemap_extend_arc_value_cost`;
//! `Cow<str>`, whose `Owned` field the predicate reads as an unnormalized projection,
//! `string_extend_cow_cost`) loses the sentinel and is refused.
//!
//! COST RECOVERED UNDER THE DEFAULT POLICY (2026-10-13, DECISION_QUEUE
//! SP-1-DROPS-COST-1): the sentinel is still withheld from the `DropKey` and `Arc<u32>`
//! shapes, but the real `extend` they keep is no longer refused there. CALL-REACH-1
//! walks its instance (`TRUST_CALL_REACH_DEBUG=1`: `closed(prefilter)` for both, on the
//! stage 1 of `825437bfeb`): every body it can run is sysroot-resident (`Arc`'s drop is
//! `alloc`'s, at `u32`) or a local item held to its own root (`DropKey::drop`). The
//! call keeps one `[assert]` panic-freedom row, reported runtime-checked, so
//! `btreeset_extend_local_drop_key_cost` and `btreemap_extend_arc_value_cost` build under
//! the default policy WITH a Verification Report (exit 0; `0 proved, 1 runtime-checked,
//! 1 skipped`). The cost stands under certify (the `_cost_certify` twins, refused for
//! that row). Guards, all refused under the default policy: the same `Arc` holding a
//! dependency's `Bomb` (`btreemap_extend_arc_bomb_value`: the walk opens at
//! `Arc::drop_slow` → `Bomb::drop`), a local key whose `Drop` is `#[trust::skip]`
//! (`btreeset_extend_local_skip_drop_key`: the walk opens at the skipped body, which no
//! root holds), and a local key whose `Drop` panics
//! (`btreeset_extend_local_panicking_drop_key`: the `Drop` is its own root and is
//! refused, so the crate does not build).
//!
//! Ordinary Rust programs: the auxiliary is a plain verify-off dependency
//! (`auxiliary/keyed_drop_unverified_dep.rs`); this crate names the
//! allocator-carrying boxes only through its aliases, so it needs no feature gate.
//!
//! RE-PINNED 2026-10-15 (the merge of 2026-10-14; DECISION_QUEUE D103): `btreemap_extend_arc_value_cost`, `btreeset_extend_local_drop_key_cost`, `hashmap_collect_string_value`, `hashmap_extend_u8_value`, `vec_extend_bomb_value`
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
//!
//! RE-PINNED 2026-10-18 (the 1.101 toolchain migration): the two cost
//! revisions build again with the SP-1-DROPS-COST-1 verdict (exit 0 WITH a
//! Verification Report: 0 proved, 1 runtime-checked, 1 skipped out of 2),
//! so they are check-pass again; the other three D103 flips
//! (`hashmap_collect_string_value`, `hashmap_extend_u8_value`,
//! `vec_extend_bomb_value`) still refuse on the same stage 1.

extern crate keyed_drop_unverified_dep as dep;

#[allow(unused_imports)]
use dep::{Bomb, BombBox, BombKey, BombStr};
#[allow(unused_imports)]
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

/// A LOCAL key with derived `Ord` and a total drop. (No `Hash`: a derived `Hash`
/// calls `<u32 as Hash>::hash::<H>` at a generic hasher, which strict refuses in the
/// derived body itself.)
#[cfg(btreeset_extend_local_key)]
#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct PlainKey(pub u32);

/// A LOCAL key with derived `Ord` and its own (total) `Drop`.
#[cfg(any(btreeset_extend_local_drop_key_cost, btreeset_extend_local_drop_key_cost_release_std, btreeset_extend_local_drop_key_cost_certify))]
#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct DropKey(pub u32);

#[cfg(any(btreeset_extend_local_drop_key_cost, btreeset_extend_local_drop_key_cost_release_std, btreeset_extend_local_drop_key_cost_certify))]
impl Drop for DropKey {
    fn drop(&mut self) {}
}

/// A LOCAL key whose `Drop` is `#[trust::skip]`: no root holds it.
#[cfg(btreeset_extend_local_skip_drop_key)]
#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct SkipDropKey(pub u32);

#[cfg(btreeset_extend_local_skip_drop_key)]
impl Drop for SkipDropKey {
    #[trust::skip]
    fn drop(&mut self) {
        panic!("skipped drop")
    }
}

/// A LOCAL key whose `Drop` panics: its own root, and refused there.
#[cfg(btreeset_extend_local_panicking_drop_key)]
#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct PanicDropKey(pub u32);

#[cfg(btreeset_extend_local_panicking_drop_key)]
impl Drop for PanicDropKey {
    fn drop(&mut self) {
        //[btreeset_extend_local_panicking_drop_key]~^ ERROR Trust strict verification failed for `<keyed_collect_extend_drops_inside_the_call::PanicDropKey as core::ops::drop::Drop>::drop`
        panic!("panicking drop")
    }
}

// ---- the old VALUE a keyed `extend` drops on a key collision ----

#[cfg(any(btreemap_extend_bomb_value, btreemap_extend_bomb_value_certify))]
pub fn put_b(m: &mut BTreeMap<u32, Bomb>, k: u32, b: Bomb) {
    //[btreemap_extend_bomb_value,btreemap_extend_bomb_value_certify]~^ ERROR Trust strict verification failed for `keyed_collect_extend_drops_inside_the_call::put_b`
    m.extend([(k, b)]);
}

#[cfg(any(hashmap_extend_bomb_value, hashmap_extend_bomb_value_certify))]
pub fn put_h(m: &mut HashMap<u32, Bomb>, k: u32, b: Bomb) {
    //[hashmap_extend_bomb_value,hashmap_extend_bomb_value_certify]~^ ERROR Trust strict verification failed for `keyed_collect_extend_drops_inside_the_call::put_h`
    m.extend([(k, b)]);
}

// ---- the duplicate pair `from_iter` drops ----

#[cfg(any(btreemap_collect_bomb_value, btreemap_collect_bomb_value_certify))]
pub fn mk_b(a: Bomb, b: Bomb) -> BTreeMap<u32, Bomb> {
    //[btreemap_collect_bomb_value,btreemap_collect_bomb_value_certify]~^ ERROR verification failed for `keyed_collect_extend_drops_inside_the_call::mk_b`
    [(1u32, a), (1u32, b)].into_iter().collect()
}

#[cfg(any(hashmap_collect_bomb_value, hashmap_collect_bomb_value_certify))]
pub fn mk_h(a: Bomb, b: Bomb) -> HashMap<u32, Bomb> {
    //[hashmap_collect_bomb_value,hashmap_collect_bomb_value_certify]~^ ERROR verification failed for `keyed_collect_extend_drops_inside_the_call::mk_h`
    [(1u32, a), (1u32, b)].into_iter().collect()
}

// ---- a value with no `Drop` of its own whose glue runs a dependency's allocator ----

#[cfg(btreemap_extend_box_value)]
pub fn put_box(m: &mut BTreeMap<u32, BombBox>, k: u32, b: BombBox) {
    //[btreemap_extend_box_value]~^ ERROR Trust strict verification failed for `keyed_collect_extend_drops_inside_the_call::put_box`
    m.extend([(k, b)]);
}

#[cfg(hashmap_collect_box_value)]
pub fn mk_box(a: BombBox, b: BombBox) -> HashMap<u32, BombBox> {
    //[hashmap_collect_box_value]~^ ERROR verification failed for `keyed_collect_extend_drops_inside_the_call::mk_box`
    [(1u32, a), (1u32, b)].into_iter().collect()
}

// ---- guards: a box at a dependency allocator as the KEY (the sentinel does not ----
// ---- fire for it: the real callee stays) ----

#[cfg(btreeset_extend_box_key)]
pub fn add_bs(s: &mut BTreeSet<BombBox>, k: BombBox) {
    //[btreeset_extend_box_key]~^ ERROR Trust strict verification failed for `keyed_collect_extend_drops_inside_the_call::add_bs`
    s.extend([k]);
}

#[cfg(hashset_insert_box_key)]
pub fn ins_hs(s: &mut HashSet<BombBox>, k: BombBox) -> bool {
    //[hashset_insert_box_key]~^ ERROR Trust strict verification failed for `keyed_collect_extend_drops_inside_the_call::ins_hs`
    s.insert(k)
}

#[cfg(hashmap_remove_box_key)]
pub fn rm_hm(m: &mut HashMap<BombBox, u8>, k: &BombBox) -> Option<u8> {
    //[hashmap_remove_box_key]~^ ERROR Trust strict verification failed for `keyed_collect_extend_drops_inside_the_call::rm_hm`
    m.remove(k)
}

// ---- every owned item `String::extend` appends ----

#[cfg(any(string_extend_bomb_str, string_extend_bomb_str_certify))]
pub fn push_strs(s: &mut String, it: std::vec::IntoIter<BombStr>) {
    //[string_extend_bomb_str,string_extend_bomb_str_certify]~^ ERROR Trust strict verification failed for `keyed_collect_extend_drops_inside_the_call::push_strs`
    s.extend(it);
}

// ---- guards: a dependency's derived key (the sentinel does not fire for it) ----

#[cfg(btreeset_extend_dep_key)]
pub fn add_dep_bs(s: &mut BTreeSet<BombKey>, k: BombKey) {
    //[btreeset_extend_dep_key]~^ ERROR Trust strict verification failed for `keyed_collect_extend_drops_inside_the_call::add_dep_bs`
    s.extend([k]);
}

#[cfg(hashset_extend_dep_key)]
pub fn add_dep_hs(s: &mut HashSet<BombKey>, k: BombKey) {
    //[hashset_extend_dep_key]~^ ERROR Trust strict verification failed for `keyed_collect_extend_drops_inside_the_call::add_dep_hs`
    s.extend([k]);
}

#[cfg(hashmap_insert_dep_key)]
pub fn ins_dep_hm(m: &mut HashMap<BombKey, u8>, k: BombKey) {
    //[hashmap_insert_dep_key]~^ ERROR Trust strict verification failed for `keyed_collect_extend_drops_inside_the_call::ins_dep_hm`
    m.insert(k, 0);
}

// ---- control: the CALLER drops the old value `insert` returns (refused) ----

#[cfg(btreemap_insert_caller_drop)]
pub fn ins_b(m: &mut BTreeMap<u32, Bomb>, k: u32, b: Bomb) {
    //[btreemap_insert_caller_drop]~^ ERROR Trust full verification failed for `keyed_collect_extend_drops_inside_the_call::ins_b`: this body drops a value whose type carries `keyed_drop_unverified_dep::Bomb`
    m.insert(k, b);
}

// ---- controls that stay accepted ----

#[cfg(any(btreemap_extend_u8_value, btreemap_extend_u8_value_certify))]
pub fn put_b8(m: &mut BTreeMap<u32, u8>, k: u32, b: u8) {
    m.extend([(k, b)]);
}

#[cfg(hashmap_extend_u8_value)]
pub fn put_h8(m: &mut HashMap<u32, u8>, k: u32, b: u8) {
    m.extend([(k, b)]);
}

#[cfg(btreemap_extend_string_value)]
pub fn put_bs(m: &mut BTreeMap<u32, String>, k: u32, b: String) {
    m.extend([(k, b)]);
}

#[cfg(hashmap_collect_string_value)]
pub fn mk_hs(a: String, b: String) -> HashMap<u32, String> {
    [(1u32, a), (1u32, b)].into_iter().collect()
}

#[cfg(btreeset_extend_local_key)]
pub fn add_plain(s: &mut BTreeSet<PlainKey>, k: PlainKey) {
    s.extend([k]);
}

#[cfg(hashset_insert_u32)]
pub fn ins_u32(s: &mut HashSet<u32>, k: u32) -> bool {
    s.insert(k)
}

#[cfg(hashmap_remove_u32)]
pub fn rm_u32(m: &mut HashMap<u32, u8>, k: &u32) -> Option<u8> {
    m.remove(k)
}

#[cfg(string_extend_string)]
pub fn push_strings(s: &mut String, it: std::vec::IntoIter<String>) {
    s.extend(it);
}

#[cfg(vec_extend_bomb_value)]
pub fn push_bombs(v: &mut Vec<Bomb>, b: Bomb) {
    v.extend([b]);
}

// ---- cost: a local key with its own `Drop` loses the sentinel (accepted under ----
// ---- the default policy with a runtime-checked row; refused under certify) ----

#[cfg(any(btreeset_extend_local_drop_key_cost, btreeset_extend_local_drop_key_cost_release_std, btreeset_extend_local_drop_key_cost_certify))]
pub fn add_drop_key(s: &mut BTreeSet<DropKey>, k: DropKey) {
    //[btreeset_extend_local_drop_key_cost_certify]~^ ERROR Trust strict verification failed for `keyed_collect_extend_drops_inside_the_call::add_drop_key`
    s.extend([k]);
}

// ---- guards: a local `Drop` that is skipped, or that panics, stays refused ----

#[cfg(btreeset_extend_local_skip_drop_key)]
pub fn add_skip_drop_key(s: &mut BTreeSet<SkipDropKey>, k: SkipDropKey) {
    //[btreeset_extend_local_skip_drop_key]~^ ERROR Trust strict verification failed for `keyed_collect_extend_drops_inside_the_call::add_skip_drop_key`
    s.extend([k]);
}

#[cfg(btreeset_extend_local_panicking_drop_key)]
pub fn add_panic_drop_key(s: &mut BTreeSet<PanicDropKey>, k: PanicDropKey) {
    s.extend([k]);
}

// ---- cost: std owners outside the drop stamp's audited list (`Arc<u32>`: ----
// ---- accepted under the default policy with a runtime-checked row; refused ----
// ---- under certify) ----

#[cfg(any(btreemap_extend_arc_value_cost, btreemap_extend_arc_value_cost_certify))]
pub fn put_arc(m: &mut BTreeMap<u32, std::sync::Arc<u32>>, k: u32, b: std::sync::Arc<u32>) {
    //[btreemap_extend_arc_value_cost_certify]~^ ERROR Trust strict verification failed for `keyed_collect_extend_drops_inside_the_call::put_arc`
    m.extend([(k, b)]);
}

// ---- guard: the same `Arc` over a dependency's `Bomb` stays refused ----

#[cfg(btreemap_extend_arc_bomb_value)]
pub fn put_arc_bomb(
    m: &mut BTreeMap<u32, std::sync::Arc<Bomb>>,
    k: u32,
    b: std::sync::Arc<Bomb>,
) {
    //[btreemap_extend_arc_bomb_value]~^^^^^ ERROR Trust strict verification failed for `keyed_collect_extend_drops_inside_the_call::put_arc_bomb`
    m.extend([(k, b)]);
}

#[cfg(string_extend_cow_cost)]
pub fn push_cows(s: &mut String, it: std::vec::IntoIter<std::borrow::Cow<'static, str>>) {
    //[string_extend_cow_cost]~^ ERROR Trust strict verification failed for `keyed_collect_extend_drops_inside_the_call::push_cows`
    s.extend(it);
}
