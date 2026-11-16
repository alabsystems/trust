//@ revisions: btreeset_extend_clone_bomb_set btreeset_extend_clone_bomb_set_certify
//@ revisions: vec_extend_clone_bomb_set hashset_collect_clone_bomb_set_iter
//@ revisions: btreeset_collect_clone_bomb_set_iter hashset_collect_clone_bomb_keys
//@ revisions: vec_extend_clone_bomb_values vec_extend_clone_bomb_map_ref_cost
//@ revisions: btreeset_collect_bomb_keys vec_extend_bomb_list vec_extend_bomb_list_certify
//@ revisions: btreeset_extend_bomb_list hashset_collect_bomb_list_iter vec_extend_bomb_vec
//@ revisions: vec_extend_into_alloc_bomb_vec vec_extend_into_alloc_bomb_vec_certify
//@ revisions: btreeset_extend_into_clone_bomb_set
//@ revisions: btreeset_extend_enumerate_u128 btreeset_extend_enumerate_u128_certify
//@ revisions: btreemap_extend_enumerate_inclusive_u64 btreeset_extend_enumerate_repeat
//@ revisions: btreeset_extend_enumerate_chain_ranges btreeset_extend_enumerate_skip_u128
//@ revisions: btreeset_extend_global_set btreeset_extend_global_set_certify
//@ revisions: hashset_collect_global_list_iter btreeset_collect_global_keys
//@ revisions: btreeset_extend_enumerate_u32 btreeset_extend_enumerate_usize
//@ revisions: btreeset_extend_enumerate_take_repeat hashset_collect_enumerate_chain_slices
//@ revisions: vec_extend_enumerate_slice
//@ needs-trust-verify
//@ only-64bit
//@ edition: 2021
//@ aux-build: source_allocator_unverified_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[btreeset_extend_clone_bomb_set_certify] compile-flags: -Ztrust-policy=certify
//@[vec_extend_bomb_list_certify] compile-flags: -Ztrust-policy=certify
//@[vec_extend_into_alloc_bomb_vec_certify] compile-flags: -Ztrust-policy=certify
//@[btreeset_extend_enumerate_u128_certify] compile-flags: -Ztrust-policy=certify
//@[btreeset_extend_global_set_certify] compile-flags: -Ztrust-policy=certify
//@[btreeset_extend_clone_bomb_set] check-fail
//@[btreeset_extend_clone_bomb_set_certify] check-fail
//@[vec_extend_clone_bomb_set] check-fail
//@[hashset_collect_clone_bomb_set_iter] check-fail
//@[btreeset_collect_clone_bomb_set_iter] check-fail
//@[hashset_collect_clone_bomb_keys] check-fail
//@[vec_extend_clone_bomb_values] check-fail
//@[vec_extend_clone_bomb_map_ref_cost] check-fail
//@[btreeset_collect_bomb_keys] check-fail
//@[vec_extend_bomb_list] check-fail
//@[vec_extend_bomb_list_certify] check-fail
//@[btreeset_extend_bomb_list] check-fail
//@[hashset_collect_bomb_list_iter] check-fail
//@[vec_extend_bomb_vec] check-fail
//@[vec_extend_into_alloc_bomb_vec] check-fail
//@[vec_extend_into_alloc_bomb_vec_certify] check-fail
//@[btreeset_extend_into_clone_bomb_set] check-fail
//@[btreeset_extend_enumerate_u128] check-pass
//@[btreeset_extend_enumerate_u128_certify] check-fail
//@[btreemap_extend_enumerate_inclusive_u64] check-pass
//@[btreeset_extend_enumerate_repeat] check-pass
//@[btreeset_extend_enumerate_chain_ranges] check-pass
//@[btreeset_extend_enumerate_skip_u128] check-pass
//@[btreeset_extend_global_set] check-pass
//@[btreeset_extend_global_set_certify] check-pass
//@[hashset_collect_global_list_iter] check-fail
//@[btreeset_collect_global_keys] check-fail
//@[btreeset_extend_enumerate_u32] check-pass
//@[btreeset_extend_enumerate_usize] check-pass
//@[btreeset_extend_enumerate_take_repeat] check-pass
//@[hashset_collect_enumerate_chain_slices] check-fail
//@[vec_extend_enumerate_slice] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! SP-2 review: code the keyed-collect / collection-extend TOTAL sentinel still
//! erased after `into_iter_source_runs_only_verified_code` landed. The sentinel
//! rewrites the call to `__trust_total_clone`, which the bridge models as total with
//! no callback, so whatever the std `from_iter`/`extend` runs — pulling items from
//! the SOURCE, and reserving or inserting in the RECEIVER — must be std's own code or
//! verified as its own root.
//!
//! (1) THE SOURCE'S ALLOCATOR. The closed list admitted a std collection by value and
//! its owning iterators without asking for the allocator type argument `A`, but
//! `btree::map::IntoIter::next` calls `dying_next`, which calls `self.alloc.clone()`
//! on every item (library/alloc/src/collections/btree/map.rs `dying_next`), and
//! `linked_list::IntoIter::next` is `pop_front`, which frees the node through
//! `A::deallocate`. BEFORE (stage 1 of `1181cb2edb3`, compiled as compiletest does):
//! every `clone_bomb` and `bomb` shape below built exit 0 with no Verification
//! Report on the default policy, and the `_certify` ones under certify. A certify
//! rlib holding the `btreeset_extend_clone_bomb_set`, `vec_extend_bomb_list` and
//! `hashset_collect_clone_bomb_keys` functions, linked into a verify-off `main` that
//! arms the auxiliary's allocators, panicked in `CloneBomb::clone` (inside
//! `dying_next` < `IntoIter::next` < `BTreeSet::extend`, and < `IntoKeys::next` <
//! `HashSet::from_iter`) and in `DeallocBomb::deallocate` (inside `pop_front` <
//! `linked_list::IntoIter::next` < `Vec::extend`), exit 101. `vec_extend_bomb_vec`
//! reaches its allocator when `Vec::extend` drops the drained `IntoIter`, a drop
//! rather than a call inside `next`; the rule refuses it too, because it asks every
//! allocator position.
//!
//! (1') THE RECEIVER'S ALLOCATOR (predates SP-2; found reproducing (1)). An `extend`
//! receiver's own allocator runs inside the call too: `Vec<T, A>::extend` reserves
//! through `A::allocate`, `BTreeSet<T, A>::extend` clones `A` for each vacant entry
//! (`BTreeMap::entry`). BEFORE: both receiver shapes below built exit 0 with no
//! Verification Report (the `Vec` one under certify too), and a certify rlib holding
//! them panicked in `AllocBomb::allocate` (< `RawVecInner::finish_grow` <
//! `Vec::reserve` < `Vec::extend`) and in `CloneBomb::clone` (< `BTreeMap::entry` <
//! `BTreeSet::extend`), exit 101.
//!
//! (2) `Enumerate`'s COUNTER. `Enumerate::next`/`fold` run `count += 1` under
//! `#[rustc_inherit_overflow_checks]`, the reason the same list refuses `RangeFrom`;
//! DC-1 (`b79833747f5`) made `Enumerate` total elsewhere only over an inner of at
//! most `usize::MAX` items, and the `BTreeMap`/`BTreeSet` `extend` arm has no count
//! gate. BEFORE: the `enumerate` shapes below built exit 0 with no Verification
//! Report (and the `_certify` one under certify), while DC-1's own spelling,
//! `it.next()` on `&mut Enumerate<Range<u128>>`, is refused under certify. Reaching
//! the overflow needs `2^64` items on a 64-bit target, so there is no run witness.
//!
//! AFTER: the predicate asks every allocator position of every listed std type for a
//! sysroot allocator (`audited_container_allocators_are_sysroot`, the drop stamp's
//! rule), the `extend` gate asks it of the receiver, and `Enumerate` is admitted only
//! over an inner that yields at most `usize::MAX` items (`source_len_fits_usize`).
//! Each shape keeps its real callee and is charged: the allocator shapes are refused
//! on the default policy and under certify; the `Enumerate` shapes, like DC-1's, keep
//! one runtime-checked row (the `WARN` annotations: before, there was no report at
//! all) that the default policy reports and certify refuses. The controls without an
//! annotation (the same collections at `Global`, `Enumerate` over
//! `Range<u32>`/`Range<usize>`, `Take<Repeat<_>>`, a chain of two slices, a slice)
//! stay accepted with no report.
//!
//! Ordinary Rust programs: the auxiliary is a plain verify-off dependency
//! (`auxiliary/source_allocator_unverified_dep.rs`); this crate names the
//! allocator-carrying types only through its aliases, so it needs no feature gate.
//!
//! RE-PINNED 2026-10-15 (the merge of 2026-10-14; DECISION_QUEUE D103): `btreeset_collect_global_keys`, `hashset_collect_enumerate_chain_slices`, `hashset_collect_global_list_iter`, `vec_extend_enumerate_slice`
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

extern crate source_allocator_unverified_dep as dep;

use std::collections::{btree_map, linked_list, BTreeMap, BTreeSet, HashSet};
use std::iter::{Chain, Copied, Enumerate, Repeat, Skip, Take};
use std::ops::{Range, RangeInclusive};
use std::slice::Iter;

// ---- (1) the source's allocator: `clone` inside `dying_next` ----

#[cfg(any(btreeset_extend_clone_bomb_set, btreeset_extend_clone_bomb_set_certify))]
pub fn f(s: &mut BTreeSet<u32>, src: dep::CloneBombSet) {
    //[btreeset_extend_clone_bomb_set,btreeset_extend_clone_bomb_set_certify]~^ ERROR Trust strict verification failed for `collect_extend_source_allocator_and_counter::f`
    s.extend(src)
}

#[cfg(vec_extend_clone_bomb_set)]
pub fn f(v: &mut Vec<u32>, src: dep::CloneBombSet) {
    //[vec_extend_clone_bomb_set]~^ ERROR Trust strict verification failed for `collect_extend_source_allocator_and_counter::f`
    v.extend(src)
}

#[cfg(hashset_collect_clone_bomb_set_iter)]
pub fn f(it: dep::CloneBombSetIter) -> HashSet<u32> {
    //[hashset_collect_clone_bomb_set_iter]~^ ERROR Trust strict verification failed for `collect_extend_source_allocator_and_counter::f`
    it.collect()
}

#[cfg(btreeset_collect_clone_bomb_set_iter)]
pub fn f(it: dep::CloneBombSetIter) -> BTreeSet<u32> {
    //[btreeset_collect_clone_bomb_set_iter]~^ ERROR Trust strict verification failed for `collect_extend_source_allocator_and_counter::f`
    it.collect()
}

#[cfg(hashset_collect_clone_bomb_keys)]
pub fn f(it: dep::CloneBombKeys) -> HashSet<u32> {
    //[hashset_collect_clone_bomb_keys]~^ ERROR Trust strict verification failed for `collect_extend_source_allocator_and_counter::f`
    it.collect()
}

#[cfg(vec_extend_clone_bomb_values)]
pub fn f(v: &mut Vec<u32>, it: dep::CloneBombValues) {
    //[vec_extend_clone_bomb_values]~^ ERROR Trust strict verification failed for `collect_extend_source_allocator_and_counter::f`
    v.extend(it)
}

/// Capability cost (docs/DECISION_QUEUE.md SP-2): a BORROWED `&BTreeMap<_, _, A>`
/// iterates through `btree_map::Iter`, which never touches `A`, but the rule asks
/// every allocator position of a listed type, owned or borrowed, so this `extend`
/// keeps its real callee too.
#[cfg(vec_extend_clone_bomb_map_ref_cost)]
pub fn f<'a>(v: &mut Vec<(&'a u32, &'a u32)>, m: &'a dep::CloneBombMap) {
    //[vec_extend_clone_bomb_map_ref_cost]~^ ERROR Trust strict verification failed for `collect_extend_source_allocator_and_counter::f`
    v.extend(m)
}

// ---- (1) the source's allocator: `deallocate` inside `next` ----

#[cfg(btreeset_collect_bomb_keys)]
pub fn f(it: dep::BombKeys) -> BTreeSet<u32> {
    //[btreeset_collect_bomb_keys]~^ ERROR Trust strict verification failed for `collect_extend_source_allocator_and_counter::f`
    it.collect()
}

#[cfg(any(vec_extend_bomb_list, vec_extend_bomb_list_certify))]
pub fn f(v: &mut Vec<u32>, l: dep::BombList) {
    //[vec_extend_bomb_list,vec_extend_bomb_list_certify]~^ ERROR Trust strict verification failed for `collect_extend_source_allocator_and_counter::f`
    v.extend(l)
}

#[cfg(btreeset_extend_bomb_list)]
pub fn f(s: &mut BTreeSet<u32>, l: dep::BombList) {
    //[btreeset_extend_bomb_list]~^ ERROR Trust strict verification failed for `collect_extend_source_allocator_and_counter::f`
    s.extend(l)
}

#[cfg(hashset_collect_bomb_list_iter)]
pub fn f(it: dep::BombListIter) -> HashSet<u32> {
    //[hashset_collect_bomb_list_iter]~^ ERROR Trust strict verification failed for `collect_extend_source_allocator_and_counter::f`
    it.collect()
}

/// The drained `vec::IntoIter` is dropped inside `Vec::extend`, freeing the buffer
/// through `A::deallocate`: a drop, refused because the rule asks every allocator
/// position.
#[cfg(vec_extend_bomb_vec)]
pub fn f(v: &mut Vec<u32>, src: dep::BombVec) {
    //[vec_extend_bomb_vec]~^ ERROR Trust strict verification failed for `collect_extend_source_allocator_and_counter::f`
    v.extend(src)
}

// ---- (1') the RECEIVER's allocator: `extend` reserves through it, inserts clone it ----

#[cfg(any(vec_extend_into_alloc_bomb_vec, vec_extend_into_alloc_bomb_vec_certify))]
pub fn f(v: &mut dep::AllocBombVec, w: &[u32]) {
    //[vec_extend_into_alloc_bomb_vec,vec_extend_into_alloc_bomb_vec_certify]~^ ERROR Trust strict verification failed for `collect_extend_source_allocator_and_counter::f`
    v.extend(w.iter().copied())
}

#[cfg(btreeset_extend_into_clone_bomb_set)]
pub fn f(s: &mut dep::CloneBombSet, w: &[u32]) {
    //[btreeset_extend_into_clone_bomb_set]~^ ERROR Trust strict verification failed for `collect_extend_source_allocator_and_counter::f`
    s.extend(w.iter().copied())
}

// ---- (2) `Enumerate` over an inner longer than `usize::MAX` ----

#[cfg(any(btreeset_extend_enumerate_u128, btreeset_extend_enumerate_u128_certify))]
pub fn f(v: &mut BTreeSet<(usize, u128)>, it: Enumerate<Range<u128>>) {
    //[btreeset_extend_enumerate_u128_certify]~^ ERROR Trust strict verification failed for `collect_extend_source_allocator_and_counter::f`
    //[btreeset_extend_enumerate_u128]~^^ WARN Trust verification advisory for `collect_extend_source_allocator_and_counter::f`
    v.extend(it)
}

/// `RangeInclusive<u64>` yields `2^64` items: one more than a 64-bit `usize` counts.
#[cfg(btreemap_extend_enumerate_inclusive_u64)]
pub fn f(m: &mut BTreeMap<usize, u64>, it: Enumerate<RangeInclusive<u64>>) {
    //[btreemap_extend_enumerate_inclusive_u64]~^ WARN Trust verification advisory for `collect_extend_source_allocator_and_counter::f`
    m.extend(it)
}

#[cfg(btreeset_extend_enumerate_repeat)]
pub fn f(v: &mut BTreeSet<(usize, u8)>, it: Enumerate<Repeat<u8>>) {
    //[btreeset_extend_enumerate_repeat]~^ WARN Trust verification advisory for `collect_extend_source_allocator_and_counter::f`
    v.extend(it)
}

#[cfg(btreeset_extend_enumerate_chain_ranges)]
pub fn f(v: &mut BTreeSet<(usize, u64)>, it: Enumerate<Chain<Range<u64>, Range<u64>>>) {
    //[btreeset_extend_enumerate_chain_ranges]~^ WARN Trust verification advisory for `collect_extend_source_allocator_and_counter::f`
    v.extend(it)
}

/// DC-1's lead shape, under `Skip` (whose `next` calls the inner `nth`).
#[cfg(btreeset_extend_enumerate_skip_u128)]
pub fn f(v: &mut BTreeSet<(usize, u128)>, it: Skip<Enumerate<Range<u128>>>) {
    //[btreeset_extend_enumerate_skip_u128]~^ WARN Trust verification advisory for `collect_extend_source_allocator_and_counter::f`
    v.extend(it)
}

// ---- controls that stay accepted ----

#[cfg(any(btreeset_extend_global_set, btreeset_extend_global_set_certify))]
pub fn f(s: &mut BTreeSet<u32>, src: BTreeSet<u32>) {
    s.extend(src)
}

#[cfg(hashset_collect_global_list_iter)]
pub fn f(it: linked_list::IntoIter<u32>) -> HashSet<u32> {
    it.collect()
}

#[cfg(btreeset_collect_global_keys)]
pub fn f(it: btree_map::IntoKeys<u32, u8>) -> BTreeSet<u32> {
    it.collect()
}

#[cfg(btreeset_extend_enumerate_u32)]
pub fn f(v: &mut BTreeSet<(usize, u32)>, it: Enumerate<Range<u32>>) {
    v.extend(it)
}

#[cfg(btreeset_extend_enumerate_usize)]
pub fn f(v: &mut BTreeSet<(usize, usize)>, it: Enumerate<Range<usize>>) {
    v.extend(it)
}

#[cfg(btreeset_extend_enumerate_take_repeat)]
pub fn f(v: &mut BTreeSet<(usize, u8)>, it: Enumerate<Take<Repeat<u8>>>) {
    v.extend(it)
}

/// A chain sums its sides, so no structural arm admits it; the live-memory count
/// does (`2^56` items per side, far below a 64-bit `usize::MAX`).
#[cfg(hashset_collect_enumerate_chain_slices)]
pub fn f(it: Enumerate<Chain<Copied<Iter<'_, u32>>, Copied<Iter<'_, u32>>>>) -> HashSet<(usize, u32)> {
    it.collect()
}

#[cfg(vec_extend_enumerate_slice)]
pub fn f(v: &mut Vec<(usize, u32)>, it: Enumerate<Copied<Iter<'_, u32>>>) {
    v.extend(it)
}
