//@ revisions: hashset_collect_fnptr vec_extend_fnptr hashset_collect_fnptr_certify
//@ revisions: vec_extend_fnptr_certify btreeset_collect_fnptr hashset_extend_fnptr
//@ revisions: string_extend_fnptr filter_fnptr filter_map_fnptr inspect_fnptr scan_fnptr
//@ revisions: take_while_fnptr skip_while_fnptr map_while_fnptr chain_fnptr zip_fnptr
//@ revisions: rev_fnptr peekable_fnptr fuse_fnptr take_fnptr ref_mut_fnptr cloned_dep_clone
//@ revisions: btree_difference_dep_ord btree_intersection_dep_ord btree_union_dep_ord
//@ revisions: hash_difference_dep_hash split_fnptr matches_fnptr btreeset_extend_fnptr
//@ revisions: btreemap_extend_fnptr btreeset_extend_dep_iter btreeset_extend_dep_iter_certify
//@ revisions: btreemap_extend_dep_iter local_closure_panics requires_local
//@ revisions: plain_collect plain_collect_certify plain_extend local_closure local_closure_ref
//@ revisions: local_fnitem ctor_local ctor_some split_char split_str cloned_u32 cloned_string
//@ revisions: btreeset_extend_range btreeset_extend_once btreeset_extend_repeat_take
//@ revisions: btree_difference_u32_cost zip_range_from_cost
//@ revisions: btreeset_extend_local_closure btreemap_extend_local_closure btreeset_extend_local_fnitem
//@ revisions: btreeset_extend_ref_mut_fnptr
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: source_callback_unverified_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[hashset_collect_fnptr_certify] compile-flags: -Ztrust-policy=certify
//@[vec_extend_fnptr_certify] compile-flags: -Ztrust-policy=certify
//@[btreeset_extend_dep_iter_certify] compile-flags: -Ztrust-policy=certify
//@[plain_collect_certify] compile-flags: -Ztrust-policy=certify
//@[hashset_collect_fnptr] check-fail
//@[vec_extend_fnptr] check-fail
//@[hashset_collect_fnptr_certify] check-fail
//@[vec_extend_fnptr_certify] check-fail
//@[btreeset_collect_fnptr] check-fail
//@[hashset_extend_fnptr] check-fail
//@[string_extend_fnptr] check-fail
//@[filter_fnptr] check-fail
//@[filter_map_fnptr] check-fail
//@[inspect_fnptr] check-fail
//@[scan_fnptr] check-fail
//@[take_while_fnptr] check-fail
//@[skip_while_fnptr] check-fail
//@[map_while_fnptr] check-fail
//@[chain_fnptr] check-fail
//@[zip_fnptr] check-fail
//@[rev_fnptr] check-fail
//@[peekable_fnptr] check-fail
//@[fuse_fnptr] check-fail
//@[take_fnptr] check-fail
//@[ref_mut_fnptr] check-fail
//@[cloned_dep_clone] check-fail
//@[btree_difference_dep_ord] check-fail
//@[btree_intersection_dep_ord] check-fail
//@[btree_union_dep_ord] check-fail
//@[hash_difference_dep_hash] check-fail
//@[split_fnptr] check-fail
//@[matches_fnptr] check-fail
//@[btreeset_extend_fnptr] check-fail
//@[btreemap_extend_fnptr] check-fail
//@[btreeset_extend_ref_mut_fnptr] check-fail
//@[btreeset_extend_dep_iter] check-fail
//@[btreeset_extend_dep_iter_certify] check-fail
//@[btreemap_extend_dep_iter] check-fail
//@[local_closure_panics] check-fail
//@[requires_local] check-fail
//@[btree_difference_u32_cost] check-fail
//@[zip_range_from_cost] check-fail
//@[plain_collect] check-fail
//@[plain_collect_certify] check-fail
//@[plain_extend] check-pass
//@[local_closure] check-pass
//@[local_closure_ref] check-pass
//@[local_fnitem] check-pass
//@[ctor_local] check-pass
//@[ctor_some] check-fail
//@[split_char] check-pass
//@[split_str] check-pass
//@[cloned_u32] check-pass
//@[cloned_string] check-pass
//@[btreeset_extend_range] check-pass
//@[btreeset_extend_once] check-pass
//@[btreeset_extend_repeat_take] check-pass
//@[btreeset_extend_local_closure] check-pass
//@[btreemap_extend_local_closure] check-pass
//@[btreeset_extend_local_fnitem] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! SP-2: the keyed-collect / collection-extend TOTAL sentinel credited code that
//! runs INSIDE the call it erases. `trust-mir-extract` rewrites a `collect` into a
//! std keyed collection and an `extend` of a std collection to
//! `__trust_total_clone`, which the bridge models as a total call with no callback.
//! But `from_iter`/`extend` drive the SOURCE iterator, and the source can run code:
//! a `Map`'s callback, a `Filter`'s predicate, `Cloned`'s `T::clone`, a `str`
//! pattern, a set operation's `Ord`/`Hash`, a dependency iterator's `next`. The gates
//! asked the source only for a bounded COUNT (an adapter's iterator argument, never
//! its callback), and the `BTreeMap`/`BTreeSet` `extend` arm asked nothing of it.
//!
//! BEFORE (stage 1 `3fbce29e3`; the same functions compiled as compiletest does):
//! every shape revision — the `check-fail` ones listed before `local_closure_panics` —
//! built exit 0 with no Verification Report and zero rows on the default policy, and
//! so did the lead's two under certify (`btreeset_extend_dep_iter_certify` was
//! measured exit 0 only on the mutation build: the fix with its conjuncts made vacuous).
//! A certify rlib holding the lead's two functions, linked into a verify-off `main`
//! handed `w.iter().copied().map(p as fn(u32) -> u32)` with `p` panicking at 7,
//! panicked inside `HashSet::from_iter` and `Vec::extend` (exit 101, the SP-2 triage's
//! witness); so did certify rlibs holding the `cloned_dep_clone`,
//! `btree_difference_dep_ord`, `hash_difference_dep_hash`, `split_fnptr`,
//! `matches_fnptr` and `chain_fnptr` shapes, each panicking in the dependency's
//! `clone`/`cmp`/`hash` or in the fn-pointer callback.
//!
//! AFTER: `into_iter_source_runs_only_verified_code` licenses the rewrite only when
//! every piece of the source is std's own code or verified as its own root — a LOCAL
//! closure or LOCAL function item, or a constructor — so each such call keeps its
//! real callee and is charged. The controls pin what must not move:
//! `local_closure_panics` (a local closure is its own verification root, refused
//! there) and `requires_local` (a local item owing a `requires` is refused by the
//! callable type-argument gate, whatever the extractor does) stay refused; the
//! `check-pass` revisions — sources with no callback, local closures and items,
//! constructors, `char`/`&str` patterns, `cloned()` over total-`Clone` elements, and
//! `BTreeSet::extend` from `0..n`, `once(..)` and `repeat(..).take(n)` — stay accepted
//! (the last two with the runtime-checked row of their own constructor call). The two
//! `_cost` revisions pin what the closed list gives up (docs/DECISION_QUEUE.md SP-2): a
//! set operation's iterator, even over `u32`, and a `zip(0..)` (`RangeFrom::next` is an
//! add under the caller's overflow checks) were accepted on the default policy BEFORE,
//! with one runtime-checked row, and now keep the real `collect`/`extend`, refused there.
//!
//! CALL-REACH-1 D6 (2026-10-13, docs/DECISION_QUEUE.md CALL-REACH-1-D6): a call that
//! hands its sysroot instance a `fn` pointer type no longer takes D2's leaf at a call
//! through a pointer, so the call walk OPENS it and the bridge withdraws the callee
//! into a counted fail-closed absent-callee row. That is what now refuses
//! `{btreeset,btreemap}_extend_fnptr` (accepted on main `825437bfeb` with one
//! runtime-checked row). `hashset_collect_fnptr{,_certify}` and `matches_fnptr` were
//! refused there by the uncounted `native-verification-gap` row ("a closure-driving
//! consumer call runs code outside the verified closure"), which is minted only when
//! no counted obligation charges the call; the withdrawn row now charges it, so they
//! are refused by the strict and Level 0 errors instead: still refused under both
//! policies.
//!
//! Ordinary Rust programs: the auxiliary is a plain verify-off dependency
//! (`auxiliary/source_callback_unverified_dep.rs`).
//!
//! RE-PINNED 2026-10-15 (the merge of 2026-10-14; DECISION_QUEUE D103): `ctor_some`, `plain_collect`, `plain_collect_certify`
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

extern crate source_callback_unverified_dep as dep;

use std::collections::{btree_set, hash_set, BTreeMap, BTreeSet, HashSet};
use std::iter::{
    Chain, Cloned, Copied, Filter, FilterMap, Fuse, Inspect, Map, MapWhile, Peekable, Rev, Scan,
    SkipWhile, Take, TakeWhile, Zip,
};
use std::slice::Iter;

type Src<'a> = Copied<Iter<'a, u32>>;
type M<'a> = Map<Src<'a>, fn(u32) -> u32>;

// ---- the lead: a fn pointer handed in from outside, inside the source ----

#[cfg(any(hashset_collect_fnptr, hashset_collect_fnptr_certify))]
pub fn f(it: M<'_>) -> HashSet<u32> {
    //[hashset_collect_fnptr,hashset_collect_fnptr_certify]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    //[hashset_collect_fnptr,hashset_collect_fnptr_certify]~| ERROR Trust Level 0 safety verification incomplete for `collect_extend_source_runs_unverified_code::f`
    it.collect()
}

#[cfg(any(vec_extend_fnptr, vec_extend_fnptr_certify))]
pub fn f(v: &mut Vec<u32>, it: M<'_>) {
    //[vec_extend_fnptr,vec_extend_fnptr_certify]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    v.extend(it)
}

// ---- the same callback behind other destinations and adapters ----

#[cfg(btreeset_collect_fnptr)]
pub fn f(it: M<'_>) -> BTreeSet<u32> {
    //[btreeset_collect_fnptr]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    it.collect()
}

#[cfg(hashset_extend_fnptr)]
pub fn f(s: &mut HashSet<u32>, it: M<'_>) {
    //[hashset_extend_fnptr]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    s.extend(it)
}

#[cfg(string_extend_fnptr)]
pub fn f(s: &mut String, it: Map<Copied<Iter<'_, char>>, fn(char) -> char>) {
    //[string_extend_fnptr]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    s.extend(it)
}

#[cfg(filter_fnptr)]
pub fn f(v: &mut Vec<u32>, it: Filter<Src<'_>, fn(&u32) -> bool>) {
    //[filter_fnptr]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    v.extend(it)
}

#[cfg(filter_map_fnptr)]
pub fn f(v: &mut Vec<u32>, it: FilterMap<Src<'_>, fn(u32) -> Option<u32>>) {
    //[filter_map_fnptr]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    v.extend(it)
}

#[cfg(inspect_fnptr)]
pub fn f(v: &mut Vec<u32>, it: Inspect<Src<'_>, fn(&u32)>) {
    //[inspect_fnptr]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    v.extend(it)
}

#[cfg(scan_fnptr)]
pub fn f(v: &mut Vec<u32>, it: Scan<Src<'_>, u32, fn(&mut u32, u32) -> Option<u32>>) {
    //[scan_fnptr]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    v.extend(it)
}

#[cfg(take_while_fnptr)]
pub fn f(v: &mut Vec<u32>, it: TakeWhile<Src<'_>, fn(&u32) -> bool>) {
    //[take_while_fnptr]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    v.extend(it)
}

#[cfg(skip_while_fnptr)]
pub fn f(v: &mut Vec<u32>, it: SkipWhile<Src<'_>, fn(&u32) -> bool>) {
    //[skip_while_fnptr]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    v.extend(it)
}

#[cfg(map_while_fnptr)]
pub fn f(v: &mut Vec<u32>, it: MapWhile<Src<'_>, fn(u32) -> Option<u32>>) {
    //[map_while_fnptr]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    v.extend(it)
}

#[cfg(chain_fnptr)]
pub fn f(v: &mut Vec<u32>, it: Chain<Src<'_>, M<'_>>) {
    //[chain_fnptr]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    v.extend(it)
}

#[cfg(zip_fnptr)]
pub fn f(v: &mut Vec<(u32, u32)>, it: Zip<Src<'_>, M<'_>>) {
    //[zip_fnptr]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    v.extend(it)
}

#[cfg(rev_fnptr)]
pub fn f(v: &mut Vec<u32>, it: Rev<M<'_>>) {
    //[rev_fnptr]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    v.extend(it)
}

#[cfg(peekable_fnptr)]
pub fn f(v: &mut Vec<u32>, it: Peekable<M<'_>>) {
    //[peekable_fnptr]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    v.extend(it)
}

#[cfg(fuse_fnptr)]
pub fn f(it: Fuse<M<'_>>) -> BTreeSet<u32> {
    //[fuse_fnptr]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    it.collect()
}

#[cfg(take_fnptr)]
pub fn f(v: &mut Vec<u32>, it: Take<M<'_>>) {
    //[take_fnptr]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    v.extend(it)
}

#[cfg(ref_mut_fnptr)]
pub fn f(v: &mut Vec<u32>, it: &mut M<'_>) {
    //[ref_mut_fnptr]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    v.extend(it)
}

// ---- other code the source runs: a dependency's `Clone`, `Ord`, `Hash`, `next` ----

#[cfg(cloned_dep_clone)]
pub fn f(v: &mut Vec<dep::K>, it: Cloned<Iter<'_, dep::K>>) {
    //[cloned_dep_clone]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    v.extend(it)
}

#[cfg(btree_difference_dep_ord)]
pub fn f<'a>(v: &mut Vec<&'a dep::O>, it: btree_set::Difference<'a, dep::O>) {
    //[btree_difference_dep_ord]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    v.extend(it)
}

#[cfg(btree_intersection_dep_ord)]
pub fn f<'a>(v: &mut Vec<&'a dep::O>, it: btree_set::Intersection<'a, dep::O>) {
    //[btree_intersection_dep_ord]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    v.extend(it)
}

#[cfg(btree_union_dep_ord)]
pub fn f<'a>(v: &mut Vec<&'a dep::O>, it: btree_set::Union<'a, dep::O>) {
    //[btree_union_dep_ord]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    v.extend(it)
}

#[cfg(hash_difference_dep_hash)]
type HDiff<'a> = hash_set::Difference<'a, dep::H, std::hash::RandomState>;
#[cfg(hash_difference_dep_hash)]
pub fn f<'a>(v: &mut Vec<&'a dep::H>, it: HDiff<'a>) {
    //[hash_difference_dep_hash]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    v.extend(it)
}

#[cfg(split_fnptr)]
pub fn f<'a>(v: &mut Vec<&'a str>, it: std::str::Split<'a, fn(char) -> bool>) {
    //[split_fnptr]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    v.extend(it)
}

#[cfg(matches_fnptr)]
pub fn f<'a>(it: std::str::Matches<'a, fn(char) -> bool>) -> HashSet<&'a str> {
    //[matches_fnptr]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    //[matches_fnptr]~| ERROR Trust Level 0 safety verification incomplete for `collect_extend_source_runs_unverified_code::f`
    it.collect()
}

// ---- `BTreeMap`/`BTreeSet` `extend`: its arm asked nothing of the source ----

#[cfg(btreeset_extend_fnptr)]
pub fn f(s: &mut BTreeSet<u32>, it: M<'_>) {
    //[btreeset_extend_fnptr]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    s.extend(it)
}

#[cfg(btreemap_extend_fnptr)]
pub fn f(m: &mut BTreeMap<u32, u32>, it: Map<Src<'_>, fn(u32) -> (u32, u32)>) {
    //[btreemap_extend_fnptr]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    m.extend(it)
}

// CALL-REACH-1 D6 review (2026-10-13): the handed iterator behind a `&mut`, so the
// pointer type reaches `extend` only through `&mut I: Iterator`. Accepted on main
// `825437bfeb` (exit 0, one runtime-checked row); refused by D6.
#[cfg(btreeset_extend_ref_mut_fnptr)]
pub fn f(s: &mut BTreeSet<u32>, it: &mut Map<std::ops::Range<u32>, fn(u32) -> u32>) {
    //[btreeset_extend_ref_mut_fnptr]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    s.extend(it)
}

#[cfg(any(btreeset_extend_dep_iter, btreeset_extend_dep_iter_certify))]
pub fn f(s: &mut BTreeSet<u32>, it: dep::Countdown) {
    //[btreeset_extend_dep_iter,btreeset_extend_dep_iter_certify]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    s.extend(it)
}

#[cfg(btreemap_extend_dep_iter)]
pub fn f(m: &mut BTreeMap<u32, ()>, it: Zip<dep::Countdown, std::iter::Repeat<()>>) {
    //[btreemap_extend_dep_iter]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    m.extend(it)
}

// ---- controls that stay refused, by the gates the carve-outs rely on ----

/// A local closure is its own verification root: refused there.
#[cfg(local_closure_panics)]
pub fn f(v: &mut Vec<u32>, w: &[u32]) {
    v.extend(w.iter().copied().map(|x| x / (x - 1)))
    //[local_closure_panics]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f::{closure#0}`
}

/// A local item owing a `requires`, handed to `map`: the callable type-argument
/// gate refuses the hand-over on the rustc MIR, sentinel or not.
#[cfg(requires_local)]
fn add1(x: u32) -> u32
    requires x < 100
{
    x + 1
}
#[cfg(requires_local)]
pub fn f(w: &[u32]) -> HashSet<u32> {
    //[requires_local]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    //[requires_local]~| NOTE `add1` carries a `requires` its callers owe
    w.iter().copied().map(add1).collect()
}

// ---- controls that stay accepted ----

#[cfg(any(plain_collect, plain_collect_certify))]
pub fn f(it: Src<'_>) -> HashSet<u32> {
    it.collect()
}

#[cfg(plain_extend)]
pub fn f(v: &mut Vec<u32>, it: Src<'_>) {
    v.extend(it)
}

#[cfg(local_closure)]
pub fn f(v: &mut Vec<u32>, w: &[u32]) {
    v.extend(w.iter().copied().map(|x| x.wrapping_add(1)))
}

#[cfg(local_closure_ref)]
pub fn f(v: &mut Vec<u32>, w: &[u32]) {
    let mut c = |x: u32| x.wrapping_add(1);
    v.extend(w.iter().copied().map(&mut c))
}

#[cfg(local_fnitem)]
fn inc(x: u32) -> u32 {
    x.wrapping_add(1)
}
#[cfg(local_fnitem)]
pub fn f(v: &mut Vec<u32>, w: &[u32]) {
    v.extend(w.iter().copied().map(inc))
}

#[cfg(ctor_local)]
pub struct W(pub u32);
#[cfg(ctor_local)]
pub fn f(v: &mut Vec<W>, w: &[u32]) {
    v.extend(w.iter().copied().map(W))
}

#[cfg(ctor_some)]
pub fn f(v: &mut Vec<Option<u32>>, w: &[u32]) {
    v.extend(w.iter().copied().map(Some))
}

#[cfg(split_char)]
pub fn f<'a>(v: &mut Vec<&'a str>, s: &'a str) {
    v.extend(s.split(','))
}

#[cfg(split_str)]
pub fn f<'a>(v: &mut Vec<&'a str>, s: &'a str) {
    v.extend(s.split("ab"))
}

#[cfg(cloned_u32)]
pub fn f(v: &mut Vec<u32>, w: &[u32]) {
    v.extend(w.iter().cloned())
}

#[cfg(cloned_string)]
pub fn f(v: &mut Vec<String>, w: &[String]) {
    v.extend(w.iter().cloned())
}

#[cfg(btreeset_extend_range)]
pub fn f(s: &mut BTreeSet<u64>, n: u64) {
    s.extend(0..n)
}

#[cfg(btreeset_extend_once)]
pub fn f(s: &mut BTreeSet<u64>) {
    s.extend(std::iter::once(3u64))
}

#[cfg(btreeset_extend_repeat_take)]
pub fn f(s: &mut BTreeSet<u64>, n: usize) {
    s.extend(std::iter::repeat(3u64).take(n))
}

// CALL-REACH-1 D6 (2026-10-13): the `{btreeset,btreemap}_extend_fnptr` refusals come
// from the call walk opening a pointer call while the call hands `extend` a `fn`
// pointer type. A closure's generic arguments carry its signature AS a `fn` pointer
// type, which names no pointer value; these pin that a local closure or fn item
// behind the same `BTreeSet`/`BTreeMap::extend` is not read as one (accepted on main
// `825437bfeb` before D6, exit 0 with no report).

#[cfg(btreeset_extend_local_closure)]
pub fn f(s: &mut BTreeSet<u32>, w: &[u32]) {
    s.extend(w.iter().copied().map(|x| x.wrapping_add(1)))
}

#[cfg(btreemap_extend_local_closure)]
pub fn f(m: &mut BTreeMap<u32, u32>, w: &[u32]) {
    m.extend(w.iter().copied().map(|x| (x, x)))
}

#[cfg(btreeset_extend_local_fnitem)]
fn inc(x: u32) -> u32 {
    x.wrapping_add(1)
}
#[cfg(btreeset_extend_local_fnitem)]
pub fn f(s: &mut BTreeSet<u32>, w: &[u32]) {
    s.extend(w.iter().copied().map(inc))
}

// ---- capability cost, pinned (docs/DECISION_QUEUE.md SP-2): no longer sentineled ----

/// A set operation runs the keys' `Ord`; the predicate lists none, even over a
/// total key, so `extend` keeps its real callee.
#[cfg(btree_difference_u32_cost)]
pub fn f<'a>(v: &mut Vec<&'a u32>, a: &'a BTreeSet<u32>, b: &'a BTreeSet<u32>) {
    //[btree_difference_u32_cost]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    v.extend(a.difference(b))
}

/// `RangeFrom::next` is `Step::forward`, an add under the caller's overflow checks.
#[cfg(zip_range_from_cost)]
pub fn f(w: &[u32]) -> HashSet<(u32, u32)> {
    //[zip_range_from_cost]~^ ERROR Trust strict verification failed for `collect_extend_source_runs_unverified_code::f`
    w.iter().copied().zip(0..).collect()
}
