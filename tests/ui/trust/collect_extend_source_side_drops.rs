//@ revisions: hash_map_hasher hash_map_hasher_certify hash_set_hasher hash_set_hasher_certify
//@ revisions: result_err result_err_certify take_remainder take_remainder_certify
//@ revisions: skip_discard skip_discard_certify filter_discard filter_discard_certify
//@ revisions: skip_ref_discard skip_ref_discard_certify
//@ revisions: stepby_ref_discard stepby_ref_discard_certify
//@ revisions: zip_remainder zip_remainder_certify chain_ref_take chain_ref_take_certify
//@ revisions: into_keys_discard into_keys_discard_certify scan_state scan_state_certify
//@ revisions: collect_into_keys collect_into_keys_certify
//@ revisions: collect_filter_capture collect_filter_capture_certify
//@ revisions: ref_take_cost controls controls_certify
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: source_side_drops_unverified_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[hash_map_hasher_certify] compile-flags: -Ztrust-policy=certify
//@[hash_set_hasher_certify] compile-flags: -Ztrust-policy=certify
//@[result_err_certify] compile-flags: -Ztrust-policy=certify
//@[take_remainder_certify] compile-flags: -Ztrust-policy=certify
//@[skip_discard_certify] compile-flags: -Ztrust-policy=certify
//@[filter_discard_certify] compile-flags: -Ztrust-policy=certify
//@[skip_ref_discard_certify] compile-flags: -Ztrust-policy=certify
//@[stepby_ref_discard_certify] compile-flags: -Ztrust-policy=certify
//@[zip_remainder_certify] compile-flags: -Ztrust-policy=certify
//@[chain_ref_take_certify] compile-flags: -Ztrust-policy=certify
//@[into_keys_discard_certify] compile-flags: -Ztrust-policy=certify
//@[scan_state_certify] compile-flags: -Ztrust-policy=certify
//@[collect_into_keys_certify] compile-flags: -Ztrust-policy=certify
//@[collect_filter_capture_certify] compile-flags: -Ztrust-policy=certify
//@[controls_certify] compile-flags: -Ztrust-policy=certify
//@[hash_map_hasher] check-fail
//@[hash_map_hasher_certify] check-fail
//@[hash_set_hasher] check-fail
//@[hash_set_hasher_certify] check-fail
//@[result_err] check-fail
//@[result_err_certify] check-fail
//@[take_remainder] check-fail
//@[take_remainder_certify] check-fail
//@[skip_discard] check-fail
//@[skip_discard_certify] check-fail
//@[filter_discard] check-fail
//@[filter_discard_certify] check-fail
//@[skip_ref_discard] check-fail
//@[skip_ref_discard_certify] check-fail
//@[stepby_ref_discard] check-fail
//@[stepby_ref_discard_certify] check-fail
//@[zip_remainder] check-fail
//@[zip_remainder_certify] check-fail
//@[chain_ref_take] check-fail
//@[chain_ref_take_certify] check-fail
//@[into_keys_discard] check-fail
//@[into_keys_discard_certify] check-fail
//@[scan_state] check-fail
//@[scan_state_certify] check-fail
//@[collect_into_keys] check-fail
//@[collect_into_keys_certify] check-fail
//@[collect_filter_capture] check-fail
//@[collect_filter_capture_certify] check-fail
//@[ref_take_cost] check-fail
//@[controls] check-fail
//@[controls_certify] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! SOURCE-SIDE-DROP-CERTIFY-1: the keyed-collect / collection-extend TOTAL sentinel
//! never asked the drops the call runs on the SOURCE side. `trust-mir-extract`
//! rewrites a `collect` into a std keyed collection and an `extend` of a std
//! collection to `__trust_total_clone`, which the bridge models as a total call,
//! once `into_iter_source_runs_only_verified_code` approves the source. That
//! predicate asked what CODE the source's iteration runs (SP-2), never what it
//! DROPS, and a drop is code too:
//!  * a by-value `HashMap`/`HashSet` drops its hasher `S` in `into_iter`
//!    (`hash_map_hasher`, `hash_set_hasher`; CALL-REACH-1's H6);
//!  * a by-value `Result` drops its `Err` payload: `Result::into_iter` is
//!    `self.ok()` (`result_err`);
//!  * `Take` leaves a remainder and the call drops it with the source
//!    (`take_remainder`), and so does `Zip` (`zip_remainder`);
//!  * `Skip`, `StepBy` and `Filter` drop the items they pass over (`skip_discard`,
//!    `filter_discard`), EVEN behind `&mut` (`skip_ref_discard`,
//!    `stepby_ref_discard`): the item is pulled through the borrow and dropped in
//!    the adapter;
//!  * a `Chain` drops its first half the moment it runs dry, so a `Take` under a
//!    BORROWED `Chain` still has its remainder dropped inside the call
//!    (`chain_ref_take`);
//!  * `IntoKeys` drops each value (`into_keys_discard`, `collect_into_keys`);
//!  * a `Scan` state and a callback's by-move capture are dropped with the
//!    adapter (`scan_state`, `collect_filter_capture`).
//! The dependency's `Drop` panics inside std's `extend`/`from_iter`; the run twin
//! `collect_extend_source_side_drops_run.rs` witnesses each of them.
//!
//! BEFORE (stage 1 `scratchpad/stage1-w25f`, tree of `a971311ee2`, each revision
//! compiled with its own flags as compiletest does, `--emit=metadata`): every
//! check-fail revision built exit 0, with no error and no unproved row, under the
//! default policy and under certify alike. `ref_take_cost` built exit 0 too.
//!
//! AFTER (predicted, not built in the lane): `source_side_drops_are_total`
//! (trust-mir-extract `convert.rs`), asked beside the SP-2 predicate by both
//! sentinel gates, answers `false` for each shape above, so each call keeps its real
//! `extend`/`collect` callee and is refused (the annotations). `controls` and
//! `controls_certify` stay accepted: a `RandomState` map, a `Result<u32, u32>`, a
//! whole `Vec<dep::Bomb>`, `Option<dep::Bomb>`, `[dep::Bomb; 2]`,
//! `BTreeMap<u32, dep::Bomb>` and `Chain` of two `vec::IntoIter<dep::Bomb>` drained
//! by value (nothing is left to drop), a borrowed `HashMap` at `dep::DropBuild` (a
//! borrow drops no hasher), `Take<vec::IntoIter<u32>>`, `&mut Skip<IntoIter<u32>>`,
//! `Take<slice::Iter<dep::Bomb>>` (it discards only references), a `u32` `Scan`
//! state and a `String` by-move capture.
//!
//! COST (docs/DECISION_QUEUE.md SOURCE-SIDE-DROP-CERTIFY-1, row SP-2-DROPS):
//! `ref_take_cost`, `v.extend(&mut take)` over a `Take<vec::IntoIter<dep::Bomb>>`,
//! drops nothing inside the call on today's std (the remainder stays in the
//! caller's iterator), but the predicate gives no lossy adapter a borrow carve-out
//! (`chain_ref_take` shows why), so it loses the sentinel too.
//!
//! Ordinary Rust programs: the auxiliary is a plain verify-off dependency
//! (`auxiliary/source_side_drops_unverified_dep.rs`).
//!
//! RE-PINNED 2026-10-15 (the merge of 2026-10-14; DECISION_QUEUE D103): `controls`, `controls_certify`
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

extern crate source_side_drops_unverified_dep as dep;

#[allow(unused_imports)]
use dep::{Bomb, DropBuild, ErrBomb};
#[allow(unused_imports)]
use std::collections::{btree_map, BTreeMap, HashMap, HashSet};
#[allow(unused_imports)]
use std::iter::{Chain, Scan, Skip, StepBy, Take, Zip};
#[allow(unused_imports)]
use std::ops::Range;
#[allow(unused_imports)]
use std::vec::IntoIter;

// ---- a by-value hash collection drops its hasher in `into_iter` ----

#[cfg(any(hash_map_hasher, hash_map_hasher_certify))]
pub fn f(v: &mut Vec<(u32, u8)>, m: HashMap<u32, u8, DropBuild>) {
    //[hash_map_hasher,hash_map_hasher_certify]~^ ERROR verification failed for `collect_extend_source_side_drops::f`
    v.extend(m)
}

#[cfg(any(hash_set_hasher, hash_set_hasher_certify))]
pub fn f(v: &mut Vec<u32>, s: HashSet<u32, DropBuild>) {
    //[hash_set_hasher,hash_set_hasher_certify]~^ ERROR verification failed for `collect_extend_source_side_drops::f`
    v.extend(s)
}

// ---- a by-value `Result` drops its `Err` payload (`into_iter` is `self.ok()`) ----

#[cfg(any(result_err, result_err_certify))]
pub fn f(v: &mut Vec<u32>, r: Result<u32, ErrBomb>) {
    //[result_err,result_err_certify]~^ ERROR verification failed for `collect_extend_source_side_drops::f`
    v.extend(r)
}

// ---- remainders and discards ----

#[cfg(any(take_remainder, take_remainder_certify))]
pub fn f(v: &mut Vec<Bomb>, src: Vec<Bomb>) {
    //[take_remainder,take_remainder_certify]~^ ERROR verification failed for `collect_extend_source_side_drops::f`
    v.extend(src.into_iter().take(1))
}

#[cfg(any(skip_discard, skip_discard_certify))]
pub fn f(v: &mut Vec<Bomb>, src: Vec<Bomb>) {
    //[skip_discard,skip_discard_certify]~^ ERROR verification failed for `collect_extend_source_side_drops::f`
    v.extend(src.into_iter().skip(1))
}

#[cfg(any(filter_discard, filter_discard_certify))]
pub fn f(v: &mut Vec<Bomb>, src: Vec<Bomb>) {
    //[filter_discard,filter_discard_certify]~^ ERROR verification failed for `collect_extend_source_side_drops::f`
    v.extend(src.into_iter().filter(|b| b.0 != 7))
}

#[cfg(any(skip_ref_discard, skip_ref_discard_certify))]
pub fn f(v: &mut Vec<Bomb>, it: &mut Skip<IntoIter<Bomb>>) {
    //[skip_ref_discard,skip_ref_discard_certify]~^ ERROR verification failed for `collect_extend_source_side_drops::f`
    v.extend(it)
}

#[cfg(any(stepby_ref_discard, stepby_ref_discard_certify))]
pub fn f(v: &mut Vec<Bomb>, it: &mut StepBy<IntoIter<Bomb>>) {
    //[stepby_ref_discard,stepby_ref_discard_certify]~^ ERROR verification failed for `collect_extend_source_side_drops::f`
    v.extend(it)
}

#[cfg(any(zip_remainder, zip_remainder_certify))]
pub fn f(v: &mut Vec<(Bomb, u32)>, it: Zip<IntoIter<Bomb>, Range<u32>>) {
    //[zip_remainder,zip_remainder_certify]~^ ERROR verification failed for `collect_extend_source_side_drops::f`
    v.extend(it)
}

#[cfg(any(chain_ref_take, chain_ref_take_certify))]
pub fn f(v: &mut Vec<Bomb>, it: &mut Chain<Take<IntoIter<Bomb>>, IntoIter<Bomb>>) {
    //[chain_ref_take,chain_ref_take_certify]~^ ERROR verification failed for `collect_extend_source_side_drops::f`
    v.extend(it)
}

#[cfg(any(into_keys_discard, into_keys_discard_certify))]
pub fn f(v: &mut Vec<u32>, it: btree_map::IntoKeys<u32, Bomb>) {
    //[into_keys_discard,into_keys_discard_certify]~^ ERROR verification failed for `collect_extend_source_side_drops::f`
    v.extend(it)
}

#[cfg(any(scan_state, scan_state_certify))]
pub fn f(v: &mut Vec<u32>, it: IntoIter<u32>, st: Bomb) {
    //[scan_state,scan_state_certify]~^ ERROR verification failed for `collect_extend_source_side_drops::f`
    v.extend(it.scan(st, |_, x| Some(x)))
}

// ---- the keyed-collect twins ----

#[cfg(any(collect_into_keys, collect_into_keys_certify))]
pub fn f(it: btree_map::IntoKeys<u32, Bomb>) -> HashSet<u32> {
    //[collect_into_keys,collect_into_keys_certify]~^ ERROR verification failed for `collect_extend_source_side_drops::f`
    it.collect()
}

#[cfg(any(collect_filter_capture, collect_filter_capture_certify))]
pub fn f(it: IntoIter<(u32, u8)>, cap: Bomb) -> HashMap<u32, u8> {
    //[collect_filter_capture,collect_filter_capture_certify]~^ ERROR verification failed for `collect_extend_source_side_drops::f`
    it.filter(move |p| {
        let _c = &cap;
        p.0 != 7
    })
    .collect()
}

// ---- cost: a borrowed `Take` gets no carve-out ----

#[cfg(ref_take_cost)]
pub fn f(v: &mut Vec<Bomb>, it: &mut Take<IntoIter<Bomb>>) {
    //[ref_take_cost]~^ ERROR verification failed for `collect_extend_source_side_drops::f`
    v.extend(it)
}

// ---- controls that stay accepted ----

#[cfg(any(controls, controls_certify))]
pub fn random_state_map(v: &mut Vec<(u32, u8)>, m: HashMap<u32, u8>) {
    v.extend(m)
}

#[cfg(any(controls, controls_certify))]
pub fn result_u32(v: &mut Vec<u32>, r: Result<u32, u32>) {
    v.extend(r)
}

#[cfg(any(controls, controls_certify))]
pub fn whole_vec_bomb(v: &mut Vec<Bomb>, src: Vec<Bomb>) {
    v.extend(src)
}

#[cfg(any(controls, controls_certify))]
pub fn option_bomb(v: &mut Vec<Bomb>, o: Option<Bomb>) {
    v.extend(o)
}

#[cfg(any(controls, controls_certify))]
pub fn array_bomb(v: &mut Vec<Bomb>, a: [Bomb; 2]) {
    v.extend(a)
}

#[cfg(any(controls, controls_certify))]
pub fn btreemap_bomb_values(v: &mut Vec<(u32, Bomb)>, m: BTreeMap<u32, Bomb>) {
    v.extend(m)
}

#[cfg(any(controls, controls_certify))]
pub fn chain_bomb(v: &mut Vec<Bomb>, it: Chain<IntoIter<Bomb>, IntoIter<Bomb>>) {
    v.extend(it)
}

#[cfg(any(controls, controls_certify))]
pub fn borrowed_drop_build_map<'a>(
    v: &mut Vec<(&'a u32, &'a u8)>,
    m: &'a HashMap<u32, u8, DropBuild>,
) {
    v.extend(m)
}

#[cfg(any(controls, controls_certify))]
pub fn take_u32(v: &mut Vec<u32>, src: Vec<u32>) {
    v.extend(src.into_iter().take(1))
}

#[cfg(any(controls, controls_certify))]
pub fn skip_ref_u32(v: &mut Vec<u32>, it: &mut Skip<IntoIter<u32>>) {
    v.extend(it)
}

#[cfg(any(controls, controls_certify))]
pub fn take_slice_bomb<'a>(v: &mut Vec<&'a Bomb>, w: &'a [Bomb]) {
    v.extend(w.iter().take(1))
}

#[cfg(any(controls, controls_certify))]
pub fn scan_u32_state(v: &mut Vec<u32>, it: IntoIter<u32>) {
    v.extend(it.scan(0u32, |s, x| {
        *s = x;
        Some(x)
    }))
}

#[cfg(any(controls, controls_certify))]
pub fn filter_string_capture(it: IntoIter<(u32, u8)>, cap: String) -> HashMap<u32, u8> {
    it.filter(move |p| cap.len() != usize::from(p.1)).collect()
}
