//@ needs-trust-verify
//@ edition: 2021
//@ revisions: refused bounded
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[refused] check-fail
//@[bounded] check-fail
//! CAPACITY OVERFLOW BEHIND A TUPLE `extend` / `Iterator::unzip` (measured
//! 2026-09-25 on main, stage-1 `7c7e46061`): two FALSE ACCEPTS, each built rc=0
//! on the default lane and panicked "capacity overflow" (exit 101) when a
//! `-Ztrust-verify=off` driver passed `n = usize::MAX` (the same driver against a
//! verify-off build of the library also exits 101).
//!
//! core's `impl Extend<(A, B, ..)> for (ExtendA, ExtendB, ..)` runs
//! `default_extend`, which calls `extend_reserve(size_hint().0)` on EVERY
//! component before inserting anything, and `Iterator::unzip` is
//! `let mut p: (FromA, FromB) = Default::default(); p.extend(self); p`. The F2
//! `extend` sink (`is_capacity_reserving_std_extend`) matched the receiver's path
//! head only, so a TUPLE receiver was no sink, and `unzip` was no sink at all.
//! Found by the W4 HASHMAP redo: once std's hash tables joined the vanilla class,
//! the `HashSet` forms would have followed (pinned in
//! `hashmap_caller_value_panics_stay_refused.rs`, `tuple_extend`/`unzip`).
//!
//!   * `refused` — both `Vec` forms are refused (a tuple receiver holding a
//!     reserving collection, and `unzip`, are now allocation sinks). On the
//!     baseline each built clean, so this revision is red there through its
//!     missing annotations.
//!   * `bounded` — the nearby shapes that MUST still verify: both from a source
//!     bounded by an existing non-zero-sized collection.
//!
//! RE-PINNED 2026-10-15 (the merge of 2026-10-14; DECISION_QUEUE D103): `bounded`
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

#[cfg(refused)]
pub fn vec_tuple_extend(pair: &mut (Vec<u32>, Vec<u8>), n: usize) {
    //[refused]~^ ERROR Trust strict verification failed for `tuple_extend_unzip_capacity_charged::vec_tuple_extend`
    pair.extend(std::iter::repeat((1u32, 1u8)).take(n));
}

#[cfg(refused)]
pub fn vec_unzip(n: usize) -> (Vec<u32>, Vec<u8>) {
    //[refused]~^ ERROR Trust strict verification failed for `tuple_extend_unzip_capacity_charged::vec_unzip`
    std::iter::repeat((1u32, 1u8)).take(n).unzip()
}

#[cfg(bounded)]
pub fn vec_tuple_extend_from_slice(pair: &mut (Vec<u32>, Vec<u8>), v: &[(u32, u8)]) {
    pair.extend(v.iter().copied());
}

#[cfg(bounded)]
pub fn vec_unzip_from_slice(v: &[(u32, u8)]) -> (Vec<u32>, Vec<u8>) {
    v.iter().copied().unzip()
}
