//@ needs-trust-verify
//@ edition: 2021
//@ revisions: refused bounded upfront
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@[refused] dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[refused] check-fail
//@[upfront] dont-require-annotations: ERROR
//@[bounded] check-pass
//@[upfront] check-fail
//! CAPACITY OVERFLOW BEHIND `collect` / `extend` (measured 2026-09-25 on stage-1
//! `ab7e41892`): twelve FALSE ACCEPTS, each built rc=0 on the default lane and
//! each panicked "capacity overflow" when a `-Ztrust-verify=off` driver handed it
//! the adversarial input (the same driver against a verify-off build of the same
//! library also exits 101, so the panic is the program's, not the harness's).
//!
//! THREE defects, one property — the allocation lane's charge went missing:
//!
//!   * F1, the keyed collect/extend TOTAL sentinel. `trust-mir-extract` rewrote
//!     `collect::<HashSet<K>>`, `collect::<BTreeSet<K>>` and `HashSet::extend` to
//!     `__trust_total_clone` whenever the key's `Hash`/`Eq`/`Ord` was total. The
//!     rewrite ERASED the call, and vcgen's allocation lane finds a sink by its
//!     name, so the capacity charge vanished with it: ZERO rows.
//!   * F2, `extend` itself. The same rewrite covered `Vec`/`VecDeque`/`String`
//!     `extend` for ANY source, and vcgen had no `extend` sink at all. Every one of
//!     those `extend`s reserves `size_hint().0` first.
//!   * F3, a zero-sized SOURCE element. The bounded-source skip read "the source
//!     is an existing collection" as "the count is bounded", which is false when
//!     the element costs no memory: `vec![(); 1 << 61]` is a real value.
//!
//! What each revision pins:
//!
//!   * `refused` — every function is refused. On the baseline each built clean,
//!     so this revision is red there through its missing annotations.
//!   * `bounded` — the nearby shapes that MUST still verify: a source bounded by
//!     an existing non-zero-sized collection (the rewrite is still licensed), a
//!     count a guard bounds (the allocation lane proves it), and `BTreeSet::extend`
//!     (which inserts one item at a time and reserves nothing).
//!
//! 2026-09-27: "MUST still verify" holds on a 64-bit target only. The bounded-source
//! grant is withheld off 64-bit, where these shapes reach the capacity panic from an
//! ordinary input. On 64-bit, `collect_hashset_from_slice` and
//! `extend_hashset_from_slice` reserve UPFRONT with hashbrown's bucket overhead, a
//! byte factor above what `MAX_LIVE_ALLOC_BYTES` covers, so they verify on a
//! disclosed, undecided premise (`docs/DECISION_QUEUE.md` D12; `docs/KNOWN_HAZARDS.md`,
//! "the bounded-source capacity grant"). If D12 is decided as "charge them", those
//! two rows move to `refused`.
//!
//! 2026-10-06: D12 was decided as option (a), "charge them", and the two rows moved to
//! the `upfront` revision. The grant now also requires the destination's largest
//! upfront reservation to fit on the axiom (`trust_types::alloc_model::
//! bounded_source_reservation_fits`).

use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::net::Ipv4Addr;

// ---- refused: F1, the keyed sentinel hid the capacity charge ----

#[cfg(refused)]
pub fn collect_hashset_range(n: usize) -> HashSet<usize> {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `collect_extend_capacity_charged::collect_hashset_range`
    (0..n).collect::<HashSet<usize>>()
}

/// `BTreeSet::from_iter` collects into a `Vec` first: the same panic.
#[cfg(refused)]
pub fn collect_btreeset_range(n: usize) -> BTreeSet<usize> {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `collect_extend_capacity_charged::collect_btreeset_range`
    (0..n).collect::<BTreeSet<usize>>()
}

#[cfg(refused)]
pub fn extend_hashset_range(s: &mut HashSet<usize>, n: usize) {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `collect_extend_capacity_charged::extend_hashset_range`
    s.extend(0..n);
}

/// A `HashSet<()>` reserves `2^61` for a `2^61`-unit source, and overflows.
#[cfg(refused)]
pub fn extend_hashset_unit_from_zst_slice(s: &mut HashSet<()>, v: &[()]) {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `collect_extend_capacity_charged::extend_hashset_unit_from_zst_slice`
    s.extend(v.iter().copied());
}

// ---- refused: F2, `extend` reserves from an unbounded `size_hint` ----

#[cfg(refused)]
pub fn vec_extend_repeat_take(v: &mut Vec<Ipv4Addr>, n: usize) {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `collect_extend_capacity_charged::vec_extend_repeat_take`
    v.extend(std::iter::repeat(Ipv4Addr::LOCALHOST).take(n));
}

/// `cycle` over a non-empty source reports `size_hint().0 == usize::MAX`.
#[cfg(refused)]
pub fn vec_extend_cycle(v: &mut Vec<u64>, src: &[u64]) {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `collect_extend_capacity_charged::vec_extend_cycle`
    v.extend(src.iter().copied().cycle());
}

#[cfg(refused)]
pub fn vec_extend_repeat_n(v: &mut Vec<u64>, x: u64, n: usize) {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `collect_extend_capacity_charged::vec_extend_repeat_n`
    v.extend(std::iter::repeat_n(x, n));
}

#[cfg(refused)]
pub fn vecdeque_extend_repeat_n(v: &mut VecDeque<u64>, n: usize) {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `collect_extend_capacity_charged::vecdeque_extend_repeat_n`
    v.extend(std::iter::repeat_n(3u64, n));
}

#[cfg(refused)]
pub fn string_extend_repeat_n(s: &mut String, n: usize) {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `collect_extend_capacity_charged::string_extend_repeat_n`
    s.extend(std::iter::repeat_n('x', n));
}

#[cfg(refused)]
pub fn hashmap_extend_zip_ranges(m: &mut HashMap<u64, u64>, n: u64) {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `collect_extend_capacity_charged::hashmap_extend_zip_ranges`
    m.extend((0..n).zip(0..n));
}

#[cfg(refused)]
pub fn collect_hashmap_zip_ranges(n: usize) -> HashMap<usize, usize> {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `collect_extend_capacity_charged::collect_hashmap_zip_ranges`
    (0..n).zip(0..n).collect()
}

// ---- refused: F3, a zero-sized source bounds nothing ----

/// `2^61` units cost nothing; `2^61` eight-byte references overflow.
#[cfg(refused)]
pub fn vec_collect_refs_of_zst_slice(v: &[()]) -> Vec<&()> {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `collect_extend_capacity_charged::vec_collect_refs_of_zst_slice`
    v.iter().collect()
}

// ---- upfront: D12 option (a), 2026-10-06 ----
//
// A hash table reserves up to 16/7 buckets of `size_of::<T>() + 1` bytes per item,
// so a table built from a slice of `u64` can request more than twice the source's
// bytes. On the `MAX_LIVE_ALLOC_BYTES` axiom alone that reservation can exceed
// `isize::MAX`, so these two are charged now (`docs/DECISION_QUEUE.md` D12). They
// were the `bounded` revision's pins of the undecided premise.

#[cfg(upfront)]
pub fn extend_hashset_from_slice(s: &mut HashSet<u64>, v: &[u64]) {
    //[upfront]~^ ERROR Trust Level 0 safety verification incomplete for `collect_extend_capacity_charged::extend_hashset_from_slice`
    s.extend(v.iter().copied());
}

#[cfg(upfront)]
pub fn collect_hashset_from_slice(v: &[u64]) -> HashSet<u64> {
    //[upfront]~^ ERROR Trust Level 0 safety verification incomplete for `collect_extend_capacity_charged::collect_hashset_from_slice`
    v.iter().copied().collect()
}

/// The extractor's keyed-collect licence ERASES the call; it now asks the same
/// question (`bounded_source_reservation_fits_for`): 4 KiB per item from one byte.
#[cfg(upfront)]
pub fn collect_hashset_of_pages(v: &[u8]) -> HashSet<[u8; 4096]> {
    //[upfront]~^ ERROR Trust Level 0 safety verification incomplete for `collect_extend_capacity_charged::collect_hashset_of_pages`
    v.iter().map(|&b| [b; 4096]).collect()
}

/// `BTreeSet::from_iter` collects into a `Vec` of pages first.
#[cfg(upfront)]
pub fn collect_btreeset_of_pages(v: &[u8]) -> BTreeSet<[u8; 4096]> {
    //[upfront]~^ ERROR Trust Level 0 safety verification incomplete for `collect_extend_capacity_charged::collect_btreeset_of_pages`
    v.iter().map(|&b| [b; 4096]).collect()
}

/// The collection-extend licence: `Vec::extend` reserves the source's length.
#[cfg(upfront)]
pub fn vec_extend_pages(s: &mut Vec<[u8; 4096]>, v: &[u8]) {
    //[upfront]~^ ERROR Trust Level 0 safety verification incomplete for `collect_extend_capacity_charged::vec_extend_pages`
    s.extend(v.iter().map(|&b| [b; 4096]));
}

/// Review round 53: a one-item hash table still has four buckets, so a near-`2^61`-byte
/// entry overflows from an `Option` source; `3 * (entry + 1)` per item missed it.
#[cfg(upfront)]
pub fn collect_hashmap_of_huge_from_option(o: Option<u8>) -> usize {
    //[upfront]~^ ERROR Trust Level 0 safety verification incomplete for `collect_extend_capacity_charged::collect_hashmap_of_huge_from_option`
    const N: usize = (1usize << 61) - 2;
    let m: HashMap<u8, std::mem::MaybeUninit<[u8; N]>> =
        o.iter().map(|&k| (k, std::mem::MaybeUninit::<[u8; N]>::uninit())).collect();
    m.len()
}

/// Review round 54: `String`'s `Extend<&str>` for an array (`SpecExtendStr`) reserves
/// the SUM of the strings' lengths, and all three may be one live string.
#[cfg(upfront)]
pub fn string_extend_str_array(out: &mut String, s: &str) {
    //[upfront]~^ ERROR Trust Level 0 safety verification incomplete for `collect_extend_capacity_charged::string_extend_str_array`
    out.extend([s, s, s]);
}

/// Review round 54: after taking a char, `extend_desugared` reserves `lower + 1`, one
/// past `ceil(len / 4)`; with four-byte items that is past the extend budget.
#[cfg(upfront)]
pub fn vec_extend_chars(v: &mut Vec<char>, s: &str) {
    //[upfront]~^ ERROR Trust Level 0 safety verification incomplete for `collect_extend_capacity_charged::vec_extend_chars`
    v.extend(s.chars());
}

/// Review round 55: `BTreeSet::from_iter` sorts what it collected, and the stable
/// sort's scratch holds at least 48 elements once there are more than 20. 21 items
/// of `2e17` bytes fit the axiom; 48 do not fit `isize::MAX`.
#[cfg(upfront)]
pub fn collect_btreeset_of_huge_items(v: &[[u8; 200_000_000_000_000_000]]) -> BTreeSet<[u8; 200_000_000_000_000_000]> {
    //[upfront]~^ ERROR Trust Level 0 safety verification incomplete for `collect_extend_capacity_charged::collect_btreeset_of_huge_items`
    v.iter().copied().collect()
}

// ---- bounded: nearby shapes that must still verify ----

/// Review round 55: a hash table holds at most `MAX_LIVE / (entry + 1)` entries, so
/// copying them out at the same width fits.
#[cfg(bounded)]
pub fn vec_from_hashset(h: &HashSet<u64>) -> Vec<u64> {
    h.iter().copied().collect()
}

/// Review round 55: `String`'s string-item impls push in turn and reserve nothing
/// upfront (only a by-value `[&str; N]` reserves the sum, see `upfront`).
#[cfg(bounded)]
pub fn string_extend_words(out: &mut String, w: &[&str]) {
    out.extend(w.iter().copied());
}

#[cfg(bounded)]
pub fn string_extend_owned(out: &mut String, w: Vec<String>) {
    out.extend(w);
}

#[cfg(bounded)]
pub fn vec_extend_utf16(v: &mut Vec<u16>, s: &str) {
    v.extend(s.encode_utf16());
}

#[cfg(bounded)]
pub fn collect_btreeset_from_slice(v: &[u64]) -> BTreeSet<u64> {
    v.iter().copied().collect()
}

/// Review round 53: a str view reserves its `size_hint().0` upfront (zero for the
/// split family), not its item count, so these collects keep their grant.
#[cfg(bounded)]
pub fn collect_split_fields(s: &str) -> Vec<&str> {
    s.split(',').collect()
}

#[cfg(bounded)]
pub fn collect_chars(s: &str) -> Vec<char> {
    s.chars().collect()
}

#[cfg(bounded)]
pub fn vec_from_iter_copied(v: &[u32]) -> Vec<u32> {
    Vec::from_iter(v.iter().copied())
}

#[cfg(bounded)]
pub fn vec_extend_from_slice_iter(v: &mut Vec<u64>, src: &[u64]) {
    v.extend(src.iter().copied());
}

#[cfg(bounded)]
pub fn vec_extend_from_vec_ref(v: &mut Vec<u64>, w: &Vec<u64>) {
    v.extend(w);
}

#[cfg(bounded)]
pub fn string_extend_chars(s: &mut String, t: &str) {
    s.extend(t.chars());
}

#[cfg(bounded)]
// ZERO-ROW-GATE (2026-10-10) refused this body while it published zero rows. Since the
// merge of 2026-10-14 its bundled `collect` carries the counted panic-freedom aggregate
// (the soundness line's carrier for a call into a bundled body), which the CHC lane
// refutes and the compiler keeps `runtime_checked`: `0 proved, 1 runtime-checked, 1
// skipped`, the same verdict as `vec_from_hashset` above, a default-policy warning
// (measured on the merged stage 1, 2026-10-15). The gate is unchanged; this body is no
// longer zero-row.
pub fn vec_collect_refs_of_slice(v: &[u64]) -> Vec<&u64> {
    v.iter().collect()
}

#[cfg(bounded)]
pub fn collect_hashset_guarded_range(n: usize) -> HashSet<usize> {
    if n < 1000 { (0..n).collect::<HashSet<usize>>() } else { HashSet::new() }
}

#[cfg(bounded)]
pub fn vec_extend_guarded_repeat_n(v: &mut Vec<u64>, n: usize) {
    if n < 1000 {
        v.extend(std::iter::repeat_n(7u64, n));
    }
}

/// `BTreeSet::extend` inserts one item at a time and reserves nothing: it can
/// exhaust memory on an endless source, never panic "capacity overflow".
#[cfg(bounded)]
pub fn btreeset_extend_range(s: &mut BTreeSet<u64>, n: u64) {
    s.extend(0..n);
}
