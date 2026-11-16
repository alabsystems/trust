//@ needs-trust-verify
//@ edition: 2021
//@ revisions: bounded charged
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[bounded] check-pass
//@[charged] check-fail
//! A counted allocation whose count IS the length of an existing slice or str is
//! bounded the way a collect over that collection is (`docs/DECISION_QUEUE.md` D12
//! option (a)): granted only when that many items times the exact stride fits
//! `isize::MAX` (against the live-receiver budget for `reserve`). ordsweep2
//! strings/c04 hit the 2^28-element availability ceiling on `String::with_capacity
//! (s.len())`. A wider stride, a count derived from the length, a reassigned count,
//! and a zero-sized source keep their charge.
//! Since D102 (2026-10-15) the skip applies only where main's ALLOC-LEN availability
//! theorem also holds, so `reserve_for` (an additional count) moved to `charged`.
#![allow(dead_code)]

#[cfg(bounded)]
pub fn upper(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        out.push(c.to_ascii_uppercase());
    }
    out
}

#[cfg(bounded)]
pub fn zeros(v: &[u8]) -> Vec<u8> {
    vec![0u8; v.len()]
}

// MOVED to `charged` 2026-10-15 (DECISION_QUEUE D102, fail-closed meanwhile): main's
// ALLOC-LEN keeps the `2^28`-element availability ceiling on a `reserve`'s ADDITIONAL
// count (no counted sequence bounds the receiver's length), and the existing-length
// skip now applies only where that theorem holds. No capacity panic is reachable here
// under either line's axiom; the two lines differ on the availability policy only
// (measured on the merged stage 1: `[unbounded_allocation] FAILED` at `v.len() = 2^28`).
#[cfg(charged)]
pub fn reserve_for(out: &mut Vec<u32>, v: &[u32]) {
    //[charged]~^ ERROR Trust Level 0 safety verification incomplete for `counted_alloc_of_existing_length::reserve_for`
    out.reserve(v.len());
}

#[cfg(charged)]
pub fn wide(s: &str) -> Vec<u64> {
    //[charged]~^ ERROR Trust Level 0 safety verification incomplete for `counted_alloc_of_existing_length::wide`
    vec![0u64; s.len()]
}

#[cfg(charged)]
pub fn huge(v: &[u8]) -> Vec<[u8; 1 << 20]> {
    //[charged]~^ ERROR Trust Level 0 safety verification incomplete for `counted_alloc_of_existing_length::huge`
    Vec::with_capacity(v.len())
}

#[cfg(charged)]
pub fn scaled(v: &[u8]) -> Vec<u8> {
    //[charged]~^ ERROR Trust Level 0 safety verification incomplete for `counted_alloc_of_existing_length::scaled`
    let mut n = v.len();
    n = n.saturating_mul(3);
    Vec::with_capacity(n)
}

#[cfg(charged)]
pub fn units(v: &[()]) -> Vec<u8> {
    //[charged]~^ ERROR Trust Level 0 safety verification incomplete for `counted_alloc_of_existing_length::units`
    Vec::with_capacity(v.len())
}

/// Review round 58: a raw slice pointer's length is any `usize` (`slice_from_raw_parts`
/// is safe and allocates nothing).
#[cfg(charged)]
pub fn raw_len(p: *const [u64]) -> Vec<u64> {
    //[charged]~^ ERROR Trust Level 0 safety verification incomplete for `counted_alloc_of_existing_length::raw_len`
    Vec::with_capacity(p.len())
}

/// Review round 58: a hash table reserves far more per item than its element.
#[cfg(charged)]
pub fn hashset_of(s: &str) -> std::collections::HashSet<u8> {
    //[charged]~^ ERROR Trust Level 0 safety verification incomplete for `counted_alloc_of_existing_length::hashset_of`
    std::collections::HashSet::with_capacity(s.len())
}

/// Review round 59: a zero-sized element's length is bounded by no memory, and
/// `reserve` adds to it, so `len + additional` can overflow `usize` ("capacity
/// overflow") whatever the count's provenance.
#[cfg(charged)]
pub fn reserve_units(v: &mut Vec<()>, n: usize) {
    //[charged]~^ ERROR Trust Level 0 safety verification incomplete for `counted_alloc_of_existing_length::reserve_units`
    v.reserve(n);
}

/// `with_capacity` and `resize` take an ABSOLUTE count, so a zero-sized element costs
/// nothing and cannot overflow.
#[cfg(bounded)]
pub fn units_with_capacity(n: usize) -> Vec<()> {
    Vec::with_capacity(n)
}

// MOVED to `charged` 2026-10-15: still cannot overflow (an absolute count of a
// zero-sized element allocates nothing), but since the merge of 2026-10-14 the `resize`
// call is an unproved generic absent callee under main's default-policy rule, which
// keeps the function fail-closed (measured on the merged stage 1). A capability cost of
// the merge, not this lane's: the allocation row itself is not charged.
#[cfg(charged)]
pub fn units_resized(v: &mut Vec<()>, n: usize) {
    //[charged]~^ ERROR Trust strict verification failed for `counted_alloc_of_existing_length::units_resized`
    v.resize(n, ());
}
