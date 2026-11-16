//@ needs-trust-verify
//@ edition: 2021
//@ revisions: refused guarded guarded_count
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[refused] check-fail
//@[guarded] check-pass
//@[guarded_count] check-fail
//! STD METHODS THAT PANIC ON A CALLER INDEX, RANGE OR COUNT (measured 2026-09-25
//! on stage-1 `6606d3bdf`): a FALSE ACCEPT class. Every function in `refused`
//! built rc=0 on the default lane and, driven verify-off with an out-of-range
//! argument, panicked (exit 101): "slice index starts at 2 but ends at 1",
//! "insertion index (is 5) should be <= len (is 1)", "Out of bounds access",
//! "assertion failed: self.is_char_boundary(at)", "capacity overflow", "range end
//! index 5 out of range for slice of length 3", "assertion failed: j <
//! self.len()". Their panics live inside the library (`slice::range`, a
//! char-boundary `assert!`, `checked_mul(..).expect(..)`, `get(i).expect(..)`), so
//! no caller-visible `Assert` carried the argument, and no call-site recognizer
//! named the method.
//!
//! The calls now join the call-site panic family (`slice_method_panic` ->
//! `collection_range`):
//!
//!   * `refused` — each unguarded call: a precise bounds row the solver refutes
//!     (`VecDeque` index/swap/range, `..=b` and `(Bound, Bound)` on a slice), or a
//!     fail-honest row where no sound precise model exists (`Vec::splice`/
//!     `extract_if`/`insert_mut` resize their receiver; `String`'s char
//!     boundaries; `<[T]>::repeat`'s capacity product; an owned `Vec`/`str`
//!     receiver of the new index shapes; a const chunk size `N` that is not a
//!     nonzero literal; `into_flattened` over a zero-sized element).
//!   * `guarded` — the same calls under a guard that establishes the bound (the
//!     precise rows prove), and the arguments that cannot panic (`..`, `0..0`,
//!     `0`, `repeat(1)`), which mint nothing.
//!   * `guarded_count` (2026-09-29) — `v.extract_if(.., ..).count()`, moved out of
//!     `guarded`: the full range still mints no bounds row, but the function is now
//!     REFUSED by the bundled std-member fix. `count()` bundles a core member whose
//!     inherited `Overflow(Add)` Assert the admission lane refuses; that refusal
//!     used to DISCARD the whole bundle and the lowering-failure tolerance accepted
//!     the function. The kept bundle carries a fail-closed "generic absent callee"
//!     row for `Vec::<u32>::extract_if::<{closure}, RangeFull>` — the row the
//!     success path already refuses for `v.extract_if(0..n, ..).last()`, which
//!     bundles no refused member (measured on origin/main `f6773df328e`,
//!     release-like std: rc=1, same row class). A capability loss, recorded in
//!     docs/KNOWN_HAZARDS.md ("CLOSED 2026-09-29 — the bundled std-member
//!     tolerance …").

use std::collections::VecDeque;
use std::ops::Bound;

// ---- refused ----

#[cfg(refused)]
pub fn vec_splice(v: &mut Vec<u32>, a: usize, b: usize) -> usize {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `std_index_range_panics_charged::vec_splice`
    v.splice(a..b, [9u32]).count()
}

#[cfg(refused)]
pub fn vec_extract_if(v: &mut Vec<u32>, a: usize, b: usize) -> usize {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `std_index_range_panics_charged::vec_extract_if`
    v.extract_if(a..b, |x| *x > 1).count()
}

#[cfg(refused)]
pub fn vec_insert_mut(v: &mut Vec<u32>, i: usize) -> u32 {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `std_index_range_panics_charged::vec_insert_mut`
    *v.insert_mut(i, 7)
}

#[cfg(refused)]
pub fn vec_index_to_inclusive(v: &Vec<u32>, b: usize) -> usize {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `std_index_range_panics_charged::vec_index_to_inclusive`
    v[..=b].len()
}

#[cfg(refused)]
pub fn vec_index_bound_pair(v: &Vec<u32>, a: usize, b: usize) -> usize {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `std_index_range_panics_charged::vec_index_bound_pair`
    v[(Bound::Included(a), Bound::Excluded(b))].len()
}

#[cfg(refused)]
pub fn slice_repeat(v: &[u8], n: usize) -> Vec<u8> {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `std_index_range_panics_charged::slice_repeat`
    v.repeat(n)
}

#[cfg(refused)]
pub fn slice_index_to_inclusive(v: &[u8], b: usize) -> usize {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `std_index_range_panics_charged::slice_index_to_inclusive`
    v[..=b].len()
}

#[cfg(refused)]
pub fn slice_index_bound_pair(v: &[u8], a: usize, b: usize) -> usize {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `std_index_range_panics_charged::slice_index_bound_pair`
    v[(Bound::Included(a), Bound::Excluded(b))].len()
}

#[cfg(refused)]
pub fn str_index_to_inclusive(s: &str, b: usize) -> usize {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `std_index_range_panics_charged::str_index_to_inclusive`
    s[..=b].len()
}

#[cfg(refused)]
pub fn str_index_bound_pair(s: &str, a: usize, b: usize) -> usize {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `std_index_range_panics_charged::str_index_bound_pair`
    s[(Bound::Included(a), Bound::Excluded(b))].len()
}

#[cfg(refused)]
pub fn string_split_off(s: &mut String, at: usize) -> String {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `std_index_range_panics_charged::string_split_off`
    s.split_off(at)
}

#[cfg(refused)]
pub fn string_truncate(s: &mut String, n: usize) {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `std_index_range_panics_charged::string_truncate`
    s.truncate(n)
}

#[cfg(refused)]
pub fn string_drain(s: &mut String, a: usize, b: usize) -> usize {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `std_index_range_panics_charged::string_drain`
    s.drain(a..b).count()
}

#[cfg(refused)]
pub fn string_replace_range(s: &mut String, a: usize, b: usize) {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `std_index_range_panics_charged::string_replace_range`
    s.replace_range(a..b, "x")
}

#[cfg(refused)]
pub fn string_extend_from_within(s: &mut String, a: usize, b: usize) {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `std_index_range_panics_charged::string_extend_from_within`
    s.extend_from_within(a..b)
}

#[cfg(refused)]
pub fn deque_swap(d: &mut VecDeque<u32>, i: usize, j: usize) {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `std_index_range_panics_charged::deque_swap`
    d.swap(i, j)
}

#[cfg(refused)]
pub fn deque_index(d: &VecDeque<u32>, i: usize) -> u32 {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `std_index_range_panics_charged::deque_index`
    d[i]
}

#[cfg(refused)]
pub fn deque_index_mut(d: &mut VecDeque<u32>, i: usize) {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `std_index_range_panics_charged::deque_index_mut`
    d[i] = 3
}

#[cfg(refused)]
pub fn deque_range(d: &VecDeque<u32>, a: usize, b: usize) -> usize {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `std_index_range_panics_charged::deque_range`
    d.range(a..b).count()
}

#[cfg(refused)]
pub fn deque_range_mut(d: &mut VecDeque<u32>, a: usize, b: usize) -> usize {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `std_index_range_panics_charged::deque_range_mut`
    d.range_mut(a..b).count()
}

#[cfg(refused)]
pub fn deque_insert_mut(d: &mut VecDeque<u32>, i: usize) -> u32 {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `std_index_range_panics_charged::deque_insert_mut`
    *d.insert_mut(i, 7)
}

#[cfg(refused)]
pub fn slice_as_chunks_zero(v: &[u8]) -> usize {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `std_index_range_panics_charged::slice_as_chunks_zero`
    v.as_chunks::<0>().1.len()
}

/// `Vec<[(); 2]>` of length `usize::MAX` flattens to `2 * usize::MAX` units.
#[cfg(refused)]
pub fn vec_into_flattened_zst(v: Vec<[(); 2]>) -> usize {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `std_index_range_panics_charged::vec_into_flattened_zst`
    v.into_flattened().len()
}

// ---- guarded: must still verify ----

#[cfg(guarded)]
pub fn slice_as_chunks_four(v: &[u8]) -> usize {
    v.as_chunks::<4>().1.len()
}

#[cfg(guarded)]
pub fn vec_into_flattened_sized(v: Vec<[u8; 2]>) -> usize {
    v.into_flattened().len()
}

#[cfg(guarded)]
pub fn deque_index_guarded(d: &VecDeque<u32>, i: usize) -> u32 {
    if i < d.len() { d[i] } else { 0 }
}

#[cfg(guarded)]
pub fn deque_index_mut_guarded(d: &mut VecDeque<u32>, i: usize) {
    if i < d.len() { d[i] = 3 }
}

#[cfg(guarded)]
pub fn deque_index_front_nonempty(d: &VecDeque<u32>) -> u32 {
    if !d.is_empty() { d[0] } else { 0 }
}

#[cfg(guarded)]
pub fn deque_swap_guarded(d: &mut VecDeque<u32>, i: usize, j: usize) {
    let n = d.len();
    if i < n && j < n { d.swap(i, j) }
}

#[cfg(guarded)]
pub fn deque_range_guarded(d: &VecDeque<u32>, a: usize, b: usize) -> usize {
    if a <= b && b <= d.len() { d.range(a..b).count() } else { 0 }
}

#[cfg(guarded)]
pub fn deque_range_mut_guarded(d: &mut VecDeque<u32>, a: usize, b: usize) -> usize {
    if a <= b && b <= d.len() { d.range_mut(a..b).count() } else { 0 }
}

#[cfg(guarded)]
pub fn deque_range_inclusive_guarded(d: &VecDeque<u32>, a: usize, b: usize) -> usize {
    if a <= b && b < d.len() { d.range(a..=b).count() } else { 0 }
}

#[cfg(guarded)]
pub fn deque_range_full(d: &VecDeque<u32>) -> usize {
    d.range(..).count()
}

#[cfg(guarded)]
pub fn slice_index_to_inclusive_guarded(v: &[u8], b: usize) -> usize {
    if b < v.len() { v[..=b].len() } else { 0 }
}

#[cfg(guarded)]
pub fn slice_index_inclusive_guarded(v: &[u8], a: usize, b: usize) -> usize {
    if a <= b && b < v.len() { v[a..=b].len() } else { 0 }
}

#[cfg(guarded)]
pub fn slice_index_bound_pair_guarded(v: &[u8], a: usize, b: usize) -> usize {
    if a <= b && b <= v.len() { v[(Bound::Included(a), Bound::Excluded(b))].len() } else { 0 }
}

#[cfg(guarded)]
pub fn slice_index_bound_pair_unbounded(v: &[u8]) -> usize {
    v[(Bound::<usize>::Unbounded, Bound::<usize>::Unbounded)].len()
}

#[cfg(guarded)]
pub fn vec_splice_full(v: &mut Vec<u32>) -> usize {
    v.splice(.., [9u32]).count()
}

#[cfg(guarded)]
pub fn vec_splice_front(v: &mut Vec<u32>) -> usize {
    v.splice(0..0, [9u32]).count()
}

#[cfg(guarded_count)]
pub fn vec_extract_if_full(v: &mut Vec<u32>) -> usize {
    //[guarded_count]~^ ERROR Trust strict verification failed for `std_index_range_panics_charged::vec_extract_if_full`: 1 obligation(s) were not fully verified
    v.extract_if(.., |x| *x > 1).count()
}

#[cfg(guarded)]
pub fn vec_insert_mut_front(v: &mut Vec<u32>) -> u32 {
    *v.insert_mut(0, 7)
}

#[cfg(guarded)]
pub fn string_drain_full(s: &mut String) -> usize {
    s.drain(..).count()
}

#[cfg(guarded)]
pub fn string_truncate_zero(s: &mut String) {
    s.truncate(0)
}

#[cfg(guarded)]
pub fn string_split_off_zero(s: &mut String) -> String {
    s.split_off(0)
}

#[cfg(guarded)]
pub fn slice_repeat_once(v: &[u8]) -> Vec<u8> {
    v.repeat(1)
}
