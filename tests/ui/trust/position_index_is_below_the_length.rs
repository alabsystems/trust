//@ needs-trust-verify
//@ edition: 2021
//@ revisions: position rposition iter_mut after_next
//@ revisions: other_slice reseated_slice next_index user_position
//@ revisions: count_filtered count_chained
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[position] check-pass
//@[rposition] check-pass
//@[iter_mut] check-pass
//@[after_next] check-pass
//@[other_slice] check-fail
//@[reseated_slice] check-fail
//@[next_index] check-fail
//@[user_position] check-fail
//@[count_filtered] check-pass
//@[count_chained] check-fail
//! **The index `position` returns is below the length of the slice it searched
//! (Trust, 2026-09-29).**
//!
//! `if let Some(i) = v.iter().position(|&x| x == t) { v[i] }` was refuted with
//! `i = 0`, `v.len() = 0` (the ordinary-Rust completeness sweep): nothing related the
//! index to the slice. `Iterator::position` and `rposition` on a slice's own iterator
//! return the index of an element counted from the front of what the iterator has
//! not yet yielded, so a `Some` index is below the slice's length
//! (`container_len::build_position_yield_guard_map`). The iterator's `&mut` may feed
//! only `next`, `position` and `rposition`, which consume and never reseat it.
//!
//! * `position` … `after_next`: POSITIVE.
//! * `other_slice`: the index of one slice is not an index into another.
//! * `reseated_slice`: the slice searched is not the slice indexed.
//! * `next_index`: `i + 1` can equal the length.
//! * `user_position`: a user method named `position` promises nothing.
//! * `count_filtered`: POSITIVE. `count()` over a slice's iterator through adapters
//!   that never add items is at most the slice's length
//!   (`container_len::build_count_bound_guard_map`, over
//!   `loop_bounds::iterated_slice_of`), so `v.len() - v.iter().filter(p).count()`
//!   cannot underflow; it was refuted with `count = 1`, `len = 0`.
//! * `count_chained`: `chain` yields more than its receiver, so it is not followed.

#[cfg(position)]
pub fn find(v: &[u32], t: u32) -> u32 {
    if let Some(i) = v.iter().position(|&x| x == t) { v[i] } else { 0 }
}

#[cfg(rposition)]
pub fn rfind(v: &[u32], t: u32) -> u32 {
    if let Some(i) = v.iter().rposition(|&x| x == t) { v[i] } else { 0 }
}

#[cfg(iter_mut)]
pub fn clear_first_zero(v: &mut [u32]) {
    if let Some(i) = v.iter_mut().position(|x| *x == 0) {
        v[i] = 1;
    }
}

#[cfg(after_next)]
pub fn find_after_first(v: &[u32], t: u32) -> u32 {
    let mut it = v.iter();
    it.next();
    if let Some(i) = it.position(|&x| x == t) { v[i] } else { 0 }
}

#[cfg(other_slice)]
pub fn find_in_a_read_b(a: &[u32], b: &[u32], t: u32) -> u32 {
    //[other_slice]~^ ERROR Trust
    if let Some(i) = a.iter().position(|&x| x == t) { b[i] } else { 0 }
}

#[cfg(reseated_slice)]
pub fn find_then_reseat(a: &[u32], b: &[u32], t: u32) -> u32 {
    //[reseated_slice]~^ ERROR Trust
    let mut s = a;
    if let Some(i) = s.iter().position(|&x| x == t) {
        s = b;
        s[i]
    } else {
        0
    }
}

#[cfg(next_index)]
pub fn next_after_match(v: &[u32], t: u32) -> u32 {
    //[next_index]~^ ERROR Trust
    if let Some(i) = v.iter().position(|&x| x == t) { v[i + 1] } else { 0 }
}

#[cfg(user_position)]
pub struct Finder;

#[cfg(user_position)]
impl Finder {
    pub fn position(&self, _v: &[u32]) -> Option<usize> {
        Some(7)
    }
}

#[cfg(user_position)]
pub fn user_find(f: &Finder, v: &[u32]) -> u32 {
    //[user_position]~^ ERROR Trust
    if let Some(i) = f.position(v) { v[i] } else { 0 }
}

#[cfg(count_filtered)]
pub fn not_matching(v: &[u32], t: u32) -> usize {
    v.len() - v.iter().filter(|&&x| x == t).count()
}

#[cfg(count_chained)]
pub fn not_in_either(v: &[u32], w: &[u32]) -> usize {
    //[count_chained]~^ ERROR Trust
    v.len() - v.iter().chain(w.iter()).count()
}
