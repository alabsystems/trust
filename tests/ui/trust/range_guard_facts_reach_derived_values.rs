//@ needs-trust-verify
//@ edition: 2021
//@ revisions: digit lowercase control_false_branch prev_index
//@ revisions: alphabetic_underflows next_index_oob stale_copy_after_empty_loop
//@ revisions: ascii_tested_value_changed_by_call range_bound_changed_by_call
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[digit] check-pass
//@[lowercase] check-pass
//@[control_false_branch] check-pass
//@[prev_index] check-pass
//@[alphabetic_underflows] check-fail
//@[next_index_oob] check-fail
//@[stale_copy_after_empty_loop] check-fail
//@[ascii_tested_value_changed_by_call] check-fail
//@[range_bound_changed_by_call] check-fail
//! **A range a guard establishes reaches the values computed from it (Trust,
//! 2026-09-29).**
//!
//! Two ordinary shapes the ordinary-Rust completeness sweep found refused on the
//! default lane:
//!
//! * `if b.is_ascii_digit() { b - b'0' }` was refuted for underflow with `b = 0`. The
//!   guard lane gave every std ascii predicate the family-wide `b <= 127`, which says
//!   nothing about the low end. Each predicate now carries its exact codepoint set on
//!   the TRUE branch and its complement on the FALSE branch
//!   (`guards::ascii_predicate_bound`, transcribed from `library/core`).
//! * `for i in 1..v.len() { v[i - 1] }` was refuted with `i = 1`, `len = 0`: the
//!   range-yield fact `1 <= i < len` was attached only to blocks that name `i`, and
//!   the bounds check reads `i - 1`'s temp. It now also reaches blocks that name a
//!   single-assignment local computed from `i` (`iterator_yield::locals_derived_from`).
//!
//! * `digit` … `prev_index`: POSITIVE.
//! * `alphabetic_underflows`: `b'A' - b'a'` underflows; the alphabetic set includes
//!   `A`, so it must stay refuted.
//! * `next_index_oob`: `v[i + 1]` reaches `v.len()` on the last iteration.
//! * `stale_copy_after_empty_loop`: `s` is assigned twice, so it is not derived from
//!   `i`. When the loop never runs, `s` is `0` and `s - 1` underflows; attaching
//!   `1 <= i < len` there (unsatisfiable for `len == 0`) would have proved it.
//! * `ascii_tested_value_changed_by_call`, `range_bound_changed_by_call`: a `&mut`
//!   handed to a callee between the test and the use (`zero(x)`, `shrink(s)`) can
//!   change the tested byte or the range bound with no store naming it. Both were
//!   proved and panic (the ascii precondition audit and the trip-count lane
//!   review, 2026-09-29). The ascii set is now versioned at the predicate call
//!   (`guards::ascii_predicate_bound`), and a range bound read through a reference
//!   needs every pointer derived from its root accounted for
//!   (`local_defs::deref_read_is_never_written`);
//!   `guard_facts_behind_a_pointer_are_versioned.rs` has the reload and alias shapes.

#[cfg(digit)]
pub fn digit(b: u8) -> u8 {
    if b.is_ascii_digit() { b - b'0' } else { 0 }
}

#[cfg(lowercase)]
pub fn letter_index(c: char) -> u32 {
    if c.is_ascii_lowercase() { c as u32 - 'a' as u32 } else { 26 }
}

#[cfg(control_false_branch)]
pub fn printable_offset(b: u8) -> u8 {
    // On the FALSE branch of `is_ascii_control`, `b` is not in `0..=31` or `127`,
    // and it is `<= 126` here, so `b - 32` cannot underflow.
    if b.is_ascii_control() || b > 126 { 0 } else { b - 32 }
}

#[cfg(prev_index)]
pub fn prev(v: &[u32]) -> u32 {
    let mut s = 0u32;
    for i in 1..v.len() {
        s = s.wrapping_add(v[i - 1]);
    }
    s
}

#[cfg(alphabetic_underflows)]
pub fn alpha_index(b: u8) -> u8 {
    //[alphabetic_underflows]~^ ERROR Trust
    if b.is_ascii_alphabetic() { b - b'a' } else { 0 }
}

#[cfg(next_index_oob)]
pub fn next(v: &[u32]) -> u32 {
    //[next_index_oob]~^ ERROR Trust
    let mut s = 0u32;
    for i in 1..v.len() {
        s = s.wrapping_add(v[i + 1]);
    }
    s
}

#[cfg(stale_copy_after_empty_loop)]
pub fn last_index(v: &[u32]) -> u32 {
    //[stale_copy_after_empty_loop]~^ ERROR Trust
    let mut s = 0usize;
    for i in 1..v.len() {
        s = i;
    }
    v[s - 1]
}

#[cfg(ascii_tested_value_changed_by_call)]
fn zero(p: &mut u8) {
    *p = 0;
}

#[cfg(ascii_tested_value_changed_by_call)]
pub fn stale_digit(x: &mut u8) -> u8 {
    //[ascii_tested_value_changed_by_call]~^ ERROR Trust
    let d = x.is_ascii_digit();
    zero(x);
    if d { *x - b'0' } else { 0 }
}

#[cfg(range_bound_changed_by_call)]
pub struct S {
    pub n: usize,
}

#[cfg(range_bound_changed_by_call)]
fn shrink(s: &mut S) {
    s.n = 0;
}

#[cfg(range_bound_changed_by_call)]
pub fn count_down(s: &mut S) -> usize {
    //[range_bound_changed_by_call]~^ ERROR Trust
    let mut t = 0usize;
    for i in 0..s.n {
        shrink(s);
        t ^= s.n - i - 1;
    }
    t
}
