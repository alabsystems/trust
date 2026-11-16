//@ needs-trust-verify
//@ edition: 2021
//@ revisions: guarded_swap_remove guarded_remove unguarded off_by_one two_resizes looped use_after guarded_insert field_receiver user_trait_spelled_std stale_len_tie_user_trait
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[guarded_swap_remove] check-pass
//@[guarded_remove] check-pass
//@[unguarded] check-fail
//@[off_by_one] check-fail
//@[two_resizes] check-fail
//@[looped] check-fail
//@[use_after] check-pass
//@[guarded_insert] check-pass
//@[field_receiver] check-pass
//@[user_trait_spelled_std] check-fail
//@[stale_len_tie_user_trait] check-fail
//! Sweep c05 (2026-10-10): `Vec::remove(i)` / `swap_remove(i)` on a `&mut Vec`
//! parameter carry their real index precondition `i < v.len()` when the call is the
//! vector's SOLE resize and nothing that uses the vector is reachable after it
//! (`value_facts::vec_sole_mutator_block`): every `.len()` then ran before the
//! resize, so it is the length the call sees. The bridge leaves that precondition to
//! the formula lane (`vec_index_removal_call`) instead of an absent-callee may-panic
//! marker; neither method allocates or runs element code.
//! Negative controls, each refused:
//! * `unguarded`, `off_by_one` (`i <= len`): the precondition is refuted.
//! * `two_resizes` (`let n = v.len(); v.remove(0); v.remove(n - 1)`), `looped`:
//!   the stale-length shapes keep the fail-honest Unknown.
//!
//! RE-PINNED 2026-10-15 (the merge of 2026-10-14): three shapes this lane declines
//! are proved by main's VEC-INSERT region (`vec_region.rs`, docs/TCB.md "A `Vec`
//! index mutator inside its base's pre-mutation region"), each a correct program
//! with one `&mut` parameter and no other writing argument (DECISION_QUEUE D101), so
//! they are now `check-pass`:
//! * `use_after`: the guarded `remove(i)` is in the region; the `v.len()` after it is
//!   outside and carries no obligation.
//! * `guarded_insert`: the `i <= len` row is stated over `L0`. `insert`'s growth is
//!   `push`'s, charged as such; for this non-zero-sized element it cannot reach the
//!   capacity panic under the live-allocation axiom, and a `Vec<()>` twin (`if i <=
//!   v.len() { v.insert(i, ()) }`) and `push` on `Vec<()>` are still refused
//!   (measured on the merged stage 1).
//! * `field_receiver`: main's VEC-INSERT-FIELD admits a field base under an `&mut`
//!   parameter.
//! * `user_trait_spelled_std` (review round 97, a certified false row): a user trait's
//!   associated fn whose `Self` is a std ops type (`<core::ops::Range<usize> as
//!   Evil>::index(v, 0)`) clears the vector between the guard and the remove. It was
//!   counted a benign length read by a prefix test; the trait is now matched
//!   structurally. `stale_len_tie_user_trait` is the older `.len()`-tie shape of the
//!   same hole (`let n = v.len(); ...; v[n - 1]`).

#[cfg(guarded_swap_remove)]
pub fn take_at(v: &mut Vec<u32>, i: usize) -> Option<u32> {
    if i < v.len() { Some(v.swap_remove(i)) } else { None }
}

#[cfg(guarded_remove)]
pub fn remove_at(v: &mut Vec<u32>, i: usize) -> u32 {
    if i < v.len() { v.remove(i) } else { 0 }
}

#[cfg(unguarded)]
pub fn remove_any(v: &mut Vec<u32>, i: usize) -> u32 {
    v.remove(i)
}

#[cfg(off_by_one)]
pub fn remove_le(v: &mut Vec<u32>, i: usize) -> u32 {
    if i <= v.len() { v.remove(i) } else { 0 }
}

#[cfg(two_resizes)]
pub fn remove_twice(v: &mut Vec<u32>) -> u32 {
    let n = v.len();
    if n == 0 {
        return 0;
    }
    v.remove(0);
    v.remove(n - 1)
}

#[cfg(looped)]
pub fn drain_at(v: &mut Vec<u32>, i: usize) {
    while i < v.len() {
        v.swap_remove(i);
    }
}

#[cfg(use_after)]
pub fn remove_then_len(v: &mut Vec<u32>, i: usize) -> usize {
    if i < v.len() {
        v.remove(i);
        v.len()
    } else {
        0
    }
}

#[cfg(guarded_insert)]
pub fn insert_at(v: &mut Vec<u32>, i: usize) {
    if i <= v.len() {
        v.insert(i, 7);
    }
}

#[cfg(field_receiver)]
pub struct Stack {
    pub items: Vec<u32>,
}

#[cfg(field_receiver)]
pub fn pop_at(s: &mut Stack, i: usize) -> u32 {
    if i < s.items.len() { s.items.remove(i) } else { 0 }
}

#[cfg(any(user_trait_spelled_std, stale_len_tie_user_trait))]
pub trait Evil {
    fn index(v: &mut Vec<u32>, i: usize) -> usize;
}

#[cfg(any(user_trait_spelled_std, stale_len_tie_user_trait))]
impl Evil for core::ops::Range<usize> {
    fn index(v: &mut Vec<u32>, _i: usize) -> usize {
        v.clear();
        0
    }
}

#[cfg(user_trait_spelled_std)]
pub fn cleared_then_removed(v: &mut Vec<u32>, i: usize) -> u32 {
    if i < v.len() {
        <core::ops::Range<usize> as Evil>::index(v, 0);
        v.remove(i)
    } else {
        0
    }
}

#[cfg(stale_len_tie_user_trait)]
pub fn cleared_then_indexed(v: &mut Vec<u32>) -> u32 {
    let n = v.len();
    if n == 0 {
        return 0;
    }
    <core::ops::Range<usize> as Evil>::index(v, 0);
    v[n - 1]
}
