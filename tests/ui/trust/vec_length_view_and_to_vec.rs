//@ needs-trust-verify
//@ edition: 2021
//@ revisions: to_vec_index to_vec_len sort_then_guard as_slice_view iter_view to_vec_wrong sort_then_pop iter_after_push
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[to_vec_index] check-pass
//@[to_vec_len] check-pass
//@[sort_then_guard] check-pass
//@[as_slice_view] check-pass
//@[iter_view] check-pass
//@[iter_view] rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//@[to_vec_wrong] check-fail
//@[sort_then_pop] check-fail
//@[iter_after_push] check-fail
//! **The `Vec` length equations (VEC-AS-SLICE (b), Trust 2026-09-25).**
//!
//! Three std facts tie a `Vec`'s abstract length `coll_len(v)` to the slices around
//! it (`guards::slice_last_some_nonempty_definitions`; premises in docs/TCB.md):
//! `Vec`'s own `deref`/`as_slice` view has the `Vec`'s length; `v = xs.to_vec()` has
//! `xs`'s; and a `&mut v` consumed only by `Vec`'s own `deref_mut` (`v.sort()`)
//! cannot change it. Each is minted only under the `.len()` tie's gates — a
//! uniquely traced base whose length is stable for the whole body.
//!
//! # Before (stage 1 `0.10.0+gb4bc7cdf9`, 2026-09-25)
//!
//! Every revision was rc=1 on the bundled-member Assert gate (`refused Assert-bearing
//! transitive member `<usize as core::slice::index::SliceIndex<[u32]>>::index``),
//! except `iter_view`/`iter_after_push`, which index an ARRAY and were refused on
//! `[bounds] FAILED` (the iterated slice's length unrelated to `v.len()`).
//!
//! # After
//!
//! The check-pass revisions build; each check-fail revision is refused on its own
//! row. `sort_then_pop` and `iter_after_push` resize the `Vec`, so no equation is
//! minted for it at all: the first index is the never-provable
//! `container-index-unstable-len` row, the second an unrelated `[bounds]` length.
//! Since SRH-1 S3 (2026-10-20) that `[bounds]` row is `UNKNOWN`, its counterexample
//! withheld: it rests on `enumerate`'s unmodelled `Some` payload. Main refuted it
//! with `i = 2` over a 3-element slice, a real execution, but nothing in the query
//! ties the payload to the slice, so the solver's value was free; the build is
//! still refused, and the lost counterexample is DECISION_QUEUE SRH-1's measured
//! capability cost (recovery: an `enumerate` index below the slice length).
//!
//! `iter_view` runs with `TRUST_NO_SYSROOT_CENSUS=1` (2026-10-08, std-absent-callee):
//! its NOTE pins the obligation COUNT, and withholding the census (it only removes
//! proof) keeps that count the bridge's own. Until 2026-10-20 the count held one
//! runtime-checked absent-callee row, for `<Vec<u32> as Deref>::deref` (the `v.iter()`
//! auto-deref), which the census removed. Since 3e62fb1ff13 the bridge classifies that
//! call total itself (`is_vec_deref_slice_callee`: coherence leaves alloc's own impl as
//! the only one, and its body is `&*aggregate_raw_ptr(ptr, len)`, with no branch and no
//! user code), so the row is never minted: three obligations, with or without the census.

#[cfg(to_vec_index)]
pub fn first_copy(xs: &[u32]) -> u32 {
    //[to_vec_index]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 3 obligation(s)
    let v = xs.to_vec();
    if !xs.is_empty() { v[0] } else { 0 }
}

#[cfg(to_vec_len)]
pub fn third_copy(xs: &[u32]) -> u32 {
    //[to_vec_len]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 3 obligation(s)
    if xs.len() < 3 {
        return 0;
    }
    let v = xs.to_vec();
    v[2]
}

#[cfg(sort_then_guard)]
pub fn sorted_at(xs: &[u32], i: usize) -> u32 {
    //[sort_then_guard]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 3 obligation(s)
    let mut v = xs.to_vec();
    v.sort_unstable();
    if i < v.len() { v[i] } else { 0 }
}

#[cfg(as_slice_view)]
pub fn third(v: &Vec<u32>) -> u32 {
    //[as_slice_view]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    let s = v.as_slice();
    if v.len() > 2 { s[2] } else { 0 }
}

#[cfg(iter_view)]
pub fn into_array(v: &Vec<u32>) -> u32 {
    //[iter_view]~^ NOTE Trust verification: 3 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 3 obligation(s)
    let mut t = [0u32; 4];
    if v.len() > 4 {
        return 0;
    }
    for (i, x) in v.iter().enumerate() {
        t[i] = *x;
    }
    t[0]
}

#[cfg(to_vec_wrong)]
pub fn copy_at(xs: &[u32], ys: &[u32], i: usize) -> u32 {
    //[to_vec_wrong]~^ NOTE [slice] FAILED
    let v = xs.to_vec();
    if i < ys.len() { v[i] } else { 0 }
}

#[cfg(sort_then_pop)]
pub fn sorted_last(xs: &[u32]) -> u32 {
    //[sort_then_pop]~^ NOTE unsupported MIR `container-index-unstable-len`
    if xs.is_empty() {
        return 0;
    }
    let mut v = xs.to_vec();
    v.sort();
    v.pop();
    v[xs.len() - 1]
}

#[cfg(iter_after_push)]
pub fn pushed_into_array(mut v: Vec<u32>) -> u32 {
    //[iter_after_push]~^ NOTE [bounds] UNKNOWN (trust-full-verifier): generic solver counterexample withheld: query rests on the unmodelled return of a foreign call
    let mut t = [0u32; 2];
    if v.len() != 2 {
        return 0;
    }
    v.push(1);
    for (i, x) in v.iter().enumerate() {
        t[i] = *x;
    }
    t[0]
}
