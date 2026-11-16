//@ revisions: on off
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[off] compile-flags: -Ztrust-no-adapter-yield
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! `ADAPTER_YIELD` (2026-10-08): what the widened receiver stack must NOT
//! prove. Each closure below PANICS on some input and stays refused in BOTH
//! revisions:
//!
//! * `runtime_size` — `windows(k)` with a runtime `k`: the premise gives only
//!   `len >= 1`, and `w[1]` panics for `k = 1`.
//! * `chunks_tail` — `chunks(k)` runtime: the last chunk can have length 1.
//! * `filter_does_not_narrow` — `filter` keeps the length fact, it does not
//!   add the predicate's: `w[2]` on a 2-window panics.
//! * `enumerate_keeps_the_length` — `enumerate` moves the fact to field 1 of
//!   the item and keeps it exact: `w[2]` on a 2-window panics.
//! * `enumerate_index_is_unbounded` — field 0, the counter, gets no fact:
//!   `w[i]` panics once `i >= 2`.

pub fn runtime_size(v: &[u32], k: usize) -> bool {
    if k == 0 {
        return false;
    }
    v.windows(k).all(|w| w[0] <= w[1])
    //~^ NOTE [slice] FAILED
}

pub fn chunks_tail(v: &[u32], k: usize) -> bool {
    if k == 0 {
        return false;
    }
    v.chunks(k).any(|c| c[1] == 0)
    //~^ NOTE [slice] FAILED
}

pub fn filter_does_not_narrow(v: &[u8]) -> bool {
    v.windows(2).filter(|w| w.len() > 2).any(|w| w[2] == 0)
    //~^ NOTE [slice] FAILED
}

pub fn enumerate_keeps_the_length(v: &[u8]) -> bool {
    v.windows(2).enumerate().any(|(_, w)| w[2] == 0)
    //~^ NOTE [slice] FAILED
}

pub fn enumerate_index_is_unbounded(v: &[u8]) -> bool {
    v.windows(2).enumerate().any(|(i, w)| w[i] == 0)
    //~^ NOTE [slice] FAILED
}
