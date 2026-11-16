//@ revisions: on off
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[off] compile-flags: -Ztrust-no-adapter-yield
//@[on] check-pass
//@[off] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! `ADAPTER_YIELD` (2026-10-08) over a slice receiver under a stack of core
//! adapters that hand on only inner items, unchanged (`filter`, `rev`, `skip`,
//! `take`, `step_by`, and `enumerate`, whose item is `(index, slice)`), and over
//! `windows`/`chunks`/`chunks_exact` with a NON-constant
//! size (every item is non-empty: the constructor panics on zero). Each was
//! refused on the ordinary-Rust sweep (`m07_windows_filter_any`,
//! `n06_windows_rev_any`, `n13_windows_k_param`).
//!
//! The `off` revision (`-Ztrust-no-adapter-yield`) refuses every closure.

pub fn filter_any(v: &[u8]) -> bool {
    v.windows(2).filter(|w| w[1] > 0).any(|w| w[0] == 0)
}

pub fn rev_any(v: &[u32]) -> bool {
    v.windows(2).rev().any(|w| w[0] > w[1])
}

pub fn skip_take_all(v: &[u32]) -> bool {
    v.windows(3).skip(1).take(2).all(|w| w[2] >= w[0])
}

pub fn step_by_chunks_exact(v: &[u32]) -> bool {
    v.chunks_exact(2).step_by(2).any(|c| c[1] == 0)
}

pub fn runtime_window(v: &[u8], k: usize) -> bool {
    if k == 0 {
        return false;
    }
    v.windows(k).any(|w| w[0] == 0)
}

pub fn runtime_chunks_position(v: &[u8], k: usize) -> Option<usize> {
    if k == 0 {
        return None;
    }
    v.chunks(k).position(|c| c[0] == 0)
}

pub fn runtime_chunks_exact_all(v: &[u8], k: usize) -> bool {
    if k == 0 {
        return false;
    }
    v.chunks_exact(k).all(|c| c[0] < 200)
}

pub fn enumerate_any(v: &[u32]) -> bool {
    v.windows(2).enumerate().any(|(_, w)| w[0] > w[1])
}

pub fn enumerate_filter_position(v: &[u32]) -> Option<usize> {
    v.windows(3).enumerate().filter(|(_, w)| w[1] > 0).position(|(_, w)| w[2] == w[0])
}

pub fn range_enumerate_all(a: &[u8; 8]) -> bool {
    (0..8usize).enumerate().all(|(_, i)| a[i] == 0)
}
