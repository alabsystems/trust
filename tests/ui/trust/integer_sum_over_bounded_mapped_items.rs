//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@[default] compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//! `Iterator::sum` into a primitive integer over a `map` whose closure's return
//! interval is known and whose source's item count is bounded: the fold row's
//! items come from the closure's summary and its count from the array length or
//! `take(n)`, and std's `Sum` body is no longer bundled (its member assert refused
//! the whole bundle). Sweep A10 (r03, p31, r33). The twin `_refused.rs` keeps an
//! overflowing sum refused.
pub fn widen_sum(a: &[u32; 4]) -> u64 {
    a.iter().map(|&x| x as u64).sum()
}

pub fn byte_sum(a: &[u8; 4]) -> u32 {
    a.iter().map(|&b| b as u32).sum()
}

pub fn take_sum(v: &[u8]) -> u64 {
    v.iter().take(1000).map(|&b| b as u64).sum()
}

fn widen(b: u8) -> u32 {
    b as u32
}

pub fn fn_item_sum(a: &[u8; 4]) -> u32 {
    a.iter().copied().map(widen).sum()
}

/// A capturing closure constructed in this body lends its summary too.
pub fn capturing_sum(a: &[u32; 4], k: u8) -> u64 {
    a.iter().map(|&x| x as u64 + k as u64).sum()
}
