//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//! `v.iter().flatten()` over a slice of std `Option`s or `Result`s yields at most
//! one item per element, so at most `v.len()` items. The flatten had no trip count,
//! so a counter in its loop was refuted at `usize::MAX` (sweep `c45`). The twin
//! `_refused.rs` keeps a flatten over many-item elements unbounded.
//! Default policy only: under certify the std call's own absent-callee panic
//! aggregate (`Flatten::next`) stays runtime-checked, a separate gap.
pub fn count_some(v: &[Option<u32>]) -> usize {
    let mut n = 0usize;
    for x in v.iter().flatten() {
        if *x > 0 {
            n += 1;
        }
    }
    n
}

pub fn count_ok(v: &[Result<u8, ()>]) -> usize {
    let mut n = 1usize;
    for _ in v.iter().flatten() {
        n += 1;
    }
    n
}
