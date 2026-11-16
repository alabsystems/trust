//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//! A range whose END is a slice's length runs at most `isize::MAX` times when the
//! element is non-zero-sized, the bound the slice-iterator trip count already uses.
//! The range form had no trip count, so a counter was refuted at `usize::MAX`
//! (sweep `q18`). The twin keeps a counter that can really overflow refused.
//! `even_zeros` is the sweep shape: its counter now proves, but `step_by`'s own
//! absent-callee panic aggregate stays runtime-checked, an advisory under the
//! default policy and an error under certify, so it is compiled only by `default`.
#[cfg(default)]
pub fn even_zeros(v: &[u8]) -> usize {
    let mut c = 0usize;
    for i in (0..v.len()).step_by(2) {
        if v[i] == 0 {
            c += 1;
        }
    }
    c
}

pub fn zeros(v: &[u8]) -> usize {
    let mut c = 0usize;
    for i in 0..v.len() {
        if v[i] == 0 {
            c += 1;
        }
    }
    c
}

pub fn count_all(v: &[u32]) -> usize {
    let mut c = 0usize;
    for _ in 0..v.len() {
        c += 1;
    }
    c
}

/// Starting at 1, `isize::MAX` trips of `+= 1` stay within `usize::MAX`; the
/// raw-pointer twin in `_refused.rs` is the same loop without that bound.
pub fn from_one(v: &[u32]) -> usize {
    let mut c = 1usize;
    for _ in 0..v.len() {
        c += 1;
    }
    c
}
