//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
#![crate_type = "lib"]
//! `s.len()` on a `&str` is the length every index and range slice of `s` is
//! checked against.
//!
//! MEASURED OVER-REFUSAL, 2026-09-29: each function below was refuted, e.g.
//! `byte_at_inline` with `s = 1`, `s__slice_len = 0`. A `&str` is extracted as a
//! `&[u8]`, whose `len()` rustc lowers to the fat pointer's metadata, but `str::len`
//! stayed a call, and its result was tied to a second length name that nothing
//! else read. The extractor now lowers it the same way. The `&String` twins proved
//! before. The refusing twins are in `str_len_is_the_slice_length_refused.rs`.

pub fn byte_at(s: &str, i: usize) -> u8 {
    let n = s.len();
    if i < n { s.as_bytes()[i] } else { 0 }
}

pub fn byte_at_inline(s: &str, i: usize) -> u8 {
    if i < s.len() { s.as_bytes()[i] } else { 0 }
}

pub fn last_byte(s: &str) -> u8 {
    if s.is_empty() { 0 } else { s.as_bytes()[s.len() - 1] }
}

pub fn tail(s: &str, k: usize) -> &[u8] {
    if k <= s.len() { &s.as_bytes()[s.len() - k..] } else { s.as_bytes() }
}
