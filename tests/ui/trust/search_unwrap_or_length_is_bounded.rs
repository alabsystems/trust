//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
#![crate_type = "lib"]
//! `v.iter().position(p).unwrap_or(v.len())` and `s.find(c).unwrap_or(s.len())` are
//! at most the length, and the `str` one is a char boundary: each is either a search
//! result or the length itself.
//!
//! MEASURED OVER-REFUSAL, 2026-09-29 (z03 of the ordinary-Rust sweep):
//! `&v[v.iter().position(|&x| x == 0).unwrap_or(v.len())..]` was refuted with the
//! result 1 and the length 0: the `unwrap_or` result carried nothing of the search.
//! The refusing twins are in `search_unwrap_or_length_is_bounded_refused.rs`. The
//! slice rows prove; the search call's own panic-freedom keeps its runtime check on
//! the default lane.

pub fn from_zero(v: &[u8]) -> &[u8] {
    let i = v.iter().position(|&x| x == 0).unwrap_or(v.len());
    &v[i..]
}

pub fn first_field(s: &str) -> &str {
    &s[..s.find(',').unwrap_or(s.len())]
}

pub fn after_last_slash(s: &str) -> &str {
    let i = s.rfind('/').unwrap_or(0);
    &s[i..]
}
