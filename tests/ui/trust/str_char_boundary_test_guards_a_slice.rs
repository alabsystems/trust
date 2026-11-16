//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
#![crate_type = "lib"]
//! On a path where `s.is_char_boundary(n)` held, `n` is a char boundary of `s` and at
//! most its length, so `&s[..n]` and `&s[n..]` cannot panic.
//!
//! MEASURED OVER-REFUSAL, 2026-09-29 (p59 of the ordinary-Rust sweep): `prefix` was
//! refuted, a str slice endpoint having to be 0 or an index the string itself
//! yielded. The refusing twins are in `str_char_boundary_test_guards_a_slice_refused.rs`.

pub fn prefix(s: &str, n: usize) -> &str {
    if n <= s.len() && s.is_char_boundary(n) { &s[..n] } else { s }
}

pub fn suffix(s: &str, n: usize) -> &str {
    if s.is_char_boundary(n) { &s[n..] } else { "" }
}

pub fn middle(s: &str, a: usize, b: usize) -> &str {
    if a <= b && s.is_char_boundary(a) && s.is_char_boundary(b) { &s[a..b] } else { "" }
}
