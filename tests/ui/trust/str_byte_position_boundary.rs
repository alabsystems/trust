//@ needs-trust-verify
//@ edition: 2021
//@ revisions: tail tail_o1 head from split reversed loop_reentry prior_next non_ascii_k not_eq other_root plus_two off_switch
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[tail] check-pass
//@[tail_o1] check-pass
//@[tail_o1] compile-flags: -Copt-level=1 -Coverflow-checks=on
//@[head] check-pass
//@[from] check-pass
//@[split] check-pass
//@[reversed] check-pass
//@[loop_reentry] check-fail
//@[prior_next] check-fail
//@[non_ascii_k] check-fail
//@[not_eq] check-fail
//@[other_root] check-fail
//@[plus_two] check-fail
//@[off_switch] check-fail
//@[off_switch] compile-flags: -Ztrust-no-str-byte-position
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! Trust (STR_BYTE_POSITION, 2026-10-04): when the predicate of
//! `s.bytes().position(..)` is a capture-free closure whose whole body is
//! `b == K` with an ASCII `K`, the index `i` it returns is an exact one-byte match:
//! `i` and `i + 1` are char boundaries of `s`. The compiler certifies the closure
//! and the call (`rustc_mir_transform`'s `trust_verify/byte_eq_predicate.rs`);
//! vcgen requires a fresh iterator consumed by one dynamic execution of the call
//! (`generate::str_offset`, `bytes_position_origin`). `docs/TCB.md` has the premise.
//!
//! # Before (measured on the stage 1 of `33c5b92355`, 2026-10-04)
//!
//! `tail`: `&rest[i + 1..]`'s str slice row FAILED (the char-boundary fail-close);
//! its `i + 1` row already proved (STR_BYTES_POSITION_BOUND).
//!
//! # The refused rails, each a program that really panics
//!
//! * `loop_reentry` — `"a/é/"`: the second `position` on the same iterator returns
//!   `2`, relative to the remaining `"é/"`, and `&s[3..]` cuts `é`.
//! * `prior_next` — `"xé/"`: after `next()`, `position` returns `2`; `&s[2..]` cuts `é`.
//! * `non_ascii_k` — `K = 0xC3` on `"é"`: `i = 0`, `&s[1..]` cuts `é`.
//! * `not_eq` — `b != b'/'` on `"é"`: `i = 0`, `&s[1..]` cuts `é`.
//! * `other_root` — `a`'s index used on `b = "é"`.
//! * `plus_two` — `"/é"`: `i = 0`, `&s[2..]` cuts `é`.
//! * `off_switch` — `tail` under `-Ztrust-no-str-byte-position` (the negative control).

#[cfg(any(tail, tail_o1, off_switch))]
pub fn tail(rest: &str) -> &str {
    match rest.bytes().position(|b| b == b'/') {
        Some(i) => &rest[i + 1..],
        None => rest,
    }
}

#[cfg(head)]
pub fn head(s: &str) -> &str {
    match s.bytes().position(|b| b == b':') {
        Some(i) => &s[..i],
        None => s,
    }
}

#[cfg(from)]
pub fn from(s: &str) -> &str {
    match s.bytes().position(|b| b == b'#') {
        Some(i) => &s[i..],
        None => s,
    }
}

#[cfg(split)]
pub fn split(s: &str) -> (&str, &str) {
    match s.bytes().position(|b| b == b'=') {
        Some(i) => s.split_at(i),
        None => (s, ""),
    }
}

#[cfg(reversed)]
pub fn reversed(s: &str) -> &str {
    match s.bytes().position(|b| b'/' == b) {
        Some(i) => &s[i + 1..],
        None => s,
    }
}

#[cfg(loop_reentry)]
pub fn loop_reentry(s: &str) -> &str {
    let mut it = s.bytes();
    let mut out = s;
    while let Some(i) = it.position(|b| b == b'/') {
        out = &s[i + 1..];
    }
    out
}

#[cfg(prior_next)]
pub fn prior_next(s: &str) -> &str {
    let mut it = s.bytes();
    it.next();
    match it.position(|b| b == b'/') {
        Some(i) => &s[i..],
        None => s,
    }
}

#[cfg(non_ascii_k)]
pub fn non_ascii_k(s: &str) -> &str {
    match s.bytes().position(|b| b == 0xC3) {
        Some(i) => &s[i + 1..],
        None => s,
    }
}

#[cfg(not_eq)]
pub fn not_eq(s: &str) -> &str {
    match s.bytes().position(|b| b != b'/') {
        Some(i) => &s[i + 1..],
        None => s,
    }
}

#[cfg(other_root)]
pub fn other_root<'a>(a: &str, b: &'a str) -> &'a str {
    match a.bytes().position(|c| c == b'/') {
        Some(i) => &b[i..],
        None => b,
    }
}

#[cfg(plus_two)]
pub fn plus_two(s: &str) -> &str {
    match s.bytes().position(|b| b == b'/') {
        Some(i) => &s[i + 2..],
        None => s,
    }
}
