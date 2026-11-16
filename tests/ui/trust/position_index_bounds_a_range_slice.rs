//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
#![crate_type = "lib"]
//! The index `position` returns bounds a RANGE slice of the same slice.
//!
//! MEASURED OVER-REFUSAL, 2026-09-29, on the ordinary-Rust sweep (m11):
//! `match v.iter().position(p) { Some(i) => &v[..i], None => v }` was refuted with
//! the `Some` payload above the length. `position_index_is_below_the_length.rs`
//! bounds the copied index `i`, but a range index resolves its end through the copy
//! to the payload place `(o as Some).0`, which had no bound. It now carries the same
//! one (`container_len::build_position_yield_guard_map`). The range rows prove; the
//! `position` call's own panic-freedom keeps its runtime check on the default lane.

pub fn before_zero(v: &[u8]) -> &[u8] {
    match v.iter().position(|&b| b == 0) {
        Some(i) => &v[..i],
        None => v,
    }
}

pub fn from_zero(v: &[u8]) -> &[u8] {
    match v.iter().position(|&b| b == 0) {
        Some(i) => &v[i..],
        None => v,
    }
}

pub fn after_last_zero(v: &[u8]) -> &[u8] {
    match v.iter().rposition(|&b| b == 0) {
        Some(i) => &v[i + 1..],
        None => v,
    }
}
