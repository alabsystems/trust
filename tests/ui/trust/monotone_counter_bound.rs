//@ needs-trust-verify
//@ edition: 2021
//@ revisions: tables down_index wrapping wrapping_o1 decremented
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[tables] check-pass
//@[down_index] check-pass
//@[wrapping] check-fail
//@[wrapping_o1] check-fail
//@[wrapping_o1] compile-flags: -Copt-level=1 -Coverflow-checks=on
//@[decremented] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! Trust (2026-10-04, monotone counters): a local whose every value is a constant, a
//! copy, or a CHECKED `x + d` (`d >= 0`, guarded by rustc's overflow assert) is at least
//! its smallest constant at every read; with checked `x - d` it is at most its largest
//! (`callee_summaries::local_value_monotone_bounds`).
//!
//! # Before (measured on the stage 1 of `072eb4d419`, 2026-10-04)
//!
//! `tables` (astream_wire `crc32_tables`): `k - 1` was `[overflow:sub] FAILED` with
//! `k = 0`.
//!
//! # The refused rails, each a program that really panics
//!
//! * `wrapping`, `wrapping_o1` — `k.overflowing_add(usize::MAX)` wraps `k` to 0 and
//!   `k - 1` underflows. Measured: at -O0 and -O1 the verified body keeps it a CALL,
//!   which refuses on its own; the unguarded checked-tuple shape it lowers to once
//!   inlined is pinned at the crate level (`crates/trust-vcgen/tests/
//!   monotone_counter_realmir.rs`, which fails with the assert guard disabled).
//! * `decremented` — a checked `k -= 1` breaks the lower bound; `k - 1` underflows.

#[cfg(tables)]
pub const fn tables() -> [u32; 8] {
    let mut t = [0u32; 8];
    let mut k = 1usize;
    while k < 8 {
        t[k] = t[k - 1] ^ 1;
        k += 1;
    }
    t
}

#[cfg(down_index)]
pub fn down_index(a: &[u8; 8], c: &[bool; 64]) -> u8 {
    let mut j = 7usize;
    let mut n = 0usize;
    while j > 0 && n < 64 && c[n] {
        j -= 1;
        n += 1;
    }
    a[j]
}

#[cfg(any(wrapping, wrapping_o1))]
pub fn wrapping() -> usize {
    let mut k = 1usize;
    let (v, _) = k.overflowing_add(usize::MAX);
    k = v;
    k - 1
}

#[cfg(decremented)]
pub fn decremented(c: bool) -> usize {
    let mut k = 1usize;
    if c {
        k -= 1;
    }
    k - 1
}
