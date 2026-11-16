//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
#![crate_type = "lib"]
//! `drain(..)` and `drain(0..)` on a std `Vec` or `String` drain
//! `0..len`, which is always in range, so they cannot panic.
//!
//! MEASURED OVER-REFUSAL, 2026-09-29, on the ordinary-Rust sweep: each function
//! below failed the build on a `Call::drain::panic-freedom-unverified` Unknown row,
//! which vcgen mints for every range-taking `drain` because an out-of-range bound
//! panics. The row is now withheld when the range is provably the whole receiver
//! (`unwrap_panic::drain_range_is_whole`); any other range keeps it —
//! `whole_range_drain_cannot_panic_refused.rs` holds ranges that do panic.
//!
//! `VecDeque::drain(..)` loses the row too, but still fails on the drop glue of
//! `vec_deque::Drain`, which is not in the credited drop-glue set; it is not
//! pinned here.

pub fn clear_all(v: &mut Vec<u32>) {
    v.drain(..);
}

pub fn clear_from_zero(v: &mut Vec<u32>) {
    v.drain(0..);
}

pub fn drain_max(v: &mut Vec<u32>) -> u32 {
    let mut m = 0u32;
    for x in v.drain(..) {
        if x > m {
            m = x;
        }
    }
    m
}

pub fn clear_string(s: &mut String) {
    s.drain(..);
}
