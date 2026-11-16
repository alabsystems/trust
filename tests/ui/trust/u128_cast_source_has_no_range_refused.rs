//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! A `u128` has no range the interval domain can represent, so a cast from one
//! carries none. Every function below panics for `x >= 2^127`.
//!
//! MEASURED FALSE PROOFS, 2026-09-30 (round 10 of the callee-summary review): the
//! domain seeded a `u128` with `[0, i128::MAX]`, which excludes every value at or
//! above 2^127, and the new cast transfer kept that interval through `x as i128`.
//! `y < 0` was then unreachable, and the index and the division below were PROVED
//! and kernel-certified. `type_to_interval` now answers `None` for `u128`, as
//! `discharge::type_bounds` already did (P1-12).

pub fn index_by_sign(a: &[u8; 1], x: u128) -> u8 { //~ ERROR strict verification failed for `u128_cast_source_has_no_range_refused::index_by_sign`
    let y = x as i128;
    let i = if y < 0 { 5usize } else { 0usize };
    a[i]
}

pub fn divide_by_sign(x: u128) -> u32 { //~ ERROR strict verification failed for `u128_cast_source_has_no_range_refused::divide_by_sign`
    let y = x as i128;
    let d: u32 = if y < 0 { 0 } else { 1 };
    100 / d
}

fn to_i128(x: u128) -> i128 {
    x as i128
}

pub fn index_by_summary(a: &[u8; 1], x: u128) -> u8 { //~ ERROR strict verification failed for `u128_cast_source_has_no_range_refused::index_by_summary`
    let y = to_i128(x);
    let i = if y < 0 { 5usize } else { 0usize };
    a[i]
}
