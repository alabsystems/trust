//@ needs-trust-verify
//@ edition: 2021
//@ revisions: plus_one index_u32 rposition_plus bytes_rposition other_slice join_max reseated
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[plus_one] check-pass
//@[index_u32] check-pass
//@[rposition_plus] check-pass
//@[bytes_rposition] check-pass
//@[other_slice] check-fail
//@[join_max] check-fail
//@[reseated] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! Trust (STR_BYTES_POSITION_BOUND widened, 2026-10-04): the `Some(i)` of
//! `v.iter().position(..)` / `rposition(..)` over a shared slice, and of
//! `s.bytes().rposition(..)`, is below the length (`docs/TCB.md`).
//!
//! # Before (measured on the stage 1 of `6e497d8b2c`, 2026-10-04)
//!
//! `plus_one` and `rposition_plus` were `[overflow:add] FAILED` and `index_u32` was
//! `[slice] FAILED`.
//!
//! # The refused rails, each a program that really panics
//!
//! * `other_slice` — `v`'s index used on a shorter `w`.
//! * `join_max` — `None => usize::MAX`, then `i + 1` overflows.
//! * `reseated` — the iterator is reseated to a longer slice through `&mut`.

#[cfg(plus_one)]
pub fn plus_one(v: &[u8]) -> usize {
    match v.iter().position(|&b| b == 7) {
        Some(i) => i + 1,
        None => 0,
    }
}

#[cfg(index_u32)]
pub fn index_u32(v: &[u32]) -> u32 {
    match v.iter().position(|&x| x > 3) {
        Some(i) => v[i],
        None => 0,
    }
}

#[cfg(rposition_plus)]
pub fn rposition_plus(v: &[u16]) -> usize {
    match v.iter().rposition(|&x| x == 9) {
        Some(i) => i + 1,
        None => 0,
    }
}

#[cfg(bytes_rposition)]
pub fn bytes_rposition(s: &str) -> usize {
    match s.bytes().rposition(|b| b == b'.') {
        Some(i) => i + 1,
        None => 0,
    }
}

#[cfg(other_slice)]
pub fn other_slice(v: &[u32], w: &[u32]) -> u32 {
    match v.iter().position(|&x| x > 3) {
        Some(i) => w[i],
        None => 0,
    }
}

#[cfg(join_max)]
pub fn join_max(v: &[u8]) -> usize {
    let i = match v.iter().position(|&b| b == 7) {
        Some(i) => i,
        None => usize::MAX,
    };
    i + 1
}

#[cfg(reseated)]
pub fn reseated(v: &[u32], w: &'static [u32]) -> u32 {
    let mut it = v.iter();
    let p = &mut it;
    *p = w.iter();
    match it.position(|&x| x > 3) {
        Some(i) => v[i],
        None => 0,
    }
}
