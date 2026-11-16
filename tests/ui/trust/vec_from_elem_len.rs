//@ needs-trust-verify
//@ edition: 2021
//@ revisions: idx last off_by_one reassigned cleared loop_header opaque_assoc
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[idx] check-pass
//@[last] check-pass
//@[off_by_one] check-fail
//@[reassigned] check-fail
//@[cleared] check-fail
//@[loop_header] check-fail
//@[opaque_assoc] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! Trust (2026-10-05, VEC_FROM_ELEM_LEN): `vec![x; n]` has length `n`
//! (`generate::call_facts::vec_from_elem_len_facts`).
//!
//! # Before (measured on the stage 1 of `3733cf32b1`, 2026-10-05)
//!
//! `idx` and `last`: the guarded index was `[slice] FAILED` (the length was unconstrained).
//! Both bound `n` first only so that the separate `unbounded allocation` row of
//! `vec![x; n]` (a real obligation for an unbounded `n`) discharges too.
//!
//! # The refused rails, each a program that really panics
//!
//! * `off_by_one` — guard `i <= n`; `v[n]` is out of bounds.
//! * `reassigned` — `v = vec![0; 1]` after the macro; `v[i]` with `1 <= i < n`.
//! * `cleared` — `v.clear()` after the macro; `v[i]` with `i < n`.
//! * `loop_header`, `opaque_assoc` — the two false proofs the 2026-10-05 adversarial review
//!   found in the first version of this fact: the call returning straight into a `while`
//!   header (whose phi covers the cleared vector), and two identity-less associated
//!   constants sharing one SMT term (`opaque_assoc::<Ten, One>(5)` panics).

#[cfg(idx)]
pub fn idx(n: usize, i: usize) -> u8 {
    if n > 4096 {
        return 0;
    }
    let v = vec![7u8; n];
    if i < n { v[i] } else { 0 }
}

#[cfg(last)]
pub fn last(n: usize) -> u8 {
    if n > 4096 {
        return 0;
    }
    let v = vec![7u8; n];
    if n > 0 { v[n - 1] } else { 0 }
}

#[cfg(off_by_one)]
pub fn off_by_one(n: usize, i: usize) -> u8 {
    let v = vec![7u8; n];
    if i <= n { v[i] } else { 0 }
}

#[cfg(reassigned)]
pub fn reassigned(n: usize, i: usize) -> u8 {
    let mut v = vec![7u8; n];
    v = vec![0u8; 1];
    if i < n { v[i] } else { 0 }
}

#[cfg(cleared)]
pub fn cleared(n: usize, i: usize) -> u8 {
    let mut v = vec![7u8; n];
    v.clear();
    if i < n { v[i] } else { 0 }
}

#[cfg(loop_header)]
pub fn loop_header(more: fn() -> bool) -> u8 {
    let mut v = vec![0u8; 4];
    while more() {
        v.clear();
    }
    v[0]
}

#[cfg(opaque_assoc)]
pub trait K {
    const N: usize;
}

#[cfg(opaque_assoc)]
pub fn opaque_assoc<A: K, B: K>(i: usize) -> u8 {
    let v = vec![7u8; B::N];
    if i < A::N { v[i] } else { 0 }
}
