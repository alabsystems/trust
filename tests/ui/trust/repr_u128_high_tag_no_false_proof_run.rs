//@ revisions: idx add agg cast
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -Coverflow-checks=on
//@ run-fail
//@[idx] error-pattern: index out of bounds: the len is 1 but the index is 1
//@[add] error-pattern: attempt to add with overflow
//@[agg] error-pattern: attempt to add with overflow
//@[cast] error-pattern: index out of bounds: the len is 4 but the index is 4
//@ ignore-emscripten no processes
//! The runtime WITNESS for `repr_u128_high_tag_no_false_proof.rs`
//! (REPR-U128-HIGH-TAG-1): the same enums and the same `index_arm`, `add_arm`,
//! `local_aggregate` and `cast_index`, built with verification OFF and driven into
//! the arm of the variant whose tag is `u128::MAX`. Before the fix the sibling's
//! `default` and `certify` revisions PROVED the row of each of these arms.
//!
//! MEASURED 2026-10-11 on `scratchpad/stage1-w22probe` with these flags: every
//! revision panics with its pattern and exits 101. The binary does not depend on the
//! verifier, so the fix does not change it; the file pins the fact the sibling's
//! annotations rest on.

use std::hint::black_box;

#[repr(u128)]
#[derive(Clone, Copy)]
pub enum E {
    A = 0,
    B = u128::MAX,
    C = 5,
}

#[repr(u128)]
#[derive(Clone, Copy)]
pub enum K {
    A = 0,
    B = u128::MAX,
    C = 3,
}

#[inline(never)]
pub fn index_arm(e: E, a: &[u8; 1], i: usize) -> u8 {
    match e {
        E::B => a[i],
        _ => 0,
    }
}

#[inline(never)]
pub fn add_arm(e: E, x: u8) -> u8 {
    if let E::B = e { x + 1 } else { 0 }
}

#[inline(never)]
pub fn local_aggregate(b: bool, x: u8) -> u8 {
    let e = if b { E::B } else { E::A };
    match e {
        E::B => x + 1,
        _ => 0,
    }
}

#[inline(never)]
pub fn cast_index(e: K, a: &[u8; 4]) -> u8 {
    let d = e as u128;
    if d > 3 { a[(d - u128::MAX + 4) as usize] } else { 0 }
}

fn main() {
    // The tag really is `u128::MAX`: no wrap, no `-1`.
    assert_eq!(black_box(E::B) as u128, u128::MAX);
    #[cfg(idx)]
    println!("{}", index_arm(black_box(E::B), &[7], black_box(1)));
    #[cfg(add)]
    println!("{}", add_arm(black_box(E::B), black_box(255)));
    #[cfg(agg)]
    println!("{}", local_aggregate(black_box(true), black_box(255)));
    #[cfg(cast)]
    println!("{}", cast_index(black_box(K::B), &[1, 2, 3, 4]));
}
