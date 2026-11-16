//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! Reading an enum's discriminant as a SIGNED integer of the repr's width is not
//! value-preserving: `A = u64::MAX` read `as i64` is -1. Every function below
//! indexes out of bounds for `A`.
//!
//! MEASURED FALSE PROOFS (round 10 of the callee-summary review, 2026-09-30; older
//! than it, the 2026-09-19 stage 2 proves them too): the discriminant-cast lane
//! stated `_d == e_disc` whenever the destination was at least as wide as the repr
//! and every discriminant was non-negative, so `y < 0` was unreachable. It now also
//! requires every discriminant to fit the destination's range.
//!
//! Round 11 found the `u128` sibling, with no cast at all: a discriminant at or
//! above 2^127 is decoded into an `i128` as a NEGATIVE tag, so the tag-set fact over
//! the `u128` discriminant said `d ∈ {-1, 1}` and `(e as u128) > 5` was unreachable
//! (`index_by_huge`, proved and certified by every build before this one). An
//! unsigned discriminant with a negative decoded tag now gets no tag-set fact.

#[repr(u64)]
#[derive(Clone, Copy)]
pub enum Big {
    A = u64::MAX,
    B = 1,
}

pub fn index_by_big(a: &[u8; 10], e: Big) -> u8 { //~ ERROR strict verification failed for `enum_discriminant_cast_must_fit_the_destination_refused::index_by_big`
    let y = e as i64;
    let i: usize = if y < 0 { 50 } else { 0 };
    a[i]
}

pub fn index_by_big_direct(a: &[u8; 10], e: Big) -> u8 { //~ ERROR strict verification failed for `enum_discriminant_cast_must_fit_the_destination_refused::index_by_big_direct`
    let i: usize = if (e as i64) < 0 { 50 } else { 0 };
    a[i]
}

#[repr(u8)]
#[derive(Clone, Copy)]
pub enum Byte {
    A = 255,
    B = 1,
}

pub fn index_by_byte(a: &[u8; 10], e: Byte) -> u8 { //~ ERROR strict verification failed for `enum_discriminant_cast_must_fit_the_destination_refused::index_by_byte`
    let y = e as i8;
    let i: usize = if y < 0 { 50 } else { 0 };
    a[i]
}

#[repr(u128)]
#[derive(Clone, Copy)]
pub enum Huge {
    A = u128::MAX,
    B = 1,
}

pub fn index_by_huge(t: &[u8], e: Huge) -> u8 { //~ ERROR full verification failed for `enum_discriminant_cast_must_fit_the_destination_refused::index_by_huge`
    if t.len() != 1 {
        return 0;
    }
    if (e as u128) > 5 {
        return t[1];
    }
    t[0]
}
