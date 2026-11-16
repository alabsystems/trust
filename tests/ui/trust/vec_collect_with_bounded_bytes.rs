//@ needs-trust-verify
//@ only-64bit
//@ edition: 2021
//@ revisions: range_u32 copied_slice rev_range_u8 enumerate_slice string_from_strs chars refs_u8
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[range_u32] check-pass
//@[copied_slice] check-pass
//@[rev_range_u8] check-pass
//@[enumerate_slice] check-fail
//@[string_from_strs] check-fail
//@[chars] check-fail
//@[refs_u8] check-fail
//! **`collect` into `Vec<T, Global>` is total when its bytes provably fit
//! (Trust, 2026-09-28).**
//!
//! `collect` into a `Vec` moves items into a buffer. Allocation failure aborts, which
//! is outside the panic model. Its one panic is "capacity overflow", when the item
//! count times `size_of::<T>()` passes `isize::MAX`. The compiler grants the call
//! (`collect_bounded_vec_collect_total_calls`) only when that product is bounded:
//! * `range_u32` (the ordinary sweep's s20): at most `2^32 - 1` items of 4 bytes;
//! * `copied_slice`: items no larger than the slice's elements, so no more bytes than
//!   the slice, which Rust's layout rules bound;
//! * `rev_range_u8`: `Rev` adds no items.
//!
//! The NEGATIVES can reach "capacity overflow", so they stay refused. Each is
//! annotated on `f`:
//! * `enumerate_slice` (t25): 16-byte items from 4-byte elements.
//!   `MAX_LIVE_ALLOC_BYTES = isize::MAX / 2` allows `2^60` of them;
//! * `string_from_strs` (s32): the slice may hold one large `&str` many times, so the
//!   summed length has no per-allocation bound;
//! * `chars`: up to four bytes of `char` per byte of `str`;
//! * `refs_u8`: eight-byte `&u8`s from one-byte elements.
//!
//! Before 2026-09-28 the first two negatives built under `certify` for no reason at all:
//! their may-panic marker had no counted carrier (`docs/KNOWN_HAZARDS.md`).

#[cfg(range_u32)]
pub fn f(n: usize) -> Vec<u32> {
    (0..n.min(8) as u32).collect()
}

#[cfg(copied_slice)]
pub fn f(v: &[u32]) -> Vec<u32> {
    v.iter().copied().collect()
}

#[cfg(rev_range_u8)]
pub fn f(n: u8) -> Vec<u8> {
    (0u8..n).rev().collect()
}

#[cfg(enumerate_slice)]
pub fn f(v: &[u32]) -> Vec<(usize, u32)> {
    //[enumerate_slice]~^ ERROR Trust Level 0 safety verification incomplete for `vec_collect_with_bounded_bytes::f`
    v.iter().copied().enumerate().collect()
}

#[cfg(string_from_strs)]
pub fn f(v: &[&str]) -> String {
    //[string_from_strs]~^ ERROR Trust Level 0 safety verification incomplete for `vec_collect_with_bounded_bytes::f`
    v.iter().copied().collect()
}

#[cfg(chars)]
pub fn f(s: &str) -> Vec<char> {
    //[chars]~^ ERROR Trust Level 0 safety verification incomplete for `vec_collect_with_bounded_bytes::f`
    s.chars().collect()
}

#[cfg(refs_u8)]
pub fn f(v: &[u8]) -> Vec<&u8> {
    //[refs_u8]~^ ERROR Trust Level 0 safety verification incomplete for `vec_collect_with_bounded_bytes::f`
    v.iter().collect()
}
