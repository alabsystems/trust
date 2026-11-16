//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ revisions: str_from slice_range new_range const_incl const_str inline_incl
//@ compile-flags: -Ztrust-verify=off
//@[inline_incl] compile-flags: -Zinline-mir=yes
//@[str_from] error-pattern: start byte index 1 is not a char boundary
//@[slice_range] error-pattern: range end index 5 out of range for slice of length 3
//@[new_range] error-pattern: range end index 5 out of range for slice of length 3
//@[const_incl] error-pattern: range end index 4 out of range for slice of length 3
//@[const_str] error-pattern: start byte index 1 is not a char boundary
//@[inline_incl] error-pattern: range end index 4 out of range for slice of length 3
//@ ignore-emscripten no processes
//! The WITNESS for `core_range_index_charged.rs` (UTF8-CORE-RANGE-INDEX-1): its
//! `str_from` and `slice_range` bodies, and the `new_range` spelling of the latter,
//! built with verification OFF. Each panics (exit 101) — before and after the fix,
//! which changes only whether the VERIFIED build of the same bodies is accepted (it
//! was, rc=0, on the stage 1 of `dc15b882f6`).
//!
//! `const_incl`, `const_str` and `inline_incl` (2026-10-06, CONST-RANGE-INDEX-1 and
//! AGG-BOOL-TWIN-SORT-1): the fixture's `const_item` and `inline_incl` bodies. Their
//! verified builds were accepted (rc=0) on the stage 1 of `0ac7a96d9f`, whose fix
//! did not reach a constant range operand or the inlined inclusive range.

#![cfg_attr(new_range, feature(new_range))]

#[cfg(str_from)]
fn str_from(s: &str) -> &str {
    if s.len() >= 1 { &s[core::range::RangeFrom::from(1..)] } else { "" }
}

#[cfg(slice_range)]
fn slice_range(v: &[u8]) -> &[u8] {
    &v[core::range::Range::from(0..5)]
}

#[cfg(new_range)]
fn slice_range(v: &[u8]) -> &[u8] {
    &v[0..5]
}

#[cfg(const_incl)]
const CR_INCL: core::range::RangeInclusive<usize> = core::range::RangeInclusive { start: 0, last: 4 };

#[cfg(const_incl)]
fn const_cr_incl(a: &[u8; 3]) -> &[u8] {
    &a[CR_INCL]
}

#[cfg(const_str)]
const CR_FROM: core::range::RangeFrom<usize> = core::range::RangeFrom { start: 1 };

#[cfg(const_str)]
fn const_cr_from_str(s: &str) -> &str {
    &s[CR_FROM]
}

#[cfg(inline_incl)]
fn arr_incl_from(a: &[u8; 3]) -> &[u8] {
    &a[core::range::RangeInclusive::from(0..=4)]
}

fn main() {
    #[cfg(str_from)]
    println!("{}", str_from(std::hint::black_box("é")));
    #[cfg(any(slice_range, new_range))]
    println!("{:?}", slice_range(std::hint::black_box(&[1u8, 2, 3])));
    #[cfg(const_incl)]
    println!("{:?}", const_cr_incl(std::hint::black_box(&[1u8, 2, 3])));
    #[cfg(const_str)]
    println!("{}", const_cr_from_str(std::hint::black_box("é")));
    #[cfg(inline_incl)]
    println!("{:?}", arr_incl_from(std::hint::black_box(&[1u8, 2, 3])));
}
