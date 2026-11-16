//@ needs-trust-verify
//@ only-64bit
//@ edition: 2021
//@ revisions: slice_iter split_char range_u32 range_u128 range_u128_param inclusive_u64
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[slice_iter] check-pass
//@[split_char] check-pass
//@[range_u32] check-pass
//@[range_u128] check-fail
//@[range_u128_param] check-fail
//@[inclusive_u64] check-fail
//! **`Iterator::count` must fit `usize` (Trust, 2026-09-28).**
//!
//! `count` panics once the item count passes `usize::MAX`: core's default adds one per
//! item under `#[rustc_inherit_overflow_checks]`, and the integer-range specialization
//! calls `expect("count overflowed usize")`.
//!
//! The bridge modelled every `count` as a closure-driving consumer call. That meant a
//! fresh result, an in-body `Assert(false)` may-panic marker, and a panic-freedom row
//! with no public twin. No counted obligation ever requested the marker, so
//! `(0u128..u128::MAX).count()` built under `certify` with one
//! `native-verification-gap` row. A binary calling the certified rlib then exited 101 at
//! `core/src/iter/range.rs`. The closure-driving arm now mints the counted
//! whole-function carrier (`opaque_consumer_panic_carrier_required`), and a `count`
//! whose item count provably fits `usize` is modelled as total
//! (`total_iterator_count_call`).
//!
//! * `slice_iter`, `split_char`, `range_u32`: POSITIVE. A slice holds at most
//!   `isize::MAX` items, a `str` iterator yields at most `len + 1`, and a `u32` range at
//!   most `2^32 - 1`.
//! * `range_u128`, `range_u128_param`: the NEGATIVES that were false accepts.
//! * `inclusive_u64`: `(0..=u64::MAX).count()` is `2^64`, one past a 64-bit `usize`.
//!
//! The annotation on `f` discriminates each negative.

#[cfg(slice_iter)]
pub fn f(v: &[u32]) -> usize {
    v.iter().count()
}

#[cfg(split_char)]
pub fn f(s: &str) -> usize {
    s.split(',').count()
}

#[cfg(range_u32)]
pub fn f(n: u32) -> usize {
    (0u32..n).count()
}

#[cfg(range_u128)]
pub fn f() -> usize {
    //[range_u128]~^ ERROR Trust Level 0 safety verification incomplete for `iterator_count_must_fit_usize::f`
    (0u128..u128::MAX).count()
}

#[cfg(range_u128_param)]
pub fn f(n: u128) -> usize {
    //[range_u128_param]~^ ERROR Trust Level 0 safety verification incomplete for `iterator_count_must_fit_usize::f`
    (0u128..n).count()
}

#[cfg(inclusive_u64)]
pub fn f(n: u64) -> usize {
    //[inclusive_u64]~^ ERROR Trust Level 0 safety verification incomplete for `iterator_count_must_fit_usize::f`
    (0u64..=n).count()
}
