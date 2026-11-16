//@ needs-trust-verify
//@ only-64bit
//@ edition: 2021
//@ revisions: filter_count windows_all windows_filter_count lines_count split_whitespace_count bytes_rev_collect filter_panics filter_u128 filter_owning two_adapters
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[filter_count] check-pass
//@[windows_all] check-pass
//@[windows_filter_count] check-pass
//@[lines_count] check-pass
//@[split_whitespace_count] check-pass
//@[bytes_rev_collect] check-pass
//@[filter_panics] check-fail
//@[filter_u128] check-fail
//@[filter_owning] check-fail
//@[two_adapters] check-fail
//! **`count` and the other drive-only consumers over a `Filter`/`Map` of a total
//! base, and four more total std iterators (Trust, 2026-09-28).**
//!
//! `v.iter().filter(|x| **x >= t).count()` bundled std's `Filter::count`. Its `Sum`
//! closure carries an `Overflow(Add)` assert, which the member-assert lane refuses, so
//! the whole bundle failed. Yet the sum of `0`/`1` never passes the base's item count.
//! Now `drive_only_consumer_call_decision` grants the call: `count` is drive-only, and
//! a receiver may be one core `Filter`/`Map` over a total base whose predicate or
//! mapper is admissible. The bundle walk declines the granted call's body.
//! `total_std_iterator_ty` also learns four receivers:
//! * `Windows`, whose `NonZero` size makes `next` total;
//! * `Bytes`, `Lines` and `SplitWhitespace`, whose inner closures are core fns.
//!
//! `collect` bounds `Bytes` at one byte per byte.
//!
//! * POSITIVE: the ordinary sweep's t40, s23, s19, t12 and s25, and a
//!   `split_whitespace().count()`.
//! * NEGATIVE, each annotated on `f`:
//!   * a predicate that can panic;
//!   * a `u128` range under the `Filter`, whose count can pass `usize::MAX`;
//!   * an owning base;
//!   * two adapters over the base (only one is admitted).

#[cfg(filter_count)]
pub fn f(v: &[i16], t: i16) -> usize {
    v.iter().filter(|x| **x >= t).count()
}

#[cfg(windows_all)]
pub fn f(v: &[u32]) -> bool {
    v.windows(2).all(|w| w[0] <= w[1])
}

#[cfg(windows_filter_count)]
pub fn f(v: &[u32]) -> usize {
    v.windows(2).filter(|w| w[0] <= w[1]).count()
}

#[cfg(lines_count)]
pub fn f(s: &str) -> usize {
    s.lines().count()
}

#[cfg(split_whitespace_count)]
pub fn f(s: &str) -> usize {
    s.split_whitespace().count()
}

#[cfg(bytes_rev_collect)]
pub fn f(s: &str) -> Vec<u8> {
    s.bytes().rev().collect()
}

#[cfg(filter_panics)]
pub fn f(v: &[u32]) -> usize {
    //[filter_panics]~^ ERROR Trust certify verification failed for `iterator_consumer_over_filter_and_str_bases::f`
    v.iter()
        .filter(|x| {
            assert!(**x != 7);
            true
        })
        .count()
}

#[cfg(filter_u128)]
pub fn f(n: u128) -> usize {
    //[filter_u128]~^ ERROR Trust certify verification failed for `iterator_consumer_over_filter_and_str_bases::f`
    (0u128..n).filter(|x| *x > 3).count()
}

#[cfg(filter_owning)]
pub fn f(v: Vec<u32>) -> usize {
    //[filter_owning]~^ ERROR Trust certify verification failed for `iterator_consumer_over_filter_and_str_bases::f`
    v.into_iter().filter(|x| *x > 3).count()
}

#[cfg(two_adapters)]
pub fn f(v: &[u32]) -> usize {
    //[two_adapters]~^ ERROR Trust certify verification failed for `iterator_consumer_over_filter_and_str_bases::f`
    v.iter()
        .map(|x| {
            assert!(*x != 7);
            *x
        })
        .filter(|x| *x > 3)
        .count()
}
