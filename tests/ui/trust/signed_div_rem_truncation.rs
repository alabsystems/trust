//@ needs-trust-verify
//@ proc-macro: trust.rs
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE

// Rust signed `/` and `%` truncate toward zero.  The typed-CHC transport must
// not silently give them Euclidean integer semantics: doing so previously
// false-PROVED both deliberately false postconditions below.
//
// SPELLING (2026-08-30, fixture repair): the attribute-`ensures` surface
// accepts exactly the upstream closure form `move |r: &T| <predicate>`.  The
// bare-expression form `#[trust::ensures(result >= 0)]` this file originally
// used has NEVER lowered through the attribute snippet lane
// (`trust_contract_query`'s attribute-origin ensures arm required the closure
// spelling at this fixture's own birth commit a941f69a89), so every predicate
// here — the true controls included — fail-closed as `SpecEnsuresUnparseable`
// and the file asserted nothing about div/rem semantics.  With the supported
// spelling, the two positive controls PROVE end-to-end (truncating semantics
// reach the solver) and the two Euclidean-only claims stay unproved, which is
// the actual pin.  A false-PROVE of either negative deletes an expected error
// below and fails this test; a lost proof on either positive control emits an
// unexpected error and fails it too.

extern crate trust;

/// `-1 % 2 == -1`, so signed remainder is not always non-negative.
#[trust::ensures(move |r: &i32| *r >= 0)]
pub fn signed_remainder_is_not_non_negative(x: i32) -> i32 {
    x % 2
}
//~^^^ ERROR Trust strict verification failed

/// Positive control: Rust's `x % 2` is always in `[-1, 1]`.
#[trust::ensures(move |r: &i32| *r >= -1)]
#[trust::ensures(move |r: &i32| *r <= 1)]
pub fn signed_remainder_bounds_are_true(x: i32) -> i32 {
    x % 2
}

/// Euclidean division gives `-3 div 2 == -2`, but Rust truncates toward zero
/// and returns `-1`.  The old typed-CHC lowering therefore proved this false
/// result equality.
#[trust::requires(x == -3)]
#[trust::ensures(move |r: &i32| *r == -2)]
pub fn signed_division_is_not_floor_division(x: i32) -> i32 {
    x / 2
}
//~^^^ ERROR Trust strict verification failed

/// Positive control: at the same input the Rust result is exactly `-1`.
#[trust::requires(x == -3)]
#[trust::ensures(move |r: &i32| *r == -1)]
pub fn signed_division_truncation_result_is_true(x: i32) -> i32 {
    x / 2
}
