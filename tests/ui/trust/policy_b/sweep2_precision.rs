//@ needs-trust-verify
//@ edition: 2021
//@ revisions: first_some last_some first_some_bad first_none_bad rem_param rem_one_short rem_reassigned
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[first_some] check-pass
//@[last_some] check-pass
//@[rem_param] check-pass
//@[first_some_bad] check-fail
//@[first_none_bad] check-fail
//@[rem_one_short] check-fail
//@[rem_reassigned] check-fail
//! Sweep2 (2026-10-11), two precision fixes, each with panicking twins that stay
//! refused:
//! * `first`/`last`: a `Some` from the std `first()`/`last()` of a slice reference
//!   now also seeds the slice's length metadata `v__slice_len >= 1`, the name its
//!   bounds rows read (`first_some`, `last_some`). One element is not two
//!   (`first_some_bad`), and the `None` arm knows nothing (`first_none_bad`).
//! * `b != 0 ⟹ a % b < b` now holds for a never-written parameter divisor
//!   (`rem_param`). `b - r - 2` underflows for
//!   `b = 1` (`rem_one_short`), and a divisor reassigned after the remainder carries
//!   no bound (`rem_reassigned`).

#[cfg(first_some)]
pub fn f(v: &[i32]) -> i32 {
    match v.first() { Some(_) => v[0], None => 0 }
}

#[cfg(last_some)]
pub fn f(v: &[u8]) -> u8 {
    if let Some(_) = v.last() { v[v.len() - 1] } else { 0 }
}

#[cfg(first_some_bad)]
pub fn f(v: &[i32]) -> i32 {
    match v.first() { Some(_) => v[1], None => 0 }
}

#[cfg(first_none_bad)]
pub fn f(v: &[i32]) -> i32 {
    match v.first() { Some(_) => 0, None => v[0] }
}

#[cfg(rem_param)]
pub fn f(a: u64, b: u64) -> u64 {
    if b == 0 { return 0; }
    let r = a % b;
    b - r
}

#[cfg(rem_one_short)]
pub fn f(a: u64, b: u64) -> u64 {
    if b == 0 { return 0; }
    let r = a % b;
    b - r - 2
}

#[cfg(rem_reassigned)]
pub fn f(a: u64, b: u64) -> u64 {
    if b == 0 { return 0; }
    let mut d = b;
    let r = a % d;
    d = a & 1;
    d - r
}
