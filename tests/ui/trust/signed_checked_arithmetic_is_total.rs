//@ needs-trust-verify
//@ edition: 2021
//@ revisions: add sub mul unwrap_panics
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[add] check-pass
//@[sub] check-pass
//@[mul] check-pass
//@[unwrap_panics] check-fail
//! **A SIGNED `checked_{add,sub,mul}` is panic-free under certify (Trust,
//! 2026-09-28).**
//!
//! `fn cadd(a: i64, b: i64) -> Option<i64> { a.checked_add(b) }` failed certify,
//! while the same function over `u32` passed. The extractor stamps a SIGNED
//! checked primitive call `@trust-rustc-checked-primitive-method::…` (E6 models
//! it). The stamp renamed the call site, so the call missed the bridge's
//! `EXACT_TOTAL` entry for its unstamped spelling (`core::num::checked_add`),
//! and its body was never bundled under the stamped name. It fell to the
//! absent-callee may-panic arm. The bridge now reads the stamp through the one
//! shared classifier. That is panic-freedom only: the result is a havoc.
//!
//! * `add`, `sub`, `mul`: POSITIVE, at `i64`, `i32` and `i8`.
//! * `unwrap_panics`: the NEGATIVE. `checked_add(..).unwrap()` really panics on
//!   overflow, and totality of `checked_add` must not reach the `unwrap`.

#[cfg(add)]
pub fn cadd(a: i64, b: i64) -> Option<i64> {
    a.checked_add(b)
}

#[cfg(sub)]
pub fn csub(a: i32, b: i32) -> Option<i32> {
    a.checked_sub(b)
}

#[cfg(mul)]
pub fn cmul(a: i8, b: i8) -> i8 {
    a.checked_mul(b).unwrap_or(0)
}

#[cfg(unwrap_panics)]
pub fn cadd_unwrap(a: i64, b: i64) -> i64 {
    //[unwrap_panics]~^ ERROR Trust
    a.checked_add(b).unwrap()
}
