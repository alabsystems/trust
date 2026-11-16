//@ revisions: full_range narrow_add
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Twin of `integer_abs_has_its_value.rs`: `full_range` adds two `i64` magnitudes,
//! which overflows at `a = b = i64::MAX`; `narrow_add` adds 200 to a magnitude up to
//! 128, which overflows a `u8`.
#[cfg(full_range)]
pub fn f(a: i64, b: i64) -> i64 { //[full_range]~ ERROR verification
    a.abs() + b.abs()
}

#[cfg(narrow_add)]
pub fn f(a: i8) -> u8 { //[narrow_add]~ ERROR verification
    let x = (a as i16).abs();
    (x as u8) + 200
}
