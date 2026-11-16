//@ revisions: pow div_euclid
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A sysroot fn item handed to a std routine as a type argument runs inside that
//! routine, where no call-site recognizer looks, so it is tolerated only where a
//! DIRECT call to it would be charged nothing. A direct `x.pow(y)` (overflow) and
//! `a.div_euclid(b)` (zero divisor) ARE charged, but the family that answers that
//! question lacked both: review round 31 (2026-10-01) measured
//! `v.iter().copied().fold(2u32, u32::pow)` as only an advisory under the default
//! policy while it panics on `[40]`. Both now keep their row and are refused.
#[cfg(pow)]
pub fn f(v: &[u32]) -> u32 { //[pow]~ ERROR verification
    v.iter().copied().fold(2u32, u32::pow)
}

#[cfg(div_euclid)]
pub fn f(v: &[u32]) -> u32 { //[div_euclid]~ ERROR verification
    v.iter().copied().fold(100u32, u32::div_euclid)
}
