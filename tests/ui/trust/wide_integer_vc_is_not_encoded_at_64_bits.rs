//@ revisions: gt_u64_max signed_wide round_trip const_param signed_const_param
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! An unsigned VC carrying an out-of-i64 literal was re-encoded as bitvectors at a
//! width chosen as if every variable were below `2^64`. Over `x: u128`/`i128` that
//! made `x > u64::MAX` never true, so a division by the `0` that branch selects was
//! PROVED and kernel-certified (review round 34, 2026-10-01; panics for
//! `x = 1 << 64`). A function holding a wider-than-64-bit integer now keeps the
//! exact integer formula. Review round 35: a `const N: u128` generic is no local
//! (vcgen's `__trust_constparam_…` symbol), and a negative `const N: i128` was read
//! as unsigned, so the gate is now an allow-list over the formula's variables.
#[cfg(gt_u64_max)]
pub fn f(x: u128) -> u8 { //[gt_u64_max]~ ERROR verification
    let d: u8 = if x > 18446744073709551615 { 0 } else { 1 };
    100 / d
}

#[cfg(signed_wide)]
pub fn f(x: i128) -> u8 { //[signed_wide]~ ERROR verification
    let d: u8 = if x > 18446744073709551615 { 0 } else { 1 };
    100 / d
}

#[cfg(round_trip)]
pub fn f(x: u128) -> u8 { //[round_trip]~ ERROR verification
    let d: u8 = if ((x as u64) as u128) < x { 0 } else { 1 };
    100 / d
}

#[cfg(const_param)]
pub fn f<const N: u128>() -> u8 { //[const_param]~ ERROR verification
    let d: u8 = if N > 18446744073709551615 { 0 } else { 1 };
    100 / d
}

#[cfg(signed_const_param)]
pub fn f<const N: i128>(y: u64) -> u8 { //[signed_const_param]~ ERROR verification
    let d: u8 = if y > 9223372036854775808 && N < 0 { 0 } else { 1 };
    100 / d
}
