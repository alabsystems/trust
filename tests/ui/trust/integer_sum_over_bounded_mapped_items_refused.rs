//@ revisions: halves slice
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Twin of `integer_sum_over_bounded_mapped_items.rs`. `halves`: four items up to
//! `2^31 - 1` overflow a `u32` (`[u32::MAX; 4]`). `slice`: a slice of `u8` widened
//! to `u16` holds far more than the 258 items of 255 that overflow it.
#[cfg(halves)]
pub fn halves(a: &[u32; 4]) -> u32 { //[halves]~ ERROR verification
    a.iter().map(|&x| x / 2).sum()
}

#[cfg(slice)]
pub fn widen16(v: &[u8]) -> u16 { //[slice]~ ERROR verification
    v.iter().map(|&b| b as u16).sum()
}
