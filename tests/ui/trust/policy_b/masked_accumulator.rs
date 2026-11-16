//@ needs-trust-verify
//@ edition: 2021
//@ revisions: masked masked_mul signed_masked wide_mask mul_too_wide negative_mask
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[masked] check-pass
//@[masked_mul] check-pass
//@[signed_masked] check-pass
//@[wide_mask] check-fail
//@[mul_too_wide] check-fail
//@[negative_mask] check-fail
//! Sweep p21 (2026-10-10): `s = (s + b as u32) & 0xffff` in a loop keeps `s` in
//! `[0, 0xffff]`, so `s + b` cannot overflow. The interval lane read `x & m` as Top
//! when only `m` was non-negative, and the function-wide environment diluted the add
//! temp `_10 = copy s` to its type range. Negative controls: a mask that bounds
//! nothing (`wide_mask`, `negative_mask`) and a product past `u32::MAX` after the
//! masked loop (`mul_too_wide`) each overflow for some input and stay refused.

#[cfg(masked)]
pub fn fold_checksum(data: &[u8]) -> u16 {
    let mut s: u32 = 0;
    for &b in data {
        s = (s + b as u32) & 0xffff;
    }
    s as u16
}

#[cfg(masked_mul)]
pub fn spread(data: &[u8]) -> u32 {
    let mut s: u32 = 0;
    for &b in data {
        s = (s + b as u32) & 0xffff;
    }
    s * 65537
}

#[cfg(signed_masked)]
pub fn fold_signed(data: &[i8]) -> i32 {
    let mut s: i32 = 0;
    for &b in data {
        s = (s + b as i32) & 0x7fff;
    }
    s
}

#[cfg(wide_mask)]
pub fn fold_wide(data: &[u8]) -> u32 {
    let mut s: u32 = 0;
    for &b in data {
        s = (s + b as u32) & 0xffff_ffff;
    }
    s
}

#[cfg(mul_too_wide)]
pub fn spread_wide(data: &[u8]) -> u32 {
    let mut s: u32 = 0;
    for &b in data {
        s = (s + b as u32) & 0xffff;
    }
    s * 70000
}

#[cfg(negative_mask)]
pub fn fold_even(data: &[i8]) -> i32 {
    let mut s: i32 = 0;
    for &b in data {
        s = (s + b as i32) & -2;
    }
    s
}
