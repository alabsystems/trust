//@ needs-trust-verify
//@ edition: 2021
//@ revisions: shr_u128 div_u128 rem_u128 cast_u128 drop_guard
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[shr_u128] check-fail
//@[div_u128] check-fail
//@[rem_u128] check-fail
//@[cast_u128] check-fail
//@[drop_guard] check-fail
//! Review round 115 (2026-10-10): the interval domain is `i128`, and its arithmetic
//! read an unknown `u128` operand as the `i128` range, so a shift, division or
//! remainder of a `u128` by a large constant, or `x as i128` after `x > 100`, got an
//! interval that excludes real values. Once single-assignment temps carried their
//! def-site interval into every VC, each of these panicking programs verified
//! (kernel-certified under `-Ztrust-policy=certify`). Each panics for some input
//! (`u128::MAX`, `64 << 121`, `2^127`) and must stay refused. Round 116: a guard
//! whose `Drop` stores through the `&mut` it holds left its referent's interval
//! stale (`drop_guard`, `v = 0` divides by zero).

#[cfg(shr_u128)]
pub fn s2(x: u128) -> u8 {
    let a = [0u8; 128];
    let t = (x >> 121) as i32;
    a[(t + 64) as usize]
}

#[cfg(div_u128)]
pub fn h_div3(x: u128) -> u32 {
    let t = (x / 2658455991569831745807614120560689152u128) as i32;
    100 / (t - 64) as u32
}

#[cfg(rem_u128)]
pub fn h_rem2(x: u128, y: u128) -> u32 {
    if y == 0 {
        return 0;
    }
    let t = ((x % y) >> 121) as i32;
    100 / (t - 64) as u32
}

#[cfg(cast_u128)]
pub fn c1(x: u128) -> u32 {
    if x > 100 {
        let s = ((x as i128) / 2658455991569831745807614120560689152i128) as i32;
        return 100 / (s + 64) as u32;
    }
    0
}

#[cfg(drop_guard)]
pub struct G<'a>(&'a mut usize, usize);

#[cfg(drop_guard)]
impl<'a> Drop for G<'a> {
    fn drop(&mut self) {
        *self.0 = self.1;
    }
}

#[cfg(drop_guard)]
pub fn drop_writes_div(v: usize) -> usize {
    let mut m: usize = 1;
    {
        let _g = G(&mut m, v);
    }
    let t = m;
    100 / t
}
