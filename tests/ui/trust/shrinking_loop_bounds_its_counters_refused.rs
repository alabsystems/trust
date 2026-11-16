//@ revisions: never_zero any_divisor regrown_by_ref regrown_by_callee hoisted_temp
//@ revisions: popcount_overflows other_minus_one hoisted_minus_one
//@ revisions: digit_sum_wide_remainder digit_sum_signed
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Twin of `shrinking_loop_bounds_its_counters.rs`: each loop can run forever, so its
//! `u8` counter overflows. `never_zero`: `n / 2 + 1` never reaches 0. `any_divisor`:
//! the divisor may be 1. Review round 35 (2026-10-01): `regrown_by_ref` and
//! `regrown_by_callee` write `n` through an `&mut` the write scan did not see (both
//! CERTIFIED); `hoisted_temp` copies a quotient computed once, before the loop, so
//! `n` stops shrinking. `popcount_overflows`: 64 iterations of `c += 4` reach 256
//! at `x = u64::MAX`. `other_minus_one`: `x &= y - 1` need not clear a bit of `x`.
//! `hoisted_minus_one`: `x - 1` computed once, so `x &= m` stops changing `x`.
//! `digit_sum_wide_remainder`: `n % 100` (up to 99) over 20 iterations overflows a
//! `u8` at `n = u64::MAX`. `digit_sum_signed`: a signed `n % 10` is not in `[0, 9]`.
#[cfg(never_zero)]
pub fn spin(mut n: u32) -> u8 { //[never_zero]~ ERROR verification
    let mut c: u8 = 0;
    while n > 0 {
        n = n / 2 + 1;
        c += 1;
    }
    c
}

#[cfg(any_divisor)]
pub fn spin(mut n: u32, d: u32) -> u8 { //[any_divisor]~ ERROR verification
    let mut c: u8 = 0;
    if d == 0 {
        return 0;
    }
    while n > 0 {
        n /= d;
        c += 1;
    }
    c
}

#[cfg(regrown_by_ref)]
pub fn spin(mut n: u32) -> u8 { //[regrown_by_ref]~ ERROR verification
    let mut c: u8 = 0;
    while n != 0 {
        n >>= 1;
        c += 1;
        let r = &mut n;
        *r = 1000;
    }
    c
}

#[cfg(regrown_by_callee)]
fn reset(x: &mut u32) {
    *x = 1000;
}
#[cfg(regrown_by_callee)]
pub fn spin(mut n: u32) -> u8 { //[regrown_by_callee]~ ERROR verification
    let mut c: u8 = 0;
    while n != 0 {
        n >>= 1;
        c += 1;
        reset(&mut n);
    }
    c
}

#[cfg(hoisted_temp)]
pub fn spin(mut n: u32) -> u8 { //[hoisted_temp]~ ERROR verification
    let mut c: u8 = 0;
    let t = n >> 1;
    while n != 0 {
        c += 1;
        n = t;
    }
    c
}

#[cfg(popcount_overflows)]
pub fn spin(mut x: u64) -> u8 { //[popcount_overflows]~ ERROR verification
    let mut c: u8 = 0;
    while x != 0 {
        x &= x - 1;
        c += 4;
    }
    c
}

#[cfg(other_minus_one)]
pub fn spin(mut x: u64, y: u64) -> u8 { //[other_minus_one]~ ERROR verification
    let mut c: u8 = 0;
    if y == 0 {
        return 0;
    }
    while x != 0 {
        x &= y - 1;
        c += 1;
    }
    c
}

#[cfg(hoisted_minus_one)]
pub fn spin(mut x: u64) -> u8 { //[hoisted_minus_one]~ ERROR verification
    let mut c: u8 = 0;
    if x == 0 {
        return 0;
    }
    let m = x - 1;
    while x != 0 {
        x &= m;
        c += 1;
    }
    c
}

#[cfg(digit_sum_wide_remainder)]
pub fn spin(mut n: u64) -> u8 { //[digit_sum_wide_remainder]~ ERROR verification
    let mut s: u8 = 0;
    while n > 0 {
        s += (n % 100) as u8;
        n /= 10;
    }
    s
}

#[cfg(digit_sum_signed)]
pub fn spin(mut n: i64) -> i8 { //[digit_sum_signed]~ ERROR verification
    let mut s: i8 = 0;
    while n > 0 {
        s += (n % 10) as i8;
        n /= 10;
    }
    s
}
