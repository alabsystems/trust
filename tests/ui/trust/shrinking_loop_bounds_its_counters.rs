//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@[default] compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//! A loop that continues only while an unsigned `n >= 1` and divides `n` by a
//! constant `d >= 2` (or shifts it right) on every iteration runs at most as many
//! times as `MAX` has base-`d` digits, so counters in it are bounded. Without a
//! trip count, `d += 1` in a digit loop was refuted (ordsweep2 numeric/c03, c15).
//! `n &= n - 1` clears one set bit per iteration, so such a loop runs at most
//! `width` times (popcount, ordsweep2 numeric/c07); a shift by `k` at most
//! `ceil(width / k)` times (a u128 `>>= 127` was refused, review round 36).
//! A digit sum adds `n % 10` (at most 9) per iteration, so over at most 20
//! iterations of a `u64` a `u8` sum stays at most 180 (ordsweep2 numeric/c03).
//! The twin `_refused.rs` keeps loops that do not shrink to zero refused.
pub fn num_digits(mut n: u32) -> u32 {
    let mut d = 1;
    while n >= 10 {
        n /= 10;
        d += 1;
    }
    d
}

pub fn bit_len(mut n: u64) -> u8 {
    let mut b: u8 = 0;
    while n != 0 {
        n >>= 1;
        b += 1;
    }
    b
}

pub fn popcount_times_three(mut x: u64) -> u8 {
    let mut c: u8 = 0;
    while x != 0 {
        x &= x - 1;
        c += 3;
    }
    c
}

pub fn wide_halves(mut n: u128) -> u8 {
    let mut c: u8 = 0;
    while n != 0 {
        n >>= 127;
        c += 50;
    }
    c
}

pub fn digit_sum(mut n: u64) -> u32 {
    let mut s: u32 = 0;
    while n > 0 {
        s += (n % 10) as u32;
        n /= 10;
    }
    s
}

pub fn digit_sum_u8(mut n: u64) -> u8 {
    let mut s: u8 = 0;
    while n > 0 {
        s += (n % 10) as u8;
        n /= 10;
    }
    s
}
