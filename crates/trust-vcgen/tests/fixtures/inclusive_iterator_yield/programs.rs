#![allow(dead_code)]

pub fn inclusive_step_skips_past_end(a: &[u8; 1]) -> u8 {
    let mut acc = 0;
    for i in (0..=1usize).step_by(2) {
        acc ^= a[i];
    }
    acc
}

pub fn inclusive_first_yield_returns(a: &[u8; 1]) -> u8 {
    for i in 0..=1usize {
        return a[i];
    }
    0
}

pub fn exclusive_first_yield_returns(a: &[u8; 1]) -> u8 {
    for i in 0..2usize {
        return a[i];
    }
    0
}

pub fn inclusive_safe_bound(a: &[u8; 2]) -> u8 {
    let mut acc = 0;
    for i in 0..=1usize {
        acc ^= a[i];
    }
    acc
}
