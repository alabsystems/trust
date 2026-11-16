//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! The refusing twins of `integer_log_and_zero_count_ranges.rs`. Each panics on the
//! input named beside it, so none may prove.

// x = 0: 64 leading zeros, `63 - 64` underflows.
pub fn unguarded_log2(x: u64) -> u32 { //~ ERROR failed for `integer_log_and_zero_count_ranges_refused::unguarded_log2`
    63 - x.leading_zeros()
}

// x = 0, y = 1: the guard is on another value.
pub fn guard_on_another(x: u64, y: u64) -> u32 { //~ ERROR failed for `integer_log_and_zero_count_ranges_refused::guard_on_another`
    if y == 0 { 0 } else { 63 - x.leading_zeros() }
}

// x = 1: the receiver is reassigned to 0 after its guard.
pub fn receiver_reassigned(x: u64) -> u32 { //~ ERROR failed for `integer_log_and_zero_count_ranges_refused::receiver_reassigned`
    let mut z = x;
    if z != 0 {
        z = 0;
        63 - z.leading_zeros()
    } else {
        0
    }
}

// x = 0: 64 trailing zeros index past a 64-entry table.
pub fn unguarded_lowest(t: &[u8; 64], x: u64) -> u8 { //~ ERROR failed for `integer_log_and_zero_count_ranges_refused::unguarded_lowest`
    t[x.trailing_zeros() as usize]
}

// x = u64::MAX: `ilog10` is 19, and `19 * 14 = 266` overflows a `u8`.
pub fn log10_scaled(x: u64) -> u8 { //~ ERROR failed for `integer_log_and_zero_count_ranges_refused::log10_scaled`
    match x.checked_ilog10() {
        Some(d) => (d as u8) * 14,
        None => 0,
    }
}

// Any slice of three or more: `get(1..3)` has length 2.
pub fn past_the_sub_slice(v: &[u32]) -> u32 { //~ ERROR failed for `integer_log_and_zero_count_ranges_refused::past_the_sub_slice`
    if let Some(s) = v.get(1..3) { s[2] } else { 0 }
}
