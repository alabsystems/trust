//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@[default] compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//! `c as u8` over a `char` keeps the code point when it fits, so a digit arm's
//! `c as u8 - b'0'` cannot underflow. The cast's result was a free value and the
//! subtraction was refuted at `c = '0'` (ordsweep2 enums/c03). The twin
//! `_refused.rs` keeps a char that may not fit refused.
pub fn digit(c: char) -> u8 {
    match c {
        '0'..='9' => c as u8 - b'0',
        _ => 0,
    }
}

pub fn digit_if(c: char) -> u8 {
    if c >= '0' && c <= '9' { c as u8 - b'0' } else { 0 }
}

pub fn low_byte_plus(c: char) -> u16 {
    if (c as u32) < 0x100 { c as u16 + 1 } else { 0 }
}

/// The same fact for any integer narrowing: a value that fits keeps its value.
pub fn small_plus(x: u32) -> u8 {
    if x < 200 { x as u8 + 55 } else { 0 }
}
