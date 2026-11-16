//@ revisions: char_big int_edge
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Twin of `char_narrowing_cast_keeps_its_code_point.rs`: `'Ā'` (U+0100) truncates to
//! `0`, so `c as u8 - 1` underflows for a char above the range; the code point only
//! pins the cast when it fits `u8`.
#[cfg(char_big)]
pub fn shifted(c: char) -> u8 { //[char_big]~ ERROR verification
    if c >= '\u{1}' { c as u8 - 1 } else { 0 }
}

/// `x = 255` fits `u8` and `255 + 1` overflows; the value fact pins the cast and the
/// overflow stays refuted.
#[cfg(int_edge)]
pub fn edge(x: u32) -> u8 { //[int_edge]~ ERROR verification
    if x <= 256 { x as u8 + 1 } else { 0 }
}
