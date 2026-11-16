//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! The refusing twins of `matches_range_pattern_narrows.rs`. Each guard admits the
//! input named beside it, on which the guarded subtraction underflows.

// c = b'a' (97): `97 - 98`.
pub fn off_by_one(c: u8) -> u8 { //~ ERROR failed for `matches_range_pattern_narrows_refused::off_by_one`
    if matches!(c, b'a'..=b'z') { c - 98 } else { c }
}

// c = 0: the NEGATED pattern admits it.
pub fn negated(c: u8) -> u8 { //~ ERROR failed for `matches_range_pattern_narrows_refused::negated`
    if !matches!(c, b'a'..=b'z') { c - 32 } else { c }
}

// c = 0: the disjunction admits it.
pub fn or_zero(c: u8) -> u8 { //~ ERROR failed for `matches_range_pattern_narrows_refused::or_zero`
    let is_lower = matches!(c, b'a'..=b'z');
    if is_lower || c == 0 { c - 32 } else { c }
}

// c = b'0' (48): `48 - 49`.
pub fn digit_off_by_one(c: u8) -> u8 { //~ ERROR failed for `matches_range_pattern_narrows_refused::digit_off_by_one`
    if matches!(c, b'0'..=b'9' | b'a'..=b'z') { c - 49 } else { 0 }
}
