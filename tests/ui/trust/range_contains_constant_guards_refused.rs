//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! The refusing twins of `range_contains_constant_guards.rs`. Each guard admits the
//! input named beside it, on which the guarded operation panics.

// c = 97: `97 - 98` underflows.
pub fn upper_ascii_off_by_one(c: u8) -> u8 { //~ ERROR failed for `range_contains_constant_guards_refused::upper_ascii_off_by_one`
    if (b'a'..=b'z').contains(&c) { c - 98 } else { c }
}

// c = 0: the range starts at 0.
pub fn shifted_from_zero(c: u32) -> u32 { //~ ERROR failed for `range_contains_constant_guards_refused::shifted_from_zero`
    if (0..201).contains(&c) { c - 50 } else { c }
}

// c = 0: the range contains 0.
pub fn divided(c: i32) -> i32 { //~ ERROR failed for `range_contains_constant_guards_refused::divided`
    if (-5..=5).contains(&c) { 10 / c } else { 0 }
}

// i = 10: `..=` includes the end.
pub fn lookup_inclusive(t: &[u8; 10], i: usize) -> u8 { //~ ERROR failed for `range_contains_constant_guards_refused::lookup_inclusive`
    if (0..=10).contains(&i) { t[i] } else { 0 }
}
