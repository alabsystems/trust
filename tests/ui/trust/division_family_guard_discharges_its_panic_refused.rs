//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! The division-family precondition is exact, and nothing weaker discharges it.
//! Every function below panics on the witness input.

// n = 0.
pub fn unguarded_rem_euclid(i: i64, n: i64) -> i64 { //~ ERROR strict verification failed
    i.rem_euclid(n)
}

// A nonzero divisor is not enough for a signed `rem_euclid`: i = i32::MIN, n = -1.
pub fn nonzero_is_not_enough(i: i32, n: i32) -> i32 { //~ ERROR strict verification failed
    if n != 0 { i.rem_euclid(n) } else { 0 }
}

// n = 0.
pub fn unguarded_wrapping_div(a: u32, n: u32) -> u32 { //~ ERROR strict verification failed
    a.wrapping_div(n)
}

// Both operands are literals, so neither carries a width; the overflow condition must
// take i8's MIN from the callee, not i64's (review round 17 saw these prove).
pub fn literal_min_div_euclid_i8() -> i8 { //~ ERROR strict verification failed
    (-128i8).div_euclid(-1)
}

pub fn literal_min_rem_euclid_i32() -> i32 { //~ ERROR strict verification failed
    i32::MIN.rem_euclid(-1)
}
