//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! FAIL-OPEN GUARD for the loop-reaching callee return summary (TRUST-10).
//!
//! `nine()` returns 9, so `i` reaches 8 and `byte >> 8` overflows: the summary
//! `nine() == 9` is TRUE and must leave this real bug refuted. If this file ever
//! compiles, the summary has stopped being a fact about the callee.
//!
//! Paired with `loop_callee_return_summary_no_false_refutation.rs`.
fn nine() -> usize {
    9
}

pub fn lsb_fold_real(byte: u8) -> u8 {
    //~^ ERROR Trust strict verification failed
    let mut r = 0;
    for i in 0..nine() {
        r |= (byte >> i) & 1;
    }
    r
}
