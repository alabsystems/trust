//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! W4 ITER-HOF fix round 1: a verify-OFF dependency whose fn items the test
//! crate hands to std higher-order functions BY REFERENCE (adversarial probes
//! p41, p43 and p45 of the W4 ITER-HOF review). Each item
//! panics on 7; nothing in the verifying compilation looks inside it.

pub fn boom(x: &u32) -> u32 {
    assert!(*x != 7, "foreign item panicked");
    *x
}

pub fn boom_v(x: u32) -> u32 {
    assert!(x != 7, "foreign item panicked");
    x
}
