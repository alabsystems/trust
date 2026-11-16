//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! THE SOUNDNESS HALF of `loop_break_bound_discharges_overflow.rs`.
//!
//! The same loop with a caller-supplied bound. At `n == u32::MAX` the counter
//! really does reach `u32::MAX` and the increment really does overflow, so this
//! must keep failing — and it is what makes the neighbouring file a fix rather
//! than a blanket loosening. The back edge here bounds the counter by `n`, and
//! `n` is unbounded, so no bound reaches the loop head.

pub fn f(n: u32) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    let mut r = 0;
    loop {
        r += 1;
        if r > n {
            break;
        }
    }
    r
}
