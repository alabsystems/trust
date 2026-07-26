//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ check-fail
// `caller_bad` forwards an unconstrained `d`, so `divisor != 0` is NOT established at
// every call site. `decide_caller_propagation` requires ALL callers to discharge, so
// R1 must NOT flip — the div-by-zero stays a failure.
fn helper(x: u32, divisor: u32) -> u32 { //~ ERROR Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed for
    x / divisor
}
fn caller_ok() -> u32 {
    helper(10, 5)
}
fn caller_bad(d: u32) -> u32 {
    helper(10, d)
}
fn main() { //~ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed for
    let _ = caller_ok() + caller_bad(7);
}
