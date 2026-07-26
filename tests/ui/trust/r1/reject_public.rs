//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ check-fail
// `pub` makes `helper` externally reachable (an out-of-crate caller can pass 0), so
// caller coverage is not Total and R1 must NOT flip — the div-by-zero stays a failure.
pub fn helper(x: u32, divisor: u32) -> u32 { //~ ERROR Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed for
    x / divisor
}
pub fn caller() -> u32 {
    helper(10, 5)
}
