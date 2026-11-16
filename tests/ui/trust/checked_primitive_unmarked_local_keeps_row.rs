//@ edition: 2021
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! **L2a negative: a NAME is not the stamp.**
//!
//! The native checked-primitive arm admits only the TyCtxt-authenticated
//! `@trust-rustc-checked-primitive-method::` stamp, never a rendered
//! `checked_add`. A local free function with the same name and the same
//! `(i64, i64) -> Option<i64>` signature that really panics must keep its own
//! panic row, and so must a caller that reaches it. If either of these starts
//! verifying, the arm has started matching by name.
//!
//! The positive twin is `checked_primitive_native_total.rs`.

pub fn checked_add(a: i64, b: i64) -> Option<i64> {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE Trust verification: 0 proved, 1 failed, 1 unknown, 0 timed out, 1 runtime-checked out of 3
    if a == 7 {
        panic!("not the core method");
    }
    Some(a.wrapping_add(b))
}

pub fn caller(a: i64, b: i64) -> Option<i64> {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE Trust verification: 0 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 1
    checked_add(a, b)
}
