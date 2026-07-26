//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ check-fail
//! `#[trust::skip]` is an explicit unverified assumption in advisory
//! verification. It cannot bypass strict batteries-on verification, whose contract is
//! that every in-scope function is proved.
//!
//! Consumer crates opt in with `#![feature(register_tool)]` and
//! `#![register_tool(trust)]`. After that, `#[trust::skip]` applies on
//! any item.
//!
//! The advisory transport behavior is covered by the
//! `trust-assumption-rows` run-make test. This strict fixture must fail at
//! the policy boundary before `unsafe_div` can disappear from the inventory.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

#![feature(register_tool)]
#![register_tool(trust)]

#[trust::skip]
pub fn unsafe_div(x: i32, y: i32) -> i32 {
    //~^ ERROR Trust full verification skipped `trust_skip_attribute::unsafe_div`
    x / y // would be a strict L0 failure without `#[trust::skip]`
}

pub fn safe_caller(x: i32) -> i32 { //~ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed for
    if x != 0 { unsafe_div(10, x) } else { 0 }
}

fn main() { //~ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed for
    let _ = safe_caller(5);
}
