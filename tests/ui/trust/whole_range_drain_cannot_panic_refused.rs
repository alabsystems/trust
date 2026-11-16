//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! The refusing twins of `whole_range_drain_cannot_panic.rs`: each range can fall
//! outside the receiver, and each panics on an empty one.

pub fn drain_from_one(v: &mut Vec<u32>) { //~ ERROR failed for `whole_range_drain_cannot_panic_refused::drain_from_one`
    v.drain(1..);
}

pub fn drain_to_n(v: &mut Vec<u32>, n: usize) { //~ ERROR failed for `whole_range_drain_cannot_panic_refused::drain_to_n`
    v.drain(..n);
}

pub fn drain_first_inclusive(v: &mut Vec<u32>) { //~ ERROR failed for `whole_range_drain_cannot_panic_refused::drain_first_inclusive`
    v.drain(0..=0);
}
