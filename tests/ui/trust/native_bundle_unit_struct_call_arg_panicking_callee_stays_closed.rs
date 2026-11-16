//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Copt-level=0 --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! Trust (native bundle, 2026-09-27): the negative twin of
//! `native_bundle_unit_struct_call_arg_proves.rs`. Minting a unit-struct call
//! argument at its declared zero-field type makes the bundle's module valid,
//! so the call is now modeled -- and `take` panics for `x == 7`, which `pass`
//! reaches. The build must stay refused: a valid module is proof input, never
//! a proof.

pub struct Marker;

#[inline(never)]
fn take(_m: Marker, x: u64) -> u64 {
    if x == 7 {
        panic!()
    }
    x
}

pub fn pass(x: u64) -> u64 {
    take(Marker, x)
}
