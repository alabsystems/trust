//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Copt-level=0 --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-pass
//! Trust (native bundle, 2026-09-27): a unit-struct argument does not make the
//! native bundle's module invalid.
//!
//! `take(Marker, x)` passes a dataless constant, which reaches the bridge as
//! `ConstValue::Unit` and was spelled `TrustIrTy::Unit`, while `take`'s
//! parameter is the registered zero-field struct `Marker`. Full-module
//! validation refused the module (`call to take arg 0 type mismatch: expected
//! struct.0, got ()`), trust-mc's proof-authority gate refused the whole bundle,
//! and `pass`'s panic-freedom row stayed `runtime_checked` -- refused under
//! certify. The inventory's instances are `s[..]` on an `OsString` (`RangeFull`)
//! and `ok_or(AllocError)`. MEASURED on a stage-1 build of 7fbacf787f: this file
//! fails with exactly that validation error.
//!
//! The bridge now mints the argument as the empty aggregate at the declared
//! zero-field type -- the one value that type has -- and the row is proved. The
//! negative twin, `native_bundle_unit_struct_call_arg_panicking_callee_stays_closed.rs`,
//! keeps a reachable panic refused.

pub struct Marker;

#[inline(never)]
fn take(_m: Marker, x: u64) -> u64 {
    x
}

pub fn pass(x: u64) -> u64 {
    let r = take(Marker, x);
    if r != x {
        panic!()
    }
    r
}
