//@ revisions: off certify strict
//@ needs-trust-verify
//@ aux-build: rmw_literal_lanes.rs
//@ compile-flags: --crate-type=lib
//@[off] compile-flags: -Ztrust-verify=off -Ztrust-ir-lower=on
//@[off] check-pass
//@[certify] compile-flags: -Ztrust-verify=on -Ztrust-ir-lower=on -Ztrust-policy=certify
//@[certify] check-pass
//@[strict] compile-flags: -Ztrust-verify=on -Ztrust-ir-lower=strict -Ztrust-policy=advisory
//@[strict] check-fail
//@[strict] dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
// Copyright 2026 Andrew Yates
//! Trust (R101, 2026-10-21): **a drop-free ZST in a `()` lane the RMW builder floored takes the
//! `(Ty::Unit, PhantomData)` stand-in, and the body still lowers.**
//!
//! `[String; 0]` is zero-sized and needs no drop, but it is not a pure value (its element holds
//! pointers). Before the ordinary-registration repair, the whole-struct read of `self.n`
//! registered `ZeroLen { n: u32, z: () }` through `struct_ty_rmw_opaque` while `map_ty` spelled
//! the field `[ty.0 x 0]`. Measured before the fix on
//! a stage 1 of trust d2b525a13f (the route-G head), the literal inserts the array into the `()`
//! lane:
//!
//!   warning: trust-ir-lower semantic finalization failed: final Trust-IR module validation
//!   failed [OperandTypeMismatch] ...: OperandTypeMismatch { block: 0, op: "insert_field",
//!   role: "value", expected: "()", actual: "[ty.0 x 0]" }
//!
//! (`off`), a hard error under `certify`. The LOCAL case now keeps the faithful array spelling;
//! it must not be mistaken for a floor just because the first RMW retains its effect refusal.
//! The EXTERNAL case still registers a real `()` floor and takes the stand-in the call edges use
//! for the same population (d75f13f978's seed). Both literals lower and reach the strict
//! effect-conservation refusal. A literal refusal would instead report
//! `Adt(rmw-degraded field lane)`, as the external non-ZST companion controls do.
#![allow(dead_code)]

extern crate rmw_literal_lanes;

use rmw_literal_lanes::ExternalZeroLen;

pub struct ZeroLen {
    n: u32,
    z: [String; 0],
}

impl ZeroLen {
    pub fn rebuilt(&self) -> u32 {
        //[strict]~^ ERROR effect-conservation check refused it
        let n = self.n;
        let t = Self { n, z: [] };
        t.n
    }
}

pub fn external_rebuilt(this: &ExternalZeroLen) -> u32 {
    //[strict]~^ ERROR effect-conservation check refused it
    let n = this.n;
    let t = ExternalZeroLen { n, z: [] };
    t.n
}
