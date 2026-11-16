//@ aux-build:xcmreq_callee.rs
//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir -Copt-level=3
//@ edition: 2021
//@ no-prefer-dynamic
//! DEP-MEMBER-REQ-1, the re-derivation half: a verify-off dependency built at
//! `-Copt-level=3` whose trait impls a consumer reaches through `dyn`, where the
//! C-FLOW bar RE-DERIVES the impl body as its own root (it is not a B-lane
//! member). Its MIR inliner copied `xcmreq_callee::inc`'s encoded body, whose
//! overflow check `xcmreq_callee`'s verification elided under `requires x < 100`,
//! into `<Sq as Shape>::area`: `scope 1 (inlined xcmreq_callee::inc)` over a bare
//! `AddWithOverflow`, with no call left to charge and no `Assert`.
//!
//! `Half` is the control: it inlines `xcmreq_callee::halve`, which owes its
//! caller nothing, so its body stays re-derivable.
#![crate_name = "xcmreq_dyn_o3"]

extern crate xcmreq_callee;

pub trait Shape {
    fn area(&self) -> u32;
}

pub struct Sq(pub u32);

impl Shape for Sq {
    fn area(&self) -> u32 {
        xcmreq_callee::inc(self.0)
    }
}

pub struct Half(pub u32);

impl Shape for Half {
    fn area(&self) -> u32 {
        xcmreq_callee::halve(self.0)
    }
}
