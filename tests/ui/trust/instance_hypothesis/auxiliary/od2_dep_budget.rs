//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ edition: 2021
//@ no-prefer-dynamic
//! OD-1 phase 2 review fix (2026-10-05): a dependency generic whose instance at
//! `DA` a consumer discharges, and a `dyn Shape` whose only vtable provenance is
//! `Sq`, which a consumer's C-FLOW case split must re-derive to credit.

pub trait Tr {
    fn m(&self) -> u32;
}

pub fn f<X: Tr>(x: &X) -> u32 {
    x.m()
}

pub struct DA;

impl Tr for DA {
    fn m(&self) -> u32 {
        3
    }
}

pub trait Shape {
    fn area(&self) -> u32;
}

pub struct Sq(pub u32);

impl Shape for Sq {
    fn area(&self) -> u32 {
        self.0 / 2
    }
}
