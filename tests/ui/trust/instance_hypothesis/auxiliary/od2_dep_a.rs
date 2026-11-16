//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ edition: 2021
//@ no-prefer-dynamic
//! OD-1 phase 2 review fix (2026-10-05): the FIRST of two dependencies. Its
//! generic `f` dispatches on its parameter; `od2_dep_b::g` calls it still generic.

pub trait Tr {
    fn m(&self) -> u32;
}

pub fn f<X: Tr>(x: &X) -> u32 {
    x.m()
}

pub struct DepBad;

impl Tr for DepBad {
    fn m(&self) -> u32 {
        panic!("boom")
    }
}
