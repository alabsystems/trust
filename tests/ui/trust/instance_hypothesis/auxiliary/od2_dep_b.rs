//@ aux-build: od2_dep_a.rs
//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ edition: 2021
//@ no-prefer-dynamic
//! OD-1 phase 2 review fix (2026-10-05): the SECOND dependency: a generic that
//! reaches `od2_dep_a::f`'s site through a still-generic call into a THIRD crate,
//! behind its own `#[trust::assume_total]`.
#![feature(register_tool)]
#![register_tool(trust)]

extern crate od2_dep_a;

#[trust::assume_total]
pub fn g<X: od2_dep_a::Tr>(x: &X) -> u32 {
    od2_dep_a::f(x)
}

pub fn g_plain<X: od2_dep_a::Tr>(x: &X) -> u32 {
    od2_dep_a::f(x)
}
