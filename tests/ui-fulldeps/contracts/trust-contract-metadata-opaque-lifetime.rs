//@ build-pass
//@ compile-flags: --crate-type=lib --emit=metadata -Zcontract-checks=no
//@ ignore-stage1 (requires matching sysroot built with in-tree compiler)
//@ ignore-cross-compile
//@ ignore-remote
//@ edition: 2021

#![allow(incomplete_features)]
#![feature(contracts)]

pub trait Project<'a> {
    fn project(&self) -> &'a u32;
}

pub struct Holder<'a>(&'a u32);

impl<'a> Project<'a> for Holder<'a> {
    fn project(&self) -> &'a u32 {
        self.0
    }
}

// Regression test for metadata encoding of Trust contract tables: the public
// opaque return type captures `'a`, which creates non-contract-bearing opaque
// and lifetime-param DefIds. Encoding metadata must not query contracts for
// those DefIds.
pub fn opaque_with_captured_lifetime<'a>(value: &'a u32) -> impl Project<'a> + 'a {
    Holder(value)
}
