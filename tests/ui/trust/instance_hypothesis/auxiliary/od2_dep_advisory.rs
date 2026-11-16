//@ compile-flags: --crate-type=rlib -Ztrust-verify=on -Ztrust-policy=advisory -Zalways-encode-mir
//@ edition: 2021
//@ no-prefer-dynamic
//! OD-1 phase 2: a dependency that DEFINES open generic dispatch, compiled
//! `-Ztrust-verify=on -Ztrust-policy=advisory`. Its own rows (`f`, `g` carry one instance hypothesis
//! each when it verifies) are its own; a consumer charges every instance IT names,
//! against sites it re-derives from this crate's encoded MIR, whatever this crate's
//! verification setting was.
pub trait Tr {
    fn m(&self) -> u32;
}

/// One open dispatch at its own parameter.
pub fn f<X: Tr>(x: &X) -> u32 {
    x.m()
}

/// A still-generic call to `f`: its instances reach `f`'s site.
pub fn g<Y: Tr>(y: &Y) -> u32 {
    f(y)
}

pub struct DepGood;

impl Tr for DepGood {
    fn m(&self) -> u32 {
        7
    }
}
