//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! A dependency compiled with verification OFF, the way Targo compiles every
//! dependency unit, for `unverified_edge_generic_instance.rs`. Every function here
//! is ordinary and returns a constant; what matters is only that NOTHING here is
//! checked by Trust, so a body of the crate under test that can run one of these
//! impls is an edge into unverified code. The impls are for foundational types
//! (`u32`, `()`, `str`) and a blanket one, so a type-argument check that asks only
//! whether `u32` is foreign cannot see them.
pub trait Blanket {
    fn bl(&self) -> u32 {
        0
    }
}

impl<T: ?Sized> Blanket for T {}

pub trait Act2 {
    fn a2(&self) -> u32;
}

impl Act2 for u32 {
    fn a2(&self) -> u32 {
        1
    }
}

impl Act2 for str {
    fn a2(&self) -> u32 {
        2
    }
}

pub trait Act3 {
    fn a3() -> u32;
}

impl Act3 for () {
    fn a3() -> u32 {
        3
    }
}
