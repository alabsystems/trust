//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! A verify-off dependency declaring a `#[trust::panic_free]` trait method and
//! one provable impl of it, for `xcrate_foreign_trait_closure_phi.rs` (D4
//! increment B). Built the way `targo` builds a dependency unit.
#![feature(register_tool)]
#![register_tool(trust)]
#![crate_name = "xcphi_dep"]

pub trait T {
    #[trust::panic_free]
    fn m(&self) -> u32;
}

pub struct Good(pub u32);
impl T for Good {
    fn m(&self) -> u32 {
        self.0 & 0xff
    }
}
