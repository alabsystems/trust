//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! `xcphi_dep.rs` plus a PANICKING impl, `Bad`, that the consumer never
//! constructs. `Bad` IS THE ASSERTION — do not make it total: the foreign-trait
//! closure (D4 increment B) quantifies over every impl in the crate graph, not
//! over the types a program happens to use, so its presence alone must refuse.
//! This crate is verify-off because a verifying build of it would refuse `Bad`
//! at the impl (Φ's per-impl discharge); nothing a dependency's own build
//! decided is read by the consumer.
#![feature(register_tool)]
#![register_tool(trust)]
#![crate_name = "xcphi_dep_bad"]

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

pub struct Bad;
impl T for Bad {
    fn m(&self) -> u32 {
        panic!("boom")
    }
}
