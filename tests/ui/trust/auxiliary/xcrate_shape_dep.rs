//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! A verify-off dependency's trait and impls, reached through `dyn` in a
//! consumer (`xcrate_dyn_flow.rs`). `Boom` IS THE ASSERTION — do not make it
//! total. No `#[trust::panic_free]` here: C-FLOW (the value-flow case split),
//! not C-UNIVERSAL, is what D4 increment A serves. D4 increment B reuses it as
//! the rung-2 enumeration's panicking, never-constructed impl
//! (`xcrate_foreign_trait_closure_sealed.rs` `dep_boom`).
#![crate_name = "xcshape_dep"]

pub trait Shape {
    fn area(&self) -> u32;
}

pub struct Sq(pub u32);
impl Shape for Sq {
    fn area(&self) -> u32 {
        self.0 & 0xff
    }
}

pub struct Boom;
impl Shape for Boom {
    fn area(&self) -> u32 {
        panic!("boom")
    }
}
