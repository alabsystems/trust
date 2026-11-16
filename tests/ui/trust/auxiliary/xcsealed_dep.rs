//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! A verify-off dependency's trait WITHOUT `#[trust::panic_free]` and its one
//! provable impl, for `xcrate_foreign_trait_closure_sealed.rs` (D4 increment B,
//! rung 2: the impl set is closed by enumeration, not by a declaration).
#![crate_name = "xcsealed_dep"]

pub trait Shape {
    fn area(&self) -> u32;
}

pub struct Sq(pub u32);
impl Shape for Sq {
    fn area(&self) -> u32 {
        self.0 & 0xff
    }
}
