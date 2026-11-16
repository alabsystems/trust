//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! `xcsealed_dep.rs` plus a BLANKET impl. Both bodies are total; the blanket impl
//! is refused by rung 2's enumerability premise, not by its body.
#![crate_name = "xcsealed_blanket_dep"]

pub trait Shape {
    fn area(&self) -> u32;
}

pub trait Marker {}

pub struct Sq(pub u32);
impl Shape for Sq {
    fn area(&self) -> u32 {
        self.0 & 0xff
    }
}

impl<S: Marker> Shape for S {
    fn area(&self) -> u32 {
        0
    }
}
