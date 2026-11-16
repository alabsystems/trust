//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A dependency with no MIR for its plain functions (no `-Zalways-encode-mir`):
//! a tuple-variant constructor, and a function that hands a callable back.

pub enum Shape {
    Circle(u32),
    Square(u32),
}

#[inline(never)]
pub fn make_callback() -> fn() {
    noop
}

fn noop() {}
