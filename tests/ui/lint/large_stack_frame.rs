// Trust: rust-lang#100914 regression test for the large_stack_frame lint.
//@ compile-flags: -Z stack_frame_limit=1000
//@ check-pass

#![deny(large_stack_frame)]

fn small() {
    let _x = [0u8; 100];
}

#[allow(large_stack_frame)]
fn allowed_large() {
    let _x = [0u8; 2000];
}

fn main() {
    small();
    allowed_large();
}
