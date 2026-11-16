//! Built by the DEFAULT backend; calls the F1-built control.
extern crate control;

fn main() {
    println!("mix={}", control::f1_mix(0x55, 7));
}
