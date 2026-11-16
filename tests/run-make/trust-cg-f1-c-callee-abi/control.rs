//! The positive control: the same recipe, no C callee. It completes on F1 and runs through the
//! same link-and-execute path the subjects take when they compile, so that path is not dead code.
#![crate_name = "control"]

pub fn f1_mix(a: i32, b: i32) -> i32 {
    a ^ b
}
