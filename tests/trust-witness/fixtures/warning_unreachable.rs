#![warn(unreachable_code)]
#![allow(dead_code)]

// Typeck emits `unreachable_code` for this root. The witness does not carry
// diagnostics, so mint must exclude it and replay must cold-typecheck it.
pub fn warns() {
    return;
    let _never_reached = 1;
}
