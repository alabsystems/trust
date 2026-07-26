#![expect(unreachable_code)]
#![allow(dead_code)]

// Typeck fulfills the `unreachable_code` expectation for this root without
// printing a warning. The witness does not serialize fulfilled-expectation
// state, so mint must exclude it and replay must cold-typecheck it.
pub fn fulfills_expectation() {
    return;
    let _never_reached = 1;
}
