// Trust test: signed arithmetic edge cases plus narrowing cast in one file
// VcKind: NegationOverflow, DivisionByZero, CastOverflow
// Expected: NegationOverflow FAILED, DivisionByZero FAILED
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#[allow(unused_variables)]
fn negate(x: i32) -> i32 {
    -x // BUG 1: NegationOverflow when x == i32::MIN
}

fn signed_divide(x: i32, y: i32) -> i32 {
    x / y // BUG 2: DivisionByZero when y == 0; ArithmeticOverflow(Div) when x == i32::MIN, y == -1
}

fn narrowing_cast(z: u32) -> u8 {
    z as u8 // BUG 3: CastOverflow when z > 255
}

fn main() {
    // Unknown-at-compile-time inputs: with safe constants here, the restored
    // R1 caller-propagation lane correctly proves the WHOLE PROGRAM safe and
    // discharges the helpers' isolated refutations — which is the capability
    // working, not the bug this example teaches. An argv-derived value has no
    // caller-established bound, so no sealed flip mints and the isolated
    // refutations stand, as the typed header expects.
    let n = std::env::args().len() as i32;
    let _ = negate(n);
    let _ = signed_divide(n, n - 1);
    let _ = narrowing_cast(n as u32);
}
