// Trust test: negation overflow (signed MIN)
// VcKind: NegationOverflow { ty: Ty::i32() }
// Expected: NegationOverflow FAILED
// Counterexample: x = i32::MIN (-2147483648)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn negate(x: i32) -> i32 {
    -x // BUG: overflows when x == i32::MIN (-(-2^31) > i32::MAX)
}

fn main() {
    // Argv-derived (unknown) inputs: safe constants here would let the R1
    // caller-propagation lane prove the whole program safe and discharge the
    // isolated refutation this example exists to demonstrate.
    let n = std::env::args().len() as i32;
    let _ = negate(n);
}
