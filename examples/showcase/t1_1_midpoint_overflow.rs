// examples/showcase/t1_1_midpoint_overflow.rs — Arithmetic overflow detection.
//
// Trust Showcase T1.1: The classic midpoint overflow bug.
// The expression (a + b) can exceed usize::MAX for large inputs.
// This is the same bug found in JDK's Arrays.binarySearch (Bloch, 2006).
//
// What Trust catches:
//   VcKind::ArithmeticOverflow { op: Add, operand_tys: (usize, usize) }
//   Result: FAILED — counterexample: a = 1, b = 18446744073709551615
//   The division by 2 is trivially safe (constant non-zero divisor).
//
// Demonstrates: L0 safety verification, concrete counterexample extraction.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn get_midpoint(a: usize, b: usize) -> usize {
    (a + b) / 2 // OVERFLOW: a + b can exceed usize::MAX
}

fn main() {
    println!("{}", get_midpoint(3, 7));
}
