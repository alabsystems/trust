// examples/showcase/t1_6_safe_midpoint_proof.rs — Proof of correctness.
//
// Trust Showcase T1.6: The textbook-correct midpoint (Bloch, 2006).
// This function computes the same result as (a + b) / 2 but cannot overflow.
// The key insight: a/2 <= MAX/2, b/2 <= MAX/2, and (a%2 + b%2)/2 <= 1,
// so their sum is at most MAX/2 + MAX/2 + 1 = MAX. No overflow possible.
//
// What Trust proves:
//   VcKind::ArithmeticOverflow { op: Add } — multiple VCs, all PROVED
//   Division and remainder by constant 2 do not generate DivisionByZero
//   or RemainderByZero VCs (statically known non-zero divisor).
//   Result: PROVED (all VCs are UNSAT)
//
// Demonstrates: Trust can prove the absence of bugs, not just find them.
// This is the complement to T1.1 — same computation, safe implementation.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn safe_midpoint(a: usize, b: usize) -> usize {
    a / 2 + b / 2 + (a % 2 + b % 2) / 2
}

fn main() {
    println!("{}", safe_midpoint(3, 7));
    // Also works for extreme values without overflow:
    println!("{}", safe_midpoint(usize::MAX, usize::MAX));
}
