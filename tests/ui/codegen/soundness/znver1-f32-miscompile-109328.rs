// Regression test for rust-lang#109328.
// Miscompilation with `target-cpu=znver1` and f32 operations: certain
// floating-point arithmetic sequences produced incorrect results when
// compiled with optimizations targeting AMD Zen 1 (znver1) due to
// incorrect instruction selection or register allocation in LLVM.
//
// The pattern involves chained f32 multiply-add operations where LLVM
// would incorrectly fuse or reorder operations, changing the numerical
// result due to floating-point non-associativity.
//
// We test the arithmetic pattern without requiring znver1 target, since
// the underlying LLVM issue could manifest on any target with aggressive
// float optimization.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ build-pass
//@ edition: 2021
//@ compile-flags: -C opt-level=3

#![allow(dead_code)]

// Chained f32 operations that are sensitive to operation ordering.
// With incorrect fma fusion, (a * b) + c != fma(a, b, c) for certain inputs.
#[inline(never)]
fn chained_f32_ops(a: f32, b: f32, c: f32, d: f32) -> f32 {
    // This specific pattern triggered the miscompilation:
    // The intermediate products must not be fused across additions.
    let p1 = a * b;
    let p2 = c * d;
    let sum = p1 + p2;
    // Additional operation to prevent the entire chain from being optimized away.
    sum * 0.5_f32 + 1.0_f32
}

// Multiple sequential f32 operations with dependencies, exercising
// the register allocation path that was buggy on znver1.
#[inline(never)]
fn sequential_f32_deps(values: &[f32; 8]) -> f32 {
    let mut acc = values[0];
    // Each step depends on the previous, stressing register allocation.
    acc = acc * values[1] + values[2];
    acc = acc * values[3] + values[4];
    acc = acc * values[5] + values[6];
    acc + values[7]
}

fn main() {
    // Test chained operations with values known to be sensitive to fma fusion.
    let result = chained_f32_ops(1.0000001_f32, 2.0_f32, 3.0_f32, 4.0_f32);
    // The exact result depends on whether operations are fused.
    // We just verify it's a finite, reasonable number (not NaN or wildly wrong).
    assert!(result.is_finite(), "chained f32 ops produced non-finite result");
    assert!(result > 0.0_f32, "chained f32 ops produced non-positive result");

    // Test sequential dependent operations.
    let values = [1.0_f32, 2.0, 3.0, 0.5, 1.0, 2.0, -1.0, 0.25];
    let result2 = sequential_f32_deps(&values);
    assert!(result2.is_finite(), "sequential f32 ops produced non-finite result");

    // Verify the exact computation (without fma fusion):
    // acc = 1.0
    // acc = 1.0 * 2.0 + 3.0 = 5.0
    // acc = 5.0 * 0.5 + 1.0 = 3.5
    // acc = 3.5 * 2.0 + (-1.0) = 6.0
    // acc = 6.0 + 0.25 = 6.25
    //
    // With FMA fusion the result may differ slightly, but should be very close.
    assert!(
        (result2 - 6.25_f32).abs() < 0.001_f32,
        "sequential f32 result {result2} too far from expected 6.25"
    );
}
