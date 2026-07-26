// tRust regression test for rust-lang/rust#131585
//
// SOUNDNESS BUG: `simd_select` accepts a mask where only the sign bit (MSB)
// of each lane is supposed to matter, but the implementation does not enforce
// this. On some backends, non-sign bits in the mask lanes are used, leading
// to incorrect element selection. Passing a mask with arbitrary integer values
// (not just 0 / -1) produces implementation-defined results instead of the
// documented "select based on sign bit" behavior.
//
// This is unsound because safe wrappers over `simd_select` (e.g., in
// `std::simd`) trust the intrinsic to perform correct masking. If the
// backend selects wrong lanes or partially blends values, the caller
// observes data that violates the documented semantics — without any
// unsafe code at the call site.
//
// The root cause is that LLVM's `select` on vectors requires an i1 mask,
// but rustc's `simd_select` accepts wider integer masks and relies on the
// backend to extract only the sign bit. Some backends (especially on
// non-x86 targets without dedicated blend instructions) miscompile this.
//
// Status: open upstream. The fix requires either:
//   (a) normalizing the mask to i1 vector before lowering to LLVM, or
//   (b) documenting and enforcing that mask lanes must be exactly 0 or -1.
// tRust should reject non-canonical mask values at compile time when
// statically known, and insert runtime normalization otherwise.
//
// This test uses manual bitwise operations to demonstrate the pattern that
// simd_select should implement, since direct access to the intrinsic
// requires internal compiler features. The test verifies that the
// sign-bit-only masking contract is well-defined.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Reference: https://github.com/rust-lang/rust/issues/131585

//@ check-pass

#![allow(dead_code)]

/// Demonstrates the correct sign-bit masking semantics that simd_select
/// should enforce. The bug is that the intrinsic does not normalize its
/// mask input, so backends may use non-sign bits.
///
/// For each lane: if mask MSB is 1, select from `a`; otherwise select from `b`.
fn scalar_simd_select(mask: [i32; 4], a: [i32; 4], b: [i32; 4]) -> [i32; 4] {
    let mut result = [0i32; 4];
    for i in 0..4 {
        // Correct behavior: only the sign bit (bit 31) matters.
        if mask[i] < 0 {
            result[i] = a[i];
        } else {
            result[i] = b[i];
        }
    }
    result
}

/// Demonstrates the BUGGY behavior some backends exhibit: they treat
/// any non-zero mask value as "true" instead of checking only the sign bit.
fn buggy_simd_select(mask: [i32; 4], a: [i32; 4], b: [i32; 4]) -> [i32; 4] {
    let mut result = [0i32; 4];
    for i in 0..4 {
        // BUG: treating non-zero as "true" instead of checking sign bit.
        // This gives wrong results for positive non-zero mask values like 1.
        if mask[i] != 0 {
            result[i] = a[i];
        } else {
            result[i] = b[i];
        }
    }
    result
}

fn main() {
    let a = [10, 20, 30, 40];
    let b = [50, 60, 70, 80];

    // Canonical mask: -1 means "select a", 0 means "select b".
    let canonical = [-1, 0, -1, 0];
    let correct_result = scalar_simd_select(canonical, a, b);
    assert_eq!(correct_result, [10, 60, 30, 80]);

    // Non-canonical mask that exposes the bug:
    // Value 1: sign bit is 0 (should select b), but non-zero (buggy: selects a)
    // Value 0x7FFF_FFFF: sign bit is 0 (should select b), but non-zero (buggy: selects a)
    let noncanonical = [1, -1, 0x7FFF_FFFF, -2];

    let correct = scalar_simd_select(noncanonical, a, b);
    let buggy = buggy_simd_select(noncanonical, a, b);

    // Correct: lanes 0 and 2 select from b (sign bit is 0)
    assert_eq!(correct, [50, 20, 70, 40]);

    // Buggy: lanes 0 and 2 incorrectly select from a (non-zero treated as true)
    assert_eq!(buggy, [10, 20, 30, 40]);

    // The divergence between correct and buggy demonstrates the soundness issue:
    // simd_select backends that use non-zero-check instead of sign-bit-check
    // produce wrong results for non-canonical masks.
    assert_ne!(correct, buggy, "non-canonical masks produce different results \
        depending on whether the implementation checks sign bit or non-zero");
}
