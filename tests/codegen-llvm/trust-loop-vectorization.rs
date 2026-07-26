// Trust: regression test for rust-lang#126585
// Simple loops that perform element-wise operations on slices should be
// vectorized by LLVM. When the loop body is a straightforward scalar
// operation (add, multiply, bitwise), the autovectorizer should produce
// SIMD instructions. Missed vectorization for these simple patterns is
// a significant performance regression.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>

//@ compile-flags: -Copt-level=3

#![crate_type = "lib"]

// CHECK-LABEL: @sum_slice
// A simple summation loop should be vectorized. LLVM should produce
// vector add instructions (add <N x i32> or similar).
// CHECK: <{{[0-9]+}} x i32>
// CHECK: ret
#[no_mangle]
pub fn sum_slice(s: &[u32]) -> u32 {
    let mut sum: u32 = 0;
    for &x in s {
        sum = sum.wrapping_add(x);
    }
    sum
}

// CHECK-LABEL: @add_slices
// Element-wise addition of two slices into a destination should vectorize.
// CHECK: <{{[0-9]+}} x i32>
// CHECK: ret
#[no_mangle]
pub fn add_slices(dst: &mut [u32], a: &[u32], b: &[u32]) {
    let len = dst.len().min(a.len()).min(b.len());
    for i in 0..len {
        dst[i] = a[i].wrapping_add(b[i]);
    }
}

// CHECK-LABEL: @xor_slices
// Element-wise XOR should trivially vectorize.
// CHECK: <{{[0-9]+}} x i{{[0-9]+}}>
// CHECK: ret
#[no_mangle]
pub fn xor_slices(dst: &mut [u8], src: &[u8]) {
    let len = dst.len().min(src.len());
    for i in 0..len {
        dst[i] ^= src[i];
    }
}

// CHECK-LABEL: @find_max
// Finding the maximum in a slice should also vectorize with conditional
// moves or vector max instructions.
// CHECK-NOT: panic
// CHECK: ret
#[no_mangle]
pub fn find_max(s: &[u32]) -> u32 {
    let mut max = 0u32;
    for &x in s {
        if x > max {
            max = x;
        }
    }
    max
}
