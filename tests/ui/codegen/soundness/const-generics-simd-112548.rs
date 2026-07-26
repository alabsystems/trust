// Regression test for rust-lang#112548.
// Miscompilation with const generics and SIMD: when const generic
// parameters were used to determine SIMD vector widths or array sizes
// in generic functions, LLVM could generate incorrect vector operations.
// The monomorphizer would produce the correct MIR, but LLVM's type
// legalization or vector combining passes could mishandle the unusual
// widths resulting from const generic instantiation.
//
// The bug pattern:
// 1. A generic function parameterized by const N: usize operates on
//    arrays of size N
// 2. The function is instantiated with multiple different N values
// 3. LLVM's autovectorizer or type legalizer conflates the different
//    instantiations or generates incorrect shuffle masks
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ build-pass
//@ compile-flags: -C opt-level=3

#![allow(dead_code)]

// Const-generic array dot product — a pattern where LLVM might
// autovectorize with incorrect width.
#[inline(never)]
fn dot_product<const N: usize>(a: &[f32; N], b: &[f32; N]) -> f32 {
    let mut sum = 0.0f32;
    let mut i = 0;
    while i < N {
        sum += a[i] * b[i];
        i += 1;
    }
    sum
}

// Const-generic element-wise operation that produces a new array.
#[inline(never)]
fn add_arrays<const N: usize>(a: &[u32; N], b: &[u32; N]) -> [u32; N] {
    let mut result = [0u32; N];
    let mut i = 0;
    while i < N {
        result[i] = a[i].wrapping_add(b[i]);
        i += 1;
    }
    result
}

// Const-generic reduction — sum of elements.
#[inline(never)]
fn sum_array<const N: usize>(arr: &[u64; N]) -> u64 {
    let mut sum = 0u64;
    let mut i = 0;
    while i < N {
        sum += arr[i];
        i += 1;
    }
    sum
}

// Const-generic transformation with a non-power-of-2 size to stress
// vector legalization.
#[inline(never)]
fn scale_array<const N: usize>(arr: &[i32; N], factor: i32) -> [i32; N] {
    let mut result = [0i32; N];
    let mut i = 0;
    while i < N {
        result[i] = arr[i].wrapping_mul(factor);
        i += 1;
    }
    result
}

// Multiple const generic parameters interacting.
#[inline(never)]
fn copy_with_stride<const SRC: usize, const DST: usize>(
    src: &[u8; SRC],
    stride: usize,
) -> [u8; DST] {
    let mut result = [0u8; DST];
    let mut si = 0;
    let mut di = 0;
    while di < DST && si < SRC {
        result[di] = src[si];
        si += stride;
        di += 1;
    }
    result
}

fn main() {
    // Power-of-2 sizes (typical SIMD widths).
    let a4 = [1.0f32, 2.0, 3.0, 4.0];
    let b4 = [5.0f32, 6.0, 7.0, 8.0];
    let dot4 = dot_product(&a4, &b4);
    // 1*5 + 2*6 + 3*7 + 4*8 = 5 + 12 + 21 + 32 = 70
    assert_eq!(dot4, 70.0);

    let a8 = [1.0f32, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0];
    let b8 = [2.0f32, 2.0, 2.0, 2.0, 2.0, 2.0, 2.0, 2.0];
    assert_eq!(dot_product(&a8, &b8), 16.0);

    // Non-power-of-2 sizes (stress vector legalization).
    let a3 = [1.0f32, 2.0, 3.0];
    let b3 = [4.0f32, 5.0, 6.0];
    assert_eq!(dot_product(&a3, &b3), 32.0); // 4 + 10 + 18

    let a5 = [1.0f32, 2.0, 3.0, 4.0, 5.0];
    let b5 = [1.0f32, 1.0, 1.0, 1.0, 1.0];
    assert_eq!(dot_product(&a5, &b5), 15.0);

    // Integer element-wise add.
    let x = [10u32, 20, 30];
    let y = [1u32, 2, 3];
    assert_eq!(add_arrays(&x, &y), [11, 22, 33]);

    let x7 = [1u32, 2, 3, 4, 5, 6, 7];
    let y7 = [7u32, 6, 5, 4, 3, 2, 1];
    assert_eq!(add_arrays(&x7, &y7), [8, 8, 8, 8, 8, 8, 8]);

    // Reduction with different sizes.
    let s4 = [1u64, 2, 3, 4];
    assert_eq!(sum_array(&s4), 10);

    let s6 = [10u64, 20, 30, 40, 50, 60];
    assert_eq!(sum_array(&s6), 210);

    // Scaling with non-power-of-2 size.
    let v = [1i32, -2, 3, -4, 5];
    assert_eq!(scale_array(&v, 3), [3, -6, 9, -12, 15]);

    // Cross-size stride copy.
    let src = [10u8, 20, 30, 40, 50, 60, 70, 80];
    let dst: [u8; 4] = copy_with_stride(&src, 2); // indices 0, 2, 4, 6
    assert_eq!(dst, [10, 30, 50, 70]);
}
