// Regression test for rust-lang#121028.
// Miscompilation in release mode with array indexing: under -C opt-level=2
// or higher, LLVM could incorrectly optimize array index calculations,
// producing out-of-bounds accesses or reading wrong elements when the
// index computation involved multiple intermediate steps.
//
// The bug manifested when:
// 1. An array index was computed from multiple variables
// 2. The optimizer inlined the computation
// 3. LLVM's GVN or LICM pass incorrectly hoisted or merged index values
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ build-pass
//@ compile-flags: -C opt-level=2

#![allow(dead_code)]

const TABLE: [u32; 16] = [
    100, 200, 300, 400, 500, 600, 700, 800, 900, 1000, 1100, 1200, 1300, 1400, 1500, 1600,
];

// Computed index from multiple variables — the pattern that triggered
// the miscompilation when LLVM incorrectly merged index computations.
#[inline(never)]
fn lookup_computed_index(base: usize, offset: usize) -> u32 {
    let idx = (base + offset) % TABLE.len();
    TABLE[idx]
}

// Multiple array accesses in a loop with varying computed indices.
#[inline(never)]
fn sum_with_stride(arr: &[u32; 16], start: usize, stride: usize) -> u32 {
    let mut sum = 0u32;
    let mut idx = start % arr.len();
    for _ in 0..4 {
        sum += arr[idx];
        idx = (idx + stride) % arr.len();
    }
    sum
}

// Index computed via bit operations — another pattern sensitive to
// optimizer merging.
#[inline(never)]
fn bitwise_index_lookup(a: usize, b: usize) -> u32 {
    let idx = (a ^ b) & 0xF; // guaranteed in [0, 15]
    TABLE[idx]
}

// Conditional index selection that the optimizer might incorrectly
// speculate past.
#[inline(never)]
fn conditional_index(arr: &[u32; 16], cond: bool, idx_a: usize, idx_b: usize) -> u32 {
    let idx = if cond { idx_a % 16 } else { idx_b % 16 };
    arr[idx]
}

fn main() {
    // Computed index tests.
    assert_eq!(lookup_computed_index(3, 4), TABLE[7]);
    assert_eq!(lookup_computed_index(10, 10), TABLE[4]); // (10+10) % 16 = 4
    assert_eq!(lookup_computed_index(0, 0), TABLE[0]);
    assert_eq!(lookup_computed_index(15, 1), TABLE[0]); // (15+1) % 16 = 0

    // Strided sum: start=0, stride=4 → indices 0, 4, 8, 12.
    let expected = TABLE[0] + TABLE[4] + TABLE[8] + TABLE[12];
    assert_eq!(sum_with_stride(&TABLE, 0, 4), expected);

    // Strided sum: start=1, stride=3 → indices 1, 4, 7, 10.
    let expected2 = TABLE[1] + TABLE[4] + TABLE[7] + TABLE[10];
    assert_eq!(sum_with_stride(&TABLE, 1, 3), expected2);

    // Bitwise index tests.
    assert_eq!(bitwise_index_lookup(0xFF, 0xF0), TABLE[0x0F]); // 0xFF ^ 0xF0 = 0x0F
    assert_eq!(bitwise_index_lookup(0xAA, 0xA5), TABLE[0x0F]); // 0xAA ^ 0xA5 = 0x0F
    assert_eq!(bitwise_index_lookup(0, 0), TABLE[0]);

    // Conditional index tests.
    assert_eq!(conditional_index(&TABLE, true, 5, 10), TABLE[5]);
    assert_eq!(conditional_index(&TABLE, false, 5, 10), TABLE[10]);
    assert_eq!(conditional_index(&TABLE, true, 100, 0), TABLE[100 % 16]); // 100 % 16 = 4
}
