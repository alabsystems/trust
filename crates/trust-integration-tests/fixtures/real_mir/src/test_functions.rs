// test_functions.rs: Source functions for real MIR fixture generation.
//
// Compile with: trustc -Ztrust-policy=advisory \
//   -Ztrust-dump=mir:<output_dir> --edition 2021 test_functions.rs
//
// Each function covers one of the 7 categories from #941:
//   1. Simple arithmetic (overflow, div-by-zero)
//   2. Control flow (if/else, match, loops)
//   3. References and borrows
//   4. Generic functions (monomorphized MIR)
//   5. Drop elaboration
//   6. Closures and function pointers
//   7. Unsafe blocks
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// === Category 1: Simple arithmetic ===

/// Checked addition with a precondition that rules out overflow.
///
/// The fixture JSON checked into the repo carries `preconditions: [a + b <= u32::MAX]`
/// so the overflow VC is provably safe — this is the "safe" companion to
/// `safe_divide` (which has no precondition and remains failable).
#[requires("a + b <= u32::MAX")]
pub fn checked_add(a: u32, b: u32) -> u32 {
    a + b
}

/// Integer division that may divide by zero.
pub fn safe_divide(x: u32, y: u32) -> u32 {
    x / y
}

/// Wrapping multiplication (no overflow check).
pub fn wrapping_mul(a: u64, b: u64) -> u64 {
    a.wrapping_mul(b)
}

// === Category 2: Control flow ===

/// If/else with comparison.
pub fn max_of(a: i32, b: i32) -> i32 {
    if a > b { a } else { b }
}

/// Match on enum-like integer.
pub fn classify(n: i32) -> &'static str {
    match n {
        0 => "zero",
        1..=9 => "small",
        10..=99 => "medium",
        _ => "large",
    }
}

/// Simple loop with accumulator.
pub fn sum_to(n: u32) -> u32 {
    let mut acc = 0u32;
    let mut i = 0u32;
    while i < n {
        acc += i;
        i += 1;
    }
    acc
}

// === Category 3: References and borrows ===

/// Takes a shared reference and reads it.
pub fn read_ref(x: &i32) -> i32 {
    *x
}

/// Takes a mutable reference and modifies it.
pub fn increment(x: &mut i32) {
    *x += 1;
}

// === Category 4: Generic functions ===

/// Generic identity function (monomorphized per call site).
pub fn identity<T: Copy>(x: T) -> T {
    x
}

/// Generic max using Ord trait.
pub fn generic_max<T: Ord + Copy>(a: T, b: T) -> T {
    if a > b { a } else { b }
}

// === Category 5: Drop elaboration ===

/// Function that creates and drops a String.
pub fn string_creation() -> usize {
    let s = String::from("hello");
    s.len()
}

/// Function with a Vec that gets dropped.
pub fn vec_sum() -> i32 {
    let v = vec![1, 2, 3, 4, 5];
    v.iter().sum()
}

// === Category 6: Closures and function pointers ===

/// Function that uses a closure.
pub fn apply_twice(x: i32) -> i32 {
    let double = |n: i32| n * 2;
    double(double(x))
}

/// Function pointer usage.
pub fn apply_fn(f: fn(i32) -> i32, x: i32) -> i32 {
    f(x)
}

// === Category 7: Unsafe blocks ===

/// Unsafe pointer dereference.
pub unsafe fn unsafe_read(ptr: *const i32) -> i32 {
    *ptr
}

/// Unsafe mutable pointer write.
pub unsafe fn unsafe_write(ptr: *mut i32, val: i32) {
    *ptr = val;
}

// === Category 8: Explicit unsupported slice/fat-pointer/provenance gaps ===
//
// These functions are source anchors for the real-MIR coverage manifest. They
// must stay in the sample set even though their proof-grade modeling remains
// unsupported.

/// Slice indexing depends on fat-pointer length metadata and provenance.
pub fn slice_first(data: &[u32]) -> u32 {
    data[0]
}

/// Slice length reads the fat-pointer metadata lane.
pub fn slice_len(data: &[u32]) -> usize {
    data.len()
}

/// Array-to-slice unsizing synthesizes metadata that is not modeled yet.
pub fn array_as_slice_len(data: &[u32; 4]) -> usize {
    let slice: &[u32] = data;
    slice.len()
}

/// Raw slice pointer construction creates a data pointer plus metadata pair.
pub fn raw_slice_from_parts(ptr: *const u32, len: usize) -> *const [u32] {
    core::ptr::slice_from_raw_parts(ptr, len)
}

/// Pointer-to-integer casts expose address bits without preserving provenance.
pub fn exposed_addr_as_usize(ptr: *const u32) -> usize {
    ptr as usize
}

// === Monomorphization entry points ===
// These call generic functions with concrete types so MIR exists for them.

pub fn use_identity() -> i32 {
    identity(42i32)
}

pub fn use_generic_max() -> i32 {
    generic_max(10i32, 20i32)
}
