// examples/showcase/safe/safe_sum_array.rs — Safe array summation.
//
// Safe variant of T1.4 (t1_4_sum_array_bounds.rs).
// Uses iterator-based summation instead of manual indexing, eliminating
// the possibility of IndexOutOfBounds. The u64 accumulator prevents
// overflow for any practical array of u32 values (would need 2^32
// elements all at u32::MAX to overflow u64).
//
// Trust expected result: PROVED (no IndexOutOfBounds, no ArithmeticOverflow)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn sum_array(arr: &[u32]) -> u64 {
    let mut total: u64 = 0;
    for &val in arr {
        total += val as u64; // SAFE: iterator yields valid references
    }
    total
}

fn main() {
    let data = [10u32, 20, 30, 40, 50];
    println!("sum([10, 20, 30, 40, 50]) = {}", sum_array(&data));
    println!("sum([]) = {}", sum_array(&[]));
}
