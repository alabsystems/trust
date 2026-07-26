// examples/showcase/t1_4_sum_array_bounds.rs — Loop with array access.
//
// Trust Showcase T1.4: Index-based iteration over a slice.
// The loop `for i in 0..arr.len()` uses direct indexing with arr[i].
// The bounds check is provably safe because the iterator range is bounded
// by arr.len(), which the loop invariant analyzer can determine.
//
// What Trust catches:
//   VcKind::IndexOutOfBounds — on `arr[i]`
//   VcKind::ArithmeticOverflow { op: Add } — on `total += arr[i] as u64`
//   Expected result for bounds: PROVED — the Iterator pattern in
//   loop_invariant.rs handles 0..arr.len() index patterns.
//   Expected result for overflow: depends on array size bounds in the
//   abstract domain (u64 accumulator of u32 values).
//
// Demonstrates: Abstract interpretation discharge, loop analysis.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn sum_array(arr: &[u32]) -> u64 {
    let mut total: u64 = 0;
    for i in 0..arr.len() {
        total += arr[i] as u64;
    }
    total
}

fn main() {
    let data = [10u32, 20, 30, 40, 50];
    println!("sum([10, 20, 30, 40, 50]) = {}", sum_array(&data));
}
