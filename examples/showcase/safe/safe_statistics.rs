// examples/showcase/safe/safe_statistics.rs — Safe mean calculation.
//
// Safe variant of verify_statistics.rs which had three bugs:
//   1. Off-by-one: `i < data.len() + 1` causes IndexOutOfBounds
//   2. ArithmeticOverflow: `sum + data[i]` can exceed u32::MAX
//   3. DivisionByZero: `sum / data.len()` when data is empty
//
// This version fixes all three:
//   1. Uses iterator instead of manual indexing (no off-by-one possible)
//   2. Uses u64 accumulator (prevents overflow for practical inputs)
//   3. Returns None for empty input (prevents division by zero)
//
// Trust expected result: PROVED (all VCs satisfied)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn mean(data: &[u32]) -> Option<u64> {
    if data.is_empty() {
        return None; // SAFE: no division by zero
    }
    let mut sum: u64 = 0;
    for &val in data {
        sum += val as u64; // SAFE: iterator + u64 accumulator
    }
    Some(sum / data.len() as u64) // SAFE: len > 0 guaranteed
}

fn main() {
    println!("mean([1,2,3,4,5]) = {:?}", mean(&[1, 2, 3, 4, 5]));
    println!("mean([]) = {:?}", mean(&[]));
    println!("mean([MAX]) = {:?}", mean(&[u32::MAX]));
}
