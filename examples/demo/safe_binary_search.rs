// examples/demo/safe_binary_search.rs -- Binary search with all bugs fixed.
//
// This is the "after" program for the Trust demo. The obvious overflow and
// underflow bugs are eliminated, but the current checked toolchain still leaves
// open obligations on this example. Keep it as a workflow/report case study,
// not as a guaranteed PASS example.
//
// Fixes applied:
//   1. Empty-array guard before `arr.len() - 1`.
//   2. Safe midpoint: `low + (high - low) / 2` instead of `(low + high) / 2`.
//   3. Checked subtraction for `high = mid - 1` when mid could be 0.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

/// Binary search over a sorted slice.
///
/// Returns `Some(index)` if `target` is found, `None` otherwise.
/// The source fixes the known midpoint and decrement bugs, but current proof
/// results may still be incomplete on this example.
fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    // FIX 1: guard against empty array (prevents arr.len() - 1 underflow)
    if arr.is_empty() {
        return None;
    }

    let mut low: usize = 0;
    let mut high: usize = arr.len() - 1; // safe: arr.len() >= 1

    while low <= high {
        // FIX 2: safe midpoint (high - low cannot underflow because high >= low
        // in this branch; adding half the difference to low cannot exceed high)
        let mid = low + (high - low) / 2;

        if arr[mid] == target {
            return Some(mid);
        } else if arr[mid] < target {
            low = mid + 1;
        } else {
            // FIX 3: checked subtraction (when mid == 0, we must exit)
            match mid.checked_sub(1) {
                Some(new_high) => high = new_high,
                None => break,
            }
        }
    }

    None
}

fn main() {
    let data = [2, 5, 8, 12, 16, 23, 38, 56, 72, 91];

    println!("Searching sorted array: {:?}", data);
    println!();

    // Normal case
    match binary_search(&data, 23) {
        Some(i) => println!("  Found 23 at index {i}"),
        None => println!("  23 not found"),
    }

    // Not found
    match binary_search(&data, 50) {
        Some(i) => println!("  Found 50 at index {i}"),
        None => println!("  50 not found"),
    }

    // Empty array -- returns None safely
    match binary_search(&[], 1) {
        Some(i) => println!("  Found 1 at index {i}"),
        None => println!("  1 not found in empty array (safe!)"),
    }

    // Edge cases
    match binary_search(&data, 2) {
        Some(i) => println!("  Found 2 (first element) at index {i}"),
        None => println!("  2 not found"),
    }
    match binary_search(&data, 91) {
        Some(i) => println!("  Found 91 (last element) at index {i}"),
        None => println!("  91 not found"),
    }
}
