// examples/binary_search_fixed.rs — Corrected binary search (what M4 should produce).
//
// This is the expected output of the M4 loop applied to binary_search.rs.
// All three bugs are fixed:
//   1. Empty array guard using `arr.is_empty()`
//   2. Safe midpoint using `low + (high - low) / 2`
//   3. Safe decrement using `mid.checked_sub(1)`
//
// This is the intended fixed version of the example. The source-level bugs are
// removed, but current proof results may still leave open obligations.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

/// Binary search over a sorted slice.
///
/// Returns `Some(index)` if `target` is found, `None` otherwise.
/// Requires: `arr` is sorted in ascending order.
fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    // FIX 1: explicit empty-array guard (replaces `arr.len() - 1` underflow)
    if arr.is_empty() {
        return None;
    }

    let mut low: usize = 0;
    let mut high: usize = arr.len() - 1; // safe: arr.len() >= 1

    while low <= high {
        // FIX 2: safe midpoint calculation (replaces `(low + high) / 2` overflow)
        // Since high >= low in this branch, `high - low` cannot underflow.
        // Adding the halved difference to low cannot overflow because
        // the result is at most high, which fits in usize.
        let mid = low + (high - low) / 2;

        if arr[mid] == target {
            return Some(mid);
        } else if arr[mid] < target {
            low = mid + 1;
        } else {
            // FIX 3: safe decrement (replaces `mid - 1` underflow)
            // When mid == 0 and target < arr[0], we must exit the loop.
            match mid.checked_sub(1) {
                Some(new_high) => high = new_high,
                None => break, // mid == 0, target not found
            }
        }
    }

    None
}

fn main() {
    let arr = [1, 3, 5, 7, 9, 11, 13, 15];

    // Normal case
    println!("search([1..15], 7) = {:?}", binary_search(&arr, 7));

    // Not found — safe even when target < arr[0]
    println!("search([1..15], 0) = {:?}", binary_search(&arr, 0));

    // Empty array — returns None without panicking
    println!("search([], 1) = {:?}", binary_search(&[], 1));

    // Edge cases for confidence
    println!("search([1..15], 1) = {:?}", binary_search(&arr, 1));   // first element
    println!("search([1..15], 15) = {:?}", binary_search(&arr, 15)); // last element
    println!("search([1..15], 4) = {:?}", binary_search(&arr, 4));   // between elements
    println!("search([42], 42) = {:?}", binary_search(&[42], 42));   // single-element found
    println!("search([42], 0) = {:?}", binary_search(&[42], 0));     // single-element not found
}
