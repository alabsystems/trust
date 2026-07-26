// examples/demo/buggy_binary_search.rs -- Binary search with integer overflow bug.
//
// This is the "before" program for the Trust demo. The midpoint calculation
// `(low + high) / 2` can overflow when `low + high > usize::MAX`, and the
// empty-array case causes `arr.len() - 1` to underflow on usize.
//
// Trust catches both bugs automatically using ay and produces counterexamples.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

/// Binary search with two classic bugs:
///   1. `arr.len() - 1` underflows when `arr` is empty (usize wraps to MAX).
///   2. `(low + high) / 2` overflows for large indices.
fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    // BUG: underflows when arr.is_empty() -- arr.len() is 0, 0_usize - 1 wraps
    let mut low: usize = 0;
    let mut high: usize = arr.len() - 1;

    while low <= high {
        // BUG: overflows when low + high > usize::MAX
        let mid = (low + high) / 2;

        if arr[mid] == target {
            return Some(mid);
        } else if arr[mid] < target {
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }

    None
}

fn main() {
    let data = [2, 5, 8, 12, 16, 23, 38, 56, 72, 91];

    println!("Searching sorted array: {:?}", data);
    println!();

    // Normal case -- finds element
    match binary_search(&data, 23) {
        Some(i) => println!("  Found 23 at index {i}"),
        None => println!("  23 not found"),
    }

    // Not found case
    match binary_search(&data, 50) {
        Some(i) => println!("  Found 50 at index {i}"),
        None => println!("  50 not found"),
    }

    // Empty array -- triggers bug 1 (panics in debug, wraps in release)
    // Uncomment to see the panic:
    // binary_search(&[], 1);
}
