// examples/showcase/safe/safe_binary_search.rs — Safe binary search.
//
// Safe variant of T1.2 (t1_2_binary_search_overflow.rs).
// Fixes the JDK binary search bug by using lo + (hi - lo) / 2
// instead of (lo + hi) / 2. Since hi >= lo is a loop invariant
// (guaranteed by the while condition and update logic), (hi - lo)
// cannot underflow, and lo + (hi - lo) / 2 cannot overflow.
//
// Trust expected result: PROVED for ArithmeticOverflow
//   (IndexOutOfBounds requires relational domain to prove lo <= mid < hi)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    let mut lo = 0usize;
    let mut hi = arr.len();
    while lo < hi {
        let mid = lo + (hi - lo) / 2; // SAFE: no overflow possible
        if arr[mid] == target {
            return Some(mid);
        }
        if arr[mid] < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    None
}

fn main() {
    let data = [2, 4, 6, 8, 10, 12, 14, 16];
    println!("search([2..16], 10) = {:?}", binary_search(&data, 10));
    println!("search([2..16], 5) = {:?}", binary_search(&data, 5));
}
