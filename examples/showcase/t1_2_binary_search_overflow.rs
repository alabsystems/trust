// examples/showcase/t1_2_binary_search_overflow.rs — Integer overflow in binary search.
//
// Trust Showcase T1.2: The JDK binary search bug (Bloch, 2006).
// The midpoint calculation (lo + hi) / 2 overflows when lo + hi > usize::MAX.
// This bug went undetected in java.util.Arrays for nearly a decade.
//
// What Trust catches:
//   VcKind::ArithmeticOverflow { op: Add } — on `(lo + hi) / 2`
//   VcKind::IndexOutOfBounds — on `arr[mid]` (requires relational analysis)
//   Result: FAILED for overflow — detectable today.
//   Bounds check: out of scope for interval domain; requires relational
//   abstract domain (octagon/polyhedra) to prove 0 <= lo <= hi <= arr.len().
//
// Demonstrates: Real-world bug pattern, multi-VC generation.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    let mut lo = 0usize;
    let mut hi = arr.len();
    while lo < hi {
        let mid = (lo + hi) / 2; // OVERFLOW: same bug as T1.1
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
