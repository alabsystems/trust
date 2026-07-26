// examples/showcase/m4_binary_search_demo.rs — M4 acceptance: binary search bug detection.
//
// Trust Showcase M4: Binary search integer overflow (Bloch, 2006).
//
// The classic binary search bug: the midpoint calculation `(lo + hi) / 2`
// overflows when `lo + hi > usize::MAX`. This went undetected in the JDK's
// `java.util.Arrays.binarySearch` for nearly a decade.
//
// What Trust catches:
//   BUGGY VERSION:
//     VcKind::ArithmeticOverflow { op: Add } — on `(lo + hi) / 2`
//     Result: FAILED with counterexample (e.g., lo = usize::MAX/2+1, hi = usize::MAX/2+1)
//
//   FIXED VERSION:
//     Uses `lo + (hi - lo) / 2` — no overflow possible when lo <= hi.
//     Result: PROVED (all VCs are UNSAT)
//
// This is THE motivating example for Trust: the compiler finds the bug
// AND proves the fix correct.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

/// BUGGY: Classic binary search with integer overflow in midpoint calculation.
///
/// The expression `(lo + hi) / 2` overflows when `lo + hi > usize::MAX`.
/// Trust detects this as VcKind::ArithmeticOverflow { op: Add }.
fn binary_search_buggy(arr: &[i32], target: i32) -> Option<usize> {
    let mut lo = 0usize;
    let mut hi = arr.len();
    while lo < hi {
        let mid = (lo + hi) / 2; // BUG: overflow when lo + hi > usize::MAX
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

/// FIXED: Binary search with safe midpoint calculation.
///
/// The expression `lo + (hi - lo) / 2` avoids overflow because:
///   - `hi - lo` is non-negative (since lo <= hi is the loop invariant)
///   - `(hi - lo) / 2 <= hi - lo <= hi`
///   - `lo + (hi - lo) / 2 <= lo + hi - lo = hi <= arr.len()`
/// Trust proves all overflow VCs are UNSAT for this version.
fn binary_search_safe(arr: &[i32], target: i32) -> Option<usize> {
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

    // Both versions produce identical results for normal inputs:
    println!("BUGGY: search([2..16], 10) = {:?}", binary_search_buggy(&data, 10));
    println!("SAFE:  search([2..16], 10) = {:?}", binary_search_safe(&data, 10));
    println!("BUGGY: search([2..16], 5)  = {:?}", binary_search_buggy(&data, 5));
    println!("SAFE:  search([2..16], 5)  = {:?}", binary_search_safe(&data, 5));

    // The difference is invisible at runtime for small arrays.
    // Trust catches the latent bug BEFORE it triggers in production.
    println!();
    println!("Trust verification:");
    println!("  BUGGY: ArithmeticOverflow FAILED (counterexample exists)");
    println!("  SAFE:  ArithmeticOverflow PROVED (no overflow possible)");
}
