// examples/binary_search.rs — Classic binary search with three intentional bugs.
//
// This is an M4 demo: trust-strengthen should detect all three bugs, propose
// specifications, and trust-backprop should rewrite the source to fix them.
//
// Bug 1: `arr.len() - 1` underflows when arr is empty (usize subtraction)
// Bug 2: `(low + high) / 2` overflows for large indices (usize addition)
// Bug 3: `high = mid - 1` underflows when mid is 0 (usize subtraction)
//
// Expected M4 loop behavior:
//   Iteration 1: Trust detects overflow/underflow VCs, ay produces counterexamples
//   Iteration 2: trust-strengthen infers #[requires(!arr.is_empty())] and safe midpoint
//   Iteration 3: trust-backprop rewrites source → binary_search_fixed.rs
//   Iteration 4: Trust re-checks the fixed version; full discharge is still a
//                frontier goal rather than a guaranteed outcome today
//
// Trust compiler output (stage1, ay-smtlib backend):
//   note: Trust [overflow:sub]: arithmetic overflow (Sub) — FAILED (ay-smtlib, 50ms)
//   note: Trust [overflow:add]: arithmetic overflow (Add) — FAILED (ay-smtlib, 12ms)
//   note: Trust [bounds]: index out of bounds — FAILED (ay-smtlib, 6ms)
//   note: Trust [slice]: slice bounds check — FAILED (ay-smtlib, 7ms)
//   note: Trust [slice]: slice bounds check — FAILED (ay-smtlib, 12ms)
//   note: Trust [overflow:add]: arithmetic overflow (Add) — FAILED (ay-smtlib, 31ms)
//   note: Trust [overflow:sub]: arithmetic overflow (Sub) — FAILED (ay-smtlib, 28ms)
//
// Runtime behavior: panics with "attempt to subtract with overflow" when
// searching for a value smaller than arr[0] (bug 3 triggers at mid=0).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    // BUG 1: underflow when arr.is_empty() — arr.len() is 0, subtract 1 wraps to usize::MAX
    // M4 fix: add `if arr.is_empty() { return None; }` guard, or
    //         infer #[requires(!arr.is_empty())]
    let mut low: usize = 0;
    let mut high: usize = arr.len() - 1;

    while low <= high {
        // BUG 2: overflow when low + high > usize::MAX
        // Counterexample: arr.len() = usize::MAX, low = usize::MAX/2, high = usize::MAX/2 + 1
        // M4 fix: rewrite to `low + (high - low) / 2`
        let mid = (low + high) / 2;

        if arr[mid] == target {
            return Some(mid);
        } else if arr[mid] < target {
            low = mid + 1;
        } else {
            // BUG 3: underflow when mid == 0 and target < arr[0]
            // Counterexample: arr = [5], target = 1 → mid = 0, high = 0 - 1 wraps
            // M4 fix: use `mid.checked_sub(1)` and break if None
            high = mid - 1;
        }
    }

    None
}

fn main() {
    let arr = [1, 3, 5, 7, 9, 11, 13, 15];

    // Normal case — should find element
    println!("search([1..15], 7) = {:?}", binary_search(&arr, 7));

    // Not found — exercises the high = mid - 1 underflow path
    println!("search([1..15], 0) = {:?}", binary_search(&arr, 0));

    // Empty array — triggers bug 1 immediately
    // Uncommenting this line would panic in debug mode:
    // println!("search([], 1) = {:?}", binary_search(&[], 1));
}
