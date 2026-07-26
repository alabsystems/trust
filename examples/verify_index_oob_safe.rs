// Trust test: array index out of bounds -- safe variant
// VcKind: IndexOutOfBounds
// Expected: IndexOutOfBounds PROVED (guard proves the index is in bounds)
// Safe pattern: if-guard `idx < 10` ensures index within array bounds
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn lookup_safe(arr: [u32; 10], idx: usize) -> u32 {
    if idx < 10 {
        arr[idx] // SAFE: guard ensures idx < array length
    } else {
        0 // fallback for out-of-bounds index
    }
}

fn main() {
    let arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    let _ = lookup_safe(arr, 5);
    let _ = lookup_safe(arr, 15); // takes fallback branch
}
