// Trust: regression test for rust-lang#127553
// When an index is already known to be in-bounds (e.g., from a prior
// bounds check, loop bound, or modulo operation), the compiler should
// eliminate redundant bounds checks.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>

//@ compile-flags: -Copt-level=3

#![crate_type = "lib"]

// CHECK-LABEL: @modulo_index_no_bounds_check
// An index computed via `% len` is always < len (for len > 0), so
// the subsequent indexing should not generate a bounds check.
// CHECK-NOT: panic
// CHECK-NOT: slice_index_fail
// CHECK-NOT: panic_bounds_check
#[no_mangle]
pub fn modulo_index_no_bounds_check(s: &[u8], i: usize) -> u8 {
    if s.is_empty() {
        return 0;
    }
    let idx = i % s.len();
    s[idx]
}

// CHECK-LABEL: @bitand_index_no_bounds_check
// An index computed via `& (len - 1)` on a power-of-two-sized slice
// is always in bounds. This pattern is common for hash tables.
// CHECK-NOT: panic
// CHECK-NOT: slice_index_fail
// CHECK-NOT: panic_bounds_check
#[no_mangle]
pub fn bitand_index_no_bounds_check(s: &[u8; 256], i: usize) -> u8 {
    let idx = i & 0xFF;
    s[idx]
}

// CHECK-LABEL: @loop_index_no_bounds_check
// Iterating with `0..s.len()` should not generate bounds checks since
// the index is always < len.
// CHECK-NOT: panic
// CHECK-NOT: slice_index_fail
// CHECK-NOT: panic_bounds_check
#[no_mangle]
pub fn loop_index_no_bounds_check(s: &[u8]) -> u8 {
    let mut sum: u8 = 0;
    for i in 0..s.len() {
        sum = sum.wrapping_add(s[i]);
    }
    sum
}

// CHECK-LABEL: @checked_then_index_no_bounds_check
// After an explicit bounds check, the subsequent index should not
// generate another bounds check.
// CHECK-NOT: slice_index_fail
// CHECK-NOT: panic_bounds_check
#[no_mangle]
pub fn checked_then_index_no_bounds_check(s: &[u8], i: usize) -> u8 {
    if i < s.len() { s[i] } else { 0 }
}
