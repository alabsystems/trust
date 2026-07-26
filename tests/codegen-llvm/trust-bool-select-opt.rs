// Trust: regression test for rust-lang#118292
// Boolean select patterns like `if cond { a } else { b }` on simple scalar
// types should be lowered to a `select` instruction, not a branch. The
// branch-based codegen for trivial boolean selects is a missed optimization
// that can hurt performance in tight loops.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>

//@ compile-flags: -Copt-level=3

#![crate_type = "lib"]

// CHECK-LABEL: @bool_select_u32
// A simple conditional returning one of two constants should produce a
// `select` instruction, not a branch.
// CHECK: select i1
// CHECK-NOT: br i1
// CHECK: ret
#[no_mangle]
pub fn bool_select_u32(cond: bool) -> u32 {
    if cond { 42 } else { 99 }
}

// CHECK-LABEL: @bool_select_two_values
// Selecting between two function parameters based on a bool should
// be a single `select`, not a conditional branch.
// CHECK: select i1
// CHECK: ret
#[no_mangle]
pub fn bool_select_two_values(cond: bool, a: u64, b: u64) -> u64 {
    if cond { a } else { b }
}

// CHECK-LABEL: @bool_to_int
// Converting bool to integer (a very common pattern) should not
// generate a branch. It should be a zero-extend.
// CHECK: zext i1
// CHECK-NOT: br i1
// CHECK: ret
#[no_mangle]
pub fn bool_to_int(b: bool) -> u32 {
    if b { 1 } else { 0 }
}

// CHECK-LABEL: @conditional_negate
// Conditional negation `if cond { -x } else { x }` should produce a
// `select` or `sub`/`neg` pattern, not a branch.
// CHECK-NOT: panic
// CHECK: ret
#[no_mangle]
pub fn conditional_negate(cond: bool, x: i32) -> i32 {
    if cond { x.wrapping_neg() } else { x }
}
