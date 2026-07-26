// Trust: regression test for rust-lang#120556
// Small structs that fit in registers should be returned directly in
// registers without going through memory (memcpy). When a struct is
// small enough (e.g., two u32 fields = 8 bytes), the compiler should
// return it in a register pair, not allocate stack space and memcpy.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>

//@ compile-flags: -Copt-level=3

#![crate_type = "lib"]

#[derive(Clone, Copy)]
pub struct Point {
    pub x: u32,
    pub y: u32,
}

// CHECK-LABEL: @make_point
// Creating and returning a small struct should not involve memcpy.
// The two u32 fields should be packed into a single i64 return or
// returned as a register pair.
// CHECK-NOT: memcpy
// CHECK: ret
#[no_mangle]
pub fn make_point(x: u32, y: u32) -> Point {
    Point { x, y }
}

// CHECK-LABEL: @swap_point
// Swapping fields of a small struct should not involve memcpy.
// CHECK-NOT: memcpy
// CHECK: ret
#[no_mangle]
pub fn swap_point(p: Point) -> Point {
    Point { x: p.y, y: p.x }
}

#[derive(Clone, Copy)]
pub struct Pair<T: Copy> {
    pub first: T,
    pub second: T,
}

// CHECK-LABEL: @make_u64_pair
// A pair of u64 values (16 bytes) should still avoid memcpy on x86-64
// where two registers are available for return values.
// CHECK-NOT: memcpy
// CHECK: ret
#[no_mangle]
pub fn make_u64_pair(a: u64, b: u64) -> Pair<u64> {
    Pair { first: a, second: b }
}

// CHECK-LABEL: @add_points
// Element-wise addition of two small structs should be pure register
// operations with no memory traffic for the result.
// CHECK-NOT: memcpy
// CHECK: add
// CHECK: add
// CHECK: ret
#[no_mangle]
pub fn add_points(a: Point, b: Point) -> Point {
    Point {
        x: a.x.wrapping_add(b.x),
        y: a.y.wrapping_add(b.y),
    }
}
