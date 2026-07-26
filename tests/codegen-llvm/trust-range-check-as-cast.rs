// Trust: regression test for rust-lang#123542
// When casting between integer types where the source range is known to
// fit in the target type, the compiler should eliminate the range check.
// For example, `u16 as u32` never needs a bounds check, and `u8 as usize`
// should be a simple zero-extend with no conditional.
//
// The missed optimization occurs when `as` casts on values with known
// ranges still generate comparison + branch instead of direct widening.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>

//@ compile-flags: -Copt-level=3

#![crate_type = "lib"]

// CHECK-LABEL: @u8_to_u32_index
// A u8 value used as an index into a 256-element array should not
// generate a bounds check — u8 max (255) < array length (256).
// CHECK-NOT: panic
// CHECK-NOT: slice_index_fail
// CHECK-NOT: panic_bounds_check
// CHECK: ret
#[no_mangle]
pub fn u8_to_u32_index(table: &[u32; 256], idx: u8) -> u32 {
    table[idx as usize]
}

// CHECK-LABEL: @u16_widen_no_check
// Widening a u16 to u32 and comparing should be a simple zero-extend
// plus comparison, no additional range checks.
// CHECK: zext
// CHECK-NOT: panic
// CHECK: ret
#[no_mangle]
pub fn u16_widen_no_check(x: u16) -> u32 {
    let wide = x as u32;
    if wide < 1000 { wide } else { 0 }
}

// CHECK-LABEL: @clamped_to_u8
// When a u32 is clamped to 0..=255, the subsequent `as u8` cast should
// not generate any range-related checks since the value is proven in range.
// CHECK-NOT: panic
// CHECK: ret
#[no_mangle]
pub fn clamped_to_u8(x: u32) -> u8 {
    let clamped = if x > 255 { 255 } else { x };
    clamped as u8
}

// CHECK-LABEL: @enum_variant_count_in_range
// An enum with fewer than 256 variants has a discriminant that fits in u8.
// Using it as an array index into a table sized to the enum's variant count
// should not generate a bounds check.
// CHECK-NOT: panic
// CHECK-NOT: slice_index_fail
// CHECK-NOT: panic_bounds_check
// CHECK: ret
#[repr(u8)]
#[derive(Clone, Copy)]
pub enum SmallEnum {
    A, B, C, D, E, F, G, H,
}

#[no_mangle]
pub fn enum_variant_count_in_range(e: SmallEnum, table: &[u32; 8]) -> u32 {
    table[e as usize]
}
