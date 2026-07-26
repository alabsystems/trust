// Unsafe functions: raw pointer operations, transmute.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

/// # Safety
/// `ptr` must be valid and aligned for a `u8` read.
pub unsafe fn read_byte(ptr: *const u8) -> u8 {
    // SAFETY: caller guarantees validity
    *ptr
}

/// # Safety
/// `ptr` must be valid and aligned for a `u8` write.
pub unsafe fn write_byte(ptr: *mut u8, val: u8) {
    // SAFETY: caller guarantees validity
    *ptr = val;
}

/// # Safety
/// Both pointers must be valid, aligned, and non-overlapping.
pub unsafe fn swap_raw(a: *mut u32, b: *mut u32) {
    // SAFETY: caller guarantees validity
    let tmp = *a;
    *a = *b;
    *b = tmp;
}

/// # Safety
/// `base.offset(offset)` must be within allocated bounds.
pub unsafe fn offset_read(base: *const u32, offset: isize) -> u32 {
    // SAFETY: caller guarantees validity
    *base.offset(offset)
}

pub fn safe_read(data: &[u8], index: usize) -> Option<u8> {
    data.get(index).copied()
}

pub fn bytes_to_u32(bytes: &[u8; 4]) -> u32 {
    u32::from_le_bytes(*bytes)
}

/// # Safety
/// `ptr` must point to `len` valid bytes.
pub unsafe fn slice_from_raw(ptr: *const u8, len: usize) -> &'static [u8] {
    // SAFETY: caller guarantees validity
    std::slice::from_raw_parts(ptr, len)
}
