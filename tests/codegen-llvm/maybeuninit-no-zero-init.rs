// Trust: Regression test for rust-lang#152541
// MaybeUninit::uninit() repeated in arrays should not generate memset.
// LLVM is free to materialize `undef` as zero, so emitting memset with undef
// can silently zero-initialize what should be uninit memory.

//@ compile-flags: -Copt-level=0

#![crate_type = "lib"]

use std::mem::MaybeUninit;

// CHECK-LABEL: @create_uninit_array
// CHECK-NOT: memset
#[no_mangle]
pub fn create_uninit_array() -> [MaybeUninit<u8>; 1048576] {
    [MaybeUninit::uninit(); 1048576]
}

// CHECK-LABEL: @create_uninit_u32_array
// CHECK-NOT: memset
#[no_mangle]
pub fn create_uninit_u32_array() -> [MaybeUninit<u32>; 4096] {
    [MaybeUninit::uninit(); 4096]
}
