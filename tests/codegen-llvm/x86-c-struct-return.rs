// Trust: Regression test for rust-lang#102174 / tRust#921
// Verifies that extern "C" struct return ABI on x86 matches clang for all
// struct sizes <= 8 bytes, including non-power-of-two sizes (3, 5, 6, 7).
//
// On targets with abi_return_struct_as_int (macOS, FreeBSD, Windows, OpenBSD),
// structs <= 8 bytes must be returned in EAX(:EDX) cast to i8/i16/i32/i64.
// Previously, Rust only handled exact sizes 1/2/4/8 and fell through to sret
// for sizes 3/5/6/7, mismatching clang's ABI.
//
// This test uses -Zreg-struct-return on i686-unknown-linux-gnu to enable the
// register return path (equivalent to abi_return_struct_as_int=true behavior).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>

//@ revisions: ENABLED DISABLED
//@ add-minicore
//@ compile-flags: --target i686-unknown-linux-gnu -Cno-prepopulate-passes -Copt-level=3
//@ [ENABLED] compile-flags: -Zreg-struct-return
//@ needs-llvm-components: x86

#![crate_type = "lib"]
#![no_std]
#![no_core]
#![feature(no_core, lang_items)]

extern crate minicore;
use minicore::*;

// 1-byte struct
#[repr(C)]
pub struct S1 {
    a: u8,
}

// 2-byte struct
#[repr(C)]
pub struct S2 {
    a: u8,
    b: u8,
}

// 3-byte struct — key regression case for rust-lang#102174.
// Previously fell through to sret even with reg_struct_return.
#[repr(C)]
pub struct S3 {
    a: u8,
    b: u8,
    c: u8,
}

// 4-byte struct
#[repr(C)]
pub struct S4 {
    a: u16,
    b: u16,
}

// 5-byte struct — key regression case.
#[repr(C)]
pub struct S5 {
    a: u32,
    b: u8,
}

// 6-byte struct — key regression case.
#[repr(C)]
pub struct S6 {
    a: u32,
    b: u16,
}

// 7-byte struct — key regression case.
#[repr(C)]
pub struct S7 {
    a: u32,
    b: u16,
    c: u8,
}

// 8-byte struct
#[repr(C)]
pub struct S8 {
    a: u32,
    b: u32,
}

// 12-byte struct: always sret (> 8 bytes)
#[repr(C)]
pub struct S12 {
    a: u32,
    b: u32,
    c: u32,
}

// ENABLED: i8 @ret_s1()
// DISABLED: void @ret_s1(ptr {{.*}}sret
#[no_mangle]
pub extern "C" fn ret_s1() -> S1 {
    S1 { a: 1 }
}

// ENABLED: i16 @ret_s2()
// DISABLED: void @ret_s2(ptr {{.*}}sret
#[no_mangle]
pub extern "C" fn ret_s2() -> S2 {
    S2 { a: 1, b: 2 }
}

// ENABLED: i32 @ret_s3()
// DISABLED: void @ret_s3(ptr {{.*}}sret
#[no_mangle]
pub extern "C" fn ret_s3() -> S3 {
    S3 { a: 1, b: 2, c: 3 }
}

// ENABLED: i32 @ret_s4()
// DISABLED: void @ret_s4(ptr {{.*}}sret
#[no_mangle]
pub extern "C" fn ret_s4() -> S4 {
    S4 { a: 1, b: 2 }
}

// ENABLED: i64 @ret_s5()
// DISABLED: void @ret_s5(ptr {{.*}}sret
#[no_mangle]
pub extern "C" fn ret_s5() -> S5 {
    S5 { a: 1, b: 2 }
}

// ENABLED: i64 @ret_s6()
// DISABLED: void @ret_s6(ptr {{.*}}sret
#[no_mangle]
pub extern "C" fn ret_s6() -> S6 {
    S6 { a: 1, b: 2 }
}

// ENABLED: i64 @ret_s7()
// DISABLED: void @ret_s7(ptr {{.*}}sret
#[no_mangle]
pub extern "C" fn ret_s7() -> S7 {
    S7 { a: 1, b: 2, c: 3 }
}

// ENABLED: i64 @ret_s8()
// DISABLED: void @ret_s8(ptr {{.*}}sret
#[no_mangle]
pub extern "C" fn ret_s8() -> S8 {
    S8 { a: 1, b: 2 }
}

// CHECK: void @ret_s12(ptr {{.*}}sret
#[no_mangle]
pub extern "C" fn ret_s12() -> S12 {
    S12 { a: 1, b: 2, c: 3 }
}
