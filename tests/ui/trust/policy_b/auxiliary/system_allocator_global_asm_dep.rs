//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A verify-off dependency whose global assembly DEFINES `malloc`, the C symbol std's
//! `System` allocator calls (`library/std/src/sys/alloc/unix.rs`), as a tail branch to
//! a Rust function that forwards unchanged to the platform allocator (the malloc zone
//! API of `<malloc/malloc.h>`). No Rust item carries the name `malloc`: only the
//! assembly defines it, so nothing here changes what an allocation does, only WHOSE
//! code runs inside every `System` allocation.
use std::ffi::c_void;

// <malloc/malloc.h>
unsafe extern "C" {
    fn malloc_default_zone() -> *mut c_void;
    fn malloc_zone_malloc(zone: *mut c_void, size: usize) -> *mut c_void;
}

extern "C" fn forward_malloc(size: usize) -> *mut c_void {
    unsafe { malloc_zone_malloc(malloc_default_zone(), size) }
}

#[cfg(target_arch = "aarch64")]
std::arch::global_asm!(
    ".globl _malloc",
    ".p2align 2",
    "_malloc:",
    "b {forward}",
    forward = sym forward_malloc,
);

#[cfg(target_arch = "x86_64")]
std::arch::global_asm!(
    ".globl _malloc",
    "_malloc:",
    "jmp {forward}",
    forward = sym forward_malloc,
);
