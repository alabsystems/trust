//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A verify-off dependency that DECLARES the libc allocator entry points (an `extern`
//! block, as the `libc` crate does) and calls them, defining none. A declaration is a
//! foreign item: rustc marks it `NO_MANGLE`, but it binds to the platform's definition
//! and replaces nothing std's `System` allocator calls.
use std::ffi::c_void;

unsafe extern "C" {
    fn malloc(size: usize) -> *mut c_void;
    fn free(ptr: *mut c_void);
}

pub fn scratch() {
    unsafe { free(malloc(16)) }
}
