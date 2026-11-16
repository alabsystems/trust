//@ compile-flags: --crate-type=rlib -Ztrust-verify=off --emit=metadata
//@ no-prefer-dynamic
//! A verify-off dependency built WITHOUT codegen (`--emit=metadata`, as `cargo check`
//! builds a dependency) that defines `free`, one of the libc allocator entry points std's
//! `System` allocator calls, forwarding unchanged to the platform allocator's own entry
//! point (Apple: the malloc zone API of `<malloc/malloc.h>`; elsewhere glibc's
//! `__libc_free`). A crate compiled without codegen exports no symbol list
//! (`exported_non_generic_symbols` is empty), so only its definitions show the symbol.
use std::ffi::c_void;

#[cfg(target_vendor = "apple")]
unsafe extern "C" {
    fn malloc_default_zone() -> *mut c_void;
    fn malloc_zone_from_ptr(ptr: *const c_void) -> *mut c_void;
    fn malloc_zone_free(zone: *mut c_void, ptr: *mut c_void);
}

#[cfg(target_vendor = "apple")]
#[no_mangle]
pub unsafe extern "C" fn free(ptr: *mut c_void) {
    if ptr.is_null() {
        return;
    }
    let zone = unsafe { malloc_zone_from_ptr(ptr) };
    let zone = if zone.is_null() { unsafe { malloc_default_zone() } } else { zone };
    unsafe { malloc_zone_free(zone, ptr) }
}

#[cfg(not(target_vendor = "apple"))]
unsafe extern "C" {
    fn __libc_free(ptr: *mut c_void);
}

#[cfg(not(target_vendor = "apple"))]
#[no_mangle]
pub unsafe extern "C" fn free(ptr: *mut c_void) {
    unsafe { __libc_free(ptr) }
}
