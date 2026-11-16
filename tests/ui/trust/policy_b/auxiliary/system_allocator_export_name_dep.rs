//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A verify-off dependency that DEFINES the libc allocator entry points std's `System`
//! allocator calls (`library/std/src/sys/alloc/unix.rs`: `malloc`, `calloc`, `realloc`,
//! `free`, `posix_memalign`) under `#[export_name]`, on functions named otherwise. Each
//! one forwards unchanged to the platform allocator's own entry points (Apple: the malloc
//! zone API of `<malloc/malloc.h>`; elsewhere glibc's `__libc_*`), so nothing here changes
//! what an allocation does: it only changes WHOSE code runs inside every `System`
//! allocation.
use std::ffi::{c_int, c_void};

#[cfg(target_vendor = "apple")]
mod platform {
    use std::ffi::c_void;
    // <malloc/malloc.h>
    unsafe extern "C" {
        fn malloc_default_zone() -> *mut c_void;
        fn malloc_zone_from_ptr(ptr: *const c_void) -> *mut c_void;
        fn malloc_zone_malloc(zone: *mut c_void, size: usize) -> *mut c_void;
        fn malloc_zone_calloc(zone: *mut c_void, num_items: usize, size: usize) -> *mut c_void;
        fn malloc_zone_realloc(zone: *mut c_void, ptr: *mut c_void, size: usize) -> *mut c_void;
        fn malloc_zone_free(zone: *mut c_void, ptr: *mut c_void);
        fn malloc_zone_memalign(zone: *mut c_void, alignment: usize, size: usize) -> *mut c_void;
    }
    unsafe fn zone_of(ptr: *mut c_void) -> *mut c_void {
        let zone = unsafe { malloc_zone_from_ptr(ptr) };
        if zone.is_null() { unsafe { malloc_default_zone() } } else { zone }
    }
    pub unsafe fn malloc(size: usize) -> *mut c_void {
        unsafe { malloc_zone_malloc(malloc_default_zone(), size) }
    }
    pub unsafe fn calloc(n: usize, size: usize) -> *mut c_void {
        unsafe { malloc_zone_calloc(malloc_default_zone(), n, size) }
    }
    pub unsafe fn realloc(ptr: *mut c_void, size: usize) -> *mut c_void {
        if ptr.is_null() {
            return unsafe { malloc(size) };
        }
        unsafe { malloc_zone_realloc(zone_of(ptr), ptr, size) }
    }
    pub unsafe fn free(ptr: *mut c_void) {
        if !ptr.is_null() {
            unsafe { malloc_zone_free(zone_of(ptr), ptr) }
        }
    }
    pub unsafe fn memalign(align: usize, size: usize) -> *mut c_void {
        unsafe { malloc_zone_memalign(malloc_default_zone(), align, size) }
    }
}

#[cfg(not(target_vendor = "apple"))]
mod platform {
    use std::ffi::c_void;
    // glibc's own entry points behind its public allocator symbols
    unsafe extern "C" {
        fn __libc_malloc(size: usize) -> *mut c_void;
        fn __libc_calloc(n: usize, size: usize) -> *mut c_void;
        fn __libc_realloc(ptr: *mut c_void, size: usize) -> *mut c_void;
        fn __libc_free(ptr: *mut c_void);
        fn __libc_memalign(align: usize, size: usize) -> *mut c_void;
    }
    pub unsafe fn malloc(size: usize) -> *mut c_void {
        unsafe { __libc_malloc(size) }
    }
    pub unsafe fn calloc(n: usize, size: usize) -> *mut c_void {
        unsafe { __libc_calloc(n, size) }
    }
    pub unsafe fn realloc(ptr: *mut c_void, size: usize) -> *mut c_void {
        unsafe { __libc_realloc(ptr, size) }
    }
    pub unsafe fn free(ptr: *mut c_void) {
        unsafe { __libc_free(ptr) }
    }
    pub unsafe fn memalign(align: usize, size: usize) -> *mut c_void {
        unsafe { __libc_memalign(align, size) }
    }
}

#[export_name = "malloc"]
pub unsafe extern "C" fn forward_malloc(size: usize) -> *mut c_void {
    unsafe { platform::malloc(size) }
}

#[export_name = "calloc"]
pub unsafe extern "C" fn forward_calloc(n: usize, size: usize) -> *mut c_void {
    unsafe { platform::calloc(n, size) }
}

#[export_name = "realloc"]
pub unsafe extern "C" fn forward_realloc(ptr: *mut c_void, size: usize) -> *mut c_void {
    unsafe { platform::realloc(ptr, size) }
}

#[export_name = "free"]
pub unsafe extern "C" fn forward_free(ptr: *mut c_void) {
    unsafe { platform::free(ptr) }
}

#[export_name = "posix_memalign"]
pub unsafe extern "C" fn forward_posix_memalign(
    out: *mut *mut c_void,
    align: usize,
    size: usize,
) -> c_int {
    let ptr = unsafe { platform::memalign(align, size) };
    if ptr.is_null() {
        return 12; // ENOMEM
    }
    unsafe { *out = ptr };
    0
}
