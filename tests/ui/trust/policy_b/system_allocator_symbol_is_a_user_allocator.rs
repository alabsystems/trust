//@ needs-trust-verify
//@ revisions: local dep_no_mangle dep_export_name dep_metadata_only dep_declares_only
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type bin
//@[dep_no_mangle] aux-build: system_allocator_symbols_dep.rs
//@[dep_export_name] aux-build: system_allocator_export_name_dep.rs
//@[dep_metadata_only] aux-build: system_allocator_free_metadata_only_dep.rs
//@[dep_declares_only] aux-build: system_allocator_declarations_dep.rs
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A crate that DEFINES a libc allocator symbol std's `System` allocator calls is a
//! user allocator, and is charged as one (2026-10-03).
//!
//! std's default global allocator is `System`, and `System` calls `malloc`, `calloc`,
//! `realloc`, `free` and `posix_memalign` by their C names
//! (`library/std/src/sys/alloc/unix.rs`). A Rust definition of one of them that is
//! linked into the binary runs in place of the platform's inside every allocation and
//! dealloc of the default chain — the channel a `#[global_allocator]` opens, without
//! the attribute (`has_global_allocator`) that the contract asked about. The
//! definitions here forward unchanged to the platform allocator; what is tested is
//! that they are SEEN, not what they do.
//!
//! MEASURED on stage 1 of origin/main `57121fb6713` (m3), in probes of this shape: with
//! the definitions in the binary itself, `make_box` and `make_string` were credited with
//! no premise row (`functions_verified` 4 of 15; the build failed only on the
//! forwarders' own unsafe bodies), and `nm` showed the executable's own `_malloc`. With
//! them in a verify-off dependency (`#[no_mangle]`, or `#[export_name = "malloc"]` on a
//! function named otherwise) nothing was credited, but not by this contract: the
//! spawn census answered UNKNOWN for every function, `plain` included. Now every
//! revision refuses the
//! two allocating functions with `contract:global-alloc-dealloc-panic-free:refused`,
//! naming the crate and the symbol; `plain`, which allocates nothing, keeps its credit
//! (pinned where the census does not refuse it: `local`, and `dep_metadata_only`, whose
//! dependency is built without codegen and so exports no symbol list — the census reads
//! that list and sees nothing there; this charge reads the dependency's definitions).
//! This file on that stage 1: `local`, `dep_no_mangle` and `dep_export_name` fail (no
//! refusal reported). `dep_metadata_only` was added later; with the dependency scan
//! reading `exported_non_generic_symbols` instead (a mutant), it built exit 0.
//!
//! `dep_declares_only` (review, 2026-10-03) is the control the scan's foreign-item
//! skip needs: a dependency that only DECLARES `malloc`/`free` in an `extern` block
//! (as the `libc` crate does) and calls them. rustc marks a foreign item `NO_MANGLE`
//! (`codegen_attrs.rs`), so without the skip every such graph would be refused; the
//! allocating functions keep their credit.
#[cfg(dep_declares_only)]
extern crate system_allocator_declarations_dep;
#[cfg(dep_export_name)]
extern crate system_allocator_export_name_dep;
#[cfg(dep_metadata_only)]
extern crate system_allocator_free_metadata_only_dep;
#[cfg(dep_no_mangle)]
extern crate system_allocator_symbols_dep;

use std::mem::forget;

/// The same forwarders the auxiliary crates define, in the binary itself.
#[cfg(local)]
mod interposer {
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
            fn malloc_zone_realloc(zone: *mut c_void, ptr: *mut c_void, size: usize)
            -> *mut c_void;
            fn malloc_zone_free(zone: *mut c_void, ptr: *mut c_void);
            fn malloc_zone_memalign(
                zone: *mut c_void,
                alignment: usize,
                size: usize,
            ) -> *mut c_void;
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

    #[no_mangle]
    pub unsafe extern "C" fn malloc(size: usize) -> *mut c_void {
        unsafe { platform::malloc(size) }
    }

    #[no_mangle]
    pub unsafe extern "C" fn calloc(n: usize, size: usize) -> *mut c_void {
        unsafe { platform::calloc(n, size) }
    }

    #[no_mangle]
    pub unsafe extern "C" fn realloc(ptr: *mut c_void, size: usize) -> *mut c_void {
        unsafe { platform::realloc(ptr, size) }
    }

    #[no_mangle]
    pub unsafe extern "C" fn free(ptr: *mut c_void) {
        unsafe { platform::free(ptr) }
    }

    #[no_mangle]
    pub unsafe extern "C" fn posix_memalign(
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
}

const T: [u8; 2] = [7, 8];

pub fn make_box(i: usize) -> Box<u8> {
    //[local,dep_no_mangle,dep_export_name,dep_metadata_only]~^ ERROR a libc allocator symbol std's default `System` allocator calls
    //[dep_declares_only]~^^ NOTE 0 runtime-checked out of
    Box::new(T[i & 1])
}

pub fn make_string(i: usize) -> String {
    //[local,dep_no_mangle,dep_export_name,dep_metadata_only]~^ ERROR a libc allocator symbol std's default `System` allocator calls
    //[dep_declares_only]~^^ NOTE 0 runtime-checked out of
    String::from(T[i & 1] as char)
}

pub fn plain(i: usize) -> u8 {
    //[local,dep_metadata_only,dep_declares_only]~^ NOTE 0 runtime-checked out of
    T[i & 1] / 2
}

fn main() {
    #[cfg(dep_declares_only)]
    system_allocator_declarations_dep::scratch();
    forget(make_box(1));
    forget(make_string(1));
    let _ = plain(1);
}
