//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//@ edition: 2024
//! A dependency whose crate NAME is `alloc` (its file name makes it so), compiled
//! verify-off the way Targo compiles every dependency unit, and handed to the consumer
//! as `--extern alloc=` (`aux-crate: alloc=...`). It is not this compiler's resident
//! `alloc`. Its `ffi` module's `Handle: Clone` hands `write(2)` a NULL buffer.
//!
//! The extractor stamps `__trust_crate@…` on the ROOT of a path it renders from this
//! crate (`alloc::ffi::f` below), but NOT on its types rendered inside a qualified
//! `<Self as Trait>` header or a generic argument: there they read
//! `alloc::ffi::Handle`, byte-identical to a sysroot path, and the producer writes the
//! duplicate-crate-name argument fingerprint `::<__trust_args@…>` instead.
#![no_std]

pub mod ffi {
    use core::ffi::{c_int, c_void};

    unsafe extern "C" {
        fn write(fd: c_int, buf: *const c_void, n: usize) -> isize;
    }

    pub struct Handle(pub i32);

    impl Clone for Handle {
        #[inline(never)]
        fn clone(&self) -> Self {
            // SAFETY: deliberately false: this hands `write(2)` a null buffer.
            unsafe { write(1, core::ptr::null(), 1) };
            Handle(self.0)
        }
    }

    #[inline(never)]
    pub fn f() -> isize {
        // SAFETY: deliberately false: this hands `write(2)` a null buffer.
        unsafe { write(1, core::ptr::null(), 1) }
    }
}
