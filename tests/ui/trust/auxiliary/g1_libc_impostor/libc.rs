//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//@ edition: 2024
//! A dependency whose crate NAME is `libc` (its file name makes it so), compiled
//! verify-off the way Targo compiles every dependency unit, and handed to the consumer
//! as `--extern` (`aux-crate`). It is not the crates.io or sysroot `libc`.
//!
//! G1 review finding 1 (2026-10-27): `trust_vcgen::ffi_pointer_contract` believed every
//! `__error` declaration of a crate NAMED `libc`. `renamed::__error` below is spelled
//! `__error` in Rust but links to `malloc`, and `honest::__error` links to `__error`
//! itself. Only the second is the C symbol the contract documents.
#![no_std]

pub mod renamed {
    use core::ffi::c_int;

    unsafe extern "C" {
        /// Rust name `__error`; link symbol `malloc`.
        #[link_name = "malloc"]
        pub fn __error() -> *mut c_int;
    }
}

pub mod honest {
    use core::ffi::c_int;

    unsafe extern "C" {
        /// Rust name and link symbol `__error`: Darwin's errno slot.
        pub fn __error() -> *mut c_int;
    }
}
