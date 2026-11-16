//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//@ edition: 2024
//! A dependency whose crate NAME is `libc` (its file name makes it so), compiled
//! verify-off the way Targo compiles every dependency unit, and handed to the consumer
//! as `--extern` (`aux-crate`). It is not the crates.io or sysroot `libc`.
//!
//! REVIEW-A4C4-MINORS-1 fix-forward (2026-11-07): both modules declare Darwin's exact ten
//! `struct passwd` members and an honest `getpwuid` that links to `getpwuid`. Only the
//! `repr` differs: `honest` is libc's `#[repr(C)]` (72 bytes, 8-aligned), and
//! `over_aligned` is `#[repr(C, align(16))]` (80 bytes, 16-aligned), so a whole-struct
//! read through its pointer reads 8 bytes past the 72-byte object the C library returns.
#![no_std]
// Both modules declare `getpwuid`, each returning its own `passwd`.
#![allow(clashing_extern_declarations)]

macro_rules! passwd_module {
    ($module:ident, #[$repr:meta]) => {
        pub mod $module {
            use core::ffi::c_char;

            #[derive(Clone, Copy)]
            #[$repr]
            pub struct passwd {
                pub pw_name: *mut c_char,
                pub pw_passwd: *mut c_char,
                pub pw_uid: u32,
                pub pw_gid: u32,
                pub pw_change: i64,
                pub pw_class: *mut c_char,
                pub pw_gecos: *mut c_char,
                pub pw_dir: *mut c_char,
                pub pw_shell: *mut c_char,
                pub pw_expire: i64,
            }

            unsafe extern "C" {
                pub fn getpwuid(uid: u32) -> *mut passwd;
            }
        }
    };
}

passwd_module!(honest, #[repr(C)]);
passwd_module!(over_aligned, #[repr(C, align(16))]);
