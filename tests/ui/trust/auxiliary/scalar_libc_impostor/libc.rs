//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//@ edition: 2024
//! A dependency whose crate NAME is `libc` (its file name makes it so), compiled
//! verify-off the way Targo compiles every dependency unit, and handed to the consumer
//! as `--extern` (`aux-crate`). It is not the crates.io or sysroot `libc`.
//!
//! FFI-SCALAR-LIBC-1 (2026-11-01): the integer-argument libc summaries
//! (`trust_vcgen::ffi_summary::scalar_libc_summaries`) bind a call only when the
//! declaration's Rust name AND its link symbol are the summarized symbol, at the
//! documented arity. `renamed::getpid` is spelled `getpid` in Rust but links to
//! `getppid`; `renamed::session_of` links to `getsid` under another Rust name;
//! `wrong_arity::getpid` takes an argument the C function does not; `honest::getsid`
//! links to `getsid` itself at its arity.
#![no_std]

pub mod renamed {
    unsafe extern "C" {
        /// Rust name `getpid`; link symbol `getppid`.
        #[link_name = "getppid"]
        pub fn getpid() -> i32;
        /// Rust name `session_of`; link symbol `getsid`.
        #[link_name = "getsid"]
        pub fn session_of(pid: i32) -> i32;
    }
}

pub mod wrong_arity {
    unsafe extern "C" {
        /// Rust name and link symbol `getpid`, with one parameter too many.
        pub fn getpid(x: i32) -> i32;
    }
}

pub mod honest {
    unsafe extern "C" {
        /// Rust name and link symbol `getsid`, one `pid_t` parameter.
        pub fn getsid(pid: i32) -> i32;
    }
}
