//@ needs-trust-verify
//@ only-macos
//@ edition: 2024
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//! FFI-SCALAR-LIBC-1 (2026-11-01): the integer-argument libc call summaries
//! (`trust_vcgen::ffi_summary::scalar_libc_summaries`; docs/TCB.md, "libc
//! integer-argument call summaries"), on the COMPILER path. The vcgen lane on the same
//! shapes' extracted MIR is `crates/trust-vcgen/tests/ffi_scalar_libc_realmir.rs`.
//!
//! Before: each function below failed the strict lane on one row, the FFI lane's
//! `unmodeled FFI call: no summary` (`hardened_ffi_boundary`, UNKNOWN) for the libc call
//! itself (on the combined G1+G3 tree 87c5b81eef: `0 proved, 0 failed, 1 unknown, ...,
//! 1 skipped out of 2` each). Now a call of the upstream `libc` crate's own declaration
//! at its documented arity mints no row, and the functions that make only that call
//! verify. The negative control keeps the row: the program's own `extern` block.
//! `ffi_scalar_libc_link_symbol.rs` pins the upstream negatives (a crate named `libc`
//! whose declaration links another symbol under a summarized name, links a summarized
//! symbol under another name, or takes an argument the C function does not) and an
//! honest upstream declaration. `hardened_ffi_gap_is_not_a_design_mandate.rs` (local
//! `getpgrp`/`raise` declarations) is unchanged by this. The positives emit no Trust
//! error (an unexpected one fails this test); the negative's counts below pin it.

#![feature(rustc_private)]

extern crate libc;

use core::ffi::c_int;

pub fn pid() -> libc::pid_t {
    // SAFETY: getpid has no preconditions.
    unsafe { libc::getpid() }
}

pub fn pgrp() -> libc::pid_t {
    // SAFETY: getpgrp has no preconditions.
    unsafe { libc::getpgrp() }
}

pub fn euid() -> libc::uid_t {
    // SAFETY: geteuid has no preconditions.
    unsafe { libc::geteuid() }
}

pub fn sid(p: libc::pid_t) -> libc::pid_t {
    // SAFETY: any pid is accepted.
    unsafe { libc::getsid(p) }
}

pub fn foreground(fd: c_int) -> libc::pid_t {
    // SAFETY: any fd is accepted.
    unsafe { libc::tcgetpgrp(fd) }
}

pub fn raise_it(sig: c_int) -> c_int {
    // SAFETY: any signal number is accepted.
    unsafe { libc::raise(sig) }
}

pub fn errno_slot() -> *mut c_int {
    // SAFETY: always succeeds.
    unsafe { libc::__error() }
}

mod own {
    unsafe extern "C" {
        pub fn getpid() -> i32;
    }
}

/// The program's own declaration of `getpid`: the row stays.
pub fn own_declaration() -> i32 {
    //~^ NOTE Trust verification: 0 proved, 0 failed, 1 unknown, 0 timed out, 0 runtime-checked, 2 skipped out of 3 obligation(s)
    //~^^ ERROR Trust Level 0 safety verification incomplete for `ffi_scalar_libc_summaries::own_declaration`: 1 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `ffi_scalar_libc_summaries::own_declaration`: 1 obligation(s) were not fully verified
    // SAFETY: negative control.
    unsafe { own::getpid() }
}
