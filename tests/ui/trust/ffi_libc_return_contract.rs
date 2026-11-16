//@ needs-trust-verify
//@ only-macos
//@ edition: 2024
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//! G1 (2026-10-27): the documented return contracts of the pointer-returning libc
//! symbols `__error` and `getpwuid` (`trust_vcgen::ffi_pointer_contract`; docs/TCB.md,
//! "libc/Darwin pointer return-contract summaries"), on the COMPILER path. The vcgen
//! lane on the same shapes' extracted MIR is
//! `crates/trust-vcgen/tests/ffi_pointer_contract_realmir.rs`.
//!
//! Before: every deref of the errno slot and of a null-checked `getpwuid` result kept
//! its `[unsafe:sep:deref]` null / allocation / alignment rows (and the write row) as
//! FAILED, and rustc's `CheckNull`/`CheckAlignment` asserts in front of it were
//! `UnmodeledSafetyAssert` UNKNOWN rows (on main: `on_signal` 12 unproved rows,
//! `errno_direct` and `passwd_dir_is_null` 6 each). Now the null and write rows are
//! PROVED, the allocation and alignment rows and the asserts are dropped, and each
//! positive keeps only rows outside this change: the FFI lane's `unmodeled FFI call` row
//! for the libc call itself (`hardened_ffi_boundary`, G3's group) and, in `on_signal`, a
//! runtime-checked panic-freedom row. Each negative control keeps its rows: the null and
//! allocation rows without the null check, the allocation row after another `getpw*`
//! call, every row for the program's own `__error` declaration and for an offset pointer.
//! The per-function counts below pin both.
//!
//! The `&raw const` source-liveness rows of the same signal-mask code are pinned in
//! `addr_of_straight_run_storage_markers.rs`.
//!
//! G3-MANDATE-L1-ONLY-1 (combined G1+G3 landing, 2026-11-01): the `unmodeled FFI call`
//! row is an L0 `FfiBoundary` fail-close, not an L1 design mandate, so it no longer draws
//! the default lane's advisory. `errno_slot`, whose only unproved row it is, fails the
//! strict lane (its counts are unchanged). Before G3 it was pinned as an advisory.
//!
//! FFI-SCALAR-LIBC-1 (2026-11-01): `__error` takes no argument, so it is also one of
//! the integer-argument libc call summaries (`trust_vcgen::ffi_summary::
//! scalar_libc_summaries`), and a call of the upstream `libc` crate's own declaration
//! mints no `unmodeled FFI call` row. `errno_slot` and `errno_direct` now verify, and
//! `errno_offset` loses that one unknown row (its offset deref keeps every row); the
//! program's own declaration (`errno_own_declaration`) keeps it. Before, on the combined
//! G1+G3 tree: `errno_slot` 1 unknown of 2, `errno_direct` 1 unknown of 4,
//! `errno_offset` 3 unknown of 10.

#![feature(rustc_private)]

extern crate libc;

use core::ffi::c_int;

fn errno_slot() -> *mut c_int {
    // SAFETY: `__error` returns this thread's errno slot.
    unsafe { libc::__error() }
}

/// The errno save/restore a signal handler performs: proves.
pub extern "C" fn on_signal(_sig: c_int) {
    //~^ NOTE Trust verification: 5 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 6 obligation(s)
    //~^^ WARN Trust Level 0 safety verification incomplete for `ffi_libc_return_contract::on_signal`: 1 obligation(s) were not proved
    //~^^^ WARN Trust verification advisory for `ffi_libc_return_contract::on_signal`: 4 obligation(s) were not fully verified
    let slot = errno_slot();
    // SAFETY: the slot is this thread's errno.
    let saved = unsafe { *slot };
    // SAFETY: as above.
    unsafe { *slot = saved };
}

/// A direct deref of the libc call: proves.
pub fn errno_direct() -> c_int {
    //~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 skipped out of 3 obligation(s)
    // SAFETY: this thread's errno slot.
    unsafe { *libc::__error() }
}

/// `getpwuid` with the null check: proves.
pub fn passwd_dir_is_null() -> bool {
    //~^ NOTE Trust verification: 2 proved, 0 failed, 1 unknown, 0 timed out, 0 runtime-checked, 1 skipped out of 4 obligation(s)
    //~^^ ERROR Trust Level 0 safety verification incomplete for `ffi_libc_return_contract::passwd_dir_is_null`: 1 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `ffi_libc_return_contract::passwd_dir_is_null`: 2 obligation(s) were not fully verified
    // SAFETY: static storage or null, read before any other call.
    unsafe {
        let pw = libc::getpwuid(libc::getuid());
        if pw.is_null() {
            return true;
        }
        (*pw).pw_dir.is_null()
    }
}

/// `getpwuid` WITHOUT the null check: the null and allocation rows stay.
pub fn passwd_unchecked() -> bool {
    //~^ NOTE Trust verification: 1 proved, 2 failed, 2 unknown, 0 timed out, 0 runtime-checked, 1 skipped out of 6 obligation(s)
    //~^^ ERROR Trust Level 0 safety verification incomplete for `ffi_libc_return_contract::passwd_unchecked`: 4 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `ffi_libc_return_contract::passwd_unchecked`: 4 obligation(s) were not fully verified
    // SAFETY: deliberately missing the null check (negative control).
    unsafe { (*libc::getpwuid(libc::getuid())).pw_dir.is_null() }
}

/// A `getpwuid` result read after another `getpw*` call: the allocation row stays.
pub fn passwd_stale() -> bool {
    //~^ NOTE Trust verification: 2 proved, 1 failed, 2 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 7 obligation(s)
    //~^^ ERROR Trust Level 0 safety verification incomplete for `ffi_libc_return_contract::passwd_stale`: 4 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `ffi_libc_return_contract::passwd_stale`: 5 obligation(s) were not fully verified
    // SAFETY: deliberately stale (negative control).
    unsafe {
        let pw = libc::getpwuid(libc::getuid());
        if pw.is_null() {
            return true;
        }
        let _ = libc::getpwnam(c"root".as_ptr());
        (*pw).pw_dir.is_null()
    }
}

/// The program's own declaration of `__error` lends nothing: only an UPSTREAM crate's
/// declaration carries the link symbol the contract is keyed on
/// (`CalleeKey::upstream_foreign_link_symbol`). The rows stay.
/// `ffi_libc_contract_link_symbol.rs` pins the same shape compiled `--crate-name libc`,
/// and an upstream `#[link_name = "malloc"] fn __error()`.
mod own {
    unsafe extern "C" {
        pub fn __error() -> *mut core::ffi::c_int;
    }
}

pub fn errno_own_declaration() -> c_int {
    //~^ NOTE Trust verification: 1 proved, 3 failed, 3 unknown, 0 timed out, 0 runtime-checked, 2 skipped out of 9 obligation(s)
    //~^^ ERROR Trust Level 0 safety verification incomplete for `ffi_libc_return_contract::errno_own_declaration`: 6 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `ffi_libc_return_contract::errno_own_declaration`: 6 obligation(s) were not fully verified
    // SAFETY: deliberately the program's own declaration (negative control).
    unsafe { *own::__error() }
}

/// An offset from the errno slot: the deref of the offset pointer keeps its rows.
pub fn errno_offset() -> c_int {
    //~^ NOTE Trust verification: 1 proved, 4 failed, 2 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 9 obligation(s)
    //~^^ ERROR Trust Level 0 safety verification incomplete for `ffi_libc_return_contract::errno_offset`: 7 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `ffi_libc_return_contract::errno_offset`: 7 obligation(s) were not fully verified
    // SAFETY: deliberately out of bounds (negative control).
    unsafe { *libc::__error().add(1) }
}

/// `WIFEXITED` is a Rust `const fn` in the libc crate, not a foreign item: it is not
/// routed to the FFI lane's `unmodeled FFI call` stand-in (ffi_vcgen pattern 1 routes
/// only an unkeyed callee). The call keeps the cross-crate call policy's runtime-checked
/// absent-callee row, like any dependency function.
pub fn exited(status: c_int) -> bool {
    //~^ NOTE Trust verification: 0 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 1 obligation(s)
    //~^^ WARN Trust Level 0 safety verification incomplete for `ffi_libc_return_contract::exited`: 1 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `ffi_libc_return_contract::exited`: 1 obligation(s) were not fully verified
    libc::WIFEXITED(status)
}
