//@ needs-trust-verify
//@ only-macos
//@ edition: 2024
//@ aux-crate: libc=g1_libc_impostor/libc.rs
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib --crate-name libc
//@ compile-flags: -Cmetadata=g1-local-libc
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//! G1 review finding 1 (2026-10-27): the documented return contract of `__error`
//! (`trust_vcgen::ffi_pointer_contract`) is a fact about a C SYMBOL, and a crate NAME
//! says nothing about which symbol a declaration links to. Before the fix the recognizer
//! believed every declaration whose crate was named `libc`, so:
//!
//! * the program's own `extern "C" { fn __error() -> *mut c_int; }`, compiled
//!   `--crate-name libc` (this file is), was discharged exactly like the real libc's
//!   (the reviewer measured 1 proved / 3 failed / 3 unknown of 9 rows -> 2 / 0 / 1 of 5);
//! * a dependency named `libc` declaring `#[link_name = "malloc"] fn __error()` would
//!   have been believed too.
//!
//! Now a declaration lends the contract only when it is an UPSTREAM crate's
//! (`CalleeKey::upstream_foreign_link_symbol` is `None` for a local one), its link
//! symbol is the contract's symbol (`tcx.symbol_name`), its arity is the documented
//! one, and its crate is named `libc`. `own_declaration` and `renamed_by_link_name` keep
//! every row; `honest_upstream_declaration` — an upstream crate named `libc` whose
//! declaration links to `__error` itself — is the positive control, and proves like
//! `ffi_libc_return_contract::errno_direct`. The per-function counts below pin all three.
//!
//! FFI-SCALAR-LIBC-1 (2026-11-01): the integer-argument libc call summaries bind under
//! the same identity (upstream declaration, link symbol, arity, crate name), so
//! `honest_upstream_declaration` also loses its `unmodeled FFI call` row for the
//! `__error` call (before: 2 proved, 1 unknown, 2 skipped of 5; now it verifies), and
//! both negatives keep it with every other row.

use core::ffi::c_int;

mod own {
    unsafe extern "C" {
        pub fn __error() -> *mut core::ffi::c_int;
    }
}

/// The program's own declaration, in a crate named `libc`: the rows stay.
pub fn own_declaration() -> c_int {
    //~^ NOTE Trust verification: 1 proved, 3 failed, 3 unknown, 0 timed out, 0 runtime-checked, 2 skipped out of 9 obligation(s)
    //~^^ ERROR Trust Level 0 safety verification incomplete for `libc::own_declaration`: 6 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `libc::own_declaration`: 6 obligation(s) were not fully verified
    // SAFETY: deliberately the program's own declaration (negative control).
    unsafe { *own::__error() }
}

/// An upstream `libc`-named crate's `__error` that links to `malloc`: the rows stay.
pub fn renamed_by_link_name() -> c_int {
    //~^ NOTE Trust verification: 1 proved, 3 failed, 3 unknown, 0 timed out, 0 runtime-checked, 2 skipped out of 9 obligation(s)
    //~^^ ERROR Trust Level 0 safety verification incomplete for `libc::renamed_by_link_name`: 6 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `libc::renamed_by_link_name`: 6 obligation(s) were not fully verified
    // SAFETY: deliberately a renamed declaration (negative control).
    unsafe { *::libc::renamed::__error() }
}

/// An upstream `libc`-named crate's `__error` that links to `__error`: proves.
pub fn honest_upstream_declaration() -> c_int {
    //~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 2 skipped out of 4 obligation(s)
    // SAFETY: this thread's errno slot.
    unsafe { *::libc::honest::__error() }
}
