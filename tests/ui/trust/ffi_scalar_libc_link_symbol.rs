//@ needs-trust-verify
//@ only-macos
//@ edition: 2024
//@ aux-crate: libc=scalar_libc_impostor/libc.rs
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//! FFI-SCALAR-LIBC-1 (2026-11-01): an integer-argument libc summary
//! (`trust_vcgen::ffi_summary::scalar_libc_summaries`) is a fact about a C SYMBOL at its
//! documented arity, so it binds a call only when the declaration's Rust name
//! (`CalleeKey::foreign_block_leaf`) AND its link symbol
//! (`CalleeKey::upstream_foreign_link_symbol`, `tcx.symbol_name`) are the symbol, the
//! declaration is an UPSTREAM crate's, the crate is named `libc`, and the call passes
//! the documented number of arguments. The dependency here is named `libc` but is not
//! the real one (`auxiliary/scalar_libc_impostor/libc.rs`): a link symbol other than
//! the Rust name, or the wrong arity, keeps the `unmodeled FFI call` row; an honest
//! declaration of `getsid` binds (the crate name is defense in depth, not the identity,
//! exactly as for G1's `ffi_libc_contract_link_symbol.rs`). The honest declaration emits
//! no Trust error (an unexpected one fails this test); the counts below pin the three
//! negatives.

/// An upstream crate named `libc` (not the real one) declaring `getsid` honestly: the
/// link symbol is the identity, the crate name only defense in depth, so it binds.
pub fn honest_upstream_getsid(p: i32) -> i32 {
    // SAFETY: any pid is accepted.
    unsafe { ::libc::honest::getsid(p) }
}

/// `#[link_name = "getppid"] fn getpid()` in an upstream crate named `libc`: the row stays.
pub fn renamed_by_link_name() -> i32 {
    //~^ NOTE Trust verification: 0 proved, 0 failed, 1 unknown, 0 timed out, 0 runtime-checked, 2 skipped out of 3 obligation(s)
    //~^^ ERROR Trust Level 0 safety verification incomplete for `ffi_scalar_libc_link_symbol::renamed_by_link_name`: 1 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `ffi_scalar_libc_link_symbol::renamed_by_link_name`: 1 obligation(s) were not fully verified
    // SAFETY: negative control.
    unsafe { ::libc::renamed::getpid() }
}

/// `#[link_name = "getsid"] fn session_of(pid)`: the row stays.
pub fn symbol_under_another_name(p: i32) -> i32 {
    //~^ NOTE Trust verification: 0 proved, 0 failed, 1 unknown, 0 timed out, 0 runtime-checked, 2 skipped out of 3 obligation(s)
    //~^^ ERROR Trust Level 0 safety verification incomplete for `ffi_scalar_libc_link_symbol::symbol_under_another_name`: 1 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `ffi_scalar_libc_link_symbol::symbol_under_another_name`: 1 obligation(s) were not fully verified
    // SAFETY: negative control.
    unsafe { ::libc::renamed::session_of(p) }
}

/// `fn getpid(x: i32)`: the arity is not the C prototype's, so the row stays.
pub fn wrong_arity(x: i32) -> i32 {
    //~^ NOTE Trust verification: 0 proved, 0 failed, 1 unknown, 0 timed out, 0 runtime-checked, 2 skipped out of 3 obligation(s)
    //~^^ ERROR Trust Level 0 safety verification incomplete for `ffi_scalar_libc_link_symbol::wrong_arity`: 1 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `ffi_scalar_libc_link_symbol::wrong_arity`: 1 obligation(s) were not fully verified
    // SAFETY: negative control.
    unsafe { ::libc::wrong_arity::getpid(x) }
}
