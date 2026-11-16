//@ aux-build:xcmreq_callee.rs
//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ edition: 2021
//@ no-prefer-dynamic
//! An ordinary dependency, compiled the way `targo` compiles a non-root unit:
//! `-Ztrust-verify=off`, so nothing here is verified and nothing charges `wrapper`'s
//! call for `inc`'s `requires`, plus `-Zalways-encode-mir` so a caller that declares
//! this crate in its bundling scope can bundle these bodies. At `-O0` its MIR keeps
//! the CALL to `xcmreq_callee::inc`.
#![crate_name = "xcmreq_mid"]

extern crate xcmreq_callee;

/// Calls a `requires` function with an argument nothing constrains.
pub fn wrapper(x: u32) -> u32 {
    xcmreq_callee::inc(x)
}

/// The same through `inc_via` and its private callee `bump` (ADVISORY-REQUIRES-CROSS-CRATE
/// kept `inc`'s check, not `bump`'s; ADVISORY-REQUIRES-TRANSITIVE-1 keeps `bump`'s).
pub fn wrapper_via(x: u32) -> u32 {
    xcmreq_callee::inc_via(x)
}

/// The control: calls a dependency function that owes its caller nothing.
pub fn pick(x: u32) -> u32 {
    xcmreq_callee::cap(x)
}
