//@ aux-build:xcmreq_callee.rs
//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir -Copt-level=3
//@ edition: 2021
//@ no-prefer-dynamic
//! `xcmreq_mid.rs`'s `wrapper` at `-Copt-level=3`, still verify-off. A verify-off
//! session's MIR inliner runs at this level and keeps no `requires` call (that rule
//! is a verifying session's, `requires_callee_inlining`), so it copies `inc`'s
//! encoded body, whose overflow check `xcmreq_callee`'s verification elided, into
//! `wrapper`: the encoded MIR is `scope 1 (inlined xcmreq_callee::inc)` over a bare
//! `AddWithOverflow`, with no call and no `Assert` left.
#![crate_name = "xcmreq_mid_o3"]

extern crate xcmreq_callee;

pub fn wrapper(x: u32) -> u32 {
    xcmreq_callee::inc(x)
}
