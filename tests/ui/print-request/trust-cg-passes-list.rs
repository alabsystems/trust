//! `-Cpasses=list` is handled before Session construction. Trust-CG must still
//! answer explicitly rather than inheriting the empty default implementation.

//@ needs-trust-cg-backend
//@ check-pass
//@ compile-flags: -Cpasses=list -Zcodegen-backend=trust-cg -Ztrust-verify=off

fn main() {}
