//! trust-cg accepts broad crate kinds for frontend-only outputs, but its
//! audited linked-artifact capability is currently exactly rlib. The print
//! request must report the latter rather than infer capability from the
//! no-link output mode used by the request itself.

//@ needs-trust-cg-backend
//@ check-pass
//@ compile-flags: --print=supported-crate-types -Zunstable-options -Zcodegen-backend=trust-cg -Ztrust-verify=off

fn main() {}
