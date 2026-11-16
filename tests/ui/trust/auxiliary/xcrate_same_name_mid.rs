//@ aux-build:xcrate_same_name_inner.rs
//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! Hands a consumer a value of the TRANSITIVE `xcsame` crate
//! (`xcrate_same_name_inner.rs`) without the consumer ever naming that crate.
//! See `xcrate_rederivation_identity.rs`.
#![crate_name = "xcsame_mid"]
extern crate xcsame;

pub fn make() -> xcsame::Good {
    xcsame::Good
}
