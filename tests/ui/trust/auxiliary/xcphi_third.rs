//@ aux-build:xcphi_dep.rs
//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! A THIRD crate implementing `xcphi_dep::T` with a PANICKING body. Neither the
//! trait's crate nor the consumer's source contains this impl; it exists in the
//! consumer's crate graph only because the consumer links this crate. `Third` IS
//! THE ASSERTION — do not make it total.
#![crate_name = "xcphi_third"]
extern crate xcphi_dep;

pub struct Third;
impl xcphi_dep::T for Third {
    fn m(&self) -> u32 {
        panic!("boom")
    }
}
