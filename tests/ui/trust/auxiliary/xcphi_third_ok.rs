//@ aux-build:xcphi_dep.rs
//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! A THIRD crate implementing `xcphi_dep::T` with a PROVABLE body — the control
//! for `xcphi_third.rs`, and the crate an undeclared consumer must still refuse
//! to credit.
#![crate_name = "xcphi_third_ok"]
extern crate xcphi_dep;

pub struct Third;
impl xcphi_dep::T for Third {
    fn m(&self) -> u32 {
        3
    }
}
