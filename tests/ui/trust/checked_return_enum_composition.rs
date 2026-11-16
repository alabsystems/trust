//@ needs-trust-verify
//@ edition: 2021
//@ aux-build:checked_return_enum_types.rs
//@ compile-flags: --crate-type=lib -Ztrust-verify=on -Ztrust-policy=certify -Cpanic=abort
//@ compile-flags: -Ztrust-bundle-foreign-crate=checked_return_enum_types
//@ check-pass
//@ dont-check-compiler-stderr
//! Exact foreign method -> local helper -> law, without MIR inlining or an
//! authored helper contract. Both helpers need fresh original-body proofs.

extern crate checked_return_enum_types;
use checked_return_enum_types::{CallingConv, Linkage, Visibility};

#[inline(never)]
pub fn contradicts(linkage: Linkage, visibility: Visibility) -> bool {
    linkage.is_module_local() && matches!(visibility, Visibility::Hidden)
}

pub fn private_default() -> bool ensures result == false {
    contradicts(Linkage::Private, Visibility::Default)
}

pub fn private_hidden() -> bool ensures result {
    contradicts(Linkage::Private, Visibility::Hidden)
}

pub fn abi_surface() -> bool ensures result {
    CallingConv::RustCold.is_abi_surface()
}
