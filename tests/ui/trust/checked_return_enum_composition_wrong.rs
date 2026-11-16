//@ needs-trust-verify
//@ edition: 2021
//@ aux-build:checked_return_enum_types.rs
//@ compile-flags: --crate-type=lib -Ztrust-verify=on -Ztrust-policy=certify -Cpanic=abort
//@ compile-flags: -Ztrust-bundle-foreign-crate=checked_return_enum_types
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Wrong twins must not inherit a true result from a name or neighboring law.

extern crate checked_return_enum_types;
use checked_return_enum_types::{CallingConv, Linkage, Visibility};

#[inline(never)]
pub fn contradicts(linkage: Linkage, visibility: Visibility) -> bool {
    linkage.is_module_local() && matches!(visibility, Visibility::Hidden)
}

pub fn wrong_private_default() -> bool ensures result {
    contradicts(Linkage::Private, Visibility::Default)
}

pub fn wrong_abi_surface() -> bool ensures result {
    CallingConv::Rust.is_abi_surface()
}
