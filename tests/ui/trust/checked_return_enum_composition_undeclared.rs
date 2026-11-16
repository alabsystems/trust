//@ needs-trust-verify
//@ edition: 2021
//@ aux-build:checked_return_enum_types.rs
//@ compile-flags: --crate-type=lib -Ztrust-verify=on -Ztrust-policy=certify -Cpanic=abort
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A matching pure method name is not permission to re-derive a dependency.

extern crate checked_return_enum_types;
use checked_return_enum_types::Linkage;

pub fn private_is_local() -> bool ensures result {
    Linkage::Private.is_module_local()
}
