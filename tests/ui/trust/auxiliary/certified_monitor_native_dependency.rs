//@ no-prefer-dynamic

#![crate_type = "rlib"]

#[link(name = "trust_untrusted_dependency_native", kind = "dylib")]
unsafe extern "C" {}

pub fn ordinary_rust_symbol() {}
