#![crate_type = "rlib"]

#[unsafe(no_mangle)]
pub extern "C" fn dependency_controlled_symbol() {}

pub fn ordinary_rust_symbol() {}
