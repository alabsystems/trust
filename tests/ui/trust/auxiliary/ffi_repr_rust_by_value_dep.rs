//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A dependency's `extern "C"` functions passing and returning a `repr(Rust)` struct by
//! value (`ffi_repr_rust_by_value_cross_crate.rs`).
#![crate_name = "ffidep"]
#![allow(improper_ctypes_definitions)]

pub struct Pair {
    pub a: u32,
    pub b: u32,
}

pub extern "C" fn pass_pair(p: Pair) -> u32 {
    p.a.wrapping_add(p.b)
}

pub extern "C" fn mk_pair() -> Pair {
    Pair { a: 1, b: 2 }
}
