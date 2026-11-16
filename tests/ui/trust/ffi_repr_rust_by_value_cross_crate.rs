// Trust: KNOWN_HAZARDS "producer C-ABI residuals after S2/S3", third residual. A call to a
// dependency's `pub extern "C" fn` that passes or returns a `repr(Rust)` struct by value
// made trust-ir-build's `FfiStructReprUnpinned` reject the WHOLE crate module: every function
// in the crate (`plain` here) lost the native verification route, and the strict lanes made
// the module failure a hard error. S2's guard only covered LOCAL foreign items. It now covers
// every non-local non-Rust-ABI callee, so only `sum` and `first` are refused, with
// `Callee(foreign-ABI repr(Rust) struct by value)`, and the module validates.
//@ aux-build:ffi_repr_rust_by_value_dep.rs
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -Ztrust-ir-lower=on --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ forbid-output: FfiStructReprUnpinned
//@ forbid-output: final Trust-IR module validation failed
extern crate ffidep;

pub fn sum() -> u32 {
    ffidep::pass_pair(ffidep::Pair { a: 3, b: 4 })
}

pub fn first() -> u32 {
    ffidep::mk_pair().a
}

pub fn plain(x: u32) -> u32 {
    x / 2
}
