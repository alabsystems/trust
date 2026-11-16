//@ needs-trust-verify
//@ aux-build: cross_crate_display_dep.rs
//@ compile-flags: -Ztrust-verify=on -Copt-level=0
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! Hidden-packer `to_string` twin of `format_cross_crate_display_refused.rs`
//! (2026-09-14). `d.to_string()` is `<D as ToString>::to_string(&d)`, which packs
//! `core::fmt::rt::Argument::new_display::<D>` INSIDE the alloc `ToString` blanket
//! impl body — OUT of `main`'s MIR. So the main-MIR packer scan sees no
//! non-foundational packer and the `alloc::fmt::format` "runs a user Display"
//! extern-call row was demoted/tolerated — ACCEPTED, then a panic at runtime.
//! The direct twin `println!("{}", d)`/`format!("{}", d)` is correctly refused.
//!
//! `function_format_args_all_foundational_display` now also reads the formatted
//! `Self` type from the `ToString::to_string` DISPATCH call in `main` (not from a
//! packer, and never from the row, which cannot carry the type): a non-foundational
//! `Self` makes the function fail closed, so `to_string` of a dep `Display`
//! refuses like `println!`/`format!`. Foundational `to_string` (`41i32`, `"s"`,
//! `String`) still compiles. This file MUST stay red.
extern crate cross_crate_display_dep;
use cross_crate_display_dep::D;

fn main() {
    let d = D(std::hint::black_box(1i32));
    let s = d.to_string();
    let _ = std::hint::black_box(s);
}
