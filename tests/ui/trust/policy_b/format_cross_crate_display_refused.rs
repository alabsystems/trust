//@ needs-trust-verify
//@ aux-build: cross_crate_display_dep.rs
//@ compile-flags: -Ztrust-verify=on -Copt-level=0
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! `format!` twin of `println_cross_crate_display_refused.rs` (2026-09-14). The
//! b59 `alloc::fmt::format` demotion demoted a `format!` row to a runtime-checked
//! `assumption:extern-call` ledger entry even when the formatted value's
//! `Display`/`Debug` was a PANICKING user/dependency impl — while the
//! byte-identical `println!` twin is a HARD error. `format!("{}", D(v))` where the
//! verify-off dep `D::fmt` panics compiled exit 0 and panicked at runtime.
//!
//! The demotion is now gated on `function_format_args_all_foundational_display`
//! (the same discriminator the `println!` path uses): it fires ONLY when every
//! `new_*::<T>` packer formats a foundational type. Here `main` packs
//! `new_display::<D>` with a non-foundational `D`, so the `format!` row stays
//! FATAL and refuses like `println!`. Foundational `format!` still demotes. This
//! file MUST stay red.
extern crate cross_crate_display_dep;
use cross_crate_display_dep::D;

fn main() {
    let v = std::hint::black_box(1i32);
    let s = format!("{}", D(v));
    let _ = std::hint::black_box(s);
}
