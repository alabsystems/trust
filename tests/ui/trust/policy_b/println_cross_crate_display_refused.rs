//@ needs-trust-verify
//@ aux-build: cross_crate_display_dep.rs
//@ compile-flags: -Ztrust-verify=on -Copt-level=0
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! The cross-crate twin of `println_user_display_stays_closed.rs` (HOLE —
//! indirect Display fold-mask, 2026-09-14). A value formatted through a
//! DEPENDENCY `Display` (built `-Ztrust-verify=off`) whose `fmt` PANICS may NOT
//! ride the std print-backend completeness gap: the `fmt` is never verified and
//! is reached only indirectly through the print machinery inside `_print` (no
//! direct Call in `main`, no bundled obligation), so its panic edge folds into
//! the same whole-function panic-freedom aggregate as the tolerated `_print`
//! row. `function_format_args_all_foundational_display` detects the
//! non-foundational `T` at `main`'s `core::fmt::rt::Argument::new_display::<D>`
//! packer, and `print_gap_masks_fail_closed_dispatch` makes it a POSITIVE
//! fail-closed condition whenever there is a print gap (not merely a guard inside
//! the tolerate branch, which the cross-crate case never enters). This file MUST
//! stay red; its byte-identical local twin also refuses (cleanly, no ICE).
extern crate cross_crate_display_dep;
use cross_crate_display_dep::D;

fn main() {
    let v = std::hint::black_box(1i32);
    println!("{}", D(v));
}
