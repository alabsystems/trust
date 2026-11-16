//@ needs-trust-verify
//@ aux-build: dropglue_bomb_dep.rs
//@ compile-flags: -Ztrust-verify=on -Copt-level=0
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! Hidden-drop-routing pin (2026-09-14). `std::mem::drop(b)` runs `b`'s drop glue
//! INSIDE `core::mem::drop` (a Call), NOT via a `Drop` TERMINATOR in `main` — so
//! the `drop_ty_has_masked_fail_closed_glue` terminator scan misses it, and a
//! dependency `Bomb` whose `Drop::drop` panics (or performs UB), dropped this way
//! beside a `println!`, was ACCEPTED and aborted at runtime. The no-`println!`
//! twin is already refused (the drop-glue row is then the representative).
//!
//! `function_has_masked_fail_closed_dispatch` now also flags a Call to
//! `core::mem::drop::<T>` / `core::ptr::drop_in_place::<T>` (authenticated core)
//! whose value type `T` — read from the call's generic args — has non-foundational
//! drop glue, reusing `drop_ty_has_masked_fail_closed_glue(T)`. `Bomb`'s `Drop` is
//! in a non-authentic crate, so this refuses. `std::mem::drop` of a foundational
//! value (`String`, `i32`) still tolerates. This file MUST stay red.
extern crate dropglue_bomb_dep;
use dropglue_bomb_dep::Bomb;

fn main() {
    let b = Bomb(std::hint::black_box(7));
    std::mem::drop(b);
    println!("survived");
}
