//@ needs-trust-verify
//@ aux-build: dropglue_bomb_dep.rs
//@ compile-flags: -Ztrust-verify=on -Copt-level=0 --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! Masked-DROP-GLUE fold pin (2026-09-14). The default policy tolerates the std
//! stdout/stderr print backend absent-callee row. The bridge folds every
//! absent/foreign panic source of a function into ONE whole-function
//! panic-freedom row named after a single representative callee; when a
//! `println!` is present that representative is `std::io::stdio::_print`, so a
//! co-folded dependency DROP-glue panic (`Bomb::drop`, which `panic!`s, in a
//! verify-off dep) was silently classified as the benign print gap — compile
//! exit 0 while the program panics at runtime.
//!
//! `function_has_masked_fail_closed_dispatch` /
//! `drop_ty_has_masked_fail_closed_glue` re-derive the masked drop glue from MIR:
//! `Bomb`'s `Drop::drop` DefId's crate is `dropglue_bomb_dep`, not std/core/alloc,
//! so its panic-freedom is unproven and the function MUST stay fatal. Its
//! no-`println!` twin is already fatal (the drop glue is then the row's own
//! representative). CONTROL that this is not over-refusal: a bare `String`
//! (foundational alloc `Drop`) beside a `println!` still compiles. This file MUST
//! stay red.
extern crate dropglue_bomb_dep;
use dropglue_bomb_dep::Bomb;

pub fn run(x: i32) {
    // A verified function whose only static incompleteness would be the std print
    // backend — EXCEPT it also drops a dependency `Bomb` whose `Drop` may panic.
    println!("runtime value = {}", x);
    let _b = Bomb(x);
}
