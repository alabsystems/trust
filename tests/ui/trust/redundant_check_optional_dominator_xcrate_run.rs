//@ run-fail
//@ edition: 2021
//@ revisions: opt noopt advisory
//@ aux-build: redundant_check_optional_dominator_dep.rs
//@ compile-flags: -Coverflow-checks=off
//@[opt] compile-flags: -O -Ztrust-verify=off
//@[noopt] compile-flags: -Copt-level=0 -Ztrust-verify=off
//@[advisory] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[advisory] dont-check-compiler-stderr
//@ error-pattern: attempt to divide with overflow
//@ ignore-emscripten no processes
//! RBCE-OPTIONAL-DOMINATOR-1 across crates. The dependency (overflow checks ON, -O)
//! encodes `#[inline] f`: `x.neg()`, then `x / -1`. This crate (overflow checks OFF)
//! codegens its own copy of that MIR, so here the optional negate assert is erased.
//!
//! BEFORE (a pre-fix stage 1, `scratchpad/stage1-w22probe`, measured 2026-10-11; the
//! pass source there is byte-identical to `2bf0ad72e3`): every revision built rc=0 and
//! printed `0`, exit 0.
//! * `noopt` and `advisory`: this crate runs no `RedundantBoundsCheckElim` (-O0; a
//!   proof session runs the -O0 MIR pipeline), so the deletion is the dependency's,
//!   in the MIR it encoded. With the dependency built
//!   `-Zmir-enable-passes=-RedundantBoundsCheckElim`, `noopt` panics.
//! * `opt`: this crate inlines `f` and its own pass deletes the check again. Only with
//!   BOTH crates built `-Zmir-enable-passes=-RedundantBoundsCheckElim` does `opt` panic.
//! * `advisory`: the verify-on consumer's row for the call was a `runtime_checked`
//!   claim about a check that no longer existed.
//!
//! AFTER: neither crate's pass deletes the mandatory check; every revision panics
//! (exit 101). Measured 2026-10-11 under compiletest on the stage 1 of `integ/wave22`
//! `618d7bd287`. `advisory` also warns that `main`'s one `runtime_checked` row is not
//! proved, as it did before the fix; the annotation pins that row.

extern crate redundant_check_optional_dominator_dep as dep;

fn main() {
    //[advisory]~^ WARN Trust Level 0 safety verification incomplete
    let r = dep::f(std::hint::black_box(i32::MIN));
    // Reaching this line means the mandatory overflow check was deleted.
    println!("{r}");
}
