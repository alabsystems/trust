//@ needs-trust-verify
//@ aux-build:xcrate_shape_dep.rs
//@ revisions: sq sq_two undeclared boom both root_param
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[sq] compile-flags: -Ztrust-bundle-foreign-crate=xcshape_dep
//@[sq_two] compile-flags: -Ztrust-bundle-foreign-crate=xcshape_dep
//@[boom] compile-flags: -Ztrust-bundle-foreign-crate=xcshape_dep
//@[both] compile-flags: -Ztrust-bundle-foreign-crate=xcshape_dep
//@[root_param] compile-flags: -Ztrust-bundle-foreign-crate=xcshape_dep
//@ dont-check-compiler-stderr
//@[undeclared] dont-require-annotations: ERROR
//@[boom] dont-require-annotations: ERROR
//@[both] dont-require-annotations: ERROR
//@[root_param] dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[sq] check-fail
//@[sq_two] check-fail
//@[undeclared] check-fail
//@[boom] check-fail
//@[both] check-fail
//@[root_param] check-fail
//! D4 increment A (2026-09-24) — C-FLOW over a DEPENDENCY's trait and impls:
//! the `dyn` case split may use a dependency impl's verdict only when this
//! compilation RE-DERIVES it (`trust_verify/foreign_rederivation.rs`).
//!
//! EVERY `check-fail` REVISION MUST STAY REFUSED. Fix the compiler, never this
//! file.
//!
//! Measured BEFORE (stage-1 with wave 0, `a8c853de6f`): every revision refused;
//! for `sq`, `TRUST_DYN_RELIANCE_PROBE=1` printed "C-FLOW declined: target
//! `<xcshape_dep::Sq as xcshape_dep::Shape>::area` is not local to this crate".
//! A LOCAL copy of the `sq`/`sq_two` programs built rc=0 on the same compiler.
//! Re-measured on the stage-1 snapshot at `4e9fe36bf` (current main, without
//! D4-A) through a compiletest-equivalent harness: every revision refused with
//! "Trust strict verification failed" on the fail-closed dispatch row ("an
//! unproven panic-freedom obligation for a call to an absent callee"), which
//! each refusal below pins.
//!
//! * `sq` / `sq_two` — check-pass: every coercion to `dyn Shape` is in `f`, and
//!   every enumerated `Self` (`Sq`) is re-derived panic-free here.
//! * `undeclared` — the same program, crate not declared: nothing re-derived.
//! * `boom` — the only coerced `Self` panics. `both` — one of two coerced
//!   `Self` types panics; the case split needs EVERY member.
//! * `root_param` — `fn g(x: &dyn Shape)`: a `dyn`-bearing root parameter
//!   poisons the trait, so C-FLOW cannot enumerate, whatever the impls are.
//!   The foreign-trait closure argument (increment B) is not a `dyn` argument:
//!   a vtable can be minted in dependency bodies nobody walked.
extern crate xcshape_dep;
use xcshape_dep::Shape;

#[cfg(any(sq, undeclared))]
// ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
//[sq]~vv ERROR Trust strict verification failed for `xcrate_dyn_flow::f`
//[sq]~v NOTE this function has no obligation of its own
pub fn f() -> u32 {
    //[undeclared]~^ ERROR Trust strict verification failed
    //[undeclared]~| NOTE an unproven panic-freedom obligation for a call to an absent callee
    let s: &dyn Shape = &xcshape_dep::Sq(3);
    s.area()
}

#[cfg(sq_two)]
// ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
//[sq_two]~vv ERROR Trust strict verification failed for `xcrate_dyn_flow::f`
//[sq_two]~v NOTE this function has no obligation of its own
pub fn f() -> u32 {
    let b = std::hint::black_box(true);
    let s: &dyn Shape = if b { &xcshape_dep::Sq(3) } else { &xcshape_dep::Sq(4) };
    s.area()
}

#[cfg(boom)]
pub fn f() -> u32 {
    //[boom]~^ ERROR Trust strict verification failed
    //[boom]~| NOTE an unproven panic-freedom obligation for a call to an absent callee
    let s: &dyn Shape = &xcshape_dep::Boom;
    s.area()
}

#[cfg(both)]
pub fn f() -> u32 {
    //[both]~^ ERROR Trust strict verification failed
    //[both]~| NOTE an unproven panic-freedom obligation for a call to an absent callee
    let b = std::hint::black_box(true);
    let s: &dyn Shape = if b { &xcshape_dep::Sq(3) } else { &xcshape_dep::Boom };
    s.area()
}

#[cfg(root_param)]
pub fn g(x: &dyn Shape) -> u32 {
    //[root_param]~^ ERROR Trust strict verification failed
    //[root_param]~| NOTE an unproven panic-freedom obligation for a call to an absent callee
    x.area()
}
