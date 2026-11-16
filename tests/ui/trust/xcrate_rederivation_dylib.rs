//@ needs-trust-verify
//@ needs-dynamic-linking
//@ aux-build:xcrate_fmt_dep.rs
//@ aux-build:xcrate_fmt_dep_dylib.rs
//@ revisions: rlib_declared dylib_declared
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[rlib_declared] compile-flags: -Ztrust-bundle-foreign-crate=xcfmt_dep
//@[dylib_declared] compile-flags: -Ztrust-bundle-foreign-crate=xcfmt_dylib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[rlib_declared] check-pass
//@[dylib_declared] check-fail
//! D4 increment A (2026-09-24) — a DYNAMIC-LIBRARY dependency is never in the
//! declared bundling scope (`foreign_rederivation::declared_scope_membership`,
//! `ScopeMiss::DynamicLinkage`).
//!
//! `dylib_declared` MUST STAY REFUSED. Fix the compiler, never this file.
//!
//! Re-derivation trusts that a dependency's encoded MIR is the body its linked
//! code came from (the P-MIR premise, `docs/TCB.md`). A statically linked rlib
//! is fixed into the artifact at link time; a dylib is loaded at RUN time, from
//! whatever file sits at its path then, so the body this compilation checked
//! need not be the body that runs. (A `cdylib` cannot be a Rust dependency at
//! all — it carries no metadata a consumer can link against — so `dylib` and
//! `sdylib` are the only dynamic shapes that arise.)
//!
//! * `rlib_declared` — the control: the same `Good` body from the rlib
//!   `xcfmt_dep`, declared, is re-derived and credited.
//! * `dylib_declared` — `Good` from the dylib `xcfmt_dylib`, declared and with
//!   encoded MIR: declined, and the NOTE names the dynamic linkage.
//!
//! Measured BEFORE (stage-1 snapshot at `4e9fe36bf`, current main without this
//! change, compiletest-equivalent harness): both revisions refused with "a value
//! is formatted through a user `Display`/`Debug` implementation whose
//! panic-freedom was not established" — no foreign impl was ever re-derived.
extern crate xcfmt_dep;
extern crate xcfmt_dylib;

#[cfg(rlib_declared)]
pub fn f() {
    println!("{:?}", xcfmt_dep::Good);
}

#[cfg(dylib_declared)]
pub fn f() {
    //[dylib_declared]~^ ERROR a value is formatted through a user
    //[dylib_declared]~| NOTE was not re-derived in this compilation: it is in a declared crate whose code reaches the program through a dynamic library
    println!("{:?}", xcfmt_dylib::Good);
}
