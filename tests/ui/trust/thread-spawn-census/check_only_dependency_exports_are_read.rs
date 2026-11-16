//@ revisions: exported_fn exported_static
//@[exported_fn] aux-build:check_only_fn_dep.rs
//@[exported_static] aux-build:check_only_static_dep.rs
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Spawn census: foreign code may call what a dependency links under a name of
//! its own (`exported_fn`) or read what such a static holds (`exported_static`). The census
//! read a dependency's exports from its encoded export list, which a crate
//! compiled without codegen leaves EMPTY, and `targo trust check` compiles
//! every library dependency that way: both were invisible, so `run`, which
//! calls C, was QUIET. An empty list is now read past: every non-generic
//! function and static of the dependency is a candidate, kept by its own
//! attributes. Both auxiliary crates are compiled `--emit=metadata`.

#![allow(dead_code)]

#[cfg(exported_fn)]
extern crate check_only_fn_dep;
#[cfg(exported_static)]
extern crate check_only_static_dep;

unsafe extern "C" {
    safe fn trust_census_run();
}

pub fn run() { //~ NOTE may spawn (indirect)
    trust_census_run()
}
