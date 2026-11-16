//@ revisions: dep_off dep_advisory dep_strict
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: od2_dep_off.rs
//@ aux-build: od2_dep_advisory.rs
//@ aux-build: od2_dep_strict.rs
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@[dep_off] compile-flags: -Ztrust-bundle-foreign-crate=od2_dep_off
//@[dep_advisory] compile-flags: -Ztrust-bundle-foreign-crate=od2_dep_advisory
//@[dep_strict] compile-flags: -Ztrust-bundle-foreign-crate=od2_dep_strict
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-fail
//! OD-1 PHASE 2 (2026-10-05): the SAME generic in three dependencies compiled
//! `-Ztrust-verify=off`, `-Ztrust-policy=advisory` and `-Ztrust-policy=strict`.
//! This consumer's discharge rows must not depend on which: D4 rejected any
//! dependency verdict bit, and phase 2 re-derives the sites from the encoded MIR,
//! so no dependency setting, verdict or row is read. Every revision charges
//! `f::<Bad>` the same `failed` discharge (an error under this strict consumer),
//! and `g::<Good>` the same `assumed (instance discharge)` row through the
//! dependency's own still-generic call. A verify-on dependency's rows for `f` and
//! `g` (one `assumption:instance-hypothesis` each, its own) are never retired and
//! never consulted here.
//!
//! The interaction with ADVISORY-REQUIRES-CROSS-CRATE is
//! `dependency_generic_requires_keeps_check_run.rs`.

#[cfg(dep_off)]
extern crate od2_dep_off as dep;
#[cfg(dep_advisory)]
extern crate od2_dep_advisory as dep;
#[cfg(dep_strict)]
extern crate od2_dep_strict as dep;

pub struct Good;
pub struct Bad;

impl dep::Tr for Good {
    fn m(&self) -> u32 {
        1
    }
}

impl dep::Tr for Bad {
    fn m(&self) -> u32 {
        //~^ ERROR Trust Level 0 safety verification incomplete
        //~| ERROR Trust strict verification failed
        panic!("bad")
    }
}

pub fn use_bad() -> u32 {
    //~^ ERROR Trust instance discharge not established for `dependency_policy_is_not_read::use_bad`: 1 instance(s)
    //~| NOTE ; a site of a `od2_dep_
    //~| ERROR Trust strict verification failed
    dep::f(&Bad)
}

pub fn use_good() -> u32 {
    //~^ NOTE 1 runtime-checked, 1 assumed (instance discharge)
    //~| ERROR Trust strict verification failed
    dep::g(&Good)
}
