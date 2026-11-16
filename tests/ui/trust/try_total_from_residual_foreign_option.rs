//@ revisions: default certify memsafe
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: try_total_from_residual_foreign_option_dep.rs
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[memsafe] compile-flags: -Ztrust-policy=memory-safe
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! `FromResidual::from_residual` into an `Option` is total only for core's own impl
//! (TRY-TOTAL-ANCHOR-1).
//!
//! `trust_try_total_marker` marked every `from_residual` whose TARGET is a std
//! `Option` total (`Some(StdCarrier::Option) => true`) without looking at the
//! residual type. The orphan rule lets a crate implement core's real
//! `FromResidual<Res> for Option<T>` for a residual type `Res` of its own, and the
//! dependency's impl panics. `d` calls it directly.
//!
//! BEFORE (stage 1 of main + wave 7, `scratchpad/stage1-w14`, each revision's own
//! flags plus `--cfg <revision> --emit=metadata`, measured 2026-10-05): `d` reads
//! `no_obligations | trivially panic-free` and has no diagnostic in any of the three
//! revisions. The program panics (`..._run.rs`).
//!
//! AFTER (predicted): the marker also requires the RESIDUAL to be the same std
//! carrier as the target. Orphan and overlap rules forbid any `FromResidual<Option<_>>`
//! impl for `Option` but core's, so that pins core's `None => None` body; a foreign
//! residual is left unmarked. `d` then keeps its absent-callee may-panic row. The
//! annotations on `d` are what the BEFORE compiler prints for `d_ctl`, a call to a
//! plain dependency function with the same body, line for line.

#![feature(try_trait_v2)]

extern crate try_total_from_residual_foreign_option_dep as dep;

use std::ops::FromResidual;

pub fn d() -> Option<u32> {
    //[default,certify]~^ ERROR Trust strict verification failed for `try_total_from_residual_foreign_option::d`: 1 obligation(s) were not fully verified
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete for `try_total_from_residual_foreign_option::d`: 1 obligation(s) were not proved
    //[memsafe]~^^^ ERROR Trust memory-safe verification failed for `try_total_from_residual_foreign_option::d`: at least one result is not an authenticated memory-safe assumption
    <Option<u32> as FromResidual<dep::Res>>::from_residual(dep::Res)
}

pub fn d_ctl() -> Option<u32> {
    //[default,certify]~^ ERROR Trust strict verification failed for `try_total_from_residual_foreign_option::d_ctl`: 1 obligation(s) were not fully verified
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete for `try_total_from_residual_foreign_option::d_ctl`: 1 obligation(s) were not proved
    //[memsafe]~^^^ ERROR Trust memory-safe verification failed for `try_total_from_residual_foreign_option::d_ctl`: at least one result is not an authenticated memory-safe assumption
    dep::boom_option()
}
