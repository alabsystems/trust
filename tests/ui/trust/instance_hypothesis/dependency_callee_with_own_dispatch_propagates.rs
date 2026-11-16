//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: od2_dep_fold.rs
//@ compile-flags: -Ztrust-verify=on --crate-type=lib -Ztrust-bundle-foreign-crate=od2_dep_fold
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-fail
//! OD-1 PHASE 2 REVIEW FIX (2026-10-05): `run::<Q>`'s site resolves to the
//! DEPENDENCY default body `<Q as Fold>::wrap`, which dispatches on `Self` itself
//! (the `ty` `ExprFold::fold_box` shape: 100 of the 102 `failed` rows measured on
//! `tla-model-normalizer`).
//!
//! BEFORE (stage 1 of `20eace3baa`): the row read `[failed]` with a reason naming
//! `skip`/`assume_total`/a clause/a cycle — as if `wrap` had been refuted, when it
//! is only proved RELATIVE to its own site. AFTER: the row is `unknown` and says so,
//! and `wrap`'s own site is discharged at `Q` (the ruling's "propagate"): it resolves
//! to the local `Q::leaf`, proved here, so that propagated row is
//! `assumed (instance discharge)` and the summary counts 4 rows, not 3.

extern crate od2_dep_fold as dep;

pub struct Q;

impl dep::Fold for Q {
    fn leaf(&self, x: u32) -> u32 {
        x
    }
}

pub fn use_it() -> u32 {
    //~^ ERROR Trust instance discharge not established for `dependency_callee_with_own_dispatch_propagates::use_it`: 1 instance(s)
    //~| NOTE resolves to `<dependency_callee_with_own_dispatch_propagates::Q as od2_dep_fold::Fold>::wrap` [unknown]
    //~| NOTE 1 runtime-checked, 1 assumed (instance discharge), 1 skipped out of 4 obligation(s)
    //~| ERROR Trust strict verification failed
    dep::run(&Q)
}
