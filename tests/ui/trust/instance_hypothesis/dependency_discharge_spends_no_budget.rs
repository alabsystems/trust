//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: od2_dep_budget.rs
//@ compile-flags: -Ztrust-verify=on --crate-type=lib -Ztrust-bundle-foreign-crate=od2_dep_budget
//@ rustc-env:TRUST_REDERIVE_MAX_BODIES=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-fail
//! OD-1 PHASE 2 REVIEW FIX (2026-10-05): an instance discharge carries no credit,
//! so it must not spend the shared D4-A re-derivation budget a credit-bearing
//! check needs. With the budget lowered to ONE body, `a`'s discharge of
//! `f::<DA>` comes first.
//!
//! BEFORE (stage 1 of `20eace3baa`): the discharge re-derived `DA::m` (a `proved`
//! row, no credit), which spent the one slot; `z`'s C-FLOW case split then declined
//! ("exceeds this compilation's re-derivation budget") and `z` FAILED strict on its
//! kept `dyn` row — a credit `main` (`8364c5a6af`) grants. AFTER: the discharge
//! reads `unknown` (nothing re-derived `DA::m` for credit yet) and charges nothing;
//! `z` verifies.

extern crate od2_dep_budget as dep;

pub fn a() -> u32 {
    //~^ ERROR Trust instance discharge not established for `dependency_discharge_spends_no_budget::a`: 1 instance(s)
    //~| NOTE resolves to `<od2_dep_budget::DA as od2_dep_budget::Tr>::m` [unknown]
    //~| ERROR Trust strict verification failed
    dep::f(&dep::DA)
}

// ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
//~vv ERROR Trust strict verification failed for `dependency_discharge_spends_no_budget::z`
//~v NOTE this function has no obligation of its own
pub fn z(v: u32) -> u32 {
    let s: &dyn dep::Shape = &dep::Sq(v);
    s.area()
}
