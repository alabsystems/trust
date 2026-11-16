//@ needs-trust-verify
//@ edition: 2021
//@ aux-build:xcrate_same_name_mid.rs
//@ aux-crate:xcsame=xcsame.rs
//@ revisions: same_name_transitive same_name_bound
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Ztrust-bundle-foreign-crate=xcsame
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[same_name_transitive] check-fail
//@[same_name_bound] check-pass
//! D4 increment A (2026-09-24) — the declared bundling scope is keyed on crate
//! IDENTITY, not the crate name (`foreign_rederivation::declared_scope_membership`).
//!
//! `same_name_transitive` MUST STAY REFUSED. Fix the compiler, never this file.
//!
//! Two different crates are both NAMED `xcsame` here: the one this compilation
//! BINDS with an exact `--extern xcsame=<path>` (`auxiliary/xcsame.rs`), and a
//! second one, with its own `-Cmetadata` and so its own `StableCrateId`, that
//! arrives only transitively through `xcsame_mid`
//! (`auxiliary/xcrate_same_name_inner.rs`). Their `Good` impls are
//! byte-identical. `-Ztrust-bundle-foreign-crate=xcsame` names the bound one.
//! Keyed on the name alone (as `native_bundle_crate_is_declared` was, and as the
//! parked D4-A draft left it), the transitive crate was in scope too: whatever
//! crate happens to carry the declared string gets its bodies bundled and
//! re-derived under a declaration that was never about it.
//!
//! * `same_name_transitive` — formats the TRANSITIVE crate's `Good` (reached
//!   through `xcsame_mid::make()`): declined, and the NOTE names why.
//! * `same_name_bound` — formats the BOUND crate's `Good`: re-derived and
//!   credited, with the same-named transitive crate loaded alongside. This is
//!   the control: without it, `same_name_transitive` could be refused for any
//!   reason at all.
//!
//! Measured BEFORE (stage-1 snapshot at `4e9fe36bf`, current main without this
//! change, compiletest-equivalent harness): both revisions refused with "a value
//! is formatted through a user `Display`/`Debug` implementation whose
//! panic-freedom was not established" — no foreign impl was ever re-derived.
extern crate xcsame_mid;

#[cfg(same_name_transitive)]
pub fn f() {
    //[same_name_transitive]~^ ERROR a value is formatted through a user
    //[same_name_transitive]~| NOTE was not re-derived in this compilation: it is in a crate whose NAME is declared (`-Ztrust-bundle-foreign-crate`) but which is not the crate this compilation binds under that name
    println!("{:?}", xcsame_mid::make());
}

#[cfg(same_name_bound)]
pub fn f() {
    println!("{:?}", xcsame::Good);
}
