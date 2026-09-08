//@ needs-trust-verify
//@ aux-build:cross_crate_value_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Ztrust-bundle-foreign-crate=trust_xcbundle_dep
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! **ARM 6 — a REFUTATION is an expected direction of this change, not a
//! regression. Pre-registered.**
//!
//! Modelling a foreign call's return value moves rows in BOTH directions, and
//! the second direction is the one a reader of the counts will misread. Before
//! the change `c` is havoc, so `c * 200` is refuted with a counterexample no
//! execution can produce, and `reclassify_havoc_only_refutations` demotes that
//! honestly to `unsupported_mir UnmodeledCalleeReturn` — an UNKNOWN. After the
//! change `c` is pinned by the callee's proved `ensures result <= 31`, and
//! `c * 200` on a `u8` genuinely overflows for every `c >= 2`. The row goes
//! from `unknown` to `failed`, and the `failed` count goes UP.
//!
//! That is the lane working. The obligation was always there; what changed is
//! that the compiler can now decide it, and the answer is no. A change that
//! only ever moved rows toward `proved` would be a change that could not refute
//! anything, which is the shape of a false PROVE rather than the absence of one.
//!
//! This arm exists so nobody has to reconstruct that argument from a count.
extern crate trust_xcbundle_dep;

pub fn scale() -> u8 {
    let c = trust_xcbundle_dep::clamp_index(3);
    c * 200
}
