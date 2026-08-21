//@ needs-trust-verify
//@ aux-build:clean_origin_aux.rs
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr

//! **I7 — the cross-crate Clean-origin call in CONST position: the
//! `mir_for_ctfe` chokepoint arm specifically.**
//!
//! The CTFE machine loads an `InstanceKind::Item` body via `tcx.mir_for_ctfe`
//! DIRECTLY — not via `instance_mir` (measured in the I7 plan and re-verified
//! by its review) — so a readmission guard on the extern `optimized_mir` arm
//! alone would miss exactly this lane. This fixture forces the extern
//! `mir_for_ctfe` decode arm to serve the imported body, which means its own
//! `trust_clean_extern_readmission` ensure ran first.
//!
//! Both MIR rows are encoded for a Clean-origin def and both decode surfaces
//! are guarded, so a `constness` drift that flips which table CTFE reads
//! cannot route around the gate (I7 risk R8).
//!
//! The runtime assert keeps the fixture value-asserted end to end: a CTFE
//! result baked into the binary is still a value a wrong body would corrupt.

extern crate clean_origin_aux;

const PICKED: u64 = clean_origin_aux::m::pick(6, 7);

fn main() {
    assert_eq!(
        PICKED, 6,
        "the CTFE-evaluated imported Clean-origin body must be the projection \
         the Clean `def` denotes (parameter 0)"
    );
}
