//@ needs-trust-verify
//@ aux-build:clean_origin_aux_private.rs
//@ compile-flags: -Z trust-verify=off

//! **I7 — the private-module negative (review defect 2's control).**
//!
//! The mint forces the planted DEF's visibility to `Public` — a parity
//! requirement so `crate::m::pick` and `Crate.m.pick` denote the same entity
//! everywhere in the OWNING crate — but it must not widen the enclosing
//! MODULE. This fixture pins that cross-crate privacy is unchanged: a private
//! `mod m` in the exporting crate refuses `clean_origin_aux_private::m::pick`
//! exactly as it refuses an ordinary private-module Rust item, BEFORE any MIR
//! is decoded — so the readmission chokepoint is never reached, and no
//! readmission diagnostic may appear here.
//!
//! PINNING RULE (from the I7 review): the annotation below pins E0603, the
//! diagnostic ordinary Rust produces for a path through a private module (and
//! the code the local parity work measured when the DEF itself was private).
//! If a real run produces a different diagnostic for this path, re-pin the
//! annotation to the measured one and record the change — the invariant under
//! test is only that the refusal is the SAME one ordinary Rust gets, not its
//! exact spelling. What must never appear is a successful resolution.

extern crate clean_origin_aux_private;

fn main() {
    let _ = clean_origin_aux_private::m::pick(1, 2);
    //~^ ERROR module `m` is private
}
