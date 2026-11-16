//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off --crate-type=lib
//@ edition: 2021
// Divergence D2's root-fix (full-population frontier, wave-full-0831): a
// `-> !` fn whose body FALLS THROUGH seals `Unreachable`, never `Return`.
// Rust types such a fall-through only via divergence the producer did not
// model or a never-pattern absurdity; built MIR's own spelling is
// `unreachable`, the oracle proved that trap, and the producer's old `ret`
// RETURNED from a diverging fn — the measured divergence
// (rfc-0000-never_patterns/diverges.rs::ref_never_arg). `Unreachable` is
// the faithful emission: executing past an uninhabited-argument entry is
// UB by Rust's own rules.
#![feature(never_patterns)]
#![allow(incomplete_features)]

pub enum Void {}

// The measured divergent shape: a never-pattern argument, an empty body.
pub fn ref_never_arg(&!: &Void) -> ! {}

pub fn never_arg(!: Void) -> ! {}
