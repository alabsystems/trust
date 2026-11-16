//@ revisions: ctor minted
//@ aux-build:ctor_dep.rs
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[ctor] forbid-output:UnmodeledThreadSpawnEffect
//! Spawn census (P2m cost 5): a dependency's tuple-variant constructor has no
//! MIR in its metadata, so reifying it (`Shape::Square as fn(u32) -> Shape`)
//! made it MIR-less Rust whose signature can carry a callable out: an UNKNOWN
//! sink, which unclosed every pool, so `plain` (a `format!`) was UNKNOWN too.
//! A constructor only builds its value from its arguments; it runs and mints
//! nothing, so `ctor` has no row. `minted` keeps the refusal it was mistaken
//! for: a MIR-less function that returns a fn pointer may return one it
//! minted, so its caller and every formatting function stay UNKNOWN.

#![allow(dead_code)]

extern crate ctor_dep;

use ctor_dep::Shape;

#[cfg(ctor)]
pub fn pick(square: bool) -> fn(u32) -> Shape {
    if square { Shape::Square as fn(u32) -> Shape } else { Shape::Circle }
}

#[cfg(minted)]
pub fn pick() -> fn() { ctor_dep::make_callback() } //[minted]~ NOTE not enumerated (no spawn was found)

pub fn plain(n: u32) -> String { format!("{n}") } //[minted]~ NOTE not enumerated (no spawn was found)
