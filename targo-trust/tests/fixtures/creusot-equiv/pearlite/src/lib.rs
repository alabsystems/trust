//! Blob-equivalence INPUT side (pearlite original).
//!
//! These attributes are what an author migrating off Creusot starts from.
//! The attributes reach tippy as inert tool attributes (`register_tool`),
//! exactly like the lint's own ui tests: no creusot-contracts dependency is
//! declared, so no proc macro ever runs and nothing here can assert anything.
//!
//! This file contains NO goal text and NO native clause: the mapper proposes
//! the native clause (see ../proposed/), an independent author writes the
//! native clause by hand (see ../native/), and goals are rendered only by the
//! compiler's spec-emit artifact on those two packages.
#![feature(register_tool)]
#![register_tool(creusot_contracts)]

// Supported subset: a machine comparison between immutable by-value params.
#[creusot_contracts::ensures(x >= x)]
pub fn observe(x: u64) -> u64 {
    x
}

// Supported subset: `old(lo)` on an immutable by-value machine parameter —
// the entry and exit values provably coincide (the compiler's own by-value
// prime-collapse class), so the mapper may collapse `old(lo)` to `lo`.
#[creusot_contracts::ensures(old(lo) <= lo)]
pub fn keep(lo: u64) -> u64 {
    lo
}
