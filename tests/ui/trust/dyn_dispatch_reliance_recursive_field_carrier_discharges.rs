//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! The COST GUARD on the field walk: a RECURSIVE type in the bundle must not
//! take the whole bundle's C-FLOW discharge down with it.
//!
//! Walking an ADT's fields recurses through `List { next: Option<Box<List>> }`
//! forever. The naive repairs both fail here, which is why this file exists:
//!
//! * no cycle guard at all — the walk spins until fuel runs out, and fuel
//!   exhaustion sets `opaque`, which is a BUNDLE-WIDE refusal of C-FLOW for
//!   every trait. `local.emit(1)` below would stop discharging even though
//!   nothing about it is unknown;
//! * "raise the fuel" — a bigger budget, still exhausted, same refusal.
//!
//! The walk therefore carries a VISITED SET keyed by the full interned type, and
//! a repeat is SKIPPED rather than reported opaque. That is sound for a reason
//! the bug this file guards did not have: the identical `Ty` is already being
//! walked into the SAME carrier set, so no principal is lost. Fuel remains, and
//! remains fail-closed, for the case a visited set cannot bound at all —
//! polymorphic recursion, whose reachable type set is infinite.
//!
//! `Pair` is not decoration: it reaches `List` through a SECOND path, so the
//! visited set has to be a set and not a parent-chain check.
#![no_std]
#![allow(dead_code)]
extern crate alloc;

use alloc::boxed::Box;

pub trait Emit {
    fn emit(&mut self, n: u32) -> u32;
}

pub struct Good;

impl Emit for Good {
    fn emit(&mut self, n: u32) -> u32 {
        n.wrapping_add(1)
    }
}

pub struct List {
    pub next: Option<Box<List>>,
    pub v: u32,
}

pub struct Pair {
    pub a: Option<Box<Pair>>,
    pub b: Option<Box<List>>,
}

pub fn drive(_l: &List, _p: &Pair) -> u32 {
    let mut g = Good;
    let local: &mut dyn Emit = &mut g;
    local.emit(1)
}
