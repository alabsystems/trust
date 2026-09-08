//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ check-pass
//! Trust (E5 CONSERVATION), the half that keeps the rule from being vacuous.
//!
//! `trust_attr_namespace_conservation.rs` proves an unclaimed `trust::` name is
//! refused. On its own that is satisfied by a check that refuses EVERYTHING, which
//! would be a far worse defect than the silent acceptance it replaces. This fixture
//! pins the other side: names the compiler really does consume still compile.
//!
//! The names here are the claimed ones that produce no diagnostic of their own in a
//! benign position, so an unexpected diagnostic in this file can only have come
//! from the namespace rule. The remaining claimed names are covered by the
//! `every_claimed_name_classifies_as_claimed` and
//! `the_last_segment_alias_spellings_are_claimed` unit tests in
//! `trust_types::trust_attr_namespace`, which pin the whole table of twenty-four
//! together with the consumer that reads each one — including the six
//! `attr.path().last()` alias spellings (`contracts_requires`, `contracts_ensures`,
//! `trust_requires`, `trust_ensures`, `trust_invariant`, `trust_decreases`) that an
//! exact-path enumeration misses and that a naive vocabulary would have rejected
//! while they were producing real obligations.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

#![feature(register_tool)]
#![register_tool(trust)]

#[trust::backing]
pub struct Buf {
    pub ptr: u32,
    pub len: usize,
}

#[trust::paired]
pub struct Pair {
    pub v: u32,
}

pub struct Machine {
    #[trust::var(name = "state", kind = "Int")]
    pub state: u64,
}

impl Machine {
    #[trust::action(name = "Step")]
    pub fn step(&mut self) {}
}

fn main() {}
