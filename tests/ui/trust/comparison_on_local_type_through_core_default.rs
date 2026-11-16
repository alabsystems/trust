//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[default] check-pass
//@[certify] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A comparison on a LOCAL type that runs through core's default or forwarding body
//! (`Ord::max`, `PartialOrd::lt`, `&A: PartialEq<&B>`) was declined by the std
//! trait-identity filter, which exists to protect the bridge's typed gates for
//! primitives; no typed gate decides a user type, so each call became a fatal absent
//! callee (sweep m14, m14b, m16, p15, p23). The twin
//! `comparison_on_local_type_through_core_default_refused.rs` keeps panicking
//! hand-written comparisons refused.
//!
//! What this buys, measured on stage 1 (2026-09-30): `is_upgrade` and `order` PROVE;
//! `max_prio`, `same_kind` and `different` now reach core's body with the
//! resolved-call carrier, whose whole-function row trust-mc leaves undecided, so they
//! build under the default policy with a runtime-checked advisory and certify refuses
//! them. Before, all five were refused outright by a fatal absent-callee row.
use std::cmp::Ordering;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Priority {
    Low,
    High,
}

pub fn max_prio(a: Priority, b: Priority) -> Priority { //[certify]~ ERROR verification
    a.max(b)
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Version {
    pub major: u16,
    pub minor: u16,
}

pub fn is_upgrade(from: &Version, to: &Version) -> bool {
    to > from
}

pub struct Token {
    pub kind: u8,
    pub pos: u32,
}

impl PartialEq for Token {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

pub fn same_kind(a: &Token, b: &Token) -> bool { //[certify]~ ERROR verification
    a == b
}

pub fn different(a: &Token, b: &Token) -> bool { //[certify]~ ERROR verification
    a != b
}

pub fn order(a: &Version, b: &Version) -> Ordering {
    a.cmp(b)
}
