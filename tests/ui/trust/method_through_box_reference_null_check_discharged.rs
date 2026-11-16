//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-pass
//@ dont-check-compiler-stderr
//! rust 1.99 inserts a `NullReferenceConstructed` UB check when `&**b` forms a
//! reference from a `Box`'s pointer (here, the autoref receiver of `b.is_leaf()`).
//! The extractor discharged only `NullPointerDereference` checks from Box or
//! reference provenance, so this one stayed undischarged and refused the caller
//! (sweep `m19b`). It is the same `!(addr == 0 & check)` condition and the same
//! non-null proof.
pub enum E {
    Leaf,
    Node(Box<E>),
}

impl E {
    pub fn is_leaf(&self) -> bool {
        matches!(self, E::Leaf)
    }
}

pub fn child_is_leaf(e: &E) -> bool {
    match e {
        E::Node(b) => b.is_leaf(),
        E::Leaf => false,
    }
}
