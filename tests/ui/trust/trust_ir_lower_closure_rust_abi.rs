//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-CAB): a CLOSURE def-kind is positive evidence of the Rust ABI.
//!
//! `Node::fn_sig()` has no closure arm, so the HIR route the declaration half
//! uses cannot answer for a closure and returns `None` — which the ABI test
//! then read as "not Rust", declaring an ordinary Rust closure C-ABI. That is
//! #190 one def-kind over: absence of evidence for Rust is not evidence of C.
//!
//! Decided from the DEF-KIND rather than a query, for the reason the `Ctor` arm
//! beside it gives: Rust has no syntax for a non-Rust-ABI closure, so there is
//! nothing to look up. This makes the DECLARATION half agree with the
//! DEFINITION half, which already answers `true` for every sig-less def-kind.

pub struct P(pub u32);

pub fn by_value_struct_closure(p: &P) -> u32 {
    let f = |q: &P| P(q.0 + 1);
    f(p).0
}

fn main() {
    assert_eq!(by_value_struct_closure(&P(4)), 5);
}
