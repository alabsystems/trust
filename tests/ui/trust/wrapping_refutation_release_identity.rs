//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -O
//@ check-pass
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ normalize-stderr: "\n\n$" -> "\n"
//! Release-mode identity pin for exact core wrapping calls outside the narrow
//! E6 import lane. Signed and pointer-sized add/sub remain available to the
//! full assertion-refutation model, while u128 remains a precise total
//! TrustIR operation even though the <=64-bit refutation model declines it.
//! If MIR inlining erases any of these authenticated call identities before
//! Trust verification, they become ordinary overflow-obligated arithmetic and
//! this strict `-O` fixture fails.

#![crate_type = "lib"]

pub fn signed_literal_roundtrip(x: i32) {
    assert!(x.wrapping_add(1).wrapping_sub(1) == x);
}

pub fn usize_roundtrip(x: usize, n: usize) {
    assert!(x.wrapping_add(n).wrapping_sub(n) == x);
}

pub fn u128_wrapping_is_total(x: u128, y: u128) -> u128 {
    x.wrapping_add(y)
}
