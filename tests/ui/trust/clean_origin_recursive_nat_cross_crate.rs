//@ needs-trust-verify
//@ aux-build:clean_origin_recursive_nat_aux.rs
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr

//! C11 end-to-end: a structurally recursive Clean definition crosses rmeta as
//! an induction-proved, unbounded-exact bignum projection.
//!
//! This is deliberately cross-crate. A local run would test planning and MIR
//! emission but could miss either new v2 wire field. The imported call forces
//! digest decode, local carrier recomputation, re-admission, and the fresh
//! local MIR gate before the body is served. `2^64` is the anti-vacuity value:
//! no fixed-width carrier can return it unchanged.

extern crate clean_origin_recursive_nat_aux;
extern crate trust_bignum;

fn main() {
    let small = trust_bignum::Nat::from_u64(7);
    assert_eq!(clean_origin_recursive_nat_aux::m::keep_rec(small).to_u64(), Some(7));

    let text = "18446744073709551616";
    let big = trust_bignum::Nat::from_decimal(text).expect("2^64 parses");
    let result = clean_origin_recursive_nat_aux::m::keep_rec(big);
    assert_eq!(result.to_u64(), None, "the carrier must remain genuinely unbounded");
    assert_eq!(result.to_decimal(), text, "the induction-proved projection must preserve 2^64");
}
