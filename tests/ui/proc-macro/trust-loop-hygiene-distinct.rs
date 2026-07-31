//@ proc-macro: trust-prime-boundary.rs
//@ check-fail
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr

extern crate trust_prime_boundary;

use trust_prime_boundary::emit_distinct_native_collision;

// Rust can distinguish the call-site parameter from the mixed-site local, but
// both render as `bound` in a native clause. Until verifier terms carry syntax
// contexts, that same-spelled binding set must fail closed as ambiguous.
emit_distinct_native_collision!();
//~^ ERROR invalid `invariant` clause: source-contract variable `bound` is not in scope

fn main() {}
