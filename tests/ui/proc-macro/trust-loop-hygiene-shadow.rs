//@ proc-macro: trust-prime-boundary.rs
//@ check-fail
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr

extern crate trust_prime_boundary;

use trust_prime_boundary::emit_collapsed_native_shadow;

// The expansion-emitted local is a genuine lexical shadow of the scalar
// parameter. It must remain an unsupported shadow instead of reviving the
// hidden parameter as proof-authoritative verifier state.
emit_collapsed_native_shadow!();
//~^ ERROR invalid `invariant` clause: source-contract variable `bound` is not in scope

fn main() {}
