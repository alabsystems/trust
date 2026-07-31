//@ proc-macro: trust-prime-boundary.rs
//@ check-fail
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr

extern crate trust_prime_boundary;

use trust_prime_boundary::emit_distinct_native_parameters;

// Both parameters display as `bound`, but the second has a mixed-site syntax
// context. A text-keyed function proposition/monitor environment cannot choose
// one exact HIR identity, so the whole contract bundle must be rejected.
emit_distinct_native_parameters!();
//~^ ERROR parameters named `bound` have distinct hygienic identities

fn main() {}
