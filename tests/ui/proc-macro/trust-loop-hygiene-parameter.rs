//@ proc-macro: trust-prime-boundary.rs
//@ run-pass
//@ compile-flags: -Z trust-verify=off

extern crate trust_prime_boundary;

use trust_prime_boundary::emit_collapsed_native_contract;

// Every token in the function has the invocation's call-site span. The exact
// HIR identity of the macro-emitted scalar parameter `n` must nevertheless be
// admitted for both E4 (`invariant`) and E5 (`decreases`) elaboration.
emit_collapsed_native_contract!();

fn main() {
    collapsed_native_contract(1, 1);
}
