//@ proc-macro: trust-prime-boundary.rs
//@ compile-flags: -Z trust-verify=off
//@ check-fail
//! Proc macros may collapse every emitted token to one call-site span. Two
//! stateful Clean islands then have no trustworthy authored order and must be
//! rejected instead of being sequenced by HIR/DefId accident.

extern crate trust_prime_boundary;

use trust_prime_boundary::emit_collapsed_clean_islands;

emit_collapsed_clean_islands!();
//~^ ERROR Clean island source order is ambiguous because island spans are equal or overlap

fn main() {}
