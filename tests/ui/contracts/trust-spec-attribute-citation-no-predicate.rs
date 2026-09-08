//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ proc-macro: trust.rs
//@ edition: 2021
//! Trust E9 — a citation with nothing to cite. `#[trust::ensures(by T)]` has
//! no predicate for the theorem to prove, so it is an authored error rather
//! than an empty clause that would trivially "hold".
//!
//! DIRECTIVE NOTE: `-Ztrust-verify=on` is LOAD-BEARING. In vanilla mode
//! (compiletest's default `-Ztrust-verify=off`) the resolver's spec-contract
//! hook does not fire, `trust::ensures` stays the stable-Rust PASSTHROUGH
//! proc macro, and the payload is never parsed as a contract at all — so this
//! case would compile clean and assert nothing.

#[trust::ensures(by self_le)]
//~^ ERROR expected a predicate expression after the contract clause keyword
pub fn no_predicate(x: u64) -> u64 {
    x
}

fn main() {}
