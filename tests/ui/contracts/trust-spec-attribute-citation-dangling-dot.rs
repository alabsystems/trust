//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ proc-macro: trust.rs
//@ edition: 2021
//! Trust E9 — a dotted citation path that stops at the dot is an authored
//! error on the attribute surface, exactly as it is on the signature surface.
//! The alternative — folding `by Clean.` back into the predicate — would leave
//! a contract that looks cited and is not.
//!
//! DIRECTIVE NOTE: `-Ztrust-verify=on` is LOAD-BEARING. In vanilla mode
//! (compiletest's default `-Ztrust-verify=off`) the resolver's spec-contract
//! hook does not fire, `trust::ensures` stays the stable-Rust PASSTHROUGH
//! proc macro, and the payload is never parsed as a contract at all — so this
//! case would compile clean and assert nothing.

#[trust::ensures(result <= x by Clean.)]
//~^ ERROR expected a name segment after `.` in the contract clause citation
pub fn dangling(x: u64) -> u64 {
    x
}

fn main() {}
