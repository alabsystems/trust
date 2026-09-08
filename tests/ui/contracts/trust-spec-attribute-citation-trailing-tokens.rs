//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ proc-macro: trust.rs
//@ edition: 2021
//! Trust E9 — the attribute payload group is self-delimiting, so a citation is
//! the LAST thing in it. Tokens after the citation are authored text no
//! consumer would ever see; refuse them instead of discarding them.
//!
//! DIRECTIVE NOTE: `-Ztrust-verify=on` is LOAD-BEARING. In vanilla mode
//! (compiletest's default `-Ztrust-verify=off`) the resolver's spec-contract
//! hook does not fire, `trust::ensures` stays the stable-Rust PASSTHROUGH
//! proc macro, and the payload is never parsed as a contract at all — so this
//! case would compile clean and assert nothing.

#[trust::ensures(result <= x by self_le; junk)]
//~^ ERROR expected the end of the contract clause after its `by` citation
pub fn trailing(x: u64) -> u64 {
    x
}

fn main() {}
