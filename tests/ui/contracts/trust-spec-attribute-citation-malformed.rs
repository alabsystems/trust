//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ proc-macro: trust.rs
//@ edition: 2021
//! Trust E9 — a malformed `by` citation on the attribute surface FAILS CLOSED.
//!
//! A citation the parser cannot read must be an authored error, never a
//! silently discarded suffix: a dropped citation leaves a contract that reads
//! as kernel-checked while nothing checked it. Each case below is claimed by
//! the one citation grammar shared with the first-class signature surface, so
//! both spellings reject exactly the same authored mistakes.
//!
//! DIRECTIVE NOTE: `-Ztrust-verify=on` is LOAD-BEARING. In vanilla mode
//! (compiletest's default `-Ztrust-verify=off`) the resolver's spec-contract
//! hook does not fire, `trust::ensures` stays the stable-Rust PASSTHROUGH
//! proc macro, and the payload is never parsed as a contract at all — so this
//! case would compile clean and assert nothing.

// A reserved word cannot name a theorem.
#[trust::ensures(result <= x by fn)]
//~^ ERROR expected a theorem name after `by` in the contract clause citation
pub fn reserved_name(x: u64) -> u64 {
    x
}

fn main() {}
