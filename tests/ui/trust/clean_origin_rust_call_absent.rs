//@ needs-trust-verify
//@ check-fail
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! **W5 (Lean-calls-Rust) — the ABSENT-CALLEE refusal, with options.**
//! (`docs/design/2026-09-13-lean-calls-rust-lane.md`, Diagnostics.)
//!
//! No `fn inc` is a sibling of the island: the Clean environment holds no
//! `inc`, the batch is rejected with the elaborator's own
//! `Unknown identifier: inc` (the pre-increment spelling, unchanged), and
//! the note now says WHY and what to do — define a sibling `fn` at a carrier
//! type, or declare it in Clean. A `fn inc` in ANOTHER module (`elsewhere`,
//! below) is deliberately not a sibling of this island under increment 1's
//! visibility rule, and the note names the module it looked in.
//!
//! What is NOT claimed: nothing is minted, nothing is emitted; the `E0425`
//! at the call site carries the batch-rejection note.

mod elsewhere {
    pub fn inc(x: u64) -> u64 {
        x.wrapping_add(1)
    }
}

clean {
    def twice_inc (x : UInt64) : UInt64 := inc (inc x)
}
//~^^ ERROR Unknown identifier: inc
//~| NOTE `inc` is not a Rust `fn` next to this island
//~| NOTE define `fn inc(..)` in the same module as the island

fn main() {
    let _ = elsewhere::inc(1);
    let _ = twice_inc(5);
    //~^ ERROR cannot find function `twice_inc` in this scope
}
