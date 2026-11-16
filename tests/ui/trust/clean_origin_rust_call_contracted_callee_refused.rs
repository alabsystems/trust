//@ needs-trust-verify
//@ check-fail
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! **W5 (Lean-calls-Rust) — a CONTRACTED callee is refused (soundness).**
//! (`docs/design/2026-09-13-lean-calls-rust-lane.md`, SOUNDNESS; the fix of
//! 2026-09-13.)
//!
//! `safe_div` carries a `requires x < 10` precondition, so it discharges its
//! own `DivisionByZero` obligation only CONDITIONALLY on that contract (the
//! precondition row is recorded "skipped; every caller must establish the
//! requires contract"). The plain-Rust call path charges that precondition at
//! the caller; a Clean `def` call site does NOT, so admitting `safe_div` as a
//! Clean callee would turn a conditional proof into an unconditional false
//! accept: `call_div(10)` would compile and then divide by zero at run time.
//!
//! CORRECTED 2026-09-25: this paragraph used to attribute the gap to "increment
//! 3's `trust_check_clean_rust_callees` charge is unbuilt". Increment 3's FACET
//! charge is now built (`trust_charge_clean_rust_callees`) — and it does not
//! close this hole and was never going to. It certifies a callee's
//! `Pure ∧ Total ∧ Deterministic ∧ NoPanic`; it does not establish a callee's
//! `requires` at the call site, and a contracted callee never reaches it because
//! the MINT SEAM refuses one first. This refusal is what closes the false
//! accept, and it stays load-bearing.
//!
//! The mint therefore refuses a `requires`/`ensures` callee at the AST
//! admissibility seam (`rustc_resolve::trust_clean_mint`): `safe_div` never
//! enters the Clean environment, the island's `safe_div x` fails to elaborate
//! with `Unknown identifier: safe_div`, and the v7/D3 note says WHY and what to
//! do. Nothing is minted, so the call site gets `E0425`. This refusal is
//! independent of the verification mode — it happens at resolve time — which is
//! why this test runs with `-Z trust-verify=off`.

fn safe_div(x: u64) -> u64 requires x < 10 {
    100 / (10 - x)
}

clean {
    def call_div (x : UInt64) : UInt64 := safe_div x
}
//~^^ ERROR Unknown identifier: safe_div
//~| NOTE precondition is not charged at the Clean call site

fn main() {
    let _ = safe_div(0);
    let _ = call_div(10);
    //~^ ERROR cannot find function `call_div` in this scope
}
