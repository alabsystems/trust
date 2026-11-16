//@ needs-trust-verify
//@ check-fail
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! **W5 (Lean-calls-Rust) — the WRONG-CARRIER refusal, with options.**
//! (`docs/design/2026-09-13-lean-calls-rust-lane.md`, Diagnostics.)
//!
//! `fn inc` takes `u32` and returns `u64`; the island applies it at `UInt64`.
//! The callee IS admitted (its signature is in the carrier vocabulary), so it
//! is declared in the Clean environment at `UInt32 → UInt64` — and the
//! island's `inc x` at `x : UInt64` is then a TYPE MISMATCH at the kernel,
//! not an unknown identifier. Nothing is coerced: the batch is rejected, the
//! Clean error is reported at the declaration (measured wording:
//! `Type mismatch: expected UInt32, got …`), and the note says which `fn`
//! takes what in which position, with the three ways forward. The `E0425`
//! at the call site follows with the batch-rejection note.
//!
//! What is NOT claimed: nothing about `inc` itself — the compiler asserted
//! only its type, and the kernel refused the application on that type.

fn inc(x: u32) -> u64 {
    u64::from(x) + 1
}

clean {
    def twice_inc (x : UInt64) : UInt64 := inc (inc x)
}
//~^^ ERROR Type mismatch
//~| NOTE `fn inc` takes `u32` in position 0 and returns `u64`
//~| NOTE restate the callee at the carrier `twice_inc` uses

fn main() {
    let _ = twice_inc(5);
    //~^ ERROR cannot find function `twice_inc` in this scope
}
