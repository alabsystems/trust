//@ compile-flags: -Z trust-verify=off
//@ check-pass
//! Lean block comments nest, and a `}` inside one does not end the island.
//! The island body is scanned as Clean text to its matching `}`, so a Rust
//! token tree is no longer the island's boundary (G2). This fixture used to
//! pin the opposite — `unexpected closing delimiter` — as a fail-closed limit.

clean {
    theorem before : 0 = 0 := rfl
    /- outer /- nested } -/ outer -/
    theorem after : 0 = 0 := rfl
}

fn main() {}
