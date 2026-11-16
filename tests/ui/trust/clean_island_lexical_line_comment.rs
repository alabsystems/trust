//@ compile-flags: -Z trust-verify=off
//@ check-pass
//! A Lean line comment containing `}` does not end the island. The island
//! body is scanned as Clean text to its matching `}`, so a Rust token tree
//! is no longer the island's boundary (G2). This fixture used to pin the
//! opposite — `unexpected closing delimiter` — as a fail-closed limit.

clean {
    theorem before : 0 = 0 := rfl
    -- }
    theorem after : 0 = 0 := rfl
}

fn main() {}
