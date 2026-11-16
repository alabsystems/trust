//! WS5.14 (F-095, stale-text half): the recorded reason for a `Nat` recursion
//! SKIP must name the blocker it is actually blocked on.
//!
//! Three declarations at the same `Nat` carrier, all three refused by the same
//! runtime-less signature walk, differing only in SHAPE:
//!   * `tozero`       — structural recursion   (gets the SHAPE NOTE)
//!   * `countdownSum` — well-founded recursion (gets the SHAPE NOTE)
//!   * `natId`        — projection             (the negative twin: plain text)

mod m {
    clean {
        def tozero : Nat -> Nat
          | 0 => 0
          | n + 1 => tozero n

        def countdownSum (n : Nat) : Nat :=
          if h : 0 < n then n + countdownSum (n - 1) else 0
        termination_by n

        def natId (n : Nat) : Nat := n
    }
}

/// A Rust row, so the module is a real two-language crate rather than an
/// island-only artifact.
pub fn rust_half(x: u64) -> u64 {
    x
}
