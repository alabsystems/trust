//@ battery-lane: C-combo
//@ battery-expect: pass
//@ battery-flags: -Ztrust-verify=on --crate-type=lib
//! LANE C (THE COMBO) — a readable island that still discharges.
//!
//! `c1_cited_min2.rs` shows what the citation lane costs today: to discharge
//! `min2(x, y) <= x` the author must state a theorem over
//! `Bool.rec (fun _ => UInt64) y x (Bool.not (Nat.ble (UInt64.toNat y)
//! (UInt64.toNat x)))` — the compiler's encoding of their own function body.
//! Nobody writing a ring buffer will produce that, and it breaks if the
//! encoding ever changes.
//!
//! This file is the same program with no citation and no theorem — but it is a
//! STOPGAP, not the shape to teach. Naming the comparison as a helper is still
//! boilerplate the author should never have to write.
//!
//! RULED 2026-07-25: the target is `if a < b then a else b` and nothing else.
//! When that lands, delete the helpers below and let this file use it directly.
//!
//! The remaining gap, measured and recorded: writing the island the *most*
//! natural way — `if a < b then a else b` — still fails, because Clean's `if`
//! over a Prop elaborates through `Decidable`/`ite`, which is definitionally
//! equal to nothing in the `Bool.rec` world the compiler mints into. See
//! `docs/design/2026-07-25-select-encoding-ergonomics.md` and probe `f01`.

clean {
    def min_isl (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
}

/// Ordinary Rust. The island above is its specification, and no proof is written.
pub fn min2(a: u64, b: u64) -> u64
    ensures result == min_isl(a, b)
{
    if a < b { a } else { b }
}
