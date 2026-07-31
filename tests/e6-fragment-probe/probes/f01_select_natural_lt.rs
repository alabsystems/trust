//@ probe-shape: Select
//@ probe-expect: discharged
//@ probe-note: THE GOAL, REACHED 2026-07-26. The island is written the way a person
//@ probe-note: writes it and the clause discharges with NOTHING else: no helper
//@ probe-note: definition, no `cond`, no `Bool.rec`, no theorem, no citation.
//@ probe-note:
//@ probe-note: This probe spent its life as the headline gap. The mint used to emit
//@ probe-note: `Bool.rec` over `Nat.ble`-of-`toNat`, and the natural spelling
//@ probe-note: elaborates to `ite`/`Decidable.casesOn`. Both are STUCK on a neutral
//@ probe-note: scrutinee — but at different recursors of different inductives, so they
//@ probe-note: compared structurally and never unified. An iota mismatch, not an
//@ probe-note: unfolding one: no amount of reducibility could ever have bridged it.
//@ probe-note: The fix was for the compiler to mint what Clean's own `elab_if` already
//@ probe-note: produces. See docs/design/2026-07-25-select-encoding-ergonomics.md.
//@ probe-note:
//@ probe-note: The soundness condition attached to that change lives in `d11` and in
//@ probe-note: `machine_comparison_agrees_with_unsigned_nat_order_at_every_width`:
//@ probe-note: the discharge is now a tautology ABOUT `instLTUInt64`, so a theorem
//@ probe-note: pins that `<` means unsigned Nat order on the toNat images.
clean { def min2_isl (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b }
pub fn min2(a: u64, b: u64) -> u64
    ensures result == min2_isl(a, b)
{ if a < b { a } else { b } }
