//@ battery-lane: A-rust
//@ battery-expect: pass
//@ battery-flags: -Ztrust-verify=on --crate-type=lib
//! LANE A (Rust, native clauses, solver authority) — a real accumulator.
//!
//! Every clause here is a FIRST-CLASS SIGNATURE CLAUSE, not an attribute:
//! the ratified two-language surface (§3.1). No Lean is involved; the
//! obligations belong to the arithmetic no-overflow class that native proof
//! authority covers (see docs/TCB.md for what that verdict means).
//!
//! The preconditions are what make the postconditions provable in declared
//! width: `add_bounded` excludes the single wrap point exactly as
//! `s1c_arith_true_ensures_proves` does, so the QF_BV query is
//! UNSAT-to-violate rather than accidentally true over unbounded Int.

/// Add one bounded step to a running total.
pub fn add_bounded(total: u64, step: u64) -> u64
    requires total <= 1000000
    requires step <= 1000
    ensures result >= total
    ensures result == total + step
{
    total + step
}

/// Advance a counter that must never reach its saturation point.
pub fn tick(counter: u32) -> u32
    requires counter < 4294967295
    ensures result == counter + 1
    ensures result > counter
{
    counter + 1
}

/// Halve a value — the classic shift contract, at a width where the shift
/// amount is statically in range (the class the shift-range obligation guards).
pub fn halve(x: u64) -> u64
    requires x <= 1000000
    ensures result <= x
{
    x >> 1
}
