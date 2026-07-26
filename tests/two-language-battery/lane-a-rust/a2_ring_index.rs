//@ battery-lane: A-rust
//@ battery-expect: pass
//@ battery-flags: -Ztrust-verify=on --crate-type=lib
//! LANE A (Rust, native clauses) — ring-buffer index arithmetic.
//!
//! A real data-structure invariant: the advance of a circular index must stay
//! inside the buffer for every admissible input. This is the shape that makes
//! bounds checks provable rather than merely tested.

/// Advance a ring index, wrapping at `cap`.
pub fn advance(idx: u32, cap: u32) -> u32
    requires cap > 0
    requires idx < cap
    ensures result < cap
{
    if idx + 1 == cap { 0 } else { idx + 1 }
}

/// Distance from an index to the buffer end — never larger than the capacity.
pub fn headroom(idx: u32, cap: u32) -> u32
    requires cap > 0
    requires idx < cap
    ensures result <= cap
    ensures result > 0
{
    cap - idx
}
