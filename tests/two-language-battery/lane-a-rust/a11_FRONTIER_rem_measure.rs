//@ battery-lane: A-rust
//@ battery-expect: frontier
//@ battery-flags: -Ztrust-verify=on --crate-type=lib
//! LANE A FRONTIER — Euclid's algorithm: a TRUE termination claim the lane
//! cannot model yet.
//!
//! `gcd` terminates, and `decreases b` is the right measure: `a % b < b`
//! whenever `b > 0`. Nothing here is wrong. But the E5 recursion lane binds a
//! recursive call's measure argument only through the exact checked-subtraction
//! chain; `rustc` lowers `a % b` as a `Rvalue::BinaryOp(Rem, ..)` inside the
//! call block, and `block_has_unmodeled_recursion_arithmetic` refuses any
//! Add/Sub/Mul/Div/Rem/Shl/Shr on an int-width operand there. So
//! `recursion_measure_bindings` returns `None`, and with an explicit clause
//! present the lane emits `unsupported_recursion_decreases_vc` — an
//! UnsupportedMir row, preclassified UNKNOWN.
//!
//! This is scored `frontier`, NOT `reject`. The distinction is the whole point:
//! an UNKNOWN row means the tool could not model the program, and calling that
//! a successful rejection would let a capability gap impersonate a proof.
//!
//! DO NOT "fix" this by hoisting `let r = a % b;` before the call. The `Rem`
//! stays in the call block; and if a block split is forced, the argument
//! becomes a free variable with nothing binding it to `a % b`, which converts
//! an honest UNKNOWN into a FALSE FAILED termination row — strictly worse than
//! the gap it papers over.
//!
//! Closing this properly means giving `%` an exact machine lowering in the
//! recursion-measure lane. When that lands, this file flips to
//! `frontier-closed` on its own.

/// Euclid's algorithm. Terminates because `b` strictly decreases.
pub fn gcd(a: u32, b: u32) -> u32
    decreases b
{
    if b == 0 { a } else { gcd(b, a % b) }
}
