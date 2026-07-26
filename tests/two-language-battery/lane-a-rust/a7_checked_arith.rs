//@ battery-lane: A-rust
//@ battery-expect: pass
//@ battery-flags: -Ztrust-verify=on --crate-type=lib
//! LANE A (Rust, native clauses) — a small FIXED-POINT type, with the
//! saturating and rounding arithmetic that every such type needs.
//!
//! The type is `u32` milli-units: `1000` is one unit and `1_000_000` (1000.000)
//! is the largest representable magnitude. Rust has no way to say that in a
//! `struct`, so the range lives in the contract — which is the point. Field
//! projections are NOT usable here: exact native admission rejects an ordinary
//! field until signatures carry layouts
//! (`crates/trust-types/src/spec_render.rs:395-402`), so a real fixed-point
//! contract today is written over the scalar representation.
//!
//! What makes this file different from `a1_saturating_accumulator.rs`: a1's
//! obligations are all discharged FROM PRECONDITIONS. `sat_add`/`sat_sub` here
//! are TOTAL — they carry no `requires` at all, and their panic-freedom must
//! come from the branch above each operation, the shape
//! `tests/ui/trust/scalar_safety_good.rs:14-20` pins as `build-pass`. So this
//! file separates two proof routes that a1 conflates:
//!
//!   * path condition -> arithmetic safety  (`sat_add`, `sat_sub`)
//!   * precondition   -> arithmetic safety  (`round_units`)
//!
//! The second route is the one `tests/ui/trust/functional_contracts.rs:12-15`
//! records as historically weak ("the verifier does not yet thread a contract
//! precondition into the dependent integer arithmetic"), so if this file fails
//! it should fail on `round_units` alone — which is a more useful measurement
//! than a single green tick.

/// Saturating fixed-point add, capped at 1000.000.
///
/// Total: defined for every `u32` pair, so there is no `requires`. Every
/// arithmetic operation in the body is guarded by the branch above it —
/// `1000000 - a` only runs where `a < 1000000`, and `a + b` only where
/// `b < 1000000 - a`, which is exactly why `a + b` cannot overflow. That
/// guard is load-bearing: the naive `if a + b > 1000000` spelling wraps before
/// the comparison it is supposed to protect.
///
/// The second clause is the interesting half of the specification: saturation
/// must never LOSE ground for an in-range operand. It is also this battery's
/// only top-level `==>` in a signature clause — the spec implication that
/// routes the payload to the opaque verifier-language lane
/// (`compiler/rustc_parse/src/parser/generics.rs`, `trust_spec_payload_is_opaque`).
pub fn sat_add(a: u32, b: u32) -> u32
    ensures result <= 1000000
    ensures a <= 1000000 ==> result >= a
{
    if a >= 1000000 {
        1000000
    } else {
        let room = 1000000 - a;
        if b >= room { 1000000 } else { a + b }
    }
}

/// Saturating fixed-point subtract, floored at zero.
///
/// Also total. `a - b` runs only where `b < a`, so the unsigned subtraction
/// cannot wrap — the single most common fixed-point bug, stated as a contract
/// rather than as a comment. `result <= a` is the defining property of a
/// saturating subtract: it may lose precision at the floor, never gain
/// magnitude.
pub fn sat_sub(a: u32, b: u32) -> u32
    ensures result <= a
{
    if b >= a { 0 } else { a - b }
}

/// Round milli-units to the nearest whole unit.
///
/// This clause is non-trivial in the way rounding contracts usually are: the
/// naive reading of `(1_000_000 + 500) / 1000` is 1000.5 and therefore "1001,
/// out of range", and the true value is 1000 because the division truncates.
/// A verifier that models `/` as rational division refutes this; one that
/// models it as `bvudiv` proves it. That is the whole obligation.
///
/// Unlike the two above, panic-freedom here rests on the PRECONDITION rather
/// than on a branch: `x + 500` is in range only because `x <= 1_000_000`.
pub fn round_units(x: u32) -> u32
    requires x <= 1000000
    ensures result <= 1000
{
    (x + 500) / 1000
}
