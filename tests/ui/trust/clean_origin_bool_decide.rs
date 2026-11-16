//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **A CLEAN COMPARISON RETURNED AS `Bool` RUNS** (2026-09-13, W6 widening:
//! Rust calls a Clean `def` whose body is a comparison of two parameters
//! returned as `Bool`).
//!
//! A Rust `main` calls kernel-checked Clean `def`s of the form
//! `def f (a b : UInt{N}) : Bool := a <cmp> b`, through the minted `DefId`s.
//! Their kernel bodies are `decide (a < b)` (`<`/`<=`) and `BEq.beq {C} … a b`
//! (`==`), measured 2026-09-13. The emitted MIR is a one-block
//! `_0 = <cmp>(l, r); return`, and the faithfulness gate verifies the emitted
//! body's reflection (`Decidable.decide <prop> <inst>`, minted by the FROZEN
//! `admit_comparison_function`) against the island's own term BEFORE anything
//! links.
//!
//! Every value asserted distinguishes the correct comparison from a plausible
//! wrong emission, so a green run pins the polarity and the operand order and
//! not merely that a call linked:
//!
//! * `lt(2, 1)` must be `false` and `lt(1, 2)` `true` — a swapped operator
//!   (`<=`) would make `lt(2, 2)` true, and swapped operands would flip both;
//! * `gt`/`ge` are expressed by OPERAND ORDER (`b < a`, `b <= a`), the way `>`
//!   desugars — `gt(2, 1)` is `true`;
//! * `eq` distinguishes equal from unequal, and `le` distinguishes `<` from
//!   `==` at the boundary (`le(2, 2)` is `true`, `lt(2, 2)` is `false`);
//! * the extremes `0` and `u64::MAX` exercise the full carrier.
//!
//! `!=` and a literal operand (`a < 10 : Bool`) are deliberately NOT here: they
//! are measured residuals (`!=` is `Bool.not (BEq.beq …)`, and a literal
//! comparison's Decidable instance is Nat-reduced, not the carrier instance the
//! frozen producer mints) — see `CleanOriginShape::DecideComparison`.
//!
//! `-Z trust-verify=off` is the point, not a convenience: the faithfulness gate
//! is a compilation-correctness check, deliberately NOT behind any verification
//! switch, and this fixture would be worthless if the flag could disable the
//! machinery it measures.

mod m {
    clean {
        def lt (a : UInt64) (b : UInt64) : Bool := a < b
        def le (a : UInt64) (b : UInt64) : Bool := a <= b
        def eqf (a : UInt64) (b : UInt64) : Bool := a == b
        def gt (a : UInt64) (b : UInt64) : Bool := b < a
        def ge (a : UInt64) (b : UInt64) : Bool := b <= a
    }
}

fn main() {
    // `<`: strictly less. lt(2,1) MUST be false — a swapped operator or swapped
    // operands would make it true.
    assert!(crate::m::lt(1, 2), "1 < 2");
    assert!(!crate::m::lt(2, 1), "NOT 2 < 1");
    assert!(!crate::m::lt(2, 2), "NOT 2 < 2 (strict)");
    assert!(crate::m::lt(0, u64::MAX), "0 < u64::MAX");
    assert!(!crate::m::lt(u64::MAX, 0), "NOT u64::MAX < 0");

    // `<=`: `le(2,2)` is true where `lt(2,2)` is false — pins `<` vs `<=`.
    assert!(crate::m::le(2, 2), "2 <= 2");
    assert!(crate::m::le(1, 2), "1 <= 2");
    assert!(!crate::m::le(2, 1), "NOT 2 <= 1");
    assert!(crate::m::le(u64::MAX, u64::MAX), "MAX <= MAX");

    // `==`: equal vs unequal.
    assert!(crate::m::eqf(5, 5), "5 == 5");
    assert!(!crate::m::eqf(5, 6), "NOT 5 == 6");
    assert!(crate::m::eqf(0, 0), "0 == 0");
    assert!(crate::m::eqf(u64::MAX, u64::MAX), "MAX == MAX");
    assert!(!crate::m::eqf(0, u64::MAX), "NOT 0 == MAX");

    // `>` and `>=` via operand order (b < a, b <= a).
    assert!(crate::m::gt(2, 1), "2 > 1");
    assert!(!crate::m::gt(1, 2), "NOT 1 > 2");
    assert!(!crate::m::gt(2, 2), "NOT 2 > 2 (strict)");
    assert!(crate::m::ge(2, 2), "2 >= 2");
    assert!(crate::m::ge(2, 1), "2 >= 1");
    assert!(!crate::m::ge(1, 2), "NOT 1 >= 2");
}
