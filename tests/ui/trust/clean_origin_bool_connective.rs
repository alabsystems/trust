//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **CLEAN BOOLEAN CONNECTIVES RUN** (2026-09-13, W6 widening: Rust calls a
//! Clean `def` that is a boolean negation or connective over `Bool`
//! parameters).
//!
//! A Rust `main` calls kernel-checked Clean `def`s of the form
//! `def f (a b : Bool) : Bool := a && b` (and `not b`, `a || b`), through the
//! minted `DefId`s. Their kernel terms are `Bool.not b`, `and a b`, `or a b`
//! (the last two def-eq to `Bool.and`/`Bool.or`, measured 2026-09-13). The
//! emitted MIR is a one-block `_0 = UnaryOp(Not, p)` / `_0 = <BitAnd|BitOr>(l,
//! r)`, reflected through the authored `admit_bool_value_function` and verified
//! def-eq against the island term before anything links.
//!
//! The truth-table assertions distinguish the correct connective from every
//! plausible wrong one: `and(true, false)` must be `false` (an `or` would give
//! `true`), `or(false, false)` must be `false`, `neg(true)` must be `false` (an
//! identity would give `true`).
//!
//! `-Z trust-verify=off` is the point, not a convenience: the faithfulness gate
//! is a compilation-correctness check, deliberately NOT behind any verification
//! switch.

mod m {
    clean {
        def neg (b : Bool) : Bool := not b
        def conj (a : Bool) (b : Bool) : Bool := a && b
        def disj (a : Bool) (b : Bool) : Bool := a || b
    }
}

fn main() {
    // Negation: the full one-input truth table.
    assert_eq!(crate::m::neg(true), false, "not true == false");
    assert_eq!(crate::m::neg(false), true, "not false == true");

    // Conjunction: the full two-input truth table. `and(true,false)` is false
    // where an `||` mis-emission would give true.
    assert_eq!(crate::m::conj(true, true), true, "true && true");
    assert_eq!(crate::m::conj(true, false), false, "true && false");
    assert_eq!(crate::m::conj(false, true), false, "false && true");
    assert_eq!(crate::m::conj(false, false), false, "false && false");

    // Disjunction: the full two-input truth table. `or(false,false)` is false
    // where an `&&` mis-emission would agree but `or(true,false)` distinguishes.
    assert_eq!(crate::m::disj(true, true), true, "true || true");
    assert_eq!(crate::m::disj(true, false), true, "true || false");
    assert_eq!(crate::m::disj(false, true), true, "false || true");
    assert_eq!(crate::m::disj(false, false), false, "false || false");

    // A composed check exercising all three together.
    assert!(crate::m::conj(crate::m::disj(true, false), crate::m::neg(false)));
}
