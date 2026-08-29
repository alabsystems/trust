//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **R2/C9 — SELECT-VS-LITERAL RUNS.**
//!
//! A Rust `main` calls a kernel-checked Clean `if a < 10 then a else b`
//! through the minted `DefId`: the literal comparison operand exercises the
//! C9 ladder end-to-end — the new `admit_select_literal_function` route on
//! side B, the recognizer's literal-operand arm, the planner's ite arm with
//! a numeral in comparison position, and the diamond emitter with a
//! `const_from_scalar` operand in the entry comparison.
//!
//! The boundary asserts are the load-bearing ones: 9 (below), 10 (AT the
//! literal — the comparison is strict `<`, so the else arm), and 11 (above).
//! An off-by-one in the emitted comparison — `<=` for `<`, or a drifted
//! literal — flips exactly the `10` case.

mod m {
    clean {
        def clamp10 (a : UInt64) (b : UInt64) : UInt64 := if a < 10 then a else b
    }
}

fn main() {
    let below = crate::m::clamp10(9, 77);
    println!("{below}");
    assert_eq!(below, 9, "below the literal: the then arm returns a");
    assert_eq!(crate::m::clamp10(10, 77), 77, "AT the literal: strict < takes the else arm");
    assert_eq!(crate::m::clamp10(11, 77), 77, "above the literal: the else arm");
    assert_eq!(crate::m::clamp10(0, u64::MAX), 0, "the extremes select correctly");
}
