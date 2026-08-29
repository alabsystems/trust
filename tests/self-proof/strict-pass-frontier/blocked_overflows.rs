#![no_std]
//! THE MUTATION CONTROL for `blocked.rs` — same body, guards widened until the
//! add GENUINELY overflows. This must FAIL, and it is the only thing standing
//! between #222's canonical-spelling fix and a false PROVE.
//!
//! `blocked.rs` differs from this file in exactly one constant: `1_000_000` here
//! becomes `2_000_000_000`. Under those guards `a + b` can reach `4e9`, which is
//! outside `i32`. z3 4.x reports the violation SAT with `a = 147483648,
//! b = 2000000000`, a model that satisfies EVERY guard — so the refutation is
//! reachable and correct, not an artifact of an unreachable counterexample.
//!
//! WHY A SEPARATE FIXTURE. #222 changed the hardened `Overflow(*)` twin to emit
//! its violation as the canonical disjunction `r < min ∨ r > max` instead of the
//! hand-rolled `Not(min <= r && r <= max)`. Those are the same proposition, so
//! the change must be invisible to the mathematics and visible only to the
//! kernel recognizer. `blocked.rs` proves the PROVE direction moved. Only this
//! file proves the REFUTE direction did not: a re-spelling that made a
//! satisfiable violation certify would ship exactly the false verify the whole
//! change is supposed to avoid, and `blocked.rs` passing cannot detect it.
//!
//! Its unit-level twin is
//! `crates/trust-certify/tests/hardened_overflow_twin_certification.rs`'s
//! `a_genuinely_overflowing_twin_certifies_nothing_before_or_after_de_morgan`,
//! which asserts the same thing about the certifier alone. This file asserts it
//! about the shipping, authenticated `targo trust check` lane.
//!
//! IF THIS FILE EVER PASSES, the compiler is claiming a proof about a program
//! that really can overflow. Do not adjust the expectation; revert the change.
pub fn add_guarded(a: i32, b: i32) -> i32 {
    if a > 2_000_000_000 { return 0; }
    if a < -2_000_000_000 { return 0; }
    if b > 2_000_000_000 { return 0; }
    if b < -2_000_000_000 { return 0; }
    a + b
}
