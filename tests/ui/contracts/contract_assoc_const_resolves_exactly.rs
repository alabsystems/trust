//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ proc-macro: trust.rs
//@ edition: 2021
//! Trust D3 (associated-constant half). A contract clause that names a
//! user-defined associated constant must denote THE constant the program uses.
//!
//! Two-language design §1: requires/ensures are pretty notation for the LITERAL
//! program objects. Before this fixture's fix, `Variable::MAX_ID` was refused —
//! only `u32::MIN`/`u32::MAX`-shaped paths were recognised — and the documented
//! workaround was to write the literal `2_147_483_647` beside a
//! `const _: () = assert!(Variable::MAX_ID == 2_147_483_647)` stand-in guard.
//! That is a re-declared twin: two numbers that must be kept in sync by hand,
//! and a contract that is a statement about the toolchain rather than the code.
//!
//! The value here is NOT pattern-matched from the spelling. `MAX_ID` is
//! `u32::MAX >> 1` — a const EXPRESSION — so the clause can only lower by
//! asking rustc's own const evaluator for the value of the resolved `DefId`,
//! which is the same evaluation the program itself gets.
//!
//! WHAT THIS ASSERTS IS THE OBLIGATION, NOT COMPILATION. `ok` asserts exactly
//! the bound the precondition states, so it discharges only if the const
//! resolved to exactly 2147483647. `off_by_one` asserts a bound ONE TIGHTER
//! than the precondition; it must stay REFUTED (counterexample
//! id = 2147483647), which is what rules out the const having been
//! over-approximated or replaced by a convenient nearby number.
//!
//! MEASURED before the fix (sealed toolchain trust-e26541e3): `ok` reported
//! `0 proved, 1 failed, 2 unknown, 1 runtime-checked out of 4` — the clause did
//! not lower, so it was not assumed and the body's assert was REFUTED. The
//! literal twin reported `0 proved, 0 failed, 1 unknown, 1 runtime-checked out
//! of 2`. After the fix the associated-constant spelling reports exactly what
//! the literal spelling reports.
//!
//! `main`'s PINS RE-MEASURED 2026-09-16. It carried two WARN annotations —
//! `Trust Level 0 safety verification incomplete` and `Trust verification
//! advisory` — recording that the harness body itself had an unproved row. It
//! does not any more: `main` now reports `1 proved, 0 failed, 0 unknown, 0 timed
//! out, 0 runtime-checked out of 1 obligation(s)` and emits no warning at all.
//!
//! The pins are REPLACED by that line rather than deleted. `main` exists here
//! only to instantiate the functions above, so a silent `main` is indistinguishable
//! from a `main` that was never verified; pinning the count keeps the harness
//! itself measured. Every ERROR this file is actually about is unchanged and
//! still covered by `dont-require-annotations: ERROR`.

#![allow(dead_code)]

pub struct Variable(u32);

impl Variable {
    // A const EXPRESSION, not a literal: nothing here can be recognised by
    // spelling, only by evaluation.
    pub const MAX_ID: u32 = u32::MAX >> 1;
}

// The precondition is assumed, so the identical bound discharges.
#[trust::requires(id <= Variable::MAX_ID)]
pub fn ok(id: u32) -> u32 {
    assert!(id <= 2147483647);
    id
}

// EXACTNESS GUARD. One tighter than the precondition -> must NOT discharge.
#[trust::requires(id <= Variable::MAX_ID)]
pub fn off_by_one(id: u32) -> u32 {
    assert!(id <= 2147483646);
    id
}

fn main() { //~ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    let _ = ok(3);
    let _ = off_by_one(3);
}
