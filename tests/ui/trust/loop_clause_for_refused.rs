//@ dont-check-compiler-stderr
//! Trust: `for` loops have no first-class clause position, and the refusal
//! must SAY SO rather than emitting vanilla rustc's "expected `{`, found
//! `invariant`" with its `{ invariant } acc <= 100` block-recovery suggestion.
//!
//! Why `for` is refused rather than supported is a measurement, not an
//! omission: a `for` is entered through the `IntoIterator::into_iter` call, so
//! its loop header is never reached by a straight-line path and vcgen has no
//! exact initiation model for it. On a build that wired the `for` clause
//! position through end to end, every `for` clause produced its obligations
//! and every one came back UNKNOWN. See
//! `Parser::reject_trust_for_loop_contract`.
//!
//! This test is the tripwire for that decision: if someone gives `for` a
//! clause position again, they must delete this file deliberately and replace
//! it with obligation-level evidence that the clauses now discharge.

pub fn for_invariant_is_refused(v: &[u8]) -> u32 {
    let mut acc = 0u32;
    for _x in v invariant acc == 0 {
        //~^ ERROR `for` loops have no first-class clause position
        acc = 0;
    }
    acc
}

pub fn for_decreases_is_refused(v: &[u8]) -> u32 {
    let mut acc = 0u32;
    for _x in v decreases acc {
        //~^ ERROR `for` loops have no first-class clause position
        acc = 0;
    }
    acc
}

fn main() {}
