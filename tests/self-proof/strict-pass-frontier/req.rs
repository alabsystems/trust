#![no_std]
#![expect(incomplete_features)]
#![feature(contracts)]
//! CONTROLLED EXPERIMENT — one variable against `pass.rs`.
//!
//! Body is BYTE-IDENTICAL to `pass.rs`, which is measured at
//! `Gate: PASS [strict lane, exit 0]`, `2 proved, 0 unknown (2 total)`.
//! The single change is one added `#[requires(..)]` clause.
//!
//! The precondition is TRUE of every use: it constrains the caller to a
//! divisor the function already handles, and the body's own `d == 0` guard
//! makes it total regardless — so the clause never has to be leaned on for
//! panic-freedom. It is a domain statement, exactly like the six clauses in
//! `crates/trust-semantics/src/lib.rs`.
//!
//! QUESTION: does adding a true precondition to a crate that PASSES the
//! strict lane keep it passing?
use core::contracts::requires;

#[requires(d <= 1_000_000)]
pub fn udiv_guarded(n: u32, d: u32) -> u32 {
    if d == 0 {
        return 0;
    }
    n / d
}
