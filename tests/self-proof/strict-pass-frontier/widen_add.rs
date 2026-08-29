#![no_std]
//! THE OTHER SIDE OF THE `blocked.rs` BOUNDARY — the fixture that refutes
//! "the hardened twin blocks any crate that adds two integers".
//!
//! This crate ADDS TWO INTEGERS and PASSES the authenticated strict lane with
//! the hardened `Overflow(Add)` twin PROVED. Measured 2026-08-27,
//! `targo trust check` at stage1 `31ccf1b56`:
//!
//!   exit 0, `Gate: PASS [strict lane, exit 0]`
//!   `Coverage: 1/1 eligible function bodies verified (complete)`
//!   `Summary: 2 proved, 0 failed, 0 runtime-checked, 0 assumed, 0 unknown (2 total)`
//!   `proved by kind: arithmetic_overflow_add=1, hardened_panic_boundary=1`
//!   `additionally proved=2 (certified=2, smt-backed=0)`
//!
//! NON-VACUITY: the two proved rows are the arithmetic-overflow obligation and
//! its `hardened_panic_boundary mir_assert::Overflow(Add)` twin — the exact
//! twin that stays UNKNOWN in `blocked.rs`. Neither is `VcKind::Unreachable`
//! (formula `Bool(true)`); both carry
//! `CONSTRUCTIVE (certified; validation=kernel-rechecked)`.
//!
//! WHY THIS ONE AND NOT `blocked.rs`. Both twins carry the SAME violation core
//! shape `Not(And([Le(lo, sum), Le(sum, hi)]))` — the De Morgan dual of the
//! `Or([Lt(sum, lo), Gt(sum, hi)])` the per-statement lane emits. The
//! certifier's guarded-arithmetic refutation
//! (`certify_disjunctive_contradiction`) scans the conjunct pool for
//! `Formula::Or`, so the dual never reaches it. Here a DIFFERENT recognizer
//! fires — the operand bounds come from the `as u16` casts (`_3 <= 255`,
//! `_4 <= 255`), which the closed cast-range path can refute directly. In
//! `blocked.rs` the bounds come from dominating `if` guards and no other
//! recognizer covers them, so that twin declines.
//!
//! So the boundary is a certifier-COVERAGE boundary keyed on the shape of the
//! violation, not "the hardened profile cannot discharge arithmetic". Measured
//! on the same authenticated lane the same day: `Overflow(Shl)` under a
//! `s >= 32` guard PASSES, a guarded `BoundsCheck` PASSES, `DivisionByZero`
//! PASSES (`pass.rs`), and `Overflow(Add|Sub|Mul)` on direct integer
//! parameters under `if` guards does not.
pub fn add_u8(a: u8, b: u8) -> u16 {
    (a as u16) + (b as u16)
}
