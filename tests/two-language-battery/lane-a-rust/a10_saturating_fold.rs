//@ battery-lane: A-rust
//@ battery-expect: pass
//@ battery-flags: -Ztrust-verify=on --crate-type=lib
//! LANE A (Rust, native clauses) — accumulation without an overflow obligation.
//!
//! This program exists because of a real defect the battery caught in its own
//! first run. The original version accumulated with `acc += xs[i] as u32`
//! under the invariant `i <= xs.len()`, and the verifier refused it:
//!
//!     must hold: the `Add` result must fit in its integer type
//!     fix: use `checked_*`/`saturating_*`/`try_into`
//!
//! The verifier was right and the program was wrong — nothing in that
//! invariant bounds `acc`, so the addition genuinely can overflow for a long
//! enough slice. The honest fix is not a stronger claim about a program that
//! can overflow; it is a program that cannot. `saturating_add` discharges the
//! obligation by construction, which is exactly the guidance the diagnostic
//! gave.
//!
//! Kept as a battery entry because "the tool told me my loop was wrong and it
//! was" is the single most useful thing a verifier can do.

/// Fold a byte slice into a saturating total.
pub fn saturating_fold(xs: &[u8]) -> u32 {
    let mut acc = 0u32;
    let mut i = 0usize;
    while i < xs.len()
        invariant i <= xs.len()
        decreases xs.len() - i
    {
        acc = acc.saturating_add(xs[i] as u32);
        i += 1;
    }
    acc
}
