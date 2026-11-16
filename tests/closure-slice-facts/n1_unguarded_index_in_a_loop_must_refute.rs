//@ slice-facts: refuses
//! THE NEGATIVE CONTROL FOR THE 2026-09-20 GATE, and the row that makes the
//! seven greens above readable as a fix rather than a laundering.
//!
//! Nothing here bounds `i` by `v.len()`, so `v[i]` really does panic — on
//! `v = []` at the first iteration, and on any `v` shorter than 8. rustc emits
//! its `BoundsCheck` assert for it exactly as it does for the `windows` rows,
//! and the suppression drops the rvalue-side twin here too. What must survive is
//! the ASSERT row, and it must be REFUTED: the whole distinction is that where
//! the access is genuinely unsafe the surviving row is a refutation with a
//! witness, and where it is safe-but-unproved the surviving row is
//! runtime-checked and reported.
//!
//! If this row ever goes green, the suppression has stopped leaving a refutable
//! obligation behind and the seven rows it turned green are false proofs.
pub fn f(v: &[u32]) -> u32 {
    let mut s = 0u32;
    let mut i = 0usize;
    while i < 8 {
        s = s.wrapping_add(v[i]);
        i += 1;
    }
    s
}
