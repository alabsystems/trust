//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
//! Trust (wave-CHG): a switch CASE must not hoist past an earlier FALLTHROUGH arm.
//!
//! Cases dispatch at the `Inst::Switch` BEFORE the fallthrough chain runs, whatever the
//! source order, so a literal arm written AFTER a range or guarded arm would steal the
//! values they claim. Measured live before the guard, at HEAD:
//!
//! ```text
//! match x { 0..=5 => 10, 2 => 20, _ => 30 }
//! clean=true, and: DIVERGENCE on input [2]: THIR returned 20, MIR oracle returned 10
//! ```
//!
//! Rust answers 10 at `x == 2` — the source-earlier range wins. The sampled oracle
//! misses the theft whenever the stolen literal is unsampled (a literal of 3 read
//! `equal=true` on the same shape), and the guarded variant is invisible to BOTH
//! oracles while counting clean — which is why the repair is a GUARD, not a sample,
//! and why this file is the instrument: the pinned corpus contains no
//! case-after-fall-arm shape at all, so a regression here would read as nothing.
//!
//! The R-cases must refuse; the A-cases pin that the guard is not a blanket ban on
//! mixing arm classes — a case BEFORE the fall arms dispatches first in both source
//! and switch order, which is exactly when the hoist is not a theft.

#![allow(dead_code)]
#![allow(unreachable_patterns)]

// R1 — the measured wrong-value shape: a literal inside an earlier range.
pub fn range_steal(x: u32) -> u32 {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    match x {
        0..=5 => 10,
        2 => 20,
        _ => 30,
    }
}

// R2 — the oracle-invisible shape: a literal after a guarded arm. The guard may pass at
// runtime, so a guarded catch-all claims EVERY literal.
pub fn guard_steal(n: u32) -> u32 {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    match n {
        m if m < 2 => 10,
        1 => 20,
        _ => 30,
    }
}

// A1 — the case FIRST: source order and dispatch order agree, no theft.
pub fn case_then_range(x: u32) -> u32 {
    match x {
        2 => 20,
        0..=5 => 10,
        _ => 30,
    }
}

// A2 — a case OUTSIDE the earlier range's interval: nothing to steal, so the wave-CHG
// guard deliberately does NOT fire, the body lowers clean, and the value differential
// AGREES on every sample (measured: `equal=true, samples=5, mode=Agreed`).
//
// It still errors under `strict`, and the error is worth pinning for what it says: the
// derived MIR dispatches the hoisted case first (`switch(x)[7 -> ..]`) while built MIR
// tests the range first (`Le(0, x)` chain) — value-equal, structurally divergent, so the
// second channel reports a DerivedMismatch and the flip gate refuses the body. That is
// the honest posture for a semantically-safe reordering the structural comparator cannot
// bless: clean for coverage, never flipped. Widening the guard to refuse this shape
// would trade a true `Agreed` for a refusal — the wrong direction.
pub fn disjoint_case(x: u32) -> u32 {
    //~^ ERROR -Ztrust-ir-lower=strict: MIR re-derived from the THIR-derived trust-ir DISAGREES
    match x {
        0..=5 => 10,
        7 => 20,
        _ => 30,
    }
}
