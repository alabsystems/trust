//! Total, verified ratio and clamp arithmetic for Trust's own scorecards.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0
//!
//! # Why this crate exists
//!
//! Trust's reports are full of hand-rolled ratio arithmetic, and the idiom in
//! use across the tree is a defect waiting to happen:
//!
//! ```text
//! recognized.len() * 100 / SHOULD_BE_TOTAL.len().max(1)   // trust-ir-bridge
//! (td - tr) * 100 / td.max(1)                             // trust-clean tests
//! 100.0 * std_ok as f64 / std_n.max(1) as f64             // trust-clean/src/prove.rs
//! idx.min(self.verify_steps.len().saturating_sub(1))      // trust-loop, e2e_loop
//! ```
//!
//! `.max(1)` does not make a zero-population ratio meaningful — it silently
//! substitutes a denominator nobody chose, so `0/0` reads as `0%` only by luck
//! and `n/0` would read as `n * 100`%. `idx.min(len.saturating_sub(1))` is not
//! a safe index either: on an empty container it yields `0`, which is out of
//! bounds. Both idioms are open-coded because the safe version is fiddly, and
//! being fiddly is exactly the thing a verifier is for.
//!
//! Every function here is **total** — defined on all inputs, with no panicking
//! path — and the compiler proves it. There are no dependencies, no `derive`,
//! no `impl Display`, no allocation and no trait objects, because each of those
//! is a measured blocker on the authenticated strict lane and this crate is
//! written to pass that lane rather than to be retrofitted onto it.
//!
//! # Two tiers, and the difference is stated per function
//!
//! **Tier 1 — proved bound.** The function carries a grammar `ensures` clause
//! that the compiler discharges. `clamp_upper`'s `result <= hi` is a *checked
//! proposition*: a caller may rely on it, and a body that broke it would not
//! compile.
//!
//! **Tier 2 — proved totality, bound by construction.** The function contains a
//! division, and a division in a body makes its `ensures` clause undischargeable
//! today (measured; see the module note below). These functions therefore carry
//! **no** contract, and their stated range is an ordinary code invariant that a
//! reviewer must check — exactly like any other Rust. What IS proved about them
//! is that they cannot panic: the zero-divisor and overflow obligations are
//! statically discharged, so no runtime check remains.
//!
//! The distinction is marked on every item. Do not read a tier-2 range comment
//! as a machine-checked claim.
//!
//! # The measured fragment boundary
//!
//! Recorded here because it is the reason the crate is shaped this way, and
//! because a later reader will otherwise "simplify" tier 2 into tier 1 and
//! discover it the hard way. All measured 2026-08-28 on the authenticated
//! `targo trust check` lane, stage1 `8d4210bcf`:
//!
//! * A grammar `ensures` discharges only if the body contains **no arithmetic
//!   operator**. Comparison, selection, `let` and widening `as` casts are fine.
//!   With `+ - * /` present, an extra `trust-exact-source-clause-discharge` row
//!   appears and returns UNKNOWN *even when every per-branch postcondition VC is
//!   PROVED*.
//! * The way around that is **composition**: put the arithmetic in an
//!   uncontracted callee and let the contract-carrying wrapper inherit the bound
//!   from `clamp_upper`'s postcondition. That is why `span_width`,
//!   `saturating_diff` and `capped_sum` are written as one call to a `raw_*`
//!   helper wrapped in `clamp_upper`, and it is not stylistic.
//! * Composition works for addition, subtraction, multiplication and casts, and
//!   **not for division**: a caller of a division-containing callee fails with
//!   *"native typed-TrustIr lowering did not complete, so the panic-freedom of
//!   an unmodeled construct could not be established"*. That single fact is
//!   what puts `percent`, `permille` and `scaled_ratio` in tier 2 — division is
//!   the one operator that cannot be hidden behind a helper.
//! * A **disjunctive** (`a || b`) or **conjunctive** (`a && b`) `ensures` is not
//!   discharged. That is why `clamp_index(idx, len)` does not exist: its honest
//!   contract is `len == 0 || result < len`, and it measures UNKNOWN. The
//!   supported spelling is `clamp_upper(idx, last_index(len))`.
//! * Both spellings of `requires` — the `#[requires]` attribute and the native
//!   grammar form — are recorded as `[ASSUMED] assumption:requires ...
//!   unsupported MIR FullVerification::Precondition`, and an assumed row fails
//!   the strict gate. So no function here has a precondition; totality is not a
//!   convenience, it is the only shape that passes.
//!
//! # The zero-denominator convention
//!
//! `den == 0` returns `0`. That is a choice, and it is stated rather than left
//! to the reader: an empty population has no ratio. Callers that must
//! distinguish "0% of 100" from "no population at all" have to test `den`
//! themselves — this crate will not invent a denominator.

#![no_std]

// ---------------------------------------------------------------------------
// Tier 1 — proved bound. Every `ensures` below is discharged by the compiler.
// ---------------------------------------------------------------------------

/// `v`, clamped from above by `hi`.
///
/// **Tier 1.** `ensures result <= hi` is checked.
///
/// This is the crate's load-bearing primitive, not a convenience wrapper over
/// `Ord::min`: it is the one function whose postcondition every other tier-1
/// bound is composed from.
pub fn clamp_upper(v: u32, hi: u32) -> u32 ensures result <= hi {
    if v > hi { hi } else { v }
}

/// `v`, clamped from below by `lo`.
///
/// **Tier 1.** `ensures result >= lo` is checked.
pub fn clamp_lower(v: u32, lo: u32) -> u32 ensures result >= lo {
    if v < lo { lo } else { v }
}

/// `v`, clamped into `[lo, hi]`, and `lo` when the window is inverted.
///
/// **Tier 1.** `ensures result >= lo` is checked.
///
/// The postcondition is deliberately one-sided. `core`'s `Ord::clamp` panics
/// when `lo > hi`; this function is total there and returns `lo`, so
/// `result <= hi` is *false* on an inverted window and stating it would be a
/// lie. The lower bound is the half that holds unconditionally, and it is the
/// half a caller sizing a buffer actually depends on.
pub fn clamp_range(v: u32, lo: u32, hi: u32) -> u32 ensures result >= lo {
    if v < lo {
        return lo;
    }
    if v > hi {
        if hi < lo {
            return lo;
        }
        return hi;
    }
    v
}

/// The width of the half-open interval `[lo, hi)`, or `0` when it is empty or
/// inverted.
///
/// **Tier 1.** `ensures result <= hi` is checked — the fact a caller indexing a
/// buffer of length `hi` needs — and the subtraction is proved not to underflow.
///
/// The two-call shape is required, not stylistic: see the fragment note in the
/// module docs.
pub fn span_width(lo: u32, hi: u32) -> u32 ensures result <= hi {
    clamp_upper(raw_span(lo, hi), hi)
}

/// `a - b`, saturating at `0`.
///
/// **Tier 1.** `ensures result <= a` is checked, and the subtraction is proved
/// not to underflow.
///
/// The bound is the non-trivial half: it is what lets a caller pass the result
/// straight into a length or an index computation derived from `a`.
pub fn saturating_diff(a: u32, b: u32) -> u32 ensures result <= a {
    clamp_upper(raw_diff(a, b), a)
}

/// `a + b`, saturating at `u32::MAX` and then capped at `cap`.
///
/// **Tier 1.** `ensures result <= cap` is checked, and the addition is proved
/// not to overflow.
pub fn capped_sum(a: u32, b: u32, cap: u32) -> u32 ensures result <= cap {
    clamp_upper(raw_sum(a, b), cap)
}

// ---------------------------------------------------------------------------
// Tier 2 — proved totality; the stated range is a code invariant, NOT a checked
// proposition. Each of these contains a division. See the module docs.
// ---------------------------------------------------------------------------

/// The last valid index of a container holding `len` elements, or `0` when it
/// is empty.
///
/// **Tier 2 by contract shape, not by division.** The honest postcondition is
/// `len == 0 || result < len`, and a disjunctive `ensures` is not discharged
/// today, so this function carries none. What is proved is that the `len - 1`
/// cannot underflow — the exact failure the open-coded
/// `len.saturating_sub(1)` is written to dodge.
///
/// `0` is returned for an empty container and **is not a valid index there**.
/// Compose as `clamp_upper(idx, last_index(len))`, which is bounded by
/// `last_index(len)` *as a checked proposition*, and test `len` separately.
pub fn last_index(len: u32) -> u32 {
    if len == 0 {
        return 0;
    }
    len - 1
}

/// `num` as a percentage of `den`, truncated toward zero.
///
/// **Tier 2.** Proved: no zero-divisor panic and no multiplication overflow, on
/// every input. Not proved, and true by construction only: the result is in
/// `0..=100`.
///
/// Returns `0` when `den == 0` and `100` when `num >= den`.
pub fn percent(num: u32, den: u32) -> u32 {
    if den == 0 {
        return 0;
    }
    // The clamp is in u64 and the cast comes AFTER it. The other order — cast
    // first, clamp the u32 — reads the same and is WRONG: `(num as u64) * 100`
    // reaches 4.29e11, and truncating that to u32 can land under 100, so
    // `percent(42_949_673, 1)` would return 4. That shape passed the verifier
    // (its overflow and zero-divisor rows both PROVE; neither is about
    // truncation) and was caught by a unit test. See the module note.
    let q: u64 = (num as u64) * 100 / (den as u64);
    if q > 100 {
        return 100;
    }
    q as u32
}

/// `num` as parts-per-thousand of `den`, truncated toward zero.
///
/// **Tier 2**, on the same terms as [`percent`]. The finer-grained twin, for
/// the coverage lines where the difference between 99.4% and 99.9% is the whole
/// message.
pub fn permille(num: u32, den: u32) -> u32 {
    if den == 0 {
        return 0;
    }
    let q: u64 = (num as u64) * 1000 / (den as u64);
    if q > 1000 {
        return 1000;
    }
    q as u32
}

/// `num` as a fraction of `den` expressed out of `scale`.
///
/// **Tier 2**, on the same terms as [`percent`]. The general form: pass
/// `scale = 100` for a percentage, `10_000` for basis points.
pub fn scaled_ratio(num: u32, den: u32, scale: u32) -> u32 {
    if den == 0 {
        return 0;
    }
    // `(num as u64) * (scale as u64)` peaks at `(2^32 - 1)^2`, which is below
    // `u64::MAX` — that is why the multiplication overflow row proves for every
    // input rather than needing a guard.
    let q: u64 = (num as u64) * (scale as u64) / (den as u64);
    if q > (scale as u64) {
        return scale;
    }
    q as u32
}

// ---------------------------------------------------------------------------
// Uncontracted arithmetic helpers. These exist so the tier-1 wrappers above can
// stay arithmetic-free; their own safety obligations are proved.
// ---------------------------------------------------------------------------

fn raw_span(lo: u32, hi: u32) -> u32 {
    if lo >= hi {
        return 0;
    }
    hi - lo
}

fn raw_diff(a: u32, b: u32) -> u32 {
    if b >= a {
        return 0;
    }
    a - b
}

fn raw_sum(a: u32, b: u32) -> u32 {
    // WIDENED, not guarded. The obvious spelling
    //     if a > 4_294_967_295u32 - b { return 4_294_967_295u32; }
    //     a + b
    // is the measured `Overflow(Add)` wall: a guarded add on direct integer
    // parameters leaves both the primary row and its hardened twin UNKNOWN, and
    // the `MAX - b` gets downgraded to runtime-checked as well. Widening both
    // operands first puts the sum in reach of the closed cast-range recognizer
    // — `(a as u64) + (b as u64)` peaks at `2^33 - 2`, far below `u64::MAX` —
    // and the row proves outright.
    //
    // The clamp is in u64 and the cast follows it, for the same truncation
    // reason as `percent`.
    let s: u64 = (a as u64) + (b as u64);
    if s > 4_294_967_295u64 {
        return 4_294_967_295u32;
    }
    s as u32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clamps_are_total_and_bounded() {
        assert_eq!(clamp_upper(5, 3), 3);
        assert_eq!(clamp_upper(2, 3), 2);
        assert_eq!(clamp_upper(0, 0), 0);
        assert_eq!(clamp_upper(u32::MAX, 0), 0);
        assert_eq!(clamp_lower(1, 3), 3);
        assert_eq!(clamp_lower(5, 3), 5);
        assert_eq!(clamp_range(5, 1, 3), 3);
        assert_eq!(clamp_range(0, 1, 3), 1);
        assert_eq!(clamp_range(2, 1, 3), 2);
        // Inverted window: `core`'s `Ord::clamp` panics here.
        assert_eq!(clamp_range(9, 7, 3), 7);
    }

    #[test]
    fn span_and_diff_cannot_underflow() {
        assert_eq!(span_width(3, 9), 6);
        assert_eq!(span_width(9, 3), 0);
        assert_eq!(span_width(4, 4), 0);
        assert_eq!(span_width(0, u32::MAX), u32::MAX);
        assert_eq!(saturating_diff(9, 3), 6);
        assert_eq!(saturating_diff(3, 9), 0);
        assert_eq!(saturating_diff(0, u32::MAX), 0);
    }

    #[test]
    fn capped_sum_saturates_then_caps() {
        assert_eq!(capped_sum(2, 3, 100), 5);
        assert_eq!(capped_sum(2, 3, 4), 4);
        assert_eq!(capped_sum(u32::MAX, u32::MAX, u32::MAX), u32::MAX);
        assert_eq!(capped_sum(u32::MAX, 1, 10), 10);
    }

    #[test]
    fn last_index_is_the_safe_len_minus_one() {
        assert_eq!(last_index(0), 0);
        assert_eq!(last_index(1), 0);
        assert_eq!(last_index(4), 3);
        assert_eq!(last_index(u32::MAX), u32::MAX - 1);
        // The composition the docs prescribe.
        assert_eq!(clamp_upper(7, last_index(4)), 3);
        assert_eq!(clamp_upper(2, last_index(4)), 2);
    }

    #[test]
    fn percent_is_bounded_and_zero_population_is_zero() {
        assert_eq!(percent(0, 0), 0);
        assert_eq!(percent(7, 0), 0);
        assert_eq!(percent(1, 3), 33);
        assert_eq!(percent(2, 3), 66);
        assert_eq!(percent(3, 3), 100);
        assert_eq!(percent(9, 3), 100);
        assert_eq!(percent(u32::MAX, u32::MAX), 100);
        assert_eq!(percent(u32::MAX, 1), 100);
        assert_eq!(percent(1, u32::MAX), 0);
    }

    /// Regression: written 2026-08-28 against a defect this crate shipped for
    /// twenty minutes. Casting to u32 BEFORE the clamp truncates
    /// `(num as u64) * 100`, and these three inputs land the truncated value
    /// under the clamp threshold, so the buggy version returned 4, 40 and 396.
    ///
    /// The point worth keeping: that version PASSED every verification
    /// obligation it had. Truncation of an `as` cast is not an overflow and not
    /// a zero divisor, so nothing in tier 2 was ever going to see it. A proved
    /// safety obligation is not a proved specification.
    #[test]
    fn cast_before_clamp_truncation_regression() {
        assert_eq!(percent(42_949_673, 1), 100);
        assert_eq!(permille(4_294_968, 1), 1000);
        assert_eq!(scaled_ratio(42_949_673, 1, 100), 100);
    }

    #[test]
    fn permille_and_scaled_ratio_agree_with_percent() {
        assert_eq!(permille(0, 0), 0);
        assert_eq!(permille(994, 1000), 994);
        assert_eq!(permille(5, 1), 1000);
        assert_eq!(scaled_ratio(1, 3, 100), percent(1, 3));
        assert_eq!(scaled_ratio(994, 1000, 1000), permille(994, 1000));
        assert_eq!(scaled_ratio(1, 2, 10_000), 5_000);
        assert_eq!(scaled_ratio(3, 0, 10_000), 0);
        assert_eq!(scaled_ratio(9, 3, 7), 7);
        assert_eq!(scaled_ratio(u32::MAX, 1, u32::MAX), u32::MAX);
    }
}
