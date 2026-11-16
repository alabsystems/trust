// trust_vcgen/abstract_interp/arithmetic.rs: Interval arithmetic operations
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use super::{AbstractDomain, Interval};

// ── Interval Arithmetic ────────────────────────────────────────────────────

/// Add two intervals with overflow to Top.
#[must_use]
pub fn interval_add(a: &Interval, b: &Interval) -> Interval {
    if a.is_bottom() || b.is_bottom() {
        return Interval::BOTTOM;
    }
    let lo = a.lo.checked_add(b.lo);
    let hi = a.hi.checked_add(b.hi);
    match (lo, hi) {
        (Some(lo), Some(hi)) => Interval { lo, hi },
        _ => Interval::TOP,
    }
}

/// Subtract two intervals with overflow to Top.
#[must_use]
pub fn interval_sub(a: &Interval, b: &Interval) -> Interval {
    if a.is_bottom() || b.is_bottom() {
        return Interval::BOTTOM;
    }
    // [a.lo - b.hi, a.hi - b.lo]
    let lo = a.lo.checked_sub(b.hi);
    let hi = a.hi.checked_sub(b.lo);
    match (lo, hi) {
        (Some(lo), Some(hi)) => Interval { lo, hi },
        _ => Interval::TOP,
    }
}

/// Multiply two intervals. Uses the four-corners approach.
#[must_use]
pub fn interval_mul(a: &Interval, b: &Interval) -> Interval {
    if a.is_bottom() || b.is_bottom() {
        return Interval::BOTTOM;
    }
    let corners = [
        a.lo.checked_mul(b.lo),
        a.lo.checked_mul(b.hi),
        a.hi.checked_mul(b.lo),
        a.hi.checked_mul(b.hi),
    ];
    let mut lo = i128::MAX;
    let mut hi = i128::MIN;
    for c in &corners {
        match c {
            Some(v) => {
                lo = lo.min(*v);
                hi = hi.max(*v);
            }
            None => return Interval::TOP,
        }
    }
    Interval { lo, hi }
}

/// Divide two intervals. Handles division by intervals containing zero.
///
/// When the divisor interval contains zero, we split into sub-intervals
/// excluding zero and take the join of results. If the divisor is entirely
/// zero, the result is Bottom (undefined).
#[must_use]
pub fn interval_div(a: &Interval, b: &Interval) -> Interval {
    if a.is_bottom() || b.is_bottom() {
        return Interval::BOTTOM;
    }
    // Divisor is exactly zero — undefined.
    if b.lo == 0 && b.hi == 0 {
        return Interval::BOTTOM;
    }
    // Divisor does not contain zero — standard four-corners.
    if b.lo > 0 || b.hi < 0 {
        return div_four_corners(a, b);
    }
    // Divisor spans zero: split into [b.lo, -1] and [1, b.hi], compute each,
    // and join. This is sound but may over-approximate.
    let mut result = Interval::BOTTOM;
    if b.lo < 0 {
        let neg_part = Interval::new(b.lo, -1);
        result = result.join(&div_four_corners(a, &neg_part));
    }
    if b.hi > 0 {
        let pos_part = Interval::new(1, b.hi);
        result = result.join(&div_four_corners(a, &pos_part));
    }
    result
}

/// Four-corners division for intervals where b does not contain zero.
fn div_four_corners(a: &Interval, b: &Interval) -> Interval {
    let corners = [
        a.lo.checked_div(b.lo),
        a.lo.checked_div(b.hi),
        a.hi.checked_div(b.lo),
        a.hi.checked_div(b.hi),
    ];
    let mut lo = i128::MAX;
    let mut hi = i128::MIN;
    for c in &corners {
        match c {
            Some(v) => {
                lo = lo.min(*v);
                hi = hi.max(*v);
            }
            None => return Interval::TOP,
        }
    }
    Interval { lo, hi }
}

/// Remainder (modulo) of two intervals.
///
/// For a % b where b is a known interval not containing zero:
/// - If a >= 0 and b > 0: result in [0, min(a.hi, b.hi - 1)]
/// - General case: result in [-(|b.hi| - 1), |b.hi| - 1]
#[must_use]
pub fn interval_rem(a: &Interval, b: &Interval) -> Interval {
    if a.is_bottom() || b.is_bottom() {
        return Interval::BOTTOM;
    }
    if b.lo == 0 && b.hi == 0 {
        return Interval::BOTTOM;
    }
    // The absolute max of divisor determines the remainder range.
    let b_abs_max = b.lo.unsigned_abs().max(b.hi.unsigned_abs());
    if b_abs_max == 0 {
        return Interval::BOTTOM;
    }
    let bound = match i128::try_from(b_abs_max - 1) {
        Ok(v) => v,
        Err(_) => return Interval::TOP,
    };
    // If dividend is non-negative, result is in [0, min(a.hi, bound)].
    if a.lo >= 0 {
        return Interval::new(0, a.hi.min(bound));
    }
    // If dividend is non-positive, result is in [max(a.lo, -bound), 0].
    if a.hi <= 0 {
        return Interval::new(a.lo.max(-bound), 0);
    }
    // Mixed sign dividend: result in [-bound, bound].
    Interval::new(-bound, bound)
}

/// Right-shift interval (logical or arithmetic, treated as division by 2^shift).
///
/// For a >> b where b is a constant shift amount:
/// - Unsigned context (a >= 0): result in [a.lo >> b.hi, a.hi >> b.lo]
/// - Signed: use floor division by the shift power.
#[must_use]
pub fn interval_shr(a: &Interval, b: &Interval) -> Interval {
    if a.is_bottom() || b.is_bottom() {
        return Interval::BOTTOM;
    }
    // Shift amount must be non-negative.
    if b.lo < 0 {
        return Interval::TOP;
    }
    // Trust (2026-09-30): an amount interval reaching 128 used to answer `[0, 0]`
    // (or `[-1, 0]`) whatever its LOWER end, so `x >> k` with `k` in `[0, u32::MAX]`
    // was zero (round 10 of the review: `h / x >> s.min(31)` proved and panicked).
    // `a >> s` is monotone in `s` (towards 0, or towards -1 for a negative `a`),
    // so the variable-shift arm below, which clamps each end at 127, covers it.
    // (The transfer clamps an amount to the operand's width before it gets here.)
    // For constant shift amount (common case).
    if b.lo == b.hi {
        let shift = (b.lo as u32).min(127);
        let lo = a.lo >> shift;
        let hi = a.hi >> shift;
        return Interval::new(lo.min(hi), lo.max(hi));
    }
    // Variable shift: conservative bounds.
    // min shift gives widest range, max shift gives narrowest.
    let slo = (b.lo as u32).min(127);
    let shi = (b.hi as u32).min(127);
    let lo_min_shift = a.lo >> slo;
    let lo_max_shift = a.lo >> shi;
    let hi_min_shift = a.hi >> slo;
    let hi_max_shift = a.hi >> shi;
    let all = [lo_min_shift, lo_max_shift, hi_min_shift, hi_max_shift];
    let lo = all.iter().copied().min().unwrap_or(i128::MIN);
    let hi = all.iter().copied().max().unwrap_or(i128::MAX);
    Interval::new(lo, hi)
}

/// Left-shift interval.
#[must_use]
pub fn interval_shl(a: &Interval, b: &Interval) -> Interval {
    if a.is_bottom() || b.is_bottom() {
        return Interval::BOTTOM;
    }
    if b.lo < 0 || b.hi >= 128 {
        return Interval::TOP;
    }
    if b.lo == b.hi {
        // Trust (2026-09-28): multiply by `2^shift` with `checked_mul`. `i128::checked_shl`
        // checks only the shift AMOUNT, so bits shifted past bit 127 were lost silently,
        // and `2^126 << 2` answered 0. The destination's own width is applied separately,
        // by `clamp_bare_binop_to_dest_range`.
        let Some(factor) = 1i128.checked_shl(b.lo as u32).filter(|f| *f > 0) else {
            return Interval::TOP;
        };
        let lo = a.lo.checked_mul(factor);
        let hi = a.hi.checked_mul(factor);
        return match (lo, hi) {
            (Some(lo), Some(hi)) => Interval::new(lo.min(hi), lo.max(hi)),
            _ => Interval::TOP,
        };
    }
    Interval::TOP
}

/// Bitwise AND interval (conservative: at least one non-negative input).
#[must_use]
pub fn interval_bitand(a: &Interval, b: &Interval) -> Interval {
    if a.is_bottom() || b.is_bottom() {
        return Interval::BOTTOM;
    }
    // If both are non-negative, result is in [0, min(a.hi, b.hi)].
    if a.lo >= 0 && b.lo >= 0 {
        return Interval::new(0, a.hi.min(b.hi));
    }
    // Trust (2026-10-10): ONE non-negative operand bounds the result alone. Its sign
    // bit is clear, so the result's is too, and the result's set bits are a subset of
    // its bits, so `0 <= a & m <= m` whatever the other operand is (any width, two's
    // complement). `s = (s + b) & 0xffff` read `s` as Top at its loop head (the add
    // temp it masks has no interval), so `s + b` was refused overflow (sweep p21).
    if b.lo >= 0 {
        return Interval::new(0, b.hi);
    }
    if a.lo >= 0 {
        return Interval::new(0, a.hi);
    }
    Interval::TOP
}

/// Bitwise OR interval (conservative).
#[must_use]
pub fn interval_bitor(a: &Interval, b: &Interval) -> Interval {
    if a.is_bottom() || b.is_bottom() {
        return Interval::BOTTOM;
    }
    // If both are non-negative, result is in [max(a.lo, b.lo), next_power_of_two - 1].
    if a.lo >= 0 && b.lo >= 0 {
        let lo = a.lo.max(b.lo);
        // Upper bound: at most the sum (OR can't exceed that for non-overlapping bits).
        let hi = a.hi.checked_add(b.hi).unwrap_or(i128::MAX);
        return Interval::new(lo, hi);
    }
    Interval::TOP
}
