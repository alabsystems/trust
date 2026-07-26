// trust-strengthen/abstract_domains/interval.rs: Interval domain
//
// Classic integer interval domain: [low, high] with unbounded endpoints
// and widening with thresholds.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt;

use super::AbstractDomainOps;

// ---------------------------------------------------------------------------
// Bound
// ---------------------------------------------------------------------------

/// Bound for an interval endpoint: either a finite value or unbounded.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Bound {
    /// Negative infinity (lower bound) or positive infinity (upper bound).
    Unbounded,
    /// A finite value.
    Finite(i128),
}

impl Bound {
    /// Returns the finite value, or `None` if unbounded.
    #[must_use]
    pub fn finite(self) -> Option<i128> {
        match self {
            Self::Finite(v) => Some(v),
            Self::Unbounded => None,
        }
    }
}

impl fmt::Display for Bound {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unbounded => write!(f, "inf"),
            Self::Finite(v) => write!(f, "{v}"),
        }
    }
}

// ---------------------------------------------------------------------------
// IntervalDomain
// ---------------------------------------------------------------------------

/// Classic integer interval domain: [low, high].
///
/// Supports unbounded intervals (e.g., [0, +inf)) and widening with thresholds.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IntervalDomain {
    /// The empty set -- unreachable program point.
    Bottom,
    /// An interval [low, high] where low <= high.
    Interval { low: Bound, high: Bound },
}

/// Default widening thresholds: common bounds that help convergence.
const DEFAULT_THRESHOLDS: &[i128] = &[
    i128::MIN,
    -1_000_000,
    -65536,
    -256,
    -128,
    -1,
    0,
    1,
    2,
    127,
    255,
    256,
    65535,
    65536,
    1_000_000,
    i128::MAX,
];

impl IntervalDomain {
    /// Create a new interval [low, high].
    #[must_use]
    pub fn new(low: i128, high: i128) -> Self {
        if low > high {
            Self::Bottom
        } else {
            Self::Interval { low: Bound::Finite(low), high: Bound::Finite(high) }
        }
    }

    /// Create a singleton interval [v, v].
    #[must_use]
    pub fn constant(v: i128) -> Self {
        Self::Interval { low: Bound::Finite(v), high: Bound::Finite(v) }
    }

    /// Create an interval [low, +inf).
    #[must_use]
    pub fn at_least(low: i128) -> Self {
        Self::Interval { low: Bound::Finite(low), high: Bound::Unbounded }
    }

    /// Create an interval (-inf, high].
    #[must_use]
    pub fn at_most(high: i128) -> Self {
        Self::Interval { low: Bound::Unbounded, high: Bound::Finite(high) }
    }

    /// Returns the lower bound, if finite.
    #[must_use]
    pub fn low(&self) -> Option<i128> {
        match self {
            Self::Bottom => None,
            Self::Interval { low, .. } => low.finite(),
        }
    }

    /// Returns the upper bound, if finite.
    #[must_use]
    pub fn high(&self) -> Option<i128> {
        match self {
            Self::Bottom => None,
            Self::Interval { high, .. } => high.finite(),
        }
    }

    /// Check if the interval contains a specific value.
    #[must_use]
    pub fn contains(&self, value: i128) -> bool {
        match self {
            Self::Bottom => false,
            Self::Interval { low, high } => {
                let low_ok = match low {
                    Bound::Unbounded => true,
                    Bound::Finite(l) => value >= *l,
                };
                let high_ok = match high {
                    Bound::Unbounded => true,
                    Bound::Finite(h) => value <= *h,
                };
                low_ok && high_ok
            }
        }
    }

    /// Widen with user-supplied thresholds.
    ///
    /// Instead of jumping to +/- infinity, jumps to the next threshold value.
    #[must_use]
    pub fn widen_with_thresholds(&self, new: &Self, thresholds: &[i128]) -> Self {
        match (self, new) {
            (Self::Bottom, x) => x.clone(),
            (x, Self::Bottom) => x.clone(),
            (
                Self::Interval { low: l1, high: h1, .. },
                Self::Interval { low: l2, high: h2, .. },
            ) => {
                let low = widen_lower_bound(*l1, *l2, thresholds);
                let high = widen_upper_bound(*h1, *h2, thresholds);
                Self::Interval { low, high }
            }
        }
    }

    /// Abstract addition: [a, b] + [c, d] = [a+c, b+d].
    #[must_use]
    pub fn add(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (Self::Interval { low: l1, high: h1 }, Self::Interval { low: l2, high: h2 }) => {
                Self::Interval { low: add_bounds(*l1, *l2), high: add_bounds(*h1, *h2) }
            }
        }
    }

    /// Abstract subtraction: [a, b] - [c, d] = [a-d, b-c].
    #[must_use]
    pub fn sub(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (Self::Interval { low: l1, high: h1 }, Self::Interval { low: l2, high: h2 }) => {
                Self::Interval { low: sub_bounds(*l1, *h2), high: sub_bounds(*h1, *l2) }
            }
        }
    }

    /// Abstract multiplication (handles sign correctly).
    #[must_use]
    pub fn mul(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (Self::Interval { low: l1, high: h1 }, Self::Interval { low: l2, high: h2 }) => {
                // If any bound is unbounded, result is top
                let corners = match (l1.finite(), h1.finite(), l2.finite(), h2.finite()) {
                    (Some(a), Some(b), Some(c), Some(d)) => {
                        vec![
                            a.saturating_mul(c),
                            a.saturating_mul(d),
                            b.saturating_mul(c),
                            b.saturating_mul(d),
                        ]
                    }
                    _ => return Self::top(),
                };
                let lo = *corners.iter().min().expect("corners non-empty");
                let hi = *corners.iter().max().expect("corners non-empty");
                Self::new(lo, hi)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Helper functions
// ---------------------------------------------------------------------------

/// Helper: widen a lower bound using thresholds.
fn widen_lower_bound(old: Bound, new: Bound, thresholds: &[i128]) -> Bound {
    match (old, new) {
        (Bound::Unbounded, _) => Bound::Unbounded,
        (_, Bound::Unbounded) => Bound::Unbounded,
        (Bound::Finite(o), Bound::Finite(n)) => {
            if n >= o {
                Bound::Finite(o)
            } else {
                // Jump to next threshold below n
                let threshold = thresholds.iter().rev().find(|&&t| t <= n);
                match threshold {
                    Some(&t) => Bound::Finite(t),
                    None => Bound::Unbounded,
                }
            }
        }
    }
}

/// Helper: widen an upper bound using thresholds.
fn widen_upper_bound(old: Bound, new: Bound, thresholds: &[i128]) -> Bound {
    match (old, new) {
        (Bound::Unbounded, _) => Bound::Unbounded,
        (_, Bound::Unbounded) => Bound::Unbounded,
        (Bound::Finite(o), Bound::Finite(n)) => {
            if n <= o {
                Bound::Finite(o)
            } else {
                // Jump to next threshold above n
                let threshold = thresholds.iter().find(|&&t| t >= n);
                match threshold {
                    Some(&t) => Bound::Finite(t),
                    None => Bound::Unbounded,
                }
            }
        }
    }
}

/// Helper: add two bounds.
fn add_bounds(a: Bound, b: Bound) -> Bound {
    match (a, b) {
        (Bound::Unbounded, _) | (_, Bound::Unbounded) => Bound::Unbounded,
        (Bound::Finite(x), Bound::Finite(y)) => Bound::Finite(x.saturating_add(y)),
    }
}

/// Helper: subtract two bounds.
fn sub_bounds(a: Bound, b: Bound) -> Bound {
    match (a, b) {
        (Bound::Unbounded, _) | (_, Bound::Unbounded) => Bound::Unbounded,
        (Bound::Finite(x), Bound::Finite(y)) => Bound::Finite(x.saturating_sub(y)),
    }
}

impl fmt::Display for IntervalDomain {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bottom => write!(f, "bottom"),
            Self::Interval { low, high } => {
                let lo_str = match low {
                    Bound::Unbounded => "-inf".to_string(),
                    Bound::Finite(v) => v.to_string(),
                };
                let hi_str = match high {
                    Bound::Unbounded => "+inf".to_string(),
                    Bound::Finite(v) => v.to_string(),
                };
                write!(f, "[{lo_str}, {hi_str}]")
            }
        }
    }
}

impl AbstractDomainOps for IntervalDomain {
    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Bottom, x) | (x, Self::Bottom) => x.clone(),
            (Self::Interval { low: l1, high: h1 }, Self::Interval { low: l2, high: h2 }) => {
                let low = match (l1, l2) {
                    (Bound::Unbounded, _) | (_, Bound::Unbounded) => Bound::Unbounded,
                    (Bound::Finite(a), Bound::Finite(b)) => Bound::Finite((*a).min(*b)),
                };
                let high = match (h1, h2) {
                    (Bound::Unbounded, _) | (_, Bound::Unbounded) => Bound::Unbounded,
                    (Bound::Finite(a), Bound::Finite(b)) => Bound::Finite((*a).max(*b)),
                };
                Self::Interval { low, high }
            }
        }
    }

    fn meet(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (Self::Interval { low: l1, high: h1 }, Self::Interval { low: l2, high: h2 }) => {
                let low = match (l1, l2) {
                    (Bound::Unbounded, x) | (x, Bound::Unbounded) => *x,
                    (Bound::Finite(a), Bound::Finite(b)) => Bound::Finite((*a).max(*b)),
                };
                let high = match (h1, h2) {
                    (Bound::Unbounded, x) | (x, Bound::Unbounded) => *x,
                    (Bound::Finite(a), Bound::Finite(b)) => Bound::Finite((*a).min(*b)),
                };
                // Check for empty interval
                match (low, high) {
                    (Bound::Finite(lo), Bound::Finite(hi)) if lo > hi => Self::Bottom,
                    _ => Self::Interval { low, high },
                }
            }
        }
    }

    fn widen(&self, new: &Self) -> Self {
        self.widen_with_thresholds(new, DEFAULT_THRESHOLDS)
    }

    fn narrow(&self, new: &Self) -> Self {
        match (self, new) {
            (Self::Bottom, _) => Self::Bottom,
            (x, Self::Bottom) => x.clone(),
            (Self::Interval { low: l1, high: h1 }, Self::Interval { low: l2, high: h2 }) => {
                let low = if *l1 == Bound::Unbounded { *l2 } else { *l1 };
                let high = if *h1 == Bound::Unbounded { *h2 } else { *h1 };
                match (low, high) {
                    (Bound::Finite(lo), Bound::Finite(hi)) if lo > hi => Self::Bottom,
                    _ => Self::Interval { low, high },
                }
            }
        }
    }

    fn is_bottom(&self) -> bool {
        matches!(self, Self::Bottom)
    }

    fn is_top(&self) -> bool {
        matches!(self, Self::Interval { low: Bound::Unbounded, high: Bound::Unbounded })
    }

    fn bottom() -> Self {
        Self::Bottom
    }

    fn top() -> Self {
        Self::Interval { low: Bound::Unbounded, high: Bound::Unbounded }
    }

    fn is_subset_of(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Bottom, _) => true,
            (_, Self::Bottom) => false,
            (Self::Interval { low: l1, high: h1 }, Self::Interval { low: l2, high: h2 }) => {
                let low_ok = match (l1, l2) {
                    (_, Bound::Unbounded) => true,
                    (Bound::Unbounded, Bound::Finite(_)) => false,
                    (Bound::Finite(a), Bound::Finite(b)) => a >= b,
                };
                let high_ok = match (h1, h2) {
                    (_, Bound::Unbounded) => true,
                    (Bound::Unbounded, Bound::Finite(_)) => false,
                    (Bound::Finite(a), Bound::Finite(b)) => a <= b,
                };
                low_ok && high_ok
            }
        }
    }
}
