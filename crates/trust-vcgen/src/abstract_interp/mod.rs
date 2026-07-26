// trust_vcgen/abstract_interp: Abstract interpretation framework for VC generation
//
// Implements interval abstract domain with widening-based fixpoint computation
// over MIR CFGs. Extracts loop invariants from converged abstract states.
//
// Architecture:
//   AbstractDomain trait  -> generic lattice operations
//   IntervalDomain        -> variable -> [lo, hi] mapping
//   transfer_function     -> statement-level abstract transformer
//   fixpoint              -> iterative fixpoint with widening at loop headers
//   extract_invariants    -> interval bounds -> Formula invariants
//
// Reference: Cousot & Cousot, "Abstract Interpretation: A Unified Lattice Model
// for Static Analysis of Programs" (POPL 1977).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

pub(crate) mod arithmetic;
pub(crate) mod discharge;
pub(crate) mod domain;
#[cfg(test)]
mod tests;
pub(crate) mod transfer;

// Re-export all public items so external consumers see the same API.
pub use arithmetic::*;
pub use discharge::*;
pub use domain::*;
pub use transfer::*;

// ── Abstract Domain Trait ──────────────────────────────────────────────────

/// Lattice operations for an abstract domain.
pub trait AbstractDomain: Clone + PartialEq {
    /// Top element (no information — all values possible).
    fn top() -> Self;
    /// Bottom element (unreachable — no values possible).
    fn bottom() -> Self;
    /// Least upper bound (join).
    fn join(&self, other: &Self) -> Self;
    /// Greatest lower bound (meet).
    fn meet(&self, other: &Self) -> Self;
    /// Widening operator for convergence guarantee.
    fn widen(&self, other: &Self) -> Self;
    /// Narrowing operator to recover precision after widening.
    fn narrow(&self, other: &Self) -> Self;
    /// Is this the bottom element?
    fn is_bottom(&self) -> bool;
    /// Partial order: self <= other in the lattice.
    fn leq(&self, other: &Self) -> bool;
}

/// Compute the exact function-wide interval environment used by both
/// production VC augmentation and proof-gated reconstruction. Keeping this in
/// one helper prevents the E4 authority gate from accepting a merely
/// shape-compatible `And([env, raw])` whose environment was not derived by the
/// same sound abstract interpreter.
pub(crate) fn merged_interval_environment(
    func: &trust_types::VerifiableFunction,
) -> IntervalDomain {
    let initial = type_aware_initial_state(func);
    let config = FixpointConfig::for_function(func);
    let fixpoint = fixpoint_configured(func, initial, &config);
    let mut merged = IntervalDomain::bottom();
    for state in fixpoint.block_states.values() {
        merged = merged.join(state);
    }
    merged
}

// ── Interval ───────────────────────────────────────────────────────────────

/// A single numeric interval [lo, hi]. Both bounds are inclusive.
/// Bottom is represented by lo > hi.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Interval {
    pub lo: i128,
    pub hi: i128,
}

impl Interval {
    pub const TOP: Self = Interval { lo: i128::MIN, hi: i128::MAX };
    pub const BOTTOM: Self = Interval { lo: 1, hi: 0 }; // lo > hi

    #[must_use]
    pub fn new(lo: i128, hi: i128) -> Self {
        Interval { lo, hi }
    }

    #[must_use]
    pub fn constant(v: i128) -> Self {
        Interval { lo: v, hi: v }
    }

    #[must_use]
    pub fn is_bottom(&self) -> bool {
        self.lo > self.hi
    }

    #[must_use]
    pub fn contains(&self, v: i128) -> bool {
        !self.is_bottom() && self.lo <= v && v <= self.hi
    }

    /// Widen with thresholds: instead of jumping to +/-infinity, jump to the
    /// nearest threshold constant. Falls back to infinity when no threshold
    /// is available.
    #[must_use]
    pub fn widen_with_thresholds(&self, other: &Self, thresholds: &ThresholdSet) -> Self {
        if self.is_bottom() {
            return *other;
        }
        if other.is_bottom() {
            return *self;
        }
        let lo = if other.lo < self.lo { thresholds.next_below(self.lo) } else { self.lo };
        let hi = if other.hi > self.hi { thresholds.next_above(self.hi) } else { self.hi };
        Interval { lo, hi }
    }
}

impl AbstractDomain for Interval {
    fn top() -> Self {
        Self::TOP
    }

    fn bottom() -> Self {
        Self::BOTTOM
    }

    fn join(&self, other: &Self) -> Self {
        if self.is_bottom() {
            return *other;
        }
        if other.is_bottom() {
            return *self;
        }
        Interval { lo: self.lo.min(other.lo), hi: self.hi.max(other.hi) }
    }

    fn meet(&self, other: &Self) -> Self {
        if self.is_bottom() || other.is_bottom() {
            return Self::BOTTOM;
        }
        let lo = self.lo.max(other.lo);
        let hi = self.hi.min(other.hi);
        if lo > hi { Self::BOTTOM } else { Interval { lo, hi } }
    }

    fn widen(&self, other: &Self) -> Self {
        if self.is_bottom() {
            return *other;
        }
        if other.is_bottom() {
            return *self;
        }
        let lo = if other.lo < self.lo { i128::MIN } else { self.lo };
        let hi = if other.hi > self.hi { i128::MAX } else { self.hi };
        Interval { lo, hi }
    }

    fn narrow(&self, other: &Self) -> Self {
        if self.is_bottom() {
            return Self::BOTTOM;
        }
        if other.is_bottom() {
            return Self::BOTTOM;
        }
        let lo = if self.lo == i128::MIN { other.lo } else { self.lo };
        let hi = if self.hi == i128::MAX { other.hi } else { self.hi };
        if lo > hi { Self::BOTTOM } else { Interval { lo, hi } }
    }

    fn is_bottom(&self) -> bool {
        self.lo > self.hi
    }

    fn leq(&self, other: &Self) -> bool {
        if self.is_bottom() {
            return true;
        }
        if other.is_bottom() {
            return false;
        }
        other.lo <= self.lo && self.hi <= other.hi
    }
}

// ── Threshold Widening ────────────────────────────────────────────────────

/// Sorted set of threshold constants extracted from a function's CFG.
///
/// Used by threshold widening to jump to the nearest "interesting" constant
/// instead of +/-infinity. Reference: Blanchet et al., "A Static Analyzer
/// for Large Safety-Critical Software" (PLDI 2003).
#[derive(Debug, Clone)]
pub struct ThresholdSet {
    /// Threshold values in ascending order (deduplicated).
    values: Vec<i128>,
}

impl ThresholdSet {
    /// Create a threshold set, sorting and deduplicating the input.
    #[must_use]
    pub fn new(mut values: Vec<i128>) -> Self {
        values.sort_unstable();
        values.dedup();
        Self { values }
    }

    /// Find the nearest threshold strictly greater than `value`, or `i128::MAX`.
    #[must_use]
    pub fn next_above(&self, value: i128) -> i128 {
        // Binary search for the first element > value.
        match self.values.binary_search(&value) {
            Ok(i) => {
                // Exact match; look for next strictly greater.
                if i + 1 < self.values.len() { self.values[i + 1] } else { i128::MAX }
            }
            Err(i) => {
                if i < self.values.len() {
                    self.values[i]
                } else {
                    i128::MAX
                }
            }
        }
    }

    /// Find the nearest threshold strictly less than `value`, or `i128::MIN`.
    #[must_use]
    pub fn next_below(&self, value: i128) -> i128 {
        match self.values.binary_search(&value) {
            Ok(i) => {
                // Exact match; look for next strictly less.
                if i > 0 { self.values[i - 1] } else { i128::MIN }
            }
            Err(i) => {
                if i > 0 {
                    self.values[i - 1]
                } else {
                    i128::MIN
                }
            }
        }
    }

    /// Whether the set is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    /// Number of thresholds.
    #[must_use]
    pub fn len(&self) -> usize {
        self.values.len()
    }

    /// Access the sorted threshold values.
    #[must_use]
    pub fn values(&self) -> &[i128] {
        &self.values
    }
}
