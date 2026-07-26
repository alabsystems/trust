// trust-strengthen/abstract_domains/product.rs: Reduced product domain
//
// Combines multiple abstract domains with cross-domain reduction
// to tighten the overall abstraction.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use super::AbstractDomainOps;
use super::congruence::CongruenceValue;
use super::interval::{Bound, IntervalDomain};
use super::octagon::OctagonDomain;

// ---------------------------------------------------------------------------
// ReducedProduct
// ---------------------------------------------------------------------------

/// Reduced product of two abstract domains.
///
/// After each lattice operation, the `reduce` method is called to propagate
/// information between the two component domains, tightening the overall
/// abstraction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReducedProduct<A: AbstractDomainOps, B: AbstractDomainOps> {
    /// First component domain.
    pub first: A,
    /// Second component domain.
    pub second: B,
}

impl<A: AbstractDomainOps, B: AbstractDomainOps> ReducedProduct<A, B> {
    /// Create a new product domain from two components.
    #[must_use]
    pub fn new(first: A, second: B) -> Self {
        Self { first, second }
    }
}

impl<A: AbstractDomainOps, B: AbstractDomainOps> AbstractDomainOps for ReducedProduct<A, B> {
    fn join(&self, other: &Self) -> Self {
        Self { first: self.first.join(&other.first), second: self.second.join(&other.second) }
    }

    fn meet(&self, other: &Self) -> Self {
        Self { first: self.first.meet(&other.first), second: self.second.meet(&other.second) }
    }

    fn widen(&self, new: &Self) -> Self {
        Self { first: self.first.widen(&new.first), second: self.second.widen(&new.second) }
    }

    fn narrow(&self, new: &Self) -> Self {
        Self { first: self.first.narrow(&new.first), second: self.second.narrow(&new.second) }
    }

    fn is_bottom(&self) -> bool {
        self.first.is_bottom() || self.second.is_bottom()
    }

    fn is_top(&self) -> bool {
        self.first.is_top() && self.second.is_top()
    }

    fn bottom() -> Self {
        Self { first: A::bottom(), second: B::bottom() }
    }

    fn top() -> Self {
        Self { first: A::top(), second: B::top() }
    }

    fn is_subset_of(&self, other: &Self) -> bool {
        self.first.is_subset_of(&other.first) && self.second.is_subset_of(&other.second)
    }
}

// ---------------------------------------------------------------------------
// Reduction helpers for specific product combinations
// ---------------------------------------------------------------------------

/// Reduce an interval+octagon product by propagating interval bounds into the octagon
/// and octagon-derived bounds back into intervals.
pub fn reduce_interval_octagon(
    interval: &mut IntervalDomain,
    octagon: &mut OctagonDomain,
    var: &str,
) {
    if interval.is_bottom() || octagon.is_bottom() {
        *interval = IntervalDomain::Bottom;
        octagon.is_bottom = true;
        return;
    }

    // Propagate interval bounds into octagon
    if let Some(lo) = interval.low() {
        octagon.add_lower_bound(var, lo);
    }
    if let Some(hi) = interval.high() {
        octagon.add_upper_bound(var, hi);
    }

    if octagon.is_bottom() {
        *interval = IntervalDomain::Bottom;
        return;
    }

    // Propagate octagon-derived bounds back into interval
    let oct_interval = octagon.get_interval(var);
    *interval = interval.meet(&oct_interval);
}

/// Reduce an interval+congruence product by using congruence to tighten interval bounds.
///
/// For example, if interval is [3, 10] and congruence is `x === 0 (mod 4)`,
/// then we can tighten to [4, 8] (the range of multiples of 4 in [3, 10]).
pub fn reduce_interval_congruence(interval: &mut IntervalDomain, congruence: &CongruenceValue) {
    if interval.is_bottom() || matches!(congruence, CongruenceValue::Bottom) {
        *interval = IntervalDomain::Bottom;
        return;
    }

    match congruence {
        CongruenceValue::Bottom => {
            *interval = IntervalDomain::Bottom;
        }
        CongruenceValue::Congruence { modulus: 0, residue } => {
            // Exact value: intersect with interval
            let exact = IntervalDomain::constant(*residue as i128);
            *interval = interval.meet(&exact);
        }
        CongruenceValue::Congruence { modulus, residue } if *modulus > 1 => {
            // Tighten lower bound up to next value in congruence class
            if let Some(lo) = interval.low() {
                let m = *modulus as i128;
                let r = *residue as i128;
                // Find smallest x >= lo such that x === r (mod m)
                let remainder = ((lo % m) + m) % m;
                let new_lo =
                    if remainder <= r { lo + (r - remainder) } else { lo + (m - remainder + r) };
                if let Some(hi) = interval.high()
                    && new_lo > hi
                {
                    *interval = IntervalDomain::Bottom;
                    return;
                }
                *interval = match interval {
                    IntervalDomain::Bottom => IntervalDomain::Bottom,
                    IntervalDomain::Interval { high, .. } => {
                        IntervalDomain::Interval { low: Bound::Finite(new_lo), high: *high }
                    }
                };
            }
            // Tighten upper bound down to previous value in congruence class
            if let Some(hi) = interval.high() {
                let m = *modulus as i128;
                let r = *residue as i128;
                // Find largest x <= hi such that x === r (mod m)
                let remainder = ((hi % m) + m) % m;
                let new_hi =
                    if remainder >= r { hi - (remainder - r) } else { hi - (m - r + remainder) };
                if let Some(lo) = interval.low()
                    && new_hi < lo
                {
                    *interval = IntervalDomain::Bottom;
                    return;
                }
                *interval = match interval {
                    IntervalDomain::Bottom => IntervalDomain::Bottom,
                    IntervalDomain::Interval { low, .. } => {
                        IntervalDomain::Interval { low: *low, high: Bound::Finite(new_hi) }
                    }
                };
            }
        }
        _ => {} // modulus == 1 is top, no tightening possible
    }
}
