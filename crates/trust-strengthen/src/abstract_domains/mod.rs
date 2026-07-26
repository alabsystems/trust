// trust-strengthen/abstract_domains: Abstract domain hierarchy with reduced product
//
// Implements a proper abstract domain hierarchy:
// - AbstractDomainOps trait: join, meet, widen, narrow, is_bottom, is_top
// - IntervalDomain: classic [low, high] integer intervals with widening thresholds
// - OctagonDomain: difference-bound matrices (DBM) for relational properties (x - y <= c)
// - CongruenceDomain: modular arithmetic (x === a mod n)
// - ReducedProduct: combines multiple domains with cross-domain reduction
//
// Part of #448.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

mod congruence;
mod interval;
mod octagon;
mod product;
#[cfg(test)]
mod tests;

use std::fmt;

// ---------------------------------------------------------------------------
// Abstract domain trait
// ---------------------------------------------------------------------------

/// Core operations that every abstract domain must support.
///
/// Generic over the concrete element type to allow different numeric types.
pub trait AbstractDomainOps: Clone + fmt::Debug + PartialEq {
    /// Least upper bound: smallest element containing both `self` and `other`.
    fn join(&self, other: &Self) -> Self;

    /// Greatest lower bound: largest element contained in both `self` and `other`.
    fn meet(&self, other: &Self) -> Self;

    /// Widening operator: accelerate convergence by extrapolating.
    ///
    /// `old` is the previous iterate, `new` is the current iterate.
    /// The result must be an upper bound of `new` and must guarantee
    /// termination of ascending chains.
    fn widen(&self, new: &Self) -> Self;

    /// Narrowing operator: recover precision after widening.
    ///
    /// `old` is the widened result, `new` is a more precise iterate.
    /// The result is between `new` and `old` (inclusive).
    fn narrow(&self, new: &Self) -> Self;

    /// Returns true if this element represents the empty set (unreachable).
    fn is_bottom(&self) -> bool;

    /// Returns true if this element represents the universal set (no information).
    fn is_top(&self) -> bool;

    /// Returns the bottom element (empty set).
    fn bottom() -> Self;

    /// Returns the top element (universal set).
    fn top() -> Self;

    /// Returns true if `self` is a subset of `other` in the lattice ordering.
    fn is_subset_of(&self, other: &Self) -> bool;
}

// Re-export all public types from submodules.
pub use congruence::{CongruenceDomain, CongruenceValue};
// Re-export congruence helpers for tests only (used in abstract_domains/tests.rs).
#[cfg(test)]
pub(crate) use congruence::{congruence_join, congruence_meet, congruence_subset, gcd};
pub use interval::{Bound, IntervalDomain};
pub use octagon::OctagonDomain;
pub use product::{ReducedProduct, reduce_interval_congruence, reduce_interval_octagon};
