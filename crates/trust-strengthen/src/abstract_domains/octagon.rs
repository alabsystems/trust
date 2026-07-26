// trust-strengthen/abstract_domains/octagon.rs: Octagon domain
//
// Difference Bound Matrix (DBM) representation for relational properties
// of the form +/-x_i +/- x_j <= c.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;
use std::fmt;

use super::AbstractDomainOps;
use super::interval::{Bound, IntervalDomain};

/// Octagon domain using Difference Bound Matrix (DBM) representation.
///
/// For `n` variables, the DBM is a `2n x 2n` matrix where:
/// - Variable `x_i` has positive form at index `2*i` and negative form at index `2*i + 1`.
/// - Entry `dbm[i][j]` represents the constraint `x_i' - x_j' <= dbm[i][j]`
///   where `x_k'` is `+x_{k/2}` if `k` is even, `-x_{k/2}` if `k` is odd.
///
/// This captures constraints of the form: `+/-x_i +/- x_j <= c`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OctagonDomain {
    /// Variable names, in order. Variable `i` has index `i` in this vec.
    pub(super) vars: Vec<String>,
    /// Variable name to index mapping.
    pub(super) var_index: BTreeMap<String, usize>,
    /// The DBM matrix, stored as a flat vec of size `(2*n) * (2*n)`.
    /// Entry `[i][j]` is at position `i * (2*n) + j`.
    /// Uses `Option<i128>`: None = +infinity (no constraint).
    pub(super) dbm: Vec<Option<i128>>,
    /// Whether this is bottom (empty set).
    pub(super) is_bottom: bool,
}

impl OctagonDomain {
    /// Create a top (unconstrained) octagon for the given variables.
    #[must_use]
    pub fn new(vars: Vec<String>) -> Self {
        let n = vars.len();
        let dim = 2 * n;
        let mut dbm = vec![None; dim * dim];

        // Diagonal entries are 0
        for i in 0..dim {
            dbm[i * dim + i] = Some(0);
        }

        let var_index: BTreeMap<String, usize> =
            vars.iter().enumerate().map(|(i, v)| (v.clone(), i)).collect();

        Self { vars, var_index, dbm, is_bottom: false }
    }

    /// Create a bottom (empty) octagon.
    #[must_use]
    pub fn new_bottom(vars: Vec<String>) -> Self {
        let mut oct = Self::new(vars);
        oct.is_bottom = true;
        oct
    }

    /// DBM dimension (2 * number of variables).
    fn dim(&self) -> usize {
        2 * self.vars.len()
    }

    /// Get DBM entry at (i, j).
    fn get(&self, i: usize, j: usize) -> Option<i128> {
        self.dbm[i * self.dim() + j]
    }

    /// Add a constraint: `var_i - var_j <= bound`.
    pub fn add_difference_constraint(&mut self, var_i: &str, var_j: &str, bound: i128) {
        if self.is_bottom {
            return;
        }
        if let (Some(&i), Some(&j)) = (self.var_index.get(var_i), self.var_index.get(var_j)) {
            // x_i - x_j <= bound translates to x_i^+ - x_j^+ <= bound
            let ii = 2 * i; // positive form of x_i
            let jj = 2 * j; // positive form of x_j
            self.tighten(ii, jj, bound);
            // Also: x_j^- - x_i^- <= bound (equivalent constraint by negation)
            self.tighten(2 * j + 1, 2 * i + 1, bound);
            self.close();
        }
    }

    /// Add a unary upper bound: `var <= bound`.
    pub fn add_upper_bound(&mut self, var: &str, bound: i128) {
        if self.is_bottom {
            return;
        }
        if let Some(&i) = self.var_index.get(var) {
            // x_i <= bound translates to x_i^+ - x_i^- <= 2*bound
            // (since x_i^+ = x_i and x_i^- = -x_i, so x_i - (-x_i) = 2*x_i <= 2*bound)
            self.tighten(2 * i, 2 * i + 1, 2 * bound);
            self.close();
        }
    }

    /// Add a unary lower bound: `var >= bound`.
    pub fn add_lower_bound(&mut self, var: &str, bound: i128) {
        if self.is_bottom {
            return;
        }
        if let Some(&i) = self.var_index.get(var) {
            // x_i >= bound means -x_i <= -bound
            // x_i^- - x_i^+ <= -2*bound
            self.tighten(2 * i + 1, 2 * i, -2 * bound);
            self.close();
        }
    }

    /// Check if the constraint `var_i - var_j <= bound` holds.
    #[must_use]
    pub fn check_difference(&self, var_i: &str, var_j: &str, bound: i128) -> bool {
        if self.is_bottom {
            return true; // Bottom satisfies everything
        }
        if let (Some(&i), Some(&j)) = (self.var_index.get(var_i), self.var_index.get(var_j)) {
            let ii = 2 * i;
            let jj = 2 * j;
            match self.get(ii, jj) {
                Some(current) => current <= bound,
                None => false, // No constraint, so we cannot prove it
            }
        } else {
            false
        }
    }

    /// Check if `var <= bound`.
    #[must_use]
    pub fn check_upper_bound(&self, var: &str, bound: i128) -> bool {
        if self.is_bottom {
            return true;
        }
        if let Some(&i) = self.var_index.get(var) {
            match self.get(2 * i, 2 * i + 1) {
                Some(current) => {
                    // x_i^+ - x_i^- <= current means 2*x_i <= current means x_i <= current/2
                    // But we need to be careful with rounding: if current is odd, x_i <= floor(current/2)
                    // We check: current <= 2*bound
                    current <= 2 * bound
                }
                None => false,
            }
        } else {
            false
        }
    }

    /// Check if `var >= bound`.
    #[must_use]
    pub fn check_lower_bound(&self, var: &str, bound: i128) -> bool {
        if self.is_bottom {
            return true;
        }
        if let Some(&i) = self.var_index.get(var) {
            match self.get(2 * i + 1, 2 * i) {
                Some(current) => {
                    // x_i^- - x_i^+ <= current means -2*x_i <= current means x_i >= -current/2
                    // Check: current <= -2*bound
                    current <= -2 * bound
                }
                None => false,
            }
        } else {
            false
        }
    }

    /// Tighten a DBM entry: only update if new value is smaller.
    fn tighten(&mut self, i: usize, j: usize, val: i128) {
        let dim = self.dim();
        let idx = i * dim + j;
        self.dbm[idx] = match self.dbm[idx] {
            None => Some(val),
            Some(old) => Some(old.min(val)),
        };
    }

    /// Floyd-Warshall shortest-path closure of the DBM.
    ///
    /// After closure, the DBM is in canonical form and the domain is bottom
    /// iff any diagonal entry is negative.
    pub fn close(&mut self) {
        if self.is_bottom {
            return;
        }
        let dim = self.dim();

        // Standard Floyd-Warshall
        for k in 0..dim {
            for i in 0..dim {
                for j in 0..dim {
                    if let (Some(ik), Some(kj)) = (self.get(i, k), self.get(k, j)) {
                        let new_val = ik.saturating_add(kj);
                        let idx = i * dim + j;
                        self.dbm[idx] = match self.dbm[idx] {
                            None => Some(new_val),
                            Some(old) => Some(old.min(new_val)),
                        };
                    }
                }
            }
        }

        // Tighten using octagonal closure: for each variable pair (i, i_bar),
        // ensure consistency between positive and negative forms.
        for i in 0..dim {
            for j in 0..dim {
                // Octagonal tightening: d[i][j] <= (d[i][i_bar] + d[j_bar][j]) / 2
                let i_bar = i ^ 1;
                let j_bar = j ^ 1;
                if let (Some(i_ibar), Some(jbar_j)) = (self.get(i, i_bar), self.get(j_bar, j)) {
                    let tightened = (i_ibar.saturating_add(jbar_j)) / 2;
                    let idx = i * dim + j;
                    self.dbm[idx] = match self.dbm[idx] {
                        None => Some(tightened),
                        Some(old) => Some(old.min(tightened)),
                    };
                }
            }
        }

        // Check for negative cycles: any negative diagonal entry means bottom
        for i in 0..dim {
            if let Some(d) = self.get(i, i)
                && d < 0
            {
                self.is_bottom = true;
                return;
            }
        }
    }

    /// Extract the interval bound for a variable from the octagon.
    #[must_use]
    pub fn get_interval(&self, var: &str) -> IntervalDomain {
        if self.is_bottom {
            return IntervalDomain::Bottom;
        }
        if let Some(&i) = self.var_index.get(var) {
            // Upper bound: x_i^+ - x_i^- <= d means x_i <= d/2
            let high = self.get(2 * i, 2 * i + 1).map(|d| d / 2);
            // Lower bound: x_i^- - x_i^+ <= d means x_i >= -d/2
            let low = self.get(2 * i + 1, 2 * i).map(|d| -(d / 2));

            let low_bound = match low {
                Some(l) => Bound::Finite(l),
                None => Bound::Unbounded,
            };
            let high_bound = match high {
                Some(h) => Bound::Finite(h),
                None => Bound::Unbounded,
            };
            IntervalDomain::Interval { low: low_bound, high: high_bound }
        } else {
            IntervalDomain::top()
        }
    }
}

impl fmt::Display for OctagonDomain {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_bottom {
            return write!(f, "bottom");
        }
        let dim = self.dim();
        let mut constraints = Vec::new();
        for i in 0..dim {
            for j in 0..dim {
                if i == j {
                    continue;
                }
                if let Some(bound) = self.get(i, j) {
                    let vi = i / 2;
                    let vj = j / 2;
                    let si = if i % 2 == 0 { "+" } else { "-" };
                    let sj = if j % 2 == 0 { "+" } else { "-" };
                    if vi < self.vars.len() && vj < self.vars.len() {
                        constraints.push(format!(
                            "{si}{} - {sj}{} <= {bound}",
                            self.vars[vi], self.vars[vj]
                        ));
                    }
                }
            }
        }
        write!(f, "octagon({})", constraints.join(", "))
    }
}

impl AbstractDomainOps for OctagonDomain {
    fn join(&self, other: &Self) -> Self {
        if self.is_bottom {
            return other.clone();
        }
        if other.is_bottom {
            return self.clone();
        }
        assert_eq!(self.vars, other.vars, "OctagonDomain join requires same variables");
        let dim = self.dim();
        let mut result = Self::new(self.vars.clone());
        for i in 0..dim {
            for j in 0..dim {
                let idx = i * dim + j;
                result.dbm[idx] = match (self.dbm[idx], other.dbm[idx]) {
                    (Some(a), Some(b)) => Some(a.max(b)),
                    _ => None, // If either is unconstrained, join is unconstrained
                };
            }
        }
        result
    }

    fn meet(&self, other: &Self) -> Self {
        if self.is_bottom || other.is_bottom {
            let mut r = Self::new(self.vars.clone());
            r.is_bottom = true;
            return r;
        }
        assert_eq!(self.vars, other.vars, "OctagonDomain meet requires same variables");
        let dim = self.dim();
        let mut result = Self::new(self.vars.clone());
        for i in 0..dim {
            for j in 0..dim {
                let idx = i * dim + j;
                result.dbm[idx] = match (self.dbm[idx], other.dbm[idx]) {
                    (Some(a), Some(b)) => Some(a.min(b)),
                    (Some(a), None) => Some(a),
                    (None, Some(b)) => Some(b),
                    (None, None) => None,
                };
            }
        }
        result.close();
        result
    }

    fn widen(&self, new: &Self) -> Self {
        if self.is_bottom {
            return new.clone();
        }
        if new.is_bottom {
            return self.clone();
        }
        assert_eq!(self.vars, new.vars, "OctagonDomain widen requires same variables");
        let dim = self.dim();
        let mut result = Self::new(self.vars.clone());
        for i in 0..dim {
            for j in 0..dim {
                let idx = i * dim + j;
                result.dbm[idx] = match (self.dbm[idx], new.dbm[idx]) {
                    (Some(a), Some(b)) => {
                        if b <= a {
                            Some(a) // Stable or decreased: keep old
                        } else {
                            None // Increased: widen to unconstrained
                        }
                    }
                    (None, _) => None,       // Already unconstrained
                    (Some(_), None) => None, // New is unconstrained
                };
            }
        }
        result
    }

    fn narrow(&self, new: &Self) -> Self {
        if self.is_bottom {
            return Self::new_bottom(self.vars.clone());
        }
        if new.is_bottom {
            return self.clone();
        }
        assert_eq!(self.vars, new.vars, "OctagonDomain narrow requires same variables");
        let dim = self.dim();
        let mut result = Self::new(self.vars.clone());
        for i in 0..dim {
            for j in 0..dim {
                let idx = i * dim + j;
                result.dbm[idx] = match (self.dbm[idx], new.dbm[idx]) {
                    (None, x) => x, // Was unconstrained: take new bound
                    (x, _) => x,    // Was constrained: keep old
                };
            }
        }
        result
    }

    fn is_bottom(&self) -> bool {
        self.is_bottom
    }

    fn is_top(&self) -> bool {
        if self.is_bottom {
            return false;
        }
        let dim = self.dim();
        for i in 0..dim {
            for j in 0..dim {
                if i == j {
                    continue;
                }
                if self.dbm[i * dim + j].is_some() {
                    return false;
                }
            }
        }
        true
    }

    fn bottom() -> Self {
        Self::new_bottom(Vec::new())
    }

    fn top() -> Self {
        Self::new(Vec::new())
    }

    fn is_subset_of(&self, other: &Self) -> bool {
        if self.is_bottom {
            return true;
        }
        if other.is_bottom {
            return false;
        }
        let dim = self.dim();
        for i in 0..dim {
            for j in 0..dim {
                let idx = i * dim + j;
                match (self.dbm[idx], other.dbm[idx]) {
                    (_, None) => {}                  // Other unconstrained: ok
                    (None, Some(_)) => return false, // We're unconstrained, other isn't
                    (Some(a), Some(b)) => {
                        if a > b {
                            return false;
                        }
                    }
                }
            }
        }
        true
    }
}
