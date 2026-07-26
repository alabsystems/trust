// trust_vcgen/abstract_interp/domain.rs: IntervalDomain — variable-to-interval mapping
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use trust_types::fx::FxHashSet;

use super::{AbstractDomain, Interval, ThresholdSet};

// ── Interval Domain (variable → interval map) ─────────────────────────────

/// Abstract state mapping variable names to intervals.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntervalDomain {
    /// Variable name → interval. Missing = Top.
    pub vars: BTreeMap<String, Interval>,
    /// Whether this state is bottom (unreachable).
    pub is_unreachable: bool,
}

impl IntervalDomain {
    /// Look up a variable's interval, defaulting to Top.
    #[must_use]
    pub fn get(&self, var: &str) -> Interval {
        if self.is_unreachable {
            return Interval::BOTTOM;
        }
        self.vars.get(var).copied().unwrap_or(Interval::TOP)
    }

    /// Set a variable's interval.
    pub fn set(&mut self, var: String, interval: Interval) {
        if !self.is_unreachable {
            self.vars.insert(var, interval);
        }
    }

    /// Widen with thresholds, variable-by-variable.
    #[must_use]
    pub fn widen_with_thresholds(&self, other: &Self, thresholds: &ThresholdSet) -> Self {
        if self.is_unreachable {
            return other.clone();
        }
        if other.is_unreachable {
            return self.clone();
        }
        let all_keys: FxHashSet<&String> = self.vars.keys().chain(other.vars.keys()).collect();
        let mut vars = BTreeMap::new();
        for key in all_keys {
            let a = self.get(key);
            let b = other.get(key);
            let widened = a.widen_with_thresholds(&b, thresholds);
            if widened != Interval::TOP {
                vars.insert(key.clone(), widened);
            }
        }
        IntervalDomain { vars, is_unreachable: false }
    }
}

impl AbstractDomain for IntervalDomain {
    fn top() -> Self {
        IntervalDomain { vars: BTreeMap::new(), is_unreachable: false }
    }

    fn bottom() -> Self {
        IntervalDomain { vars: BTreeMap::new(), is_unreachable: true }
    }

    fn join(&self, other: &Self) -> Self {
        if self.is_unreachable {
            return other.clone();
        }
        if other.is_unreachable {
            return self.clone();
        }
        let all_keys: FxHashSet<&String> = self.vars.keys().chain(other.vars.keys()).collect();
        let mut vars = BTreeMap::new();
        for key in all_keys {
            let a = self.get(key);
            let b = other.get(key);
            let joined = a.join(&b);
            // Only store non-Top intervals (Top is the default).
            if joined != Interval::TOP {
                vars.insert(key.clone(), joined);
            }
        }
        IntervalDomain { vars, is_unreachable: false }
    }

    fn meet(&self, other: &Self) -> Self {
        if self.is_unreachable || other.is_unreachable {
            return Self::bottom();
        }
        let all_keys: FxHashSet<&String> = self.vars.keys().chain(other.vars.keys()).collect();
        let mut vars = BTreeMap::new();
        for key in all_keys {
            let a = self.get(key);
            let b = other.get(key);
            let met = a.meet(&b);
            if met.is_bottom() {
                return Self::bottom();
            }
            if met != Interval::TOP {
                vars.insert(key.clone(), met);
            }
        }
        IntervalDomain { vars, is_unreachable: false }
    }

    fn widen(&self, other: &Self) -> Self {
        if self.is_unreachable {
            return other.clone();
        }
        if other.is_unreachable {
            return self.clone();
        }
        let all_keys: FxHashSet<&String> = self.vars.keys().chain(other.vars.keys()).collect();
        let mut vars = BTreeMap::new();
        for key in all_keys {
            let a = self.get(key);
            let b = other.get(key);
            let widened = a.widen(&b);
            if widened != Interval::TOP {
                vars.insert(key.clone(), widened);
            }
        }
        IntervalDomain { vars, is_unreachable: false }
    }

    fn narrow(&self, other: &Self) -> Self {
        if self.is_unreachable || other.is_unreachable {
            return Self::bottom();
        }
        let all_keys: FxHashSet<&String> = self.vars.keys().chain(other.vars.keys()).collect();
        let mut vars = BTreeMap::new();
        for key in all_keys {
            let a = self.get(key);
            let b = other.get(key);
            let narrowed = a.narrow(&b);
            if narrowed.is_bottom() {
                return Self::bottom();
            }
            if narrowed != Interval::TOP {
                vars.insert(key.clone(), narrowed);
            }
        }
        IntervalDomain { vars, is_unreachable: false }
    }

    fn is_bottom(&self) -> bool {
        self.is_unreachable
    }

    fn leq(&self, other: &Self) -> bool {
        if self.is_unreachable {
            return true;
        }
        if other.is_unreachable {
            return false;
        }
        // For all vars in self, self[v] <= other[v].
        for (key, interval) in &self.vars {
            if !interval.leq(&other.get(key)) {
                return false;
            }
        }
        true
    }
}
