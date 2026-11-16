// trust_vcgen/abstract_interp/domain.rs: IntervalDomain — variable-to-interval mapping
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::cmp::Ordering;
use std::collections::BTreeMap;

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
        // Any key absent from `self.vars` has `a = Interval::TOP`, and
        // `Interval::TOP.widen_with_thresholds(&b, thresholds) == Interval::TOP`.
        let mut vars = BTreeMap::new();
        for (key, a) in &self.vars {
            let b = other.vars.get(key).copied().unwrap_or(Interval::TOP);
            let widened = a.widen_with_thresholds(&b, thresholds);
            if widened != Interval::TOP {
                vars.insert(key.clone(), widened);
            }
        }
        IntervalDomain { vars, is_unreachable: false }
    }

    /// Join `other` into `self` in place without allocating a fresh map.
    pub fn join_in_place(&mut self, other: &Self) {
        let _ = self.join_in_place_changed(other);
    }

    /// Join `other` into `self` in place, returning `true` iff `*self` changed
    /// (exact twin of `let m = self.join(other); let changed = m != *self; *self = m`).
    pub fn join_in_place_changed(&mut self, other: &Self) -> bool {
        if other.is_unreachable {
            return false;
        }
        if self.is_unreachable {
            *self = other.clone();
            return true;
        }
        self.join_reachable_vars_in_place(&other.vars)
    }

    /// Join owned `other` into `self` in place, moving `other` with zero allocations
    /// when `self` is bottom and returning `true` iff `*self` changed.
    pub fn join_owned_in_place(&mut self, other: Self) -> bool {
        if other.is_unreachable {
            return false;
        }
        if self.is_unreachable {
            *self = other;
            return true;
        }
        self.join_reachable_vars_in_place(&other.vars)
    }

    fn join_reachable_vars_in_place(&mut self, other_vars: &BTreeMap<String, Interval>) -> bool {
        if self.vars.is_empty() {
            return false;
        }
        if other_vars.is_empty() {
            self.vars.clear();
            return true;
        }
        // Any key absent from either side has `Interval::TOP` there, and
        // `a.join(&Interval::TOP) == Interval::TOP`. Only keys present in both
        // maps can produce a non-Top joined interval.
        let mut changed = false;
        self.vars.retain(|key, a| {
            if let Some(b) = other_vars.get(key) {
                let joined = a.join(b);
                if joined != Interval::TOP {
                    if *a != joined {
                        *a = joined;
                        changed = true;
                    }
                    return true;
                }
            }
            changed = true;
            false
        });
        changed
    }

    /// Widen `self` with `other` in place, returning `true` iff `*self` changed
    /// (exact twin of `let m = self.widen(other); let changed = m != *self; *self = m`).
    pub fn widen_in_place_changed(&mut self, other: &Self) -> bool {
        if other.is_unreachable {
            return false;
        }
        if self.is_unreachable {
            *self = other.clone();
            return true;
        }
        self.widen_reachable_vars_in_place(&other.vars)
    }

    /// Widen `self` with owned `other` in place, moving `other` when `self` is bottom.
    pub fn widen_owned_in_place(&mut self, other: Self) -> bool {
        if other.is_unreachable {
            return false;
        }
        if self.is_unreachable {
            *self = other;
            return true;
        }
        self.widen_reachable_vars_in_place(&other.vars)
    }

    fn widen_reachable_vars_in_place(&mut self, other_vars: &BTreeMap<String, Interval>) -> bool {
        if self.vars.is_empty() {
            return false;
        }
        if other_vars.is_empty() {
            self.vars.clear();
            return true;
        }
        let mut changed = false;
        self.vars.retain(|key, a| {
            if let Some(b) = other_vars.get(key) {
                let widened = a.widen(b);
                if widened != Interval::TOP {
                    if *a != widened {
                        *a = widened;
                        changed = true;
                    }
                    return true;
                }
            }
            changed = true;
            false
        });
        changed
    }

    /// Widen `self` with `other` using `thresholds` in place, moving `other` when
    /// `self` is bottom and returning `true` iff `*self` changed.
    pub fn widen_with_thresholds_owned_in_place(
        &mut self,
        other: Self,
        thresholds: &ThresholdSet,
    ) -> bool {
        if other.is_unreachable {
            return false;
        }
        if self.is_unreachable {
            *self = other;
            return true;
        }
        if self.vars.is_empty() {
            return false;
        }
        // Note: when `key` is absent from `other.vars`, `b` is `Interval::TOP`, and
        // `a.widen_with_thresholds(&Interval::TOP, thresholds)` steps `a` to the next
        // threshold (not necessarily `Interval::TOP`).
        let mut changed = false;
        self.vars.retain(|key, a| {
            let b = other.vars.get(key).copied().unwrap_or(Interval::TOP);
            let widened = a.widen_with_thresholds(&b, thresholds);
            if widened != Interval::TOP {
                if *a != widened {
                    *a = widened;
                    changed = true;
                }
                true
            } else {
                changed = true;
                false
            }
        });
        changed
    }

    /// Narrow `self` with owned `other` in place, returning `true` iff `*self` changed
    /// (exact twin of `let n = self.narrow(&other); let changed = n != *self; *self = n`).
    pub fn narrow_owned_in_place(&mut self, other: Self) -> bool {
        if self.is_unreachable {
            return false;
        }
        if other.is_unreachable {
            self.vars.clear();
            self.is_unreachable = true;
            return true;
        }
        let mut changed = false;
        let mut hit_bottom = false;
        self.vars.retain(|key, a| {
            if hit_bottom {
                return false;
            }
            let b = other.vars.get(key).copied().unwrap_or(Interval::TOP);
            let narrowed = a.narrow(&b);
            if narrowed.is_bottom() {
                hit_bottom = true;
                return false;
            }
            if narrowed != Interval::TOP {
                if *a != narrowed {
                    *a = narrowed;
                    changed = true;
                }
                true
            } else {
                changed = true;
                false
            }
        });
        if hit_bottom {
            self.vars.clear();
            self.is_unreachable = true;
            return true;
        }
        for (key, b) in other.vars {
            if b.is_bottom() {
                self.vars.clear();
                self.is_unreachable = true;
                return true;
            }
            if b != Interval::TOP && !self.vars.contains_key(&key) {
                self.vars.insert(key, b);
                changed = true;
            }
        }
        changed
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
        // Any key absent from either side has `Interval::TOP` there, and
        // `a.join(&Interval::TOP) == Interval::TOP`. Only keys present in both
        // maps can produce a non-Top joined interval.
        let (smaller, larger) = if self.vars.len() <= other.vars.len() {
            (&self.vars, &other.vars)
        } else {
            (&other.vars, &self.vars)
        };
        if smaller.is_empty() {
            return Self::top();
        }
        let mut vars = BTreeMap::new();
        if smaller.len().saturating_mul(4) < larger.len() {
            for (key, a) in smaller {
                if let Some(b) = larger.get(key) {
                    let joined = a.join(b);
                    if joined != Interval::TOP {
                        vars.insert(key.clone(), joined);
                    }
                }
            }
        } else {
            let mut it_a = self.vars.iter().peekable();
            let mut it_b = other.vars.iter().peekable();
            while let (Some(&(ka, va)), Some(&(kb, vb))) = (it_a.peek(), it_b.peek()) {
                match ka.cmp(kb) {
                    Ordering::Less => {
                        it_a.next();
                    }
                    Ordering::Greater => {
                        it_b.next();
                    }
                    Ordering::Equal => {
                        it_a.next();
                        it_b.next();
                        let joined = va.join(vb);
                        if joined != Interval::TOP {
                            vars.insert(ka.clone(), joined);
                        }
                    }
                }
            }
        }
        IntervalDomain { vars, is_unreachable: false }
    }

    fn meet(&self, other: &Self) -> Self {
        if self.is_unreachable || other.is_unreachable {
            return Self::bottom();
        }
        let mut vars = BTreeMap::new();
        let mut it_a = self.vars.iter().peekable();
        let mut it_b = other.vars.iter().peekable();
        loop {
            let (key, a, b) = match (it_a.peek(), it_b.peek()) {
                (Some(&(ka, va)), Some(&(kb, vb))) => match ka.cmp(kb) {
                    Ordering::Less => {
                        it_a.next();
                        (ka, *va, Interval::TOP)
                    }
                    Ordering::Greater => {
                        it_b.next();
                        (kb, Interval::TOP, *vb)
                    }
                    Ordering::Equal => {
                        it_a.next();
                        it_b.next();
                        (ka, *va, *vb)
                    }
                },
                (Some(&(ka, va)), None) => {
                    it_a.next();
                    (ka, *va, Interval::TOP)
                }
                (None, Some(&(kb, vb))) => {
                    it_b.next();
                    (kb, Interval::TOP, *vb)
                }
                (None, None) => break,
            };
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
        // Any key absent from `self.vars` has `a = Interval::TOP` and any key absent
        // from `other.vars` has `b = Interval::TOP`; in both cases `a.widen(&b) == Interval::TOP`.
        let mut vars = BTreeMap::new();
        for (key, a) in &self.vars {
            if let Some(b) = other.vars.get(key) {
                let widened = a.widen(b);
                if widened != Interval::TOP {
                    vars.insert(key.clone(), widened);
                }
            }
        }
        IntervalDomain { vars, is_unreachable: false }
    }

    fn narrow(&self, other: &Self) -> Self {
        if self.is_unreachable || other.is_unreachable {
            return Self::bottom();
        }
        let mut vars = BTreeMap::new();
        let mut it_a = self.vars.iter().peekable();
        let mut it_b = other.vars.iter().peekable();
        loop {
            let (key, a, b) = match (it_a.peek(), it_b.peek()) {
                (Some(&(ka, va)), Some(&(kb, vb))) => match ka.cmp(kb) {
                    Ordering::Less => {
                        it_a.next();
                        (ka, *va, Interval::TOP)
                    }
                    Ordering::Greater => {
                        it_b.next();
                        (kb, Interval::TOP, *vb)
                    }
                    Ordering::Equal => {
                        it_a.next();
                        it_b.next();
                        (ka, *va, *vb)
                    }
                },
                (Some(&(ka, va)), None) => {
                    it_a.next();
                    (ka, *va, Interval::TOP)
                }
                (None, Some(&(kb, vb))) => {
                    it_b.next();
                    (kb, Interval::TOP, *vb)
                }
                (None, None) => break,
            };
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
