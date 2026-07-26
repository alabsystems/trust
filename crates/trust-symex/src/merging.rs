// trust-symex path merging
//
// Merge similar symbolic execution paths to mitigate state explosion.
// Inspired by KLEE's state merging (refs/klee/lib/Core/Executor.cpp)
// and Veritesting's dynamic merge points.
//
// Two states are merge-candidates when they share the same PC (next block)
// and differ only in a bounded number of variable bindings. Merging replaces
// divergent bindings with Ite (if-then-else) expressions conditioned on the
// differing path constraints.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use trust_types::Formula;

use crate::engine::ExecutionFork;
use crate::path::{PathConstraint, symbolic_to_formula};
use crate::state::{SymbolicState, SymbolicValue};

/// Policy controlling when two states should be merged.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum MergePolicy {
    /// Never merge states (safest, no approximation).
    Never,
    /// Always merge when structurally possible (most aggressive).
    Always,
    /// Merge only when the number of differing variables is at most `threshold`.
    Heuristic { threshold: usize },
}

impl Default for MergePolicy {
    fn default() -> Self {
        Self::Heuristic { threshold: 8 }
    }
}

/// Determines whether two states can be merged under the given policy.
///
/// Requirements for mergeability:
/// - They must target the same next block (caller responsibility).
/// - Under `Heuristic`, the number of differing bindings must be <= threshold.
/// - Under `Never`, always returns `false`.
/// - Under `Always`, always returns `true` if variable sets overlap.
#[must_use]
pub fn can_merge(a: &SymbolicState, b: &SymbolicState, policy: MergePolicy) -> bool {
    match policy {
        MergePolicy::Never => false,
        MergePolicy::Always => true,
        MergePolicy::Heuristic { threshold } => {
            let diff_count = count_differing_vars(a, b);
            diff_count <= threshold
        }
    }
}

/// Merge two symbolic states, producing a new state where each differing
/// variable binding becomes an `Ite` conditioned on a fresh merge guard.
///
/// The merge guard is a fresh symbolic variable `merge_guard_N` which is
/// true for state `a`'s path and false for state `b`'s path. The caller
/// is responsible for constraining the guard in the merged path.
///
/// Uses phi-node semantics for missing variables: if a variable is present
/// in one branch but not the other, the missing side gets the pre-branch
/// value (if available via `pre_branch`). Variables introduced mid-branch
/// (not present pre-branch) get a fresh unconstrained symbolic variable.
#[must_use]
pub fn merge_states(a: &SymbolicState, b: &SymbolicState, merge_id: usize) -> SymbolicState {
    merge_states_with_pre_branch(a, b, None, merge_id)
}

/// Like `merge_states`, but accepts an optional pre-branch state for
/// phi-node semantics. When a variable is missing from one side:
/// - If `pre_branch` contains it, the pre-branch value is used.
/// - Otherwise, a fresh unconstrained symbolic variable is generated.
#[must_use]
pub fn merge_states_with_pre_branch(
    a: &SymbolicState,
    b: &SymbolicState,
    pre_branch: Option<&SymbolicState>,
    merge_id: usize,
) -> SymbolicState {
    let guard = SymbolicValue::Symbol(format!("merge_guard_{merge_id}"));

    let mut merged = SymbolicState::new();

    // Collect all variable names from both states.
    let all_vars: BTreeSet<String> =
        a.iter().map(|(k, _)| k.to_owned()).chain(b.iter().map(|(k, _)| k.to_owned())).collect();

    // Counter for generating unique fresh symbolic variables within this merge.
    let mut fresh_counter: usize = 0;

    for var in all_vars {
        // Compute the effective values using phi-node semantics for missing vars.
        let eff_a = match a.try_get(&var) {
            Some(v) => v.clone(),
            None => phi_default(pre_branch, &var, merge_id, &mut fresh_counter),
        };
        let eff_b = match b.try_get(&var) {
            Some(v) => v.clone(),
            None => phi_default(pre_branch, &var, merge_id, &mut fresh_counter),
        };

        if eff_a == eff_b {
            // Same value: no Ite needed.
            merged.set(var, eff_a);
        } else {
            // Divergent: merge with Ite(guard, a_val, b_val).
            merged.set(var, SymbolicValue::ite(guard.clone(), eff_a, eff_b));
        }
    }

    merged
}

/// Compute the phi-node default for a variable missing from one branch.
///
/// If `pre_branch` contains the variable, return that value (the variable
/// was not modified by this branch). Otherwise, return a fresh unconstrained
/// symbolic variable (the variable was introduced mid-branch on the other
/// side and has no prior definition).
fn phi_default(
    pre_branch: Option<&SymbolicState>,
    var: &str,
    merge_id: usize,
    fresh_counter: &mut usize,
) -> SymbolicValue {
    if let Some(pre) = pre_branch
        && let Some(val) = pre.try_get(var)
    {
        return val.clone();
    }
    // Fresh unconstrained symbolic variable for a variable introduced mid-branch.
    let id = *fresh_counter;
    *fresh_counter += 1;
    SymbolicValue::Symbol(format!("fresh_{var}_merge{merge_id}_{id}"))
}

/// Merge two paths, producing a combined path where the merge guard
/// distinguishes which original path was taken.
///
/// The merged path preserves:
/// 1. Common prefix constraints (shared branch decisions).
/// 2. Divergent constraints as an auxiliary formula:
///    `(guard AND a_divergent) OR (NOT guard AND b_divergent)`
///
/// This prevents the over-approximation where divergent constraints
/// are silently dropped, which would cause false alarms in CEGAR.
// Trust: #771 — preserve divergent path constraints at merge points
#[must_use]
pub fn merge_paths(a: &PathConstraint, b: &PathConstraint, merge_id: usize) -> PathConstraint {
    let guard = SymbolicValue::Symbol(format!("merge_guard_{merge_id}"));
    let guard_formula = symbolic_to_formula(&guard);

    let mut merged = PathConstraint::new();

    // Copy constraints shared by both paths (common prefix).
    let a_decisions = a.decisions();
    let b_decisions = b.decisions();
    let prefix_len = common_prefix_len(a_decisions, b_decisions);

    for d in &a_decisions[..prefix_len] {
        merged.add_constraint(d.condition.clone(), d.taken);
    }

    // The merge guard itself is added as a branch decision.
    merged.add_constraint(guard, true);

    // Build the divergent constraint formulas for each path.
    let a_divergent = decisions_to_conjunction(&a_decisions[prefix_len..]);
    let b_divergent = decisions_to_conjunction(&b_decisions[prefix_len..]);

    // Also include auxiliary formulas from each path.
    let a_aux = auxiliary_conjunction(a.auxiliary());
    let b_aux = auxiliary_conjunction(b.auxiliary());

    let a_full = conjoin_optional(a_divergent, a_aux);
    let b_full = conjoin_optional(b_divergent, b_aux);

    // If either path has divergent constraints, encode the disjunction:
    // (guard AND a_constraints) OR (NOT guard AND b_constraints)
    if let Some(disjunction) = merge_disjunction(&guard_formula, a_full, b_full) {
        merged.add_auxiliary(disjunction);
    }

    merged
}

/// Convert a slice of branch decisions into a conjunction formula.
/// Returns `None` if the slice is empty (no constraints to add).
fn decisions_to_conjunction(decisions: &[crate::path::BranchDecision]) -> Option<Formula> {
    if decisions.is_empty() {
        return None;
    }
    let clauses: Vec<Formula> = decisions
        .iter()
        .map(|d| {
            let f = symbolic_to_formula(&d.condition);
            if d.taken { f } else { Formula::Not(Box::new(f)) }
        })
        .collect();
    if clauses.len() == 1 {
        Some(clauses.into_iter().next().expect("len == 1"))
    } else {
        Some(Formula::And(clauses))
    }
}

/// Convert a slice of auxiliary formulas into a conjunction.
fn auxiliary_conjunction(aux: &[Formula]) -> Option<Formula> {
    if aux.is_empty() {
        return None;
    }
    if aux.len() == 1 {
        return Some(aux[0].clone());
    }
    Some(Formula::And(aux.to_vec()))
}

/// Conjoin two optional formulas.
fn conjoin_optional(a: Option<Formula>, b: Option<Formula>) -> Option<Formula> {
    match (a, b) {
        (Some(x), Some(y)) => Some(Formula::And(vec![x, y])),
        (Some(x), None) | (None, Some(x)) => Some(x),
        (None, None) => None,
    }
}

/// Build the merge disjunction: `(guard AND a) OR (NOT guard AND b)`.
/// Returns `None` if both sides are empty (nothing divergent to encode).
///
/// For the asymmetric case (one side has constraints, the other does not):
/// - Only A has constraints: `guard => a_constraints` (a_constraints hold when
///   guard is true; no extra constraints when guard is false).
/// - Only B has constraints: `NOT guard => b_constraints`.
///
/// The implication form is essential: using bare `And(guard, a)` would make
/// the auxiliary unsatisfiable when guard is false, incorrectly killing the
/// merged path.
fn merge_disjunction(
    guard: &Formula,
    a_constraints: Option<Formula>,
    b_constraints: Option<Formula>,
) -> Option<Formula> {
    let not_guard = Formula::Not(Box::new(guard.clone()));
    match (a_constraints, b_constraints) {
        (Some(a), Some(b)) => {
            // Both paths have divergent constraints:
            // (guard AND a) OR (NOT guard AND b)
            let a_arm = Formula::And(vec![guard.clone(), a]);
            let b_arm = Formula::And(vec![not_guard, b]);
            Some(Formula::Or(vec![a_arm, b_arm]))
        }
        (Some(a), None) => {
            // Only path A has divergent constraints. When guard is true,
            // A's constraints hold; when guard is false, no extra constraints.
            // guard => a_constraints
            Some(Formula::Implies(Box::new(guard.clone()), Box::new(a)))
        }
        (None, Some(b)) => {
            // Only path B has divergent constraints.
            // NOT guard => b_constraints
            Some(Formula::Implies(Box::new(not_guard), Box::new(b)))
        }
        (None, None) => None,
    }
}

/// Count the number of branch decisions that form a common prefix.
fn common_prefix_len(
    a: &[crate::path::BranchDecision],
    b: &[crate::path::BranchDecision],
) -> usize {
    a.iter()
        .zip(b.iter())
        .take_while(|(da, db)| da.taken == db.taken && da.condition == db.condition)
        .count()
}

/// Count how many variables have different values between two states.
///
/// A variable present in one state but absent from the other is always
/// counted as differing (phi-node semantics: absent != present). The old
/// code used `Concrete(0)` as a default for missing variables, which
/// incorrectly treated absent variables as equal to 0-valued ones.
fn count_differing_vars(a: &SymbolicState, b: &SymbolicState) -> usize {
    let all_vars: BTreeSet<String> =
        a.iter().map(|(k, _)| k.to_owned()).chain(b.iter().map(|(k, _)| k.to_owned())).collect();

    all_vars
        .iter()
        .filter(|var| {
            // If a variable is missing from one side, it is always "different"
            // — using Concrete(0) as default would mask real divergence.
            match (a.try_get(var), b.try_get(var)) {
                (Some(va), Some(vb)) => va != vb,
                _ => true, // present in one, absent in other => differing
            }
        })
        .count()
}

/// A stateful path merger that tracks merge IDs and applies a policy.
#[derive(Debug, Clone)]
pub struct PathMerger {
    policy: MergePolicy,
    next_merge_id: usize,
    /// Total number of merges performed.
    merge_count: usize,
}

impl PathMerger {
    /// Create a new `PathMerger` with the given policy.
    #[must_use]
    pub fn new(policy: MergePolicy) -> Self {
        Self { policy, next_merge_id: 0, merge_count: 0 }
    }

    /// Try to merge two states. Returns `Some(merged)` if the policy allows
    /// merging and the states are compatible; `None` otherwise.
    #[must_use]
    pub fn try_merge(&mut self, a: &SymbolicState, b: &SymbolicState) -> Option<SymbolicState> {
        if !can_merge(a, b, self.policy) {
            return None;
        }
        let id = self.next_merge_id;
        self.next_merge_id += 1;
        self.merge_count += 1;
        Some(merge_states(a, b, id))
    }

    /// Returns the current merge policy.
    #[must_use]
    pub fn policy(&self) -> MergePolicy {
        self.policy
    }

    /// Returns the number of merges performed.
    #[must_use]
    pub fn merge_count(&self) -> usize {
        self.merge_count
    }
}

// ---------------------------------------------------------------------------
// StateMerger trait + implementations
// ---------------------------------------------------------------------------

/// Result of merging two symbolic states.
#[derive(Debug, Clone)]
pub struct MergedState {
    /// The merged symbolic state.
    pub state: SymbolicState,
    /// The merged path constraint.
    pub path: PathConstraint,
    /// Identifier for this merge operation.
    pub merge_id: usize,
}

/// Trait for merging two symbolic states at a join point.
///
/// Different implementations encode different precision/performance tradeoffs:
/// - `IteMerger` (default, via `merge_states`) preserves full precision using
///   if-then-else expressions.
/// - `WideningMerger` over-approximates using interval widening for faster
///   convergence at loop heads.
pub trait StateMerger {
    /// Merge two symbolic states, returning the combined result.
    ///
    /// `merge_id` is a unique identifier for this merge point, used to
    /// generate fresh guard variables. `pre_branch` is the state before
    /// the branch point; used for phi-node semantics on missing variables.
    fn merge(
        &self,
        a: &SymbolicState,
        a_path: &PathConstraint,
        b: &SymbolicState,
        b_path: &PathConstraint,
        pre_branch: Option<&SymbolicState>,
        merge_id: usize,
    ) -> MergedState;
}

/// Ite-based merger: the default strategy that preserves full precision
/// by creating if-then-else expressions for divergent variables.
#[derive(Debug, Clone, Copy, Default)]
pub struct IteMerger;

impl StateMerger for IteMerger {
    fn merge(
        &self,
        a: &SymbolicState,
        a_path: &PathConstraint,
        b: &SymbolicState,
        b_path: &PathConstraint,
        pre_branch: Option<&SymbolicState>,
        merge_id: usize,
    ) -> MergedState {
        MergedState {
            state: merge_states_with_pre_branch(a, b, pre_branch, merge_id),
            path: merge_paths(a_path, b_path, merge_id),
            merge_id,
        }
    }
}

/// An abstract interval for widening: `[lo, hi]` (inclusive).
///
/// Used by `WideningMerger` to over-approximate the join of two concrete
/// value ranges. For example, `[0, 5]` join `[3, 8]` yields `[0, 8]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Interval {
    pub lo: i128,
    pub hi: i128,
}

impl Interval {
    /// Create an interval from a single concrete value.
    #[must_use]
    pub fn point(v: i128) -> Self {
        Self { lo: v, hi: v }
    }

    /// Join two intervals: the smallest interval containing both.
    #[must_use]
    pub fn join(self, other: Self) -> Self {
        Self { lo: self.lo.min(other.lo), hi: self.hi.max(other.hi) }
    }

    /// Widen: if the other interval extends beyond self, push to extremes.
    ///
    /// This is the standard widening operator from abstract interpretation:
    /// - If `other.lo < self.lo`, widen `lo` to `i128::MIN`.
    /// - If `other.hi > self.hi`, widen `hi` to `i128::MAX`.
    #[must_use]
    pub fn widen(self, other: Self) -> Self {
        Self {
            lo: if other.lo < self.lo { i128::MIN } else { self.lo },
            hi: if other.hi > self.hi { i128::MAX } else { self.hi },
        }
    }

    /// Returns `true` if this is a single point (lo == hi).
    #[must_use]
    pub fn is_point(&self) -> bool {
        self.lo == self.hi
    }
}

/// Extract a concrete interval from a symbolic value if possible.
fn value_to_interval(val: &SymbolicValue) -> Option<Interval> {
    match val {
        SymbolicValue::Concrete(n) => Some(Interval::point(*n)),
        _ => None,
    }
}

/// Widening-based merger: over-approximates by joining concrete values
/// into intervals and representing them as constrained fresh symbols.
///
/// When both values are concrete, the interval join `[min(a,b), max(a,b)]`
/// is computed. Non-concrete values fall back to Ite merge.
///
/// This is sound (over-approximate) but imprecise. It converges faster at
/// loop heads because repeated widening eventually stabilises.
#[derive(Debug, Clone, Copy, Default)]
pub struct WideningMerger;

impl WideningMerger {
    /// Create the symbolic representation of a widened interval.
    ///
    /// For a point interval, returns the concrete value. For a range,
    /// returns an Ite that captures the interval semantics.
    fn interval_to_symbolic(interval: Interval, var_name: &str) -> SymbolicValue {
        if interval.is_point() {
            return SymbolicValue::Concrete(interval.lo);
        }
        // Represent as: Ite(lo <= var && var <= hi, var, lo)
        // This captures that the variable is somewhere in [lo, hi].
        let widened_sym = SymbolicValue::Symbol(format!("widened_{var_name}"));
        let lo_check = SymbolicValue::bin_op(
            SymbolicValue::Concrete(interval.lo),
            trust_types::BinOp::Le,
            widened_sym.clone(),
        );
        let hi_check = SymbolicValue::bin_op(
            widened_sym.clone(),
            trust_types::BinOp::Le,
            SymbolicValue::Concrete(interval.hi),
        );
        // TODO: Use a logical conjunction once `trust_types::BinOp::And`
        // exists; `BitAnd` is the closest available operator today.
        let in_range = SymbolicValue::bin_op(lo_check, trust_types::BinOp::BitAnd, hi_check);
        SymbolicValue::ite(in_range, widened_sym, SymbolicValue::Concrete(interval.lo))
    }
}

impl StateMerger for WideningMerger {
    fn merge(
        &self,
        a: &SymbolicState,
        a_path: &PathConstraint,
        b: &SymbolicState,
        b_path: &PathConstraint,
        pre_branch: Option<&SymbolicState>,
        merge_id: usize,
    ) -> MergedState {
        let all_vars: BTreeSet<String> = a
            .iter()
            .map(|(k, _)| k.to_owned())
            .chain(b.iter().map(|(k, _)| k.to_owned()))
            .collect();

        let mut merged = SymbolicState::new();
        let mut fresh_counter: usize = 0;

        for var in &all_vars {
            // Phi-node semantics for missing variables.
            let eff_a = match a.try_get(var) {
                Some(v) => v.clone(),
                None => phi_default(pre_branch, var, merge_id, &mut fresh_counter),
            };
            let eff_b = match b.try_get(var) {
                Some(v) => v.clone(),
                None => phi_default(pre_branch, var, merge_id, &mut fresh_counter),
            };

            if eff_a == eff_b {
                merged.set(var.clone(), eff_a);
                continue;
            }

            // Try interval widening for concrete values.
            match (value_to_interval(&eff_a), value_to_interval(&eff_b)) {
                (Some(ia), Some(ib)) => {
                    let joined = ia.join(ib);
                    merged.set(var.clone(), Self::interval_to_symbolic(joined, var));
                }
                _ => {
                    // Fall back to Ite merge for non-concrete values.
                    let guard = SymbolicValue::Symbol(format!("merge_guard_{merge_id}"));
                    merged.set(var.clone(), SymbolicValue::ite(guard, eff_a, eff_b));
                }
            }
        }

        MergedState { state: merged, path: merge_paths(a_path, b_path, merge_id), merge_id }
    }
}

// ---------------------------------------------------------------------------
// MergeStrategy
// ---------------------------------------------------------------------------

/// Strategy controlling when path merging is applied during exploration.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum MergeStrategy {
    /// Never merge paths (baseline: full path enumeration).
    NoMerge,
    /// Eagerly merge at every join point where two states target the same block.
    EagerMerge,
    /// Merge only when the number of active paths exceeds `threshold`.
    SelectiveMerge { threshold: usize },
}

impl Default for MergeStrategy {
    fn default() -> Self {
        Self::SelectiveMerge { threshold: 16 }
    }
}

// ---------------------------------------------------------------------------
// Split detection
// ---------------------------------------------------------------------------

/// Result of splitting a symbolic state at a branch point.
#[derive(Debug, Clone)]
pub struct SplitResult {
    /// The state for the true branch, with the branch condition asserted.
    pub true_state: ExecutionFork,
    /// The state for the false branch, with the negated condition asserted.
    pub false_state: ExecutionFork,
    /// The branch condition that caused the split.
    pub condition: SymbolicValue,
}

/// Detects and records state splits at branch points.
///
/// When symbolic execution encounters a branch condition, the state space
/// is partitioned into two disjoint subsets. `StateSplitter` creates the
/// two resulting states with appropriate path constraints.
#[derive(Debug, Clone, Default)]
pub struct StateSplitter {
    /// Number of splits performed.
    split_count: usize,
}

impl StateSplitter {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Split a state at a branch condition, producing two forks.
    ///
    /// The `true_block` fork has the condition asserted true.
    /// The `false_block` fork has the condition asserted false (negated).
    pub fn split(
        &mut self,
        state: &SymbolicState,
        path: &PathConstraint,
        condition: SymbolicValue,
        true_block: usize,
        false_block: usize,
    ) -> SplitResult {
        self.split_count += 1;

        let mut true_path = path.clone();
        true_path.add_constraint(condition.clone(), true);

        let mut false_path = path.clone();
        false_path.add_constraint(condition.clone(), false);

        SplitResult {
            true_state: ExecutionFork {
                state: state.clone(),
                path: true_path,
                next_block: true_block,
            },
            false_state: ExecutionFork {
                state: state.clone(),
                path: false_path,
                next_block: false_block,
            },
            condition,
        }
    }

    /// Returns the number of splits performed.
    #[must_use]
    pub fn split_count(&self) -> usize {
        self.split_count
    }
}

// ---------------------------------------------------------------------------
// MergingExplorer: wires merge points into path exploration
// ---------------------------------------------------------------------------

/// A path explorer that integrates state merging at basic block join points.
///
/// Wraps a collection of pending `ExecutionFork`s and applies the configured
/// `MergeStrategy` to reduce the number of active paths. At each step,
/// forks targeting the same block are merge candidates.
#[derive(Debug)]
pub struct MergingExplorer {
    /// Pending forks waiting to be explored.
    pending: Vec<ExecutionFork>,
    /// Merge strategy controlling when to merge.
    strategy: MergeStrategy,
    /// The state merger implementation.
    merger: PathMerger,
    /// Splitter for recording branch splits.
    splitter: StateSplitter,
    /// Total number of merges applied during exploration.
    merges_applied: usize,
}

impl MergingExplorer {
    /// Create a new merging explorer with the given strategy and merge policy.
    #[must_use]
    pub fn new(strategy: MergeStrategy, policy: MergePolicy) -> Self {
        Self {
            pending: Vec::new(),
            strategy,
            merger: PathMerger::new(policy),
            splitter: StateSplitter::new(),
            merges_applied: 0,
        }
    }

    /// Add execution forks to the pending set.
    pub fn add_forks(&mut self, forks: Vec<ExecutionFork>) {
        self.pending.extend(forks);
        self.maybe_merge();
    }

    /// Split a state at a branch and add both forks to pending.
    pub fn split_and_add(
        &mut self,
        state: &SymbolicState,
        path: &PathConstraint,
        condition: SymbolicValue,
        true_block: usize,
        false_block: usize,
    ) -> SplitResult {
        let result = self.splitter.split(state, path, condition, true_block, false_block);
        self.pending.push(result.true_state.clone());
        self.pending.push(result.false_state.clone());
        self.maybe_merge();
        result
    }

    /// Take the next fork to explore, if any.
    #[must_use]
    pub fn next_fork(&mut self) -> Option<ExecutionFork> {
        self.pending.pop()
    }

    /// Returns the number of currently pending forks.
    #[must_use]
    pub fn pending_count(&self) -> usize {
        self.pending.len()
    }

    /// Returns the number of merges applied during exploration.
    #[must_use]
    pub fn merges_applied(&self) -> usize {
        self.merges_applied
    }

    /// Returns the number of splits performed.
    #[must_use]
    pub fn splits_performed(&self) -> usize {
        self.splitter.split_count()
    }

    /// Apply merge strategy if conditions are met.
    fn maybe_merge(&mut self) {
        let should_merge = match self.strategy {
            MergeStrategy::NoMerge => false,
            MergeStrategy::EagerMerge => true,
            MergeStrategy::SelectiveMerge { threshold } => self.pending.len() > threshold,
        };

        if !should_merge {
            return;
        }

        self.merge_pending();
    }

    /// Merge pending forks that target the same basic block.
    fn merge_pending(&mut self) {
        // Group forks by target block.
        let mut by_block: BTreeMap<usize, Vec<ExecutionFork>> = BTreeMap::default();
        for fork in self.pending.drain(..) {
            by_block.entry(fork.next_block).or_default().push(fork);
        }

        let mut result = Vec::new();
        for (_block, mut forks) in by_block {
            // Pairwise merge within each group.
            while forks.len() > 1 {
                // SAFETY: while loop condition guarantees forks.len() > 1.
                let b = forks.pop().unwrap_or_else(|| unreachable!("forks empty despite len > 1"));
                let a = forks
                    .last()
                    .unwrap_or_else(|| unreachable!("forks empty after pop with len > 1"));

                if let Some(merged_state) = self.merger.try_merge(&a.state, &b.state) {
                    let merged_path = merge_paths(&a.path, &b.path, self.merger.merge_count());
                    let merged_fork = ExecutionFork {
                        state: merged_state,
                        path: merged_path,
                        next_block: a.next_block,
                    };
                    forks.pop(); // remove `a`
                    forks.push(merged_fork);
                    self.merges_applied += 1;
                } else {
                    // Cannot merge: keep b separately.
                    result.push(b);
                }
            }
            result.extend(forks);
        }

        self.pending = result;
    }
}

#[cfg(test)]
mod tests {
    use trust_types::BinOp;

    use super::*;

    // --- can_merge ---

    #[test]
    fn test_merge_never_policy() {
        let a = SymbolicState::new();
        let b = SymbolicState::new();
        assert!(!can_merge(&a, &b, MergePolicy::Never));
    }

    #[test]
    fn test_merge_always_policy() {
        let a = SymbolicState::new();
        let b = SymbolicState::new();
        assert!(can_merge(&a, &b, MergePolicy::Always));
    }

    #[test]
    fn test_merge_heuristic_within_threshold() {
        let mut a = SymbolicState::new();
        let mut b = SymbolicState::new();
        a.set("x", SymbolicValue::Concrete(1));
        b.set("x", SymbolicValue::Concrete(2));
        // 1 differing var, threshold 8: should merge.
        assert!(can_merge(&a, &b, MergePolicy::Heuristic { threshold: 8 }));
    }

    #[test]
    fn test_merge_heuristic_exceeds_threshold() {
        let mut a = SymbolicState::new();
        let mut b = SymbolicState::new();
        for i in 0..5 {
            a.set(format!("v{i}"), SymbolicValue::Concrete(i as i128));
            b.set(format!("v{i}"), SymbolicValue::Concrete((i + 10) as i128));
        }
        // 5 differing vars, threshold 3: should not merge.
        assert!(!can_merge(&a, &b, MergePolicy::Heuristic { threshold: 3 }));
    }

    // --- merge_states ---

    #[test]
    fn test_merge_states_identical() {
        let mut a = SymbolicState::new();
        a.set("x", SymbolicValue::Concrete(42));
        let b = a.clone();
        let merged = merge_states(&a, &b, 0);
        // Identical values should be preserved as-is (no Ite).
        assert_eq!(merged.get("x").unwrap(), &SymbolicValue::Concrete(42));
    }

    #[test]
    fn test_merge_states_divergent() {
        let mut a = SymbolicState::new();
        let mut b = SymbolicState::new();
        a.set("x", SymbolicValue::Concrete(1));
        b.set("x", SymbolicValue::Concrete(2));
        let merged = merge_states(&a, &b, 0);
        let val = merged.get("x").unwrap();
        match val {
            SymbolicValue::Ite(guard, then_val, else_val) => {
                assert_eq!(**guard, SymbolicValue::Symbol("merge_guard_0".into()));
                assert_eq!(**then_val, SymbolicValue::Concrete(1));
                assert_eq!(**else_val, SymbolicValue::Concrete(2));
            }
            other => panic!("expected Ite, got {other:?}"),
        }
    }

    #[test]
    fn test_merge_states_asymmetric_vars_no_pre_branch() {
        // Without pre_branch, missing variables get a fresh symbolic variable.
        let mut a = SymbolicState::new();
        let b = SymbolicState::new();
        a.set("only_in_a", SymbolicValue::Concrete(99));
        let merged = merge_states(&a, &b, 1);
        // Variable only in a: should become Ite(guard, 99, fresh_symbol).
        let val = merged.get("only_in_a").unwrap();
        match val {
            SymbolicValue::Ite(_, then_val, else_val) => {
                assert_eq!(**then_val, SymbolicValue::Concrete(99));
                // The else branch is a fresh symbolic variable, not Concrete(0).
                match else_val.as_ref() {
                    SymbolicValue::Symbol(name) => {
                        assert!(
                            name.starts_with("fresh_only_in_a_merge1_"),
                            "expected fresh symbol, got {name}"
                        );
                    }
                    other => panic!("expected fresh Symbol, got {other:?}"),
                }
            }
            other => panic!("expected Ite, got {other:?}"),
        }
    }

    #[test]
    fn test_merge_states_asymmetric_with_pre_branch_propagates() {
        // Pre-branch has the variable: missing side should get pre-branch value.
        let mut pre = SymbolicState::new();
        pre.set("x", SymbolicValue::Concrete(42));

        let mut a = SymbolicState::new();
        a.set("x", SymbolicValue::Concrete(99)); // Modified on branch a
        let b = SymbolicState::new(); // x not modified on branch b

        let merged = merge_states_with_pre_branch(&a, &b, Some(&pre), 0);
        let val = merged.get("x").unwrap();
        match val {
            SymbolicValue::Ite(guard, then_val, else_val) => {
                assert_eq!(**guard, SymbolicValue::Symbol("merge_guard_0".into()));
                assert_eq!(**then_val, SymbolicValue::Concrete(99)); // branch a's value
                assert_eq!(**else_val, SymbolicValue::Concrete(42)); // pre-branch value
            }
            other => panic!("expected Ite, got {other:?}"),
        }
    }

    #[test]
    fn test_merge_states_asymmetric_with_pre_branch_unmodified_same() {
        // When neither branch modifies a pre-branch variable, it should be
        // preserved directly (no Ite).
        let mut pre = SymbolicState::new();
        pre.set("x", SymbolicValue::Concrete(42));

        // Neither a nor b has "x" — both inherit from pre_branch.
        let a = SymbolicState::new();
        let b = SymbolicState::new();

        let merged = merge_states_with_pre_branch(&a, &b, Some(&pre), 0);
        // "x" is not in merged because neither a nor b had it in their var set.
        // The all_vars union is empty, so nothing to merge.
        assert!(merged.is_empty());
    }

    #[test]
    fn test_merge_states_introduced_mid_branch_with_pre_branch() {
        // Variable introduced in branch a that does NOT exist in pre_branch.
        // The missing side (b) should get a fresh symbolic variable.
        let pre = SymbolicState::new(); // "new_var" not in pre

        let mut a = SymbolicState::new();
        a.set("new_var", SymbolicValue::Concrete(77));
        let b = SymbolicState::new();

        let merged = merge_states_with_pre_branch(&a, &b, Some(&pre), 0);
        let val = merged.get("new_var").unwrap();
        match val {
            SymbolicValue::Ite(_, then_val, else_val) => {
                assert_eq!(**then_val, SymbolicValue::Concrete(77));
                match else_val.as_ref() {
                    SymbolicValue::Symbol(name) => {
                        assert!(
                            name.starts_with("fresh_new_var_merge0_"),
                            "expected fresh symbol, got {name}"
                        );
                    }
                    other => panic!("expected fresh Symbol for mid-branch var, got {other:?}"),
                }
            }
            other => panic!("expected Ite, got {other:?}"),
        }
    }

    #[test]
    fn test_merge_states_both_sides_modified_with_pre_branch() {
        // Both branches modify x: pre_branch is irrelevant, both values present.
        let mut pre = SymbolicState::new();
        pre.set("x", SymbolicValue::Concrete(0));

        let mut a = SymbolicState::new();
        a.set("x", SymbolicValue::Concrete(10));
        let mut b = SymbolicState::new();
        b.set("x", SymbolicValue::Concrete(20));

        let merged = merge_states_with_pre_branch(&a, &b, Some(&pre), 0);
        let val = merged.get("x").unwrap();
        match val {
            SymbolicValue::Ite(_, then_val, else_val) => {
                assert_eq!(**then_val, SymbolicValue::Concrete(10));
                assert_eq!(**else_val, SymbolicValue::Concrete(20));
            }
            other => panic!("expected Ite, got {other:?}"),
        }
    }

    #[test]
    fn test_merge_states_complex_values() {
        let mut a = SymbolicState::new();
        let mut b = SymbolicState::new();
        a.set(
            "r",
            SymbolicValue::bin_op(
                SymbolicValue::Symbol("x".into()),
                BinOp::Add,
                SymbolicValue::Concrete(1),
            ),
        );
        b.set(
            "r",
            SymbolicValue::bin_op(
                SymbolicValue::Symbol("x".into()),
                BinOp::Sub,
                SymbolicValue::Concrete(1),
            ),
        );
        let merged = merge_states(&a, &b, 2);
        let val = merged.get("r").unwrap();
        match val {
            SymbolicValue::Ite(guard, _, _) => {
                assert_eq!(**guard, SymbolicValue::Symbol("merge_guard_2".into()));
            }
            other => panic!("expected Ite, got {other:?}"),
        }
    }

    // --- merge_paths ---

    #[test]
    fn test_merge_paths_common_prefix() {
        let mut a = PathConstraint::new();
        let mut b = PathConstraint::new();
        // Common prefix: both took branch on "c".
        a.add_constraint(SymbolicValue::Symbol("c".into()), true);
        b.add_constraint(SymbolicValue::Symbol("c".into()), true);
        // Divergence.
        a.add_constraint(SymbolicValue::Symbol("d".into()), true);
        b.add_constraint(SymbolicValue::Symbol("d".into()), false);

        let merged = merge_paths(&a, &b, 0);
        // Prefix (1 decision) + merge guard (1) = depth 2.
        assert_eq!(merged.depth(), 2);
    }

    #[test]
    fn test_merge_paths_no_common_prefix() {
        let mut a = PathConstraint::new();
        let mut b = PathConstraint::new();
        a.add_constraint(SymbolicValue::Symbol("x".into()), true);
        b.add_constraint(SymbolicValue::Symbol("y".into()), true);
        let merged = merge_paths(&a, &b, 0);
        // No common prefix: just the merge guard.
        assert_eq!(merged.depth(), 1);
        // divergent constraints must be preserved as auxiliary.
        assert!(!merged.auxiliary().is_empty(), "divergent constraints should be preserved");
    }

    #[test]
    fn test_merge_paths_preserves_divergent_constraints() {
        // Verify that divergent path constraints are not dropped.
        let mut a = PathConstraint::new();
        let mut b = PathConstraint::new();
        // Common prefix: both took branch on "c".
        a.add_constraint(SymbolicValue::Symbol("c".into()), true);
        b.add_constraint(SymbolicValue::Symbol("c".into()), true);
        // Path A took "d" = true, path B took "d" = false.
        a.add_constraint(SymbolicValue::Symbol("d".into()), true);
        b.add_constraint(SymbolicValue::Symbol("d".into()), false);

        let merged = merge_paths(&a, &b, 0);

        // The merged path has: prefix(c) + guard + auxiliary disjunction.
        assert_eq!(merged.depth(), 2); // c + guard
        assert_eq!(
            merged.auxiliary().len(),
            1,
            "merge should add auxiliary formula for divergent constraints"
        );

        // The auxiliary formula should be an Or of the two arms.
        let aux = &merged.auxiliary()[0];
        assert!(
            matches!(aux, Formula::Or(_)),
            "auxiliary should be (guard AND d) OR (NOT guard AND NOT d), got {aux:?}"
        );
    }

    #[test]
    fn test_merge_paths_identical_no_auxiliary() {
        // If paths have the same constraints, no auxiliary is needed.
        let mut a = PathConstraint::new();
        let mut b = PathConstraint::new();
        a.add_constraint(SymbolicValue::Symbol("c".into()), true);
        b.add_constraint(SymbolicValue::Symbol("c".into()), true);

        let merged = merge_paths(&a, &b, 0);
        assert!(merged.auxiliary().is_empty(), "identical paths should produce no auxiliary");
    }

    #[test]
    fn test_merge_paths_asymmetric_only_a_has_divergent() {
        // When only path A has divergent constraints (path B has
        // no constraints beyond the common prefix), the merged path must still
        // preserve A's constraints as `guard => a_constraints`.
        let mut a = PathConstraint::new();
        let b = PathConstraint::new();
        // Path A has a constraint; path B is empty.
        a.add_constraint(SymbolicValue::Symbol("x_positive".into()), true);

        let merged = merge_paths(&a, &b, 0);

        // The merge guard is the only decision.
        assert_eq!(merged.depth(), 1, "should have only the merge guard");
        // Divergent constraint from A must be preserved as auxiliary.
        assert_eq!(
            merged.auxiliary().len(),
            1,
            "asymmetric merge must preserve A's divergent constraint"
        );

        // The auxiliary should be an Implies (guard => a_constraints),
        // NOT a bare And(guard, a) which would kill the path when guard is false.
        let aux = &merged.auxiliary()[0];
        assert!(
            matches!(aux, Formula::Implies(_, _)),
            "asymmetric merge should use Implies, got {aux:?}"
        );
    }

    #[test]
    fn test_merge_paths_asymmetric_only_b_has_divergent() {
        // Symmetric counterpart: only path B has divergent constraints.
        let a = PathConstraint::new();
        let mut b = PathConstraint::new();
        b.add_constraint(SymbolicValue::Symbol("y_negative".into()), true);

        let merged = merge_paths(&a, &b, 0);
        assert_eq!(merged.depth(), 1);
        assert_eq!(
            merged.auxiliary().len(),
            1,
            "asymmetric merge must preserve B's divergent constraint"
        );

        let aux = &merged.auxiliary()[0];
        assert!(
            matches!(aux, Formula::Implies(_, _)),
            "asymmetric merge should use Implies for B-only case, got {aux:?}"
        );
    }

    #[test]
    fn test_merge_paths_divergent_formula_structure_symmetric() {
        // Verify the full structure of the merged formula when both
        // paths have divergent constraints. The auxiliary should be:
        //   Or(And(guard, a_constr), And(Not(guard), b_constr))
        let mut a = PathConstraint::new();
        let mut b = PathConstraint::new();
        a.add_constraint(SymbolicValue::Symbol("d".into()), true); // d = true
        b.add_constraint(SymbolicValue::Symbol("d".into()), false); // d = false

        let merged = merge_paths(&a, &b, 42);

        assert_eq!(merged.auxiliary().len(), 1);
        let aux = &merged.auxiliary()[0];
        match aux {
            Formula::Or(arms) => {
                assert_eq!(arms.len(), 2, "disjunction should have exactly 2 arms");
                // First arm: And(guard, d)
                match &arms[0] {
                    Formula::And(clauses) => {
                        assert_eq!(clauses.len(), 2);
                        // First clause should reference merge_guard_42.
                        assert!(
                            matches!(&clauses[0], Formula::Var(v, _) if v == "merge_guard_42"),
                            "first arm guard should be merge_guard_42, got {:?}",
                            clauses[0]
                        );
                    }
                    other => panic!("first arm should be And, got {other:?}"),
                }
                // Second arm: And(Not(guard), Not(d))
                match &arms[1] {
                    Formula::And(clauses) => {
                        assert_eq!(clauses.len(), 2);
                        match &clauses[0] {
                            Formula::Not(inner) => {
                                assert!(
                                    matches!(inner.as_ref(), Formula::Var(v, _) if v == "merge_guard_42"),
                                    "second arm guard should be Not(merge_guard_42), got {:?}",
                                    clauses[0]
                                );
                            }
                            other => panic!(
                                "second arm first clause should be Not(guard), got {other:?}"
                            ),
                        }
                    }
                    other => panic!("second arm should be And, got {other:?}"),
                }
            }
            other => panic!("auxiliary should be Or, got {other:?}"),
        }
    }

    #[test]
    fn test_merge_paths_to_formula_includes_auxiliary() {
        // Verify that the full merged formula (from to_formula)
        // includes the auxiliary constraints so they cannot be silently dropped.
        let mut a = PathConstraint::new();
        let mut b = PathConstraint::new();
        a.add_constraint(SymbolicValue::Symbol("c".into()), true);
        b.add_constraint(SymbolicValue::Symbol("c".into()), true);
        a.add_constraint(SymbolicValue::Symbol("d".into()), true);
        b.add_constraint(SymbolicValue::Symbol("d".into()), false);

        let merged = merge_paths(&a, &b, 0);
        let formula = merged.to_formula();

        // The formula should be a conjunction containing the common prefix,
        // the merge guard, AND the auxiliary disjunction. It should NOT drop
        // the divergent constraints.
        match &formula {
            Formula::And(clauses) => {
                // At least 3 clauses: common prefix (c), merge guard, auxiliary.
                assert!(
                    clauses.len() >= 3,
                    "merged formula should have >= 3 clauses (prefix + guard + aux), got {}",
                    clauses.len()
                );
                // The last clause should be the auxiliary (Or disjunction).
                let has_or = clauses.iter().any(|c| matches!(c, Formula::Or(_)));
                assert!(
                    has_or,
                    "merged formula must include Or disjunction for divergent constraints"
                );
            }
            _ => panic!("merged formula should be And conjunction, got {formula:?}"),
        }
    }

    // --- PathMerger ---

    #[test]
    fn test_path_merger_never() {
        let mut merger = PathMerger::new(MergePolicy::Never);
        let a = SymbolicState::new();
        let b = SymbolicState::new();
        assert!(merger.try_merge(&a, &b).is_none());
        assert_eq!(merger.merge_count(), 0);
    }

    #[test]
    fn test_path_merger_always() {
        let mut merger = PathMerger::new(MergePolicy::Always);
        let mut a = SymbolicState::new();
        let mut b = SymbolicState::new();
        a.set("x", SymbolicValue::Concrete(1));
        b.set("x", SymbolicValue::Concrete(2));
        let merged = merger.try_merge(&a, &b).expect("Always policy should merge");
        assert_eq!(merger.merge_count(), 1);
        // Verify the merged state has an Ite for x.
        match merged.get("x").unwrap() {
            SymbolicValue::Ite(_, _, _) => {}
            other => panic!("expected Ite, got {other:?}"),
        }
    }

    #[test]
    fn test_path_merger_increments_merge_id() {
        let mut merger = PathMerger::new(MergePolicy::Always);
        let a = SymbolicState::new();
        let b = SymbolicState::new();
        merger.try_merge(&a, &b).unwrap();
        merger.try_merge(&a, &b).unwrap();
        assert_eq!(merger.merge_count(), 2);
    }

    #[test]
    fn test_path_merger_heuristic_accepts() {
        let mut merger = PathMerger::new(MergePolicy::Heuristic { threshold: 2 });
        let mut a = SymbolicState::new();
        let mut b = SymbolicState::new();
        a.set("x", SymbolicValue::Concrete(1));
        b.set("x", SymbolicValue::Concrete(2));
        assert!(merger.try_merge(&a, &b).is_some());
    }

    #[test]
    fn test_path_merger_heuristic_rejects() {
        let mut merger = PathMerger::new(MergePolicy::Heuristic { threshold: 0 });
        let mut a = SymbolicState::new();
        let mut b = SymbolicState::new();
        a.set("x", SymbolicValue::Concrete(1));
        b.set("x", SymbolicValue::Concrete(2));
        assert!(merger.try_merge(&a, &b).is_none());
    }

    #[test]
    fn test_merge_policy_default() {
        let policy = MergePolicy::default();
        assert_eq!(policy, MergePolicy::Heuristic { threshold: 8 });
    }

    // --- Interval ---

    #[test]
    fn test_interval_point() {
        let i = Interval::point(5);
        assert_eq!(i.lo, 5);
        assert_eq!(i.hi, 5);
        assert!(i.is_point());
    }

    #[test]
    fn test_interval_join_overlapping() {
        let a = Interval { lo: 0, hi: 5 };
        let b = Interval { lo: 3, hi: 8 };
        let joined = a.join(b);
        assert_eq!(joined.lo, 0);
        assert_eq!(joined.hi, 8);
    }

    #[test]
    fn test_interval_join_disjoint() {
        let a = Interval { lo: 0, hi: 2 };
        let b = Interval { lo: 10, hi: 20 };
        let joined = a.join(b);
        assert_eq!(joined.lo, 0);
        assert_eq!(joined.hi, 20);
    }

    #[test]
    fn test_interval_widen_extends() {
        let a = Interval { lo: 0, hi: 5 };
        let b = Interval { lo: -1, hi: 10 };
        let widened = a.widen(b);
        assert_eq!(widened.lo, i128::MIN);
        assert_eq!(widened.hi, i128::MAX);
    }

    #[test]
    fn test_interval_widen_no_extension() {
        let a = Interval { lo: 0, hi: 10 };
        let b = Interval { lo: 2, hi: 8 };
        let widened = a.widen(b);
        assert_eq!(widened.lo, 0);
        assert_eq!(widened.hi, 10);
    }

    // --- StateMerger trait ---

    #[test]
    fn test_ite_merger_overlapping_variables() {
        // Two states with overlapping variable assignments.
        let mut a = SymbolicState::new();
        let mut b = SymbolicState::new();
        a.set("x", SymbolicValue::Concrete(10));
        a.set("y", SymbolicValue::Concrete(20));
        b.set("x", SymbolicValue::Concrete(30));
        b.set("y", SymbolicValue::Concrete(20)); // same as a

        let a_path = PathConstraint::new();
        let b_path = PathConstraint::new();

        let merger = IteMerger;
        let result = merger.merge(&a, &a_path, &b, &b_path, None, 0);

        // y should be preserved (same in both).
        assert_eq!(result.state.get("y").unwrap(), &SymbolicValue::Concrete(20));
        // x should be an Ite (different in the two states).
        match result.state.get("x").unwrap() {
            SymbolicValue::Ite(_, then_val, else_val) => {
                assert_eq!(**then_val, SymbolicValue::Concrete(10));
                assert_eq!(**else_val, SymbolicValue::Concrete(30));
            }
            other => panic!("expected Ite for x, got {other:?}"),
        }
    }

    #[test]
    fn test_widening_merger_concrete_values() {
        // WideningMerger with concrete values: [0..5] join [3..8] = [0..8]
        let mut a = SymbolicState::new();
        let mut b = SymbolicState::new();
        a.set("x", SymbolicValue::Concrete(0));
        b.set("x", SymbolicValue::Concrete(8));
        a.set("same", SymbolicValue::Concrete(42));
        b.set("same", SymbolicValue::Concrete(42));

        let a_path = PathConstraint::new();
        let b_path = PathConstraint::new();

        let merger = WideningMerger;
        let result = merger.merge(&a, &a_path, &b, &b_path, None, 0);

        // "same" should be preserved as concrete.
        assert_eq!(result.state.get("same").unwrap(), &SymbolicValue::Concrete(42));

        // "x" should be widened: not a simple Concrete, should be an Ite with
        // a widened symbol representing the interval [0, 8].
        let x_val = result.state.get("x").unwrap();
        match x_val {
            SymbolicValue::Ite(_, _, _) => {
                // Widened interval produces Ite structure.
                // Check that the widened symbol is referenced.
                let syms = x_val.symbols();
                assert!(
                    syms.iter().any(|s| s.starts_with("widened_")),
                    "expected widened symbol in {syms:?}"
                );
            }
            other => panic!("expected Ite for widened x, got {other:?}"),
        }
    }

    #[test]
    fn test_widening_merger_same_concrete_preserved() {
        let mut a = SymbolicState::new();
        let mut b = SymbolicState::new();
        a.set("x", SymbolicValue::Concrete(5));
        b.set("x", SymbolicValue::Concrete(5));

        let merger = WideningMerger;
        let result = merger.merge(&a, &PathConstraint::new(), &b, &PathConstraint::new(), None, 0);
        // Same value: no widening needed.
        assert_eq!(result.state.get("x").unwrap(), &SymbolicValue::Concrete(5));
    }

    #[test]
    fn test_widening_merger_symbolic_falls_back_to_ite() {
        let mut a = SymbolicState::new();
        let mut b = SymbolicState::new();
        a.set("x", SymbolicValue::Symbol("sym_a".into()));
        b.set("x", SymbolicValue::Symbol("sym_b".into()));

        let merger = WideningMerger;
        let result = merger.merge(&a, &PathConstraint::new(), &b, &PathConstraint::new(), None, 0);
        // Non-concrete values: falls back to Ite merge.
        match result.state.get("x").unwrap() {
            SymbolicValue::Ite(guard, then_val, else_val) => {
                assert_eq!(**guard, SymbolicValue::Symbol("merge_guard_0".into()));
                assert_eq!(**then_val, SymbolicValue::Symbol("sym_a".into()));
                assert_eq!(**else_val, SymbolicValue::Symbol("sym_b".into()));
            }
            other => panic!("expected Ite fallback, got {other:?}"),
        }
    }

    // --- MergeStrategy ---

    #[test]
    fn test_merge_strategy_default() {
        let strat = MergeStrategy::default();
        assert_eq!(strat, MergeStrategy::SelectiveMerge { threshold: 16 });
    }

    // --- StateSplitter ---

    #[test]
    fn test_splitter_if_else_branch() {
        let mut splitter = StateSplitter::new();
        let mut state = SymbolicState::new();
        state.set("x", SymbolicValue::Symbol("input".into()));
        let path = PathConstraint::new();

        let cond = SymbolicValue::bin_op(
            SymbolicValue::Symbol("input".into()),
            BinOp::Lt,
            SymbolicValue::Concrete(10),
        );

        let result = splitter.split(&state, &path, cond.clone(), 1, 2);

        // True branch: goes to block 1, condition asserted true.
        assert_eq!(result.true_state.next_block, 1);
        assert_eq!(result.true_state.path.depth(), 1);
        assert!(result.true_state.path.decisions()[0].taken);

        // False branch: goes to block 2, condition asserted false.
        assert_eq!(result.false_state.next_block, 2);
        assert_eq!(result.false_state.path.depth(), 1);
        assert!(!result.false_state.path.decisions()[0].taken);

        // Both branches share the same state (variable bindings).
        assert_eq!(
            result.true_state.state.get("x").unwrap(),
            result.false_state.state.get("x").unwrap(),
        );

        assert_eq!(result.condition, cond);
        assert_eq!(splitter.split_count(), 1);
    }

    #[test]
    fn test_splitter_multiple_splits() {
        let mut splitter = StateSplitter::new();
        let state = SymbolicState::new();
        let path = PathConstraint::new();
        let cond = SymbolicValue::Symbol("c".into());

        splitter.split(&state, &path, cond.clone(), 1, 2);
        splitter.split(&state, &path, cond, 3, 4);

        assert_eq!(splitter.split_count(), 2);
    }

    // --- MergingExplorer ---

    fn make_fork(block: usize, var: &str, val: i128) -> ExecutionFork {
        let mut state = SymbolicState::new();
        state.set(var, SymbolicValue::Concrete(val));
        ExecutionFork { state, path: PathConstraint::new(), next_block: block }
    }

    #[test]
    fn test_explorer_eager_merge_reduces_paths() {
        // With EagerMerge, two forks targeting the same block should be merged.
        let mut explorer = MergingExplorer::new(MergeStrategy::EagerMerge, MergePolicy::Always);

        let forks = vec![make_fork(5, "x", 1), make_fork(5, "x", 2), make_fork(5, "x", 3)];
        explorer.add_forks(forks);

        // Eager merge should reduce 3 forks to the same block into fewer.
        // With Always policy, all 3 should be merged pairwise.
        assert!(
            explorer.pending_count() < 3,
            "eager merge should reduce path count, got {}",
            explorer.pending_count()
        );
        assert!(explorer.merges_applied() > 0, "should have applied at least one merge");
    }

    #[test]
    fn test_explorer_no_merge_preserves_all_paths() {
        let mut explorer = MergingExplorer::new(MergeStrategy::NoMerge, MergePolicy::Always);

        let forks = vec![make_fork(5, "x", 1), make_fork(5, "x", 2), make_fork(5, "x", 3)];
        explorer.add_forks(forks);

        // NoMerge: all 3 paths preserved.
        assert_eq!(explorer.pending_count(), 3);
        assert_eq!(explorer.merges_applied(), 0);
    }

    #[test]
    fn test_explorer_eager_fewer_paths_than_no_merge() {
        // Compare eager vs no-merge: eager should produce fewer (or equal) paths.
        let forks = vec![
            make_fork(10, "x", 1),
            make_fork(10, "x", 2),
            make_fork(10, "x", 3),
            make_fork(10, "x", 4),
        ];

        let mut no_merge = MergingExplorer::new(MergeStrategy::NoMerge, MergePolicy::Always);
        no_merge.add_forks(forks.clone());
        let no_merge_count = no_merge.pending_count();

        let mut eager = MergingExplorer::new(MergeStrategy::EagerMerge, MergePolicy::Always);
        eager.add_forks(forks);
        let eager_count = eager.pending_count();

        assert!(
            eager_count <= no_merge_count,
            "eager ({eager_count}) should produce <= paths than no-merge ({no_merge_count})"
        );
        assert!(
            eager_count < no_merge_count,
            "with 4 same-block forks, eager should actually reduce count"
        );
    }

    #[test]
    fn test_explorer_selective_merge_respects_threshold() {
        // SelectiveMerge with threshold=5: 3 forks should NOT trigger merge.
        let mut explorer = MergingExplorer::new(
            MergeStrategy::SelectiveMerge { threshold: 5 },
            MergePolicy::Always,
        );

        let forks = vec![make_fork(7, "x", 1), make_fork(7, "x", 2), make_fork(7, "x", 3)];
        explorer.add_forks(forks);

        // 3 forks, threshold 5: should not merge.
        assert_eq!(explorer.pending_count(), 3);
        assert_eq!(explorer.merges_applied(), 0);
    }

    #[test]
    fn test_explorer_selective_merge_triggers_above_threshold() {
        // SelectiveMerge with threshold=2: 4 forks should trigger merge.
        let mut explorer = MergingExplorer::new(
            MergeStrategy::SelectiveMerge { threshold: 2 },
            MergePolicy::Always,
        );

        let forks = vec![
            make_fork(7, "x", 1),
            make_fork(7, "x", 2),
            make_fork(7, "x", 3),
            make_fork(7, "x", 4),
        ];
        explorer.add_forks(forks);

        // 4 forks > threshold 2: should merge.
        assert!(
            explorer.pending_count() < 4,
            "selective merge should reduce path count above threshold, got {}",
            explorer.pending_count()
        );
        assert!(explorer.merges_applied() > 0);
    }

    #[test]
    fn test_explorer_split_and_add() {
        let mut explorer = MergingExplorer::new(MergeStrategy::NoMerge, MergePolicy::Always);
        let mut state = SymbolicState::new();
        state.set("x", SymbolicValue::Symbol("input".into()));
        let path = PathConstraint::new();
        let cond = SymbolicValue::bin_op(
            SymbolicValue::Symbol("input".into()),
            BinOp::Lt,
            SymbolicValue::Concrete(10),
        );

        let result = explorer.split_and_add(&state, &path, cond, 1, 2);

        // Should have 2 pending forks from the split.
        assert_eq!(explorer.pending_count(), 2);
        assert_eq!(explorer.splits_performed(), 1);
        assert_eq!(result.true_state.next_block, 1);
        assert_eq!(result.false_state.next_block, 2);
    }

    #[test]
    fn test_explorer_different_blocks_not_merged() {
        // Forks targeting different blocks should not be merged.
        let mut explorer = MergingExplorer::new(MergeStrategy::EagerMerge, MergePolicy::Always);

        let forks = vec![make_fork(1, "x", 10), make_fork(2, "x", 20), make_fork(3, "x", 30)];
        explorer.add_forks(forks);

        // Different blocks: no merging possible.
        assert_eq!(explorer.pending_count(), 3);
        assert_eq!(explorer.merges_applied(), 0);
    }

    // --- count_differing_vars phi-node semantics ---

    #[test]
    fn test_count_differing_vars_asymmetric_zero_valued() {
        // Regression test for #770: a variable present in one state with
        // value Concrete(0) and absent from the other must be counted as
        // differing. The old code used Concrete(0) as default for missing
        // variables, which would incorrectly report 0 differences here.
        let mut a = SymbolicState::new();
        a.set("x", SymbolicValue::Concrete(0));
        let b = SymbolicState::new(); // x absent

        assert_eq!(
            count_differing_vars(&a, &b),
            1,
            "variable present with Concrete(0) vs absent must count as differing"
        );
    }

    #[test]
    fn test_count_differing_vars_asymmetric_nonzero() {
        // Variable present in one state, absent from the other (non-zero value).
        let mut a = SymbolicState::new();
        a.set("y", SymbolicValue::Concrete(42));
        let b = SymbolicState::new();

        assert_eq!(count_differing_vars(&a, &b), 1);
        assert_eq!(count_differing_vars(&b, &a), 1);
    }

    #[test]
    fn test_count_differing_vars_both_present_same() {
        let mut a = SymbolicState::new();
        let mut b = SymbolicState::new();
        a.set("x", SymbolicValue::Concrete(5));
        b.set("x", SymbolicValue::Concrete(5));

        assert_eq!(count_differing_vars(&a, &b), 0);
    }

    #[test]
    fn test_count_differing_vars_both_present_different() {
        let mut a = SymbolicState::new();
        let mut b = SymbolicState::new();
        a.set("x", SymbolicValue::Concrete(1));
        b.set("x", SymbolicValue::Concrete(2));

        assert_eq!(count_differing_vars(&a, &b), 1);
    }

    #[test]
    fn test_heuristic_asymmetric_zero_not_masked() {
        // Regression: heuristic threshold=0 must reject states with
        // asymmetric variables, even when the present value is Concrete(0).
        // Before #770, this would pass because Concrete(0) was used as
        // default for missing vars, making 0==0 look like "no difference".
        let mut a = SymbolicState::new();
        a.set("x", SymbolicValue::Concrete(0));
        let b = SymbolicState::new();

        // threshold=0 means "only merge if 0 differing vars"
        assert!(
            !can_merge(&a, &b, MergePolicy::Heuristic { threshold: 0 }),
            "asymmetric variable (even with value 0) must count as differing"
        );
    }
}
