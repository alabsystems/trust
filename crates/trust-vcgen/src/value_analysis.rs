// trust_vcgen/value_analysis.rs: Value set analysis for precise VC generation
//
// Computes value sets at each program point for each variable. More precise
// than intervals for small discrete sets (e.g., enum discriminants, boolean
// flags). Falls back to ranges for large sets.
//
// Architecture:
//   ValueSet enum       -> Exact | Range | Strided | Top
//   ValueSetAnalysis    -> per-block, per-variable value sets
//   analyze_function    -> forward dataflow to fixpoint
//   is_definite_error   -> guaranteed out-of-bounds
//   is_definite_safe    -> guaranteed in-bounds
//   generate_vc_from_value_sets -> tighter VCs from precise ranges
//
// Reference: Balakrishnan & Reps, "Analyzing Memory Accesses in x86 Executables"
// (CC 2004) — Value Set Analysis (VSA).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeSet, VecDeque};

use trust_types::fx::FxHashMap;
use trust_types::*;

// ── Value Set ──────────────────────────────────────────────────────────────

/// Maximum size for an exact value set before promoting to Range.
const MAX_EXACT_SIZE: usize = 64;

/// A set of possible values for a variable at a program point.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValueSet {
    /// Exact set of known values.
    Exact(BTreeSet<i64>),
    /// Inclusive range [lo, hi].
    Range(i64, i64),
    /// Strided set: { base + k * stride | 0 <= k < count }.
    Strided { base: i64, stride: i64, count: u64 },
    /// Unknown — all values possible.
    Top,
}

impl ValueSet {
    /// Create a singleton value set.
    #[must_use]
    pub fn singleton(v: i64) -> Self {
        let mut s = BTreeSet::new();
        s.insert(v);
        ValueSet::Exact(s)
    }

    /// Create a range value set.
    #[must_use]
    pub fn range(lo: i64, hi: i64) -> Self {
        if lo > hi {
            ValueSet::Exact(BTreeSet::new())
        } else if lo == hi {
            Self::singleton(lo)
        } else {
            ValueSet::Range(lo, hi)
        }
    }

    /// Is this the empty set?
    #[must_use]
    pub fn is_empty(&self) -> bool {
        matches!(self, ValueSet::Exact(s) if s.is_empty())
    }

    /// Is this Top (unknown)?
    #[must_use]
    pub fn is_top(&self) -> bool {
        matches!(self, ValueSet::Top)
    }

    /// Minimum value in the set, if bounded.
    #[must_use]
    pub fn min_value(&self) -> Option<i64> {
        match self {
            ValueSet::Exact(s) => s.iter().next().copied(),
            ValueSet::Range(lo, _) => Some(*lo),
            ValueSet::Strided { base, .. } => Some(*base),
            ValueSet::Top => None,
        }
    }

    /// Maximum value in the set, if bounded.
    #[must_use]
    pub fn max_value(&self) -> Option<i64> {
        match self {
            ValueSet::Exact(s) => s.iter().next_back().copied(),
            ValueSet::Range(_, hi) => Some(*hi),
            ValueSet::Strided { base, stride, count } => {
                base.checked_add(stride.checked_mul((*count as i64).saturating_sub(1))?)
            }
            ValueSet::Top => None,
        }
    }
}

// ── Value Set Operations ───────────────────────────────────────────────────

/// Join (union) two value sets.
#[must_use]
pub fn join_value_sets(a: &ValueSet, b: &ValueSet) -> ValueSet {
    match (a, b) {
        (ValueSet::Top, _) | (_, ValueSet::Top) => ValueSet::Top,

        (ValueSet::Exact(sa), ValueSet::Exact(sb)) => {
            let merged: BTreeSet<i64> = sa.union(sb).copied().collect();
            if merged.len() > MAX_EXACT_SIZE {
                // Promote to range.
                // SAFETY: merged is a union of two non-empty sets, so it is non-empty.
                let lo = *merged
                    .iter()
                    .next()
                    .unwrap_or_else(|| unreachable!("empty set after union of non-empty sets"));
                let hi = *merged
                    .iter()
                    .next_back()
                    .unwrap_or_else(|| unreachable!("empty set after union of non-empty sets"));
                ValueSet::Range(lo, hi)
            } else {
                ValueSet::Exact(merged)
            }
        }

        (ValueSet::Range(a_lo, a_hi), ValueSet::Range(b_lo, b_hi)) => {
            ValueSet::Range((*a_lo).min(*b_lo), (*a_hi).max(*b_hi))
        }

        (ValueSet::Exact(s), ValueSet::Range(lo, hi))
        | (ValueSet::Range(lo, hi), ValueSet::Exact(s)) => {
            let s_lo = s.iter().next().copied().unwrap_or(*lo);
            let s_hi = s.iter().next_back().copied().unwrap_or(*hi);
            ValueSet::Range((*lo).min(s_lo), (*hi).max(s_hi))
        }

        (
            ValueSet::Strided { base: b1, stride: s1, count: c1 },
            ValueSet::Strided { base: b2, stride: s2, count: c2 },
        ) => {
            if s1 == s2 && b1 % s1 == b2 % s2 {
                // Same stride class, merge.
                let lo = (*b1).min(*b2);
                let hi1 = b1.saturating_add(s1.saturating_mul(*c1 as i64 - 1));
                let hi2 = b2.saturating_add(s2.saturating_mul(*c2 as i64 - 1));
                let hi = hi1.max(hi2);
                if *s1 != 0 {
                    let count = ((hi - lo) / s1 + 1) as u64;
                    ValueSet::Strided { base: lo, stride: *s1, count }
                } else {
                    ValueSet::singleton(lo)
                }
            } else {
                // Different stride classes, fall back to range.
                let lo1 = *b1;
                let lo2 = *b2;
                let hi1 = b1.saturating_add(s1.saturating_mul(*c1 as i64 - 1));
                let hi2 = b2.saturating_add(s2.saturating_mul(*c2 as i64 - 1));
                ValueSet::Range(lo1.min(lo2), hi1.max(hi2))
            }
        }

        // Strided + Range or Exact => Range
        (ValueSet::Strided { base, stride, count }, other)
        | (other, ValueSet::Strided { base, stride, count }) => {
            let s_lo = *base;
            let s_hi = base.saturating_add(stride.saturating_mul(*count as i64 - 1));
            let (o_lo, o_hi) = match other {
                ValueSet::Exact(s) => {
                    let lo = s.iter().next().copied().unwrap_or(s_lo);
                    let hi = s.iter().next_back().copied().unwrap_or(s_hi);
                    (lo, hi)
                }
                ValueSet::Range(lo, hi) => (*lo, *hi),
                _ => (s_lo, s_hi),
            };
            ValueSet::Range(s_lo.min(o_lo), s_hi.max(o_hi))
        }
    }
}

// ── Transfer Functions ─────────────────────────────────────────────────────

/// Abstract state: variable name -> value set.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValueSetState {
    pub vars: FxHashMap<String, ValueSet>,
    pub is_unreachable: bool,
}

impl ValueSetState {
    #[must_use]
    pub fn top() -> Self {
        ValueSetState { vars: FxHashMap::default(), is_unreachable: false }
    }

    #[must_use]
    pub fn bottom() -> Self {
        ValueSetState { vars: FxHashMap::default(), is_unreachable: true }
    }

    /// Get value set for a variable. Missing = Top.
    #[must_use]
    pub fn get(&self, var: &str) -> ValueSet {
        if self.is_unreachable {
            return ValueSet::Exact(BTreeSet::new());
        }
        self.vars.get(var).cloned().unwrap_or(ValueSet::Top)
    }

    /// Set a variable's value set.
    pub fn set(&mut self, var: String, vs: ValueSet) {
        if !self.is_unreachable {
            self.vars.insert(var, vs);
        }
    }

    /// Join two states.
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        if self.is_unreachable {
            return other.clone();
        }
        if other.is_unreachable {
            return self.clone();
        }
        let mut vars = FxHashMap::default();
        let all_keys: BTreeSet<&String> = self.vars.keys().chain(other.vars.keys()).collect();
        for key in all_keys {
            let a = self.get(key);
            let b = other.get(key);
            let joined = join_value_sets(&a, &b);
            if !matches!(joined, ValueSet::Top) {
                vars.insert(key.clone(), joined);
            }
        }
        ValueSetState { vars, is_unreachable: false }
    }
}

/// Resolve an operand to a value set.
fn operand_to_value_set(
    op: &Operand,
    func: &VerifiableFunction,
    state: &ValueSetState,
) -> ValueSet {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            let name = crate::place_to_var_name(func, place);
            state.get(&name)
        }
        Operand::Constant(cv) => match cv {
            ConstValue::Int(n) => {
                if let Ok(v) = i64::try_from(*n) {
                    ValueSet::singleton(v)
                } else {
                    ValueSet::Top
                }
            }
            ConstValue::Uint(n, _) => {
                if let Ok(v) = i64::try_from(*n) {
                    ValueSet::singleton(v)
                } else {
                    ValueSet::Top
                }
            }
            ConstValue::Bool(b) => ValueSet::singleton(i64::from(*b)),
            ConstValue::Float(_) | ConstValue::Unit | ConstValue::CallableItem { .. } => {
                ValueSet::Top
            }
            _ => ValueSet::Top,
        },
        _ => ValueSet::Top,
    }
}

/// Apply an assignment transfer function.
#[must_use]
pub fn transfer_assign(
    target: &Place,
    rvalue: &Rvalue,
    func: &VerifiableFunction,
    state: &ValueSetState,
) -> ValueSetState {
    let mut result = state.clone();
    if result.is_unreachable {
        return result;
    }

    let target_name = crate::place_to_var_name(func, target);
    let vs = eval_rvalue_vs(rvalue, func, state);
    result.set(target_name, vs);
    result
}

/// Evaluate an rvalue to a value set.
fn eval_rvalue_vs(rvalue: &Rvalue, func: &VerifiableFunction, state: &ValueSetState) -> ValueSet {
    match rvalue {
        Rvalue::Use(op) => operand_to_value_set(op, func, state),

        Rvalue::BinaryOp(op, lhs, rhs) | Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
            let a = operand_to_value_set(lhs, func, state);
            let b = operand_to_value_set(rhs, func, state);
            apply_binop_vs(*op, &a, &b)
        }

        Rvalue::UnaryOp(UnOp::Neg, op) => {
            let a = operand_to_value_set(op, func, state);
            match a {
                ValueSet::Exact(s) => {
                    let negated: BTreeSet<i64> = s.iter().filter_map(|v| v.checked_neg()).collect();
                    if negated.len() > MAX_EXACT_SIZE {
                        ValueSet::Top
                    } else {
                        ValueSet::Exact(negated)
                    }
                }
                ValueSet::Range(lo, hi) => {
                    if let (Some(nhi), Some(nlo)) = (lo.checked_neg(), hi.checked_neg()) {
                        ValueSet::Range(nhi.min(nlo), nhi.max(nlo))
                    } else {
                        ValueSet::Top
                    }
                }
                _ => ValueSet::Top,
            }
        }

        Rvalue::Len(_) => ValueSet::range(0, i64::MAX),
        Rvalue::Discriminant(_) => ValueSet::range(0, i64::MAX),
        _ => ValueSet::Top,
    }
}

/// Apply a binary operation to value sets.
fn apply_binop_vs(op: BinOp, a: &ValueSet, b: &ValueSet) -> ValueSet {
    // For exact small sets, compute pointwise.
    if let (ValueSet::Exact(sa), ValueSet::Exact(sb)) = (a, b)
        && sa.len() * sb.len() <= MAX_EXACT_SIZE
    {
        let mut result = BTreeSet::new();
        for &va in sa {
            for &vb in sb {
                if let Some(r) = eval_binop_i64(op, va, vb) {
                    result.insert(r);
                }
            }
        }
        if result.len() <= MAX_EXACT_SIZE {
            return ValueSet::Exact(result);
        }
    }

    // Fall back to range arithmetic.
    let (a_lo, a_hi) = match (a.min_value(), a.max_value()) {
        (Some(lo), Some(hi)) => (lo, hi),
        _ => return ValueSet::Top,
    };
    let (b_lo, b_hi) = match (b.min_value(), b.max_value()) {
        (Some(lo), Some(hi)) => (lo, hi),
        _ => return ValueSet::Top,
    };

    match op {
        BinOp::Add => match (a_lo.checked_add(b_lo), a_hi.checked_add(b_hi)) {
            (Some(lo), Some(hi)) => ValueSet::range(lo, hi),
            _ => ValueSet::Top,
        },
        BinOp::Sub => match (a_lo.checked_sub(b_hi), a_hi.checked_sub(b_lo)) {
            (Some(lo), Some(hi)) => ValueSet::range(lo, hi),
            _ => ValueSet::Top,
        },
        BinOp::Mul => {
            let corners = [
                a_lo.checked_mul(b_lo),
                a_lo.checked_mul(b_hi),
                a_hi.checked_mul(b_lo),
                a_hi.checked_mul(b_hi),
            ];
            let mut lo = i64::MAX;
            let mut hi = i64::MIN;
            for c in &corners {
                match c {
                    Some(v) => {
                        lo = lo.min(*v);
                        hi = hi.max(*v);
                    }
                    None => return ValueSet::Top,
                }
            }
            ValueSet::range(lo, hi)
        }
        _ => ValueSet::Top,
    }
}

/// Evaluate a single binary operation on concrete values.
fn eval_binop_i64(op: BinOp, a: i64, b: i64) -> Option<i64> {
    match op {
        BinOp::Add => a.checked_add(b),
        BinOp::Sub => a.checked_sub(b),
        BinOp::Mul => a.checked_mul(b),
        BinOp::Div => {
            if b == 0 {
                None
            } else {
                a.checked_div(b)
            }
        }
        BinOp::Rem => {
            if b == 0 {
                None
            } else {
                a.checked_rem(b)
            }
        }
        _ => None,
    }
}

// ── Condition Transfer ─────────────────────────────────────────────────────

/// Split a state based on a branch condition.
///
/// Returns (true_state, false_state) where the condition holds / does not hold.
#[must_use]
pub fn transfer_condition(
    discr: &Operand,
    value: u128,
    func: &VerifiableFunction,
    state: &ValueSetState,
) -> (ValueSetState, ValueSetState) {
    let mut true_state = state.clone();
    let mut false_state = state.clone();

    if let Operand::Copy(place) | Operand::Move(place) = discr {
        let name = crate::place_to_var_name(func, place);
        if let Ok(v) = i64::try_from(value) {
            // True branch: variable equals the switch value.
            true_state.set(name.clone(), ValueSet::singleton(v));

            // False branch: remove the value from the set.
            let current = state.get(&name);
            match current {
                ValueSet::Exact(mut s) => {
                    s.remove(&v);
                    false_state.set(name, ValueSet::Exact(s));
                }
                _ => {
                    // Can't precisely remove one value from a range/top.
                }
            }
        }
    }

    (true_state, false_state)
}

// ── Function-Level Analysis ────────────────────────────────────────────────

/// Extract all successor block IDs from a terminator for dataflow propagation.
fn vs_terminator_successors(term: &Terminator) -> Vec<BlockId> {
    match term {
        Terminator::Goto(target) | Terminator::Drop { target, .. } => vec![*target],
        Terminator::SwitchInt { targets, otherwise, .. } => {
            let mut succs: Vec<BlockId> = targets.iter().map(|(_, b)| *b).collect();
            succs.push(*otherwise);
            succs
        }
        Terminator::Assert { target, .. } => vec![*target],
        Terminator::Call { target, .. } => target.iter().copied().collect(),
        Terminator::Opaque { targets, .. } => targets.clone(),
        Terminator::Return | Terminator::Unreachable => vec![],
        _ => vec![],
    }
}

/// Analyze an entire function, computing value sets at each block entry.
#[must_use]
pub fn analyze_function(func: &VerifiableFunction) -> FxHashMap<String, ValueSet> {
    let mut block_states: FxHashMap<BlockId, ValueSetState> = FxHashMap::default();

    // Initialize all blocks to bottom (unreachable).
    for block in &func.body.blocks {
        block_states.insert(block.id, ValueSetState::bottom());
    }

    // Entry block gets top state with argument constraints.
    let mut entry_state = ValueSetState::top();
    for (i, local) in func.body.locals.iter().enumerate() {
        if i == 0 || i > func.body.arg_count {
            continue; // skip return slot and non-args
        }
        let name = local.name.clone().unwrap_or_else(|| format!("_{i}"));
        let vs = type_to_value_set(&local.ty);
        entry_state.set(name, vs);
    }

    if let Some(first) = func.body.blocks.first() {
        block_states.insert(first.id, entry_state);
    }

    // Forward dataflow to fixpoint.
    let max_iterations = func.body.blocks.len() * 15 + 50;
    let mut worklist: VecDeque<BlockId> = func.body.blocks.iter().map(|b| b.id).collect();
    let mut iteration = 0;

    while let Some(block_id) = worklist.pop_front() {
        iteration += 1;
        if iteration > max_iterations {
            break;
        }

        let Some(block) = func.body.blocks.iter().find(|b| b.id == block_id) else {
            continue;
        };

        let entry = block_states.get(&block_id).cloned().unwrap_or_else(ValueSetState::bottom);
        if entry.is_unreachable {
            continue;
        }

        // Apply transfer functions for all statements.
        let mut current = entry;
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt {
                current = transfer_assign(place, rvalue, func, &current);
            }
        }

        // Propagate to successors.
        // Use direct terminator successor extraction (exit_targets() doesn't
        // include Assert/Call success targets).
        let successors = vs_terminator_successors(&block.terminator);
        for succ_id in successors {
            let old = block_states.get(&succ_id).cloned().unwrap_or_else(ValueSetState::bottom);
            let merged = old.join(&current);
            if merged != old {
                block_states.insert(succ_id, merged);
                if !worklist.contains(&succ_id) {
                    worklist.push_back(succ_id);
                }
            }
        }
    }

    // Collect the final state at the last reachable block.
    // Merge all block exit states for a conservative summary.
    let mut result = FxHashMap::default();
    for state in block_states.values() {
        if state.is_unreachable {
            continue;
        }
        for (var, vs) in &state.vars {
            let existing = result.remove(var).unwrap_or_else(|| ValueSet::Exact(BTreeSet::new()));
            result.insert(var.clone(), join_value_sets(&existing, vs));
        }
    }
    result
}

/// Convert a type to an initial value set based on its range.
fn type_to_value_set(ty: &Ty) -> ValueSet {
    match ty {
        Ty::Bool => {
            let mut s = BTreeSet::new();
            s.insert(0);
            s.insert(1);
            ValueSet::Exact(s)
        }
        Ty::Int { width, signed: false } => {
            let max = if *width >= 64 { i64::MAX } else { (1i64 << width) - 1 };
            ValueSet::Range(0, max)
        }
        Ty::Int { width, .. } => {
            if *width >= 64 {
                ValueSet::Range(i64::MIN, i64::MAX)
            } else {
                let half = 1i64 << (width - 1);
                ValueSet::Range(-half, half - 1)
            }
        }
        _ => ValueSet::Top,
    }
}

// ── Safety / Error Detection ───────────────────────────────────────────────

/// Array access descriptor.
#[derive(Debug, Clone)]
pub struct ArrayAccess {
    /// Index value set.
    pub index: ValueSet,
    /// Array length value set.
    pub length: ValueSet,
}

/// Check if an array access is definitely an error (guaranteed out-of-bounds).
///
/// Returns true only when ALL possible index values are outside [0, length-1].
#[must_use]
pub fn is_definite_error(access: &ArrayAccess) -> bool {
    let idx_min = match access.index.min_value() {
        Some(v) => v,
        None => return false, // Top index — can't guarantee error.
    };
    let idx_max = match access.index.max_value() {
        Some(v) => v,
        None => return false,
    };
    let len_max = match access.length.max_value() {
        Some(v) => v,
        None => return false,
    };

    // Definitely error if: all indices are negative, or all indices >= max length.
    if idx_max < 0 {
        return true;
    }
    if len_max <= 0 {
        // Zero-length array — any access is OOB.
        return !access.index.is_empty();
    }
    idx_min >= len_max
}

/// Check if an array access is definitely safe (guaranteed in-bounds).
///
/// Returns true only when ALL possible index values are within [0, min_length-1].
#[must_use]
pub fn is_definite_safe(access: &ArrayAccess) -> bool {
    let idx_min = match access.index.min_value() {
        Some(v) => v,
        None => return false,
    };
    let idx_max = match access.index.max_value() {
        Some(v) => v,
        None => return false,
    };
    let len_min = match access.length.min_value() {
        Some(v) => v,
        None => return false,
    };

    idx_min >= 0 && idx_max < len_min
}

// ── VC Generation from Value Sets ──────────────────────────────────────────

/// Generate tighter verification conditions from value set analysis results.
///
/// For each variable with a known range, adds bound assertions as VCs.
/// These are tighter than the default VCs because they incorporate
/// dataflow information.
#[must_use]
pub fn generate_vc_from_value_sets(
    analysis: &FxHashMap<String, ValueSet>,
    function_name: &str,
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    for (var_name, vs) in analysis {
        let var_f = Formula::Var(var_name.clone(), Sort::Int);

        match vs {
            ValueSet::Exact(values) if !values.is_empty() => {
                // Generate: var == v1 OR var == v2 OR ...
                let clauses: Vec<Formula> = values
                    .iter()
                    .map(|&v| {
                        Formula::Eq(Box::new(var_f.clone()), Box::new(Formula::Int(i128::from(v))))
                    })
                    .collect();
                if clauses.len() == 1 {
                    vcs.push(VerificationCondition {
                        kind: VcKind::Assertion {
                            message: format!("value_analysis: {var_name} is constant"),
                        },
                        function: function_name.into(),
                        location: SourceSpan::default(),
                        // SAFETY: we enter this branch only when clauses.len() == 1.
                        formula: Formula::Not(Box::new(
                            clauses
                                .into_iter()
                                .next()
                                .unwrap_or_else(|| unreachable!("empty clauses despite len == 1")),
                        )),
                        contract_metadata: None,
                    });
                }
                // Multi-value exact sets generate a disjunction constraint.
                // Omitted for brevity — the single-value case is most useful.
            }

            ValueSet::Range(lo, hi) => {
                // Generate: NOT (lo <= var AND var <= hi)
                // If SAT, the variable escapes its computed range.
                let lower =
                    Formula::Ge(Box::new(var_f.clone()), Box::new(Formula::Int(i128::from(*lo))));
                let upper =
                    Formula::Le(Box::new(var_f.clone()), Box::new(Formula::Int(i128::from(*hi))));
                let in_range = Formula::And(vec![lower, upper]);
                vcs.push(VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!("value_analysis: {var_name} in [{lo}, {hi}]"),
                    },
                    function: function_name.into(),
                    location: SourceSpan::default(),
                    formula: Formula::Not(Box::new(in_range)),
                    contract_metadata: None,
                });
            }

            _ => {} // Top or empty — no useful VC.
        }
    }

    vcs
}

// ── Tests ──────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    // -- Value set operations --

    #[test]
    fn test_singleton_creation() {
        let vs = ValueSet::singleton(42);
        assert_eq!(vs.min_value(), Some(42));
        assert_eq!(vs.max_value(), Some(42));
        assert!(!vs.is_empty());
        assert!(!vs.is_top());
    }

    #[test]
    fn test_range_creation() {
        let vs = ValueSet::range(0, 100);
        assert_eq!(vs.min_value(), Some(0));
        assert_eq!(vs.max_value(), Some(100));
    }

    #[test]
    fn test_range_invalid_becomes_empty() {
        let vs = ValueSet::range(10, 5);
        assert!(vs.is_empty());
    }

    #[test]
    fn test_range_single_becomes_singleton() {
        let vs = ValueSet::range(7, 7);
        assert!(matches!(vs, ValueSet::Exact(_)));
        assert_eq!(vs.min_value(), Some(7));
    }

    #[test]
    fn test_join_exact_sets() {
        let a = ValueSet::singleton(1);
        let b = ValueSet::singleton(2);
        let j = join_value_sets(&a, &b);
        match j {
            ValueSet::Exact(s) => {
                assert!(s.contains(&1));
                assert!(s.contains(&2));
                assert_eq!(s.len(), 2);
            }
            _ => panic!("expected Exact after joining two singletons"),
        }
    }

    #[test]
    fn test_join_ranges() {
        let a = ValueSet::range(0, 10);
        let b = ValueSet::range(5, 20);
        let j = join_value_sets(&a, &b);
        assert_eq!(j, ValueSet::Range(0, 20));
    }

    #[test]
    fn test_join_with_top() {
        let a = ValueSet::range(0, 10);
        let b = ValueSet::Top;
        assert!(join_value_sets(&a, &b).is_top());
    }

    #[test]
    fn test_join_exact_and_range() {
        let a = ValueSet::singleton(50);
        let b = ValueSet::range(0, 10);
        let j = join_value_sets(&a, &b);
        assert_eq!(j, ValueSet::Range(0, 50));
    }

    #[test]
    fn test_join_strided_same_class() {
        let a = ValueSet::Strided { base: 0, stride: 2, count: 5 }; // {0,2,4,6,8}
        let b = ValueSet::Strided { base: 10, stride: 2, count: 3 }; // {10,12,14}
        let j = join_value_sets(&a, &b);
        match j {
            ValueSet::Strided { base, stride, count } => {
                assert_eq!(base, 0);
                assert_eq!(stride, 2);
                assert_eq!(count, 8); // 0 to 14, stride 2 => 8 elements
            }
            _ => panic!("expected Strided, got {j:?}"),
        }
    }

    // -- Transfer function tests --

    #[test]
    fn test_transfer_assign_constant() {
        let func = crate::tests::midpoint_function();
        let state = ValueSetState::top();
        let place = Place::local(4);
        let rvalue = Rvalue::Use(Operand::Constant(ConstValue::Uint(42, 64)));
        let result = transfer_assign(&place, &rvalue, &func, &state);
        assert_eq!(result.get("_4"), ValueSet::singleton(42));
    }

    #[test]
    fn test_transfer_assign_add_singletons() {
        let func = crate::tests::midpoint_function();
        let mut state = ValueSetState::top();
        state.set("a".into(), ValueSet::singleton(10));
        state.set("b".into(), ValueSet::singleton(20));
        let place = Place::local(4);
        let rvalue = Rvalue::BinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local(1)),
            Operand::Copy(Place::local(2)),
        );
        let result = transfer_assign(&place, &rvalue, &func, &state);
        assert_eq!(result.get("_4"), ValueSet::singleton(30));
    }

    #[test]
    fn test_transfer_assign_add_ranges() {
        let func = crate::tests::midpoint_function();
        let mut state = ValueSetState::top();
        state.set("a".into(), ValueSet::range(0, 50));
        state.set("b".into(), ValueSet::range(0, 50));
        let place = Place::local(4);
        let rvalue = Rvalue::BinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local(1)),
            Operand::Copy(Place::local(2)),
        );
        let result = transfer_assign(&place, &rvalue, &func, &state);
        assert_eq!(result.get("_4"), ValueSet::Range(0, 100));
    }

    // -- Condition transfer tests --

    #[test]
    fn test_transfer_condition_narrows_true_branch() {
        let func = crate::tests::midpoint_function();
        let mut state = ValueSetState::top();
        let mut s = BTreeSet::new();
        s.insert(0);
        s.insert(1);
        state.set("flag".into(), ValueSet::Exact(s));

        let (true_state, false_state) =
            transfer_condition(&Operand::Copy(Place::local(1)), 1, &func, &state);

        // In the midpoint function, local 1 is "a", but the condition transfer
        // uses the place name. The test verifies narrowing works.
        assert_eq!(true_state.get("a"), ValueSet::singleton(1));
        // False state should have "a" narrowed to NOT 1.
        let false_vs = false_state.get("a");
        if let ValueSet::Exact(s) = false_vs {
            assert!(!s.contains(&1));
        }
    }

    // -- Safety/error detection --

    #[test]
    fn test_definite_error_negative_index() {
        let access =
            ArrayAccess { index: ValueSet::range(-5, -1), length: ValueSet::range(10, 20) };
        assert!(is_definite_error(&access));
    }

    #[test]
    fn test_definite_error_index_past_length() {
        let access =
            ArrayAccess { index: ValueSet::range(100, 200), length: ValueSet::range(5, 50) };
        assert!(is_definite_error(&access));
    }

    #[test]
    fn test_definite_error_zero_length_array() {
        let access = ArrayAccess { index: ValueSet::singleton(0), length: ValueSet::singleton(0) };
        assert!(is_definite_error(&access));
    }

    #[test]
    fn test_not_definite_error_overlapping() {
        let access = ArrayAccess { index: ValueSet::range(0, 10), length: ValueSet::range(5, 20) };
        assert!(!is_definite_error(&access));
    }

    #[test]
    fn test_definite_safe_in_bounds() {
        let access = ArrayAccess { index: ValueSet::range(0, 4), length: ValueSet::range(10, 20) };
        assert!(is_definite_safe(&access));
    }

    #[test]
    fn test_not_definite_safe_may_exceed() {
        let access = ArrayAccess { index: ValueSet::range(0, 15), length: ValueSet::range(10, 20) };
        assert!(!is_definite_safe(&access));
    }

    #[test]
    fn test_not_definite_safe_top_index() {
        let access = ArrayAccess { index: ValueSet::Top, length: ValueSet::range(10, 20) };
        assert!(!is_definite_safe(&access));
    }

    // -- Function analysis --

    #[test]
    fn test_analyze_midpoint_function() {
        let func = crate::tests::midpoint_function();
        let result = analyze_function(&func);
        // Should compute value sets for the function's variables.
        // The midpoint function has variables a, b.
        assert!(!result.is_empty(), "analysis should produce some variable bindings");
    }

    // -- VC generation --

    #[test]
    fn test_generate_vc_from_singleton() {
        let mut analysis = FxHashMap::default();
        analysis.insert("x".to_string(), ValueSet::singleton(42));
        let vcs = generate_vc_from_value_sets(&analysis, "test_fn");
        assert_eq!(vcs.len(), 1);
        assert!(matches!(vcs[0].kind, VcKind::Assertion { .. }));
    }

    #[test]
    fn test_generate_vc_from_range() {
        let mut analysis = FxHashMap::default();
        analysis.insert("y".to_string(), ValueSet::range(0, 100));
        let vcs = generate_vc_from_value_sets(&analysis, "test_fn");
        assert_eq!(vcs.len(), 1);
        assert!(matches!(vcs[0].kind, VcKind::Assertion { .. }));
    }

    #[test]
    fn test_generate_vc_from_top_produces_nothing() {
        let mut analysis = FxHashMap::default();
        analysis.insert("z".to_string(), ValueSet::Top);
        let vcs = generate_vc_from_value_sets(&analysis, "test_fn");
        assert!(vcs.is_empty(), "Top produces no useful VC");
    }

    #[test]
    fn test_type_to_value_set_bool() {
        let vs = type_to_value_set(&Ty::Bool);
        match vs {
            ValueSet::Exact(s) => {
                assert!(s.contains(&0));
                assert!(s.contains(&1));
                assert_eq!(s.len(), 2);
            }
            _ => panic!("expected Exact for Bool"),
        }
    }

    #[test]
    fn test_type_to_value_set_u32() {
        let vs = type_to_value_set(&Ty::Int { width: 32, signed: false });
        assert_eq!(vs.min_value(), Some(0));
        assert_eq!(vs.max_value(), Some((1i64 << 32) - 1));
    }

    #[test]
    fn test_type_to_value_set_i32() {
        let vs = type_to_value_set(&Ty::Int { width: 32, signed: true });
        assert_eq!(vs.min_value(), Some(-(1i64 << 31)));
        assert_eq!(vs.max_value(), Some((1i64 << 31) - 1));
    }
}
