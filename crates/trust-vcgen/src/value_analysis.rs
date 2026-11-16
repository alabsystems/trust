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

use trust_types::fx::{FxHashMap, FxHashSet};
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
            if sa.len().max(sb.len()) > MAX_EXACT_SIZE
                && let Some(lo) = sa.first().copied().into_iter().chain(sb.first().copied()).min()
                && let Some(hi) = sa.last().copied().into_iter().chain(sb.last().copied()).max()
            {
                return ValueSet::Range(lo, hi);
            }
            let merged: BTreeSet<i64> = sa.union(sb).copied().collect();
            if merged.len() > MAX_EXACT_SIZE
                && let (Some(&lo), Some(&hi)) = (merged.first(), merged.last())
            {
                // Promote to range.
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
        // A variable absent from either map denotes `ValueSet::Top`, and
        // `join_value_sets(Top, _) == Top`, so only keys present in both maps can
        // yield a non-Top entry. Iterate the smaller map and borrow both `ValueSet`s.
        let (smaller, larger) = if self.vars.len() <= other.vars.len() {
            (&self.vars, &other.vars)
        } else {
            (&other.vars, &self.vars)
        };
        let mut vars = FxHashMap::with_capacity_and_hasher(smaller.len(), Default::default());
        for (key, a) in smaller {
            if let Some(b) = larger.get(key) {
                let joined = join_value_sets(a, b);
                if !matches!(joined, ValueSet::Top) {
                    vars.insert(key.clone(), joined);
                }
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

/// Apply an assignment transfer function in place.
fn transfer_assign_in_place(
    target: &Place,
    rvalue: &Rvalue,
    func: &VerifiableFunction,
    state: &mut ValueSetState,
) {
    if state.is_unreachable {
        return;
    }

    let target_name = crate::place_to_var_name(func, target);
    // Trust (2026-09-28): a discriminant read is its enum's DECODED tag hull,
    // negative tags included (`crate::abstract_interp::transfer::discriminant_read_hull`
    // has the measured false proof the old `[0, i64::MAX]` produced); Top when the
    // hull is unknown or does not fit `i64`.
    let mut vs = if let Rvalue::Discriminant(src) = rvalue {
        crate::abstract_interp::transfer::discriminant_read_hull(func, src, target)
            .and_then(|(lo, hi)| {
                Some(ValueSet::range(i64::try_from(lo).ok()?, i64::try_from(hi).ok()?))
            })
            .unwrap_or(ValueSet::Top)
    } else {
        eval_rvalue_vs(rvalue, func, state)
    };
    // Trust (2026-10-05, NEG-WRAP-OFF-1): a bare integer `Neg` WRAPS (`-MIN ==
    // MIN`; the overflow check is the separate dominating `Assert(OverflowNeg)`), so
    // the mathematical set `eval_rvalue_vs` computes is the machine's only when it
    // fits the destination type; otherwise the destination's full range — the
    // interval lane's `clamp_bare_binop_to_dest_range`, here.
    if let Rvalue::UnaryOp(UnOp::Neg, _) = rvalue {
        vs = clamp_bare_vs_to_dest_range(vs, func, target);
    }
    state.set(target_name, vs);
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
    transfer_assign_in_place(target, rvalue, func, &mut result);
    result
}

/// The machine-value clamp for a bare (wrapping) integer op's destination: `vs`
/// unchanged when every member lies in the destination type's range (no input can
/// have wrapped), else that whole range (`Top` when it is unknown or does not fit
/// `i64`). The empty set (unreachable) passes through; `Top` stays `Top`.
fn clamp_bare_vs_to_dest_range(vs: ValueSet, func: &VerifiableFunction, dest: &Place) -> ValueSet {
    if vs.is_empty() || vs.is_top() {
        return vs;
    }
    let range = crate::place_ty_cow(func, dest).as_deref().and_then(|ty| match ty {
        Ty::PtrSizedInt { signed } => {
            crate::abstract_interp::discharge::type_bounds(&Ty::Int { width: 64, signed: *signed })
        }
        other => crate::abstract_interp::discharge::type_bounds(other),
    });
    let Some((lo, hi)) = range else {
        return ValueSet::Top;
    };
    let fits = match (vs.min_value(), vs.max_value()) {
        (Some(min), Some(max)) => i128::from(min) >= lo && i128::from(max) <= hi,
        _ => false,
    };
    if fits {
        return vs;
    }
    match (i64::try_from(lo), i64::try_from(hi)) {
        (Ok(lo), Ok(hi)) => ValueSet::range(lo, hi),
        _ => ValueSet::Top,
    }
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
                    // Trust (2026-10-05, NEG-WRAP-OFF-1): a member whose negation
                    // leaves `i64` (`i64::MIN`) makes the whole set Top. It used to be
                    // DROPPED (`filter_map`), so `{i64::MIN, 5}` negated to `{-5}` —
                    // a set that excluded the machine's wrapped `i64::MIN`.
                    let negated: Option<BTreeSet<i64>> =
                        s.iter().map(|v| v.checked_neg()).collect();
                    match negated {
                        Some(negated) if negated.len() <= MAX_EXACT_SIZE => {
                            ValueSet::Exact(negated)
                        }
                        _ => ValueSet::Top,
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
        // Trust (2026-09-28): Top here; `transfer_assign`, which knows the
        // destination, narrows it to the enum's tag hull. It was `[0, i64::MAX]`,
        // which a negative tag violates.
        Rvalue::Discriminant(_) => ValueSet::Top,
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

    if let Operand::Copy(place) | Operand::Move(place) = discr
        && let Ok(v) = i64::try_from(value)
    {
        let name = crate::place_to_var_name(func, place);
        // False branch: remove the value from the set in place.
        if !false_state.is_unreachable
            && let Some(ValueSet::Exact(s)) = false_state.vars.get_mut(&name)
        {
            s.remove(&v);
        }
        // True branch: variable equals the switch value.
        true_state.set(name, ValueSet::singleton(v));
    }

    (true_state, false_state)
}

// ── Function-Level Analysis ────────────────────────────────────────────────

/// Visit all successor block IDs from a terminator for dataflow propagation without allocating a `Vec`.
fn for_each_vs_successor(term: &Terminator, mut f: impl FnMut(BlockId)) {
    match term {
        Terminator::Goto(target)
        | Terminator::Drop { target, .. }
        | Terminator::Assert { target, .. } => f(*target),
        Terminator::SwitchInt { targets, otherwise, .. } => {
            for (_, b) in targets {
                f(*b);
            }
            f(*otherwise);
        }
        Terminator::Call { target: Some(target), .. } => f(*target),
        Terminator::Opaque { targets, .. } => {
            for &b in targets {
                f(b);
            }
        }
        Terminator::Call { target: None, .. }
        | Terminator::Return
        | Terminator::TailCall { .. }
        | Terminator::Unreachable
        | _ => {}
    }
}

/// Analyze an entire function, computing value sets at each block entry.
#[must_use]
pub fn analyze_function(func: &VerifiableFunction) -> FxHashMap<String, ValueSet> {
    if func.body.blocks.is_empty() {
        return FxHashMap::default();
    }
    let expanded = func.with_tail_calls_expanded();
    let func = expanded.as_ref();
    let mut block_states: FxHashMap<BlockId, ValueSetState> =
        FxHashMap::with_capacity_and_hasher(func.body.blocks.len(), Default::default());

    // Initialize all blocks to bottom (unreachable).
    for block in &func.body.blocks {
        block_states.insert(block.id, ValueSetState::bottom());
    }

    // Entry block gets top state with argument constraints.
    let mut entry_state = ValueSetState::top();
    for local in func.body.locals.iter().take(func.body.arg_count.saturating_add(1)).skip(1) {
        // The formula name the transfers write (`crate::local_var_name`).
        let vs = type_to_value_set(&local.ty);
        entry_state.set(crate::local_var_name(func, local), vs);
    }

    let mut worklist: VecDeque<BlockId> = VecDeque::with_capacity(func.body.blocks.len());
    let mut in_worklist: FxHashSet<BlockId> =
        FxHashSet::with_capacity_and_hasher(func.body.blocks.len(), Default::default());
    if let Some(first) = func.body.blocks.first() {
        block_states.insert(first.id, entry_state);
        worklist.push_back(first.id);
        in_worklist.insert(first.id);
    }

    // Forward dataflow to fixpoint.
    let max_iterations = func.body.blocks.len() * 15 + 50;
    let mut iteration = 0;

    while let Some(block_id) = worklist.pop_front() {
        in_worklist.remove(&block_id);
        iteration += 1;
        if iteration > max_iterations {
            break;
        }

        let Some(block) = func
            .body
            .blocks
            .get(block_id.0)
            .filter(|b| b.id == block_id)
            .or_else(|| func.body.blocks.iter().find(|b| b.id == block_id))
        else {
            continue;
        };

        let Some(entry) = block_states.get(&block_id).filter(|s| !s.is_unreachable).cloned() else {
            continue;
        };

        // Apply transfer functions for all statements.
        let mut current = entry;
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt {
                transfer_assign_in_place(place, rvalue, func, &mut current);
            }
        }

        // Propagate to successors.
        // Use direct terminator successor extraction (exit_targets() doesn't
        // include Assert/Call success targets).
        for_each_vs_successor(&block.terminator, |succ_id| {
            let (merged, changed) = match block_states.get(&succ_id) {
                Some(old) => {
                    let merged = old.join(&current);
                    let changed = &merged != old;
                    (merged, changed)
                }
                None => (current.clone(), !current.is_unreachable),
            };
            if changed {
                block_states.insert(succ_id, merged);
                if in_worklist.insert(succ_id) {
                    worklist.push_back(succ_id);
                }
            }
        });
    }

    // Collect the final state at the last reachable block.
    // Merge all block exit states for a conservative summary.
    let mut result = FxHashMap::default();
    for state in block_states.values() {
        if state.is_unreachable {
            continue;
        }
        for (var, vs) in &state.vars {
            match result.get_mut(var) {
                Some(existing) => *existing = join_value_sets(existing, vs),
                None => {
                    let initial = match vs {
                        ValueSet::Top | ValueSet::Range(_, _) => vs.clone(),
                        ValueSet::Exact(s) if s.len() <= MAX_EXACT_SIZE => vs.clone(),
                        _ => join_value_sets(&ValueSet::Exact(BTreeSet::new()), vs),
                    };
                    result.insert(var.clone(), initial);
                }
            }
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
    let mut fn_sym: Option<Symbol> = None;

    for (var_name, vs) in analysis {
        match vs {
            ValueSet::Exact(values) if values.len() == 1 => {
                if let Some(&v) = values.iter().next() {
                    let var_f = Formula::Var(var_name.clone(), Sort::Int);
                    let eq = Formula::Eq(Box::new(var_f), Box::new(Formula::Int(i128::from(v))));
                    vcs.push(VerificationCondition {
                        kind: VcKind::Assertion {
                            message: format!("value_analysis: {var_name} is constant"),
                        },
                        function: *fn_sym.get_or_insert_with(|| function_name.into()),
                        location: SourceSpan::default(),
                        formula: Formula::Not(Box::new(eq)),
                        contract_metadata: None,
                        obligation: None,
                    });
                }
                // Multi-value exact sets generate a disjunction constraint.
                // Omitted for brevity — the single-value case is most useful.
            }

            ValueSet::Range(lo, hi) => {
                // Generate: NOT (lo <= var AND var <= hi)
                // If SAT, the variable escapes its computed range.
                let var_f = Formula::Var(var_name.clone(), Sort::Int);
                let lower =
                    Formula::Ge(Box::new(var_f.clone()), Box::new(Formula::Int(i128::from(*lo))));
                let upper = Formula::Le(Box::new(var_f), Box::new(Formula::Int(i128::from(*hi))));
                let in_range = Formula::And(vec![lower, upper]);
                vcs.push(VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!("value_analysis: {var_name} in [{lo}, {hi}]"),
                    },
                    function: *fn_sym.get_or_insert_with(|| function_name.into()),
                    location: SourceSpan::default(),
                    formula: Formula::Not(Box::new(in_range)),
                    contract_metadata: None,
                    obligation: None,
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
