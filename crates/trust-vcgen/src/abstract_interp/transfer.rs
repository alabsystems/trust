// trust_vcgen/abstract_interp/transfer.rs: Transfer functions, fixpoint computation,
// threshold widening, and invariant extraction
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;

use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::*;

use super::arithmetic::*;
use super::{AbstractDomain, Interval, IntervalDomain, ThresholdSet};

// ── Transfer Functions ─────────────────────────────────────────────────────

/// Resolve an operand to an interval in the given abstract state.
fn operand_to_interval(
    op: &Operand,
    func: &VerifiableFunction,
    state: &IntervalDomain,
) -> Interval {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            let name = crate::place_to_var_name(func, place);
            state.get(&name)
        }
        Operand::Constant(cv) => match cv {
            ConstValue::Int(n) => Interval::constant(*n),
            ConstValue::Uint(n, _) => {
                if let Ok(v) = i128::try_from(*n) {
                    Interval::constant(v)
                } else {
                    Interval::TOP
                }
            }
            ConstValue::Bool(b) => Interval::constant(i128::from(*b)),
            ConstValue::Float(_) | ConstValue::Unit | ConstValue::CallableItem { .. } => {
                Interval::TOP
            }
            // Sound fallback for unknown ConstValue variants.
            _ => Interval::TOP,
        },
        // Sound fallback for unknown Operand variants.
        _ => Interval::TOP,
    }
}

/// Apply a single statement's abstract transfer function.
#[must_use]
pub fn transfer_function(
    stmt: &Statement,
    func: &VerifiableFunction,
    state: &IntervalDomain,
) -> IntervalDomain {
    let mut result = state.clone();
    if result.is_unreachable {
        return result;
    }

    match stmt {
        Statement::Assign { place, rvalue, .. } => {
            // Do not track bool-typed locals (e.g. comparison results like
            // `cond = n > 0`). Their [0,1] interval is a vacuous integer bound
            // and would be emitted as `Var(name, Int)` at the formula sink,
            // colliding with the `Var(name, Bool)` the same name carries in
            // branch guards. See `type_to_interval` for the full rationale.
            let is_bool_dest = place.projections.is_empty()
                && matches!(func.body.locals.get(place.local).map(|l| &l.ty), Some(Ty::Bool));
            if !is_bool_dest {
                let target_name = crate::place_to_var_name(func, place);
                let interval = eval_rvalue(rvalue, func, state);
                result.set(target_name, interval);
            }
        }
        Statement::Nop => {}
        _ => {}
    }
    result
}

/// Trust (P0 call-arg &mut staleness): apply a block's TERMINATOR transfer to the
/// abstract state, run AFTER every statement transfer and BEFORE propagating to
/// successors. The fixpoint previously applied only statement transfers, so the
/// CFG-edge state out of a `Call`-terminated block kept the PRE-call interval of
/// any local the callee can write — its destination AND any local whose `&mut`/
/// `&raw mut` reference (or a nested mutable pointer) escapes into the call. That
/// stale interval then discharged a safety obligation about the POST-call value:
/// e.g. `let mut i = 0; set(&mut i, 99); arr[i]` kept `i ∈ [0,0]` across
/// `set(&mut i, …)`, so the bounds check `i < 4` was proved while `i == 99` at
/// runtime (a confirmed false PROVE in DEFAULT mode for `mem::swap`/`replace`/
/// `take` and user `&mut` setters).
///
/// Havoc (forget → Top) every name the call may reassign, computed by the SAME
/// `terminator_def_names` over-approximation the formula path uses at a `Call`
/// (`mutably_borrowed_local_names ∪ mutable_pointer_local_names ∪ {dest}`), so the
/// interval lane and the SMT lane stay in lockstep. SOUNDNESS: forgetting an
/// interval can only WIDEN the abstract state (Top is the lattice identity for the
/// join), so it can only turn a PROVE into a not-proved — it can never create a
/// false proof. A by-VALUE argument and a SHARED `&`/`*const` argument are NOT in
/// the havoc set (they cannot drive a mutation), so legitimate code that passes a
/// copy or a shared borrow before indexing still proves.
#[must_use]
fn transfer_terminator(
    terminator: &Terminator,
    func: &VerifiableFunction,
    block: &BasicBlock,
    state: &IntervalDomain,
) -> IntervalDomain {
    let mut result = state.clone();
    if result.is_unreachable {
        return result;
    }
    if matches!(terminator, Terminator::Call { .. }) {
        let havoc = crate::generate::terminator_def_names(func, block);
        if !havoc.is_empty() {
            // Forget any tracked variable whose name is (prefix-)overlapped by a
            // havoced name: the local itself, its pointee `x*`, a field `x.0`, …
            result.vars.retain(|name, _| {
                !havoc.iter().any(|h| crate::generate::place_names_overlap(h, name))
            });
        }
    }
    result
}

/// Evaluate an rvalue to an interval.
fn eval_rvalue(rvalue: &Rvalue, func: &VerifiableFunction, state: &IntervalDomain) -> Interval {
    match rvalue {
        Rvalue::Use(op) => operand_to_interval(op, func, state),
        Rvalue::BinaryOp(op, lhs, rhs) | Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
            let a = operand_to_interval(lhs, func, state);
            let b = operand_to_interval(rhs, func, state);
            match op {
                BinOp::Add => interval_add(&a, &b),
                BinOp::Sub => interval_sub(&a, &b),
                BinOp::Mul => interval_mul(&a, &b),
                BinOp::Div => interval_div(&a, &b),
                BinOp::Rem => interval_rem(&a, &b),
                BinOp::Shr => interval_shr(&a, &b),
                BinOp::Shl => interval_shl(&a, &b),
                BinOp::BitAnd => interval_bitand(&a, &b),
                BinOp::BitOr => interval_bitor(&a, &b),
                // Comparisons produce boolean [0, 1].
                BinOp::Eq
                | BinOp::Ne
                | BinOp::Lt
                | BinOp::Le
                | BinOp::Gt
                | BinOp::Ge
                | BinOp::Cmp => Interval::new(0, 1),
                _ => Interval::TOP,
            }
        }
        Rvalue::UnaryOp(UnOp::Neg, op) => {
            let a = operand_to_interval(op, func, state);
            if a.is_bottom() {
                Interval::BOTTOM
            } else {
                let lo = a.hi.checked_neg();
                let hi = a.lo.checked_neg();
                match (lo, hi) {
                    (Some(lo), Some(hi)) => Interval { lo, hi },
                    _ => Interval::TOP,
                }
            }
        }
        Rvalue::Len(_) => Interval::new(0, i128::MAX),
        Rvalue::Discriminant(_) => Interval::new(0, i128::MAX),
        _ => Interval::TOP,
    }
}

// ── Widen Point Detection ──────────────────────────────────────────────────

/// A program point where widening should be applied.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct WidenPoint {
    /// Block ID of the loop header.
    pub block: BlockId,
}

/// Detect widen points (loop headers) from a function's CFG.
///
/// A loop header is the target of a back-edge: an edge from block N to
/// block M where M <= N (MIR's structured layout guarantees this).
#[must_use]
pub fn detect_widen_points(func: &VerifiableFunction) -> Vec<WidenPoint> {
    let mut headers = FxHashSet::default();
    for block in &func.body.blocks {
        for target in block.terminator.exit_targets() {
            if let ClauseTarget::Block(target_id) = target
                && target_id.0 <= block.id.0
                && target_id != block.id
            {
                headers.insert(target_id);
            }
        }
    }
    headers.into_iter().map(|block| WidenPoint { block }).collect()
}

// ── Fixpoint Computation ───────────────────────────────────────────────────

/// Extract all successor block IDs from a terminator.
///
/// Unlike `exit_targets()` which returns `ClauseTarget::Panic` for Assert
/// terminators, this extracts the actual successor block IDs needed for
/// dataflow propagation.
fn terminator_successors(term: &Terminator) -> Vec<BlockId> {
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

/// Result of fixpoint computation: abstract state at each block entry.
#[derive(Debug, Clone)]
pub struct FixpointResult {
    /// Abstract state at entry to each block.
    pub block_states: FxHashMap<BlockId, IntervalDomain>,
}

/// Compute the abstract fixpoint over a function's CFG.
///
/// Uses chaotic iteration with widening at loop headers.
/// Convergence is guaranteed by widening (finite ascending chains).
#[must_use]
pub fn fixpoint(func: &VerifiableFunction, initial: IntervalDomain) -> FixpointResult {
    let widen_points: FxHashSet<BlockId> =
        detect_widen_points(func).into_iter().map(|wp| wp.block).collect();

    let mut states: FxHashMap<BlockId, IntervalDomain> = FxHashMap::default();
    for block in &func.body.blocks {
        states.insert(block.id, IntervalDomain::bottom());
    }

    // Entry block gets the initial state.
    if let Some(first) = func.body.blocks.first() {
        states.insert(first.id, initial);
    }

    let max_iterations = func.body.blocks.len() * 20 + 100;
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

        let entry_state = states.get(&block_id).cloned().unwrap_or_else(IntervalDomain::bottom);
        if entry_state.is_unreachable {
            continue;
        }

        // Apply transfer functions for all statements in this block.
        let mut current = entry_state;
        for stmt in &block.stmts {
            current = transfer_function(stmt, func, &current);
        }
        // Trust (P0): apply the TERMINATOR transfer (a `Call` havocs its dest +
        // every `&mut`-escaped local) before propagating.
        current = transfer_terminator(&block.terminator, func, block, &current);

        // Propagate to successors.
        // exit_targets() doesn't include Assert/Call success targets
        // (they return Panic/Return), so we extract them directly.
        let successors = terminator_successors(&block.terminator);
        for succ_id in successors {
            let old = states.get(&succ_id).cloned().unwrap_or_else(IntervalDomain::bottom);
            let merged = if widen_points.contains(&succ_id) {
                old.widen(&current)
            } else {
                old.join(&current)
            };

            if merged != old {
                states.insert(succ_id, merged);
                if !worklist.contains(&succ_id) {
                    worklist.push_back(succ_id);
                }
            }
        }
    }

    FixpointResult { block_states: states }
}

/// Build a type-aware initial interval domain from a function's signature.
///
/// Initializes argument variables to their type's representable range
/// (e.g., u32 -> [0, 4294967295]), giving the abstract interpretation
/// much tighter starting bounds than Top. Additionally, declared
/// preconditions on parameters (e.g. `a <= 1000`) are folded into the
/// initial state so nonlinear safety obligations (in particular
/// multiplication) become decidable from the abstract state alone.
#[must_use]
pub fn type_aware_initial_state(func: &VerifiableFunction) -> IntervalDomain {
    let mut state = IntervalDomain::top();
    for (i, local) in func.body.locals.iter().enumerate() {
        // Skip return slot (index 0) and non-argument locals.
        if i == 0 || i > func.body.arg_count {
            continue;
        }
        let name = local.name.clone().unwrap_or_else(|| format!("_{i}"));
        if let Some(interval) = type_to_interval(&local.ty) {
            state.set(name, interval);
        }
    }

    // Refine using declared preconditions (e.g. `a <= 1000`,
    // `idx < len`, `divisor != 0`). Each refinement intersects the
    // existing interval with whatever bound the precondition exposes
    // about a single named variable; conjunctions are handled
    // recursively so multi-clause preconditions all contribute.
    for pre in &func.preconditions {
        refine_state_with_precondition(&mut state, pre);
    }

    state
}

/// Walk a precondition formula and tighten the abstract state for each
/// named integer-typed variable bound the formula exposes.
///
/// Handles the shapes the scale fixture and friends use directly:
/// `var <= lit`, `var < lit`, `var >= lit`, `var > lit`, `var != lit`,
/// `0 <= var`, conjunctions, and the same patterns with the literal on
/// the left-hand side. Unrecognized shapes are ignored — they remain
/// available as a hypothesis on each VC.
fn refine_state_with_precondition(state: &mut IntervalDomain, formula: &Formula) {
    match formula {
        Formula::And(conjuncts) => {
            for c in conjuncts {
                refine_state_with_precondition(state, c);
            }
        }
        Formula::Le(lhs, rhs) => {
            if let (Some(name), Some(v)) = (var_name(lhs), int_const(rhs)) {
                intersect(state, &name, Interval::new(i128::MIN, v));
            } else if let (Some(v), Some(name)) = (int_const(lhs), var_name(rhs)) {
                intersect(state, &name, Interval::new(v, i128::MAX));
            }
        }
        Formula::Lt(lhs, rhs) => {
            if let (Some(name), Some(v)) = (var_name(lhs), int_const(rhs)) {
                intersect(state, &name, Interval::new(i128::MIN, v.saturating_sub(1)));
            } else if let (Some(v), Some(name)) = (int_const(lhs), var_name(rhs)) {
                intersect(state, &name, Interval::new(v.saturating_add(1), i128::MAX));
            }
        }
        Formula::Ge(lhs, rhs) => {
            if let (Some(name), Some(v)) = (var_name(lhs), int_const(rhs)) {
                intersect(state, &name, Interval::new(v, i128::MAX));
            } else if let (Some(v), Some(name)) = (int_const(lhs), var_name(rhs)) {
                intersect(state, &name, Interval::new(i128::MIN, v));
            }
        }
        Formula::Gt(lhs, rhs) => {
            if let (Some(name), Some(v)) = (var_name(lhs), int_const(rhs)) {
                intersect(state, &name, Interval::new(v.saturating_add(1), i128::MAX));
            } else if let (Some(v), Some(name)) = (int_const(lhs), var_name(rhs)) {
                intersect(state, &name, Interval::new(i128::MIN, v.saturating_sub(1)));
            }
        }
        Formula::Not(inner) => {
            // Handle `!(var == c)` so divisor != 0 still tightens away the
            // single excluded point; intervals can't represent holes, so we
            // can only refine when one half of the excluded point sits
            // outside the current bound. We leave the generic case alone.
            if let Formula::Eq(lhs, rhs) = inner.as_ref() {
                let pair = match (var_name(lhs), int_const(rhs)) {
                    (Some(name), Some(v)) => Some((name, v)),
                    _ => match (var_name(rhs), int_const(lhs)) {
                        (Some(name), Some(v)) => Some((name, v)),
                        _ => None,
                    },
                };
                if let Some((name, v)) = pair {
                    let current = state.get(&name);
                    if current.lo == v {
                        intersect(state, &name, Interval::new(v.saturating_add(1), i128::MAX));
                    } else if current.hi == v {
                        intersect(state, &name, Interval::new(i128::MIN, v.saturating_sub(1)));
                    }
                }
            }
        }
        _ => {}
    }
}

/// Return the variable name of a simple `Formula::Var` (any sort).
fn var_name(formula: &Formula) -> Option<String> {
    match formula {
        Formula::Var(name, _) => Some(name.to_string()),
        Formula::SymVar(name, _) => Some(name.as_str().to_string()),
        _ => None,
    }
}

/// Return the integer literal value of a simple `Formula::Int`/`Formula::UInt`.
fn int_const(formula: &Formula) -> Option<i128> {
    match formula {
        Formula::Int(v) => Some(*v),
        Formula::UInt(v) => i128::try_from(*v).ok(),
        _ => None,
    }
}

/// Intersect the interval already stored for `name` with `bound`.
fn intersect(state: &mut IntervalDomain, name: &str, bound: Interval) {
    let current = state.get(name);
    let next = current.meet(&bound);
    state.set(name.to_string(), next);
}

/// Convert a type to its representable interval.
///
/// Returns `None` for non-numeric types, including `bool`. A bool's `[0,1]`
/// range is a vacuous integer bound (every bool already satisfies it) and is
/// never consumed by integer arithmetic — Rust requires an explicit cast,
/// which produces a fresh integer local. Tracking bools here only created a
/// sort conflict at the formula sink: the same name would surface as
/// `Var(name, Int)` from the emitted `[0,1]` bound *and* as `Var(name, Bool)`
/// in branch guards, breaking the SMT backend (a Goal-1 false-fail). So bools
/// are intentionally not tracked in the interval domain.
#[must_use]
pub fn type_to_interval(ty: &Ty) -> Option<Interval> {
    match ty {
        // Raw pointers are non-negative addresses.
        Ty::RawPtr { .. } => Some(Interval::new(0, i128::MAX)),
        Ty::Int { width, signed: true } => {
            if *width == 128 {
                Some(Interval::new(i128::MIN, i128::MAX))
            } else if *width > 0 && *width < 128 {
                let half = 1i128 << (width - 1);
                Some(Interval::new(-half, half - 1))
            } else {
                None
            }
        }
        Ty::Int { width, signed: false } => {
            if *width == 128 {
                // u128::MAX doesn't fit in i128, so use i128::MAX as conservative bound.
                Some(Interval::new(0, i128::MAX))
            } else if *width > 0 && *width < 128 {
                Some(Interval::new(0, (1i128 << width) - 1))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Extract threshold constants from a function's CFG.
///
/// Sources:
/// 1. SwitchInt target values (loop bounds, enum discriminants).
/// 2. Constants in comparison operands from Assign statements involving
///    Lt/Le/Gt/Ge/Eq BinOps.
/// 3. Type bounds (0, type_min, type_max) for each integer type in the
///    function's locals.
///
/// Always includes 0 as a threshold (common loop start).
#[must_use]
pub fn extract_thresholds(func: &VerifiableFunction) -> ThresholdSet {
    let mut values = Vec::new();

    // Always include 0.
    values.push(0);

    // Source 1: SwitchInt target values.
    for block in &func.body.blocks {
        if let Terminator::SwitchInt { targets, .. } = &block.terminator {
            for (val, _) in targets {
                if let Ok(v) = i128::try_from(*val) {
                    values.push(v);
                    // Adjacent thresholds for off-by-one precision.
                    values.push(v.saturating_sub(1));
                    values.push(v.saturating_add(1));
                }
            }
        }
    }

    // Source 2: Constants in comparison operands (BinOp comparisons in Assign).
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue, .. } = stmt {
                extract_comparison_constants(rvalue, &mut values);
            }
        }
    }

    // Source 3: Type bounds from locals.
    for local in &func.body.locals {
        if let Some(interval) = type_to_interval(&local.ty) {
            if interval.lo != i128::MIN {
                values.push(interval.lo);
            }
            if interval.hi != i128::MAX {
                values.push(interval.hi);
            }
        }
    }

    ThresholdSet::new(values)
}

/// Extract constants from comparison rvalues.
fn extract_comparison_constants(rvalue: &Rvalue, values: &mut Vec<i128>) {
    match rvalue {
        Rvalue::BinaryOp(op, lhs, rhs) | Rvalue::CheckedBinaryOp(op, lhs, rhs)
            if matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq) =>
        {
            // Extract constant from RHS of comparison.
            if let Operand::Constant(cv) = rhs {
                extract_const_value(cv, values, true);
            }
            // Also extract constant from LHS.
            if let Operand::Constant(cv) = lhs {
                extract_const_value(cv, values, false);
            }
        }
        _ => {}
    }
}

/// Extract a numeric constant into the threshold values list.
/// If `with_neighbors` is true, also adds value-1 and value+1.
fn extract_const_value(cv: &ConstValue, values: &mut Vec<i128>, with_neighbors: bool) {
    let v = match cv {
        ConstValue::Int(n) => Some(*n),
        ConstValue::Uint(n, _) => i128::try_from(*n).ok(),
        _ => None,
    };
    if let Some(v) = v {
        values.push(v);
        if with_neighbors {
            values.push(v.saturating_sub(1));
            values.push(v.saturating_add(1));
        }
    }
}

// ── Configured Fixpoint ──────────────────────────────────────────────────

/// Configuration for abstract interpretation fixpoint computation.
#[derive(Debug, Clone)]
pub struct FixpointConfig {
    /// Number of join iterations before widening kicks in at each loop header.
    /// Default: 3.
    pub widen_delay: usize,
    /// Number of descending narrowing passes after widening converges.
    /// Default: 3.
    pub narrowing_passes: usize,
    /// Optional threshold set for threshold widening.
    pub thresholds: Option<ThresholdSet>,
}

impl Default for FixpointConfig {
    fn default() -> Self {
        Self { widen_delay: 3, narrowing_passes: 3, thresholds: None }
    }
}

impl FixpointConfig {
    /// Create config with auto-extracted thresholds from the function.
    #[must_use]
    pub fn for_function(func: &VerifiableFunction) -> Self {
        Self { thresholds: Some(extract_thresholds(func)), ..Self::default() }
    }
}

/// Compute successor states with condition narrowing from SwitchInt.
///
/// For SwitchInt terminators:
///   - Match arms: narrow the discriminant variable to [value, value].
///   - Otherwise arm: narrow the discriminant to exclude all match values.
///
/// For all other terminators: propagate the state unchanged.
pub(crate) fn compute_successor_states(
    terminator: &Terminator,
    func: &VerifiableFunction,
    state: &IntervalDomain,
) -> Vec<(BlockId, IntervalDomain)> {
    match terminator {
        Terminator::SwitchInt { discr, targets, otherwise, .. } => {
            let mut successors = Vec::new();

            // Each match arm: discr == value.
            for (value, block_id) in targets {
                let narrowed = narrow_from_condition(state, func, discr, *value);
                successors.push((*block_id, narrowed));
            }

            // Otherwise arm: discr != any target value.
            let otherwise_state = narrow_from_otherwise(state, func, discr, targets);
            successors.push((*otherwise, otherwise_state));

            successors
        }
        Terminator::Assert { target, .. } => {
            // Propagate state to the success target.
            vec![(*target, state.clone())]
        }
        _ => {
            // All other terminators: propagate unchanged.
            terminator_successors(terminator).into_iter().map(|id| (id, state.clone())).collect()
        }
    }
}

/// Narrow state for the SwitchInt otherwise branch.
///
/// If the discriminant is a single variable, exclude all target values.
/// For a discriminant with interval [lo, hi] and excluded values {v1, ..., vn}:
///   - If excluded values are at the bottom of the range, raise lo.
///   - If excluded values are at the top of the range, lower hi.
///   - Otherwise, the narrowing is imprecise (intervals can't represent gaps).
#[must_use]
pub(crate) fn narrow_from_otherwise(
    state: &IntervalDomain,
    func: &VerifiableFunction,
    discr: &Operand,
    targets: &[(u128, BlockId)],
) -> IntervalDomain {
    let mut result = state.clone();
    if let Operand::Copy(place) | Operand::Move(place) = discr {
        let name = crate::place_to_var_name(func, place);
        let current = result.get(&name);
        if current.is_bottom() {
            return result;
        }

        // Collect excluded values.
        let mut excluded: Vec<i128> =
            targets.iter().filter_map(|(v, _)| i128::try_from(*v).ok()).collect();
        excluded.sort_unstable();

        if excluded.is_empty() {
            return result;
        }

        // Tighten bounds if excluded values are at the edges.
        let mut lo = current.lo;
        let mut hi = current.hi;
        for &v in &excluded {
            if v == lo {
                lo = lo.saturating_add(1);
            } else {
                break;
            }
        }
        for &v in excluded.iter().rev() {
            if v == hi {
                hi = hi.saturating_sub(1);
            } else {
                break;
            }
        }

        if lo > hi {
            result.set(name, Interval::BOTTOM);
        } else {
            result.set(name, Interval::new(lo, hi));
        }
    }
    result
}

/// Apply descending narrowing passes to a fixpoint result.
fn apply_narrowing_pass(
    func: &VerifiableFunction,
    result: &mut FixpointResult,
    widen_points: &FxHashSet<BlockId>,
    max_passes: usize,
) {
    for _ in 0..max_passes {
        let mut changed = false;
        for block in &func.body.blocks {
            let entry_state =
                result.block_states.get(&block.id).cloned().unwrap_or_else(IntervalDomain::bottom);
            if entry_state.is_unreachable {
                continue;
            }
            let mut current = entry_state;
            for stmt in &block.stmts {
                current = transfer_function(stmt, func, &current);
            }
            // Trust (P0): terminator transfer (Call havocs dest + &mut-escaped locals).
            current = transfer_terminator(&block.terminator, func, block, &current);
            let successors = terminator_successors(&block.terminator);
            for succ_id in successors {
                let old = result
                    .block_states
                    .get(&succ_id)
                    .cloned()
                    .unwrap_or_else(IntervalDomain::bottom);
                let narrowed = if widen_points.contains(&succ_id) {
                    old.narrow(&current)
                } else {
                    old.join(&current)
                };
                if narrowed != old {
                    result.block_states.insert(succ_id, narrowed);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
}

/// Compute the abstract fixpoint with threshold widening, delayed widening,
/// descending narrowing, and condition narrowing.
///
/// This is the full-featured replacement for `fixpoint()` and
/// `fixpoint_with_narrowing()`.
#[must_use]
pub fn fixpoint_configured(
    func: &VerifiableFunction,
    initial: IntervalDomain,
    config: &FixpointConfig,
) -> FixpointResult {
    let widen_points: FxHashSet<BlockId> =
        detect_widen_points(func).into_iter().map(|wp| wp.block).collect();

    let mut states: FxHashMap<BlockId, IntervalDomain> = FxHashMap::default();
    for block in &func.body.blocks {
        states.insert(block.id, IntervalDomain::bottom());
    }
    if let Some(first) = func.body.blocks.first() {
        states.insert(first.id, initial);
    }

    // Per-block iteration count for delayed widening.
    let mut block_iterations: FxHashMap<BlockId, usize> = FxHashMap::default();

    let max_iterations = func.body.blocks.len() * 20 + 100;
    let mut worklist: VecDeque<BlockId> = func.body.blocks.iter().map(|b| b.id).collect();
    let mut iteration = 0;

    // Phase 1: Ascending iteration with (threshold + delayed) widening.
    while let Some(block_id) = worklist.pop_front() {
        iteration += 1;
        if iteration > max_iterations {
            break;
        }

        let Some(block) = func.body.blocks.iter().find(|b| b.id == block_id) else {
            continue;
        };

        let entry_state = states.get(&block_id).cloned().unwrap_or_else(IntervalDomain::bottom);
        if entry_state.is_unreachable {
            continue;
        }

        // Transfer through statements.
        let mut current = entry_state;
        for stmt in &block.stmts {
            current = transfer_function(stmt, func, &current);
        }
        // Trust (P0): apply the TERMINATOR transfer (a `Call` havocs its dest +
        // every `&mut`-escaped local) before propagating, so a post-call read does
        // not inherit the stale pre-call interval.
        current = transfer_terminator(&block.terminator, func, block, &current);

        // Propagate to successors with condition narrowing.
        let successor_states = compute_successor_states(&block.terminator, func, &current);
        for (succ_id, succ_state) in successor_states {
            let old = states.get(&succ_id).cloned().unwrap_or_else(IntervalDomain::bottom);

            let count = block_iterations.entry(succ_id).or_insert(0);
            *count += 1;

            let merged = if widen_points.contains(&succ_id) && *count > config.widen_delay {
                // Threshold widening (or plain widening if no thresholds).
                match &config.thresholds {
                    Some(ts) => old.widen_with_thresholds(&succ_state, ts),
                    None => old.widen(&succ_state),
                }
            } else {
                old.join(&succ_state)
            };

            if merged != old {
                states.insert(succ_id, merged);
                if !worklist.contains(&succ_id) {
                    worklist.push_back(succ_id);
                }
            }
        }
    }

    let mut result = FixpointResult { block_states: states };

    // Phase 2: Descending narrowing.
    if config.narrowing_passes > 0 && !widen_points.is_empty() {
        apply_narrowing_pass(func, &mut result, &widen_points, config.narrowing_passes);
    }

    result
}

/// Compute fixpoint with a narrowing pass for precision recovery.
///
/// This is the backward-compatible entry point. New code should prefer
/// `fixpoint_configured()` with `FixpointConfig::for_function()`.
///
/// Now delegates to `fixpoint_configured()` with threshold widening,
/// delayed widening, and condition narrowing from SwitchInt.
#[must_use]
pub fn fixpoint_with_narrowing(
    func: &VerifiableFunction,
    initial: IntervalDomain,
    narrow_iterations: usize,
) -> FixpointResult {
    let config = FixpointConfig {
        widen_delay: 3,
        narrowing_passes: narrow_iterations,
        thresholds: Some(extract_thresholds(func)),
    };
    fixpoint_configured(func, initial, &config)
}

// ── Invariant Extraction ───────────────────────────────────────────────────

/// Extract loop invariant formulas from fixpoint results.
///
/// For each variable with a finite interval at a loop header, generates
/// bound constraints: `lo <= var` and `var <= hi`.
#[must_use]
pub fn extract_invariants(result: &FixpointResult, func: &VerifiableFunction) -> Vec<Formula> {
    let widen_points: FxHashSet<BlockId> =
        detect_widen_points(func).into_iter().map(|wp| wp.block).collect();

    let mut invariants = Vec::new();

    for block_id in &widen_points {
        let Some(state) = result.block_states.get(block_id) else {
            continue;
        };
        if state.is_unreachable {
            continue;
        }

        for (var_name, interval) in &state.vars {
            if interval.is_bottom() {
                continue;
            }
            let var_formula = Formula::Var(var_name.clone(), Sort::Int);

            // Lower bound: lo <= var
            if interval.lo != i128::MIN {
                invariants.push(Formula::Ge(
                    Box::new(var_formula.clone()),
                    Box::new(Formula::Int(interval.lo)),
                ));
            }

            // Upper bound: var <= hi
            if interval.hi != i128::MAX {
                invariants
                    .push(Formula::Le(Box::new(var_formula), Box::new(Formula::Int(interval.hi))));
            }
        }
    }

    invariants
}

// ── Narrowing Conditions ───────────────────────────────────────────────────

/// Narrow an interval domain based on a branch condition being true.
///
/// For comparisons like `x < 10`, narrows x's interval to [lo, 9].
#[must_use]
fn narrow_from_condition(
    state: &IntervalDomain,
    func: &VerifiableFunction,
    discr: &Operand,
    value: u128,
) -> IntervalDomain {
    let mut result = state.clone();
    if let Operand::Copy(place) | Operand::Move(place) = discr {
        let name = crate::place_to_var_name(func, place);
        if let Ok(v) = i128::try_from(value) {
            result.set(name, Interval::constant(v));
        }
    }
    result
}
