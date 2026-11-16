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
// Trust (2026-10-02, trust-fixpoint-deadline): the fixpoint under the ambient budget.
#[cfg(test)]
mod budget_tests;
// Trust (2026-10-04, trust-interval-drop-havoc): the transfer at `Drop` and `Opaque`.
#[cfg(test)]
mod drop_havoc_tests;
// Trust (2026-10-08, trust-interval-drop-havoc): the statement transfer at a statement
// that writes more than its own destination.
#[cfg(test)]
mod stmt_write_tests;
// Trust (2026-10-09, trust-interval-drop-havoc): the whole-function environment at
// every statement, not only at block entries.
#[cfg(test)]
mod statement_point_tests;
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
///
/// WHAT IT CLAIMS: a bound it carries for a name holds at every program point at
/// which that name is a value — every block entry and every point between two
/// statements. The discharge reads it for a name at any version on that footing.
pub(crate) fn merged_interval_environment(
    func: &trust_types::VerifiableFunction,
) -> IntervalDomain {
    merged_interval_environments(func).1
}

/// Trust (2026-10-10): the function-wide environment WITHOUT and WITH
/// [`narrow_single_assignments_to_their_def`], from one fixpoint. The second is the
/// production environment ([`merged_interval_environment`]); the discharge pre-pass
/// also asks the first which rows it would have discharged before the narrowing, so
/// the narrowing changes which FACTS a row carries and never which LANE decides it
/// (see `generate::discharge_body_vcs`).
pub(crate) fn merged_interval_environments(
    func: &trust_types::VerifiableFunction,
) -> (IntervalDomain, IntervalDomain) {
    let initial = type_aware_initial_state(func);
    // PERF-COMPILER-VCGEN-769: skip `extract_thresholds` when the CFG is acyclic
    // (`detect_widen_points` is empty, so `config.thresholds` is never consulted).
    let (fixpoint, mut havoc) = transfer::fixpoint_for_function_indexed(func, initial);

    // The ENTRY block contributes nothing about a local that is not yet a value
    // there, and joining it in only widens what every other block knows.
    //
    // At function entry a local that is neither the return slot nor an argument
    // holds no value, and valid MIR cannot read one before its first
    // definition, so its entry interval describes no reachable state. Its only
    // effect on the join is to erase real knowledge: measured on
    // `loop { r += 1; if r > 5 { break; } }`, every block including the loop
    // head bounds the counter by the break test, and the entry block's
    // type-range interval for the not-yet-assigned counter was the single
    // reason that bound did not survive into the environment the discharge
    // consumes.
    //
    // SOUNDNESS: the environment is used to discharge and to augment
    // obligations at program points. Excluding a contribution that describes no
    // reachable state cannot make the environment claim anything untrue at any
    // point where the local IS a value. Arguments and the return slot keep
    // their entry contribution, and every other block contributes unchanged.
    let entry_id = fixpoint_entry_block_id(func);
    // PERF-COMPILER-VCGEN-771: materialize `locals_undefined_at_entry(func)` lazily
    // only when `func` has non-argument locals and the entry block is reachable with
    // a non-empty environment (or when the test differential check runs).
    let has_non_arg_locals = func.body.locals.len() > func.body.arg_count.saturating_add(1);
    let undefined_at_entry: std::cell::OnceCell<trust_types::fx::FxHashSet<String>> =
        std::cell::OnceCell::new();

    let mut merged = IntervalDomain::bottom();
    for (id, state) in &fixpoint.block_states {
        if Some(*id) == entry_id {
            continue;
        }
        merged.join_in_place(state);
    }
    // Fold the entry block in key by key, skipping only the locals it cannot
    // describe. When the entry block is the ONLY state (a straight-line body
    // with one block) this is the whole environment, so it must still run.
    if let Some(entry_id) = entry_id
        && let Some(entry_state) = fixpoint.block_states.get(&entry_id)
        && !entry_state.is_unreachable
    {
        if merged.is_unreachable {
            merged = entry_state.clone();
            if has_non_arg_locals && !merged.vars.is_empty() {
                for name in undefined_at_entry.get_or_init(|| locals_undefined_at_entry(func)) {
                    merged.vars.remove(name);
                }
            }
        } else if !merged.vars.is_empty() {
            let undefined = has_non_arg_locals
                .then(|| undefined_at_entry.get_or_init(|| locals_undefined_at_entry(func)));
            merged.vars.retain(|key, interval| {
                if undefined.is_some_and(|set| set.contains(key)) {
                    return true;
                }
                let joined = interval.join(&entry_state.get(key));
                if joined == Interval::TOP {
                    false
                } else {
                    *interval = joined;
                    true
                }
            });
        }
    }
    // Trust (2026-10-09, trust-interval-drop-havoc, independent review): the join
    // above covers every block ENTRY, and the discharge reads the result for a name
    // at ANY of its versions (`discharge::interval_for_var`). A value written and
    // overwritten between two statements of one block is no block's entry state, so
    // the statements' own values are joined in too. Until this, `let mut a = 1; let
    // mut b = 0; let t = a; a = b; b = t; k / a` had its division by zero discharged
    // at generation: the environment said `b ∈ [1, 1]` of the read of `b` that copied
    // 0 (review probes `e02`, `e03`). See `transfer::join_statement_values`.
    transfer::join_statement_values(&mut havoc, &fixpoint, &mut merged);
    retain_int_sorted_locals(func, &mut merged);
    #[cfg(test)]
    if crate::generate::differential_enabled() && !merged.is_unreachable && !merged.vars.is_empty()
    {
        transfer::assert_environment_bounds_every_statement_point(
            func,
            &fixpoint,
            &merged,
            entry_id,
            undefined_at_entry.get_or_init(|| locals_undefined_at_entry(func)),
        );
    }
    // FAIL CLOSED on an empty bound. `interval_domain_to_formula` spells an environment
    // with an EMPTY entry as `false`, and `false` conjoined onto an obligation proves
    // it. That is how main proved `let y = i32::MIN; -y` (review-round probe `q01`: the
    // negation check's success edge leaves its operand no value, and before the
    // statement-point join that edge was the only state the environment had for it).
    // The join above gives every written name the value its statement leaves, and the
    // check just above asserts under `cfg(test)` that no environment a test computes
    // has an empty entry left. This line is for the shape no test has: an entry that
    // nothing gives a value bounds nothing, so it is dropped, which only weakens.
    merged.vars.retain(|_, bound| !bound.is_bottom());
    // Trust (2026-10-10, local; merge 2026-10-14): the def-site narrowing runs on the
    // finished environment, through the same lockstep statement walk the fixpoint and
    // the statement-point join use (`transfer::state_after_statement`).
    let mut narrowed = merged.clone();
    narrow_single_assignments_to_their_def(func, &fixpoint, &mut havoc, &mut narrowed);
    narrowed.vars.retain(|_, bound| !bound.is_bottom());
    // A trip inside the statement walk's own helpers (they poll too) is seen here,
    // as at the end of the fixpoint: the environment of a run any trip touched
    // bounds nothing.
    if trust_types::verify_budget::exhausted_readonly() {
        merged.vars.clear();
        narrowed.vars.clear();
    }
    (merged, narrowed)
}

/// Trust (2026-10-10): a local with exactly one whole-local STATEMENT def and no
/// mutable alias (`local_defs::unique_value_def`) holds, at every point where it is a
/// value, a value that def produced; so the interval the transfer gives it right after
/// that statement (from the fixpoint state at its block's entry) bounds every value it
/// ever holds. The join above also folds in blocks where the local holds no value yet,
/// and those carry the type-range seed of the initial state forward: the add temp
/// `_10 = copy s` of `s = (s + b) & 0xffff` in a loop was `[0, u32::MAX]` in the
/// environment while its def site read `[0, 0xffff]` (sweep p21). Meeting the two
/// keeps both sound claims.
///
/// A name two locals share is skipped: the meet would apply one local's def to the
/// other.
fn narrow_single_assignments_to_their_def(
    func: &trust_types::VerifiableFunction,
    fixpoint: &FixpointResult,
    havoc: &mut transfer::CallHavoc<'_>,
    merged: &mut IntervalDomain,
) {
    // Trust (2026-10-10, review round 118): an `Opaque` terminator (inline assembly)
    // writes places no statement names (an `asm!` output operand), so a local
    // `unique_value_def` reads as single-assignment may hold a value its def did not
    // produce: `let mut x = 1; asm!(.., inout(reg) x, ..); 100 / x` met `x` back to
    // `[1, 1]` after the terminator transfer had forgotten it.
    let non_arg_start = func.body.arg_count.saturating_add(1);
    if merged.is_unreachable
        || merged.vars.is_empty()
        || func.body.locals.len() <= non_arg_start
        || !func.body.locals[non_arg_start..]
            .iter()
            .any(|decl| type_to_interval(&decl.ty).is_some())
    {
        return;
    }
    // PERF-COMPILER-VCGEN-713: ensure a `FuncAnalysisScope` is bound to `func` so
    // `terminator_presence_for`, `unique_value_def`, and `unique_defining_block` use
    // the indexed per-function tables instead of scanning the body per local.
    let _analysis_scope = crate::generate::FuncAnalysisScope::enter_if_unbound(func);
    if crate::generate::terminator_presence_for(func).has_opaque {
        return;
    }
    // PERF-COMPILER-VCGEN-772: gate local-name uniqueness materialization behind the
    // O(1) `type_to_interval`, `unique_value_def`, `unique_defining_block`, reachable
    // block-entry, and statement-position checks so bodies with no eligible single-def
    // integer local never allocate `local_var_name` strings or a uniqueness map.
    let unique_names: std::cell::OnceCell<Vec<(String, bool)>> = std::cell::OnceCell::new();
    for (offset, decl) in func.body.locals[non_arg_start..].iter().enumerate() {
        let local = non_arg_start + offset;
        let Some(range) = type_to_interval(&decl.ty) else {
            continue;
        };
        if crate::local_defs::unique_value_def(func, local).is_none() {
            continue;
        }
        let Some(pos) = crate::local_defs::unique_defining_block(func, local) else {
            continue;
        };
        let Some(block) = func.body.blocks.get(pos) else {
            continue;
        };
        let Some(entry) = fixpoint.block_states.get(&block.id) else {
            continue;
        };
        if entry.is_unreachable {
            continue;
        }
        let Some(def_at) = block.stmts.iter().position(|stmt| {
            matches!(stmt, trust_types::Statement::Assign { place, .. }
                if place.local == local && place.projections.is_empty())
        }) else {
            continue;
        };
        let names = unique_names.get_or_init(|| {
            let raw: Vec<String> =
                func.body.locals.iter().map(|d| crate::local_var_name(func, d)).collect();
            let unique_flags: Vec<bool> = {
                let mut seen: trust_types::fx::FxHashSet<&str> =
                    trust_types::fx::FxHashSet::with_capacity_and_hasher(
                        raw.len(),
                        Default::default(),
                    );
                let mut dup: trust_types::fx::FxHashSet<&str> =
                    trust_types::fx::FxHashSet::default();
                for n in &raw {
                    if !seen.insert(n.as_str()) {
                        dup.insert(n.as_str());
                    }
                }
                raw.iter().map(|n| !dup.contains(n.as_str())).collect()
            };
            raw.into_iter().zip(unique_flags).collect()
        });
        let Some((name, true)) = names.get(local) else {
            continue;
        };
        // Merge 2026-10-14: the state after the def comes from the LOCKSTEP walk
        // (`transfer_function` AND each statement's extra writes, `StmtWrite`), never
        // from `transfer_function` alone, which keeps an interval an earlier opaque
        // store of the block may have changed.
        let Some(state) = transfer::state_after_statement(havoc, pos, block, entry.clone(), def_at)
        else {
            continue;
        };
        if state.is_unreachable {
            continue;
        }
        // Merge 2026-10-14: the def-site value narrows only where the statement-point join
        // takes it as evidence about a value of the local's type
        // (`transfer::value_is_evidence_of_type`, the rule of `as_value_of_type`). A
        // FINITE bound past the type is a mathematical result the machine value need not
        // have, which that join replaces by the whole range (upstream a93c8b2409a);
        // meeting it back in here re-admitted it: `t = copy p.0` under `requires -5 <=
        // p.0 <= 3` narrowed the `u32` `t` to `[-5, 3]`
        // (`statement_point_tests::a_one_sided_bound_survives_the_join_and_a_bound_past_the_type_does_not`).
        // An unbounded side constrains nothing, so a one-sided value still narrows by its
        // finite side. Skipping only keeps the wider environment.
        let def_value = state.get(name);
        if !transfer::value_is_evidence_of_type(&def_value, &range) {
            continue;
        }
        let narrowed = merged.get(name).meet(&def_value);
        if narrowed.is_bottom() {
            continue;
        }
        if narrowed == Interval::TOP {
            merged.vars.remove(name);
        } else {
            merged.vars.insert(name.clone(), narrowed);
        }
    }
}

/// Drop every environment entry that names a local the interval domain does not
/// model as an Int-sorted scalar (`type_to_interval` is `None`: a tuple, a
/// `bool`, an ADT, ...).
///
/// The domain tracks such locals internally for its own transfer — a
/// `CheckedBinaryOp` result TUPLE carries the interval of its unwrapped
/// arithmetic result so a later `_k.0` read can see it — but
/// `interval_domain_to_formula` exports every entry as `Var(name, Int)`. For a
/// tuple local that fact names no formula term (the checked result is the
/// separate place `_k.0`), states the UNWRAPPED range (`i32` `x + 1` exported
/// `_4 in [2, 2147483648]`, past `i32::MAX`), and gives the local a second,
/// Int sort beside any formula that reads it whole — the ill-sorted-goal
/// hazard the bitvector guard in `augment_vc_with_abstract_state` refuses for
/// the same reason. Removing an entry only weakens the environment, so this can
/// cost a discharge and never create one.
fn retain_int_sorted_locals(func: &trust_types::VerifiableFunction, env: &mut IntervalDomain) {
    if env.vars.is_empty() {
        return;
    }
    for local in &func.body.locals {
        if type_to_interval(&local.ty).is_none() {
            env.vars.remove(&crate::local_var_name(func, local));
            if env.vars.is_empty() {
                break;
            }
        }
    }
}

/// The block id the fixpoint seeds with the initial state.
fn fixpoint_entry_block_id(func: &trust_types::VerifiableFunction) -> Option<trust_types::BlockId> {
    func.body.blocks.first().map(|b| b.id)
}

/// The abstract-state names of locals that hold NO value at function entry:
/// everything but the return slot and the arguments. Named as the transfer
/// functions name them (`crate::local_var_name`): under the source name a
/// reserved or shadowed local was never recognised here, so its entry
/// contribution was joined in after all.
fn locals_undefined_at_entry(
    func: &trust_types::VerifiableFunction,
) -> trust_types::fx::FxHashSet<String> {
    let cap = func.body.locals.len().saturating_sub(func.body.arg_count + 1);
    let mut set = trust_types::fx::FxHashSet::with_capacity_and_hasher(cap, Default::default());
    for (i, local) in func.body.locals.iter().enumerate() {
        if i != 0 && i > func.body.arg_count {
            set.insert(crate::local_var_name(func, local));
        }
    }
    set
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
