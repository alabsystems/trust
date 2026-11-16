// trust-router/disjoint_components.rs: the variable-disjoint conjunctive
// component split shared by every ay-facing backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Trust: DISJOINT-COMPONENT REFUTATION (2026-08-20) — split a top-level
//! conjunction into groups of conjuncts that share no free variable, so a
//! query ay cannot dispatch AS A WHOLE can still be REFUTED component-wise.
//!
//! WHY THIS EXISTS. A violation formula routinely mixes theories over
//! DISJOINT variable sets — the canonical case is an unsigned `var*var` mul,
//! whose BV overflow predicate is over fresh `__trust_ovf_bv_*` bitvector
//! vars while the operand range/definition facts are over the program's own
//! `Sort::Int` locals. ay has no combined decision procedure for some such
//! mixtures (measured: the QF_BV + NIA shape) and answers them `incomplete`,
//! phase `theory-combination`, with its executor refusal ("unsupported logic:
//! …") as the detail (`internal-error` before ay's AD1 fix, f0bb8f9368). A
//! whole-query Unknown throws away a refutation each component would have
//! produced. Since a conjunction of
//! PAIRWISE VARIABLE-DISJOINT components is satisfiable iff EVERY component
//! is satisfiable — models over disjoint symbol sets compose — refuting each
//! component refutes the conjunction, and the union of the component models
//! is a model of the whole.
//!
//! SOUNDNESS, and why this path can only ever say `Failed`:
//!
//!   * **Variable-disjoint is NOT symbol-disjoint, and that distinction is
//!     the whole soundness argument.** `build_program` declares a query's
//!     signature from THREE walkers — `collect_free_vars`,
//!     `collect_pred_symbols` (uninterpreted predicates via `declare_fun`),
//!     and `visit_datatype_bearing_sorts`. A union-find over VARIABLES alone
//!     is blind to the other two, and the composition is then FALSE: for
//!     `And([x=1, p(x), y=1, ¬p(y)])` the variable partition is `{x}`/`{y}`,
//!     each component is satisfiable, and the conjunction is
//!     `p(1) ∧ ¬p(1)` — UNSAT. Composing those models reports `Failed` with a
//!     fabricated witness for an obligation that HOLDS: a build error on
//!     correct code, which breaks the "all valid Rust compiles" gate. (Ground
//!     conjuncts make it worse: two conjuncts with NO free variables are
//!     never linked at all, so `p(0)` and `¬p(0)` split by construction.)
//!     This lane therefore admits only a fragment in which the two notions
//!     COINCIDE: no uninterpreted predicate or function symbol, no
//!     datatype/uninterpreted sort, no quantifier, and every free variable at
//!     a concrete theory sort. Anything else fails closed to `None`.
//!
//!     The same direction was refused elsewhere in-repo for exactly this
//!     reason: `trust_cache::sub_query_splitter::combine_results` (at
//!     `3a1cb55f071`; T11 deleted it as dead, 2026-10-16) composed only
//!     `UNSAT -> Proved` and never `SAT -> Failed` ("the current dependency
//!     analysis does not track every semantic symbol (for example
//!     uninterpreted predicate identities)"), pinned by its
//!     `contradictory_predicate_partitions_cannot_synthesize_failed`. The
//!     fragment gate below is what earns this lane the composition that
//!     splitter declined to make in general.
//!   * Within that fragment the grouping is still a union-find over the free
//!     variable sets computed by the SAME walker `build_program` declares
//!     from, so sharing is exact and transitive.
//!   * `Proved` is NOT produced here, deliberately. A component's UNSAT does
//!     imply the whole formula's UNSAT (the component's clauses are a subset,
//!     so every model of the whole is a model of the component) — that
//!     direction needs no disjointness at all and is strictly easier. What
//!     stops it is not logic but PROVENANCE: the strict-checked artifact and
//!     the kernel/Carcara gates in `unsat_to_result` would then describe the
//!     COMPONENT while the seal is handed to the VC, and the canonical-problem
//!     digest a consumer re-checks would not match. Minting a trust seal off a
//!     sub-problem's certificate is a decision for its own increment; this one
//!     recovers the refutation and leaves `Unknown` exactly where it was.
//!   * Consequently this is a pure capability recovery: it runs ONLY after the
//!     whole-formula solve already returned `Unknown`, and it can only turn
//!     that `Unknown` into `Failed`. No verdict that decides today can move.
//!
//! SHARED LANE (2026-09-16). This split was written for `InProcessAyBackend`
//! and lived there; the external-process `IncrementalAYSession` needs the same
//! capability for the same VC shape (it answers the mixed QF_BV + NIA query
//! with `unsupported logic: ALL`), so the split lives here and both backends
//! call the one gate. A second, subtly different partition would be a second
//! soundness boundary to keep in sync — there is exactly one.

use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};
use std::time::{Duration, Instant};

use trust_types::fx::FxHashMap;
use trust_types::verify_budget::{self, ClockCreditMark};
use trust_types::{Formula, Sort, pred_arg_sorts};

use crate::smt2_export;

/// One component's nominal timeout. Its contract proves only that this number
/// does not exceed `total_ms`; the 1 ms floor can make the sum exceed it.
/// `ComponentRetryBudget` separately caps dispatch against one absolute deadline.
/// A configured `0` means unbounded, never an exhausted finite budget.
pub(crate) fn component_timeout_ms(total_ms: u64, components: usize) -> u64 {
    trust_budget::split_budget_ms(total_ms, components as u64)
}

/// The lock-wait backstop of a query whose own clock is `timeout_ms`: the
/// longest it may wait, in all, for ay's process-global execution lock
/// (ROUTER-LOCK-CLOCK-1). It is the time 64 queries of the same clock would
/// hold the lock, and never less than an hour; an unbounded query (`0`) gets
/// the hour.
///
/// It is a HANG bound, not a verdict input. Every holder of the lock is bounded
/// by its own clock, so an honest wait ends when the queries ahead of this one
/// end. This bound only stops a wait that a holder which never releases the
/// lock (or a machine that has stopped making progress) would make endless,
/// and a query it stops answers `Unknown` naming the wait (`wall-backstop`),
/// never a verdict.
#[must_use]
pub(crate) fn lock_wait_backstop_ms(timeout_ms: u64) -> u64 {
    /// How many full query clocks a query may wait behind.
    const QUERIES_AHEAD: u64 = 64;
    /// The least lock-wait backstop: one hour.
    const FLOOR_MS: u64 = 3_600_000;
    timeout_ms.saturating_mul(QUERIES_AHEAD).max(FLOOR_MS)
}

/// One query's wall backstop, shared by its original solve and component retry
/// (RETRY-QUERY-DEADLINE-1): one budget of `timeout_ms` for all of its work,
/// however many solves it runs.
///
/// The budget is charged for the query's WORK only, never for the time it
/// waits for ay's process-global execution lock (ROUTER-LOCK-CLOCK-1). Every
/// in-process solve in the process holds that one lock, so before this rule a
/// query queued behind a slow one spent its whole clock waiting and came back
/// `Unknown` ("shared query deadline exhausted before AY dispatch") without
/// ever being solved: its verdict was a function of the load, not of the query
/// and its effort count. Each wait is credited to the query's own deadline
/// ([`Self::note_lock_wait`]), the way a nested function's verification is
/// credited to its caller's clock.
///
/// Two bounds still stop a wait, and neither is ever moved by it:
///
/// * the OUTER deadline, the enclosing scope's ambient deadline when the query
///   began (the compiler's per-function clock). A wait cannot move it, so a
///   compile still ends within each function's budget; nested function
///   verification moves it by the existing shared-clock credit rules.
/// * the query's lock-wait backstop ([`lock_wait_backstop_ms`]), for a caller
///   with no ambient deadline (a test, a tool).
pub(crate) struct ComponentRetryBudget {
    timeout_ms: u64,
    /// `start + timeout_ms`; `None` for an unbounded query.
    own: Option<Instant>,
    /// The enclosing scope's ambient deadline when the query began.
    outer: Option<Instant>,
    credit: ClockCreditMark,
    /// Time this query has waited for ay's execution lock, in all. Credited to
    /// `own`, never to `outer`.
    lock_wait: Cell<Duration>,
}

/// Which bound ended a query's budget ([`ComponentRetryBudget::spent_by`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BudgetBound {
    /// The query's own clock: its work, not counting lock waits, used it up.
    Own,
    /// The enclosing scope's deadline (the per-function clock).
    Outer,
}

impl ComponentRetryBudget {
    pub(crate) fn new(timeout_ms: u64) -> Self {
        Self::at(timeout_ms, Instant::now())
    }

    fn at(timeout_ms: u64, start: Instant) -> Self {
        let own = (timeout_ms != 0)
            .then(|| start.checked_add(Duration::from_millis(timeout_ms)).unwrap_or(start));
        Self {
            timeout_ms,
            own,
            outer: verify_budget::current_deadline(),
            credit: verify_budget::clock_credit_mark(),
            lock_wait: Cell::new(Duration::ZERO),
        }
    }

    /// The query's own deadline: its start plus its clock, moved later by every
    /// lock wait and every nested function verification since it began.
    fn own_deadline(&self) -> Option<Instant> {
        verify_budget::credited(self.own, self.credit)
            .map(|at| at.checked_add(self.lock_wait.get()).unwrap_or(at))
    }

    /// The outer deadline: never moved by a lock wait.
    pub(crate) fn outer_deadline(&self) -> Option<Instant> {
        verify_budget::credited(self.outer, self.credit)
    }

    /// The query's deadline: the earlier of its own (moved by its lock waits)
    /// and the outer one, and never later than the ambient deadline now in
    /// force, so a scope narrowed after the query began still bounds it.
    pub(crate) fn deadline(&self) -> Option<Instant> {
        verify_budget::earliest(
            verify_budget::earliest(self.own_deadline(), self.outer_deadline()),
            verify_budget::current_deadline(),
        )
    }

    /// Which bound is spent at `now`, the outer one first; `None` while both
    /// have time left.
    pub(crate) fn spent_by(&self, now: Instant) -> Option<BudgetBound> {
        let spent = |deadline: Option<Instant>| deadline.is_some_and(|at| now >= at);
        if spent(self.outer_deadline()) {
            Some(BudgetBound::Outer)
        } else if spent(self.own_deadline()) {
            Some(BudgetBound::Own)
        } else {
            None
        }
    }

    /// Which bound [`Self::deadline`] is: the outer one when it comes no later
    /// than the query's own (or the query has no clock of its own), else the
    /// query's own. `None` when neither bound is set.
    pub(crate) fn binding_bound(&self) -> Option<BudgetBound> {
        match (self.outer_deadline(), self.own_deadline()) {
            (None, None) => None,
            (Some(_), None) => Some(BudgetBound::Outer),
            (None, Some(_)) => Some(BudgetBound::Own),
            (Some(outer), Some(own)) => {
                Some(if outer <= own { BudgetBound::Outer } else { BudgetBound::Own })
            }
        }
    }

    /// Credit `waited`, time spent waiting for ay's execution lock, to the
    /// query's own deadline (not to the outer one).
    pub(crate) fn note_lock_wait(&self, waited: Duration) {
        self.lock_wait.set(self.lock_wait.get().saturating_add(waited));
    }

    /// Time this query has waited for ay's execution lock so far.
    #[cfg(test)]
    pub(crate) fn lock_waited(&self) -> Duration {
        self.lock_wait.get()
    }

    /// This query's lock-wait backstop ([`lock_wait_backstop_ms`]).
    pub(crate) fn lock_wait_backstop_ms(&self) -> u64 {
        lock_wait_backstop_ms(self.timeout_ms)
    }

    /// The instant a lock wait begun at `now` gives up: the outer deadline, or
    /// the end of what is left of the query's lock-wait backstop, whichever
    /// comes first. A backstop the clock cannot represent reads as already
    /// passed, as an unrepresentable own deadline does ([`Self::at`]): the wait
    /// then fails closed rather than going unbounded.
    pub(crate) fn lock_wait_give_up_at(&self, now: Instant) -> Option<Instant> {
        let backstop = Duration::from_millis(lock_wait_backstop_ms(self.timeout_ms));
        let left = backstop.saturating_sub(self.lock_wait.get());
        verify_budget::earliest(self.outer_deadline(), Some(now.checked_add(left).unwrap_or(now)))
    }

    pub(crate) fn component_timeout_at(&self, components: usize, now: Instant) -> Option<u64> {
        timeout_within_deadline(
            component_timeout_ms(self.timeout_ms, components),
            self.deadline(),
            now,
        )
    }
}

/// Cap a solver's timeout without rounding a finite remainder up or passing the
/// exhausted-budget value `0` to an API where it means unbounded.
pub(crate) fn timeout_within_deadline(
    timeout_ms: u64,
    deadline: Option<Instant>,
    now: Instant,
) -> Option<u64> {
    let Some(deadline) = deadline else { return Some(timeout_ms) };
    let remaining =
        u64::try_from(deadline.saturating_duration_since(now).as_millis()).unwrap_or(u64::MAX);
    if remaining == 0 {
        None
    } else {
        Some(if timeout_ms == 0 { remaining } else { timeout_ms.min(remaining) })
    }
}

#[cfg(test)]
mod retry_budget_tests {
    use super::*;

    #[test]
    fn exhausted_original_query_has_no_component_budget() {
        let start = Instant::now();
        let budget = ComponentRetryBudget::at(3, start);
        assert_eq!(budget.component_timeout_at(2, start + Duration::from_millis(3)), None);
        assert_eq!(budget.component_timeout_at(2, start + Duration::from_millis(4)), None);
    }

    #[test]
    fn a_tiny_budget_cannot_be_renewed_for_each_floored_component() {
        let start = Instant::now();
        let budget = ComponentRetryBudget::at(1, start);
        assert_eq!(component_timeout_ms(1, 64), 1);
        assert_eq!(budget.component_timeout_at(64, start), Some(1));
        assert_eq!(budget.component_timeout_at(64, start + Duration::from_micros(1)), None);
        assert_eq!(budget.component_timeout_at(64, start + Duration::from_millis(1)), None);
    }

    #[test]
    fn component_timeouts_never_exceed_the_remaining_query_budget() {
        let start = Instant::now();
        let budget = ComponentRetryBudget::at(100, start);
        assert_eq!(budget.component_timeout_at(2, start), Some(50));
        assert_eq!(budget.component_timeout_at(2, start + Duration::from_millis(83)), Some(17));
    }

    #[test]
    fn an_unbounded_query_still_obeys_an_ambient_deadline() {
        let start = Instant::now();
        assert_eq!(ComponentRetryBudget::at(0, start).component_timeout_at(64, start), Some(0));
        let _scope = verify_budget::VerifyBudgetGuard::install(
            Some(start + Duration::from_millis(2)),
            u64::MAX,
        );
        let budget = ComponentRetryBudget::at(0, start);
        assert_eq!(budget.component_timeout_at(64, start), Some(2));
        assert_eq!(budget.component_timeout_at(64, start + Duration::from_millis(2)), None);
    }

    /// ROUTER-LOCK-CLOCK-1: a wait for AY's execution lock moves the query's own
    /// deadline by exactly the wait, so the query keeps the clock its work has
    /// not spent.
    #[test]
    fn a_lock_wait_is_not_charged_to_the_query_clock() {
        let start = Instant::now();
        let budget = ComponentRetryBudget::at(100, start);
        budget.note_lock_wait(Duration::from_millis(1_000));
        assert_eq!(budget.lock_waited(), Duration::from_millis(1_000));
        // 1,010 ms after the start, 10 of them work: 90 ms of the clock left.
        let after_wait = start + Duration::from_millis(1_010);
        assert_eq!(budget.component_timeout_at(1, after_wait), Some(90));
        assert_eq!(budget.component_timeout_at(2, after_wait), Some(50));
        assert_eq!(budget.spent_by(after_wait), None);
        // The work still spends it: 100 ms of work after the wait, nothing left.
        let spent = start + Duration::from_millis(1_100);
        assert_eq!(budget.component_timeout_at(1, spent), None);
        assert_eq!(budget.spent_by(spent), Some(BudgetBound::Own));
        assert_eq!(budget.binding_bound(), Some(BudgetBound::Own), "no ambient deadline");
    }

    /// ...and never the OUTER deadline: the enclosing scope's clock ends a query
    /// whatever it waited for, so a compile still ends within each function's
    /// budget.
    #[test]
    fn a_lock_wait_never_moves_the_outer_deadline() {
        let start = Instant::now();
        let _function = verify_budget::VerifyBudgetGuard::install(
            Some(start + Duration::from_millis(500)),
            u64::MAX,
        );
        let budget = ComponentRetryBudget::at(100, start);
        assert_eq!(budget.binding_bound(), Some(BudgetBound::Own), "100 ms ends before 500");
        budget.note_lock_wait(Duration::from_millis(1_000));
        assert_eq!(
            budget.binding_bound(),
            Some(BudgetBound::Outer),
            "the wait moved the query's own deadline past the outer one"
        );
        let after_wait = start + Duration::from_millis(1_010);
        assert_eq!(budget.component_timeout_at(1, after_wait), None);
        assert_eq!(budget.spent_by(after_wait), Some(BudgetBound::Outer));
        assert_eq!(budget.outer_deadline(), Some(start + Duration::from_millis(500)));
        assert_eq!(
            budget.lock_wait_give_up_at(after_wait),
            Some(start + Duration::from_millis(500)),
            "a wait gives up at the outer deadline when it comes first"
        );
    }

    /// The lock-wait backstop: 64 of the query's clocks, never less than an hour,
    /// saturating; what a query already waited comes off it.
    #[test]
    fn the_lock_wait_backstop_is_a_generous_hang_bound() {
        assert_eq!(lock_wait_backstop_ms(0), 3_600_000, "an unbounded query still has one");
        assert_eq!(lock_wait_backstop_ms(5_000), 3_600_000);
        assert_eq!(lock_wait_backstop_ms(30_000), 3_600_000);
        assert_eq!(lock_wait_backstop_ms(600_000), 38_400_000);
        assert_eq!(lock_wait_backstop_ms(u64::MAX), u64::MAX);
        let start = Instant::now();
        let budget = ComponentRetryBudget::at(30_000, start);
        assert_eq!(budget.lock_wait_give_up_at(start), Some(start + Duration::from_secs(3_600)));
        budget.note_lock_wait(Duration::from_secs(600));
        assert_eq!(
            budget.lock_wait_give_up_at(start),
            Some(start + Duration::from_secs(3_000)),
            "the backstop bounds the query's waits in all, not each wait"
        );
    }
}

/// Canonically flatten the TOP-LEVEL conjunction spine: `And[a, And[b, c]]`
/// becomes `And[a, b, c]`, recursively along And-children only. Pure
/// associativity — child order is preserved and nothing under `Or`/`Not`/`Ite`
/// is touched — so the result is logically equivalent by construction.
///
/// WHY (falsification regression 2026-08-11): ay 0.6 (c25240fc9) made Alethe
/// surface rendering REQUIRED for the strict UNSAT artifact, and its `and_pos`
/// surface printer indexes conjuncts against the FLATTENED surface — a nested
/// `(and A (and B C D))` then fails "and_pos indexed conjunct is absent from
/// its effective source", the whole artifact export fails, and ay publishes
/// `unknown` for a formula it PROVED. Trust's vcgen emits nested And-trees
/// (block-defs conjoined onto the violation), so previously-proving rows
/// (measured: charindices_slice_tail's slice-bounds VC) silently lost their
/// proof. Handing ay the flat spelling side-steps the printer gap with zero
/// logical change. Applied identically in `problem_smt2` and `build_program`,
/// AFTER the symbol escape, so the textual transcript, the Carcara cross-check
/// and the revalidation digest keep describing the exact program ay decided.
#[must_use]
pub(crate) fn flatten_conjunction_spine_owned(formula: Formula) -> Formula {
    fn splice_owned(formula: Formula, out: &mut Vec<Formula>) {
        match formula {
            Formula::And(terms) => {
                for term in terms {
                    splice_owned(term, out);
                }
            }
            other => out.push(other),
        }
    }
    match formula {
        Formula::And(terms) => {
            if !terms.iter().any(|t| matches!(t, Formula::And(_))) {
                return Formula::And(terms);
            }
            let mut flat = Vec::with_capacity(terms.len());
            for term in terms {
                splice_owned(term, &mut flat);
            }
            Formula::And(flat)
        }
        other => other,
    }
}

#[must_use]
pub(crate) fn flatten_conjunction_spine(formula: &Formula) -> Formula {
    fn splice(formula: &Formula, out: &mut Vec<Formula>) {
        match formula {
            Formula::And(terms) => {
                for term in terms {
                    splice(term, out);
                }
            }
            other => out.push(other.clone()),
        }
    }
    match formula {
        Formula::And(terms) => {
            if !terms.iter().any(|t| matches!(t, Formula::And(_))) {
                return Formula::And(terms.clone());
            }
            let mut flat = Vec::with_capacity(terms.len());
            splice(formula, &mut flat);
            Formula::And(flat)
        }
        _ => formula.clone(),
    }
}

/// TRUE iff every symbol in `formula` is one this lane's composition argument
/// can account for: concrete theory sorts only, and no uninterpreted
/// predicate/function, datatype sort, or quantifier anywhere. See
/// [the module docs](self) for why this gate is the
/// soundness boundary rather than a convenience.
pub(crate) fn composable_fragment(formula: &Formula) -> bool {
    fn sort_ok(sort: &Sort) -> bool {
        matches!(sort, Sort::Int | Sort::Bool | Sort::BitVec(_))
    }
    // Single-pass soundness gate:
    // 1. Uninterpreted predicates (`Pred`), uninterpreted functions (`FnApp`), and
    //    quantifiers (`Forall`/`Exists`) are outside the variable-partition fragment.
    // 2. Datatype / uninterpreted sorts (including by-name `Sel`/`IsCtor` datatype
    //    references) couple components through the theory without sharing variables.
    // 3. With no quantifiers present, every `Var`/`SymVar` is free and must sit at a
    //    concrete theory sort (`Int`, `Bool`, or `BitVec`).
    trust_types::all_formula_nodes(formula, &mut |node| {
        if matches!(
            node,
            Formula::Pred(..)
                | Formula::Forall(..)
                | Formula::Exists(..)
                | Formula::FnApp { .. }
        ) || trust_types::smt_logic::node_named_datatype_reference(node).is_some()
        {
            return false;
        }
        if let Formula::Var(_, sort) | Formula::SymVar(_, sort) = node
            && !sort_ok(sort)
        {
            return false;
        }
        let mut datatype_sort = false;
        trust_types::smt_logic::visit_node_sort_positions(node, &mut |sort| {
            if matches!(sort, Sort::Datatype { .. }) {
                datatype_sort = true;
            }
        });
        !datatype_sort
    })
}

pub(crate) fn disjoint_conjunctive_components(formula: &Formula) -> Option<Vec<Formula>> {
    if !matches!(formula, Formula::And(_)) {
        return None;
    }
    // THE SOUNDNESS GATE — see the doc above. Outside this fragment a
    // variable partition is not a symbol partition and the composition is
    // invalid.
    if !composable_fragment(formula) {
        return None;
    }
    let Formula::And(conjuncts) = flatten_conjunction_spine(formula) else {
        return None;
    };
    if conjuncts.len() < 2 {
        return None;
    }
    // Free-variable NAME lists, from the same sorted walker the program declares from.
    let var_sets: Vec<Vec<String>> = conjuncts
        .iter()
        .map(|c| {
            let mut names: Vec<String> =
                smt2_export::collect_free_vars(c).into_iter().map(|(name, _)| name).collect();
            names.dedup();
            names
        })
        .collect();
    // Union-find: conjuncts sharing any variable land in one component.
    let mut parent: Vec<usize> = (0..conjuncts.len()).collect();
    fn find(parent: &mut Vec<usize>, mut i: usize) -> usize {
        while parent[i] != i {
            parent[i] = parent[parent[i]];
            i = parent[i];
        }
        i
    }
    let mut owner: FxHashMap<&str, usize> = FxHashMap::default();
    for (i, vars) in var_sets.iter().enumerate() {
        for v in vars {
            match owner.get(v.as_str()) {
                Some(&j) => {
                    let (a, b) = (find(&mut parent, i), find(&mut parent, j));
                    if a != b {
                        parent[a] = b;
                    }
                }
                None => {
                    owner.insert(v.as_str(), i);
                }
            }
        }
    }
    let mut groups: BTreeMap<usize, Vec<Formula>> = BTreeMap::new();
    let mut var_bearing_roots: BTreeSet<usize> = BTreeSet::new();
    for (i, c) in conjuncts.into_iter().enumerate() {
        let root = find(&mut parent, i);
        if !var_sets[i].is_empty() {
            var_bearing_roots.insert(root);
        }
        groups.entry(root).or_default().push(c);
    }
    // A conjunct with NO free variables (a `Bool(true)`, a closed literal
    // comparison) forms its own singleton group and would manufacture a
    // "split" on formulas that are really one component — inflating how
    // often the retry fires. Require at least two groups that actually
    // carry variables.
    let var_bearing = var_bearing_roots.len();
    if groups.len() < 2 || var_bearing < 2 {
        return None; // one connected component — nothing to gain.
    }
    Some(
        groups
            .into_values()
            .map(|mut g| if g.len() == 1 { g.remove(0) } else { Formula::And(g) })
            .collect(),
    )
}

/// Every uninterpreted predicate symbol in `formula`, with the argument sorts
/// `build_program` declares it at (see [`uninterpreted_symbol_signatures`],
/// which is the one place that rule lives).
pub(crate) fn collect_pred_symbols(formula: &Formula) -> BTreeMap<String, Vec<Sort>> {
    let mut preds = BTreeMap::new();
    trust_types::visit_formula_nodes(formula, &mut |node| {
        if let Formula::Pred(name, args) = node
            && !preds.contains_key(name.as_str())
        {
            preds.insert(name.as_str().to_string(), pred_signature(name.as_str(), args));
        }
    });
    preds
}

/// The argument sorts one `Pred` application is DECLARED at.
///
/// A name in the closed reviewed vocabulary keeps the vocabulary's signature —
/// that table is the authority on what a safety predicate ranges over, and a
/// VC that disagrees with it is refused by
/// [`uninterpreted_signature_conflict`], never silently re-declared.
///
/// For an out-of-vocabulary name (which `Formula::Pred`'s construction gate is
/// supposed to make impossible) the sorts come from the APPLICATION itself.
/// The previous fallback invented `Int` per argument, which is how a
/// `Pred(p, [<Level-sorted term>])` — well sorted, admitted by every gate —
/// got declared `(declare-fun p (Int) Bool)` and then applied to a datatype
/// term: ay's `uf::apply` answers that with a PANIC (its `try_apply` reports
/// `SortMismatch`, the infallible wrapper unwraps it), contained only by
/// `run_with_policy`'s `catch_unwind`. Declaring what is actually applied
/// removes the mismatch instead of catching it.
fn pred_signature(name: &str, args: &[Formula]) -> Vec<Sort> {
    if let Some(vocab) = pred_arg_sorts(name) {
        return vocab.to_vec();
    }
    args.iter().map(applied_sort).collect()
}

/// The sort an argument term is applied at: the checker's answer where it has
/// one, else its total inference. Both agree on every shape the router admits
/// (it establishes `check_formula_sort(formula) == Ok(Bool)` first, which
/// recursively sorts every `Pred`/`FnApp` argument), so the fallback is only
/// there to keep this function total for direct library callers.
fn applied_sort(argument: &Formula) -> Sort {
    trust_types::smt_logic::check_formula_sort(argument)
        .unwrap_or_else(|_| trust_types::smt_logic::infer_sort(argument))
}

/// Every UNINTERPRETED SYMBOL the program must `declare-fun` before it can
/// assert `formula`: `Formula::Pred` (result sort `Bool` by definition) and
/// `Formula::FnApp` (the result sort the node carries), keyed by name, with the
/// signature of its FIRST application in visit order.
///
/// Both lanes declare from this ONE function — the in-process `build_program`
/// and the SMT-LIB text `emit_declarations` — so the executed program and the
/// canonical transcript declare the same symbols at the same signatures. That
/// matters beyond tidiness: ay's direct executor answers an application of an
/// undeclared symbol with an `ExprTranslation` error and an application at a
/// signature the declaration disagrees with inside the PANICKING `uf::apply`,
/// while the text lane would emit a query the solver rejects outright.
///
/// This is first-application-wins, which is only well defined because
/// [`uninterpreted_signature_conflict`] has already declined any formula whose
/// applications of one name disagree.
pub(crate) fn uninterpreted_symbol_signatures(
    formula: &Formula,
) -> BTreeMap<String, (Vec<Sort>, Sort)> {
    let mut signatures: BTreeMap<String, (Vec<Sort>, Sort)> = BTreeMap::new();
    trust_types::visit_formula_nodes(formula, &mut |node| match node {
        Formula::Pred(name, args) => {
            if !signatures.contains_key(name.as_str()) {
                signatures.insert(
                    name.as_str().to_string(),
                    (pred_signature(name.as_str(), args), Sort::Bool),
                );
            }
        }
        Formula::FnApp { func, args, sort } => {
            if !signatures.contains_key(func.as_str()) {
                signatures.insert(
                    func.clone(),
                    (args.iter().map(applied_sort).collect(), sort.clone()),
                );
            }
        }
        _ => {}
    });
    signatures
}

/// The first uninterpreted symbol in `formula` whose APPLICATION disagrees with
/// the signature it will be DECLARED at, as a decline reason — or `None` when
/// every application matches.
///
/// SMT-LIB and ay both have exactly one declaration per symbol, so a formula
/// that applies one name at two arities, at two argument sorts, or at two
/// result sorts has no faithful program at all. Handing it to ay anyway reaches
/// `uf::apply`, whose infallible wrapper PANICS on a sort/arity mismatch — the
/// same shape as every other translation-boundary crash class, and rescued only
/// by `catch_unwind`, which still runs the process-global panic hook. Answering
/// it here DECLINES the obligation instead (sound: it emits neither a proof nor
/// a refutation).
///
/// Sorts are compared with [`trust_types::smt_logic::sorts_agree`], so a
/// datatype's by-name and full spellings are ONE sort — exactly the relaxation
/// the sort checker and `sort_to_ay_in` apply, which lower both spellings to
/// the same ay sort.
pub(crate) fn uninterpreted_signature_conflict(formula: &Formula) -> Option<String> {
    let declared = uninterpreted_symbol_signatures(formula);
    if declared.is_empty() {
        return None;
    }
    let mut conflict: Option<String> = None;
    let _ = trust_types::all_formula_nodes(formula, &mut |node| {
        conflict = match node {
            Formula::Pred(name, args) => {
                signature_mismatch(&declared, name.as_str(), args, &Sort::Bool, "predicate")
            }
            Formula::FnApp { func, args, sort } => {
                signature_mismatch(&declared, func, args, sort, "function application")
            }
            _ => None,
        };
        conflict.is_none()
    });
    conflict
}

/// One application checked against the declaration it will be given; see
/// [`uninterpreted_signature_conflict`].
fn signature_mismatch(
    declared: &BTreeMap<String, (Vec<Sort>, Sort)>,
    name: &str,
    applied_args: &[Formula],
    result: &Sort,
    kind: &str,
) -> Option<String> {
    use trust_types::smt_logic::sorts_agree;

    let (decl_args, decl_result) = declared.get(name)?;
    if decl_args.len() != applied_args.len() {
        return Some(format!(
            "uninterpreted symbol `{name}` is declared with {} argument(s) but a {kind} applies \
             it to {}",
            decl_args.len(),
            applied_args.len()
        ));
    }
    for (index, (expected, arg)) in decl_args.iter().zip(applied_args.iter()).enumerate() {
        let actual = applied_sort(arg);
        if !sorts_agree(expected, &actual) {
            return Some(format!(
                "uninterpreted symbol `{name}` is declared with argument {index} of sort \
                 {expected:?} but a {kind} applies it to a {actual:?} term"
            ));
        }
    }
    if !sorts_agree(decl_result, result) {
        return Some(format!(
            "uninterpreted symbol `{name}` is declared with result sort {decl_result:?} but a \
             {kind} applies it at {result:?}"
        ));
    }
    None
}
