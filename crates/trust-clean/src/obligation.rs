// trust-clean/obligation.rs: Proof obligation management
//
// Manages the lifecycle of proof obligations — goals that must be proven
// for verification to succeed. Obligations are generated from verification
// conditions and tracked through pending, in-progress, discharged, or
// failed states.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{Formula, VcKind};

// ---------------------------------------------------------------------------
// Proof obligation
// ---------------------------------------------------------------------------

/// A proof obligation: a goal formula that must be proven within a context.
#[derive(Debug, Clone)]
pub struct ProofObligation {
    /// Unique identifier for this obligation.
    pub id: ObligationId,
    /// The goal formula to be proven.
    pub goal: Formula,
    /// Hypotheses (context) available for proving the goal.
    pub hypotheses: Vec<Formula>,
    /// Where this obligation came from.
    pub source: ObligationSource,
    /// Current status.
    pub status: ObligationStatus,
    /// IDs of obligations that this one depends on (must be discharged first).
    pub dependencies: Vec<ObligationId>,
}

/// Unique identifier for a proof obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ObligationId(pub u64);

/// Where a proof obligation originated.
#[derive(Debug, Clone)]
pub struct ObligationSource {
    /// The kind of verification condition that spawned this obligation.
    pub vc_kind: VcKind,
    /// The function being verified.
    pub function: String,
    /// Optional description of the sub-obligation.
    pub description: String,
}

/// Status of a proof obligation.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum ObligationStatus {
    /// Not yet attempted.
    Pending,
    /// Currently being worked on by a solver/prover.
    InProgress,
    /// Successfully proven. Stores the proof evidence (serialized bytes).
    Discharged {
        /// Serialized proof evidence.
        proof: Vec<u8>,
    },
    /// Proof attempt failed.
    Failed {
        /// Reason the proof failed.
        reason: String,
    },
}

impl ObligationStatus {
    /// Returns `true` if the obligation has been discharged.
    #[must_use]
    pub fn is_discharged(&self) -> bool {
        matches!(self, ObligationStatus::Discharged { .. })
    }

    /// Returns `true` if the obligation is still pending.
    #[must_use]
    pub fn is_pending(&self) -> bool {
        matches!(self, ObligationStatus::Pending)
    }

    /// Returns `true` if the obligation has failed.
    #[must_use]
    pub fn is_failed(&self) -> bool {
        matches!(self, ObligationStatus::Failed { .. })
    }
}

impl ProofObligation {
    /// Create a new pending obligation.
    #[must_use]
    pub fn new(id: ObligationId, goal: Formula, source: ObligationSource) -> Self {
        ProofObligation {
            id,
            goal,
            hypotheses: Vec::new(),
            source,
            status: ObligationStatus::Pending,
            dependencies: Vec::new(),
        }
    }

    /// Create a new obligation with hypotheses.
    #[must_use]
    pub fn with_hypotheses(
        id: ObligationId,
        goal: Formula,
        hypotheses: Vec<Formula>,
        source: ObligationSource,
    ) -> Self {
        ProofObligation {
            id,
            goal,
            hypotheses,
            source,
            status: ObligationStatus::Pending,
            dependencies: Vec::new(),
        }
    }

    /// Check whether this obligation can be trivially discharged.
    ///
    /// An obligation is trivial if:
    /// - The goal is `Bool(true)` (tautology)
    /// - The goal appears verbatim in the hypotheses (assumption)
    /// - The goal is `Not(Bool(false))` (negation of false)
    #[must_use]
    pub fn is_trivial(&self) -> bool {
        match &self.goal {
            Formula::Bool(true) => true,
            Formula::Not(inner) => matches!(inner.as_ref(), Formula::Bool(false)),
            goal => self.hypotheses.iter().any(|h| h == goal),
        }
    }

    /// Strengthen this obligation by adding a hypothesis.
    ///
    /// Adding hypotheses makes the obligation easier to prove (more
    /// context available). Returns `self` for chaining.
    pub fn strengthen(&mut self, hypothesis: Formula) -> &mut Self {
        self.hypotheses.push(hypothesis);
        self
    }

    /// Weaken the goal to a simpler formula.
    ///
    /// The new goal should be implied by the original goal. If the weaker
    /// goal can be proven, the original is also proven (by transitivity
    /// of implication). This is useful when the original goal is too
    /// complex for the solver.
    pub fn weaken_goal(&mut self, weaker_goal: Formula) -> &mut Self {
        self.goal = weaker_goal;
        self
    }

    /// Mark this obligation as discharged with proof evidence.
    pub fn discharge(&mut self, proof: Vec<u8>) {
        self.status = ObligationStatus::Discharged { proof };
    }

    /// Mark this obligation as failed.
    pub fn fail(&mut self, reason: &str) {
        self.status = ObligationStatus::Failed { reason: reason.to_string() };
    }

    /// Mark this obligation as in-progress.
    pub fn start(&mut self) {
        self.status = ObligationStatus::InProgress;
    }
}

// ---------------------------------------------------------------------------
// Splitting conjunctive obligations
// ---------------------------------------------------------------------------

/// Split a conjunctive obligation into sub-obligations.
///
/// If the goal is `And([P, Q, R])`, produces three obligations with goals
/// `P`, `Q`, and `R` respectively, all sharing the same hypotheses and source.
/// If the goal is not a conjunction, returns a single-element vec with the
/// original obligation cloned.
///
/// The `next_id` function generates fresh obligation IDs for the sub-obligations.
pub fn split_obligation(
    obligation: &ProofObligation,
    mut next_id: impl FnMut() -> ObligationId,
) -> Vec<ProofObligation> {
    match &obligation.goal {
        Formula::And(conjuncts) if conjuncts.len() > 1 => conjuncts
            .iter()
            .map(|conjunct| {
                let mut sub =
                    ProofObligation::new(next_id(), conjunct.clone(), obligation.source.clone());
                sub.hypotheses = obligation.hypotheses.clone();
                sub.dependencies = obligation.dependencies.clone();
                sub
            })
            .collect(),
        _ => vec![obligation.clone()],
    }
}

// ---------------------------------------------------------------------------
// Obligation set
// ---------------------------------------------------------------------------

/// A managed collection of proof obligations with lifecycle tracking.
pub struct ObligationSet {
    /// Obligations indexed by ID.
    obligations: FxHashMap<ObligationId, ProofObligation>,
    /// Counter for generating fresh IDs.
    next_id: u64,
}

impl ObligationSet {
    /// Create an empty obligation set.
    #[must_use]
    pub fn new() -> Self {
        ObligationSet { obligations: FxHashMap::default(), next_id: 1 }
    }

    /// Generate a fresh obligation ID.
    pub fn fresh_id(&mut self) -> ObligationId {
        let id = ObligationId(self.next_id);
        self.next_id += 1;
        id
    }

    /// Add an obligation to the set.
    pub fn add(&mut self, obligation: ProofObligation) {
        self.obligations.insert(obligation.id, obligation);
    }

    /// Create and add a new obligation, returning its ID.
    pub fn create(&mut self, goal: Formula, source: ObligationSource) -> ObligationId {
        let id = self.fresh_id();
        let obl = ProofObligation::new(id, goal, source);
        self.obligations.insert(id, obl);
        id
    }

    /// Create and add a new obligation with hypotheses, returning its ID.
    pub fn create_with_hypotheses(
        &mut self,
        goal: Formula,
        hypotheses: Vec<Formula>,
        source: ObligationSource,
    ) -> ObligationId {
        let id = self.fresh_id();
        let obl = ProofObligation::with_hypotheses(id, goal, hypotheses, source);
        self.obligations.insert(id, obl);
        id
    }

    /// Look up an obligation by ID.
    #[must_use]
    pub fn get(&self, id: ObligationId) -> Option<&ProofObligation> {
        self.obligations.get(&id)
    }

    /// Look up an obligation mutably by ID.
    pub fn get_mut(&mut self, id: ObligationId) -> Option<&mut ProofObligation> {
        self.obligations.get_mut(&id)
    }

    /// Discharge an obligation with proof evidence.
    ///
    /// Returns `true` if the obligation was found and discharged.
    pub fn discharge(&mut self, id: ObligationId, proof: Vec<u8>) -> bool {
        if let Some(obl) = self.obligations.get_mut(&id) {
            obl.discharge(proof);
            true
        } else {
            false
        }
    }

    /// Mark an obligation as failed.
    ///
    /// Returns `true` if the obligation was found.
    pub fn fail(&mut self, id: ObligationId, reason: &str) -> bool {
        if let Some(obl) = self.obligations.get_mut(&id) {
            obl.fail(reason);
            true
        } else {
            false
        }
    }

    /// Total number of obligations.
    #[must_use]
    pub fn len(&self) -> usize {
        self.obligations.len()
    }

    /// Whether the set is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.obligations.is_empty()
    }

    /// Count of pending obligations.
    #[must_use]
    pub fn pending_count(&self) -> usize {
        self.obligations.values().filter(|o| o.status.is_pending()).count()
    }

    /// Count of discharged obligations.
    #[must_use]
    pub fn discharged_count(&self) -> usize {
        self.obligations.values().filter(|o| o.status.is_discharged()).count()
    }

    /// Count of failed obligations.
    #[must_use]
    pub fn failed_count(&self) -> usize {
        self.obligations.values().filter(|o| o.status.is_failed()).count()
    }

    /// Returns `true` if all obligations are discharged.
    #[must_use]
    pub fn all_discharged(&self) -> bool {
        !self.obligations.is_empty() && self.obligations.values().all(|o| o.status.is_discharged())
    }

    /// Return all pending obligations in insertion order (by ID).
    #[must_use]
    pub fn pending(&self) -> Vec<&ProofObligation> {
        let mut pending: Vec<_> =
            self.obligations.values().filter(|o| o.status.is_pending()).collect();
        pending.sort_by_key(|o| o.id.0);
        pending
    }

    /// Return all obligations (any status) sorted by ID.
    #[must_use]
    pub fn all(&self) -> Vec<&ProofObligation> {
        let mut all: Vec<_> = self.obligations.values().collect();
        all.sort_by_key(|o| o.id.0);
        all
    }

    /// Split a conjunctive obligation into sub-obligations.
    ///
    /// The original obligation is replaced by the sub-obligations.
    /// If the goal is not a conjunction, this is a no-op.
    /// Returns the IDs of the new sub-obligations.
    pub fn split(&mut self, id: ObligationId) -> Vec<ObligationId> {
        let obl = match self.obligations.get(&id) {
            Some(o) => o.clone(),
            None => return Vec::new(),
        };

        let subs = split_obligation(&obl, || self.fresh_id());
        if subs.len() <= 1 {
            // Not a conjunction, nothing to split
            return vec![id];
        }

        // Remove original, insert sub-obligations
        self.obligations.remove(&id);
        let ids: Vec<ObligationId> = subs.iter().map(|s| s.id).collect();
        for sub in subs {
            self.obligations.insert(sub.id, sub);
        }
        ids
    }

    /// Compute a dependency-respecting order for all pending obligations.
    ///
    /// Returns obligation IDs in topological order: obligations with no
    /// dependencies come first. If there are cycles, obligations in the
    /// cycle are placed at the end.
    #[must_use]
    pub fn dependency_order(&self) -> Vec<ObligationId> {
        let pending: Vec<&ProofObligation> =
            self.obligations.values().filter(|o| o.status.is_pending()).collect();

        // Kahn's algorithm for topological sort
        let discharged_ids: FxHashSet<ObligationId> =
            self.obligations.values().filter(|o| o.status.is_discharged()).map(|o| o.id).collect();

        // Compute in-degree: count of unsatisfied dependencies per obligation
        let mut in_degree: FxHashMap<ObligationId, usize> = FxHashMap::default();
        for obl in &pending {
            let unsatisfied =
                obl.dependencies.iter().filter(|dep| !discharged_ids.contains(dep)).count();
            in_degree.insert(obl.id, unsatisfied);
        }

        let mut result = Vec::with_capacity(pending.len());
        let mut queue: std::collections::VecDeque<ObligationId> = {
            let mut initial: Vec<ObligationId> =
                in_degree.iter().filter(|(_, deg)| **deg == 0).map(|(&id, _)| id).collect();
            initial.sort_by_key(|id| id.0);
            initial.into_iter().collect()
        };

        while let Some(id) = queue.pop_front() {
            result.push(id);
            // "Discharge" this in the dependency graph
            let mut newly_ready = Vec::new();
            for obl in &pending {
                if obl.dependencies.contains(&id)
                    && let Some(deg) = in_degree.get_mut(&obl.id)
                {
                    *deg = deg.saturating_sub(1);
                    if *deg == 0 && !result.contains(&obl.id) {
                        newly_ready.push(obl.id);
                    }
                }
            }
            newly_ready.sort_by_key(|nid| nid.0);
            for nid in newly_ready {
                if !queue.contains(&nid) {
                    queue.push_back(nid);
                }
            }
        }

        // Append any remaining (cycle members) at the end
        for obl in &pending {
            if !result.contains(&obl.id) {
                result.push(obl.id);
            }
        }

        result
    }
}

impl Default for ObligationSet {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::{BinOp, Sort, Ty};

    use super::*;

    fn sample_source() -> ObligationSource {
        ObligationSource {
            vc_kind: VcKind::DivisionByZero,
            function: "test_fn".into(),
            description: "division safety".to_string(),
        }
    }

    fn sample_source_overflow() -> ObligationSource {
        ObligationSource {
            vc_kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::usize(), Ty::usize()),
            },
            function: "add_fn".into(),
            description: "overflow check".to_string(),
        }
    }

    // -----------------------------------------------------------------------
    // ObligationStatus tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_obligation_status_predicates() {
        assert!(ObligationStatus::Pending.is_pending());
        assert!(!ObligationStatus::Pending.is_discharged());
        assert!(!ObligationStatus::Pending.is_failed());

        let discharged = ObligationStatus::Discharged { proof: vec![1] };
        assert!(discharged.is_discharged());
        assert!(!discharged.is_pending());

        let failed = ObligationStatus::Failed { reason: "timeout".into() };
        assert!(failed.is_failed());
        assert!(!failed.is_discharged());
    }

    // -----------------------------------------------------------------------
    // ProofObligation lifecycle
    // -----------------------------------------------------------------------

    #[test]
    fn test_obligation_new_is_pending() {
        let obl = ProofObligation::new(ObligationId(1), Formula::Bool(true), sample_source());
        assert!(obl.status.is_pending());
        assert!(obl.hypotheses.is_empty());
        assert!(obl.dependencies.is_empty());
    }

    #[test]
    fn test_obligation_with_hypotheses() {
        let obl = ProofObligation::with_hypotheses(
            ObligationId(1),
            Formula::Var("x".into(), Sort::Int),
            vec![Formula::Bool(true), Formula::Int(42)],
            sample_source(),
        );
        assert_eq!(obl.hypotheses.len(), 2);
    }

    #[test]
    fn test_obligation_discharge() {
        let mut obl = ProofObligation::new(ObligationId(1), Formula::Bool(true), sample_source());
        obl.start();
        assert!(matches!(obl.status, ObligationStatus::InProgress));
        obl.discharge(vec![0xDE, 0xAD]);
        assert!(obl.status.is_discharged());
        if let ObligationStatus::Discharged { proof } = &obl.status {
            assert_eq!(proof, &[0xDE, 0xAD]);
        }
    }

    #[test]
    fn test_obligation_fail() {
        let mut obl = ProofObligation::new(ObligationId(1), Formula::Bool(true), sample_source());
        obl.fail("solver timeout");
        assert!(obl.status.is_failed());
    }

    // -----------------------------------------------------------------------
    // is_trivial
    // -----------------------------------------------------------------------

    #[test]
    fn test_is_trivial_bool_true() {
        let obl = ProofObligation::new(ObligationId(1), Formula::Bool(true), sample_source());
        assert!(obl.is_trivial());
    }

    #[test]
    fn test_is_trivial_not_false() {
        let obl = ProofObligation::new(
            ObligationId(1),
            Formula::Not(Box::new(Formula::Bool(false))),
            sample_source(),
        );
        assert!(obl.is_trivial());
    }

    #[test]
    fn test_is_trivial_assumption() {
        let goal = Formula::Var("x".into(), Sort::Bool);
        let obl = ProofObligation::with_hypotheses(
            ObligationId(1),
            goal.clone(),
            vec![goal],
            sample_source(),
        );
        assert!(obl.is_trivial());
    }

    #[test]
    fn test_is_trivial_non_trivial() {
        let obl = ProofObligation::new(
            ObligationId(1),
            Formula::Var("x".into(), Sort::Bool),
            sample_source(),
        );
        assert!(!obl.is_trivial());
    }

    // -----------------------------------------------------------------------
    // strengthen / weaken
    // -----------------------------------------------------------------------

    #[test]
    fn test_strengthen_obligation() {
        let mut obl = ProofObligation::new(
            ObligationId(1),
            Formula::Var("x".into(), Sort::Bool),
            sample_source(),
        );
        obl.strengthen(Formula::Bool(true));
        assert_eq!(obl.hypotheses.len(), 1);

        obl.strengthen(Formula::Int(0));
        assert_eq!(obl.hypotheses.len(), 2);
    }

    #[test]
    fn test_weaken_goal() {
        let mut obl = ProofObligation::new(
            ObligationId(1),
            Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]),
            sample_source(),
        );
        obl.weaken_goal(Formula::Bool(true));
        assert_eq!(obl.goal, Formula::Bool(true));
    }

    // -----------------------------------------------------------------------
    // split_obligation
    // -----------------------------------------------------------------------

    #[test]
    fn test_split_conjunction() {
        let obl = ProofObligation::with_hypotheses(
            ObligationId(1),
            Formula::And(vec![
                Formula::Bool(true),
                Formula::Int(1),
                Formula::Var("x".into(), Sort::Bool),
            ]),
            vec![Formula::Bool(false)],
            sample_source(),
        );

        let mut counter = 100u64;
        let subs = split_obligation(&obl, || {
            counter += 1;
            ObligationId(counter)
        });

        assert_eq!(subs.len(), 3);
        assert_eq!(subs[0].goal, Formula::Bool(true));
        assert_eq!(subs[1].goal, Formula::Int(1));
        assert_eq!(subs[2].goal, Formula::Var("x".into(), Sort::Bool));

        // All share the same hypotheses
        for sub in &subs {
            assert_eq!(sub.hypotheses, vec![Formula::Bool(false)]);
        }
    }

    #[test]
    fn test_split_non_conjunction() {
        let obl = ProofObligation::new(ObligationId(1), Formula::Bool(true), sample_source());
        let subs = split_obligation(&obl, || ObligationId(99));
        assert_eq!(subs.len(), 1);
        assert_eq!(subs[0].id, ObligationId(1)); // original
    }

    #[test]
    fn test_split_single_conjunct() {
        let obl = ProofObligation::new(
            ObligationId(1),
            Formula::And(vec![Formula::Bool(true)]),
            sample_source(),
        );
        let subs = split_obligation(&obl, || ObligationId(99));
        // Single-element conjunction is not split
        assert_eq!(subs.len(), 1);
    }

    // -----------------------------------------------------------------------
    // ObligationSet basics
    // -----------------------------------------------------------------------

    #[test]
    fn test_obligation_set_new_is_empty() {
        let set = ObligationSet::new();
        assert!(set.is_empty());
        assert_eq!(set.len(), 0);
    }

    #[test]
    fn test_obligation_set_create_and_get() {
        let mut set = ObligationSet::new();
        let id = set.create(Formula::Bool(true), sample_source());
        assert_eq!(set.len(), 1);
        assert!(set.get(id).is_some());
        assert!(set.get(id).unwrap().status.is_pending());
    }

    #[test]
    fn test_obligation_set_create_with_hypotheses() {
        let mut set = ObligationSet::new();
        let id =
            set.create_with_hypotheses(Formula::Bool(true), vec![Formula::Int(1)], sample_source());
        let obl = set.get(id).unwrap();
        assert_eq!(obl.hypotheses.len(), 1);
    }

    #[test]
    fn test_obligation_set_discharge() {
        let mut set = ObligationSet::new();
        let id = set.create(Formula::Bool(true), sample_source());
        assert!(set.discharge(id, vec![1, 2, 3]));
        assert!(set.get(id).unwrap().status.is_discharged());
        assert_eq!(set.discharged_count(), 1);
        assert_eq!(set.pending_count(), 0);
    }

    #[test]
    fn test_obligation_set_fail() {
        let mut set = ObligationSet::new();
        let id = set.create(Formula::Bool(true), sample_source());
        assert!(set.fail(id, "timeout"));
        assert!(set.get(id).unwrap().status.is_failed());
        assert_eq!(set.failed_count(), 1);
    }

    #[test]
    fn test_obligation_set_discharge_nonexistent() {
        let mut set = ObligationSet::new();
        assert!(!set.discharge(ObligationId(999), vec![]));
    }

    #[test]
    fn test_obligation_set_all_discharged() {
        let mut set = ObligationSet::new();
        assert!(!set.all_discharged()); // empty set is not "all discharged"

        let id1 = set.create(Formula::Bool(true), sample_source());
        let id2 = set.create(Formula::Bool(false), sample_source_overflow());

        assert!(!set.all_discharged());

        set.discharge(id1, vec![1]);
        assert!(!set.all_discharged());

        set.discharge(id2, vec![2]);
        assert!(set.all_discharged());
    }

    // -----------------------------------------------------------------------
    // ObligationSet::pending / all
    // -----------------------------------------------------------------------

    #[test]
    fn test_obligation_set_pending_sorted_by_id() {
        let mut set = ObligationSet::new();
        let _id1 = set.create(Formula::Bool(true), sample_source());
        let _id2 = set.create(Formula::Bool(false), sample_source());
        let id3 = set.create(Formula::Int(1), sample_source());

        set.discharge(id3, vec![]);

        let pending = set.pending();
        assert_eq!(pending.len(), 2);
        assert!(pending[0].id.0 < pending[1].id.0);
    }

    #[test]
    fn test_obligation_set_all_sorted_by_id() {
        let mut set = ObligationSet::new();
        set.create(Formula::Bool(true), sample_source());
        set.create(Formula::Bool(false), sample_source());

        let all = set.all();
        assert_eq!(all.len(), 2);
        assert!(all[0].id.0 < all[1].id.0);
    }

    // -----------------------------------------------------------------------
    // ObligationSet::split
    // -----------------------------------------------------------------------

    #[test]
    fn test_obligation_set_split_conjunction() {
        let mut set = ObligationSet::new();
        let id = set
            .create(Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]), sample_source());
        assert_eq!(set.len(), 1);

        let sub_ids = set.split(id);
        assert_eq!(sub_ids.len(), 2);
        // Original removed, two subs added
        assert_eq!(set.len(), 2);
        assert!(set.get(id).is_none());
        for &sub_id in &sub_ids {
            assert!(set.get(sub_id).is_some());
        }
    }

    #[test]
    fn test_obligation_set_split_non_conjunction() {
        let mut set = ObligationSet::new();
        let id = set.create(Formula::Bool(true), sample_source());
        let sub_ids = set.split(id);
        assert_eq!(sub_ids, vec![id]); // no-op
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn test_obligation_set_split_nonexistent() {
        let mut set = ObligationSet::new();
        let ids = set.split(ObligationId(999));
        assert!(ids.is_empty());
    }

    // -----------------------------------------------------------------------
    // dependency_order
    // -----------------------------------------------------------------------

    #[test]
    fn test_dependency_order_no_deps() {
        let mut set = ObligationSet::new();
        let id1 = set.create(Formula::Bool(true), sample_source());
        let id2 = set.create(Formula::Bool(false), sample_source());

        let order = set.dependency_order();
        assert_eq!(order.len(), 2);
        // Both have no deps, should appear in ID order
        assert_eq!(order[0], id1);
        assert_eq!(order[1], id2);
    }

    #[test]
    fn test_dependency_order_with_deps() {
        let mut set = ObligationSet::new();
        let id1 = set.create(Formula::Bool(true), sample_source());
        let id2 = set.create(Formula::Bool(false), sample_source());

        // id2 depends on id1
        set.get_mut(id2).unwrap().dependencies.push(id1);

        let order = set.dependency_order();
        assert_eq!(order.len(), 2);
        assert_eq!(order[0], id1); // id1 first (no deps)
        assert_eq!(order[1], id2); // id2 second (depends on id1)
    }

    #[test]
    fn test_dependency_order_satisfied_deps_ignored() {
        let mut set = ObligationSet::new();
        let id1 = set.create(Formula::Bool(true), sample_source());
        let id2 = set.create(Formula::Bool(false), sample_source());

        // Discharge id1, then id2 depends on id1 (already satisfied)
        set.discharge(id1, vec![1]);
        set.get_mut(id2).unwrap().dependencies.push(id1);

        let order = set.dependency_order();
        // Only id2 is pending; id1 is discharged
        assert_eq!(order.len(), 1);
        assert_eq!(order[0], id2);
    }

    #[test]
    fn test_dependency_order_chain() {
        let mut set = ObligationSet::new();
        let id1 = set.create(Formula::Bool(true), sample_source());
        let id2 = set.create(Formula::Bool(false), sample_source());
        let id3 = set.create(Formula::Int(0), sample_source());

        // Chain: id3 -> id2 -> id1
        set.get_mut(id2).unwrap().dependencies.push(id1);
        set.get_mut(id3).unwrap().dependencies.push(id2);

        let order = set.dependency_order();
        assert_eq!(order, vec![id1, id2, id3]);
    }

    #[test]
    fn test_dependency_order_empty() {
        let set = ObligationSet::new();
        assert!(set.dependency_order().is_empty());
    }

    // -----------------------------------------------------------------------
    // ObligationSet::default
    // -----------------------------------------------------------------------

    #[test]
    fn test_obligation_set_default() {
        let set = ObligationSet::default();
        assert!(set.is_empty());
    }

    // -----------------------------------------------------------------------
    // get_mut
    // -----------------------------------------------------------------------

    #[test]
    fn test_obligation_set_get_mut() {
        let mut set = ObligationSet::new();
        let id = set.create(Formula::Bool(true), sample_source());

        set.get_mut(id).unwrap().strengthen(Formula::Int(42));
        assert_eq!(set.get(id).unwrap().hypotheses.len(), 1);
    }

    // -----------------------------------------------------------------------
    // fresh_id monotonicity
    // -----------------------------------------------------------------------

    #[test]
    fn test_fresh_id_monotonic() {
        let mut set = ObligationSet::new();
        let id1 = set.fresh_id();
        let id2 = set.fresh_id();
        let id3 = set.fresh_id();
        assert!(id1.0 < id2.0);
        assert!(id2.0 < id3.0);
    }
}
