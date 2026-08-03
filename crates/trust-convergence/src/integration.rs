// trust-convergence/integration.rs: Bridge from CrateVerificationResult to convergence tracking.
//
// Converts verification pipeline output into ProofFrontier snapshots and tracks
// per-VC status changes across iterations to detect regressions and stagnation.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use trust_types::{CrateVerificationResult, VerificationResult};

use crate::{ConvergenceTracker, IterationSnapshot, ProofFrontier};

/// Compact status for a single VC, derived from `VerificationResult`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VcStatus {
    Proved,
    Failed,
    Unknown,
    Timeout,
}

impl VcStatus {
    /// Classify a `VerificationResult` into a `VcStatus`.
    #[must_use]
    pub fn from_result(result: &VerificationResult) -> Self {
        match result {
            VerificationResult::Proved { .. } => VcStatus::Proved,
            VerificationResult::Failed { .. } => VcStatus::Failed,
            VerificationResult::Unknown { .. } => VcStatus::Unknown,
            VerificationResult::Timeout { .. } => VcStatus::Timeout,
            _ => VcStatus::Unknown,
        }
    }
}

/// Identifies a single VC across iterations by function path and VC description.
pub type VcId = (String, String);

/// Deterministically ordered per-VC status map.
pub type VcStatusMap = BTreeMap<VcId, VcStatus>;

/// A VC whose status changed between two iterations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VcStatusChange {
    pub vc_id: VcId,
    pub old_status: VcStatus,
    pub new_status: VcStatus,
}

impl VcStatusChange {
    /// True if the VC was proved before but is no longer proved.
    #[must_use]
    pub fn is_regression(&self) -> bool {
        self.old_status == VcStatus::Proved && self.new_status != VcStatus::Proved
    }

    /// True if the VC is newly proved.
    #[must_use]
    pub fn is_improvement(&self) -> bool {
        self.old_status != VcStatus::Proved && self.new_status == VcStatus::Proved
    }
}

/// Tracks per-VC status changes across iterations on top of `ConvergenceTracker`.
#[derive(Debug, Clone)]
pub struct VerificationConvergenceTracker {
    /// Underlying aggregate convergence tracker.
    tracker: ConvergenceTracker,
    /// Per-VC status at the most recently observed iteration.
    current_statuses: VcStatusMap,
    /// Per-VC status at the previous iteration.
    previous_statuses: VcStatusMap,
    /// Changes detected at the most recent observation.
    last_changes: Vec<VcStatusChange>,
    /// Iteration counter managed internally.
    iteration: u32,
}

impl VerificationConvergenceTracker {
    /// Create a new tracker with stability and iteration limits.
    // Trust (flywheel backprop, contract PROPAGATION): the wrapped
    // `ConvergenceTracker::new` now carries `#[trust::requires]` preconditions,
    // and the verifier correctly refuted THIS wrapper for not guaranteeing
    // them — so the contract propagates up, pushing the obligation to callers.
    #[trust::requires(stable_round_limit > 0)]
    #[trust::requires(iteration_limit > 0)]
    #[must_use]
    pub fn new(stable_round_limit: usize, iteration_limit: u32) -> Self {
        Self {
            tracker: ConvergenceTracker::new(stable_round_limit, iteration_limit),
            current_statuses: VcStatusMap::new(),
            previous_statuses: VcStatusMap::new(),
            last_changes: Vec::new(),
            iteration: 0,
        }
    }

    /// Observe a new `CrateVerificationResult` and update all tracking state.
    ///
    /// Returns the per-VC status changes detected since the last observation.
    pub fn observe(&mut self, result: &CrateVerificationResult) -> Vec<VcStatusChange> {
        let frontier = ProofFrontier::from_verification_result(result);
        let new_statuses = extract_vc_statuses(result);

        // Compute per-VC changes.
        let changes = compute_changes(&self.current_statuses, &new_statuses);

        // Feed aggregate frontier into the underlying tracker.
        let snapshot = IterationSnapshot::new(self.iteration, frontier);
        self.tracker.observe(snapshot);

        // Rotate state.
        self.previous_statuses = std::mem::take(&mut self.current_statuses);
        self.current_statuses = new_statuses;
        self.last_changes = changes.clone();
        self.iteration += 1;

        changes
    }

    /// Access the underlying aggregate convergence tracker.
    #[must_use]
    pub fn tracker(&self) -> &ConvergenceTracker {
        &self.tracker
    }

    /// Per-VC status changes from the most recent observation.
    #[must_use]
    pub fn last_changes(&self) -> &[VcStatusChange] {
        &self.last_changes
    }

    /// VCs that regressed (were proved, now are not) at the most recent observation.
    #[must_use]
    pub fn regressions(&self) -> Vec<&VcStatusChange> {
        self.last_changes.iter().filter(|c| c.is_regression()).collect()
    }

    /// VCs that improved (were not proved, now are) at the most recent observation.
    #[must_use]
    pub fn improvements(&self) -> Vec<&VcStatusChange> {
        self.last_changes.iter().filter(|c| c.is_improvement()).collect()
    }

    /// Convergence score: ratio of proved VCs to total VCs (0.0..=1.0).
    ///
    /// Returns `None` if there are no VCs.
    #[must_use]
    pub fn convergence_score(&self) -> Option<f64> {
        convergence_score_from_statuses(&self.current_statuses)
    }

    /// Current iteration number (0-indexed, incremented after each observe).
    #[must_use]
    pub fn current_iteration(&self) -> u32 {
        self.iteration
    }

    /// True if any VC regressed at the most recent observation.
    #[must_use]
    pub fn has_regressions(&self) -> bool {
        self.last_changes.iter().any(VcStatusChange::is_regression)
    }

    /// Current per-VC status map.
    #[must_use]
    pub fn current_statuses(&self) -> &VcStatusMap {
        &self.current_statuses
    }
}

impl Default for VerificationConvergenceTracker {
    fn default() -> Self {
        Self::new(2, 8)
    }
}

// --- Free functions ---

/// Build a `ProofFrontier` from a `CrateVerificationResult`.
impl ProofFrontier {
    /// Construct a `ProofFrontier` by counting VC results from a crate verification.
    ///
    /// Maps `VerificationResult::Proved` to `trusted`, and `Failed`/`Unknown`/`Timeout`
    /// to their respective frontier fields. `certified` and `runtime_checked` are left
    /// at zero because the raw solver result does not distinguish those categories —
    /// that classification happens in `classify_runtime_disposition`.
    #[must_use]
    pub fn from_verification_result(result: &CrateVerificationResult) -> Self {
        let mut trusted = 0u32;
        let mut failed = 0u32;
        let mut unknown = 0u32;

        for func in &result.functions {
            for (_vc, vr) in &func.results {
                // Trust (flywheel backprop): saturating — diagnostic counters far
                // below u32::MAX; the bare `+= 1` was refuted (overflow:add) by
                // Trust's own strict self-verification of this crate.
                match vr {
                    VerificationResult::Proved { .. } => trusted = trusted.saturating_add(1),
                    VerificationResult::Failed { .. } => failed = failed.saturating_add(1),
                    VerificationResult::Unknown { .. } | VerificationResult::Timeout { .. } => {
                        unknown = unknown.saturating_add(1);
                    }
                    _ => {}
                }
            }
        }

        ProofFrontier { trusted, certified: 0, runtime_checked: 0, failed, unknown }
    }
}

/// Extract per-VC statuses from a `CrateVerificationResult`.
fn extract_vc_statuses(result: &CrateVerificationResult) -> VcStatusMap {
    let mut map = VcStatusMap::new();
    for func in &result.functions {
        for (vc, vr) in &func.results {
            let vc_id = (func.function_path.clone(), vc.kind.description());
            map.insert(vc_id, VcStatus::from_result(vr));
        }
    }
    map
}

/// Compute the set of VCs whose status changed between two iterations.
fn compute_changes(old: &VcStatusMap, new: &VcStatusMap) -> Vec<VcStatusChange> {
    let mut changes = Vec::new();

    // Check VCs present in new results.
    for (vc_id, &new_status) in new {
        if let Some(&old_status) = old.get(vc_id)
            && old_status != new_status
        {
            changes.push(VcStatusChange { vc_id: vc_id.clone(), old_status, new_status });
        }
        // VCs that appear for the first time are not status *changes*.
    }

    // VCs that disappeared (present in old but not new) are regressions
    // if they were previously proved.
    for (vc_id, &old_status) in old {
        if !new.contains_key(vc_id) {
            changes.push(VcStatusChange {
                vc_id: vc_id.clone(),
                old_status,
                new_status: VcStatus::Unknown,
            });
        }
    }

    changes
}

/// Compute convergence score from a status map.
fn convergence_score_from_statuses(statuses: &VcStatusMap) -> Option<f64> {
    let total = statuses.len();
    if total == 0 {
        return None;
    }
    let proved = statuses.values().filter(|&&s| s == VcStatus::Proved).count();
    Some(proved as f64 / total as f64)
}

#[cfg(test)]
mod tests {
    use trust_types::{
        CrateVerificationResult, Formula, FunctionVerificationResult, ProofStrength, SourceSpan,
        VcKind, VerificationCondition, VerificationResult,
    };

    use super::*;

    fn make_vc(kind: VcKind, function: &str) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: function.into(),
            location: SourceSpan {
                file: "test.rs".into(),
                line_start: 1,
                col_start: 1,
                line_end: 1,
                col_end: 1,
            },
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        }
    }

    fn proved() -> VerificationResult {
        VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: 1,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }

    fn failed() -> VerificationResult {
        VerificationResult::Failed { solver: "ay".into(), time_ms: 1, counterexample: None }
    }

    fn unknown() -> VerificationResult {
        VerificationResult::Unknown { solver: "ay".into(), time_ms: 1, reason: "idk".into() }
    }

    fn timeout() -> VerificationResult {
        VerificationResult::Timeout { solver: "ay".into(), timeout_ms: 5000 }
    }

    fn make_crate_result(
        pairs: Vec<(&str, Vec<(VcKind, VerificationResult)>)>,
    ) -> CrateVerificationResult {
        let mut cr = CrateVerificationResult::new("test_crate");
        for (func_name, vc_results) in pairs {
            let results = vc_results
                .into_iter()
                .map(|(kind, vr)| (make_vc(kind, func_name), vr))
                .collect::<Vec<_>>();
            cr.add_function(FunctionVerificationResult {
                function_path: func_name.to_string(),
                function_name: func_name.to_string(),
                results,
                from_notes: 0,
                with_assumptions: 0,
            });
        }
        cr
    }

    // -- ProofFrontier::from_verification_result tests --

    #[test]
    fn test_frontier_from_empty_crate() {
        let cr = CrateVerificationResult::new("empty");
        let frontier = ProofFrontier::from_verification_result(&cr);
        assert_eq!(frontier.trusted, 0);
        assert_eq!(frontier.failed, 0);
        assert_eq!(frontier.unknown, 0);
    }

    #[test]
    fn test_frontier_from_mixed_results() {
        let cr = make_crate_result(vec![
            ("foo", vec![(VcKind::DivisionByZero, proved()), (VcKind::IndexOutOfBounds, failed())]),
            ("bar", vec![(VcKind::Postcondition, unknown()), (VcKind::Unreachable, timeout())]),
        ]);
        let frontier = ProofFrontier::from_verification_result(&cr);
        assert_eq!(frontier.trusted, 1);
        assert_eq!(frontier.certified, 0);
        assert_eq!(frontier.runtime_checked, 0);
        assert_eq!(frontier.failed, 1);
        assert_eq!(frontier.unknown, 2); // Unknown + Timeout
    }

    // -- Convergence score tests --

    #[test]
    fn test_convergence_score_all_proved() {
        let mut tracker = VerificationConvergenceTracker::new(3, 10);
        let cr = make_crate_result(vec![(
            "foo",
            vec![(VcKind::DivisionByZero, proved()), (VcKind::IndexOutOfBounds, proved())],
        )]);
        tracker.observe(&cr);
        let score = tracker.convergence_score().expect("should have score");
        assert!((score - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_convergence_score_half_proved() {
        let mut tracker = VerificationConvergenceTracker::new(3, 10);
        let cr = make_crate_result(vec![(
            "foo",
            vec![(VcKind::DivisionByZero, proved()), (VcKind::IndexOutOfBounds, failed())],
        )]);
        tracker.observe(&cr);
        let score = tracker.convergence_score().expect("should have score");
        assert!((score - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_convergence_score_none_when_empty() {
        let tracker = VerificationConvergenceTracker::new(3, 10);
        assert!(tracker.convergence_score().is_none());
    }

    // -- Per-VC status change tracking --

    #[test]
    fn test_first_observation_no_changes() {
        let mut tracker = VerificationConvergenceTracker::new(3, 10);
        let cr = make_crate_result(vec![("foo", vec![(VcKind::DivisionByZero, proved())])]);
        let changes = tracker.observe(&cr);
        assert!(changes.is_empty(), "first observation should produce no changes");
    }

    #[test]
    fn test_improvement_detected() {
        let mut tracker = VerificationConvergenceTracker::new(3, 10);
        // Iteration 0: foo/div-by-zero fails.
        let cr0 = make_crate_result(vec![("foo", vec![(VcKind::DivisionByZero, failed())])]);
        tracker.observe(&cr0);

        // Iteration 1: foo/div-by-zero now proved.
        let cr1 = make_crate_result(vec![("foo", vec![(VcKind::DivisionByZero, proved())])]);
        let changes = tracker.observe(&cr1);
        assert_eq!(changes.len(), 1);
        assert!(changes[0].is_improvement());
        assert!(!changes[0].is_regression());
        assert!(!tracker.has_regressions());
    }

    #[test]
    fn test_regression_detected() {
        let mut tracker = VerificationConvergenceTracker::new(3, 10);
        // Iteration 0: proved.
        let cr0 = make_crate_result(vec![("foo", vec![(VcKind::DivisionByZero, proved())])]);
        tracker.observe(&cr0);

        // Iteration 1: now fails.
        let cr1 = make_crate_result(vec![("foo", vec![(VcKind::DivisionByZero, failed())])]);
        let changes = tracker.observe(&cr1);
        assert_eq!(changes.len(), 1);
        assert!(changes[0].is_regression());
        assert!(tracker.has_regressions());
        assert_eq!(tracker.regressions().len(), 1);
    }

    #[test]
    fn test_stagnation_no_changes() {
        let mut tracker = VerificationConvergenceTracker::new(3, 10);
        let cr = make_crate_result(vec![(
            "foo",
            vec![(VcKind::DivisionByZero, proved()), (VcKind::IndexOutOfBounds, failed())],
        )]);
        tracker.observe(&cr);

        // Observe same result — no changes.
        let cr2 = make_crate_result(vec![(
            "foo",
            vec![(VcKind::DivisionByZero, proved()), (VcKind::IndexOutOfBounds, failed())],
        )]);
        let changes = tracker.observe(&cr2);
        assert!(changes.is_empty(), "identical results should produce no changes");
        assert!(!tracker.has_regressions());
    }

    #[test]
    fn test_disappeared_vc_detected_as_change() {
        let mut tracker = VerificationConvergenceTracker::new(3, 10);
        // Iteration 0: two VCs.
        let cr0 = make_crate_result(vec![(
            "foo",
            vec![(VcKind::DivisionByZero, proved()), (VcKind::IndexOutOfBounds, proved())],
        )]);
        tracker.observe(&cr0);

        // Iteration 1: one VC disappeared.
        let cr1 = make_crate_result(vec![("foo", vec![(VcKind::DivisionByZero, proved())])]);
        let changes = tracker.observe(&cr1);
        assert_eq!(changes.len(), 1);
        // Disappeared proved VC is a regression.
        assert!(changes[0].is_regression());
    }

    #[test]
    fn test_convergence_across_multiple_iterations() {
        let mut tracker = VerificationConvergenceTracker::new(3, 10);

        // Iteration 0: 2 proved, 1 failed.
        let cr0 = make_crate_result(vec![(
            "foo",
            vec![
                (VcKind::DivisionByZero, proved()),
                (VcKind::IndexOutOfBounds, proved()),
                (VcKind::Postcondition, failed()),
            ],
        )]);
        tracker.observe(&cr0);
        let score0 = tracker.convergence_score().expect("score");
        assert!((score0 - 2.0 / 3.0).abs() < 0.01);

        // Iteration 1: postcondition now proved.
        let cr1 = make_crate_result(vec![(
            "foo",
            vec![
                (VcKind::DivisionByZero, proved()),
                (VcKind::IndexOutOfBounds, proved()),
                (VcKind::Postcondition, proved()),
            ],
        )]);
        let changes = tracker.observe(&cr1);
        assert_eq!(changes.len(), 1);
        assert!(changes[0].is_improvement());
        let score1 = tracker.convergence_score().expect("score");
        assert!((score1 - 1.0).abs() < f64::EPSILON);
        assert!(score1 > score0);
    }

    #[test]
    fn test_score_with_timeout_and_unknown() {
        let mut tracker = VerificationConvergenceTracker::new(3, 10);
        let cr = make_crate_result(vec![(
            "foo",
            vec![
                (VcKind::DivisionByZero, proved()),
                (VcKind::IndexOutOfBounds, timeout()),
                (VcKind::Postcondition, unknown()),
                (VcKind::Unreachable, failed()),
            ],
        )]);
        tracker.observe(&cr);
        let score = tracker.convergence_score().expect("score");
        assert!((score - 0.25).abs() < f64::EPSILON); // 1 proved / 4 total
    }

    #[test]
    fn test_multiple_functions_tracked() {
        let mut tracker = VerificationConvergenceTracker::new(3, 10);
        // Iteration 0: both functions have failures.
        let cr0 = make_crate_result(vec![
            ("foo", vec![(VcKind::DivisionByZero, failed())]),
            ("bar", vec![(VcKind::Postcondition, failed())]),
        ]);
        tracker.observe(&cr0);
        assert!((tracker.convergence_score().expect("score")).abs() < f64::EPSILON);

        // Iteration 1: foo proved, bar still fails.
        let cr1 = make_crate_result(vec![
            ("foo", vec![(VcKind::DivisionByZero, proved())]),
            ("bar", vec![(VcKind::Postcondition, failed())]),
        ]);
        let changes = tracker.observe(&cr1);
        assert_eq!(changes.len(), 1);
        assert!(changes[0].is_improvement());
        assert!((tracker.convergence_score().expect("score") - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_regression_after_improvement() {
        let mut tracker = VerificationConvergenceTracker::new(3, 10);

        // Iteration 0: failed.
        let cr0 = make_crate_result(vec![("foo", vec![(VcKind::DivisionByZero, failed())])]);
        tracker.observe(&cr0);

        // Iteration 1: proved (improvement).
        let cr1 = make_crate_result(vec![("foo", vec![(VcKind::DivisionByZero, proved())])]);
        let changes1 = tracker.observe(&cr1);
        assert_eq!(changes1.len(), 1);
        assert!(changes1[0].is_improvement());

        // Iteration 2: back to failed (regression).
        let cr2 = make_crate_result(vec![("foo", vec![(VcKind::DivisionByZero, failed())])]);
        let changes2 = tracker.observe(&cr2);
        assert_eq!(changes2.len(), 1);
        assert!(changes2[0].is_regression());
        assert!(tracker.has_regressions());
    }
}
