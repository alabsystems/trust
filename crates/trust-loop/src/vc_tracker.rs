// trust-loop/vc_tracker.rs: Per-VC status tracking with regression detection
//
// Tracks each verification condition's status history across iterations.
// Detects regressions (proved -> non-proved) and provides per-VC delta
// information for the iteration metrics.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use trust_types::{SourceSpan, VerificationCondition, VerificationResult};

/// Status of a single verification condition in one iteration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VcStatus {
    Proved,
    Failed,
    Unknown,
    Timeout,
}

impl VcStatus {
    /// Derive status from a `VerificationResult`.
    #[must_use]
    pub fn from_result(result: &VerificationResult) -> Self {
        match result {
            VerificationResult::Proved { .. } => Self::Proved,
            VerificationResult::Failed { .. } => Self::Failed,
            VerificationResult::Timeout { .. } => Self::Timeout,
            VerificationResult::Unknown { .. } => Self::Unknown,
            _ => Self::Unknown,
        }
    }

    #[must_use]
    pub fn is_proved(self) -> bool {
        matches!(self, Self::Proved)
    }
}

/// A regression event: a VC that was proved but is no longer proved.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RegressionEvent {
    /// The VC slot key identifying which VC regressed.
    pub vc_key: String,
    /// The iteration where regression was detected.
    pub iteration: u32,
    /// The previous status (always Proved for a true regression).
    pub previous_status: VcStatus,
    /// The new (regressed) status.
    pub current_status: VcStatus,
}

/// Per-iteration delta summary computed from the VcTracker.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct VcDelta {
    /// Number of VCs that became proved this iteration.
    pub(crate) newly_proved: usize,
    /// Number of VCs that became failed this iteration.
    pub(crate) newly_failed: usize,
    /// Number of VCs that regressed (proved -> non-proved).
    pub(crate) regressions: usize,
    /// Number of VCs that improved (non-proved -> better status).
    pub(crate) improvements: usize,
    /// Number of VCs unchanged from previous iteration.
    pub(crate) unchanged: usize,
}

/// Tracks per-VC status history across iterations.
#[derive(Debug, Clone, Default)]
pub(crate) struct VcTracker {
    /// Key: vc_slot_key (function|span|kind) -> history of (iteration, status).
    statuses: BTreeMap<String, Vec<(u32, VcStatus)>>,
}

impl VcTracker {
    /// Create a new empty tracker.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Record the status of a VC for a given iteration.
    pub(crate) fn record(&mut self, iteration: u32, vc_key: &str, status: VcStatus) {
        self.statuses.entry(vc_key.to_string()).or_default().push((iteration, status));
    }

    /// Record all results from a verification pass.
    pub(crate) fn record_results(
        &mut self,
        iteration: u32,
        results: &[(VerificationCondition, VerificationResult)],
    ) {
        for (vc, result) in results {
            let key = vc_slot_key(vc);
            let status = VcStatus::from_result(result);
            self.record(iteration, &key, status);
        }
    }

    /// Detect all regressions in the given iteration.
    ///
    /// A regression is any VC that was `Proved` in its most recent prior
    /// observation but is no longer `Proved` in the current iteration.
    #[must_use]
    pub(crate) fn detect_regressions(&self, iteration: u32) -> Vec<RegressionEvent> {
        let mut regressions = Vec::new();

        for (key, history) in &self.statuses {
            if history.len() < 2 {
                continue;
            }

            let current = history.last();
            let previous = history.iter().rev().nth(1);

            if let (Some(&(curr_iter, curr_status)), Some(&(_, prev_status))) = (current, previous)
                && curr_iter == iteration
                && prev_status.is_proved()
                && !curr_status.is_proved()
            {
                regressions.push(RegressionEvent {
                    vc_key: key.clone(),
                    iteration,
                    previous_status: prev_status,
                    current_status: curr_status,
                });
            }
        }

        regressions
    }

    /// Compute the per-VC delta between the current iteration and the previous.
    #[must_use]
    pub(crate) fn compute_delta(&self, iteration: u32) -> VcDelta {
        let mut delta = VcDelta::default();

        for history in self.statuses.values() {
            if history.is_empty() {
                continue;
            }

            let current = history.last();
            let previous = history.iter().rev().nth(1);

            match (current, previous) {
                (Some(&(curr_iter, curr_status)), Some(&(_, prev_status)))
                    if curr_iter == iteration =>
                {
                    if curr_status == prev_status {
                        delta.unchanged += 1;
                    } else if curr_status.is_proved() && !prev_status.is_proved() {
                        delta.newly_proved += 1;
                        delta.improvements += 1;
                    } else if !curr_status.is_proved() && prev_status.is_proved() {
                        delta.regressions += 1;
                        if matches!(curr_status, VcStatus::Failed) {
                            delta.newly_failed += 1;
                        }
                    } else if status_ordinal(curr_status) > status_ordinal(prev_status) {
                        delta.improvements += 1;
                    } else {
                        delta.newly_failed += 1;
                    }
                }
                (Some(&(curr_iter, curr_status)), None) if curr_iter == iteration => {
                    // First observation for this VC.
                    if curr_status.is_proved() {
                        delta.newly_proved += 1;
                    } else if matches!(curr_status, VcStatus::Failed) {
                        delta.newly_failed += 1;
                    }
                }
                _ => {
                    delta.unchanged += 1;
                }
            }
        }

        delta
    }
}
/// Ordinal ranking: higher = better. Used for trend analysis.
/// Ordinal ranking: higher = better. Used for per-VC delta classification.
/// Proved > Failed > Unknown > Timeout.
fn status_ordinal(status: VcStatus) -> u8 {
    match status {
        VcStatus::Proved => 3,
        VcStatus::Failed => 2, // Failed is better than Unknown (at least we know why)
        VcStatus::Unknown => 1,
        VcStatus::Timeout => 0,
    }
}

/// Compute the slot key for a VC (matches the key format in lib.rs).
pub(crate) fn vc_slot_key(vc: &VerificationCondition) -> String {
    format!("{}|{}|{}", vc.function, span_key(&vc.location), vc.kind.description())
}

fn span_key(span: &SourceSpan) -> String {
    format!(
        "{}:{}:{}:{}:{}",
        span.file, span.line_start, span.col_start, span.line_end, span.col_end
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{Formula, ProofStrength, Sort, VcKind};

    fn make_vc(function: &str, kind: VcKind) -> VerificationCondition {
        VerificationCondition {
            function: function.into(),
            kind,
            location: SourceSpan::default(),
            formula: Formula::Var("x".to_string(), Sort::Bool),
            contract_metadata: None,
        }
    }

    fn proved_result() -> VerificationResult {
        VerificationResult::Proved {
            solver: "ay".into(),
            strength: ProofStrength::smt_unsat(),
            time_ms: 1,
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }

    fn failed_result() -> VerificationResult {
        VerificationResult::Failed { solver: "ay".into(), counterexample: None, time_ms: 1 }
    }

    fn unknown_result() -> VerificationResult {
        VerificationResult::Unknown {
            solver: "ay".into(),
            reason: "incomplete".to_string(),
            time_ms: 1,
        }
    }

    fn timeout_result() -> VerificationResult {
        VerificationResult::Timeout { solver: "ay".into(), timeout_ms: 5000 }
    }

    // --- VcStatus ---

    #[test]
    fn test_vc_status_from_result() {
        assert_eq!(VcStatus::from_result(&proved_result()), VcStatus::Proved);
        assert_eq!(VcStatus::from_result(&failed_result()), VcStatus::Failed);
        assert_eq!(VcStatus::from_result(&unknown_result()), VcStatus::Unknown);
        assert_eq!(VcStatus::from_result(&timeout_result()), VcStatus::Timeout);
    }

    #[test]
    fn test_vc_status_is_proved() {
        assert!(VcStatus::Proved.is_proved());
        assert!(!VcStatus::Failed.is_proved());
        assert!(!VcStatus::Unknown.is_proved());
        assert!(!VcStatus::Timeout.is_proved());
    }

    // --- VcTracker basics ---

    #[test]
    fn test_tracker_new_empty() {
        let tracker = VcTracker::new();
        assert!(tracker.statuses.is_empty());
    }

    #[test]
    fn test_tracker_record_results() {
        let mut tracker = VcTracker::new();
        let vc_a = make_vc("crate::f", VcKind::DivisionByZero);
        let key = vc_slot_key(&vc_a);
        let results = vec![(vc_a, proved_result())];
        tracker.record_results(1, &results);

        assert_eq!(tracker.statuses.len(), 1);
        assert_eq!(tracker.statuses.get(&key), Some(&vec![(1, VcStatus::Proved)]));
    }

    // --- Regression detection ---

    #[test]
    fn test_detect_regressions_none_when_improving() {
        let mut tracker = VcTracker::new();
        tracker.record(1, "vc_a", VcStatus::Failed);
        tracker.record(2, "vc_a", VcStatus::Proved);

        let regressions = tracker.detect_regressions(2);
        assert!(regressions.is_empty());
    }

    #[test]
    fn test_detect_regressions_proved_to_failed() {
        let mut tracker = VcTracker::new();
        tracker.record(1, "vc_a", VcStatus::Proved);
        tracker.record(2, "vc_a", VcStatus::Failed);

        let regressions = tracker.detect_regressions(2);
        assert_eq!(regressions.len(), 1);
        assert_eq!(regressions[0].vc_key, "vc_a");
        assert_eq!(regressions[0].iteration, 2);
        assert_eq!(regressions[0].previous_status, VcStatus::Proved);
        assert_eq!(regressions[0].current_status, VcStatus::Failed);
    }

    #[test]
    fn test_detect_regressions_proved_to_unknown() {
        let mut tracker = VcTracker::new();
        tracker.record(1, "vc_a", VcStatus::Proved);
        tracker.record(2, "vc_a", VcStatus::Unknown);

        let regressions = tracker.detect_regressions(2);
        assert_eq!(regressions.len(), 1);
        assert_eq!(regressions[0].current_status, VcStatus::Unknown);
    }

    #[test]
    fn test_detect_regressions_multiple_vcs() {
        let mut tracker = VcTracker::new();
        // vc_a: proved -> failed (regression)
        tracker.record(1, "vc_a", VcStatus::Proved);
        tracker.record(2, "vc_a", VcStatus::Failed);
        // vc_b: proved -> proved (no regression)
        tracker.record(1, "vc_b", VcStatus::Proved);
        tracker.record(2, "vc_b", VcStatus::Proved);
        // vc_c: failed -> proved (improvement)
        tracker.record(1, "vc_c", VcStatus::Failed);
        tracker.record(2, "vc_c", VcStatus::Proved);

        let regressions = tracker.detect_regressions(2);
        assert_eq!(regressions.len(), 1);
        assert_eq!(regressions[0].vc_key, "vc_a");
    }

    #[test]
    fn test_detect_regressions_wrong_iteration() {
        let mut tracker = VcTracker::new();
        tracker.record(1, "vc_a", VcStatus::Proved);
        tracker.record(2, "vc_a", VcStatus::Failed);

        // Ask about iteration 3 -- no data for iter 3
        let regressions = tracker.detect_regressions(3);
        assert!(regressions.is_empty());
    }

    // --- VcDelta ---

    #[test]
    fn test_compute_delta_newly_proved() {
        let mut tracker = VcTracker::new();
        tracker.record(1, "vc_a", VcStatus::Failed);
        tracker.record(2, "vc_a", VcStatus::Proved);

        let delta = tracker.compute_delta(2);
        assert_eq!(delta.newly_proved, 1);
        assert_eq!(delta.regressions, 0);
    }

    #[test]
    fn test_compute_delta_regression() {
        let mut tracker = VcTracker::new();
        tracker.record(1, "vc_a", VcStatus::Proved);
        tracker.record(2, "vc_a", VcStatus::Failed);

        let delta = tracker.compute_delta(2);
        assert_eq!(delta.regressions, 1);
        assert_eq!(delta.newly_failed, 1);
        assert_eq!(delta.newly_proved, 0);
    }

    #[test]
    fn test_compute_delta_unchanged() {
        let mut tracker = VcTracker::new();
        tracker.record(1, "vc_a", VcStatus::Failed);
        tracker.record(2, "vc_a", VcStatus::Failed);

        let delta = tracker.compute_delta(2);
        assert_eq!(delta.unchanged, 1);
        assert_eq!(delta.newly_proved, 0);
        assert_eq!(delta.regressions, 0);
    }

    #[test]
    fn test_compute_delta_mixed() {
        let mut tracker = VcTracker::new();
        // vc_a: failed -> proved (newly proved)
        tracker.record(1, "vc_a", VcStatus::Failed);
        tracker.record(2, "vc_a", VcStatus::Proved);
        // vc_b: proved -> failed (regression)
        tracker.record(1, "vc_b", VcStatus::Proved);
        tracker.record(2, "vc_b", VcStatus::Failed);
        // vc_c: failed -> failed (unchanged)
        tracker.record(1, "vc_c", VcStatus::Failed);
        tracker.record(2, "vc_c", VcStatus::Failed);

        let delta = tracker.compute_delta(2);
        assert_eq!(delta.newly_proved, 1);
        assert_eq!(delta.regressions, 1);
        assert_eq!(delta.unchanged, 1);
    }

    #[test]
    fn test_compute_delta_first_iteration() {
        let mut tracker = VcTracker::new();
        tracker.record(1, "vc_a", VcStatus::Proved);
        tracker.record(1, "vc_b", VcStatus::Failed);

        let delta = tracker.compute_delta(1);
        assert_eq!(delta.newly_proved, 1);
        assert_eq!(delta.newly_failed, 1);
    }
}
