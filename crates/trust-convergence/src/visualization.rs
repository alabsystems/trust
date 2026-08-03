// trust-convergence/visualization.rs: Frontier snapshot export for dashboard visualization.
//
// Exports proof frontier state at each iteration into a JSON-serializable format
// suitable for rendering in the trust-report HTML dashboard.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::integration::{VcStatus, VerificationConvergenceTracker};

/// A snapshot of the proof frontier at a single iteration, suitable for JSON export.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrontierSnapshot {
    /// Loop iteration number.
    pub iteration: u32,
    /// Number of VCs that are proved.
    pub proved_count: usize,
    /// Number of VCs that failed verification.
    pub failed_count: usize,
    /// Number of VCs with unknown or timeout status.
    pub unknown_count: usize,
    /// Unix timestamp in seconds (0 if not set).
    pub timestamp: u64,
    /// Identifiers of proved VCs (function_path::vc_description).
    pub proved_vcs: Vec<String>,
    /// Identifiers of failed VCs (function_path::vc_description).
    pub failed_vcs: Vec<String>,
}

impl FrontierSnapshot {
    /// Total number of VCs tracked in this snapshot.
    ///
    /// Trust (flywheel backprop): saturating — the counts are diagnostics far
    /// below `usize::MAX`, so saturation is semantically a no-op, and the sum
    /// PROVES under Trust's own strict verifier (the bare `+` was refuted as
    /// an unprovable `overflow:add` when Trust verified this crate — the first
    /// self-verification hardening driven by `targo trust check` on
    /// trust-convergence itself).
    #[must_use]
    pub fn total_vcs(&self) -> usize {
        self.proved_count.saturating_add(self.failed_count).saturating_add(self.unknown_count)
    }

    /// Convergence ratio: proved / total (0.0..=1.0). Returns `None` if no VCs.
    #[must_use]
    pub fn convergence_ratio(&self) -> Option<f64> {
        let total = self.total_vcs();
        if total == 0 {
            return None;
        }
        Some(self.proved_count as f64 / total as f64)
    }
}

/// Build a `FrontierSnapshot` from the current state of a `VerificationConvergenceTracker`.
#[must_use]
pub fn from_tracker(tracker: &VerificationConvergenceTracker) -> FrontierSnapshot {
    from_tracker_with_timestamp(tracker, 0)
}

/// Build a `FrontierSnapshot` with an explicit timestamp.
#[must_use]
pub fn from_tracker_with_timestamp(
    tracker: &VerificationConvergenceTracker,
    timestamp: u64,
) -> FrontierSnapshot {
    let statuses = tracker.current_statuses();
    let mut proved_vcs = Vec::new();
    let mut failed_vcs = Vec::new();
    let mut unknown_count = 0usize;

    for ((func_path, vc_desc), &status) in statuses {
        let vc_label = format!("{func_path}::{vc_desc}");
        match status {
            VcStatus::Proved => proved_vcs.push(vc_label),
            VcStatus::Failed => failed_vcs.push(vc_label),
            VcStatus::Unknown | VcStatus::Timeout => unknown_count += 1,
        }
    }

    proved_vcs.sort();
    failed_vcs.sort();

    FrontierSnapshot {
        iteration: tracker.current_iteration(),
        proved_count: proved_vcs.len(),
        failed_count: failed_vcs.len(),
        unknown_count,
        timestamp,
        proved_vcs,
        failed_vcs,
    }
}

/// Serialize a sequence of frontier snapshots to a JSON string.
///
/// Returns a prettified JSON array for human readability in dashboard contexts.
#[must_use]
pub fn to_json(snapshots: &[FrontierSnapshot]) -> String {
    // SAFETY: FrontierSnapshot derives Serialize with only primitive/String fields;
    // serde_json serialization of such types cannot fail.
    serde_json::to_string_pretty(snapshots)
        .unwrap_or_else(|e| unreachable!("FrontierSnapshot serialization failed: {e}"))
}

/// Deserialize frontier snapshots from a JSON string.
///
/// # Errors
///
/// Returns an error if the JSON is malformed or does not match the expected schema.
pub fn from_json(json: &str) -> Result<Vec<FrontierSnapshot>, serde_json::Error> {
    serde_json::from_str(json)
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

    #[test]
    fn test_from_tracker_empty() {
        let tracker = VerificationConvergenceTracker::new(3, 10);
        let snap = from_tracker(&tracker);
        assert_eq!(snap.iteration, 0);
        assert_eq!(snap.proved_count, 0);
        assert_eq!(snap.failed_count, 0);
        assert_eq!(snap.unknown_count, 0);
        assert!(snap.proved_vcs.is_empty());
        assert!(snap.failed_vcs.is_empty());
        assert_eq!(snap.timestamp, 0);
    }

    #[test]
    fn test_from_tracker_mixed_results() {
        let mut tracker = VerificationConvergenceTracker::new(3, 10);
        let cr = make_crate_result(vec![(
            "foo",
            vec![
                (VcKind::DivisionByZero, proved()),
                (VcKind::IndexOutOfBounds, failed()),
                (VcKind::Postcondition, unknown()),
            ],
        )]);
        tracker.observe(&cr);

        let snap = from_tracker(&tracker);
        assert_eq!(snap.iteration, 1);
        assert_eq!(snap.proved_count, 1);
        assert_eq!(snap.failed_count, 1);
        assert_eq!(snap.unknown_count, 1);
        assert_eq!(snap.total_vcs(), 3);
    }

    #[test]
    fn test_from_tracker_with_timestamp() {
        let mut tracker = VerificationConvergenceTracker::new(3, 10);
        let cr = make_crate_result(vec![("foo", vec![(VcKind::DivisionByZero, proved())])]);
        tracker.observe(&cr);

        let snap = from_tracker_with_timestamp(&tracker, 1711612800);
        assert_eq!(snap.timestamp, 1711612800);
    }

    #[test]
    fn test_convergence_ratio() {
        let snap = FrontierSnapshot {
            iteration: 0,
            proved_count: 3,
            failed_count: 1,
            unknown_count: 1,
            timestamp: 0,
            proved_vcs: vec![],
            failed_vcs: vec![],
        };
        let ratio = snap.convergence_ratio().expect("ratio");
        assert!((ratio - 0.6).abs() < f64::EPSILON);
    }

    #[test]
    fn test_convergence_ratio_empty() {
        let snap = FrontierSnapshot {
            iteration: 0,
            proved_count: 0,
            failed_count: 0,
            unknown_count: 0,
            timestamp: 0,
            proved_vcs: vec![],
            failed_vcs: vec![],
        };
        assert!(snap.convergence_ratio().is_none());
    }

    #[test]
    fn test_to_json_roundtrip() {
        let snapshots = vec![
            FrontierSnapshot {
                iteration: 0,
                proved_count: 2,
                failed_count: 1,
                unknown_count: 0,
                timestamp: 100,
                proved_vcs: vec!["foo::div_by_zero".into(), "foo::postcondition".into()],
                failed_vcs: vec!["bar::index_bounds".into()],
            },
            FrontierSnapshot {
                iteration: 1,
                proved_count: 3,
                failed_count: 0,
                unknown_count: 0,
                timestamp: 200,
                proved_vcs: vec![
                    "bar::index_bounds".into(),
                    "foo::div_by_zero".into(),
                    "foo::postcondition".into(),
                ],
                failed_vcs: vec![],
            },
        ];

        let json = to_json(&snapshots);
        let deserialized = from_json(&json).expect("valid json");
        assert_eq!(deserialized, snapshots);
    }

    #[test]
    fn test_from_json_invalid() {
        let result = from_json("not valid json");
        assert!(result.is_err());
    }

    #[test]
    fn test_snapshot_vcs_are_sorted() {
        let mut tracker = VerificationConvergenceTracker::new(3, 10);
        let cr = make_crate_result(vec![
            ("zebra", vec![(VcKind::DivisionByZero, proved())]),
            ("alpha", vec![(VcKind::Postcondition, proved())]),
            ("middle", vec![(VcKind::IndexOutOfBounds, failed())]),
        ]);
        tracker.observe(&cr);

        let snap = from_tracker(&tracker);
        // Proved VCs should be sorted alphabetically.
        assert_eq!(snap.proved_count, 2);
        assert!(snap.proved_vcs.windows(2).all(|w| w[0] <= w[1]));
    }

    #[test]
    fn test_multiple_snapshots_to_json() {
        let snapshots: Vec<FrontierSnapshot> = (0..3)
            .map(|i| FrontierSnapshot {
                iteration: i,
                proved_count: i as usize,
                failed_count: 0,
                unknown_count: 3 - i as usize,
                timestamp: 0,
                proved_vcs: vec![],
                failed_vcs: vec![],
            })
            .collect();
        let json = to_json(&snapshots);
        assert!(json.contains("\"iteration\": 0"));
        assert!(json.contains("\"iteration\": 2"));
    }
}
