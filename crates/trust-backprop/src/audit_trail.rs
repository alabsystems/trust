//! Audit trail for all rewrite actions in trust-backprop.
//!
//! Provides a tamper-evident log of every rewrite action: spec insertions,
//! modifications, removals, rollbacks, and reverification results. Each entry
//! hashes the previous entry's hash, forming an integrity chain.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use trust_types::fx::FxHashSet;

/// Action type recorded in the audit trail.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AuditAction {
    /// A new spec attribute was inserted.
    SpecInserted,
    /// An existing spec attribute was modified.
    SpecModified,
    /// A spec attribute was removed.
    SpecRemoved,
    /// A source rewrite was applied.
    RewriteApplied,
    /// A rewrite was rolled back to a checkpoint.
    RewriteRolledBack,
    /// Reverification passed after a rewrite.
    VerificationPassed,
    /// Reverification failed after a rewrite.
    VerificationFailed,
}

/// Approval status recorded in an audit entry.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ApprovalStatus {
    /// Automatically approved by policy.
    Auto,
    /// Approved after manual/AI review.
    Reviewed,
    /// Pending review.
    Pending,
    /// Rejected by policy or reviewer.
    Rejected,
}

/// Reverification result recorded in an audit entry.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ReverificationResult {
    /// Verification passed.
    Passed,
    /// Verification failed with a reason.
    Failed { reason: String },
    /// Verification was not performed.
    NotRun,
}

/// A single entry in the audit trail.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuditEntry {
    /// Monotonic sequence number within the trail.
    pub sequence: u64,
    /// Timestamp (seconds since UNIX epoch).
    pub timestamp: u64,
    /// The action that was performed.
    pub action: AuditAction,
    /// Path to the source file affected.
    pub file_path: String,
    /// Name of the function affected.
    pub function_name: String,
    /// The old spec (before the action), if applicable.
    pub old_spec: Option<String>,
    /// The new spec (after the action), if applicable.
    pub new_spec: Option<String>,
    /// Approval status for this action.
    pub approval_status: ApprovalStatus,
    /// Result of reverification, if performed.
    pub reverification_result: ReverificationResult,
    /// Which prove-strengthen-backprop iteration produced this entry.
    pub iteration: Option<u32>,
    /// Unified diff between before and after source, if applicable.
    pub before_after_diff: Option<String>,
    /// Whether this rewrite can be safely rolled back without side effects.
    pub rollback_safe: bool,
    /// SHA-256 hash of the previous entry (empty string for first entry).
    pub prev_hash: String,
    /// SHA-256 hash of this entry (computed over all fields including prev_hash).
    pub entry_hash: String,
}

/// Summary statistics for an audit trail.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct AuditSummary {
    /// Total number of entries.
    pub total_entries: usize,
    /// Number of specs inserted.
    pub specs_inserted: usize,
    /// Number of specs modified.
    pub specs_modified: usize,
    /// Number of specs removed.
    pub specs_removed: usize,
    /// Number of rewrites applied.
    pub rewrites_applied: usize,
    /// Number of rewrites rolled back.
    pub rewrites_rolled_back: usize,
    /// Number of verifications passed.
    pub verifications_passed: usize,
    /// Number of verifications failed.
    pub verifications_failed: usize,
    /// Number of entries that are safe to roll back.
    pub rollback_safe_count: usize,
    /// Distinct files affected.
    pub distinct_files: usize,
    /// Distinct functions affected.
    pub distinct_functions: usize,
}

impl AuditEntry {
    /// Compute the hash for this entry based on its content and the previous hash.
    #[must_use]
    #[allow(clippy::too_many_arguments)]
    fn compute_hash(
        sequence: u64,
        timestamp: u64,
        action: &AuditAction,
        file_path: &str,
        function_name: &str,
        old_spec: &Option<String>,
        new_spec: &Option<String>,
        approval_status: &ApprovalStatus,
        reverification_result: &ReverificationResult,
        iteration: Option<u32>,
        before_after_diff: &Option<String>,
        rollback_safe: bool,
        prev_hash: &str,
    ) -> String {
        let mut hasher = Sha256::new();
        hasher.update(sequence.to_le_bytes());
        hasher.update(timestamp.to_le_bytes());
        hasher.update(format!("{action:?}").as_bytes());
        hasher.update(file_path.as_bytes());
        hasher.update(function_name.as_bytes());
        if let Some(s) = old_spec {
            hasher.update(s.as_bytes());
        }
        if let Some(s) = new_spec {
            hasher.update(s.as_bytes());
        }
        hasher.update(format!("{approval_status:?}").as_bytes());
        hasher.update(format!("{reverification_result:?}").as_bytes());
        if let Some(iter) = iteration {
            hasher.update(iter.to_le_bytes());
        }
        if let Some(d) = before_after_diff {
            hasher.update(d.as_bytes());
        }
        hasher.update([u8::from(rollback_safe)]);
        hasher.update(prev_hash.as_bytes());
        format!("{:x}", hasher.finalize())
    }
}

/// An ordered, integrity-chained log of all rewrite actions.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct AuditTrail {
    entries: Vec<AuditEntry>,
}

impl AuditTrail {
    /// Create a new empty audit trail.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Append a new entry to the trail.
    ///
    /// The entry's `sequence`, `prev_hash`, and `entry_hash` are computed
    /// automatically. Callers set the remaining fields via the builder.
    pub fn append(&mut self, entry: AuditEntryBuilder) {
        let sequence = self.entries.len() as u64;
        let prev_hash = self.entries.last().map_or_else(String::new, |e| e.entry_hash.clone());

        let entry_hash = AuditEntry::compute_hash(
            sequence,
            entry.timestamp,
            &entry.action,
            &entry.file_path,
            &entry.function_name,
            &entry.old_spec,
            &entry.new_spec,
            &entry.approval_status,
            &entry.reverification_result,
            entry.iteration,
            &entry.before_after_diff,
            entry.rollback_safe,
            &prev_hash,
        );

        self.entries.push(AuditEntry {
            sequence,
            timestamp: entry.timestamp,
            action: entry.action,
            file_path: entry.file_path,
            function_name: entry.function_name,
            old_spec: entry.old_spec,
            new_spec: entry.new_spec,
            approval_status: entry.approval_status,
            reverification_result: entry.reverification_result,
            iteration: entry.iteration,
            before_after_diff: entry.before_after_diff,
            rollback_safe: entry.rollback_safe,
            prev_hash,
            entry_hash,
        });
    }

    /// Number of entries in the trail.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the trail is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Get all entries (immutable).
    #[must_use]
    pub fn entries(&self) -> &[AuditEntry] {
        &self.entries
    }

    /// Query entries by function name.
    #[must_use]
    pub fn query_by_function(&self, name: &str) -> Vec<&AuditEntry> {
        self.entries.iter().filter(|e| e.function_name == name).collect()
    }

    /// Query entries by action type.
    #[must_use]
    pub fn query_by_action(&self, action: &AuditAction) -> Vec<&AuditEntry> {
        self.entries.iter().filter(|e| &e.action == action).collect()
    }

    /// Verify the integrity of the hash chain.
    ///
    /// Returns `true` if every entry's hash is consistent with its content
    /// and the previous entry's hash.
    #[must_use]
    pub fn verify_integrity(&self) -> bool {
        let mut expected_prev = String::new();

        for (i, entry) in self.entries.iter().enumerate() {
            if entry.sequence != i as u64 {
                return false;
            }
            if entry.prev_hash != expected_prev {
                return false;
            }

            let recomputed = AuditEntry::compute_hash(
                entry.sequence,
                entry.timestamp,
                &entry.action,
                &entry.file_path,
                &entry.function_name,
                &entry.old_spec,
                &entry.new_spec,
                &entry.approval_status,
                &entry.reverification_result,
                entry.iteration,
                &entry.before_after_diff,
                entry.rollback_safe,
                &entry.prev_hash,
            );

            if recomputed != entry.entry_hash {
                return false;
            }

            expected_prev = entry.entry_hash.clone();
        }

        true
    }

    /// Query entries by source file path.
    #[must_use]
    pub fn query_by_file(&self, path: &str) -> Vec<&AuditEntry> {
        self.entries.iter().filter(|e| e.file_path == path).collect()
    }

    /// Query entries by approval status.
    #[must_use]
    pub fn query_by_approval_status(&self, status: &ApprovalStatus) -> Vec<&AuditEntry> {
        self.entries.iter().filter(|e| &e.approval_status == status).collect()
    }

    /// Query entries within a time range (inclusive bounds).
    #[must_use]
    pub fn query_by_time_range(&self, start: u64, end: u64) -> Vec<&AuditEntry> {
        self.entries.iter().filter(|e| e.timestamp >= start && e.timestamp <= end).collect()
    }

    /// Query entries by iteration number.
    #[must_use]
    pub fn query_by_iteration(&self, iteration: u32) -> Vec<&AuditEntry> {
        self.entries.iter().filter(|e| e.iteration == Some(iteration)).collect()
    }

    /// Query entries that are safe to roll back.
    #[must_use]
    pub fn query_rollback_safe(&self) -> Vec<&AuditEntry> {
        self.entries.iter().filter(|e| e.rollback_safe).collect()
    }

    /// Compute summary statistics for this trail.
    #[must_use]
    pub fn summary(&self) -> AuditSummary {
        let mut summary = AuditSummary { total_entries: self.entries.len(), ..Default::default() };

        let mut files = FxHashSet::default();
        let mut functions = FxHashSet::default();

        for entry in &self.entries {
            files.insert(&entry.file_path);
            functions.insert(&entry.function_name);

            if entry.rollback_safe {
                summary.rollback_safe_count += 1;
            }

            match &entry.action {
                AuditAction::SpecInserted => summary.specs_inserted += 1,
                AuditAction::SpecModified => summary.specs_modified += 1,
                AuditAction::SpecRemoved => summary.specs_removed += 1,
                AuditAction::RewriteApplied => summary.rewrites_applied += 1,
                AuditAction::RewriteRolledBack => summary.rewrites_rolled_back += 1,
                AuditAction::VerificationPassed => summary.verifications_passed += 1,
                AuditAction::VerificationFailed => summary.verifications_failed += 1,
            }
        }

        summary.distinct_files = files.len();
        summary.distinct_functions = functions.len();
        summary
    }

    /// Export the trail as a JSON string.
    ///
    /// # Errors
    ///
    /// Returns an error if serialization fails (should not happen for valid data).
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Import a trail from a JSON string.
    ///
    /// # Errors
    ///
    /// Returns an error if deserialization fails.
    pub fn from_json(json: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(json)
    }
}

/// Builder for constructing an `AuditEntry` to append to the trail.
///
/// The `sequence`, `prev_hash`, and `entry_hash` fields are set by
/// `AuditTrail::append`.
#[derive(Debug, Clone)]
#[must_use]
pub struct AuditEntryBuilder {
    timestamp: u64,
    action: AuditAction,
    file_path: String,
    function_name: String,
    old_spec: Option<String>,
    new_spec: Option<String>,
    approval_status: ApprovalStatus,
    reverification_result: ReverificationResult,
    iteration: Option<u32>,
    before_after_diff: Option<String>,
    rollback_safe: bool,
}

impl AuditEntryBuilder {
    /// Create a new builder with required fields.
    pub fn new(
        action: AuditAction,
        file_path: impl Into<String>,
        function_name: impl Into<String>,
    ) -> Self {
        Self {
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs(),
            action,
            file_path: file_path.into(),
            function_name: function_name.into(),
            old_spec: None,
            new_spec: None,
            approval_status: ApprovalStatus::Pending,
            reverification_result: ReverificationResult::NotRun,
            iteration: None,
            before_after_diff: None,
            rollback_safe: true,
        }
    }

    /// Set an explicit timestamp (for testing or replays).
    pub fn timestamp(mut self, ts: u64) -> Self {
        self.timestamp = ts;
        self
    }

    /// Set the old spec text.
    pub fn old_spec(mut self, spec: impl Into<String>) -> Self {
        self.old_spec = Some(spec.into());
        self
    }

    /// Set the new spec text.
    pub fn new_spec(mut self, spec: impl Into<String>) -> Self {
        self.new_spec = Some(spec.into());
        self
    }

    /// Set the approval status.
    pub fn approval_status(mut self, status: ApprovalStatus) -> Self {
        self.approval_status = status;
        self
    }

    /// Set the reverification result.
    pub fn reverification_result(mut self, result: ReverificationResult) -> Self {
        self.reverification_result = result;
        self
    }

    /// Set the iteration number.
    pub fn iteration(mut self, iter: u32) -> Self {
        self.iteration = Some(iter);
        self
    }

    /// Set the before/after diff string.
    pub fn before_after_diff(mut self, diff: impl Into<String>) -> Self {
        self.before_after_diff = Some(diff.into());
        self
    }

    /// Mark whether this rewrite is safe to roll back.
    pub fn rollback_safe(mut self, safe: bool) -> Self {
        self.rollback_safe = safe;
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_entry(action: AuditAction, func: &str) -> AuditEntryBuilder {
        AuditEntryBuilder::new(action, "src/lib.rs", func).timestamp(1000)
    }

    // --- AuditTrail basic tests ---

    #[test]
    fn test_new_trail_is_empty() {
        let trail = AuditTrail::new();
        assert!(trail.is_empty());
        assert_eq!(trail.len(), 0);
    }

    #[test]
    fn test_append_increments_length() {
        let mut trail = AuditTrail::new();
        trail.append(make_entry(AuditAction::SpecInserted, "foo"));
        assert_eq!(trail.len(), 1);
        assert!(!trail.is_empty());

        trail.append(make_entry(AuditAction::RewriteApplied, "bar"));
        assert_eq!(trail.len(), 2);
    }

    #[test]
    fn test_sequence_numbers_monotonic() {
        let mut trail = AuditTrail::new();
        trail.append(make_entry(AuditAction::SpecInserted, "a"));
        trail.append(make_entry(AuditAction::SpecModified, "b"));
        trail.append(make_entry(AuditAction::RewriteApplied, "c"));

        for (i, entry) in trail.entries().iter().enumerate() {
            assert_eq!(entry.sequence, i as u64);
        }
    }

    // --- Hash chain integrity tests ---

    #[test]
    fn test_first_entry_has_empty_prev_hash() {
        let mut trail = AuditTrail::new();
        trail.append(make_entry(AuditAction::SpecInserted, "foo"));
        assert_eq!(trail.entries()[0].prev_hash, "");
    }

    #[test]
    fn test_second_entry_chains_to_first() {
        let mut trail = AuditTrail::new();
        trail.append(make_entry(AuditAction::SpecInserted, "foo"));
        trail.append(make_entry(AuditAction::RewriteApplied, "bar"));

        assert_eq!(trail.entries()[1].prev_hash, trail.entries()[0].entry_hash);
    }

    #[test]
    fn test_verify_integrity_valid_chain() {
        let mut trail = AuditTrail::new();
        trail.append(make_entry(AuditAction::SpecInserted, "a"));
        trail.append(make_entry(AuditAction::SpecModified, "b"));
        trail.append(make_entry(AuditAction::VerificationPassed, "a"));
        assert!(trail.verify_integrity());
    }

    #[test]
    fn test_verify_integrity_empty_trail() {
        let trail = AuditTrail::new();
        assert!(trail.verify_integrity());
    }

    #[test]
    fn test_verify_integrity_detects_tampered_hash() {
        let mut trail = AuditTrail::new();
        trail.append(make_entry(AuditAction::SpecInserted, "a"));
        trail.append(make_entry(AuditAction::RewriteApplied, "b"));

        // Tamper with the first entry's hash
        trail.entries[0].entry_hash = "tampered".into();
        assert!(!trail.verify_integrity());
    }

    #[test]
    fn test_verify_integrity_detects_tampered_content() {
        let mut trail = AuditTrail::new();
        trail.append(make_entry(AuditAction::SpecInserted, "a"));

        // Tamper with content without updating hash
        trail.entries[0].function_name = "hacked".into();
        assert!(!trail.verify_integrity());
    }

    #[test]
    fn test_verify_integrity_detects_broken_chain() {
        let mut trail = AuditTrail::new();
        trail.append(make_entry(AuditAction::SpecInserted, "a"));
        trail.append(make_entry(AuditAction::RewriteApplied, "b"));

        // Break the chain link
        trail.entries[1].prev_hash = "wrong".into();
        assert!(!trail.verify_integrity());
    }

    #[test]
    fn test_verify_integrity_detects_wrong_sequence() {
        let mut trail = AuditTrail::new();
        trail.append(make_entry(AuditAction::SpecInserted, "a"));

        trail.entries[0].sequence = 99;
        assert!(!trail.verify_integrity());
    }

    // --- Query tests ---

    #[test]
    fn test_query_by_function_returns_matching() {
        let mut trail = AuditTrail::new();
        trail.append(make_entry(AuditAction::SpecInserted, "foo"));
        trail.append(make_entry(AuditAction::RewriteApplied, "bar"));
        trail.append(make_entry(AuditAction::VerificationPassed, "foo"));

        let results = trail.query_by_function("foo");
        assert_eq!(results.len(), 2);
        assert!(results.iter().all(|e| e.function_name == "foo"));
    }

    #[test]
    fn test_query_by_function_no_match() {
        let mut trail = AuditTrail::new();
        trail.append(make_entry(AuditAction::SpecInserted, "foo"));

        let results = trail.query_by_function("nonexistent");
        assert!(results.is_empty());
    }

    #[test]
    fn test_query_by_action_returns_matching() {
        let mut trail = AuditTrail::new();
        trail.append(make_entry(AuditAction::SpecInserted, "a"));
        trail.append(make_entry(AuditAction::RewriteApplied, "b"));
        trail.append(make_entry(AuditAction::SpecInserted, "c"));

        let results = trail.query_by_action(&AuditAction::SpecInserted);
        assert_eq!(results.len(), 2);
    }

    #[test]
    fn test_query_by_action_no_match() {
        let mut trail = AuditTrail::new();
        trail.append(make_entry(AuditAction::SpecInserted, "a"));

        let results = trail.query_by_action(&AuditAction::RewriteRolledBack);
        assert!(results.is_empty());
    }

    // --- Builder tests ---

    #[test]
    fn test_builder_default_values() {
        let builder = AuditEntryBuilder::new(AuditAction::SpecInserted, "src/lib.rs", "foo");
        assert_eq!(builder.approval_status, ApprovalStatus::Pending);
        assert_eq!(builder.reverification_result, ReverificationResult::NotRun);
        assert!(builder.old_spec.is_none());
        assert!(builder.new_spec.is_none());
    }

    #[test]
    fn test_builder_with_specs() {
        let mut trail = AuditTrail::new();
        trail.append(
            AuditEntryBuilder::new(AuditAction::SpecModified, "src/lib.rs", "foo")
                .timestamp(2000)
                .old_spec("x > 0")
                .new_spec("x > 0 && x < 100")
                .approval_status(ApprovalStatus::Reviewed)
                .reverification_result(ReverificationResult::Passed),
        );

        let entry = &trail.entries()[0];
        assert_eq!(entry.old_spec.as_deref(), Some("x > 0"));
        assert_eq!(entry.new_spec.as_deref(), Some("x > 0 && x < 100"));
        assert_eq!(entry.approval_status, ApprovalStatus::Reviewed);
        assert_eq!(entry.reverification_result, ReverificationResult::Passed);
    }

    #[test]
    fn test_builder_verification_failed() {
        let mut trail = AuditTrail::new();
        trail.append(
            AuditEntryBuilder::new(AuditAction::VerificationFailed, "src/lib.rs", "bar")
                .timestamp(3000)
                .reverification_result(ReverificationResult::Failed {
                    reason: "counterexample found".into(),
                }),
        );

        let entry = &trail.entries()[0];
        assert_eq!(entry.action, AuditAction::VerificationFailed);
        assert!(matches!(
            &entry.reverification_result,
            ReverificationResult::Failed { reason } if reason == "counterexample found"
        ));
    }

    // --- JSON serialization tests ---

    #[test]
    fn test_to_json_roundtrip() {
        let mut trail = AuditTrail::new();
        trail.append(make_entry(AuditAction::SpecInserted, "foo"));
        trail.append(make_entry(AuditAction::RewriteApplied, "bar"));

        let json = trail.to_json().expect("serialization should succeed");
        let restored = AuditTrail::from_json(&json).expect("deserialization should succeed");

        assert_eq!(restored.len(), 2);
        assert_eq!(restored.entries()[0].function_name, "foo");
        assert_eq!(restored.entries()[1].function_name, "bar");
        assert!(restored.verify_integrity());
    }

    #[test]
    fn test_to_json_empty_trail() {
        let trail = AuditTrail::new();
        let json = trail.to_json().expect("serialization should succeed");
        let restored = AuditTrail::from_json(&json).expect("deserialization should succeed");
        assert!(restored.is_empty());
        assert!(restored.verify_integrity());
    }

    #[test]
    fn test_json_preserves_hash_chain() {
        let mut trail = AuditTrail::new();
        trail.append(make_entry(AuditAction::SpecInserted, "a"));
        trail.append(make_entry(AuditAction::SpecModified, "a"));
        trail.append(make_entry(AuditAction::VerificationPassed, "a"));

        let json = trail.to_json().expect("serialization should succeed");
        let restored = AuditTrail::from_json(&json).expect("deserialization should succeed");

        // Hash chain must survive serialization roundtrip
        assert!(restored.verify_integrity());
        for (orig, rest) in trail.entries().iter().zip(restored.entries().iter()) {
            assert_eq!(orig.entry_hash, rest.entry_hash);
            assert_eq!(orig.prev_hash, rest.prev_hash);
        }
    }

    // --- AuditAction tests ---

    #[test]
    fn test_audit_action_equality() {
        assert_eq!(AuditAction::SpecInserted, AuditAction::SpecInserted);
        assert_ne!(AuditAction::SpecInserted, AuditAction::SpecModified);
    }

    #[test]
    fn test_audit_action_serialization() {
        let action = AuditAction::RewriteRolledBack;
        let json = serde_json::to_string(&action).unwrap();
        let restored: AuditAction = serde_json::from_str(&json).unwrap();
        assert_eq!(action, restored);
    }

    // --- Integration test ---

    #[test]
    fn test_full_rewrite_lifecycle_audit() {
        let mut trail = AuditTrail::new();

        // 1. Spec inserted
        trail.append(
            AuditEntryBuilder::new(AuditAction::SpecInserted, "src/lib.rs", "get_midpoint")
                .timestamp(1000)
                .new_spec("a + b < u64::MAX")
                .approval_status(ApprovalStatus::Auto),
        );

        // 2. Rewrite applied
        trail.append(
            AuditEntryBuilder::new(AuditAction::RewriteApplied, "src/lib.rs", "get_midpoint")
                .timestamp(1001)
                .approval_status(ApprovalStatus::Auto),
        );

        // 3. Verification passed
        trail.append(
            AuditEntryBuilder::new(AuditAction::VerificationPassed, "src/lib.rs", "get_midpoint")
                .timestamp(1002)
                .reverification_result(ReverificationResult::Passed),
        );

        assert_eq!(trail.len(), 3);
        assert!(trail.verify_integrity());

        // Query by function
        let midpoint_entries = trail.query_by_function("get_midpoint");
        assert_eq!(midpoint_entries.len(), 3);

        // Query by action
        let applied = trail.query_by_action(&AuditAction::RewriteApplied);
        assert_eq!(applied.len(), 1);
        assert_eq!(applied[0].function_name, "get_midpoint");

        // JSON roundtrip preserves everything
        let json = trail.to_json().unwrap();
        let restored = AuditTrail::from_json(&json).unwrap();
        assert!(restored.verify_integrity());
        assert_eq!(restored.len(), 3);
    }

    #[test]
    fn test_rollback_scenario_audit() {
        let mut trail = AuditTrail::new();

        // Spec inserted
        trail.append(
            AuditEntryBuilder::new(AuditAction::SpecInserted, "src/lib.rs", "compute")
                .timestamp(100)
                .new_spec("x > 0")
                .approval_status(ApprovalStatus::Reviewed),
        );

        // Rewrite applied
        trail.append(
            AuditEntryBuilder::new(AuditAction::RewriteApplied, "src/lib.rs", "compute")
                .timestamp(101)
                .approval_status(ApprovalStatus::Reviewed),
        );

        // Verification failed
        trail.append(
            AuditEntryBuilder::new(AuditAction::VerificationFailed, "src/lib.rs", "compute")
                .timestamp(102)
                .reverification_result(ReverificationResult::Failed {
                    reason: "postcondition violated".into(),
                }),
        );

        // Rollback
        trail.append(
            AuditEntryBuilder::new(AuditAction::RewriteRolledBack, "src/lib.rs", "compute")
                .timestamp(103)
                .approval_status(ApprovalStatus::Auto),
        );

        // Spec removed
        trail.append(
            AuditEntryBuilder::new(AuditAction::SpecRemoved, "src/lib.rs", "compute")
                .timestamp(104)
                .old_spec("x > 0")
                .approval_status(ApprovalStatus::Auto),
        );

        assert_eq!(trail.len(), 5);
        assert!(trail.verify_integrity());

        let rollbacks = trail.query_by_action(&AuditAction::RewriteRolledBack);
        assert_eq!(rollbacks.len(), 1);

        let failures = trail.query_by_action(&AuditAction::VerificationFailed);
        assert_eq!(failures.len(), 1);
    }

    #[test]
    fn test_different_entries_produce_different_hashes() {
        let mut trail = AuditTrail::new();
        trail.append(make_entry(AuditAction::SpecInserted, "foo"));
        trail.append(make_entry(AuditAction::SpecInserted, "bar"));

        // Even though same action and timestamp, different function names
        // should produce different hashes (also different sequences).
        assert_ne!(trail.entries()[0].entry_hash, trail.entries()[1].entry_hash);
    }

    // --- New field tests ---

    #[test]
    fn test_iteration_field_stored() {
        let mut trail = AuditTrail::new();
        trail.append(
            AuditEntryBuilder::new(AuditAction::SpecInserted, "src/lib.rs", "foo")
                .timestamp(1000)
                .iteration(3),
        );
        assert_eq!(trail.entries()[0].iteration, Some(3));
    }

    #[test]
    fn test_iteration_field_none_by_default() {
        let mut trail = AuditTrail::new();
        trail.append(make_entry(AuditAction::SpecInserted, "foo"));
        assert_eq!(trail.entries()[0].iteration, None);
    }

    #[test]
    fn test_before_after_diff_stored() {
        let mut trail = AuditTrail::new();
        trail.append(
            AuditEntryBuilder::new(AuditAction::RewriteApplied, "src/lib.rs", "bar")
                .timestamp(2000)
                .before_after_diff("-old line\n+new line"),
        );
        assert_eq!(trail.entries()[0].before_after_diff.as_deref(), Some("-old line\n+new line"));
    }

    #[test]
    fn test_rollback_safe_default_true() {
        let mut trail = AuditTrail::new();
        trail.append(make_entry(AuditAction::SpecInserted, "foo"));
        assert!(trail.entries()[0].rollback_safe);
    }

    #[test]
    fn test_rollback_safe_set_false() {
        let mut trail = AuditTrail::new();
        trail.append(
            AuditEntryBuilder::new(AuditAction::RewriteApplied, "src/lib.rs", "bar")
                .timestamp(3000)
                .rollback_safe(false),
        );
        assert!(!trail.entries()[0].rollback_safe);
    }

    #[test]
    fn test_new_fields_included_in_hash() {
        let mut trail1 = AuditTrail::new();
        trail1.append(
            AuditEntryBuilder::new(AuditAction::SpecInserted, "src/lib.rs", "foo")
                .timestamp(1000)
                .iteration(1),
        );

        let mut trail2 = AuditTrail::new();
        trail2.append(
            AuditEntryBuilder::new(AuditAction::SpecInserted, "src/lib.rs", "foo")
                .timestamp(1000)
                .iteration(2),
        );

        // Different iterations produce different hashes
        assert_ne!(trail1.entries()[0].entry_hash, trail2.entries()[0].entry_hash);
    }

    #[test]
    fn test_integrity_with_new_fields() {
        let mut trail = AuditTrail::new();
        trail.append(
            AuditEntryBuilder::new(AuditAction::SpecInserted, "src/lib.rs", "foo")
                .timestamp(1000)
                .iteration(1)
                .before_after_diff("+#[requires(\"x > 0\")]")
                .rollback_safe(true),
        );
        trail.append(
            AuditEntryBuilder::new(AuditAction::RewriteApplied, "src/lib.rs", "foo")
                .timestamp(1001)
                .iteration(1)
                .rollback_safe(false),
        );
        assert!(trail.verify_integrity());
    }

    // --- Query method tests ---

    #[test]
    fn test_query_by_file_returns_matching() {
        let mut trail = AuditTrail::new();
        trail.append(
            AuditEntryBuilder::new(AuditAction::SpecInserted, "src/lib.rs", "foo").timestamp(100),
        );
        trail.append(
            AuditEntryBuilder::new(AuditAction::SpecInserted, "src/util.rs", "bar").timestamp(101),
        );
        trail.append(
            AuditEntryBuilder::new(AuditAction::RewriteApplied, "src/lib.rs", "baz").timestamp(102),
        );

        let results = trail.query_by_file("src/lib.rs");
        assert_eq!(results.len(), 2);
        assert!(results.iter().all(|e| e.file_path == "src/lib.rs"));
    }

    #[test]
    fn test_query_by_file_no_match() {
        let mut trail = AuditTrail::new();
        trail.append(make_entry(AuditAction::SpecInserted, "foo"));
        assert!(trail.query_by_file("nonexistent.rs").is_empty());
    }

    #[test]
    fn test_query_by_approval_status() {
        let mut trail = AuditTrail::new();
        trail.append(
            AuditEntryBuilder::new(AuditAction::SpecInserted, "a.rs", "f1")
                .timestamp(100)
                .approval_status(ApprovalStatus::Auto),
        );
        trail.append(
            AuditEntryBuilder::new(AuditAction::SpecInserted, "a.rs", "f2")
                .timestamp(101)
                .approval_status(ApprovalStatus::Reviewed),
        );
        trail.append(
            AuditEntryBuilder::new(AuditAction::RewriteApplied, "a.rs", "f3")
                .timestamp(102)
                .approval_status(ApprovalStatus::Auto),
        );

        let auto = trail.query_by_approval_status(&ApprovalStatus::Auto);
        assert_eq!(auto.len(), 2);

        let reviewed = trail.query_by_approval_status(&ApprovalStatus::Reviewed);
        assert_eq!(reviewed.len(), 1);

        let rejected = trail.query_by_approval_status(&ApprovalStatus::Rejected);
        assert!(rejected.is_empty());
    }

    #[test]
    fn test_query_by_time_range() {
        let mut trail = AuditTrail::new();
        trail
            .append(AuditEntryBuilder::new(AuditAction::SpecInserted, "a.rs", "f1").timestamp(100));
        trail
            .append(AuditEntryBuilder::new(AuditAction::SpecInserted, "a.rs", "f2").timestamp(200));
        trail
            .append(AuditEntryBuilder::new(AuditAction::SpecInserted, "a.rs", "f3").timestamp(300));

        let results = trail.query_by_time_range(100, 200);
        assert_eq!(results.len(), 2);

        let results = trail.query_by_time_range(150, 250);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].function_name, "f2");

        let results = trail.query_by_time_range(400, 500);
        assert!(results.is_empty());
    }

    #[test]
    fn test_query_by_iteration() {
        let mut trail = AuditTrail::new();
        trail.append(
            AuditEntryBuilder::new(AuditAction::SpecInserted, "a.rs", "f1")
                .timestamp(100)
                .iteration(1),
        );
        trail.append(
            AuditEntryBuilder::new(AuditAction::RewriteApplied, "a.rs", "f2")
                .timestamp(101)
                .iteration(2),
        );
        trail.append(
            AuditEntryBuilder::new(AuditAction::VerificationPassed, "a.rs", "f1")
                .timestamp(102)
                .iteration(1),
        );

        let iter1 = trail.query_by_iteration(1);
        assert_eq!(iter1.len(), 2);

        let iter2 = trail.query_by_iteration(2);
        assert_eq!(iter2.len(), 1);

        let iter99 = trail.query_by_iteration(99);
        assert!(iter99.is_empty());
    }

    #[test]
    fn test_query_rollback_safe() {
        let mut trail = AuditTrail::new();
        trail.append(
            AuditEntryBuilder::new(AuditAction::SpecInserted, "a.rs", "f1")
                .timestamp(100)
                .rollback_safe(true),
        );
        trail.append(
            AuditEntryBuilder::new(AuditAction::RewriteApplied, "a.rs", "f2")
                .timestamp(101)
                .rollback_safe(false),
        );

        let safe = trail.query_rollback_safe();
        assert_eq!(safe.len(), 1);
        assert_eq!(safe[0].function_name, "f1");
    }

    // --- Summary tests ---

    #[test]
    fn test_summary_empty_trail() {
        let trail = AuditTrail::new();
        let summary = trail.summary();
        assert_eq!(summary.total_entries, 0);
        assert_eq!(summary.distinct_files, 0);
        assert_eq!(summary.distinct_functions, 0);
    }

    #[test]
    fn test_summary_counts() {
        let mut trail = AuditTrail::new();
        trail.append(
            AuditEntryBuilder::new(AuditAction::SpecInserted, "a.rs", "f1")
                .timestamp(100)
                .rollback_safe(true),
        );
        trail.append(
            AuditEntryBuilder::new(AuditAction::SpecInserted, "b.rs", "f2")
                .timestamp(101)
                .rollback_safe(true),
        );
        trail.append(
            AuditEntryBuilder::new(AuditAction::SpecModified, "a.rs", "f1")
                .timestamp(102)
                .rollback_safe(false),
        );
        trail.append(
            AuditEntryBuilder::new(AuditAction::RewriteApplied, "a.rs", "f1").timestamp(103),
        );
        trail.append(
            AuditEntryBuilder::new(AuditAction::VerificationPassed, "a.rs", "f1").timestamp(104),
        );
        trail.append(
            AuditEntryBuilder::new(AuditAction::VerificationFailed, "b.rs", "f2").timestamp(105),
        );

        let summary = trail.summary();
        assert_eq!(summary.total_entries, 6);
        assert_eq!(summary.specs_inserted, 2);
        assert_eq!(summary.specs_modified, 1);
        assert_eq!(summary.specs_removed, 0);
        assert_eq!(summary.rewrites_applied, 1);
        assert_eq!(summary.rewrites_rolled_back, 0);
        assert_eq!(summary.verifications_passed, 1);
        assert_eq!(summary.verifications_failed, 1);
        assert_eq!(summary.rollback_safe_count, 5); // 2 explicit true + 3 default true
        assert_eq!(summary.distinct_files, 2);
        assert_eq!(summary.distinct_functions, 2);
    }

    #[test]
    fn test_json_roundtrip_with_new_fields() {
        let mut trail = AuditTrail::new();
        trail.append(
            AuditEntryBuilder::new(AuditAction::SpecInserted, "src/lib.rs", "foo")
                .timestamp(1000)
                .iteration(5)
                .before_after_diff("+#[requires(\"x > 0\")]")
                .rollback_safe(true),
        );

        let json = trail.to_json().expect("serialization should succeed");
        let restored = AuditTrail::from_json(&json).expect("deserialization should succeed");

        assert!(restored.verify_integrity());
        assert_eq!(restored.entries()[0].iteration, Some(5));
        assert_eq!(
            restored.entries()[0].before_after_diff.as_deref(),
            Some("+#[requires(\"x > 0\")]")
        );
        assert!(restored.entries()[0].rollback_safe);
    }
}
