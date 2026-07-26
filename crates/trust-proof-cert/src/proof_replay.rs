// trust-proof-cert proof replay and auditing
//
// Proof step replay for auditing verified results. Enables re-checking
// individual proof steps against their dependencies and justifications.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt::Write;

/// The kind of a proof step.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum StepKind {
    /// Assume a premise (hypothesis name/description).
    Assume(String),
    /// Assert a conclusion (assertion description).
    Assert(String),
    /// Deduce a conclusion from a rule (conclusion, rule name).
    Deduce(String, String),
    /// Transform an expression (from, to).
    Transform(String, String),
    /// Apply a rule to arguments (rule name, argument list).
    Apply(String, Vec<String>),
    /// Invoke an axiom (axiom name).
    Axiom(String),
}

/// A single step in a proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofStep {
    /// Unique identifier for this step within the proof.
    pub id: usize,
    /// What kind of step this is.
    pub kind: StepKind,
    /// Human-readable justification for why this step is valid.
    pub justification: String,
    /// IDs of prior steps this step depends on.
    pub dependencies: Vec<usize>,
}

/// Configuration for proof replay.
#[derive(Debug, Clone, PartialEq, Eq)]
#[derive(Default)]
pub struct ReplayConfig {
    /// If true, any invalid step causes immediate failure.
    pub strict_mode: bool,
    /// Maximum number of steps to replay (0 = unlimited).
    pub max_steps: usize,
    /// Whether to record per-step timing information.
    pub record_timing: bool,
}

/// The result of replaying a proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReplayResult {
    /// Number of steps that were replayed.
    pub steps_replayed: usize,
    /// Number of steps that passed validation.
    pub steps_valid: usize,
    /// Number of steps that failed validation.
    pub steps_invalid: usize,
    /// Errors encountered during replay.
    pub errors: Vec<ReplayError>,
}

impl ReplayResult {
    /// Returns true if all replayed steps were valid.
    #[must_use]
    pub fn all_valid(&self) -> bool {
        self.steps_invalid == 0
    }
}

/// An error encountered during proof step replay.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReplayError {
    /// The step that caused the error.
    pub step_id: usize,
    /// Human-readable error message.
    pub message: String,
    /// The kind of replay error.
    pub kind: ReplayErrorKind,
}

/// Classification of replay errors.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ReplayErrorKind {
    /// The step's justification is invalid or missing.
    InvalidJustification,
    /// A dependency referenced by the step does not exist.
    MissingDependency,
    /// The step's content does not match its declared kind.
    StepMismatch,
    /// The step exceeded the replay timeout.
    Timeout,
}

/// The verdict for an audited proof step.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum StepVerdict {
    /// The step is valid.
    Valid,
    /// The step is invalid, with a reason.
    Invalid(String),
    /// The step was skipped during auditing.
    Skipped,
}

/// A single entry in an audit log for proof replay.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReplayAuditEntry {
    /// The step that was audited.
    pub step_id: usize,
    /// Timestamp (unix seconds) when the audit occurred.
    pub timestamp: u64,
    /// The verdict for this step.
    pub result: StepVerdict,
    /// Additional notes about the audit.
    pub notes: String,
}

/// An audit log tracking the replay of proof steps for a certificate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReplayAuditLog {
    /// The entries in this audit log.
    pub entries: Vec<ReplayAuditEntry>,
    /// The certificate ID this audit log is associated with.
    pub certificate_id: String,
}

impl ReplayAuditLog {
    /// Create a new empty audit log for a certificate.
    pub fn new(certificate_id: &str) -> Self {
        Self { entries: Vec::new(), certificate_id: certificate_id.to_string() }
    }

    /// Returns the number of entries.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Returns true if the log is empty.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Count entries with a given verdict kind.
    pub fn count_valid(&self) -> usize {
        self.entries.iter().filter(|e| e.result == StepVerdict::Valid).count()
    }

    /// Count invalid entries.
    pub fn count_invalid(&self) -> usize {
        self.entries.iter().filter(|e| matches!(&e.result, StepVerdict::Invalid(_))).count()
    }

    /// Count skipped entries.
    pub fn count_skipped(&self) -> usize {
        self.entries.iter().filter(|e| e.result == StepVerdict::Skipped).count()
    }
}

/// Engine for replaying and auditing proof steps.
pub struct ReplayEngine {
    config: ReplayConfig,
}

impl ReplayEngine {
    /// Create a new replay engine with the given configuration.
    pub fn new(config: ReplayConfig) -> Self {
        Self { config }
    }

    /// Replay an entire proof, validating each step in sequence.
    #[must_use]
    pub fn replay_proof(&self, steps: &[ProofStep]) -> ReplayResult {
        self.replay_from_checkpoint(steps, 0)
    }

    /// Validate a single proof step against the prior steps in the proof.
    ///
    /// A step is valid if:
    /// 1. It has a non-empty justification.
    /// 2. All its dependencies reference prior steps that exist.
    /// 3. Its kind is internally consistent (e.g., `Deduce` has non-empty fields).
    #[must_use]
    pub fn validate_step(&self, step: &ProofStep, prior_steps: &[ProofStep]) -> bool {
        // Check justification is non-empty
        if step.justification.is_empty() {
            return false;
        }

        // Check all dependencies exist in prior steps
        for dep_id in &step.dependencies {
            if !prior_steps.iter().any(|s| s.id == *dep_id) {
                return false;
            }
        }

        // Check kind-specific consistency
        match &step.kind {
            StepKind::Assume(name) | StepKind::Assert(name) | StepKind::Axiom(name) => {
                !name.is_empty()
            }
            StepKind::Deduce(conclusion, rule) => !conclusion.is_empty() && !rule.is_empty(),
            StepKind::Transform(from, to) => !from.is_empty() && !to.is_empty(),
            StepKind::Apply(rule, args) => !rule.is_empty() && !args.is_empty(),
        }
    }

    /// Replay a proof starting from a given checkpoint step index.
    #[must_use]
    pub fn replay_from_checkpoint(&self, steps: &[ProofStep], from_step: usize) -> ReplayResult {
        let mut result =
            ReplayResult { steps_replayed: 0, steps_valid: 0, steps_invalid: 0, errors: vec![] };

        let effective_steps = if from_step < steps.len() { &steps[from_step..] } else { &[] };

        for (i, step) in effective_steps.iter().enumerate() {
            // Check max_steps limit
            if self.config.max_steps > 0 && result.steps_replayed >= self.config.max_steps {
                break;
            }

            // The prior steps are all steps before the current one in the original array
            let prior_end = from_step + i;
            let prior = &steps[..prior_end];

            let valid = self.validate_step(step, prior);
            result.steps_replayed += 1;

            if valid {
                result.steps_valid += 1;
            } else {
                result.steps_invalid += 1;

                let error = self.classify_error(step, prior);
                result.errors.push(error);

                if self.config.strict_mode {
                    break;
                }
            }
        }

        result
    }

    /// Generate a human-readable audit report from an audit log.
    #[must_use]
    pub fn generate_audit_report(&self, log: &ReplayAuditLog) -> String {
        let mut report = String::new();
        let _ = writeln!(report, "Audit Report for Certificate: {}", log.certificate_id);
        let _ = writeln!(report, "Total Steps Audited: {}", log.len());
        let _ = writeln!(report, "Valid: {}", log.count_valid());
        let _ = writeln!(report, "Invalid: {}", log.count_invalid());
        let _ = writeln!(report, "Skipped: {}", log.count_skipped());
        report.push_str("---\n");

        for entry in &log.entries {
            let verdict_str = match &entry.result {
                StepVerdict::Valid => "VALID".to_string(),
                StepVerdict::Invalid(reason) => format!("INVALID: {reason}"),
                StepVerdict::Skipped => "SKIPPED".to_string(),
            };
            let _ =
                write!(report, "Step {}: {} [t={}]", entry.step_id, verdict_str, entry.timestamp);
            if !entry.notes.is_empty() {
                let _ = write!(report, " -- {}", entry.notes);
            }
            report.push('\n');
        }

        report
    }

    /// Audit all steps in a proof, producing an audit log.
    #[must_use]
    pub fn audit_certificate(&self, steps: &[ProofStep]) -> ReplayAuditLog {
        let cert_id = if steps.is_empty() {
            "empty".to_string()
        } else {
            format!("proof-{}-steps", steps.len())
        };

        let mut log = ReplayAuditLog::new(&cert_id);

        for (i, step) in steps.iter().enumerate() {
            let prior = &steps[..i];
            let valid = self.validate_step(step, prior);

            let (result, notes) = if valid {
                (StepVerdict::Valid, String::new())
            } else {
                let err = self.classify_error(step, prior);
                (StepVerdict::Invalid(err.message.clone()), err.message)
            };

            log.entries.push(ReplayAuditEntry {
                step_id: step.id,
                timestamp: 0, // deterministic for testing
                result,
                notes,
            });
        }

        log
    }

    /// Classify the specific error for an invalid step.
    fn classify_error(&self, step: &ProofStep, prior_steps: &[ProofStep]) -> ReplayError {
        // Check justification first
        if step.justification.is_empty() {
            return ReplayError {
                step_id: step.id,
                message: "empty justification".to_string(),
                kind: ReplayErrorKind::InvalidJustification,
            };
        }

        // Check dependencies
        for dep_id in &step.dependencies {
            if !prior_steps.iter().any(|s| s.id == *dep_id) {
                return ReplayError {
                    step_id: step.id,
                    message: format!("missing dependency: step {dep_id}"),
                    kind: ReplayErrorKind::MissingDependency,
                };
            }
        }

        // Must be a step mismatch (kind-specific validation failed)
        ReplayError {
            step_id: step.id,
            message: format!("step kind validation failed for step {}", step.id),
            kind: ReplayErrorKind::StepMismatch,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn default_engine() -> ReplayEngine {
        ReplayEngine::new(ReplayConfig::default())
    }

    fn strict_engine() -> ReplayEngine {
        ReplayEngine::new(ReplayConfig { strict_mode: true, ..Default::default() })
    }

    fn make_assume(id: usize, name: &str) -> ProofStep {
        ProofStep {
            id,
            kind: StepKind::Assume(name.to_string()),
            justification: "hypothesis".to_string(),
            dependencies: vec![],
        }
    }

    fn make_deduce(id: usize, conclusion: &str, rule: &str, deps: Vec<usize>) -> ProofStep {
        ProofStep {
            id,
            kind: StepKind::Deduce(conclusion.to_string(), rule.to_string()),
            justification: format!("by {rule}"),
            dependencies: deps,
        }
    }

    fn make_assert(id: usize, assertion: &str, deps: Vec<usize>) -> ProofStep {
        ProofStep {
            id,
            kind: StepKind::Assert(assertion.to_string()),
            justification: "direct assertion".to_string(),
            dependencies: deps,
        }
    }

    // -----------------------------------------------------------------------
    // Basic replay
    // -----------------------------------------------------------------------

    #[test]
    fn test_replay_empty_proof() {
        let engine = default_engine();
        let result = engine.replay_proof(&[]);
        assert_eq!(result.steps_replayed, 0);
        assert_eq!(result.steps_valid, 0);
        assert_eq!(result.steps_invalid, 0);
        assert!(result.all_valid());
    }

    #[test]
    fn test_replay_single_assume() {
        let engine = default_engine();
        let steps = vec![make_assume(0, "x > 0")];
        let result = engine.replay_proof(&steps);
        assert_eq!(result.steps_replayed, 1);
        assert_eq!(result.steps_valid, 1);
        assert!(result.all_valid());
    }

    #[test]
    fn test_replay_valid_chain() {
        let engine = default_engine();
        let steps = vec![
            make_assume(0, "x > 0"),
            make_assume(1, "y > 0"),
            make_deduce(2, "x + y > 0", "add_positive", vec![0, 1]),
        ];
        let result = engine.replay_proof(&steps);
        assert_eq!(result.steps_replayed, 3);
        assert_eq!(result.steps_valid, 3);
        assert!(result.all_valid());
    }

    #[test]
    fn test_replay_missing_dependency() {
        let engine = default_engine();
        let steps = vec![
            make_assume(0, "x > 0"),
            // step 2 depends on step 99 which does not exist
            make_deduce(2, "x + y > 0", "add_positive", vec![0, 99]),
        ];
        let result = engine.replay_proof(&steps);
        assert_eq!(result.steps_replayed, 2);
        assert_eq!(result.steps_valid, 1);
        assert_eq!(result.steps_invalid, 1);
        assert!(!result.all_valid());
        assert_eq!(result.errors[0].kind, ReplayErrorKind::MissingDependency);
    }

    #[test]
    fn test_replay_empty_justification() {
        let engine = default_engine();
        let steps = vec![ProofStep {
            id: 0,
            kind: StepKind::Assume("x > 0".to_string()),
            justification: String::new(),
            dependencies: vec![],
        }];
        let result = engine.replay_proof(&steps);
        assert_eq!(result.steps_invalid, 1);
        assert_eq!(result.errors[0].kind, ReplayErrorKind::InvalidJustification);
    }

    #[test]
    fn test_replay_step_mismatch_empty_name() {
        let engine = default_engine();
        let steps = vec![ProofStep {
            id: 0,
            kind: StepKind::Assume(String::new()),
            justification: "valid justification".to_string(),
            dependencies: vec![],
        }];
        let result = engine.replay_proof(&steps);
        assert_eq!(result.steps_invalid, 1);
        assert_eq!(result.errors[0].kind, ReplayErrorKind::StepMismatch);
    }

    // -----------------------------------------------------------------------
    // Strict mode
    // -----------------------------------------------------------------------

    #[test]
    fn test_strict_mode_stops_at_first_error() {
        let engine = strict_engine();
        let steps = vec![
            ProofStep {
                id: 0,
                kind: StepKind::Assume(String::new()),
                justification: "ok".to_string(),
                dependencies: vec![],
            },
            make_assume(1, "y > 0"),
        ];
        let result = engine.replay_proof(&steps);
        // Should stop after first invalid step
        assert_eq!(result.steps_replayed, 1);
        assert_eq!(result.steps_invalid, 1);
        assert_eq!(result.steps_valid, 0);
    }

    // -----------------------------------------------------------------------
    // Max steps
    // -----------------------------------------------------------------------

    #[test]
    fn test_max_steps_limits_replay() {
        let engine = ReplayEngine::new(ReplayConfig { max_steps: 2, ..Default::default() });
        let steps = vec![
            make_assume(0, "a"),
            make_assume(1, "b"),
            make_assume(2, "c"),
            make_assume(3, "d"),
        ];
        let result = engine.replay_proof(&steps);
        assert_eq!(result.steps_replayed, 2);
        assert_eq!(result.steps_valid, 2);
    }

    // -----------------------------------------------------------------------
    // Checkpoint replay
    // -----------------------------------------------------------------------

    #[test]
    fn test_replay_from_checkpoint() {
        let engine = default_engine();
        let steps = vec![
            make_assume(0, "x > 0"),
            make_assume(1, "y > 0"),
            make_deduce(2, "x + y > 0", "add_positive", vec![0, 1]),
        ];
        // Start from step index 1 (skip step 0)
        let result = engine.replay_from_checkpoint(&steps, 1);
        assert_eq!(result.steps_replayed, 2);
        assert_eq!(result.steps_valid, 2);
    }

    #[test]
    fn test_replay_from_checkpoint_beyond_end() {
        let engine = default_engine();
        let steps = vec![make_assume(0, "x > 0")];
        let result = engine.replay_from_checkpoint(&steps, 100);
        assert_eq!(result.steps_replayed, 0);
        assert!(result.all_valid());
    }

    // -----------------------------------------------------------------------
    // validate_step
    // -----------------------------------------------------------------------

    #[test]
    fn test_validate_step_transform() {
        let engine = default_engine();
        let step = ProofStep {
            id: 1,
            kind: StepKind::Transform("a + b".to_string(), "b + a".to_string()),
            justification: "commutativity".to_string(),
            dependencies: vec![0],
        };
        let prior = vec![make_assume(0, "a + b = b + a")];
        assert!(engine.validate_step(&step, &prior));
    }

    #[test]
    fn test_validate_step_apply() {
        let engine = default_engine();
        let step = ProofStep {
            id: 1,
            kind: StepKind::Apply(
                "modus_ponens".to_string(),
                vec!["P".to_string(), "P -> Q".to_string()],
            ),
            justification: "MP application".to_string(),
            dependencies: vec![0],
        };
        let prior = vec![make_assume(0, "P")];
        assert!(engine.validate_step(&step, &prior));
    }

    #[test]
    fn test_validate_step_apply_empty_args() {
        let engine = default_engine();
        let step = ProofStep {
            id: 1,
            kind: StepKind::Apply("modus_ponens".to_string(), vec![]),
            justification: "MP".to_string(),
            dependencies: vec![],
        };
        assert!(!engine.validate_step(&step, &[]));
    }

    #[test]
    fn test_validate_step_axiom() {
        let engine = default_engine();
        let step = ProofStep {
            id: 0,
            kind: StepKind::Axiom("excluded_middle".to_string()),
            justification: "axiom of excluded middle".to_string(),
            dependencies: vec![],
        };
        assert!(engine.validate_step(&step, &[]));
    }

    // -----------------------------------------------------------------------
    // Audit
    // -----------------------------------------------------------------------

    #[test]
    fn test_audit_certificate_all_valid() {
        let engine = default_engine();
        let steps =
            vec![make_assume(0, "x > 0"), make_deduce(1, "x >= 1", "integer_bound", vec![0])];
        let log = engine.audit_certificate(&steps);
        assert_eq!(log.certificate_id, "proof-2-steps");
        assert_eq!(log.len(), 2);
        assert_eq!(log.count_valid(), 2);
        assert_eq!(log.count_invalid(), 0);
    }

    #[test]
    fn test_audit_certificate_with_invalid() {
        let engine = default_engine();
        let steps = vec![
            make_assume(0, "x > 0"),
            make_deduce(1, "result", "rule", vec![99]), // dep 99 missing
        ];
        let log = engine.audit_certificate(&steps);
        assert_eq!(log.count_valid(), 1);
        assert_eq!(log.count_invalid(), 1);
    }

    #[test]
    fn test_audit_certificate_empty() {
        let engine = default_engine();
        let log = engine.audit_certificate(&[]);
        assert_eq!(log.certificate_id, "empty");
        assert!(log.is_empty());
    }

    // -----------------------------------------------------------------------
    // Audit report generation
    // -----------------------------------------------------------------------

    #[test]
    fn test_generate_audit_report_contains_summary() {
        let engine = default_engine();
        let steps = vec![make_assume(0, "x > 0"), make_assert(1, "x >= 0", vec![0])];
        let log = engine.audit_certificate(&steps);
        let report = engine.generate_audit_report(&log);

        assert!(report.contains("Audit Report for Certificate:"));
        assert!(report.contains("Total Steps Audited: 2"));
        assert!(report.contains("Valid: 2"));
        assert!(report.contains("Invalid: 0"));
    }

    #[test]
    fn test_generate_audit_report_shows_invalid_reason() {
        let engine = default_engine();
        let steps = vec![
            make_assume(0, "x > 0"),
            make_deduce(1, "y > 0", "magic", vec![42]), // missing dep
        ];
        let log = engine.audit_certificate(&steps);
        let report = engine.generate_audit_report(&log);
        assert!(report.contains("INVALID"));
        assert!(report.contains("missing dependency"));
    }

    // -----------------------------------------------------------------------
    // ReplayResult helpers
    // -----------------------------------------------------------------------

    #[test]
    fn test_replay_result_all_valid_true() {
        let result =
            ReplayResult { steps_replayed: 3, steps_valid: 3, steps_invalid: 0, errors: vec![] };
        assert!(result.all_valid());
    }

    #[test]
    fn test_replay_result_all_valid_false() {
        let result = ReplayResult {
            steps_replayed: 3,
            steps_valid: 2,
            steps_invalid: 1,
            errors: vec![ReplayError {
                step_id: 2,
                message: "bad".to_string(),
                kind: ReplayErrorKind::StepMismatch,
            }],
        };
        assert!(!result.all_valid());
    }

    // -----------------------------------------------------------------------
    // ReplayAuditLog helpers
    // -----------------------------------------------------------------------

    #[test]
    fn test_audit_log_count_methods() {
        let log = ReplayAuditLog {
            entries: vec![
                ReplayAuditEntry {
                    step_id: 0,
                    timestamp: 0,
                    result: StepVerdict::Valid,
                    notes: String::new(),
                },
                ReplayAuditEntry {
                    step_id: 1,
                    timestamp: 0,
                    result: StepVerdict::Invalid("reason".to_string()),
                    notes: String::new(),
                },
                ReplayAuditEntry {
                    step_id: 2,
                    timestamp: 0,
                    result: StepVerdict::Skipped,
                    notes: String::new(),
                },
            ],
            certificate_id: "test".to_string(),
        };
        assert_eq!(log.count_valid(), 1);
        assert_eq!(log.count_invalid(), 1);
        assert_eq!(log.count_skipped(), 1);
        assert_eq!(log.len(), 3);
        assert!(!log.is_empty());
    }
}
