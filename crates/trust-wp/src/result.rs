// trust_wp result types
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Result types for trust_wp deductive verification.
//!
//! `TrustWpResult` is the primary output type, containing the overall verdict
//! plus per-function results, inferred loop invariants, and diagnostics.

use serde::{Deserialize, Serialize};

/// The outcome of a trust_wp verification run.
///
/// Matches the result structure from trust-wp's `StructuredVerificationResult`
/// protocol, translated into Trust's type system.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrustWpResult {
    /// The overall verification verdict.
    pub verdict: Verdict,

    /// Per-function verdicts (when verifying multiple functions).
    pub function_verdicts: Vec<FunctionVerdict>,

    /// Loop invariants inferred during verification.
    pub loop_invariants: Vec<LoopInvariant>,

    /// Proof certificate bytes if verification succeeded and
    /// `TrustWpConfig::produce_proofs` was enabled.
    pub proof_certificate: Option<Vec<u8>>,

    /// Wall-clock time for the verification in milliseconds.
    pub time_ms: u64,

    /// Diagnostic messages captured during verification
    /// (populated when `DiagConfig::Capture` is used).
    pub diagnostics: Vec<DiagnosticMessage>,

    /// The function that was verified (primary target).
    pub function_name: String,

    /// Counts from trust-wp's structured result protocol.
    pub counts: VerificationCounts,
}

impl TrustWpResult {
    /// Returns `true` if all functions were verified.
    #[must_use]
    pub fn is_verified(&self) -> bool {
        matches!(self.verdict, Verdict::Verified)
    }

    /// Returns `true` if any function's contracts were disproven.
    #[must_use]
    pub fn is_failed(&self) -> bool {
        matches!(self.verdict, Verdict::Failed)
    }

    /// Returns `true` if the result is inconclusive.
    #[must_use]
    pub fn is_unknown(&self) -> bool {
        matches!(self.verdict, Verdict::Unknown { .. })
    }

    /// Convert to a `trust_types::VerificationResult` for the router.
    #[must_use]
    pub fn to_verification_result(&self) -> trust_types::VerificationResult {
        match &self.verdict {
            Verdict::Verified => trust_types::VerificationResult::Proved {
                solver: "trust-wp-lib".into(),
                time_ms: self.time_ms,
                strength: trust_types::ProofStrength::deductive(),
                proof_certificate: self.proof_certificate.clone(),
                solver_warnings: None,
                native_proof_envelope: None,
            },
            Verdict::Failed => {
                // trust_wp produces deductive failures, not concrete counterexamples
                // in the same way as BMC. The function_verdicts carry the details.
                trust_types::VerificationResult::Failed {
                    solver: "trust-wp-lib".into(),
                    time_ms: self.time_ms,
                    counterexample: None,
                }
            }
            Verdict::Unknown { reason } => trust_types::VerificationResult::Unknown {
                solver: "trust-wp-lib".into(),
                time_ms: self.time_ms,
                reason: reason.clone(),
            },
            Verdict::Timeout => trust_types::VerificationResult::Timeout {
                solver: "trust-wp-lib".into(),
                timeout_ms: self.time_ms,
            },
            Verdict::Error { message } => trust_types::VerificationResult::Unknown {
                solver: "trust-wp-lib".into(),
                time_ms: self.time_ms,
                reason: format!("trust-wp error: {message}"),
            },
        }
    }
}

/// The verification verdict from trust_wp.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Verdict {
    /// All contracts were verified (UNSAT for all VCs).
    Verified,

    /// At least one contract was disproven.
    Failed,

    /// The result is inconclusive.
    Unknown {
        /// Reason the result is inconclusive.
        reason: String,
    },

    /// The verifier timed out.
    Timeout,

    /// An internal error occurred during verification.
    Error {
        /// Error message.
        message: String,
    },
}

/// Per-function verification verdict.
///
/// When trust_wp verifies a module, each function gets an individual verdict.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionVerdict {
    /// Fully qualified function name.
    pub function_name: String,

    /// The verdict for this function.
    pub verdict: Verdict,

    /// Number of proof obligations generated.
    pub obligation_count: u32,

    /// Number of obligations successfully discharged.
    pub discharged_count: u32,

    /// Whether this function depends on unproven axioms.
    pub has_axiom_deps: bool,
}

/// A loop invariant inferred by trust_wp.
///
/// Represents a candidate invariant discovered by trust-wp's abstract
/// interpretation or annotation inference. These can be fed back into
/// the verification pipeline for strengthening.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LoopInvariant {
    /// The function containing the loop.
    pub function_name: String,

    /// Loop identifier (basic block index or source location).
    pub loop_id: String,

    /// The invariant expression as a string.
    /// Uses trust-wp's expression syntax.
    pub expression: String,

    /// Confidence level: how certain trust_wp is about this invariant.
    /// Range: 0.0 (guess) to 1.0 (proven).
    pub confidence: f64,

    /// Whether this invariant has been verified by the solver.
    pub verified: bool,
}

/// Counts from trust-wp's structured result protocol.
///
/// Mirrors the fields from `trust-wp-core::result_protocol::StructuredVerificationResult`
/// without depending on trust-wp-core.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct VerificationCounts {
    /// Functions whose contracts were proven correct.
    pub verified: u64,
    /// Functions whose contracts were disproven.
    pub failed: u64,
    /// Functions with encoding/solver errors.
    pub errors: u64,
    /// Dropped obligation warnings.
    pub warnings: u64,
    /// Functions whose contracts were assumed correct.
    pub assumed: u64,
    /// `#[trusted]`-annotated functions skipped by design.
    pub trusted: u64,
    /// Functions skipped (no MIR body).
    pub skipped: u64,
    /// Functions verified but depending on unproven axioms.
    pub verified_with_axiom_deps: u64,
}

/// A diagnostic message from trust_wp during verification.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DiagnosticMessage {
    /// Severity level.
    pub level: DiagLevel,
    /// The message text.
    pub message: String,
    /// Source location if available.
    pub location: Option<String>,
}

/// Diagnostic severity level.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum DiagLevel {
    /// Error diagnostic.
    Error,
    /// Warning diagnostic.
    Warning,
    /// Note/info diagnostic.
    Note,
}
