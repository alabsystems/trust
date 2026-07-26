// Shared data types for the rewrite loop: proposal summaries, repair artifacts,
// and source-backpropagation blockers.

use serde::Serialize;
use trust_backprop::{AuditTrail, PendingRewrite, SourceRewrite, UnifiedDiff};
use trust_types::{Counterexample, SourceSpan};

use super::convergence::ProofFrontier;
use crate::report::CompilerDiagnostic;
use crate::types::VerificationResult;

/// A proposed source rewrite from analyzing verification failures.
#[derive(Debug, Clone)]
#[allow(dead_code)] // Fields used for display and future rewrite application.
pub(crate) struct RewriteProposal {
    pub(crate) function: String,
    pub(crate) kind: String,
    // Payload for the proposal kind: a spec body for native-clause proposals or a
    // replacement/check expression for direct rewrites.
    pub(crate) description: String,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct RepairArtifact {
    pub(crate) schema_version: &'static str,
    pub(crate) summary: RepairRunSummary,
    pub(crate) iterations: Vec<RepairIteration>,
    pub(crate) audit_trail: AuditTrail,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct RepairRunSummary {
    pub(crate) iterations: usize,
    pub(crate) succeeded: bool,
    pub(crate) final_frontier: ProofFrontier,
    pub(crate) final_decision: String,
    pub(crate) total_duration_ms: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) exact_source_type_ownership_artifact_digest: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct RepairIteration {
    pub(crate) iteration: usize,
    pub(crate) command: Vec<String>,
    pub(crate) exit_code: i32,
    pub(crate) frontier: ProofFrontier,
    pub(crate) results: Vec<VerificationResult>,
    pub(crate) compiler_diagnostics: Vec<CompilerDiagnostic>,
    pub(crate) failures: Vec<RepairFailure>,
    pub(crate) proposals: Vec<RepairProposalRecord>,
    pub(crate) applied_rewrites: Vec<SourceRewrite>,
    pub(crate) pending_rewrites: Vec<PendingRewrite>,
    pub(crate) rewrite_records: Vec<RepairRewriteRecord>,
    pub(crate) governance_skips: usize,
    pub(crate) limit_skips: usize,
    pub(crate) duration_ms: u64,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct RepairFailure {
    pub(crate) function_path: String,
    pub(crate) function_name: String,
    pub(crate) kind: String,
    pub(crate) pattern: String,
    pub(crate) description: String,
    pub(crate) location: Option<SourceSpan>,
    pub(crate) solver: String,
    pub(crate) time_ms: Option<u64>,
    pub(crate) counterexample: Option<Counterexample>,
    pub(crate) reason: Option<String>,
    pub(crate) source_context: Option<RepairSourceContext>,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct RepairSourceContext {
    pub(crate) source_file: String,
    pub(crate) signature: String,
    pub(crate) params: Vec<(String, String)>,
    pub(crate) return_type: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct RepairProposalRecord {
    pub(crate) source_file: String,
    pub(crate) function_name: String,
    pub(crate) kind: String,
    pub(crate) confidence: f64,
    pub(crate) rationale: String,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct RepairRewriteRecord {
    pub(crate) status: String,
    pub(crate) policy: Option<String>,
    pub(crate) reviewer_notes: Option<String>,
    pub(crate) rewrite: SourceRewrite,
    pub(crate) diff: Option<UnifiedDiff>,
    pub(crate) preview_error: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct BinarySourceBackpropagationBlocker {
    pub(crate) function: String,
    pub(crate) kind: String,
    pub(crate) source_file: String,
    pub(crate) reason: String,
}
