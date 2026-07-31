// targo-trust types: core data structures for verification results
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use anyhow::Result;
use serde::{Deserialize, Serialize};
use trust_types::{
    Aarch64SyncBoundarySemanticFact, BinaryArtifactDigestIdentity, BinaryOrigin,
    BinarySourceProvenanceSummary, Counterexample, PreservedSymbolicFormula, SourceSpan,
    TargetValidationBlocker, UnsupportedRecord,
};

use crate::verify_binary_evidence::{
    CheckedCertificateImportReport, CheckedCertificateProductionReport, VerifyBinaryEvidence,
};

// ---------------------------------------------------------------------------
// Output format
// ---------------------------------------------------------------------------

/// Report output format for verification results.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum OutputFormat {
    Terminal,
    Json,
    Html,
}

impl OutputFormat {
    pub(crate) fn from_str(s: &str) -> Result<Self> {
        match s {
            "terminal" => Ok(Self::Terminal),
            "json" => Ok(Self::Json),
            "html" => Ok(Self::Html),
            other => anyhow::bail!("unknown format `{other}`: expected terminal, json, or html"),
        }
    }
}

// ---------------------------------------------------------------------------
// Subcommand
// ---------------------------------------------------------------------------

/// Top-level subcommands.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Subcommand {
    /// Check-only: verify without producing a binary.
    Check,
    /// Build: verify and produce a binary.
    Build,
    /// Test: verify, compile, and execute Cargo-selected test executables with
    /// kernel-certified monitors installed. Evidence-grade execution uses
    /// sealed handle-bound launch on Linux or suspended-process/CDHash
    /// authentication on macOS, on x86-64/aarch64, and fails closed elsewhere.
    /// Only clauses reached by those test processes are checked at runtime;
    /// this is not monitor-coverage proof.
    Test,
    /// Report: generate a verification report in the requested format.
    Report,
    /// Loop: run the prove-strengthen-backprop convergence loop.
    Loop,
    /// Diff: compare current verification state against a baseline.
    Diff,
    /// Solvers: detect and report status of solver binaries.
    Solvers,
    /// Init: scaffold verification annotations for a crate.
    #[allow(dead_code)]
    Init,
}

// ---------------------------------------------------------------------------
// Binary lift report
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum BinaryLiftStatus {
    Ok,
    Incomplete,
    Failed,
}

impl BinaryLiftStatus {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Ok => "ok",
            Self::Incomplete => "incomplete",
            Self::Failed => "failed",
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct BinaryLiftFunctionReport {
    pub(crate) name: String,
    pub(crate) entry: Option<String>,
    pub(crate) blocks: usize,
    pub(crate) statements: usize,
    pub(crate) vcs: usize,
    #[serde(default)]
    pub(crate) instruction_provenance: Vec<BinaryOrigin>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct BinaryLiftReport {
    pub(crate) binary: String,
    pub(crate) format: Option<String>,
    pub(crate) architecture: Option<String>,
    pub(crate) selection: String,
    pub(crate) entry: Option<String>,
    pub(crate) binary_entry: Option<String>,
    pub(crate) strict: bool,
    pub(crate) status: BinaryLiftStatus,
    pub(crate) functions_lifted: usize,
    pub(crate) blocks: usize,
    pub(crate) statements: usize,
    pub(crate) vcs: usize,
    pub(crate) unsupported: usize,
    pub(crate) failures: usize,
    pub(crate) functions: Vec<BinaryLiftFunctionReport>,
    pub(crate) unsupported_items: Vec<String>,
    pub(crate) failure_items: Vec<String>,
}

// ---------------------------------------------------------------------------
// Binary verification report
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct BinaryVcKindCount {
    pub(crate) kind: String,
    pub(crate) count: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct BinaryVerifyFunctionReport {
    pub(crate) name: String,
    pub(crate) entry: Option<String>,
    pub(crate) blocks: usize,
    pub(crate) statements: usize,
    pub(crate) vcs: usize,
    pub(crate) vc_counts: Vec<BinaryVcKindCount>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct BinarySolverSummary {
    pub(crate) status: String,
    pub(crate) total: usize,
    pub(crate) proved: usize,
    pub(crate) failed: usize,
    pub(crate) unknown: usize,
    pub(crate) timeout: usize,
}

impl BinarySolverSummary {
    pub(crate) fn not_run() -> Self {
        Self { status: "not_run".into(), total: 0, proved: 0, failed: 0, unknown: 0, timeout: 0 }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct BinarySolverResultReport {
    pub(crate) function: String,
    pub(crate) vc_kind: String,
    pub(crate) location: Option<String>,
    pub(crate) solver: String,
    pub(crate) status: String,
    pub(crate) time_ms: u64,
    pub(crate) detail: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) replay_status: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) replay_detail: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) replay_capability_evidence: Vec<trust_symex::BinaryMachineReplayCapabilityEvidence>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) replay_capability_evidence_matched: Option<bool>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct BinaryVerifyReport {
    pub(crate) binary: String,
    pub(crate) format: Option<String>,
    pub(crate) architecture: Option<String>,
    pub(crate) selection: String,
    pub(crate) entry: Option<String>,
    pub(crate) binary_entry: Option<String>,
    pub(crate) strict: bool,
    pub(crate) status: BinaryLiftStatus,
    pub(crate) verification_status: String,
    pub(crate) trust_level: String,
    pub(crate) solver_results: BinarySolverSummary,
    pub(crate) functions_analyzed: usize,
    pub(crate) blocks: usize,
    pub(crate) statements: usize,
    pub(crate) vcs: usize,
    pub(crate) vc_counts: Vec<BinaryVcKindCount>,
    pub(crate) unsupported: usize,
    pub(crate) failures: usize,
    pub(crate) functions: Vec<BinaryVerifyFunctionReport>,
    pub(crate) unsupported_items: Vec<String>,
    pub(crate) failure_items: Vec<String>,
    pub(crate) solver_result_items: Vec<BinarySolverResultReport>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) checked_certificate_import: Option<CheckedCertificateImportReport>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) checked_certificate_production: Option<CheckedCertificateProductionReport>,
    #[serde(skip)]
    pub(crate) proof_evidence: VerifyBinaryEvidence,
}

// ---------------------------------------------------------------------------
// Binary decompilation report
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum DecompileTarget {
    TrustIr,
    Rust,
    // Trust: the on-the-wire/CLI canonical name uses a hyphen
    // (`trust-cg`) to match the sibling repo and the `label()` method.
    // The snake_case rename would otherwise emit `trust_cg`.
    #[serde(rename = "trust-cg")]
    TrustCg,
    Wasm,
}

impl DecompileTarget {
    pub(crate) fn from_convert_str(s: &str) -> Result<Self> {
        match s {
            "trust_ir" => Ok(Self::TrustIr),
            "rust" => Ok(Self::Rust),
            "trust-cg" => Ok(Self::TrustCg),
            "wasm" => Ok(Self::Wasm),
            other => {
                anyhow::bail!(
                    "unknown convert target `{other}`: expected trust_ir, rust, trust-cg, or wasm"
                )
            }
        }
    }

    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::TrustIr => "trust_ir",
            Self::Rust => "rust",
            Self::TrustCg => "trust-cg",
            Self::Wasm => "wasm",
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct DecompileFunctionReport {
    pub(crate) name: String,
    pub(crate) entry: String,
    pub(crate) blocks: usize,
    pub(crate) instructions: usize,
    pub(crate) statements: usize,
    pub(crate) memory_facts: usize,
    pub(crate) unsupported: usize,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) instruction_provenance: Vec<BinaryOrigin>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct DecompileProofGradeEvidenceReport {
    pub(crate) schema_version: String,
    pub(crate) producer: String,
    pub(crate) artifact_trust_level: String,
    pub(crate) binary_verification_trust_level: String,
    pub(crate) binary_verification_status: String,
    pub(crate) binary_replay: String,
    pub(crate) required_vcs: usize,
    pub(crate) proved_vcs: usize,
    pub(crate) checked_certificate_identity: bool,
    pub(crate) exact_replay_identity: bool,
    pub(crate) binary_artifact_digest_identity: bool,
    pub(crate) exact_source_provenance: bool,
    pub(crate) reconstruction_accepted: bool,
    pub(crate) target_validation_accepted: bool,
    pub(crate) unsupported_ledger_empty: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct ReleaseTranscriptBindingReport {
    pub(crate) schema_version: String,
    pub(crate) commit_sha256: String,
    pub(crate) binary_sha256: Option<String>,
    pub(crate) selected_image_sha256: Option<String>,
    pub(crate) selected_image_file_offset: Option<u64>,
    pub(crate) selected_image_file_size: Option<u64>,
    pub(crate) vc_sha256: Option<String>,
    pub(crate) checked_certificate_sha256: Option<String>,
    pub(crate) replay_transcript_sha256: Option<String>,
    pub(crate) provenance_sha256: Option<String>,
    pub(crate) target_consumer_evidence_sha256: Option<String>,
    pub(crate) target_consumer_binding_sha256: Option<String>,
    pub(crate) status: String,
    #[serde(default)]
    pub(crate) blockers: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct ProofGradeReleaseSelectedImageReport {
    pub(crate) identity: String,
    pub(crate) digest: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct ProofGradeReleaseVcDigestEntryReport {
    pub(crate) schema_version: String,
    pub(crate) artifact_kind: String,
    pub(crate) digest_algorithm: String,
    pub(crate) digest: String,
    pub(crate) candidate_commit: String,
    pub(crate) binary_digest: String,
    pub(crate) selected_image: ProofGradeReleaseSelectedImageReport,
    pub(crate) inventory_index: usize,
    pub(crate) inventory_count: usize,
    pub(crate) vc_id: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct ProofGradeReleaseCheckedCertificateDigestEntryReport {
    pub(crate) schema_version: String,
    pub(crate) artifact_kind: String,
    pub(crate) digest_algorithm: String,
    pub(crate) digest: String,
    pub(crate) candidate_commit: String,
    pub(crate) binary_digest: String,
    pub(crate) selected_image: ProofGradeReleaseSelectedImageReport,
    pub(crate) inventory_index: usize,
    pub(crate) inventory_count: usize,
    pub(crate) vc_digest: String,
    pub(crate) certificate_role: String,
    pub(crate) readback_status: String,
}

fn default_proof_grade_release_evidence_origin() -> String {
    "unknown".to_string()
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct ProofGradeReleaseEvidenceDigestReport {
    pub(crate) status: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) digest: Option<String>,
}

impl Default for ProofGradeReleaseEvidenceDigestReport {
    fn default() -> Self {
        Self { status: "missing".to_string(), digest: None }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct ProofGradeReleaseAarch64OrderingMonitorEvidenceReport {
    pub(crate) status: String,
    pub(crate) opcode: String,
    pub(crate) ordering: String,
    pub(crate) exclusive_monitor: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) digest: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) blockers: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct ProofGradeReleaseTranscriptRowReport {
    pub(crate) schema_version: String,
    pub(crate) row_type: String,
    #[serde(default = "default_proof_grade_release_evidence_origin")]
    pub(crate) evidence_origin: String,
    pub(crate) status: String,
    pub(crate) accepted: bool,
    pub(crate) rejection_reason: Option<String>,
    pub(crate) candidate_commit: Option<String>,
    pub(crate) proof_required_vc_count: usize,
    pub(crate) binary_digest: Option<String>,
    pub(crate) selected_image: Option<ProofGradeReleaseSelectedImageReport>,
    #[serde(default)]
    pub(crate) vc_digests: Vec<ProofGradeReleaseVcDigestEntryReport>,
    #[serde(default)]
    pub(crate) checked_certificate_digests:
        Vec<ProofGradeReleaseCheckedCertificateDigestEntryReport>,
    #[serde(default)]
    pub(crate) replay_transcript_digests: Vec<String>,
    #[serde(default)]
    pub(crate) provenance_artifact_digests: Vec<String>,
    pub(crate) unsupported_ledgers_empty: bool,
    #[serde(default)]
    pub(crate) target_proof_consumer_artifact_digests: Vec<String>,
    #[serde(default)]
    pub(crate) exact_source_ownership_evidence: ProofGradeReleaseEvidenceDigestReport,
    #[serde(default)]
    pub(crate) type_ownership_evidence: ProofGradeReleaseEvidenceDigestReport,
    #[serde(default)]
    pub(crate) aarch64_ordering_monitor_evidence:
        Vec<ProofGradeReleaseAarch64OrderingMonitorEvidenceReport>,
    pub(crate) release_transcript_binding_digest: Option<String>,
    #[serde(default)]
    pub(crate) blockers: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct ProofGradeReleaseTranscriptReport {
    pub(crate) schema_version: String,
    #[serde(default)]
    pub(crate) accepted_proof_grade_rows: Vec<ProofGradeReleaseTranscriptRowReport>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) blocked_proof_grade_rows: Vec<ProofGradeReleaseTranscriptRowReport>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct DecompileProofCertificateEvidenceReport {
    pub(crate) status: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) checker: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) format: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) artifact_path: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) reason: Option<String>,
    pub(crate) production_checker_evidence_status: String,
}

impl Default for DecompileProofCertificateEvidenceReport {
    fn default() -> Self {
        Self {
            status: "not_requested".to_string(),
            checker: None,
            format: None,
            sha256: None,
            artifact_path: None,
            reason: None,
            production_checker_evidence_status: "missing".to_string(),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct DecompileUnsupportedLedgerReport {
    pub(crate) empty: bool,
    pub(crate) total_records: usize,
    #[serde(default)]
    pub(crate) by_stage: BTreeMap<String, usize>,
    #[serde(default)]
    pub(crate) by_feature: BTreeMap<String, usize>,
    #[serde(default)]
    pub(crate) by_family: BTreeMap<String, usize>,
    #[serde(default)]
    pub(crate) aarch64_sync_boundary_facts: Vec<Aarch64SyncBoundarySemanticFact>,
    #[serde(default)]
    pub(crate) aarch64_sync_boundary_fact_count: usize,
    #[serde(default)]
    pub(crate) records: Vec<UnsupportedRecord>,
}

impl Default for DecompileUnsupportedLedgerReport {
    fn default() -> Self {
        Self {
            empty: true,
            total_records: 0,
            by_stage: BTreeMap::new(),
            by_feature: BTreeMap::new(),
            by_family: BTreeMap::new(),
            aarch64_sync_boundary_facts: Vec::new(),
            aarch64_sync_boundary_fact_count: 0,
            records: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct DecompileSolverDispatchEvidenceReport {
    pub(crate) id: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) function: Option<String>,
    pub(crate) status: String,
    pub(crate) query_semantics: String,
    pub(crate) replay: String,
    pub(crate) proof_certificate: DecompileProofCertificateEvidenceReport,
    pub(crate) checked_certificate: bool,
    pub(crate) exact_replay: bool,
    pub(crate) exact_instruction_provenance: bool,
    pub(crate) exact_source_provenance: bool,
    pub(crate) replay_digest_identity_accepted: bool,
    #[serde(default)]
    pub(crate) replay_digest_identity_blockers: Vec<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) binary_artifact_digest_identity: Option<BinaryArtifactDigestIdentity>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) vc_kind: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) origin: Option<BinaryOrigin>,
    #[serde(default)]
    pub(crate) diagnostics: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct DecompileEvidenceBlockerReport {
    pub(crate) code: String,
    pub(crate) stage: String,
    pub(crate) feature: String,
    pub(crate) detail: String,
    #[serde(default)]
    pub(crate) evidence_required: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct DecompileReleaseGateReport {
    pub(crate) accepted: bool,
    pub(crate) status: String,
    pub(crate) reason: String,
    #[serde(default)]
    pub(crate) blockers: Vec<DecompileEvidenceBlockerReport>,
}

impl Default for DecompileReleaseGateReport {
    fn default() -> Self {
        Self {
            accepted: false,
            status: "rejected".to_string(),
            reason: "binary decompilation evidence is missing".to_string(),
            blockers: vec![DecompileEvidenceBlockerReport {
                code: "binary-verification-missing".to_string(),
                stage: "targo-trust::decompile-binary-evidence".to_string(),
                feature: "proof-grade-binary-verification".to_string(),
                detail: "no binary verification dispatch evidence was attached to the decompile artifact".to_string(),
                evidence_required: vec!["binary_vc_solver_dispatch".to_string()],
            }],
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct DecompileBinaryEvidenceReport {
    pub(crate) schema_version: String,
    pub(crate) verification_status: String,
    pub(crate) verification_trust_level: String,
    pub(crate) total_vcs: usize,
    pub(crate) proved_vcs: usize,
    pub(crate) failed_vcs: usize,
    pub(crate) unknown_vcs: usize,
    pub(crate) timeout_vcs: usize,
    pub(crate) unsupported_vcs: usize,
    pub(crate) rejected_vcs: usize,
    pub(crate) replay_status: String,
    pub(crate) proof_certificate: DecompileProofCertificateEvidenceReport,
    pub(crate) checked_certificate_dispatches: usize,
    pub(crate) replayed_dispatches: usize,
    pub(crate) replay_digest_identity_dispatches: usize,
    pub(crate) exact_instruction_provenance_dispatches: usize,
    pub(crate) exact_source_provenance_dispatches: usize,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) binary_artifact_digest_identity: Option<BinaryArtifactDigestIdentity>,
    pub(crate) unsupported_ledger: DecompileUnsupportedLedgerReport,
    pub(crate) verification_unsupported_ledger: DecompileUnsupportedLedgerReport,
    #[serde(default)]
    pub(crate) solver_dispatches: Vec<DecompileSolverDispatchEvidenceReport>,
    pub(crate) release_gate: DecompileReleaseGateReport,
}

impl Default for DecompileBinaryEvidenceReport {
    fn default() -> Self {
        Self {
            schema_version: "targo-trust-decompile-binary-evidence.v1".to_string(),
            verification_status: "not_run".to_string(),
            verification_trust_level: "partial".to_string(),
            total_vcs: 0,
            proved_vcs: 0,
            failed_vcs: 0,
            unknown_vcs: 0,
            timeout_vcs: 0,
            unsupported_vcs: 0,
            rejected_vcs: 0,
            replay_status: "not_attempted".to_string(),
            proof_certificate: DecompileProofCertificateEvidenceReport::default(),
            checked_certificate_dispatches: 0,
            replayed_dispatches: 0,
            replay_digest_identity_dispatches: 0,
            exact_instruction_provenance_dispatches: 0,
            exact_source_provenance_dispatches: 0,
            binary_artifact_digest_identity: None,
            unsupported_ledger: DecompileUnsupportedLedgerReport::default(),
            verification_unsupported_ledger: DecompileUnsupportedLedgerReport::default(),
            solver_dispatches: Vec::new(),
            release_gate: DecompileReleaseGateReport::default(),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct DecompileReport {
    pub(crate) binary: String,
    pub(crate) format: Option<String>,
    pub(crate) architecture: Option<String>,
    pub(crate) selection: String,
    pub(crate) entry: Option<String>,
    pub(crate) binary_entry: Option<String>,
    #[serde(default)]
    pub(crate) source_provenance: BinarySourceProvenanceSummary,
    pub(crate) strict: bool,
    pub(crate) target: DecompileTarget,
    pub(crate) status: BinaryLiftStatus,
    pub(crate) output_kind: Option<String>,
    pub(crate) output_trust_level: String,
    pub(crate) output_validation: String,
    pub(crate) validation_note: String,
    pub(crate) output_content: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) production_proof_grade_evidence: Option<DecompileProofGradeEvidenceReport>,
    #[serde(default)]
    pub(crate) binary_evidence: DecompileBinaryEvidenceReport,
    #[serde(default)]
    pub(crate) target_validation_blockers: Vec<TargetValidationBlocker>,
    #[serde(default)]
    pub(crate) preserved_symbolic_formulas: Vec<PreservedSymbolicFormula>,
    pub(crate) functions_decompiled: usize,
    pub(crate) blocks: usize,
    pub(crate) instructions: usize,
    pub(crate) statements: usize,
    pub(crate) memory_facts: usize,
    pub(crate) unsupported: usize,
    pub(crate) failures: usize,
    pub(crate) functions: Vec<DecompileFunctionReport>,
    pub(crate) unsupported_items: Vec<String>,
    pub(crate) failure_items: Vec<String>,
}

// ---------------------------------------------------------------------------
// Exploit-finding scaffold report
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum ExploitFindTarget {
    Compiler,
    Verifier,
    Lifter,
}

impl ExploitFindTarget {
    pub(crate) fn from_str(s: &str) -> Result<Self> {
        match s {
            "compiler" => Ok(Self::Compiler),
            "verifier" => Ok(Self::Verifier),
            "lifter" => Ok(Self::Lifter),
            other => anyhow::bail!(
                "unknown exploit-find target `{other}`: expected compiler, verifier, or lifter"
            ),
        }
    }

    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Compiler => "compiler",
            Self::Verifier => "verifier",
            Self::Lifter => "lifter",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum ExploitFindStatus {
    NotRun,
    Unsupported,
    Satisfied,
}

impl ExploitFindStatus {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::NotRun => "not_run",
            Self::Unsupported => "unsupported",
            Self::Satisfied => "satisfied",
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct ExploitFindReport {
    pub(crate) input: String,
    pub(crate) target: ExploitFindTarget,
    pub(crate) status: ExploitFindStatus,
    pub(crate) exploit_found: bool,
    pub(crate) binary_status: BinaryLiftStatus,
    pub(crate) verification_status: String,
    pub(crate) functions_analyzed: usize,
    pub(crate) vcs: usize,
    pub(crate) vc_counts: Vec<BinaryVcKindCount>,
    pub(crate) solver_results: BinarySolverSummary,
    pub(crate) unsupported: usize,
    pub(crate) failures: usize,
    pub(crate) independent_refutation_status: ExploitFindStatus,
    pub(crate) independent_refutation_note: String,
    pub(crate) reducer_status: ExploitFindStatus,
    pub(crate) reducer_note: String,
    pub(crate) synthesis_status: ExploitFindStatus,
    pub(crate) synthesis_note: String,
    pub(crate) replay_status: ExploitFindStatus,
    pub(crate) replay_note: String,
    pub(crate) reason: String,
    pub(crate) binary_report: BinaryVerifyReport,
    pub(crate) notes: Vec<String>,
}

// ---------------------------------------------------------------------------
// Verification result parsing
// ---------------------------------------------------------------------------

/// Outcome of a single verification obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum VerificationOutcome {
    Proved,
    Failed,
    RuntimeChecked,
    Timeout,
    Unknown,
}

impl VerificationOutcome {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Proved => "PROVED",
            Self::Failed => "FAILED",
            Self::RuntimeChecked => "RUNTIME-CHECKED",
            Self::Timeout => "TIMEOUT",
            Self::Unknown => "UNKNOWN",
        }
    }

    pub(crate) fn is_proved(self) -> bool {
        matches!(self, Self::Proved)
    }

    pub(crate) fn is_failed(self) -> bool {
        matches!(self, Self::Failed)
    }

    pub(crate) fn is_runtime_checked(self) -> bool {
        matches!(self, Self::RuntimeChecked)
    }

    pub(crate) fn is_inconclusive(self) -> bool {
        matches!(self, Self::Unknown | Self::Timeout)
    }
}

impl From<trust_types::Outcome> for VerificationOutcome {
    /// Project a compiler outcome onto the buckets targo reports.
    ///
    /// Targo's surface is coarser than the compiler's on purpose: an admitted
    /// assumption, a capability gap, an external cancellation, and refused
    /// evidence are all reported as `Unknown`, because none of them is a
    /// verdict a reader may act on. The finer classification stays available on
    /// the transport row itself, which is where the skip/assumption ledger and
    /// the coverage accounting read it from.
    ///
    /// This projection exists once so that the transport lane, the terminal
    /// reconciliation counters, and the lossy fallback parser cannot drift into
    /// three different opinions about the same row.
    fn from(outcome: trust_types::Outcome) -> Self {
        match outcome {
            trust_types::Outcome::Proved => Self::Proved,
            trust_types::Outcome::Failed => Self::Failed,
            trust_types::Outcome::RuntimeChecked => Self::RuntimeChecked,
            trust_types::Outcome::Timeout => Self::Timeout,
            _ => Self::Unknown,
        }
    }
}

/// A single verification result parsed from compiler output.
///
/// Matches lines like:
///   note: Trust [overflow:add]: arithmetic overflow (Add) -- PROVED (ay-smtlib, 8ms)
///   note: Trust [overflow:add]: arithmetic overflow (Add) -- FAILED (ay-smtlib, 8ms)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct VerificationResult {
    pub(crate) function: String,
    pub(crate) kind: String,
    pub(crate) message: String,
    pub(crate) outcome: VerificationOutcome,
    pub(crate) backend: String,
    pub(crate) time_ms: Option<u64>,
    pub(crate) location: Option<SourceSpan>,
    pub(crate) counterexample: Option<Counterexample>,
    pub(crate) reason: Option<String>,
    pub(crate) raw_line: String,
}

const STRUCTURED_TRANSPORT_EVIDENCE_PREFIX: &str = "targo-trust-structured-transport-evidence:";

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct StructuredTransportEvidence {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) obligation_id: Option<String>,
    /// Compiler-generated digest of the complete canonical VC payload. This is
    /// an exact diagnostic identity, not proof authority by itself; Targo only
    /// consumes it while a private live-transport receipt still binds this
    /// exact row to an authenticated compiler session.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) claim_digest_sha256: Option<String>,
    /// Exact VC classification from the compiler transport. This preserves
    /// parameterized temporal/deep kinds that the legacy compact tag cannot
    /// reconstruct. It is diagnostic metadata, never proof authority.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) typed_kind: Option<Box<trust_types::VcKind>>,
    /// Compiler-provided design-mandate bit carried verbatim from the
    /// transport row (`TransportObligationResult::design_mandate`): the
    /// compiler saw a hardened-category VC with a tautology (`true`) violation
    /// formula — a design mandate, not a discharge target. targo must never
    /// infer this from row text; only this structured bit may exclude a row
    /// from the hardened proof-evidence denominator.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub(crate) design_mandate: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) native_trust_ir: Option<trust_types::TransportNativeTrustIrEvidence>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) proof_evidence: Option<trust_types::TransportProofEvidence>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) monitor: Option<trust_types::TransportMonitorEvidence>,
}

impl StructuredTransportEvidence {
    fn from_transport(r: &trust_types::TransportObligationResult) -> Option<Self> {
        let evidence = Self {
            obligation_id: r.obligation_id.clone(),
            claim_digest_sha256: r.claim_digest_sha256.clone(),
            typed_kind: r.typed_kind.clone(),
            design_mandate: r.design_mandate,
            native_trust_ir: r.native_trust_ir.clone(),
            proof_evidence: r.proof_evidence.clone(),
            monitor: r.monitor.clone(),
        };
        evidence.has_structured_fields().then_some(evidence)
    }

    fn has_structured_fields(&self) -> bool {
        self.obligation_id.is_some()
            || self.claim_digest_sha256.is_some()
            || self.typed_kind.is_some()
            || self.design_mandate
            || self.native_trust_ir.is_some()
            || self.proof_evidence.is_some()
            || self.monitor.is_some()
    }
}

pub(crate) fn structured_transport_evidence(
    result: &VerificationResult,
) -> Option<StructuredTransportEvidence> {
    let payload = result.raw_line.strip_prefix(STRUCTURED_TRANSPORT_EVIDENCE_PREFIX)?;
    serde_json::from_str(payload).ok()
}

/// Recover the exact typed VC kind only when it agrees with both adjacent
/// legacy fields. A present-but-inconsistent payload is a transport defect,
/// not an absent optional field.
pub(crate) fn exact_structured_transport_vc_kind(
    result: &VerificationResult,
) -> Result<Option<trust_types::VcKind>, ()> {
    let Some(typed_kind) =
        structured_transport_evidence(result).and_then(|evidence| evidence.typed_kind)
    else {
        return Ok(None);
    };
    let typed_kind = *typed_kind;
    if typed_kind.transport_tag() != result.kind || typed_kind.description() != result.message {
        return Err(());
    }
    Ok(Some(typed_kind))
}

/// Compact transport tags whose originating `VcKind` contains semantic fields
/// that the adjacent legacy tag/description pair cannot recover exactly.
/// These rows need the additive typed payload before they may carry proof or
/// runtime-check credit.
pub(crate) fn compact_vc_tag_requires_typed_kind(kind: &str) -> bool {
    matches!(
        kind,
        "unknown"
            | "overflow"
            | "overflow:add"
            | "overflow:sub"
            | "overflow:mul"
            | "arithmetic_overflow"
            | "arithmetic_overflow:add"
            | "arithmetic_overflow:sub"
            | "arithmetic_overflow:mul"
            | "arithmetic_overflow_add"
            | "arithmetic_overflow_sub"
            | "arithmetic_overflow_mul"
            | "shift"
            | "shift:left"
            | "shift:right"
            | "shift_overflow_shl"
            | "shift_overflow_shr"
            | "cast"
            | "cast_overflow"
            | "negation"
            | "negation_overflow"
            | "temporal"
            | "liveness"
            | "fairness"
            | "taint"
            | "taint_violation"
            | "refinement"
            | "refinement_violation"
            | "resilience"
            | "resilience_violation"
            | "protocol"
            | "protocol_violation"
            | "termination"
            | "non_termination"
            | "float_overflow_to_infinity"
            | "unbounded_allocation"
    )
}

fn structured_transport_vc_kind_defect(result: &VerificationResult) -> Option<&'static str> {
    match exact_structured_transport_vc_kind(result) {
        Err(()) => Some("with an inconsistent exact typed VC classification"),
        Ok(None) if compact_vc_tag_requires_typed_kind(&result.kind) => {
            Some("without the exact typed VC classification required by its lossy compact tag")
        }
        Ok(Some(trust_types::VcKind::UnsupportedMir { .. })) => {
            Some("for an unsupported MIR classification that cannot carry favorable authority")
        }
        Ok(None | Some(_)) => None,
    }
}

/// Whether this row has classification precise enough to participate in an
/// authority-sensitive alias equivalence. Merely self-consistent legacy loss
/// and exact `UnsupportedMir` are deliberately not authority-safe.
pub(crate) fn structured_transport_vc_kind_is_authority_safe(result: &VerificationResult) -> bool {
    structured_transport_vc_kind_defect(result).is_none()
}

pub(crate) fn replace_structured_transport_evidence(
    result: &mut VerificationResult,
    evidence: &StructuredTransportEvidence,
) -> Result<(), serde_json::Error> {
    let payload = serde_json::to_string(evidence)?;
    result.raw_line = format!("{STRUCTURED_TRANSPORT_EVIDENCE_PREFIX}{payload}");
    Ok(())
}

/// The obligation-id of a `#[trust::ensures]` postcondition row, if this result
/// carries one. A postcondition produces TWO obligations: the authoritative
/// BODY-AWARE VC (`vc:<fn>:postcondition:<n>`, whose formula pins the return slot
/// to its computed value — a closed query the backends prove) and a redundant
/// DEF-SITE contract MARKER (`obligation:<fn>:postcondition:<n>`, the bare
/// contract predicate with a havoc'd return slot, which the in-compiler pure
/// replay cannot discharge and so leaves `unknown`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PostconditionRowKind {
    BodyVc,
    DefinitionMarker,
}

/// Return the exact binding key shared by a body VC and its definition-site
/// marker. The key retains the complete function fragment and everything after
/// `:postcondition:`; in particular, two `#[ensures]` rows with different
/// indices/suffixes never alias merely because they belong to the same function.
fn postcondition_binding(result: &VerificationResult) -> Option<(PostconditionRowKind, String)> {
    if !structured_transport_vc_kind_is_authority_safe(result) {
        return None;
    }
    let postcondition_classification = match exact_structured_transport_vc_kind(result) {
        Ok(Some(trust_types::VcKind::Postcondition)) => true,
        Ok(Some(_)) | Err(()) => false,
        Ok(None) => {
            matches!(result.kind.as_str(), "postcond" | "postcondition")
                && result.message == "postcondition"
                || matches!(result.kind.as_str(), "assert" | "assertion")
                    && result.message == "assertion: postcondition"
        }
    };
    if !postcondition_classification {
        return None;
    }
    let oid = structured_transport_evidence(result)?.obligation_id?;
    let (kind, binding) = if let Some(binding) = oid.strip_prefix("vc:") {
        (PostconditionRowKind::BodyVc, binding)
    } else if let Some(binding) = oid.strip_prefix("obligation:") {
        (PostconditionRowKind::DefinitionMarker, binding)
    } else {
        return None;
    };
    let (function_fragment, suffix) = binding.rsplit_once(":postcondition:")?;
    if function_fragment.is_empty() || suffix.is_empty() {
        return None;
    }
    Some((kind, binding.to_string()))
}

/// Discharge a redundant def-site `#[trust::ensures]` MARKER by SUBSUMPTION onto
/// the function's body-aware postcondition VC(s).
///
/// A valid `#[ensures]` produces a proved body-aware VC PLUS a def-site marker
/// the pure-replay lane leaves `unknown`; that lone `unknown` keeps an otherwise
/// VERIFIED function at `Inconclusive`. When the one body-aware
/// `vc:<fn>:postcondition:<suffix>` paired with a marker is genuinely `Proved`,
/// the redundant `obligation:<fn>:postcondition:<suffix>` marker is flipped to
/// `Proved`.
///
/// SOUND + fail-closed, mirroring the compiler's own postcondition re-keying
/// (`full_verification_legacy_results`): binding uses the complete stable
/// obligation-id suffix, and requires exactly one VC plus exactly one marker for
/// that key. A missing, duplicated, failed, or inconclusive body-aware VC leaves
/// the marker `unknown` (so a genuinely-violated or unproven postcondition never
/// reads Verified). Only the def-site marker (`obligation:` prefix) is ever
/// flipped — a body-aware VC's own verdict is never altered.
pub(crate) fn subsume_redundant_postcondition_markers(results: &mut [VerificationResult]) {
    use std::collections::{HashMap, HashSet};

    #[derive(Default)]
    struct PostconditionBinding {
        body_vc_count: usize,
        marker_count: usize,
        body_vc_proved: bool,
    }

    // Count both sides of each exact binding. Include the display function in
    // the key as a second independent boundary: malformed transport cannot
    // correlate rows attributed to different functions even if their embedded
    // obligation-id fragments collide.
    let mut bindings: HashMap<(String, String), PostconditionBinding> = HashMap::new();
    for result in results.iter() {
        let Some((kind, binding)) = postcondition_binding(result) else {
            continue;
        };
        let entry = bindings.entry((result.function.clone(), binding)).or_default();
        match kind {
            PostconditionRowKind::BodyVc => {
                entry.body_vc_count += 1;
                entry.body_vc_proved = result.outcome.is_proved();
            }
            PostconditionRowKind::DefinitionMarker => entry.marker_count += 1,
        }
    }

    // Only an unambiguous one-to-one pair can establish a marker. Counting rows
    // instead of collapsing them in a set makes duplicate transport fail closed.
    let established: HashSet<(String, String)> = bindings
        .into_iter()
        .filter(|(_, binding)| {
            binding.body_vc_count == 1 && binding.marker_count == 1 && binding.body_vc_proved
        })
        .map(|(key, _)| key)
        .collect();
    if established.is_empty() {
        return;
    }

    for result in results.iter_mut() {
        if !matches!(result.outcome, VerificationOutcome::Unknown) {
            continue;
        }
        let Some((kind, binding)) = postcondition_binding(result) else {
            continue;
        };
        if kind != PostconditionRowKind::DefinitionMarker
            || !established.contains(&(result.function.clone(), binding))
        {
            continue;
        }
        result.outcome = VerificationOutcome::Proved;
        result.backend = if result.backend.trim().is_empty() {
            "subsumed:postcondition-vc".to_string()
        } else {
            format!("subsumed:{}", result.backend)
        };
        result.reason = Some(
            "discharged by SUBSUMPTION: the def-site #[ensures] contract marker is paired \
             one-to-one with its exact body-aware postcondition VC, which is genuinely proved"
                .to_string(),
        );
    }
}

fn structured_transport_evidence_raw_line(r: &trust_types::TransportObligationResult) -> String {
    let Some(evidence) = StructuredTransportEvidence::from_transport(r) else {
        return String::new();
    };
    serde_json::to_string(&evidence)
        .map(|payload| format!("{STRUCTURED_TRANSPORT_EVIDENCE_PREFIX}{payload}"))
        .unwrap_or_default()
}

/// Parse a Trust verification note from a compiler stderr line.
///
/// Expected format:
///   note: Trust [<kind>]: <message> -- <OUTCOME> (<backend>, <time>)
///   note: Trust [<kind>]: <message> — <OUTCOME> (<backend>, <time>)
///
/// Also handles the unicode em-dash variant.
pub(crate) fn parse_trust_note(line: &str) -> Option<VerificationResult> {
    let line = line.trim_start();

    // Find the "Trust [" marker after "note:"
    let trust_idx = line.find("Trust [")?;
    let after_trust = &line[trust_idx + 7..]; // skip "Trust ["

    // Extract kind: everything up to "]"
    let bracket_end = after_trust.find(']')?;
    let kind = after_trust[..bracket_end].to_string();

    // After "]: " comes the message, then " -- " or " — " separator
    let after_bracket = &after_trust[bracket_end + 1..];
    let after_colon = after_bracket.strip_prefix(": ")?;

    // Find outcome separator: " -- " (ASCII) or " — " (em-dash, encoded as \u{2014})
    let (message_part, outcome_part) = if let Some(sep_pos) = after_colon.find(" -- ") {
        (&after_colon[..sep_pos], &after_colon[sep_pos + 4..])
    } else if let Some(sep_pos) = after_colon.find(" \u{2014} ") {
        // em-dash is 3 bytes in UTF-8
        let em_dash_len = '\u{2014}'.len_utf8();
        (&after_colon[..sep_pos], &after_colon[sep_pos + 2 + em_dash_len..])
    } else {
        return None;
    };

    let message = message_part.trim().to_string();

    // Parse outcome: "PROVED (backend, time)" or "FAILED (backend, time)"
    let outcome = if outcome_part.starts_with("PROVED") {
        VerificationOutcome::Proved
    } else if outcome_part.starts_with("FAILED") {
        VerificationOutcome::Failed
    } else if outcome_part.starts_with("RUNTIME-CHECKED") {
        VerificationOutcome::RuntimeChecked
    } else if outcome_part.starts_with("TIMEOUT") {
        VerificationOutcome::Timeout
    } else {
        VerificationOutcome::Unknown
    };

    // Extract backend and time from parenthesized suffix
    let (backend, time_ms) = if let Some(paren_start) = outcome_part.find('(') {
        let paren_end = outcome_part.rfind(')').unwrap_or(outcome_part.len());
        let inner = &outcome_part[paren_start + 1..paren_end];
        let parts: Vec<&str> = inner.splitn(2, ',').collect();
        let backend = parts.first().unwrap_or(&"unknown").trim().to_string();
        let time = parts
            .get(1)
            .and_then(|t| t.trim().strip_suffix("ms").and_then(|n| n.trim().parse::<u64>().ok()));
        (backend, time)
    } else {
        ("unknown".to_string(), None)
    };

    Some(VerificationResult {
        function: "unknown".to_string(),
        kind,
        message,
        outcome,
        backend,
        time_ms,
        location: None,
        counterexample: None,
        reason: None,
        raw_line: line.to_string(),
    })
}

/// Convert a structured `TransportObligationResult` into a targo-trust
/// `VerificationResult`. This is used when structured JSON transport lines are
/// available, replacing the fragile text parsing of compiler diagnostics.
pub(crate) fn transport_to_verification_result(
    function: &str,
    r: &trust_types::TransportObligationResult,
) -> VerificationResult {
    let parsed_outcome = VerificationOutcome::from(r.outcome);
    let typed_kind_defect = match r.typed_kind.as_deref() {
        Some(kind) if kind.transport_tag() != r.kind || kind.description() != r.description => {
            Some("compiler transport typed VC kind disagrees with its compact tag or description")
        }
        Some(trust_types::VcKind::UnsupportedMir { .. }) => {
            Some("compiler transport classified the obligation as unsupported MIR")
        }
        None if compact_vc_tag_requires_typed_kind(&r.kind) => Some(
            "compiler transport omitted the exact typed VC kind required by its lossy compact tag",
        ),
        Some(_) | None => None,
    };
    let normalized = normalize_transport_outcome(r, parsed_outcome);
    // Missing, split-brain, or explicitly unsupported classification cannot
    // carry favorable authority. Preserve hard failures/timeouts, but
    // downgrade proof- or runtime-looking labels before the private live
    // receipt is minted so later report attachment has no favorable outcome to
    // restore.
    let outcome = if typed_kind_defect.is_some()
        && matches!(normalized, VerificationOutcome::Proved | VerificationOutcome::RuntimeChecked)
    {
        VerificationOutcome::Unknown
    } else {
        normalized
    };
    VerificationResult {
        function: function.to_string(),
        kind: r.kind.clone(),
        message: r.description.to_string(),
        outcome,
        backend: r.solver.clone(),
        time_ms: Some(r.time_ms),
        location: r.location.clone(),
        counterexample: r.counterexample_model.clone(),
        reason: if let Some(defect) = typed_kind_defect.filter(|_| {
            matches!(normalized, VerificationOutcome::Proved | VerificationOutcome::RuntimeChecked)
        }) {
            Some(format!("{defect}; favorable outcome downgraded before publication"))
        } else {
            normalized_transport_reason(r, outcome)
        },
        raw_line: structured_transport_evidence_raw_line(r),
    }
}

/// The direct (per-statement) MIR runtime-assert family a hardened
/// `PanicBoundary` `mir_assert` twin corresponds to. A hardened twin and the
/// per-statement safety VC at the SAME source span assert the SAME runtime
/// panic-check; if the direct sibling is genuinely proved, that one proof
/// discharges both. We only ever model the four `mir_assert` panic families the
/// language inserts a runtime check for and that vcgen emits a per-statement
/// sibling for.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum PanicTwinFamily {
    /// `mir_assert::Overflow(<op>)` / `OverflowNeg` <-> per-statement arithmetic
    /// overflow. The specific operation token (`add`/`sub`/`mul`/`neg`/..) is
    /// carried so a proved `Sub` sibling can NEVER subsume an unproven `Add` twin
    /// even when a macro expansion collapses both arithmetic asserts onto a
    /// byte-identical call-site span. Family alone is too coarse: it would let one
    /// proved op discharge a different unproven op at the same span (a false PROVE).
    ArithmeticOverflow(String),
    /// `mir_assert::Overflow(Shl)` / `Overflow(Shr)` <-> per-statement
    /// `ShiftOverflow { op }` shift-amount-in-range check. The shift op token
    /// (`shl`/`shr`) is carried so a proved `Shr` sibling can NEVER subsume an
    /// unproven `Shl` twin (and vice-versa) at a byte-identical span. This is a
    /// family DISTINCT from `ArithmeticOverflow`: a shift assert proves the shift
    /// amount is `< bit width`, NOT that an add/sub/mul result fits — the
    /// per-statement sibling kind is `shift:left`/`shift:right` (a.k.a.
    /// `shift_overflow_{shl,shr}`), never `overflow:*`/`arithmetic_overflow_*`. A
    /// shift twin therefore correlates ONLY with a `ShiftOverflow` sibling and an
    /// arithmetic twin ONLY with an `ArithmeticOverflow` sibling: no cross-family,
    /// no cross-op discharge.
    ShiftOverflow(String),
    /// `mir_assert::BoundsCheck` <-> per-statement index/slice bounds check.
    BoundsCheck,
    /// `mir_assert::DivisionByZero` <-> per-statement division-by-zero.
    DivisionByZero,
    /// `mir_assert::RemainderByZero` <-> per-statement remainder-by-zero.
    RemainderByZero,
}

/// Normalize an arithmetic-overflow operation token to a canonical lowercase
/// form so the twin marker (`Overflow(Sub)`) and the per-statement sibling kind
/// (`overflow:sub` / `arithmetic_overflow_sub`) key identically.
fn normalize_overflow_op(op: &str) -> String {
    op.trim().trim_matches(|c| c == '(' || c == ')').to_ascii_lowercase()
}

impl VerificationResult {
    /// Classify this result as a hardened `PanicBoundary` `mir_assert` TWIN and
    /// return which direct per-statement family it corresponds to.
    ///
    /// Only `mir_assert::*` panic twins are eligible — `unwrap`/`expect` panic
    /// boundaries (and every non-`PanicBoundary` hardened category) have NO
    /// arithmetic/bounds/div sibling and return `None`, so they are never
    /// subsumed. Matching is by the `hardened_panic_boundary` kind tag plus the
    /// `mir_assert::<Family>` marker the vcgen hardened lane writes into the
    /// obligation message (see trust-vcgen `hardened.rs`, `format!("mir_assert::{msg:?}")`).
    fn hardened_panic_twin_family(&self) -> Option<PanicTwinFamily> {
        // A typed row must name the exact PanicBoundary category.  Prefix
        // matching is not sufficient: `HardenedVcCategory::Unknown("panic_…")`
        // also serializes below the `hardened_panic*` namespace, but denotes a
        // different obligation and must never ride a panic twin's sibling
        // proof.  Fieldless legacy rows retain only the closed historical tag
        // set; arbitrary lookalike prefixes fail closed.
        let kind = self.kind.as_str();
        let is_panic_boundary = match exact_structured_transport_vc_kind(self) {
            Ok(Some(typed_kind)) => matches!(
                typed_kind.hardened_category(),
                Some(trust_types::HardenedVcCategory::PanicBoundary)
            ),
            Ok(None) => matches!(
                kind,
                "hardened_panic_boundary"
                    | "hardened::panic_boundary"
                    | "hardened:panic_boundary"
                    | "hardened_panic"
                    | "hardened::panic"
                    | "hardened:panic"
            ),
            Err(()) => false,
        };
        if !is_panic_boundary {
            return None;
        }
        // The mir_assert family lives in the obligation message. `unwrap`/`expect`
        // boundaries carry no `mir_assert::` marker and fall through to `None`.
        let msg = self.message.as_str();
        let marker = msg.find("mir_assert::")?;
        let after = &msg[marker + "mir_assert::".len()..];
        // Order matters only for substring disjointness, which holds here:
        // none of these four names is a substring of another.
        if let Some(rest) = after.strip_prefix("Overflow") {
            // Covers `Overflow(Add|Sub|Mul|Shl|Shr|..)` and `OverflowNeg`. Key on
            // the specific op so cross-op subsumption at a shared span is impossible.
            let op = if let Some(open) = rest.find('(') {
                let inner = &rest[open + 1..];
                let close = inner.find(')').unwrap_or(inner.len());
                normalize_overflow_op(&inner[..close])
            } else {
                // `OverflowNeg` (and any future suffix-form) -> the trailing token.
                normalize_overflow_op(rest)
            };
            // Shift overflow is a SEPARATE family from arithmetic overflow: a
            // `mir_assert::Overflow(Shl|Shr)` is the Rust `<<`/`>>` shift-amount-
            // out-of-range panic, whose per-statement sibling is a `ShiftOverflow`
            // VC (`shift:left`/`shift:right`), NOT an add/sub/mul overflow. Route
            // shl/shr into the Shift family so it can NEVER key against (and be
            // discharged by) an `ArithmeticOverflow` sibling, and vice-versa.
            if op == "shl" || op == "shr" {
                Some(PanicTwinFamily::ShiftOverflow(op))
            } else {
                Some(PanicTwinFamily::ArithmeticOverflow(op))
            }
        } else if after.starts_with("BoundsCheck") {
            Some(PanicTwinFamily::BoundsCheck)
        } else if after.starts_with("DivisionByZero") {
            Some(PanicTwinFamily::DivisionByZero)
        } else if after.starts_with("RemainderByZero") {
            Some(PanicTwinFamily::RemainderByZero)
        } else {
            None
        }
    }

    /// Classify this result as a DIRECT (per-statement) panic-check sibling and
    /// return its family. Outcome is deliberately not filtered here: the
    /// subsumption pass must count every candidate sibling before deciding that
    /// a same-span match is unambiguous, then separately require the sole sibling
    /// to be genuinely `Proved`.
    fn direct_panic_sibling_family(&self) -> Option<PanicTwinFamily> {
        // A hardened twin is never itself a direct sibling.
        if self.hardened_panic_twin_family().is_some() {
            return None;
        }
        let kind = self.kind.as_str();
        // Shift-overflow siblings FIRST: the per-statement shift VC surfaces as
        // `shift:left`/`shift:right` (and `shift_overflow_{shl,shr}` on the report
        // builder surface). It proves the shift amount is in range — the exact fact
        // the `mir_assert::Overflow(Shl|Shr)` twin asserts. This is a SEPARATE
        // family from arithmetic overflow and carries the op (`shl`/`shr`) so a
        // proved Shr sibling never discharges an Shl twin (or vice-versa), and a
        // shift sibling never discharges an arithmetic twin. None of these match
        // the `overflow:`/`arithmetic_overflow` arithmetic prefixes below.
        if kind == "shift:left" || kind == "shift_overflow_shl" {
            Some(PanicTwinFamily::ShiftOverflow("shl".to_string()))
        } else if kind == "shift:right" || kind == "shift_overflow_shr" {
            Some(PanicTwinFamily::ShiftOverflow("shr".to_string()))
        } else if let Some(op) = kind.strip_prefix("overflow:") {
            // Per-obligation arithmetic kind, e.g. `overflow:sub`.
            Some(PanicTwinFamily::ArithmeticOverflow(normalize_overflow_op(op)))
        } else if let Some(op) = kind.strip_prefix("arithmetic_overflow_") {
            // Aggregate arithmetic kind, e.g. `arithmetic_overflow_sub`.
            Some(PanicTwinFamily::ArithmeticOverflow(normalize_overflow_op(op)))
        } else if kind == "arithmetic_overflow" {
            // Op-less arithmetic kind: no op token available, so it cannot key
            // against an op-specific twin and is conservatively non-subsuming.
            None
        } else if kind == "slice"
            || kind == "slice_bounds_check"
            || kind == "index_out_of_bounds"
            || kind == "bounds"
        {
            Some(PanicTwinFamily::BoundsCheck)
        } else if matches!(kind, "divzero" | "div_by_zero" | "division_by_zero") {
            Some(PanicTwinFamily::DivisionByZero)
        } else if matches!(kind, "remzero" | "remainder_by_zero") {
            Some(PanicTwinFamily::RemainderByZero)
        } else {
            None
        }
    }
}

/// Discharge hardened `PanicBoundary` `mir_assert` twins by SUBSUMPTION.
///
/// A hardened twin `VerificationResult` whose outcome is `Unknown` is flipped to
/// `Proved` IF AND ONLY IF there is exactly ONE direct result and exactly ONE
/// hardened twin in the SAME function at the EXACT (byte-identical) SAME source
/// span and CORRESPONDING family, and the direct result is a genuine `Proved`.
/// The hardened `mir_assert` twin and the per-statement VC in that unambiguous
/// span+family pair are the SAME runtime panic-check, so the sibling's proof
/// discharges the twin.
///
/// SOUNDNESS — we subsume ONLY when ALL of:
///   * same function (`function` equal),
///   * byte-identical source span (`SourceSpan` derives `Eq`),
///   * corresponding family (Overflow(Add|Sub|Mul|..)<->ArithmeticOverflow,
///     Overflow(Shl|Shr)<->ShiftOverflow, BoundsCheck<->Index/Slice,
///     DivisionByZero<->DivisionByZero, RemainderByZero<->RemainderByZero) AND
///     SAME op — a Shr twin is discharged ONLY by a proved Shr ShiftOverflow
///     sibling, never by an Shl shift sibling and never by any arithmetic sibling,
///   * one-to-one cardinality (multiple direct siblings or multiple hardened
///     twins at the same key are ambiguous and NONE are subsumed),
///   * the sibling is a genuine `Proved` at/above the reported-proof floor (a
///     `RuntimeChecked`/`Unknown`/`Failed`/`Timeout` sibling does NOT subsume).
/// A twin with no such proved sibling (e.g. a loop-body Add twin whose
/// per-statement Add is itself only `RuntimeChecked`/`Unknown`) stays `Unknown`.
/// Only `mir_assert` `PanicBoundary` twins are eligible; `unwrap`/`expect` and
/// every other hardened category have no arithmetic sibling and are untouched.
///
/// The discharged twin is marked HONESTLY: its outcome becomes `Proved` but its
/// `backend` is rewritten to `subsumed:<sibling_backend>` and a `reason` is
/// attached, so the report never claims the twin was independently re-proved.
pub(crate) fn subsume_hardened_panic_twins(results: &mut [VerificationResult]) {
    use std::collections::HashMap;

    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    struct MatchKey {
        function: String,
        span: SourceSpan,
        family: PanicTwinFamily,
    }

    // Prefer the compiler's exact obligation identity when structured transport
    // carries one. Repeated renderings of that exact obligation remain one
    // logical candidate; without an ID every row is conservatively distinct.
    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    enum ResultIdentity {
        Obligation(String),
        UnidentifiedRow(usize),
    }

    fn result_identity(result: &VerificationResult, row: usize) -> ResultIdentity {
        structured_transport_evidence(result)
            .and_then(|evidence| evidence.obligation_id)
            .filter(|id| !id.trim().is_empty())
            .map(ResultIdentity::Obligation)
            .unwrap_or(ResultIdentity::UnidentifiedRow(row))
    }

    #[derive(Default)]
    struct MatchGroup {
        // Conflicting duplicate renderings of an exact direct obligation are
        // fail-closed, including conflicting solver provenance.
        direct: HashMap<ResultIdentity, DirectCandidate>,
        // Likewise, subsume duplicate renderings of an exact twin only if every
        // rendering is the expected Unknown target.
        twins: HashMap<ResultIdentity, bool>,
    }

    struct DirectCandidate {
        all_proved: bool,
        backend: Option<String>,
        backend_consistent: bool,
    }

    impl DirectCandidate {
        fn new(result: &VerificationResult) -> Self {
            let backend = (!result.backend.trim().is_empty()).then(|| result.backend.clone());
            Self { all_proved: result.outcome.is_proved(), backend, backend_consistent: true }
        }

        fn merge(&mut self, result: &VerificationResult) {
            self.all_proved &= result.outcome.is_proved();
            if result.backend.trim().is_empty() {
                return;
            }
            match self.backend.as_deref() {
                None => self.backend = Some(result.backend.clone()),
                Some(backend) if backend == result.backend => {}
                Some(_) => self.backend_consistent = false,
            }
        }
    }

    let mut groups: HashMap<MatchKey, MatchGroup> = HashMap::new();
    for (row, result) in results.iter().enumerate() {
        if !structured_transport_vc_kind_is_authority_safe(result) {
            continue;
        }
        let Some(span) = result.location.clone() else {
            continue;
        };
        let identity = result_identity(result, row);
        if let Some(family) = result.hardened_panic_twin_family() {
            let key = MatchKey { function: result.function.clone(), span, family };
            groups
                .entry(key)
                .or_default()
                .twins
                .entry(identity)
                .and_modify(|all_unknown| {
                    *all_unknown &= matches!(result.outcome, VerificationOutcome::Unknown);
                })
                .or_insert(matches!(result.outcome, VerificationOutcome::Unknown));
        } else if let Some(family) = result.direct_panic_sibling_family() {
            let key = MatchKey { function: result.function.clone(), span, family };
            groups
                .entry(key)
                .or_default()
                .direct
                .entry(identity)
                .and_modify(|candidate| candidate.merge(result))
                .or_insert_with(|| DirectCandidate::new(result));
        }
    }

    // Retain both the key and exact twin identity. This prevents a second,
    // unidentified twin at the same span from riding an otherwise eligible key.
    let eligible: HashMap<(MatchKey, ResultIdentity), String> = groups
        .into_iter()
        .filter_map(|(key, group)| {
            if group.direct.len() != 1 || group.twins.len() != 1 {
                return None;
            }
            let direct = group.direct.into_values().next()?;
            let (twin_identity, twin_unknown) = group.twins.into_iter().next()?;
            if !direct.all_proved || !direct.backend_consistent || !twin_unknown {
                return None;
            }
            let backend = direct.backend.unwrap_or_else(|| "per-statement-sibling".to_string());
            Some(((key, twin_identity), backend))
        })
        .collect();

    if eligible.is_empty() {
        return;
    }

    for (row, result) in results.iter_mut().enumerate() {
        if !matches!(result.outcome, VerificationOutcome::Unknown)
            || !structured_transport_vc_kind_is_authority_safe(result)
        {
            continue;
        }
        let Some(family) = result.hardened_panic_twin_family() else {
            continue;
        };
        let Some(span) = result.location.clone() else {
            continue;
        };
        let key = MatchKey { function: result.function.clone(), span, family };
        let identity = result_identity(result, row);
        if let Some(sibling_backend) = eligible.get(&(key, identity)) {
            result.outcome = VerificationOutcome::Proved;
            result.backend = format!("subsumed:{sibling_backend}");
            result.reason = Some(
                "discharged by SUBSUMPTION: the unique per-statement safety VC paired \
                 one-to-one at the identical source span and corresponding kind is \
                 genuinely proved; the hardened mir_assert twin asserts the same runtime \
                 panic-check (not independently re-proved)"
                    .to_string(),
            );
        }
    }
}

/// Normalize rows from an authenticated compiler channel for publication.
///
/// This transformation is deliberately monotone: it can only downgrade a
/// `Proved` row that lacks an exact compiler claim identity, or remove a
/// redundant diagnostic alias whose unique source obligation remains in the
/// vector unchanged.  It never creates a new proved row.  Keeping aliases out
/// of the obligation vector avoids the old Targo-side "subsumption" bug, where
/// an Unknown marker/twin was relabeled Proved without compiler proof authority
/// and then counted by the terminal gate even though the canonical report
/// correctly refused to publish it.
pub(crate) fn normalize_authenticated_results_for_publication(
    results: &mut Vec<VerificationResult>,
    materialization_root: Option<&std::path::Path>,
) {
    // `no_obligations` is function/coverage inventory, not a logical
    // obligation.  Keeping it as a synthetic Proved row inflated proof counts
    // and demanded proof evidence for a claim that does not exist.  Elide only
    // the compiler's exact structural shape; malformed lookalikes remain and
    // fail closed below.
    results.retain(|result| !is_exact_zero_obligation_inventory_row(result));

    for result in results.iter_mut() {
        if !matches!(
            result.outcome,
            VerificationOutcome::Proved | VerificationOutcome::RuntimeChecked
        ) {
            continue;
        }
        let defect = if let Some(defect) = structured_transport_vc_kind_defect(result) {
            Some(defect)
        } else if result.outcome.is_proved() && !has_exact_compiler_claim_identity(result) {
            Some("without an exact canonical claim digest")
        } else if result.outcome.is_proved()
            && !crate::report::authenticated_proved_row_has_publication_evidence(
                result,
                materialization_root,
            )
        {
            Some("without attachable native or clean-kernel proof evidence")
        } else {
            None
        };
        if let Some(defect) = defect {
            result.outcome = VerificationOutcome::Unknown;
            result.reason = Some(format!(
                "compiler transport claimed a favorable outcome {defect}; downgraded before publication"
            ));
        }
    }

    elide_rows_proved_only_by(results, subsume_hardened_panic_twins);
    elide_rows_proved_only_by(results, subsume_redundant_postcondition_markers);
}

pub(crate) fn authenticated_zero_obligation_inventory(
    results: &[VerificationResult],
) -> Vec<String> {
    let mut functions = results
        .iter()
        .filter(|result| is_exact_zero_obligation_inventory_row(result))
        .map(|result| result.function.clone())
        .filter(|function| !function.trim().is_empty())
        .collect::<Vec<_>>();
    functions.sort();
    functions.dedup();
    functions
}

fn is_exact_zero_obligation_inventory_row(result: &VerificationResult) -> bool {
    result.kind == "no_obligations"
        && result.message == "function has no panic obligations (trivially panic-free)"
        && result.outcome.is_proved()
        && result.backend == "trust-structural"
        && result.time_ms == Some(0)
        && result.location.is_none()
        && result.counterexample.is_none()
        && result.reason.as_deref() == Some("verified: zero panic obligations")
        && structured_transport_evidence(result).is_none()
}

fn has_exact_compiler_claim_identity(result: &VerificationResult) -> bool {
    structured_transport_evidence(result)
        .and_then(|evidence| evidence.claim_digest_sha256)
        .is_some_and(|digest| {
            digest.len() == 64
                && digest.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        })
}

/// Run an existing conservative alias-equivalence checker on a clone, then
/// remove only rows that checker changed from non-proof to Proved.  Every row
/// retained for publication is byte-for-byte the authenticated compiler row;
/// the Targo-derived Proved label is never retained.
fn elide_rows_proved_only_by(
    results: &mut Vec<VerificationResult>,
    derive: fn(&mut [VerificationResult]),
) {
    let mut derived = results.clone();
    derive(&mut derived);
    debug_assert_eq!(results.len(), derived.len());

    let mut index = 0usize;
    results.retain(|original| {
        let candidate = &derived[index];
        index += 1;
        original.outcome.is_proved()
            || !candidate.outcome.is_proved()
            || !structured_transport_vc_kind_is_authority_safe(original)
    });
}

fn normalize_transport_outcome(
    result: &trust_types::TransportObligationResult,
    parsed: VerificationOutcome,
) -> VerificationOutcome {
    if !is_full_verifier_solver(&result.solver) {
        return parsed;
    }

    if let Some(proof) = &result.proof_evidence {
        return match proof.status {
            trust_types::TransportProofStatus::Proved if parsed == VerificationOutcome::Proved => {
                VerificationOutcome::Proved
            }
            trust_types::TransportProofStatus::Proved => VerificationOutcome::Unknown,
            trust_types::TransportProofStatus::Failed => VerificationOutcome::Failed,
            trust_types::TransportProofStatus::Timeout => VerificationOutcome::Timeout,
            trust_types::TransportProofStatus::Unknown
            | trust_types::TransportProofStatus::Unsupported
            | trust_types::TransportProofStatus::Rejected => VerificationOutcome::Unknown,
            _ => VerificationOutcome::Unknown,
        };
    }

    match parsed {
        VerificationOutcome::RuntimeChecked => VerificationOutcome::Unknown,
        other => other,
    }
}

fn normalized_transport_reason(
    result: &trust_types::TransportObligationResult,
    outcome: VerificationOutcome,
) -> Option<String> {
    if outcome != VerificationOutcome::Unknown || !is_full_verifier_solver(&result.solver) {
        return result.reason.clone();
    }

    result.reason.clone().or_else(|| {
        result
            .proof_evidence
            .as_ref()
            .and_then(|proof| proof.diagnostics.first())
            .or_else(|| {
                result.native_trust_ir.as_ref().and_then(|native| native.diagnostics.first())
            })
            .map(|diagnostic| diagnostic.message.clone())
            .or_else(|| Some("native full verifier did not produce proof evidence".to_string()))
    })
}

#[cfg(test)]
mod subsumption_tests {
    use trust_types::{BinOp, HardenedVcCategory, SourceSpan, Ty, VcKind};

    use super::{
        STRUCTURED_TRANSPORT_EVIDENCE_PREFIX, StructuredTransportEvidence, VerificationOutcome,
        VerificationResult, authenticated_zero_obligation_inventory, elide_rows_proved_only_by,
        exact_structured_transport_vc_kind, normalize_authenticated_results_for_publication,
        structured_transport_evidence, structured_transport_vc_kind_is_authority_safe,
        subsume_hardened_panic_twins, subsume_redundant_postcondition_markers,
    };

    fn span(line: u32, c0: u32, c1: u32) -> SourceSpan {
        SourceSpan {
            file: "src/lib.rs".to_string(),
            line_start: line,
            col_start: c0,
            line_end: line,
            col_end: c1,
        }
    }

    fn result(
        function: &str,
        kind: &str,
        message: &str,
        outcome: VerificationOutcome,
        location: Option<SourceSpan>,
    ) -> VerificationResult {
        let result = VerificationResult {
            function: function.to_string(),
            kind: kind.to_string(),
            message: message.to_string(),
            outcome,
            backend: "interval".to_string(),
            time_ms: Some(0),
            location,
            counterexample: None,
            reason: None,
            raw_line: String::new(),
        };
        let u32_ty = Ty::u32();
        let typed_kind = match kind {
            "overflow:add" | "arithmetic_overflow_add" => Some(VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (u32_ty.clone(), u32_ty.clone()),
            }),
            "overflow:sub" | "arithmetic_overflow_sub" => Some(VcKind::ArithmeticOverflow {
                op: BinOp::Sub,
                operand_tys: (u32_ty.clone(), u32_ty.clone()),
            }),
            "overflow:mul" | "arithmetic_overflow_mul" => Some(VcKind::ArithmeticOverflow {
                op: BinOp::Mul,
                operand_tys: (u32_ty.clone(), u32_ty.clone()),
            }),
            "shift:left" | "shift_overflow_shl" => Some(VcKind::ShiftOverflow {
                op: BinOp::Shl,
                operand_ty: u32_ty.clone(),
                shift_ty: u32_ty.clone(),
            }),
            "shift:right" | "shift_overflow_shr" => Some(VcKind::ShiftOverflow {
                op: BinOp::Shr,
                operand_ty: u32_ty.clone(),
                shift_ty: u32_ty,
            }),
            _ => None,
        };
        match typed_kind {
            Some(typed_kind) if typed_kind.description() == result.message => {
                with_typed_kind(result, typed_kind)
            }
            _ => result,
        }
    }

    #[test]
    fn zero_obligation_inventory_is_elided_instead_of_counted_as_proof() {
        let mut results = vec![VerificationResult {
            function: "crate::empty".into(),
            kind: "no_obligations".into(),
            message: "function has no panic obligations (trivially panic-free)".into(),
            outcome: VerificationOutcome::Proved,
            backend: "trust-structural".into(),
            time_ms: Some(0),
            location: None,
            counterexample: None,
            reason: Some("verified: zero panic obligations".into()),
            raw_line: String::new(),
        }];

        assert_eq!(authenticated_zero_obligation_inventory(&results), ["crate::empty"]);
        normalize_authenticated_results_for_publication(&mut results, None);

        assert!(results.is_empty(), "inventory must not inflate logical proof totals");
    }

    #[test]
    fn malformed_zero_obligation_lookalike_fails_closed() {
        let mut results = vec![VerificationResult {
            function: "crate::empty".into(),
            kind: "no_obligations".into(),
            message: "different claim".into(),
            outcome: VerificationOutcome::Proved,
            backend: "trust-structural".into(),
            time_ms: Some(0),
            location: None,
            counterexample: None,
            reason: Some("verified: zero panic obligations".into()),
            raw_line: String::new(),
        }];

        normalize_authenticated_results_for_publication(&mut results, None);

        assert_eq!(results.len(), 1);
        assert_eq!(results[0].outcome, VerificationOutcome::Unknown);
    }

    fn overflow_twin(function: &str, family: &str, loc: SourceSpan) -> VerificationResult {
        let callee = format!("mir_assert::{family}");
        let detail =
            "MIR arithmetic assert can panic; hardened code needs proven arithmetic preconditions";
        with_typed_kind(
            result(
                function,
                "hardened_panic_boundary",
                &format!("hardened boundary (panic_boundary): {callee}: {detail}"),
                VerificationOutcome::Unknown,
                Some(loc),
            ),
            VcKind::HardenedBoundary {
                category: HardenedVcCategory::PanicBoundary,
                callee,
                detail: detail.to_string(),
            },
        )
    }

    fn with_typed_kind(mut result: VerificationResult, typed_kind: VcKind) -> VerificationResult {
        let evidence = StructuredTransportEvidence {
            obligation_id: None,
            claim_digest_sha256: None,
            typed_kind: Some(Box::new(typed_kind)),
            design_mandate: false,
            native_trust_ir: None,
            proof_evidence: None,
            monitor: None,
        };
        result.raw_line = format!(
            "{STRUCTURED_TRANSPORT_EVIDENCE_PREFIX}{}",
            serde_json::to_string(&evidence).unwrap()
        );
        result
    }

    fn with_obligation_id(result: VerificationResult, obligation_id: &str) -> VerificationResult {
        let typed_kind = structured_transport_evidence(&result)
            .and_then(|evidence| evidence.typed_kind)
            .map(|kind| *kind);
        with_obligation_id_and_typed_kind(result, obligation_id, typed_kind)
    }

    fn with_obligation_id_and_typed_kind(
        mut result: VerificationResult,
        obligation_id: &str,
        typed_kind: Option<VcKind>,
    ) -> VerificationResult {
        let evidence = StructuredTransportEvidence {
            obligation_id: Some(obligation_id.to_string()),
            claim_digest_sha256: None,
            typed_kind: typed_kind.map(Box::new),
            design_mandate: false,
            native_trust_ir: None,
            proof_evidence: None,
            monitor: None,
        };
        result.raw_line = format!(
            "{STRUCTURED_TRANSPORT_EVIDENCE_PREFIX}{}",
            serde_json::to_string(&evidence).unwrap()
        );
        result
    }

    // Build a postcondition row whose `raw_line` embeds the given obligation-id,
    // mirroring how the transport parser stamps structured evidence onto a
    // `VerificationResult` (`transport_to_verification_result`). The subsumption
    // pass recovers the `obligation:`/`vc:` prefix from exactly this encoding.
    fn postcondition_row(
        function: &str,
        obligation_id: &str,
        outcome: VerificationOutcome,
    ) -> VerificationResult {
        with_obligation_id(
            VerificationResult {
                function: function.to_string(),
                kind: "assertion".to_string(),
                message: "assertion: postcondition".to_string(),
                outcome,
                backend: "trust-full-verifier".to_string(),
                time_ms: Some(0),
                location: None,
                counterexample: None,
                reason: None,
                raw_line: String::new(),
            },
            obligation_id,
        )
    }

    #[test]
    fn ensures_marker_subsumed_when_body_vc_is_proved() {
        let mut results = vec![
            postcondition_row(
                "identity",
                "vc:identity:postcondition:0",
                VerificationOutcome::Proved,
            ),
            postcondition_row(
                "identity",
                "obligation:identity:postcondition:0",
                VerificationOutcome::Unknown,
            ),
        ];
        subsume_redundant_postcondition_markers(&mut results);
        assert!(
            matches!(results[1].outcome, VerificationOutcome::Proved),
            "a valid #[ensures]'s def-site marker must be subsumed to Proved by its proved body-aware VC"
        );
        assert!(results[1].backend.starts_with("subsumed:"));
        assert!(results[1].reason.as_deref().unwrap_or_default().contains("SUBSUMPTION"));
        // The body-aware VC's own verdict is never altered.
        assert!(matches!(results[0].outcome, VerificationOutcome::Proved));
    }

    #[test]
    fn split_brain_typed_postcondition_marker_stays_visible_and_unknown() {
        let body = postcondition_row(
            "identity",
            "vc:identity:postcondition:0",
            VerificationOutcome::Proved,
        );
        let malformed_marker = with_obligation_id_and_typed_kind(
            result(
                "identity",
                "assertion",
                "assertion: postcondition",
                VerificationOutcome::Unknown,
                None,
            ),
            "obligation:identity:postcondition:0",
            Some(VcKind::DivisionByZero),
        );
        assert!(exact_structured_transport_vc_kind(&malformed_marker).is_err());

        let mut derived = vec![body.clone(), malformed_marker.clone()];
        subsume_redundant_postcondition_markers(&mut derived);
        assert!(matches!(derived[1].outcome, VerificationOutcome::Unknown));

        // Even if a future alias derivation accidentally proposes Proved, the
        // generic elision boundary must retain a malformed typed source row.
        fn propose_second_row_as_proved(rows: &mut [VerificationResult]) {
            rows[1].outcome = VerificationOutcome::Proved;
        }
        let mut publication = vec![body, malformed_marker];
        elide_rows_proved_only_by(&mut publication, propose_second_row_as_proved);
        assert_eq!(publication.len(), 2);
        assert!(matches!(publication[1].outcome, VerificationOutcome::Unknown));

        let mut future_internal_rewrite = vec![publication[1].clone()];
        future_internal_rewrite[0].outcome = VerificationOutcome::Proved;
        normalize_authenticated_results_for_publication(&mut future_internal_rewrite, None);
        assert_eq!(future_internal_rewrite.len(), 1);
        assert!(matches!(future_internal_rewrite[0].outcome, VerificationOutcome::Unknown));
        assert!(
            future_internal_rewrite[0]
                .reason
                .as_deref()
                .is_some_and(|reason| reason.contains("inconsistent exact typed VC"))
        );
    }

    #[test]
    fn exact_wrong_kind_cannot_claim_a_postcondition_binding() {
        let body = postcondition_row(
            "identity",
            "vc:identity:postcondition:0",
            VerificationOutcome::Proved,
        );
        let wrong_marker = with_obligation_id_and_typed_kind(
            result("identity", "divzero", "division by zero", VerificationOutcome::Unknown, None),
            "obligation:identity:postcondition:0",
            Some(VcKind::DivisionByZero),
        );
        assert_eq!(
            exact_structured_transport_vc_kind(&wrong_marker),
            Ok(Some(VcKind::DivisionByZero))
        );

        let mut results = vec![body, wrong_marker];
        subsume_redundant_postcondition_markers(&mut results);
        assert!(matches!(results[1].outcome, VerificationOutcome::Unknown));
        elide_rows_proved_only_by(&mut results, subsume_redundant_postcondition_markers);
        assert_eq!(results.len(), 2);
        assert!(matches!(results[1].outcome, VerificationOutcome::Unknown));
    }

    #[test]
    fn ensures_marker_stays_unknown_when_a_body_vc_failed() {
        // The decisive soundness case (the `nondecreasing` reproduction): a
        // function with a FAILED body-aware postcondition VC must never have its
        // marker flipped — a genuinely-violated #[ensures] never reads Verified.
        let mut results = vec![
            postcondition_row("f", "vc:f:postcondition:0", VerificationOutcome::Failed),
            postcondition_row("f", "obligation:f:postcondition:0", VerificationOutcome::Unknown),
        ];
        subsume_redundant_postcondition_markers(&mut results);
        assert!(
            matches!(results[1].outcome, VerificationOutcome::Unknown),
            "the marker must stay Unknown when any body-aware postcondition VC failed"
        );
    }

    #[test]
    fn proved_postcondition_vc_subsumes_only_its_exact_index_marker() {
        // Two #[ensures] markers belong to the same function, but only #0 has a
        // body-aware proof. Function-level aggregation would incorrectly flip
        // both markers; exact suffix binding must leave #1 Unknown.
        let mut results = vec![
            postcondition_row("f", "vc:f:postcondition:0", VerificationOutcome::Proved),
            postcondition_row("f", "obligation:f:postcondition:0", VerificationOutcome::Unknown),
            postcondition_row("f", "obligation:f:postcondition:1", VerificationOutcome::Unknown),
        ];
        subsume_redundant_postcondition_markers(&mut results);
        assert!(matches!(results[1].outcome, VerificationOutcome::Proved));
        assert!(
            matches!(results[2].outcome, VerificationOutcome::Unknown),
            "a proof for postcondition #0 must never discharge marker #1"
        );
    }

    #[test]
    fn duplicate_postcondition_marker_is_ambiguous_and_not_subsumed() {
        let mut results = vec![
            postcondition_row("f", "vc:f:postcondition:0", VerificationOutcome::Proved),
            postcondition_row("f", "obligation:f:postcondition:0", VerificationOutcome::Unknown),
            postcondition_row("f", "obligation:f:postcondition:0", VerificationOutcome::Unknown),
        ];
        subsume_redundant_postcondition_markers(&mut results);
        assert!(
            results[1..]
                .iter()
                .all(|result| matches!(result.outcome, VerificationOutcome::Unknown))
        );
    }

    #[test]
    fn ensures_marker_stays_unknown_when_a_body_vc_is_inconclusive() {
        // An UNKNOWN (not failed) body-aware VC also blocks subsumption — the
        // postcondition is not fully established, so the marker stays honest.
        let mut results = vec![
            postcondition_row("g", "vc:g:postcondition:1", VerificationOutcome::Unknown),
            postcondition_row("g", "obligation:g:postcondition:0", VerificationOutcome::Unknown),
        ];
        subsume_redundant_postcondition_markers(&mut results);
        assert!(matches!(results[1].outcome, VerificationOutcome::Unknown));
    }

    #[test]
    fn ensures_marker_not_touched_without_any_body_vc() {
        // A marker with no body-aware postcondition VC at all is never flipped
        // (nothing established it) — it cannot be conjured Proved out of thin air.
        let mut results = vec![postcondition_row(
            "h",
            "obligation:h:postcondition:0",
            VerificationOutcome::Unknown,
        )];
        subsume_redundant_postcondition_markers(&mut results);
        assert!(matches!(results[0].outcome, VerificationOutcome::Unknown));
    }

    #[test]
    fn overflow_twin_is_subsumed_when_sibling_overflow_is_proved_at_same_span() {
        let s = span(7, 43, 50);
        let mut results = vec![
            result(
                "f",
                "overflow:sub",
                "arithmetic overflow (Sub)",
                VerificationOutcome::Proved,
                Some(s.clone()),
            ),
            overflow_twin("f", "Overflow(Sub)", s.clone()),
        ];
        subsume_hardened_panic_twins(&mut results);
        assert!(
            matches!(results[1].outcome, VerificationOutcome::Proved),
            "twin must be subsumed to Proved by its proved sibling at the identical span"
        );
        assert!(
            results[1].backend.starts_with("subsumed:"),
            "subsumed twin must carry an honest `subsumed:` provenance marker, got {:?}",
            results[1].backend
        );
        assert!(results[1].reason.as_deref().unwrap_or_default().contains("SUBSUMPTION"));
    }

    #[test]
    fn untyped_lossy_overflow_sibling_cannot_subsume_or_elide_a_hardened_twin() {
        let s = span(7, 43, 50);
        let mut untyped_direct = result(
            "f",
            "overflow:sub",
            "arithmetic overflow (Sub)",
            VerificationOutcome::Proved,
            Some(s.clone()),
        );
        untyped_direct.raw_line.clear();
        let twin = overflow_twin("f", "Overflow(Sub)", s);
        let mut results = vec![untyped_direct, twin];

        subsume_hardened_panic_twins(&mut results);
        assert!(matches!(results[1].outcome, VerificationOutcome::Unknown));
        elide_rows_proved_only_by(&mut results, subsume_hardened_panic_twins);
        assert_eq!(results.len(), 2);
        assert!(matches!(results[1].outcome, VerificationOutcome::Unknown));
    }

    #[test]
    fn split_brain_typed_hardened_twin_is_not_subsumed_or_elided() {
        let s = span(7, 43, 50);
        let direct = result(
            "f",
            "overflow:sub",
            "arithmetic overflow (Sub)",
            VerificationOutcome::Proved,
            Some(s.clone()),
        );
        let malformed_twin = with_obligation_id_and_typed_kind(
            overflow_twin("f", "Overflow(Sub)", s),
            "vc:f:panic_boundary:8",
            Some(VcKind::Postcondition),
        );
        assert!(exact_structured_transport_vc_kind(&malformed_twin).is_err());

        let mut results = vec![direct, malformed_twin];
        subsume_hardened_panic_twins(&mut results);
        assert_eq!(results.len(), 2);
        assert!(matches!(results[1].outcome, VerificationOutcome::Unknown));

        elide_rows_proved_only_by(&mut results, subsume_hardened_panic_twins);
        assert_eq!(results.len(), 2);
        assert!(matches!(results[1].outcome, VerificationOutcome::Unknown));
    }

    #[test]
    fn exact_unknown_hardened_category_cannot_claim_a_panic_twin_binding() {
        let s = span(7, 43, 50);
        let direct = result(
            "f",
            "overflow:add",
            "arithmetic overflow (Add)",
            VerificationOutcome::Proved,
            Some(s.clone()),
        );
        let wrong_kind = VcKind::HardenedBoundary {
            category: HardenedVcCategory::unknown_tag("panic_evil"),
            callee: "mir_assert::Overflow(Add)".to_string(),
            detail: "unrelated unknown hardened category".to_string(),
        };
        let wrong_twin = with_typed_kind(
            result(
                "f",
                &wrong_kind.transport_tag(),
                &wrong_kind.description(),
                VerificationOutcome::Unknown,
                Some(s),
            ),
            wrong_kind,
        );
        assert!(structured_transport_vc_kind_is_authority_safe(&wrong_twin));

        let mut results = vec![direct, wrong_twin];
        subsume_hardened_panic_twins(&mut results);
        assert!(matches!(results[1].outcome, VerificationOutcome::Unknown));
        elide_rows_proved_only_by(&mut results, subsume_hardened_panic_twins);
        assert_eq!(results.len(), 2, "a different hardened category must remain visible");
        assert!(matches!(results[1].outcome, VerificationOutcome::Unknown));
    }

    #[test]
    fn same_span_duplicate_direct_siblings_make_panic_twin_ambiguous() {
        // Macro expansion can collapse multiple operations onto one source
        // span. Even when both direct rows are Proved and have the same family,
        // no unique proof-to-twin pairing exists, so the twin must stay Unknown.
        let s = span(7, 43, 50);
        let mut results = vec![
            result(
                "f",
                "overflow:sub",
                "first arithmetic overflow (Sub)",
                VerificationOutcome::Proved,
                Some(s.clone()),
            ),
            result(
                "f",
                "overflow:sub",
                "second arithmetic overflow (Sub)",
                VerificationOutcome::Proved,
                Some(s.clone()),
            ),
            overflow_twin("f", "Overflow(Sub)", s),
        ];
        subsume_hardened_panic_twins(&mut results);
        assert!(
            matches!(results[2].outcome, VerificationOutcome::Unknown),
            "two same-span direct siblings are not an unambiguous one-to-one twin proof"
        );
    }

    #[test]
    fn repeated_rendering_of_one_exact_direct_obligation_is_not_double_counted() {
        // Structured transport can repeat a rendering while retaining one exact
        // obligation ID. Prefer that identity over row position: this is still
        // one direct obligation paired with one twin, not two distinct siblings.
        let s = span(7, 43, 50);
        let direct = with_obligation_id(
            result(
                "f",
                "overflow:sub",
                "arithmetic overflow (Sub)",
                VerificationOutcome::Proved,
                Some(s.clone()),
            ),
            "vc:f:arithmetic_safety:7",
        );
        let twin =
            with_obligation_id(overflow_twin("f", "Overflow(Sub)", s), "vc:f:panic_boundary:8");
        let mut results = vec![direct.clone(), direct, twin];
        subsume_hardened_panic_twins(&mut results);
        assert!(matches!(results[2].outcome, VerificationOutcome::Proved));
        assert_eq!(results[2].backend, "subsumed:interval");
    }

    #[test]
    fn same_span_duplicate_panic_twins_are_not_blanket_subsumed() {
        let s = span(7, 43, 50);
        let mut results = vec![
            result(
                "f",
                "overflow:sub",
                "arithmetic overflow (Sub)",
                VerificationOutcome::Proved,
                Some(s.clone()),
            ),
            overflow_twin("f", "Overflow(Sub)", s.clone()),
            overflow_twin("f", "Overflow(Sub)", s),
        ];
        subsume_hardened_panic_twins(&mut results);
        assert!(
            results[1..]
                .iter()
                .all(|result| matches!(result.outcome, VerificationOutcome::Unknown))
        );
    }

    #[test]
    fn overflow_add_twin_stays_unknown_when_sibling_is_runtime_checked() {
        // The decisive negative case: a loop-body Add whose per-statement sibling
        // is RuntimeChecked (not Proved) MUST NOT subsume the twin.
        let s = span(192, 12, 21);
        let mut results = vec![
            result(
                "f",
                "overflow:add",
                "arithmetic overflow (Add)",
                VerificationOutcome::RuntimeChecked,
                Some(s.clone()),
            ),
            overflow_twin("f", "Overflow(Add)", s.clone()),
        ];
        subsume_hardened_panic_twins(&mut results);
        assert!(
            matches!(results[1].outcome, VerificationOutcome::Unknown),
            "twin must stay Unknown when its sibling is only RuntimeChecked"
        );
    }

    #[test]
    fn twin_stays_unknown_when_sibling_is_unknown() {
        let s = span(110, 25, 34);
        let mut results = vec![
            result(
                "f",
                "overflow:add",
                "arithmetic overflow (Add)",
                VerificationOutcome::Unknown,
                Some(s.clone()),
            ),
            overflow_twin("f", "Overflow(Add)", s.clone()),
        ];
        subsume_hardened_panic_twins(&mut results);
        assert!(matches!(results[1].outcome, VerificationOutcome::Unknown));
    }

    #[test]
    fn twin_not_subsumed_across_a_different_span() {
        let mut results = vec![
            result(
                "f",
                "overflow:sub",
                "arithmetic overflow (Sub)",
                VerificationOutcome::Proved,
                Some(span(7, 43, 50)),
            ),
            // Twin at a DIFFERENT span (col differs) must not be subsumed.
            overflow_twin("f", "Overflow(Sub)", span(7, 43, 51)),
        ];
        subsume_hardened_panic_twins(&mut results);
        assert!(matches!(results[1].outcome, VerificationOutcome::Unknown));
    }

    #[test]
    fn add_twin_not_subsumed_by_proved_sub_sibling_at_byte_identical_span() {
        // Macro-collision soundness: an unproven `Add` twin and a PROVED `Sub`
        // sibling at the SAME byte-identical span (e.g. both arithmetic asserts
        // share one macro call-site span) must NOT cross-discharge. Family alone
        // would key them equal; op-specific keying keeps the Add twin Unknown.
        let s = span(200, 9, 18);
        let mut results = vec![
            result(
                "f",
                "overflow:sub",
                "arithmetic overflow (Sub)",
                VerificationOutcome::Proved,
                Some(s.clone()),
            ),
            overflow_twin("f", "Overflow(Add)", s.clone()),
        ];
        subsume_hardened_panic_twins(&mut results);
        assert!(
            matches!(results[1].outcome, VerificationOutcome::Unknown),
            "an Add overflow twin must NOT be subsumed by a proved Sub sibling at the same span"
        );
    }

    #[test]
    fn twin_not_subsumed_by_a_different_kind_sibling() {
        // A proved bounds sibling does NOT discharge an Overflow twin at the
        // same span (kind mismatch).
        let s = span(180, 21, 35);
        let mut results = vec![
            result(
                "f",
                "slice",
                "slice bounds check",
                VerificationOutcome::Proved,
                Some(s.clone()),
            ),
            overflow_twin("f", "Overflow(Sub)", s.clone()),
        ];
        subsume_hardened_panic_twins(&mut results);
        assert!(
            matches!(results[1].outcome, VerificationOutcome::Unknown),
            "an Overflow twin must not be subsumed by a proved bounds-check sibling"
        );
    }

    #[test]
    fn bounds_twin_is_subsumed_by_proved_slice_sibling() {
        let s = span(180, 21, 35);
        let mut results = vec![
            result(
                "f",
                "slice",
                "slice bounds check",
                VerificationOutcome::Proved,
                Some(s.clone()),
            ),
            result(
                "f",
                "hardened_panic_boundary",
                "hardened boundary (panic_boundary): mir_assert::BoundsCheck: MIR bounds-check \
                 assert can panic; hardened code needs a proven index precondition",
                VerificationOutcome::Unknown,
                Some(s.clone()),
            ),
        ];
        subsume_hardened_panic_twins(&mut results);
        assert!(matches!(results[1].outcome, VerificationOutcome::Proved));
    }

    #[test]
    fn division_and_remainder_twins_accept_current_compiler_tags() {
        for (kind, description, family) in [
            ("divzero", "division by zero", "DivisionByZero"),
            ("remzero", "remainder by zero", "RemainderByZero"),
        ] {
            let s = span(181, 21, 35);
            let mut results = vec![
                result("f", kind, description, VerificationOutcome::Proved, Some(s.clone())),
                overflow_twin("f", family, s),
            ];
            subsume_hardened_panic_twins(&mut results);
            assert!(
                matches!(results[1].outcome, VerificationOutcome::Proved),
                "current compiler tag {kind} must bind its exact hardened twin",
            );
        }
    }

    #[test]
    fn twin_not_subsumed_across_a_different_function() {
        let s = span(7, 43, 50);
        let mut results = vec![
            result(
                "g",
                "overflow:sub",
                "arithmetic overflow (Sub)",
                VerificationOutcome::Proved,
                Some(s.clone()),
            ),
            overflow_twin("f", "Overflow(Sub)", s.clone()),
        ];
        subsume_hardened_panic_twins(&mut results);
        assert!(matches!(results[1].outcome, VerificationOutcome::Unknown));
    }

    #[test]
    fn non_mir_assert_unwrap_panic_boundary_is_never_subsumed() {
        // An `unwrap` panic boundary has no arithmetic sibling. Even with a
        // proved overflow sibling at the same span, it stays Unknown.
        let s = span(173, 37, 73);
        let mut results = vec![
            result(
                "f",
                "overflow:sub",
                "arithmetic overflow (Sub)",
                VerificationOutcome::Proved,
                Some(s.clone()),
            ),
            result(
                "f",
                "hardened_panic_boundary",
                "hardened boundary (panic_boundary): std::result::Result::<T, E>::unwrap: \
                 unwrap is a denial-of-service path unless the success precondition is proven",
                VerificationOutcome::Unknown,
                Some(s.clone()),
            ),
        ];
        subsume_hardened_panic_twins(&mut results);
        assert!(
            matches!(results[1].outcome, VerificationOutcome::Unknown),
            "an unwrap panic boundary (no mir_assert marker) must never be subsumed"
        );
    }

    // --- Shift-overflow twin subsumption (mir_assert::Overflow(Shl|Shr)) ---

    #[test]
    fn shift_right_twin_is_subsumed_by_proved_shift_right_sibling_at_same_span() {
        // aterm-hash lib.rs:110/145 shape: a hardened `Overflow(Shr)` twin and a
        // genuinely-proved per-statement `shift:right` sibling at the byte-identical
        // span are the SAME `>>` shift-amount-in-range check; the proof discharges
        // the twin.
        let s = span(110, 25, 34);
        let mut results = vec![
            result(
                "f",
                "shift:right",
                "shift overflow (Shr)",
                VerificationOutcome::Proved,
                Some(s.clone()),
            ),
            overflow_twin("f", "Overflow(Shr)", s.clone()),
        ];
        subsume_hardened_panic_twins(&mut results);
        assert!(
            matches!(results[1].outcome, VerificationOutcome::Proved),
            "an Shr shift twin must be subsumed by its proved same-op shift sibling"
        );
        assert!(
            results[1].backend.starts_with("subsumed:"),
            "subsumed shift twin must carry an honest `subsumed:` marker, got {:?}",
            results[1].backend
        );
    }

    #[test]
    fn shift_left_twin_is_subsumed_by_proved_shift_left_sibling_at_same_span() {
        // aterm-hash lib.rs:182 shape: `Overflow(Shl)` twin + proved `shift:left`.
        let s = span(182, 18, 36);
        let mut results = vec![
            result(
                "f",
                "shift:left",
                "shift overflow (Shl)",
                VerificationOutcome::Proved,
                Some(s.clone()),
            ),
            overflow_twin("f", "Overflow(Shl)", s.clone()),
        ];
        subsume_hardened_panic_twins(&mut results);
        assert!(matches!(results[1].outcome, VerificationOutcome::Proved));
    }

    #[test]
    fn report_builder_shift_alias_cannot_subsume_without_exact_transport_identity() {
        // The report-builder surface stamps `shift_overflow_shr`, while the
        // compiler's authenticated transport tag is `shift:right`. A lossy
        // compatibility alias cannot participate in proof-bearing subsumption
        // without an exact typed payload that agrees with its adjacent tag.
        let s = span(145, 17, 29);
        let mut direct = result(
            "f",
            "shift_overflow_shr",
            "shift overflow (Shr)",
            VerificationOutcome::Proved,
            Some(s.clone()),
        );
        direct.raw_line.clear();
        let mut results = vec![direct, overflow_twin("f", "Overflow(Shr)", s.clone())];
        subsume_hardened_panic_twins(&mut results);
        assert!(matches!(results[1].outcome, VerificationOutcome::Unknown));
    }

    #[test]
    fn shift_twin_not_subsumed_by_arithmetic_sibling_at_same_span() {
        // SOUNDNESS (no cross-family): a proved arithmetic `overflow:sub` sibling
        // does NOT prove a `>>` shift amount is in range. A shift twin must stay
        // Unknown even when an arithmetic overflow sibling sits at the same span.
        let s = span(110, 25, 34);
        let mut results = vec![
            result(
                "f",
                "overflow:sub",
                "arithmetic overflow (Sub)",
                VerificationOutcome::Proved,
                Some(s.clone()),
            ),
            overflow_twin("f", "Overflow(Shr)", s.clone()),
        ];
        subsume_hardened_panic_twins(&mut results);
        assert!(
            matches!(results[1].outcome, VerificationOutcome::Unknown),
            "a shift twin must NOT be discharged by an arithmetic-overflow sibling"
        );
    }

    #[test]
    fn arithmetic_twin_not_subsumed_by_shift_sibling_at_same_span() {
        // SOUNDNESS (no cross-family, reverse direction): a proved `shift:right`
        // sibling must never discharge an arithmetic `Overflow(Sub)` twin.
        let s = span(110, 25, 34);
        let mut results = vec![
            result(
                "f",
                "shift:right",
                "shift overflow (Shr)",
                VerificationOutcome::Proved,
                Some(s.clone()),
            ),
            overflow_twin("f", "Overflow(Sub)", s.clone()),
        ];
        subsume_hardened_panic_twins(&mut results);
        assert!(
            matches!(results[1].outcome, VerificationOutcome::Unknown),
            "an arithmetic twin must NOT be discharged by a shift sibling"
        );
    }

    #[test]
    fn shl_twin_not_subsumed_by_proved_shr_sibling_at_byte_identical_span() {
        // SOUNDNESS (no cross-op): a proved `shift:right` (Shr) sibling must NOT
        // discharge an `Overflow(Shl)` twin even at a byte-identical span.
        let s = span(182, 18, 36);
        let mut results = vec![
            result(
                "f",
                "shift:right",
                "shift overflow (Shr)",
                VerificationOutcome::Proved,
                Some(s.clone()),
            ),
            overflow_twin("f", "Overflow(Shl)", s.clone()),
        ];
        subsume_hardened_panic_twins(&mut results);
        assert!(
            matches!(results[1].outcome, VerificationOutcome::Unknown),
            "an Shl shift twin must NOT be subsumed by a proved Shr sibling (cross-op)"
        );
    }

    #[test]
    fn shift_twin_stays_unknown_when_shift_sibling_is_unproved() {
        // An unproved (RuntimeChecked) shift sibling leaves the twin Unknown.
        let s = span(110, 25, 34);
        let mut results = vec![
            result(
                "f",
                "shift:right",
                "shift overflow (Shr)",
                VerificationOutcome::RuntimeChecked,
                Some(s.clone()),
            ),
            overflow_twin("f", "Overflow(Shr)", s.clone()),
        ];
        subsume_hardened_panic_twins(&mut results);
        assert!(
            matches!(results[1].outcome, VerificationOutcome::Unknown),
            "a shift twin must stay Unknown when its same-op sibling is only RuntimeChecked"
        );
    }

    #[test]
    fn shift_twin_not_subsumed_across_a_different_function() {
        let s = span(110, 25, 34);
        let mut results = vec![
            result(
                "g",
                "shift:right",
                "shift overflow (Shr)",
                VerificationOutcome::Proved,
                Some(s.clone()),
            ),
            overflow_twin("f", "Overflow(Shr)", s.clone()),
        ];
        subsume_hardened_panic_twins(&mut results);
        assert!(matches!(results[1].outcome, VerificationOutcome::Unknown));
    }
}

fn is_full_verifier_solver(solver: &str) -> bool {
    let solver = solver.trim();
    solver == "trust-full-verifier" || solver.contains("full-verifier")
}
