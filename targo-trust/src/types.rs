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
    // `targo trust init` is not a pipeline subcommand: `main.rs` dispatches it
    // straight to `run_init_subcommand`, which never builds a `Subcommand`.
    // An `Init` variant here was constructed only by a test (TRUST-35), so it
    // was removed rather than kept alive under `#[allow(dead_code)]`.
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
    pub(crate) original_vc_snapshot: Option<Box<trust_types::OriginalVcSnapshot>>,
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
    /// The compiler's own `Session::overflow_checks()` / `Session::ub_checks()`
    /// for the compilation unit that minted this row, carried verbatim from the
    /// unit's transport envelope (`FunctionTransportResult::runtime_checks`).
    ///
    /// It arrives on the ENVELOPE because it is a per-unit fact (see that
    /// field's own note), and it is bound HERE, per row, because every consumer
    /// decision is per row and because this is the payload the private live
    /// transport receipt covers: `live_transport_row_receipt` digests the whole
    /// serialized `VerificationResult`, `raw_line` included, so a row's check
    /// environment cannot be edited, donated from a neighbouring row, or
    /// reordered without invalidating that row's receipt. It is evidence, never
    /// proof authority — like `design_mandate`, only the compiler may set it and
    /// targo must never infer it from row text or from the flags targo appended.
    ///
    /// `None` means the producer did not state it. It is NOT "checks are off"
    /// and it is NOT "checks are on": it is the absence of a measurement, and a
    /// consumer must fall back to the most conservative value it can establish
    /// on its own.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) runtime_checks: Option<trust_types::RuntimeCheckEnv>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) native_trust_ir: Option<trust_types::TransportNativeTrustIrEvidence>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) proof_evidence: Option<trust_types::TransportProofEvidence>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) monitor: Option<trust_types::TransportMonitorEvidence>,
    /// Trust (TINV step 10.7): the transport row's `assumes` disclosure, carried
    /// verbatim so every report surface can copy it onto the row. Disclosure only,
    /// never proof authority (and bound into the row's live receipt like every field
    /// here).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) assumes: Vec<String>,
    /// Trust (T9): the row's stable key, package and function source digest,
    /// built from the compiler's envelope (`FunctionTransportResult::stable_ids`
    /// and `source_sha256`) by [`envelope_identities`]. Like `runtime_checks` it
    /// arrives on the envelope and is bound HERE, per row, inside the payload
    /// the live transport receipt covers. Identity, never authority: the
    /// verdict vector, the committed baseline and `targo trust diff` key on it,
    /// and nothing grants credit by it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) identity: Option<trust_types::obligation_identity::ObligationIdentity>,
    /// Trust (VF1): the transport row's three-axis grade (encoding, discharge,
    /// premises), carried verbatim for the `trust.obligations.v1` record.
    /// Disclosure only, never proof authority (and bound into the row's live
    /// receipt like every field here). `None` from a compiler that states none.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) grade: Option<trust_types::authority_grade::ObligationGrade>,
}

/// Trust (T9): each row's [`ObligationIdentity`] for one function envelope, in
/// `results` order — or none at all.
///
/// A key is `<function>#<stable id>` with the envelope's own (unscoped)
/// function path; the package is the envelope's Cargo package, or, outside
/// Cargo, its crate. The envelope's ids are minted for the whole row set at
/// once, so a defect anywhere — a count other than one id per row, a malformed
/// or repeated id, no package or crate — leaves EVERY row without a key, which
/// the determinism accounting reads as could-not-run: a partial key set would
/// compare a subset as if it were the whole.
///
/// [`ObligationIdentity`]: trust_types::obligation_identity::ObligationIdentity
pub(crate) fn envelope_identities(
    envelope: &trust_types::FunctionTransportResult,
) -> Vec<Option<trust_types::obligation_identity::ObligationIdentity>> {
    use trust_types::obligation_identity::{
        ObligationIdentity, is_function_source_digest, is_local_id, obligation_key,
    };
    let none = || vec![None; envelope.results.len()];
    let Some(package) = envelope
        .package_name
        .as_deref()
        .or(envelope.crate_name.as_deref())
        .filter(|package| !package.trim().is_empty())
    else {
        return none();
    };
    let ids = &envelope.stable_ids;
    let mut distinct: Vec<&str> = ids.iter().map(String::as_str).collect();
    distinct.sort_unstable();
    distinct.dedup();
    if ids.len() != envelope.results.len()
        || distinct.len() != ids.len()
        || !ids.iter().all(|id| is_local_id(id))
        || envelope.function.trim().is_empty()
    {
        return none();
    }
    let source = envelope.source_sha256.clone().filter(|digest| is_function_source_digest(digest));
    ids.iter()
        .map(|id| {
            Some(ObligationIdentity {
                key: obligation_key(&envelope.function, id),
                package: package.to_string(),
                function_source_sha256: source.clone(),
                expanded_function_identity: envelope.expanded_function_identity.clone(),
            })
        })
        .collect()
}

impl StructuredTransportEvidence {
    fn from_transport(
        r: &trust_types::TransportObligationResult,
        runtime_checks: Option<trust_types::RuntimeCheckEnv>,
        identity: Option<trust_types::obligation_identity::ObligationIdentity>,
    ) -> Option<Self> {
        let evidence = Self {
            obligation_id: r.obligation_id.clone(),
            claim_digest_sha256: r.claim_digest_sha256.clone(),
            original_vc_snapshot: r.original_vc_snapshot.clone(),
            typed_kind: r.typed_kind.clone(),
            design_mandate: r.design_mandate,
            runtime_checks,
            native_trust_ir: r.native_trust_ir.clone(),
            proof_evidence: r.proof_evidence.clone(),
            monitor: r.monitor.clone(),
            assumes: r.assumes.clone(),
            identity,
            grade: r.grade.clone(),
        };
        evidence.has_structured_fields().then_some(evidence)
    }

    /// Whether this evidence carries envelope facts and NOTHING else — the
    /// per-unit runtime-check environment and the row's stable identity (T9),
    /// neither of which speaks to a row's own claim: the identity is derived
    /// from the row's kind and source position, not from what it asserts. Used
    /// only to recognise the zero-obligation inventory row and the
    /// test-harness exclusion row, which the compiler emits with every claim
    /// field empty; see `is_exact_zero_obligation_inventory_row`.
    fn carries_only_envelope_facts(&self) -> bool {
        self.obligation_id.is_none()
            && self.claim_digest_sha256.is_none()
            && self.original_vc_snapshot.is_none()
            && self.typed_kind.is_none()
            && !self.design_mandate
            && self.native_trust_ir.is_none()
            && self.proof_evidence.is_none()
            && self.monitor.is_none()
            && self.assumes.is_empty()
            && self.grade.is_none()
    }

    fn has_structured_fields(&self) -> bool {
        self.identity.is_some()
            || self.obligation_id.is_some()
            || self.claim_digest_sha256.is_some()
            || self.original_vc_snapshot.is_some()
            || self.typed_kind.is_some()
            || self.design_mandate
            || self.runtime_checks.is_some()
            || self.native_trust_ir.is_some()
            || self.proof_evidence.is_some()
            || self.monitor.is_some()
            || !self.assumes.is_empty()
            || self.grade.is_some()
    }
}

pub(crate) fn structured_transport_evidence(
    result: &VerificationResult,
) -> Option<StructuredTransportEvidence> {
    let payload = result.raw_line.strip_prefix(STRUCTURED_TRANSPORT_EVIDENCE_PREFIX)?;
    serde_json::from_str(payload).ok()
}

/// The compiler-stated runtime-check environment of the compilation unit that
/// minted this row, or `None` when the row does not carry one.
///
/// `None` is the honest answer for an older compiler, a producer that does not
/// mint the field, a row that reached targo without structured evidence, and a
/// malformed payload alike. Callers must treat it as "no measurement", never as
/// a value: reading absence as `overflow_checks = true` would manufacture the
/// POSITIVE SAFETY CLAIM that `VcKind::has_runtime_fallback_in` exists to gate.
pub(crate) fn transport_runtime_check_env(
    result: &VerificationResult,
) -> Option<trust_types::RuntimeCheckEnv> {
    structured_transport_evidence(result).and_then(|evidence| evidence.runtime_checks)
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
    // TINV: both the transport spelling `type_invariant:<point>` and the report spelling
    // `type_invariant_<point>` drop `ty` and `site`, so the row must carry its typed kind.
    kind.starts_with("type_invariant")
        || matches!(
            kind,
            "unknown"
                | "overflow"
                | "overflow:add"
                | "overflow:sub"
                | "overflow:mul"
                | "overflow:div"
                | "overflow:rem"
                | "arithmetic_overflow"
                | "arithmetic_overflow:add"
                | "arithmetic_overflow:sub"
                | "arithmetic_overflow:mul"
                | "arithmetic_overflow:div"
                | "arithmetic_overflow:rem"
                | "arithmetic_overflow_add"
                | "arithmetic_overflow_sub"
                | "arithmetic_overflow_mul"
                | "arithmetic_overflow_div"
                | "arithmetic_overflow_rem"
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

fn structured_transport_evidence_raw_line(
    r: &trust_types::TransportObligationResult,
    runtime_checks: Option<trust_types::RuntimeCheckEnv>,
    identity: Option<trust_types::obligation_identity::ObligationIdentity>,
) -> String {
    let Some(evidence) = StructuredTransportEvidence::from_transport(r, runtime_checks, identity)
    else {
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
    } else {
        let sep_pos = after_colon.find(" \u{2014} ")?;
        // em-dash is 3 bytes in UTF-8
        let em_dash_len = '\u{2014}'.len_utf8();
        (&after_colon[..sep_pos], &after_colon[sep_pos + 2 + em_dash_len..])
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
    runtime_checks: Option<trust_types::RuntimeCheckEnv>,
    identity: Option<trust_types::obligation_identity::ObligationIdentity>,
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
            Some(publication_demotion_reason(
                r.outcome,
                r.reason.as_deref(),
                r.typed_kind.as_deref(),
                false,
                &format!("{defect}; favorable outcome downgraded before publication"),
            ))
        } else {
            normalized_transport_reason(r, outcome)
        },
        raw_line: structured_transport_evidence_raw_line(r, runtime_checks, identity),
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
    /// Why a `failed` row fails ([`trust_types::FailureBasis`]); `None` unless
    /// the outcome is `failed`. Read off the compiler-stamped solver label and
    /// the counterexample, exactly as the canonical report builder reads it, so
    /// the terminal and `report.json` cannot disagree. Display only: the
    /// outcome, the partition and the gate never consult it.
    pub(crate) fn failure_basis(&self) -> Option<trust_types::FailureBasis> {
        matches!(self.outcome, VerificationOutcome::Failed).then(|| {
            trust_types::FailureBasis::for_failed_row(&self.backend, self.counterexample.is_some())
        })
    }

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

/// The MIR-assert pairing role and family key of `result`, from the SAME
/// classifier and the same authority filter `subsume_hardened_panic_twins` keys
/// on. The report's failure-site accounting (`trust_types::failure_sites`) uses
/// this, so the two cannot drift about which rows are twins of which; there is
/// no second assert-family mapping. `None` for every other row.
pub(crate) fn panic_twin_pairing(
    result: &VerificationResult,
) -> Option<(trust_types::failure_sites::TwinRole, String)> {
    use trust_types::failure_sites::TwinRole;
    if !structured_transport_vc_kind_is_authority_safe(result) {
        return None;
    }
    if let Some(family) = result.hardened_panic_twin_family() {
        return Some((TwinRole::HardenedTwin, format!("{family:?}")));
    }
    result.direct_panic_sibling_family().map(|family| (TwinRole::L0Primary, format!("{family:?}")))
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
/// - same function (`function` equal),
/// - byte-identical source span (`SourceSpan` derives `Eq`),
/// - corresponding family (Overflow(Add|Sub|Mul|..)<->ArithmeticOverflow,
///   Overflow(Shl|Shr)<->ShiftOverflow, BoundsCheck<->Index/Slice,
///   DivisionByZero<->DivisionByZero, RemainderByZero<->RemainderByZero) AND
///   SAME op — a Shr twin is discharged ONLY by a proved Shr ShiftOverflow
///   sibling, never by an Shl shift sibling and never by any arithmetic sibling,
/// - one-to-one cardinality (multiple direct siblings or multiple hardened
///   twins at the same key are ambiguous and NONE are subsumed),
/// - the sibling is a genuine `Proved` at/above the reported-proof floor (a
///   `RuntimeChecked`/`Unknown`/`Failed`/`Timeout` sibling does NOT subsume).
///
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

/// Trust (#220 — publication-boundary disclosure): what the ONE publication
/// normalization did to the authenticated compiler vector, counted BY THE PASS
/// ITSELF.
///
/// The counts are taken inside the transformation rather than reconstructed
/// afterwards, because a favorable compiler row has TWO possible fates and only
/// one of them is reconstructible by a reader. Demotion rewrites the row to
/// `Unknown` and leaves it in place carrying the verbatim reason (`--json`
/// shows it; `grep` counts it). But demotion runs BEFORE
/// `elide_rows_proved_only_by`, which DELETES rows: a demoted hardened-panic
/// twin whose direct sibling at the same span did publish is removed from the
/// proof vector. Its diagnostic identity is retained separately below.
/// Counting the marker text in the proof vector alone would
/// therefore silently UNDER-report, which is worse than not reporting at all —
/// it reads as complete.
///
/// Conservation, held by construction and asserted in
/// `publication_boundary_conservation_holds_across_both_fates`:
/// `compiler_favorable == published_favorable + withheld_relabelled + withheld_elided`.
/// `published_favorable` counts only rows this pass did NOT demote: a policy-B
/// `RuntimeChecked` relabel (2026-09-16) is still a favorable outcome in the
/// published vector, but it is the compiler's PROOF claim withheld and a weaker
/// claim published, so it belongs to `withheld_relabelled` (and its
/// `withheld_relabelled_runtime_checked` sub-count), never to the published side.
///
/// Counts and diagnostics disclose the unchanged publication decisions. Typed
/// elided stops additionally preserve unit determinism accounting; they change
/// no row claim, demotion, elision, obligation count or proof authority.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct PublicationBoundary {
    /// Favorable (`Proved`/`RuntimeChecked`) rows in the authenticated compiler
    /// vector, EXCLUDING the exact zero-obligation inventory rows — those are
    /// function inventory rather than logical obligations and are disclosed
    /// separately as `zero_obligation_functions`.
    pub(crate) compiler_favorable: usize,
    /// Favorable rows that survived to publication.
    pub(crate) published_favorable: usize,
    /// Favorable compiler rows rewritten to `Unknown` — or, under policy B, to
    /// `RuntimeChecked` — and STILL PRESENT in the published vector, carrying
    /// the verbatim demotion reason. The compiler's PROOF claim was withheld
    /// either way; the policy-B fate publishes the weaker, entailed claim.
    pub(crate) withheld_relabelled: usize,
    /// The policy-B subset of `withheld_relabelled`: rows rewritten to
    /// `RuntimeChecked` rather than `Unknown` because their exact typed kind
    /// keeps a runtime fallback rustc emits at every setting
    /// (`transport_row_keeps_an_unconditional_runtime_check`). The gate counts
    /// them CONDITIONAL, never proved.
    pub(crate) withheld_relabelled_runtime_checked: usize,
    /// Favorable compiler rows that were demoted and then removed by the
    /// alias-elision passes. Their identities survive in diagnostic disclosure,
    /// not in the canonical proof vector.
    pub(crate) withheld_elided: usize,
    /// Rows the compiler did NOT report favorably that were elided as redundant
    /// aliases. Pre-existing intended behaviour, disclosed for completeness.
    pub(crate) alias_elided: usize,
    /// Exact zero-obligation inventory rows removed (already disclosed through
    /// `zero_obligation_functions`).
    pub(crate) inventory_elided: usize,
    /// Trust (CB4): exact test-harness exclusion rows removed (already disclosed
    /// through `test_harness_exclusions` and the gate's `exclusions`). Like the
    /// zero-obligation rows they are inventory, not obligations.
    pub(crate) harness_exclusions_elided: usize,
    /// Diagnostic identities retained before alias elision. These are not
    /// additional obligations, discharged goals, or proof authority.
    pub(crate) elided_diagnostics: Vec<ElidedPublicationDiagnostic>,
    /// Stops removed from the row vector by alias elision. These remain unit
    /// accounting, never additional obligations or proof authority.
    pub(crate) elided_stops: Vec<PublicationStop>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PublicationStop {
    /// Exact transported package identity; absent means no package can safely
    /// exclude this stop from its accounting.
    pub(crate) package: Option<String>,
    pub(crate) stop: trust_types::determinism::NotedStop,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ElidedPublicationDiagnostic {
    pub(crate) function: String,
    pub(crate) kind: String,
    pub(crate) message: String,
    pub(crate) outcome: VerificationOutcome,
    pub(crate) source_location: Option<String>,
    pub(crate) reason: Option<String>,
    pub(crate) obligation_id: Option<String>,
    pub(crate) claim_digest_sha256: Option<String>,
    pub(crate) native_request_id: Option<String>,
    pub(crate) native_id: Option<String>,
    pub(crate) native_suite: Option<String>,
    pub(crate) backend: String,
    pub(crate) withheld: bool,
}

impl ElidedPublicationDiagnostic {
    fn from_result(result: &VerificationResult, withheld: bool) -> Self {
        let evidence = structured_transport_evidence(result);
        let native = evidence.as_ref().and_then(|evidence| evidence.native_trust_ir.as_ref());
        let proof = evidence.as_ref().and_then(|evidence| evidence.proof_evidence.as_ref());
        Self {
            function: result.function.clone(),
            kind: result.kind.clone(),
            message: result.message.clone(),
            outcome: result.outcome,
            source_location: result
                .location
                .as_ref()
                .map(|span| format!("{}:{}:{}", span.file, span.line_start, span.col_start)),
            reason: result.reason.clone(),
            obligation_id: evidence.as_ref().and_then(|evidence| evidence.obligation_id.clone()),
            claim_digest_sha256: evidence
                .as_ref()
                .and_then(|evidence| evidence.claim_digest_sha256.clone()),
            native_request_id: native
                .and_then(|native| native.request_id.clone())
                .or_else(|| proof.and_then(|proof| proof.request_id.clone())),
            native_id: native
                .and_then(|native| native.native_id.clone())
                .or_else(|| proof.and_then(|proof| proof.native_id.clone())),
            native_suite: native
                .map(|native| native.suite.clone())
                .or_else(|| proof.map(|proof| proof.suite.clone())),
            backend: result.backend.clone(),
            withheld,
        }
    }
}

impl PublicationBoundary {
    /// Favorable compiler rows that did not reach publication, computed as a
    /// DIFFERENCE of two independently counted populations rather than as a sum
    /// of the attributed parts. A bookkeeping slip in the split can then show
    /// up as unattributed residue instead of quietly shrinking the total.
    pub(crate) fn withheld(&self) -> usize {
        self.compiler_favorable.saturating_sub(self.published_favorable)
    }

    /// Withheld rows the split failed to account for. Zero whenever the
    /// conservation law above holds; rendered explicitly when it does not, so a
    /// future edit that breaks the accounting is visible instead of silent.
    pub(crate) fn unattributed_withheld(&self) -> usize {
        self.withheld().saturating_sub(self.withheld_relabelled + self.withheld_elided)
    }
}

/// Preserve the producer's typed stop while adding a structural refusal.
/// No validator verdict is proof authority here. In particular, a failed
/// path-backed check conflates structural defects with IO/races, so it cannot
/// acquire a deterministic attribution from an earlier favorable label.
fn publication_demotion_reason(
    outcome: trust_types::Outcome,
    prior_reason: Option<&str>,
    typed_kind: Option<&trust_types::VcKind>,
    may_have_failed_io: bool,
    refusal: &str,
) -> String {
    use trust_types::determinism::StopCause;
    let unsupported_detail = match typed_kind {
        Some(trust_types::VcKind::UnsupportedMir { detail, .. }) => Some(detail.as_str()),
        _ => None,
    };
    let typed_outcome =
        if unsupported_detail.is_some() { trust_types::Outcome::Unsupported } else { outcome };
    let mut cause = StopCause::of_outcome(typed_outcome, prior_reason);
    // An explicitly unsupported source kind remains unsupported even if a
    // malformed favorable carrier also says `solved`.
    if unsupported_detail.is_some() && cause == StopCause::Solved {
        cause = StopCause::Unsupported;
    }
    if let Some(detail_cause) = unsupported_detail.and_then(StopCause::from_reason) {
        cause = StopCause::combine(cause, detail_cause);
    }
    if may_have_failed_io {
        cause = StopCause::combine(cause, StopCause::Unclassified);
    }
    let mut detail = format!(
        "{refusal}; prior compiler outcome `{outcome:?}`: ({})",
        prior_reason.unwrap_or("no reason supplied")
    );
    if let Some(typed_detail) = unsupported_detail {
        detail.push_str("; original typed-kind detail: (");
        detail.push_str(typed_detail);
        detail.push(')');
    }
    cause.stamp(&detail)
}

/// Missing proof envelopes and inline structural refusals do not open files.
/// Any path in a supplied proof/native envelope is conservatively enough to
/// withhold a deterministic attribution; the Boolean validators do not expose
/// whether their refusal came from structure or IO.
fn publication_evidence_may_have_failed_io(result: &VerificationResult) -> bool {
    let Some(evidence) = structured_transport_evidence(result) else { return false };
    let Some(proof) = evidence.proof_evidence.as_ref() else { return false };
    proof
        .artifacts
        .iter()
        .chain(evidence.native_trust_ir.iter().flat_map(|native| &native.artifacts))
        .any(|artifact| {
            artifact
                .materialization
                .as_ref()
                .is_some_and(|materialization| materialization.materialized_path.is_some())
        })
}

fn is_favorable_publication_row(result: &VerificationResult) -> bool {
    matches!(result.outcome, VerificationOutcome::Proved | VerificationOutcome::RuntimeChecked)
}

/// The one publication defect policy B may soften (see
/// `normalize_authenticated_results_for_publication`): the row is exact and
/// typed but carries no attachable proof evidence.
const PUBLICATION_EVIDENCE_DEFECT: &str =
    "without attachable native or clean-kernel proof evidence";

/// Whether a row's EXACT typed kind keeps a runtime fallback under the
/// fail-closed check environment (`overflow_checks = false`, `ub_checks =
/// false`) — a fallback rustc emits at EVERY setting: `Assertion` (a panic; the
/// lane-tagged UB families — every `[unsafe…]` assertion and `[provenance]` —
/// answer `false` inside the predicate itself), bounds and slice checks,
/// division and remainder by zero. Targo does not know the
/// unit's real check environment, so the `overflow_checks`-gated kinds answer
/// `false` here and stay `Unknown`; the compiler, which does know it, labels
/// those itself (`build_transport_results_with_runtime_checks_bound`).
///
/// The typed kind must agree with the adjacent legacy tag/description
/// (`exact_structured_transport_vc_kind`); a mismatch is a transport defect and
/// answers `false`, as does an untyped row. `UnsupportedMir` answers `false`
/// outright, on the rule of [`transport_row_can_carry_runtime_check`]: the
/// compiler could not lower it, so no fallback can be vouched for — even where
/// the predicate would recover a fallback-bearing tag from its text.
///
/// Two more refusals, both from the 2026-09-16 refutation of this relabel:
///
/// * the row must be EVIDENCE-FREE — policy B softens the "no attachable
///   evidence" defect only. A `proved` row that DOES carry evidence which fails
///   publication (a `failed`/`unsupported` status behind a `proved` label, a
///   torn artifact) is a laundering attempt, not a gap; the parse-time
///   `normalize_transport_outcome` re-derives that only for full-verifier
///   solver names, so it is refused here for every solver;
/// * a hardened-category `Assertion` (`hardened_category()` is `Some` for the
///   whole `[unsafe…]` family — UB and FFI claims rustc never checks) answers
///   `false` even though `has_runtime_fallback_in` now says the same: the
///   boundary keeps its own belt.
fn transport_row_keeps_an_unconditional_runtime_check(result: &VerificationResult) -> bool {
    let Some(structured) = structured_transport_evidence(result) else {
        return false;
    };
    if structured.proof_evidence.is_some() || structured.native_trust_ir.is_some() {
        return false;
    }
    let Ok(Some(kind)) = exact_structured_transport_vc_kind(result) else {
        return false;
    };
    if matches!(kind, trust_types::VcKind::UnsupportedMir { .. })
        || kind.hardened_category().is_some()
    {
        return false;
    }
    kind.has_runtime_fallback_in(trust_types::RuntimeCheckEnv::overflow_checks_only(false))
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
///
/// Trust (#220): returns the `PublicationBoundary` describing what it withheld,
/// so the human report can disclose a boundary that used to be visible only in
/// `--json` (and, for elided rows, not at all). The returned value is
/// observational for proof decisions. Its typed elided stops must also reach
/// the unit ledger, so an alias removal cannot hide stopped work.
///
/// Trust (2026-09-16, policy B at the publication boundary — blocker T4 of
/// `reports/2026-09-13-w1-alignment-obligation-sizing.md`): a `Proved` row that
/// fails ONLY the evidence criterion — exact claim identity present, typed kind
/// authority-safe, but no attachable native or clean-kernel proof evidence — is
/// rewritten to `RuntimeChecked` instead of `Unknown` WHEN its exact typed kind
/// keeps a runtime fallback under the fail-closed check environment
/// (`transport_row_keeps_an_unconditional_runtime_check`). The premise is the
/// compiler's `Proved` label on a real typed obligation whose failure mode is a
/// Rust panic (a panic-class `Assertion` — never a lane-tagged UB claim —,
/// bounds/slice checks, div/rem by zero): the compiler
/// asserted no runtime failure at all, so the strictly weaker claim "rustc's
/// runtime check for this obligation stays in the binary" is entailed by it,
/// and the gate counts the row CONDITIONAL (`conditional-pass`), never proved.
/// Measured case (`trust-acb74dd5`, `p7_helper_print`): a whole-function
/// panic-freedom row discharged by the compiler's `InterproceduralCalleeClosure`
/// (`trust-assert-refute`, TCB class `Trusted`, premises not attachable) —
/// `targo trust build` graded the crate INCONCLUSIVE on a body raw `trustc` had
/// proved, exit 1, no binary. This is NOT the `RuntimeCheckPolicy::Auto`
/// re-inference `report.rs` forbids: that laundered solver `Unknown`s (nothing
/// established) into "covered"; here the label starts from a compiler proof
/// claim and only moves DOWN. A row failing the identity or kind criterion, or
/// whose kind's fallback is conditional (`overflow_checks`-gated) or absent,
/// still fails closed to `Unknown`; the relabel is still counted as a withheld
/// proof claim in the boundary disclosure.
pub(crate) fn normalize_authenticated_results_for_publication(
    results: &mut Vec<VerificationResult>,
    materialization_root: Option<&std::path::Path>,
) -> PublicationBoundary {
    // `no_obligations` is function/coverage inventory, not a logical
    // obligation.  Keeping it as a synthetic Proved row inflated proof counts
    // and demanded proof evidence for a claim that does not exist.  Elide only
    // the compiler's exact structural shape; malformed lookalikes remain and
    // fail closed below.
    let before_inventory = results.len();
    results.retain(|result| !is_exact_zero_obligation_inventory_row(result));
    let inventory_elided = before_inventory - results.len();
    // Trust (CB4): an excluded libtest harness body is inventory in exactly the
    // same sense — it names a function, it claims nothing — so its EXACT row
    // is elided too and disclosed through `authenticated_test_harness_exclusions`.
    // A lookalike is not elided: it stays and fails closed in the partition.
    let before_exclusions = results.len();
    results.retain(|result| test_harness_exclusion_of(result).is_none());

    let mut boundary = PublicationBoundary {
        inventory_elided,
        harness_exclusions_elided: before_exclusions - results.len(),
        compiler_favorable: results.iter().filter(|r| is_favorable_publication_row(r)).count(),
        ..PublicationBoundary::default()
    };

    // Parallel to `results`: which rows THIS pass demoted. Carried through the
    // elision passes so a deleted row's original fate is still attributable.
    let mut demoted = vec![false; results.len()];

    for (index, result) in results.iter_mut().enumerate() {
        if !matches!(
            result.outcome,
            VerificationOutcome::Proved | VerificationOutcome::RuntimeChecked
        ) {
            continue;
        }
        // Trust (OD-1 phase 1): the compiler's exact instance-discharge row claims no
        // proof of its own — it reports the resolved callee's verdict, and the gate's
        // partition counts a `proved` one as conditional evidence (`assumed`), never as
        // proof. It carries no claim digest by construction, so the proof-claim checks
        // below do not apply to it.
        if trust_types::assumption::is_instance_hypothesis_discharge_row(
            &result.kind,
            &result.backend,
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
            Some(PUBLICATION_EVIDENCE_DEFECT)
        } else {
            None
        };
        if let Some(defect) = defect {
            let policy_b_runtime_checked = result.outcome.is_proved()
                && defect == PUBLICATION_EVIDENCE_DEFECT
                && transport_row_keeps_an_unconditional_runtime_check(result);
            let original_outcome = crate::determinism_report::row_status(result);
            let prior_reason = result.reason.clone();
            let typed_kind = structured_transport_evidence(result).and_then(|e| e.typed_kind);
            let may_have_failed_io = defect == PUBLICATION_EVIDENCE_DEFECT
                && publication_evidence_may_have_failed_io(result);
            if policy_b_runtime_checked {
                result.outcome = VerificationOutcome::RuntimeChecked;
                result.reason = Some(format!(
                    "compiler transport claimed a favorable outcome {defect}; published as \
                     runtime-checked under policy B (the compiler's `{}` claim is not \
                     publication-grade proof; rustc's runtime check for this obligation stays \
                     in the binary and the gate counts it conditional, never proved); \
                     downgraded before publication",
                    result.backend
                ));
            } else {
                result.outcome = VerificationOutcome::Unknown;
                result.reason = Some(format!(
                    "compiler transport claimed a favorable outcome {defect}; downgraded before publication"
                ));
            }
            result.reason = Some(publication_demotion_reason(
                original_outcome,
                prior_reason.as_deref(),
                typed_kind.as_deref(),
                may_have_failed_io,
                result.reason.as_deref().expect("demotion supplies a reason"),
            ));
            demoted[index] = true;
        }
    }

    let panic_twins =
        elide_rows_proved_only_by(results, &mut demoted, subsume_hardened_panic_twins);
    // An authored postcondition is its own source claim. A matching body-VC
    // ID suffix is not evidence that it is a redundant diagnostic alias.
    // Keep every withheld source row visible until its own proof can publish.
    boundary.withheld_elided = panic_twins.demoted;
    boundary.alias_elided = panic_twins.other;
    boundary.elided_stops = panic_twins.stops;
    boundary.elided_diagnostics = panic_twins.diagnostics;
    // A demoted row that survived elision is still visible (as `Unknown`, with
    // the reason); one that did not is gone. Only the first is reconstructible
    // from the published vector, which is exactly why both are counted here.
    boundary.withheld_relabelled = demoted.iter().filter(|was_demoted| **was_demoted).count();
    boundary.withheld_relabelled_runtime_checked = results
        .iter()
        .zip(demoted.iter())
        .filter(|(result, was_demoted)| {
            **was_demoted && result.outcome == VerificationOutcome::RuntimeChecked
        })
        .count();
    // A demoted row is never "published favorable", even when policy B left a
    // favorable `RuntimeChecked` outcome in the vector: the compiler's proof
    // claim was withheld. Conservation needs the two sides disjoint.
    boundary.published_favorable = results
        .iter()
        .zip(demoted.iter())
        .filter(|(result, was_demoted)| !**was_demoted && is_favorable_publication_row(result))
        .count();
    boundary
}

/// How many rows one `elide_rows_proved_only_by` pass removed, split by whether
/// this run's publication demotion had already rewritten them.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct ElidedRowCounts {
    /// Removed rows that THIS run demoted from a favorable compiler outcome.
    demoted: usize,
    /// Removed rows the compiler had not reported favorably — ordinary
    /// redundant aliases.
    other: usize,
    diagnostics: Vec<ElidedPublicationDiagnostic>,
    stops: Vec<PublicationStop>,
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

/// Trust (CB4): the authenticated inventory of bodies the compiler EXCLUDED
/// from the proof inventory because rustc's libtest harness synthesized them
/// (`trust_types::exclusion`), one entry per exact exclusion row, sorted by
/// function and deduplicated.
///
/// Like [`authenticated_zero_obligation_inventory`], this is function/coverage
/// inventory, never a logical obligation: the rows it reads are elided from the
/// publication vector by [`normalize_authenticated_results_for_publication`],
/// so they cannot enter `total`, and a run whose only rows are exclusions is
/// not a proof. Only an EXACT row is read ([`test_harness_exclusion_of`]); a
/// lookalike stays in the vector and the gate's partition counts it as a
/// genuine unknown with a transport defect.
pub(crate) fn authenticated_test_harness_exclusions(
    results: &[VerificationResult],
) -> Vec<trust_types::GateExclusionReport> {
    let mut exclusions = results.iter().filter_map(test_harness_exclusion_of).collect::<Vec<_>>();
    exclusions.sort_by(|left, right| left.function.cmp(&right.function));
    exclusions.dedup_by(|left, right| left.function == right.function);
    exclusions
}

/// Trust (CB4): the exclusion a row stands for, when — and only when — it is
/// the compiler's exact test-harness exclusion row, bound to a Cargo proof unit
/// that builds a libtest harness.
///
/// Every condition is load-bearing and fails closed to `None` (the caller then
/// counts the row as a genuine unknown):
///
/// * kind, solver, description and reason are exactly what the compiler mints
///   (`trust_types::exclusion::is_exact_test_harness_exclusion_row`);
/// * the outcome is the `skipped` wire value (read here as `Unknown`) — a row
///   of this kind claiming proved, runtime-checked, failed or timed out is a
///   defect;
/// * it carries no counterexample, no time, and no claim evidence (the unit's
///   runtime-check environment is tolerated: the compiler states it for every
///   row alike and it says nothing about this row's claim);
/// * `main` carries no location (it has none: rustc builds it at `DUMMY_SP`);
/// * the row's Cargo proof unit compiles in a test-harness mode (`test`,
///   `check-test`), read from the unit identity the transport stamped on it —
///   so a `build`/`check` unit, a doctest, a build script or an unscoped raw
///   compile cannot mint an exclusion.
pub(crate) fn test_harness_exclusion_of(
    result: &VerificationResult,
) -> Option<trust_types::GateExclusionReport> {
    use trust_types::exclusion::{
        TEST_HARNESS_EXCLUSION_TAG, TestHarnessExclusionItem, is_exact_test_harness_exclusion_row,
        parse_test_harness_exclusion_reason, test_harness_exclusion_admits_unit_mode,
    };
    if !is_exact_test_harness_exclusion_row(
        &result.kind,
        &result.backend,
        &result.message,
        result.reason.as_deref(),
    ) || result.outcome != VerificationOutcome::Unknown
        || result.counterexample.is_some()
        || result.time_ms != Some(0)
        || result.function.trim().is_empty()
        || !structured_transport_evidence(result)
            .is_none_or(|evidence| evidence.carries_only_envelope_facts())
    {
        return None;
    }
    let parsed = parse_test_harness_exclusion_reason(result.reason.as_deref()?)?;
    if parsed.item == TestHarnessExclusionItem::HarnessMain && result.location.is_some() {
        return None;
    }
    let mode = crate::test_target_panics::cargo_target_unit_mode(&result.function)?;
    if !test_harness_exclusion_admits_unit_mode(&mode) {
        return None;
    }
    Some(trust_types::GateExclusionReport {
        function: result.function.clone(),
        reason: TEST_HARNESS_EXCLUSION_TAG.to_string(),
        item: parsed.item.tag().to_string(),
        test_function: parsed.test_function,
    })
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
        // NOT `is_none()`. The compiler stamps its runtime-check environment on
        // the UNIT envelope and `transport_to_verification_result` binds it to
        // every row, inventory rows included, so since that landed this row has
        // always carried structured evidence and `is_none()` matched nothing.
        // The consequence was not a lost elision but a failed gate: an unelided
        // inventory row is a malformed lookalike, gets downgraded for want of a
        // claim digest, and takes `Gate: PASS` with it — measured 2026-09-26,
        // `targo trust check` on any program containing one trivially
        // panic-free function returned `INCONCLUSIVE [strict lane, exit 1]`.
        // See `zero_obligation_inventory_survives_a_stated_runtime_check_env`.
        //
        // What may be tolerated here is exactly what says NOTHING about this
        // row's claim. `runtime_checks` is a per-unit environment fact the
        // compiler states for every row alike, and the T9 `identity` is derived
        // from the row's kind and position, not its claim. Every other
        // structured field is
        // claim evidence — an id, a digest, a typed kind, a mandate bit, native
        // IR, proof evidence, a monitor — and a row bearing any of them is not
        // inventory, whatever it calls itself. Those still fail closed.
        && structured_transport_evidence(result)
            .is_none_or(|evidence| evidence.carries_only_envelope_facts())
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
///
/// Trust (#220): `demoted` is a parallel flag vector marking rows this run's
/// publication demotion rewrote from a favorable compiler outcome to `Unknown`.
/// It is filtered in lockstep with `results` and the removals are counted, so
/// the caller can tell a DELETED demotion (invisible everywhere, including
/// `--json`) from an ordinary redundant alias. The retain predicate below is
/// unchanged — the flags are observational and cannot affect which rows stay.
fn elide_rows_proved_only_by(
    results: &mut Vec<VerificationResult>,
    demoted: &mut Vec<bool>,
    derive: fn(&mut [VerificationResult]),
) -> ElidedRowCounts {
    let mut derived = results.clone();
    derive(&mut derived);
    debug_assert_eq!(results.len(), derived.len());
    debug_assert_eq!(results.len(), demoted.len());

    let keep: Vec<bool> = results
        .iter()
        .zip(derived.iter())
        .map(|(original, candidate)| {
            original.outcome.is_proved()
                || !candidate.outcome.is_proved()
                || !structured_transport_vc_kind_is_authority_safe(original)
        })
        .collect();

    let mut counts = ElidedRowCounts::default();
    for (index, kept) in keep.iter().enumerate() {
        if !kept {
            use trust_types::determinism::{NotedStop, Reproducibility};
            let row = &results[index];
            let cause = crate::determinism_report::row_stop_cause(row);
            let item = crate::determinism_report::row_stop_item(row);
            if cause.reproducibility() != Reproducibility::Deterministic
                || cause.is_solver_count()
                || item.is_some()
            {
                counts.stops.push(PublicationStop {
                    package: structured_transport_evidence(row)
                        .and_then(|e| e.identity)
                        .map(|identity| identity.package),
                    stop: NotedStop {
                        lane: "publication-alias-elision".into(),
                        cause,
                        item,
                        count: 1,
                    },
                });
            }
            let withheld = demoted.get(index).copied().unwrap_or(false);
            counts
                .diagnostics
                .push(ElidedPublicationDiagnostic::from_result(&results[index], withheld));
            if withheld {
                counts.demoted += 1;
            } else {
                counts.other += 1;
            }
        }
    }

    let mut index = 0usize;
    results.retain(|_| {
        let kept = keep.get(index).copied().unwrap_or(true);
        index += 1;
        kept
    });
    let mut index = 0usize;
    demoted.retain(|_| {
        let kept = keep.get(index).copied().unwrap_or(true);
        index += 1;
        kept
    });

    counts
}

/// Re-derive a full-verifier row's outcome from its native proof evidence, so a
/// favorable label can never outrun the evidence behind it.
///
/// `Proved` is proof credit and is accepted ONLY when the native status is
/// `Proved` — anything else is a laundered false PROVE and fails closed to
/// `Unknown`. `Failed`/`Timeout` evidence statuses are preserved as the
/// compiler stated them, with two exceptions: a row the compiler published
/// `Timeout` stays a timeout over any status but `Failed` (a clock stop; see the
/// arm), and a `Failed` status on a row the compiler reported `Unknown` stays
/// `Unknown`.
///
/// Trust (2026-09-28): that last pair is the compiler WITHHOLDING a refutation.
/// The native engine's status is its verdict on its own encoding, and the
/// compiler decides whether that verdict is a refutation of the program. It
/// withholds a solver model that chooses a value no execution produces, such as
/// the unmodeled return of a same-crate callee (DQ D5-A) or a loop-carried state
/// with no invariant (`trust_vcgen::GENERIC_REFUTATION_HELD_PREFIX`). Measured:
/// `fn lower(x, y) -> u64 ensures result <= x { min2(x, y) }` is TRUE, and raw
/// `trustc` reports its row `unknown` with "generic solver counterexample
/// withheld". This function used to map every `Failed` status to `Failed`, so
/// `targo trust check` printed `[FAILED]` and `Verdict: HAS VIOLATIONS` for a
/// contract that holds. The row now stays `Unknown`. That is not proof credit:
/// the gate still refuses an unknown row.
///
/// `RuntimeChecked` is NOT proof credit. It is the compiler's policy-B
/// disposition (`docs/design/2026-07-25-completeness-gap-policy-ruling.md`):
/// the solver could not decide, the runtime check rustc already emits stays in
/// the binary, and the gate counts the row as CONDITIONAL — `conditional-pass`,
/// never `pass`. It therefore cannot launder anything, and the compiler is the
/// sole authority on which runtime checks the emitted binary carries. So a
/// `RuntimeChecked` label is preserved across the "solver could not decide"
/// statuses (`Unknown`/`Unsupported`/`Rejected`) and across a row with no
/// evidence attached — PROVIDED the row is a real typed obligation
/// ([`transport_row_can_carry_runtime_check`]); an untyped or
/// `UnsupportedMir` row cannot say what is runtime-checked and stays `Unknown`.
///
/// Trust (2026-09-14): this function used to demote EVERY `RuntimeChecked`
/// full-verifier row to `Unknown` — via the `Unsupported` arm when evidence was
/// attached, and unconditionally when it was not. Measured on the ruling's own
/// example, `fn main() { println!("hello"); }`: the compiler shipped
/// `outcome=runtime_checked, proof_evidence.status=unsupported` for the
/// `std::io::_print` absent-callee row (a runtime-checked gap with vanilla
/// broken-pipe semantics, per the ruling's 2026-09-10 amendment), bare `trustc`
/// built and ran it with exit 0, and `targo trust build` failed the SAME
/// compile with `1 inconclusive` and no binary — because this demotion turned
/// the row into `unknown` and the gate at `report.rs` requires
/// `counts.unknown == 0`. targo's own `--help` states the intended rule ("on the
/// default lane every obligation is proved or runtime-checked"); the code now
/// matches it. `Proved`-without-evidence stays fail-closed exactly as before.
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
            // Determinism plan §3.7 (2026-10-01): a row the compiler published
            // `timeout` is a CLOCK STOP — a later lane gave up on the function
            // deadline before it decided the row or minted its authority — and
            // it keeps that outcome over whatever its native evidence says: the
            // `unsupported` of a bundle the deadline declined, the `unknown` of
            // a row the bridge never reached, the `proved` of a row whose live
            // mint the deadline refused. A timeout grants nothing, so it can
            // launder nothing; re-deriving it from the evidence turned it back
            // into the unexplained `unknown` the stamp exists to end, and kept
            // it out of the function's `timed_out`. Only a refutation outranks
            // it.
            status
                if parsed == VerificationOutcome::Timeout
                    && status != trust_types::TransportProofStatus::Failed =>
            {
                VerificationOutcome::Timeout
            }
            trust_types::TransportProofStatus::Proved => VerificationOutcome::Unknown,
            trust_types::TransportProofStatus::Failed if parsed == VerificationOutcome::Unknown => {
                VerificationOutcome::Unknown
            }
            trust_types::TransportProofStatus::Failed => VerificationOutcome::Failed,
            trust_types::TransportProofStatus::Timeout => VerificationOutcome::Timeout,
            trust_types::TransportProofStatus::Unknown
            | trust_types::TransportProofStatus::Unsupported
            | trust_types::TransportProofStatus::Rejected
                if parsed == VerificationOutcome::RuntimeChecked
                    && transport_row_can_carry_runtime_check(result) =>
            {
                VerificationOutcome::RuntimeChecked
            }
            trust_types::TransportProofStatus::Unknown
            | trust_types::TransportProofStatus::Unsupported
            | trust_types::TransportProofStatus::Rejected => VerificationOutcome::Unknown,
            _ => VerificationOutcome::Unknown,
        };
    }

    // No evidence attached: `RuntimeChecked` is preserved on the same condition
    // as above; an untyped or unsupported-MIR row still fails closed.
    match parsed {
        VerificationOutcome::RuntimeChecked if transport_row_can_carry_runtime_check(result) => {
            VerificationOutcome::RuntimeChecked
        }
        VerificationOutcome::RuntimeChecked => VerificationOutcome::Unknown,
        other => other,
    }
}

/// Whether a full-verifier row is a real, typed obligation — the precondition for
/// its `RuntimeChecked` label to survive [`normalize_transport_outcome`].
///
/// A runtime check is a claim about WHAT rustc left in the binary, so the row
/// must say what that is: a transport that omitted the typed VC kind, or one
/// classified `UnsupportedMir` (the compiler could not lower it, so no fallback
/// can be vouched for), cannot carry runtime-check authority and stays
/// `Unknown` — exactly the rule `report.rs`'s `unsupported_favorable` and
/// `pipeline::tests::parse_compiler_stderr_keeps_unsupported_full_verifier_
/// inconclusive` pin. The `std::io::_print` absent-callee row that motivated
/// this passes: `typed_kind = Assertion`.
fn transport_row_can_carry_runtime_check(result: &trust_types::TransportObligationResult) -> bool {
    result
        .typed_kind
        .as_deref()
        .is_some_and(|kind| !matches!(kind, trust_types::VcKind::UnsupportedMir { .. }))
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

fn is_full_verifier_solver(solver: &str) -> bool {
    let solver = solver.trim();
    solver == "trust-full-verifier" || solver.contains("full-verifier")
}

#[cfg(test)]
mod subsumption_tests {
    use trust_types::{BinOp, HardenedVcCategory, SourceSpan, Ty, VcKind};

    use super::{
        STRUCTURED_TRANSPORT_EVIDENCE_PREFIX, StructuredTransportEvidence, VerificationOutcome,
        VerificationResult, authenticated_zero_obligation_inventory,
        exact_structured_transport_vc_kind, normalize_authenticated_results_for_publication,
        structured_transport_evidence, structured_transport_vc_kind_is_authority_safe,
        subsume_hardened_panic_twins,
    };

    #[test]
    fn actual_selfuse_preserves_all_authored_source_rows() {
        let frames: Vec<serde_json::Value> =
            serde_json::from_str(include_str!("fixtures/native_wp_selfuse_transport.json"))
                .unwrap();
        let mut rows = Vec::new();
        for frame in frames {
            let function = frame["function"].as_str().unwrap();
            let package = frame["package_name"].as_str().unwrap();
            let runtime_checks = serde_json::from_value(frame["runtime_checks"].clone()).unwrap();
            let source = frame["source_sha256"].as_str().unwrap();
            let ids = frame["stable_ids"].as_array().unwrap();
            let transport: Vec<trust_types::TransportObligationResult> =
                serde_json::from_value(frame["results"].clone()).unwrap();
            assert_eq!(transport.len(), ids.len());
            for (row, id) in transport.iter().zip(ids) {
                let identity = trust_types::obligation_identity::ObligationIdentity {
                    key: format!("{function}#{}", id.as_str().unwrap()),
                    package: package.into(),
                    function_source_sha256: Some(source.into()),
                    expanded_function_identity: None,
                };
                rows.push(super::transport_to_verification_result(
                    function,
                    row,
                    Some(runtime_checks),
                    Some(identity),
                ));
            }
        }
        let ids = |rows: &[VerificationResult]| {
            rows.iter()
                .map(|row| structured_transport_evidence(row).unwrap().obligation_id.unwrap())
                .collect::<std::collections::BTreeSet<_>>()
        };
        let original_ids = ids(&rows);
        assert_eq!(rows.len(), 13);
        let boundary = normalize_authenticated_results_for_publication(&mut rows, None);
        assert_eq!(rows.len(), 13, "authored source claims are not diagnostic aliases");
        assert_eq!(ids(&rows), original_ids);
        assert_eq!(rows.iter().filter(|row| row.outcome == VerificationOutcome::Proved).count(), 3);
        assert_eq!(
            rows.iter().filter(|row| row.outcome == VerificationOutcome::RuntimeChecked).count(),
            5
        );
        assert_eq!(
            rows.iter().filter(|row| row.outcome == VerificationOutcome::Unknown).count(),
            5
        );
        for row in &rows {
            let evidence = structured_transport_evidence(row).unwrap();
            let id = evidence.obligation_id.as_deref().unwrap();
            if id.starts_with("obligation:") || id.contains("__wrong:postcondition:") {
                assert_eq!(row.outcome, VerificationOutcome::Unknown, "{id}");
            }
            if row.outcome == VerificationOutcome::Proved {
                assert!(id.starts_with("vc:"));
                assert_eq!(
                    evidence.proof_evidence.as_ref().unwrap().strength.as_ref().unwrap().assurance,
                    trust_types::AssuranceLevel::Certified
                );
            }
        }
        assert_eq!(boundary.withheld_elided, 0);
        assert_eq!(boundary.alias_elided, 0);
        assert_eq!(boundary.withheld_relabelled, 3);
        assert_eq!(boundary.published_favorable, 8);
    }

    #[test]
    fn malformed_typed_source_row_survives_elision_and_future_relabel() {
        let body = with_obligation_id(
            result("identity", "postcond", "postcondition", VerificationOutcome::Proved, None),
            "vc:identity:postcondition:0",
        );
        let malformed = with_obligation_id_and_typed_kind(
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
        assert!(exact_structured_transport_vc_kind(&malformed).is_err());

        fn propose_second_row_as_proved(rows: &mut [VerificationResult]) {
            rows[1].outcome = VerificationOutcome::Proved;
        }
        let mut rows = vec![body, malformed];
        elide_rows_proved_only_by(&mut rows, propose_second_row_as_proved);
        assert_eq!(rows.len(), 2);
        assert_eq!(rows[1].outcome, VerificationOutcome::Unknown);

        let mut future_internal_rewrite = vec![rows[1].clone()];
        future_internal_rewrite[0].outcome = VerificationOutcome::Proved;
        normalize_authenticated_results_for_publication(&mut future_internal_rewrite, None);
        assert_eq!(future_internal_rewrite.len(), 1);
        assert_eq!(future_internal_rewrite[0].outcome, VerificationOutcome::Unknown);
        assert!(
            future_internal_rewrite[0]
                .reason
                .as_deref()
                .is_some_and(|reason| reason.contains("inconsistent exact typed VC"))
        );
    }

    /// Trust (#220): the pre-#220 two-argument shape, so the existing elision
    /// tests below still read as assertions about the retain predicate and not
    /// about the new demotion bookkeeping. The tests that DO exercise the
    /// bookkeeping call the real function through
    /// `normalize_authenticated_results_for_publication`.
    fn elide_rows_proved_only_by(
        results: &mut Vec<VerificationResult>,
        derive: fn(&mut [VerificationResult]),
    ) {
        let mut demoted = vec![false; results.len()];
        super::elide_rows_proved_only_by(results, &mut demoted, derive);
    }

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
            "overflow:div" | "arithmetic_overflow_div" => Some(VcKind::ArithmeticOverflow {
                op: BinOp::Div,
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

    /// TINV step 2 (2026-10-05): both compact spellings of a type-invariant row drop
    /// `ty` and `site`, so an untyped row must lose any favourable outcome.
    #[test]
    fn untyped_type_invariant_rows_are_downgraded() {
        let tinv = trust_types::VcKind::TypeInvariant {
            ty: "c::S".to_string(),
            point: trust_types::TypeInvariantPoint::Call,
            site: trust_types::TypeInvariantSite { block: 1, statement_index: 0 },
            conjunct: 0,
            ordinal: 0,
            edge: None,
        };
        for kind in ["type_invariant:call", "type_invariant_call"] {
            assert!(super::compact_vc_tag_requires_typed_kind(kind), "{kind}");
            let transport = trust_types::TransportObligationResult {
                assumes: Vec::new(),
                obligation_id: None,
                claim_digest_sha256: None,
                original_vc_snapshot: None,
                typed_kind: None,
                kind: kind.to_string(),
                description: tinv.description(),
                location: None,
                outcome: trust_types::Outcome::Proved,
                solver: "ay".to_string(),
                time_ms: 0,
                counterexample: None,
                counterexample_model: None,
                reason: None,
                design_mandate: false,
                gap_class: None,
                native_trust_ir: None,
                proof_evidence: None,
                monitor: None,
                grade: None,
            };
            let row = super::transport_to_verification_result("c::f", &transport, None, None);
            assert!(
                matches!(row.outcome, VerificationOutcome::Unknown),
                "{kind}: {:?}",
                row.outcome
            );
            assert!(
                row.reason
                    .as_deref()
                    .unwrap_or_default()
                    .contains("omitted the exact typed VC kind"),
                "{kind}: {:?}",
                row.reason
            );
        }
        // With the exact typed kind, the compact tag is no defect.
        let typed = trust_types::TransportObligationResult {
            assumes: Vec::new(),
            obligation_id: None,
            claim_digest_sha256: None,
            original_vc_snapshot: None,
            typed_kind: Some(Box::new(tinv.clone())),
            kind: tinv.transport_tag(),
            description: tinv.description(),
            location: None,
            outcome: trust_types::Outcome::Proved,
            solver: "ay".to_string(),
            time_ms: 0,
            counterexample: None,
            counterexample_model: None,
            reason: None,
            design_mandate: false,
            gap_class: None,
            native_trust_ir: None,
            proof_evidence: None,
            monitor: None,
            grade: None,
        };
        let row = super::transport_to_verification_result("c::f", &typed, None, None);
        assert!(
            !row.reason.as_deref().unwrap_or_default().contains("typed VC kind"),
            "{:?}",
            row.reason
        );
    }

    /// REGRESSION (2026-09-26). The inventory row must still be elided once the
    /// compiler states its runtime-check environment — the field is stamped on
    /// the UNIT envelope and bound to every row, so after `f888a642ae6` the
    /// `is_none()` test this replaced matched no real row at all. The visible
    /// failure was not a miscount: the unelided row was downgraded for want of a
    /// claim digest and `targo trust check` returned
    /// `Gate: INCONCLUSIVE [strict lane, exit 1]` on any program with one
    /// trivially panic-free function. Built through the real producers so the
    /// writer and this reader cannot drift apart on the payload shape.
    #[test]
    fn zero_obligation_inventory_survives_a_stated_runtime_check_env() {
        let transport = trust_types::TransportObligationResult {
            assumes: Vec::new(),
            obligation_id: None,
            claim_digest_sha256: None,
            original_vc_snapshot: None,
            typed_kind: None,
            kind: "no_obligations".to_string(),
            description: "function has no panic obligations (trivially panic-free)".to_string(),
            location: None,
            outcome: trust_types::Outcome::Proved,
            solver: "trust-structural".to_string(),
            time_ms: 0,
            counterexample: None,
            counterexample_model: None,
            reason: Some("verified: zero panic obligations".to_string()),
            design_mandate: false,
            gap_class: None,
            native_trust_ir: None,
            proof_evidence: None,
            monitor: None,
            grade: None,
        };
        let env = trust_types::RuntimeCheckEnv::new(true, true);
        let mut results = vec![super::transport_to_verification_result(
            "crate::empty",
            &transport,
            Some(env),
            None,
        )];
        assert!(
            !results[0].raw_line.is_empty(),
            "the stated environment must actually reach the row, or this test proves nothing"
        );

        let boundary = normalize_authenticated_results_for_publication(&mut results, None);
        assert!(results.is_empty(), "inventory must be elided, not downgraded into the gate");
        assert_eq!(boundary.inventory_elided, 1);

        // NEGATIVE CONTROL: the same row plus ONE claim field is not inventory.
        let mut claimed = transport.clone();
        claimed.claim_digest_sha256 = Some("c".repeat(64));
        let mut results = vec![super::transport_to_verification_result(
            "crate::empty",
            &claimed,
            Some(env),
            None,
        )];
        let boundary = normalize_authenticated_results_for_publication(&mut results, None);
        assert_eq!(
            boundary.inventory_elided, 0,
            "a row carrying claim evidence must not be elided as inventory"
        );
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
            assumes: Vec::new(),
            obligation_id: None,
            claim_digest_sha256: None,
            original_vc_snapshot: None,
            typed_kind: Some(Box::new(typed_kind)),
            design_mandate: false,
            runtime_checks: None,
            native_trust_ir: None,
            proof_evidence: None,
            monitor: None,
            identity: None,
            grade: None,
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
            assumes: Vec::new(),
            obligation_id: Some(obligation_id.to_string()),
            claim_digest_sha256: None,
            original_vc_snapshot: None,
            typed_kind: typed_kind.map(Box::new),
            design_mandate: false,
            runtime_checks: None,
            native_trust_ir: None,
            proof_evidence: None,
            monitor: None,
            identity: None,
            grade: None,
        };
        result.raw_line = format!(
            "{STRUCTURED_TRANSPORT_EVIDENCE_PREFIX}{}",
            serde_json::to_string(&evidence).unwrap()
        );
        result
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

    /// PARITY: the AGGREGATE report spelling (`arithmetic_overflow_<op>`) is a lossy
    /// compact tag that `transport_tag()` never emits — it renders `overflow:<op>` —
    /// so a row carrying the aggregate spelling can never satisfy the exact typed
    /// cross-check and is authority-UNSAFE, whether or not it carries a payload.
    /// `add`/`sub`/`mul` were already listed in `compact_vc_tag_requires_typed_kind`
    /// and therefore already failed closed here; `div`/`rem` were NOT listed, so an
    /// UNTYPED aggregate div row could carry subsumption authority that an identical
    /// add row could not. That asymmetry is the gap this pins shut: Div must fail
    /// closed EXACTLY as Add does. The live transport path is covered by
    /// `transport_spelled_div_overflow_sibling_subsumes_its_twin`.
    #[test]
    fn aggregate_spelled_arithmetic_siblings_fail_closed_identically_for_div_and_add() {
        for (kind, detail, marker) in [
            ("arithmetic_overflow_div", "arithmetic overflow (Div)", "Overflow(Div)"),
            ("arithmetic_overflow_add", "arithmetic overflow (Add)", "Overflow(Add)"),
        ] {
            let s = span(419, 22, 32);
            let mut results = vec![
                result("f", kind, detail, VerificationOutcome::Proved, Some(s.clone())),
                overflow_twin("f", marker, s.clone()),
            ];
            subsume_hardened_panic_twins(&mut results);
            assert!(
                matches!(results[1].outcome, VerificationOutcome::Unknown),
                "aggregate-spelled `{kind}` must not carry subsumption authority; got {:?}",
                results[1].outcome
            );
        }
    }

    /// REGRESSION (a3d `cell_index_1d`, lib.rs:419:22-32). A Div sibling arriving
    /// over the TRANSPORT carries whatever `VcKind::transport_tag()` produced.
    /// That used to collapse `Div`/`Rem` onto the OP-LESS `"overflow"`, which
    /// `direct_panic_sibling_family` refuses by design (an op-less tag must never
    /// discharge an op-specific twin). So a PROVED div-overflow sibling was not
    /// recognized as a sibling at all and its twin stayed UNKNOWN forever, with
    /// no diagnostic — the twin simply never found its partner.
    #[test]
    fn transport_spelled_div_overflow_sibling_subsumes_its_twin() {
        let s = span(419, 22, 32);
        let mut results = vec![
            result(
                "f",
                "overflow:div",
                "arithmetic overflow (Div)",
                VerificationOutcome::Proved,
                Some(s.clone()),
            ),
            overflow_twin("f", "Overflow(Div)", s.clone()),
        ];
        subsume_hardened_panic_twins(&mut results);
        assert!(
            matches!(results[1].outcome, VerificationOutcome::Proved),
            "transport-spelled Div sibling must subsume its same-span twin; got {:?} ({:?})",
            results[1].outcome,
            results[1].reason
        );
        assert!(results[1].backend.starts_with("subsumed:"));
    }

    /// Naming `Div` must NOT weaken cross-op isolation: a proved sibling of a
    /// DIFFERENT arithmetic op at a byte-identical span must still never discharge
    /// a Div twin. (Macro expansions do collapse distinct asserts onto one span.)
    #[test]
    fn div_twin_is_not_subsumed_by_a_proved_add_sibling_at_the_same_span() {
        let s = span(419, 22, 32);
        let mut results = vec![
            result(
                "f",
                "overflow:add",
                "arithmetic overflow (Add)",
                VerificationOutcome::Proved,
                Some(s.clone()),
            ),
            overflow_twin("f", "Overflow(Div)", s.clone()),
        ];
        subsume_hardened_panic_twins(&mut results);
        assert!(
            matches!(results[1].outcome, VerificationOutcome::Unknown),
            "an Add sibling must NEVER discharge a Div twin; got {:?}",
            results[1].outcome
        );
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
