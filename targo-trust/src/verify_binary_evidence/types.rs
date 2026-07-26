// Data types — evidence aggregate, import/production reports, and the records
// they contain — for the binary verification evidence pipeline.

use std::path::PathBuf;

use serde::{Deserialize, Serialize};
use trust_proof_cert::{
    CheckedBinaryCertificateArtifact, CheckedBinaryCertificateSourceBackpropagationGate,
    SolverProofExport,
};
use trust_types::{
    BinaryArtifactDigestIdentity, BinarySelectedImageIdentity, ReplayStatus, SolverDispatchRecord,
    SolverQuerySemantics,
};

use super::binary_artifact_digest_identity_is_empty;

#[derive(Debug, Clone, Default)]
pub(crate) struct VerifyBinaryEvidence {
    pub(crate) required_vcs: usize,
    pub(crate) solver_dispatch: Vec<SolverDispatchRecord>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct NormalizedSolverProofExportArtifact {
    pub(crate) schema_version: String,
    pub(crate) dispatch_id: String,
    pub(crate) vc_sha256: String,
    pub(crate) origin_sha256: String,
    pub(crate) assumption_digest: String,
    pub(crate) query_semantics: SolverQuerySemantics,
    pub(crate) replay: ReplayStatus,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) replay_transcript_digest: Option<String>,
    pub(crate) binary_artifact_digest_identity: BinaryArtifactDigestIdentity,
    pub(crate) selected_image_identity: BinarySelectedImageIdentity,
    pub(crate) source_backpropagation_gate_sha256: String,
    pub(crate) source_backpropagation_gate: CheckedBinaryCertificateSourceBackpropagationGate,
    pub(crate) format: String,
    pub(crate) proof_sha256: String,
    pub(crate) proof_byte_len: usize,
    pub(crate) proof_export_metadata_sha256: String,
    pub(crate) proof_export: SolverProofExport,
}

#[derive(Debug, Clone)]
pub(crate) struct LoadedNormalizedSolverProofExportArtifact {
    pub(crate) artifact: NormalizedSolverProofExportArtifact,
    pub(crate) content_sha256: String,
}

#[derive(Debug, Clone)]
pub(crate) struct NormalizedSolverProofExportArtifactError {
    pub(crate) code: String,
    pub(crate) detail: String,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct CheckedCertificateImportReport {
    #[serde(default = "checked_certificate_import_loader_status_default")]
    pub(crate) loader_status: String,
    #[serde(default)]
    pub(crate) requested_artifacts: usize,
    #[serde(default)]
    pub(crate) requested_manifests: usize,
    pub(crate) loaded_artifacts: usize,
    pub(crate) imported: usize,
    pub(crate) unmatched_artifacts: usize,
    pub(crate) rejected_artifacts: usize,
    pub(crate) dispatches_missing_canonical_binding: usize,
    pub(crate) artifacts: Vec<CheckedCertificateArtifactImportRecord>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) loader_blocker: Option<CheckedCertificateLoaderBlockerRecord>,
    pub(crate) diagnostics: Vec<String>,
}

impl CheckedCertificateImportReport {
    pub(crate) fn loader_failure(
        command: &'static str,
        requested_artifacts: usize,
        requested_manifests: usize,
        error: impl std::fmt::Display,
    ) -> Self {
        let detail = format!("failed to load checked certificate artifact or manifest: {error}");
        Self {
            loader_status: "load_failed".to_string(),
            requested_artifacts,
            requested_manifests,
            loader_blocker: Some(CheckedCertificateLoaderBlockerRecord {
                code: "checked-certificate-load-failed".to_string(),
                stage: format!("targo-trust::{command}-loader"),
                detail: detail.clone(),
                evidence_required: vec![
                    "loadable_checked_certificate_artifact".to_string(),
                    "loadable_checked_certificate_manifest".to_string(),
                ],
            }),
            diagnostics: vec![detail],
            ..Default::default()
        }
    }

    pub(crate) fn loader_failed(&self) -> bool {
        self.loader_status == "load_failed"
    }
}

fn checked_certificate_import_loader_status_default() -> String {
    "loaded".to_string()
}

pub(super) fn loaded_import_loader_status(loaded_artifacts: usize) -> String {
    if loaded_artifacts == 0 { "loaded_empty" } else { "loaded" }.to_string()
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct CheckedCertificateLoaderBlockerRecord {
    pub(crate) code: String,
    pub(crate) stage: String,
    pub(crate) detail: String,
    #[serde(default)]
    pub(crate) evidence_required: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct CheckedCertificateArtifactImportRecord {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) artifact_path: Option<String>,
    pub(crate) certificate_sha256: String,
    #[serde(default)]
    pub(crate) checker: String,
    #[serde(default)]
    pub(crate) checker_version: String,
    #[serde(default)]
    pub(crate) format: String,
    #[serde(default)]
    pub(crate) checked_at_unix_ms: u64,
    pub(crate) vc_sha256: String,
    pub(crate) origin_sha256: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub(crate) proof_export_sha256: String,
    #[serde(default, skip_serializing_if = "binary_artifact_digest_identity_is_empty")]
    pub(crate) binary_artifact_digest_identity: BinaryArtifactDigestIdentity,
    #[serde(default)]
    pub(crate) source_backpropagation_gate: CheckedBinaryCertificateSourceBackpropagationGate,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) manifest_identity_sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) source_backpropagation_gate_sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) replay_transcript_digest: Option<String>,
    #[serde(default)]
    pub(crate) replay_digest_identity: CheckedCertificateReplayDigestIdentityRecord,
    #[serde(default)]
    pub(crate) production_checker_evidence_status: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) production_checker_evidence_sha256: Option<String>,
    pub(crate) status: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) dispatch_id: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) diagnostic: Option<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct CheckedCertificateReplayDigestIdentityRecord {
    pub(crate) status: String,
    pub(crate) replay: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) replay_transcript_digest: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) binary_artifact_digest_identity: Option<BinaryArtifactDigestIdentity>,
    #[serde(default)]
    pub(crate) blockers: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct CheckedCertificateProductionReport {
    pub(crate) requested: bool,
    pub(crate) status: String,
    pub(crate) export_dir: String,
    pub(crate) checker_selection: String,
    pub(crate) candidate_dispatches: usize,
    pub(crate) canonical_binding_candidates: usize,
    pub(crate) proof_export_candidates: usize,
    pub(crate) raw_solver_proof_byte_dispatches: usize,
    pub(crate) already_checked_certificates: usize,
    pub(crate) exported_artifacts: usize,
    pub(crate) rejected_dispatches: usize,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) artifact_paths: Vec<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) manifest_path: Option<String>,
    #[serde(default)]
    pub(crate) source_backpropagation_gate: CheckedBinaryCertificateSourceBackpropagationGate,
    #[serde(default)]
    pub(crate) proof_export_records: Vec<CheckedCertificateProofExportRecord>,
    #[serde(default)]
    pub(crate) certificate_check_records: Vec<CheckedCertificateCheckRecord>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) export_row_records: Vec<CheckedCertificateExportRowRecord>,
    #[serde(default)]
    pub(crate) blocker_records: Vec<CheckedCertificateProductionBlockerRecord>,
    pub(crate) blockers: Vec<String>,
    pub(crate) diagnostics: Vec<String>,
}

impl CheckedCertificateProductionReport {
    pub(crate) fn is_blocked(&self) -> bool {
        self.requested && self.status == "blocked"
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct CheckedCertificateProofExportRecord {
    pub(crate) dispatch_id: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) function: Option<String>,
    pub(crate) solver: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) backend: Option<String>,
    pub(crate) canonical_binding: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) vc_sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) origin_sha256: Option<String>,
    pub(crate) status: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) format: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) proof_sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) proof_export_metadata_sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) proof_export_artifact_sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) proof_export_content_addressed: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) artifact_path: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) proof_export_metadata_path: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) proof_export_payload_path: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) checked_certificate_artifact_path: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) raw_solver_proof_bytes: Option<RawSolverProofByteEvidence>,
    #[serde(default)]
    pub(crate) blocker_codes: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct CheckedCertificateCheckRecord {
    pub(crate) dispatch_id: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) function: Option<String>,
    pub(crate) status: String,
    pub(crate) certificate_status: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) checker: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) format: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) certificate_sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) manifest_identity_sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) source_backpropagation_gate_sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) replay_transcript_digest: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) binary_artifact_digest_identity: Option<BinaryArtifactDigestIdentity>,
    #[serde(default)]
    pub(crate) replay_digest_identity: CheckedCertificateReplayDigestIdentityRecord,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) production_checker_evidence_sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) external_checker_binary_sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) external_checker_invocation_sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) external_checker_stdout_sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) external_checker_stderr_sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) error_kind: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) diagnostic: Option<String>,
    #[serde(default)]
    pub(crate) blocker_codes: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct CheckedCertificateExportRowRecord {
    pub(crate) dispatch_id: String,
    pub(crate) vc_sha256: String,
    pub(crate) origin_sha256: String,
    pub(crate) assumption_digest: String,
    pub(crate) query_semantics: SolverQuerySemantics,
    pub(crate) replay: ReplayStatus,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) replay_transcript_digest: Option<String>,
    pub(crate) proof_sha256: String,
    pub(crate) proof_export_sha256: String,
    pub(crate) proof_export_artifact_sha256: String,
    pub(crate) proof_export_artifact_path: String,
    pub(crate) certificate_sha256: String,
    pub(crate) certificate_path: PathBuf,
    pub(crate) checked_certificate_artifact_path: String,
    pub(crate) manifest_identity_sha256: String,
    pub(crate) source_backpropagation_gate_sha256: String,
    pub(crate) source_backpropagation_gate: CheckedBinaryCertificateSourceBackpropagationGate,
    pub(crate) binary_artifact_digest_identity: BinaryArtifactDigestIdentity,
    pub(crate) selected_image_identity: BinarySelectedImageIdentity,
    pub(crate) checker: String,
    pub(crate) checker_version: String,
    pub(crate) format: String,
    pub(crate) production_checker_evidence_sha256: String,
    pub(crate) audit_export_path: PathBuf,
    pub(crate) audit_export_sha256: String,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct CheckedCertificateProductionBlockerRecord {
    pub(crate) code: String,
    pub(crate) stage: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) dispatch_id: Option<String>,
    pub(crate) detail: String,
    #[serde(default)]
    pub(crate) evidence_required: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct RawSolverProofByteEvidence {
    pub(crate) solver: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) format: Option<String>,
    pub(crate) sha256: String,
    pub(crate) byte_len: usize,
    pub(crate) audit_only: bool,
}

#[derive(Debug, Clone)]
pub(crate) struct LoadedCheckedCertificateArtifact {
    pub(crate) path: String,
    pub(crate) artifact: CheckedBinaryCertificateArtifact,
    pub(crate) source_backpropagation_gate: CheckedBinaryCertificateSourceBackpropagationGate,
    pub(crate) manifest_identity_sha256: Option<String>,
    pub(crate) source_backpropagation_gate_sha256: Option<String>,
    pub(crate) replay_transcript_digest: Option<String>,
    pub(crate) production_checker_evidence_sha256: Option<String>,
}
