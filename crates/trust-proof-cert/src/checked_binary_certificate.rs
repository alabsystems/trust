// trust-proof-cert checked binary certificate production path scaffold
//
// This module keeps raw solver proof bytes separate from independently checked
// binary proof certificates. Raw bytes are audit evidence only; production gate
// coverage starts at BinaryCertificateChecker::check.

use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    io::{self, Read},
    path::{Component, Path, PathBuf},
    process::{Child, Command, ExitStatus, Stdio},
    thread,
    time::{Duration, Instant},
};
use thiserror::Error;
use trust_types::digest::{stable_sha256_hex, stable_sha256_hex_reader};
use trust_types::{
    BinaryArtifactDigestIdentity, BinaryOrigin, BinarySelectedImageIdentity,
    BinarySourceProvenanceSummary, ModelAssumption, ProofCertificateProductionCheckerEvidenceRef,
    ProofCertificateStatus, ReplayStatus, SolverDispatchRecord, SolverDispatchStatus,
    SolverQuerySemantics, VerificationResult,
};

use crate::binary_decomp::UnsupportedLedgerSummary;

pub type CheckerId = String;
pub type ProofFormat = String;

const CHECKED_BINARY_CERTIFICATE_SCHEMA_VERSION: &str = "checked-binary-certificate.v2";
const CHECKED_BINARY_CERTIFICATE_MANIFEST_SCHEMA_VERSION: &str = "binary-certificate-manifest.v2";
const CHECKED_BINARY_CERTIFICATE_ACCEPTANCE_SCHEMA_VERSION: &str =
    "checked-binary-certificate-acceptance.v1";
const CHECKED_BINARY_CERTIFICATE_AUDIT_EXPORT_SCHEMA_VERSION: &str =
    "checked-binary-certificate-audit-export.v1";
const CHECKED_BINARY_CERTIFICATE_AUDIT_EXPORT_BUNDLE_SCHEMA_VERSION: &str =
    "checked-binary-certificate-audit-export-bundle.v1";
const CHECKED_BINARY_CERTIFICATE_SOURCE_BACKPROPAGATION_GATE_SCHEMA_VERSION: &str =
    "checked-binary-certificate-source-backpropagation-gate.v1";
const CHECKED_BINARY_CERTIFICATE_SOURCE_BACKPROPAGATION_GATE_ROW_SCHEMA_VERSION: &str =
    "checked-binary-certificate-source-backpropagation-gate-row.v1";
const CHECKED_BINARY_CERTIFICATE_PRODUCTION_MANIFEST_SCHEMA_VERSION: &str =
    "checked-binary-certificate-production-manifest.v1";
const CHECKED_BINARY_CERTIFICATE_MANIFEST_IDENTITY_SCHEMA_VERSION: &str =
    "checked-binary-certificate-manifest-identity.v1";
const CHECKED_BINARY_CERTIFICATE_MANIFEST_IDENTITY_DIAGNOSTIC_PREFIX: &str =
    "checked_binary_certificate_manifest_identity=";
const CHECKED_BINARY_CERTIFICATE_ARTIFACT_DIR: &str = "checked-binary-certificates";
const CHECKED_BINARY_CERTIFICATE_ARTIFACT_SUFFIX: &str = "checked-binary-certificate.json";
const CHECKED_BINARY_CERTIFICATE_MANIFEST_FILENAME: &str =
    "checked-binary-certificate-manifest.json";
const CHECKED_BINARY_CERTIFICATE_AUDIT_EXPORT_BUNDLE_FILENAME: &str =
    "checked-binary-certificate-audit-export-bundle.json";
const CHECKED_BINARY_CERTIFICATE_AUDIT_EXPORT_DIR: &str = "audit-exports";
const CHECKED_BINARY_CERTIFICATE_AUDIT_EXPORT_SUFFIX: &str =
    "checked-binary-certificate-audit.json";
const SOLVER_PROOF_EXPORT_ARTIFACT_DIR: &str = "solver-proof-exports";
const SOLVER_PROOF_EXPORT_METADATA_DIR: &str = "metadata";
const SOLVER_PROOF_EXPORT_PAYLOAD_DIR: &str = "payloads";
const SOLVER_PROOF_EXPORT_METADATA_SUFFIX: &str = "solver-proof-export-metadata.json";
const SOLVER_PROOF_EXPORT_PAYLOAD_SUFFIX: &str = "solver-proof-payload";

/// Raw solver proof bytes captured for audit bundles.
///
/// This type intentionally has no conversion into [`BinaryCertificateCheckRequest`].
/// A solver backend must first normalize raw bytes into [`SolverProofExport`]
/// metadata that binds the proof to a dispatch id, canonical VC digest, proof
/// digest, query semantics, and assumption digest.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuditOnlyRawSolverProofBytes {
    pub solver: String,
    pub format: Option<ProofFormat>,
    pub bytes_sha256: String,
    pub byte_len: usize,
}

impl AuditOnlyRawSolverProofBytes {
    #[must_use]
    pub fn new(solver: impl Into<String>, format: Option<ProofFormat>, bytes: &[u8]) -> Self {
        Self {
            solver: solver.into(),
            format,
            bytes_sha256: stable_sha256_hex(bytes),
            byte_len: bytes.len(),
        }
    }
}

/// Deterministic solver proof export bound to a single solver dispatch.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SolverProofExport {
    pub dispatch_id: String,
    pub vc_sha256: String,
    pub query_semantics: SolverQuerySemantics,
    pub solver: String,
    pub solver_version: Option<String>,
    pub backend: Option<String>,
    pub format: ProofFormat,
    pub proof_sha256: String,
    pub proof_bytes: Vec<u8>,
    pub assumption_digest: String,
    pub stdout_digest: Option<String>,
    pub stderr_digest: Option<String>,
    pub exported_at_unix_ms: u64,
}

/// Canonical solver proof export metadata, excluding raw proof bytes.
///
/// The proof payload itself is bound by `proof_sha256`; this metadata record
/// captures the stable identity and transcript digests that make the export
/// reproducible without embedding raw solver output into manifest rows.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SolverProofExportMetadata {
    pub dispatch_id: String,
    pub vc_sha256: String,
    pub query_semantics: SolverQuerySemantics,
    pub solver: String,
    pub solver_version: Option<String>,
    pub backend: Option<String>,
    pub format: ProofFormat,
    pub proof_sha256: String,
    pub proof_byte_len: usize,
    pub assumption_digest: String,
    pub stdout_digest: Option<String>,
    pub stderr_digest: Option<String>,
    pub exported_at_unix_ms: u64,
}

impl SolverProofExport {
    #[must_use]
    pub fn new(
        dispatch: &SolverDispatchRecord,
        canonical_vc_bytes: &[u8],
        format: impl Into<ProofFormat>,
        proof_bytes: Vec<u8>,
        solver_version: Option<String>,
        exported_at_unix_ms: u64,
    ) -> Self {
        Self {
            dispatch_id: dispatch.id.clone(),
            vc_sha256: stable_sha256_hex(canonical_vc_bytes),
            query_semantics: dispatch.query_semantics,
            solver: dispatch.solver.clone(),
            solver_version,
            backend: dispatch.backend.clone(),
            format: format.into(),
            proof_sha256: stable_sha256_hex(&proof_bytes),
            proof_bytes,
            assumption_digest: digest_model_assumptions(&dispatch.assumptions),
            stdout_digest: None,
            stderr_digest: None,
            exported_at_unix_ms,
        }
    }

    #[must_use]
    pub fn normalized_metadata(&self) -> SolverProofExportMetadata {
        SolverProofExportMetadata {
            dispatch_id: self.dispatch_id.clone(),
            vc_sha256: self.vc_sha256.clone(),
            query_semantics: self.query_semantics,
            solver: self.solver.clone(),
            solver_version: self.solver_version.clone(),
            backend: self.backend.clone(),
            format: self.format.clone(),
            proof_sha256: self.proof_sha256.clone(),
            proof_byte_len: self.proof_bytes.len(),
            assumption_digest: self.assumption_digest.clone(),
            stdout_digest: self.stdout_digest.clone(),
            stderr_digest: self.stderr_digest.clone(),
            exported_at_unix_ms: self.exported_at_unix_ms,
        }
    }

    pub fn normalized_metadata_sha256(&self) -> Result<String, CheckError> {
        self.normalized_metadata().sha256()
    }

    /// Validate that this normalized solver proof export is bound to `dispatch`.
    ///
    /// This is structural export validation only: it checks deterministic
    /// identity and digest bindings before a production checker can consume the
    /// export. It is not an LRAT/LFSC proof replay.
    pub fn validate_for_dispatch(
        &self,
        dispatch: &SolverDispatchRecord,
        canonical_vc_bytes: &[u8],
    ) -> Result<(), CheckError> {
        if self.dispatch_id.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "solver proof export is missing dispatch id".to_string(),
            });
        }
        if self.solver.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "solver proof export is missing solver id".to_string(),
            });
        }
        if self.format.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "solver proof export is missing proof format".to_string(),
            });
        }
        validate_canonical_sha256_hex("solver proof export vc_sha256", &self.vc_sha256)?;
        validate_canonical_sha256_hex("solver proof export proof_sha256", &self.proof_sha256)?;
        validate_canonical_sha256_hex(
            "solver proof export assumption_digest",
            &self.assumption_digest,
        )?;
        if let Some(stdout_digest) = self.stdout_digest.as_deref() {
            validate_canonical_sha256_hex("solver proof export stdout_digest", stdout_digest)?;
        }
        if let Some(stderr_digest) = self.stderr_digest.as_deref() {
            validate_canonical_sha256_hex("solver proof export stderr_digest", stderr_digest)?;
        }

        if self.dispatch_id != dispatch.id {
            return Err(CheckError::CheckerInternalError {
                reason: format!(
                    "proof export dispatch id `{}` does not match request dispatch id `{}`",
                    self.dispatch_id, dispatch.id
                ),
            });
        }
        if self.solver != dispatch.solver {
            return Err(binding_mismatch("solver", dispatch.solver.as_str(), self.solver.as_str()));
        }
        if self.backend != dispatch.backend {
            return Err(binding_mismatch(
                "backend",
                format!("{:?}", dispatch.backend),
                format!("{:?}", self.backend),
            ));
        }
        if self.query_semantics != dispatch.query_semantics {
            return Err(binding_mismatch(
                "query_semantics",
                format!("{:?}", dispatch.query_semantics),
                format!("{:?}", self.query_semantics),
            ));
        }

        let actual_vc_sha256 = stable_sha256_hex(canonical_vc_bytes);
        if actual_vc_sha256 != self.vc_sha256 {
            return Err(CheckError::VcDigestMismatch {
                expected: self.vc_sha256.clone(),
                actual: actual_vc_sha256,
            });
        }

        let actual_proof_sha256 = stable_sha256_hex(&self.proof_bytes);
        if self.proof_bytes.is_empty() || actual_proof_sha256 != self.proof_sha256 {
            return Err(CheckError::MalformedProof {
                reason: "proof payload is empty or does not match proof_sha256".to_string(),
            });
        }

        let actual_assumption_digest = digest_model_assumptions(&dispatch.assumptions);
        if actual_assumption_digest != self.assumption_digest {
            return Err(CheckError::AssumptionDigestMismatch {
                expected: self.assumption_digest.clone(),
                actual: actual_assumption_digest,
            });
        }

        Ok(())
    }
}

impl SolverProofExportMetadata {
    pub fn sha256(&self) -> Result<String, CheckError> {
        self.validate_structure()?;
        let bytes = serde_json::to_vec(self)
            .map_err(|err| CheckError::CheckerInternalError { reason: err.to_string() })?;
        Ok(stable_sha256_hex(&bytes))
    }

    pub fn validate_structure(&self) -> Result<(), CheckError> {
        if self.dispatch_id.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "solver proof export metadata is missing dispatch id".to_string(),
            });
        }
        if self.solver.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "solver proof export metadata is missing solver id".to_string(),
            });
        }
        if self.format.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "solver proof export metadata is missing proof format".to_string(),
            });
        }
        if self.proof_byte_len == 0 {
            return Err(CheckError::MalformedProof {
                reason: "solver proof export metadata has empty proof payload length".to_string(),
            });
        }
        validate_canonical_sha256_hex("solver proof export metadata vc_sha256", &self.vc_sha256)?;
        validate_canonical_sha256_hex(
            "solver proof export metadata proof_sha256",
            &self.proof_sha256,
        )?;
        validate_canonical_sha256_hex(
            "solver proof export metadata assumption_digest",
            &self.assumption_digest,
        )?;
        if let Some(stdout_digest) = self.stdout_digest.as_deref() {
            validate_canonical_sha256_hex(
                "solver proof export metadata stdout_digest",
                stdout_digest,
            )?;
        }
        if let Some(stderr_digest) = self.stderr_digest.as_deref() {
            validate_canonical_sha256_hex(
                "solver proof export metadata stderr_digest",
                stderr_digest,
            )?;
        }

        Ok(())
    }
}

/// Production checker request for one binary-derived VC.
#[derive(Debug, Clone, Copy)]
pub struct BinaryCertificateCheckRequest<'a> {
    pub dispatch: &'a SolverDispatchRecord,
    pub canonical_vc_bytes: &'a [u8],
    pub vc_sha256: &'a str,
    pub export: &'a SolverProofExport,
    pub expected_query_semantics: SolverQuerySemantics,
    pub model_assumptions: &'a [ModelAssumption],
    pub assumption_digest: &'a str,
    pub replay_transcript_digest: Option<&'a str>,
}

impl<'a> BinaryCertificateCheckRequest<'a> {
    #[must_use]
    pub fn from_export(
        dispatch: &'a SolverDispatchRecord,
        canonical_vc_bytes: &'a [u8],
        export: &'a SolverProofExport,
    ) -> Self {
        Self {
            dispatch,
            canonical_vc_bytes,
            vc_sha256: &export.vc_sha256,
            export,
            expected_query_semantics: SolverQuerySemantics::SatIsCounterexample,
            model_assumptions: &dispatch.assumptions,
            assumption_digest: &export.assumption_digest,
            replay_transcript_digest: None,
        }
    }
}

/// Checker-normalized certificate artifact.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateArtifact {
    pub dispatch_id: String,
    pub vc_sha256: String,
    pub origin_sha256: String,
    pub proof_sha256: String,
    #[serde(default)]
    pub proof_export_sha256: String,
    pub certificate_sha256: String,
    pub format: ProofFormat,
    pub checker: CheckerId,
    pub checker_version: String,
    pub query_semantics: SolverQuerySemantics,
    pub replay: ReplayStatus,
    #[serde(default)]
    pub replay_transcript_digest: Option<String>,
    pub origin: BinaryOrigin,
    #[serde(default)]
    pub binary_artifact_digest_identity: BinaryArtifactDigestIdentity,
    pub normalized_payload: Vec<u8>,
    pub dependencies: Vec<String>,
    pub assumption_digest: String,
    pub assumptions: Vec<ModelAssumption>,
    pub checked_at_unix_ms: u64,
    pub diagnostics: Vec<String>,
}

/// Filesystem reference for a content-addressed checked binary certificate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateArtifactRef {
    pub content_sha256: String,
    pub path: PathBuf,
}

/// Filesystem references for a content-addressed normalized solver proof export.
///
/// The metadata path is keyed by the normalized proof-export metadata digest.
/// The payload path is keyed by the proof payload digest. Audit manifests only
/// carry these digests; this side artifact exists so a production checker can
/// inspect the normalized proof export during certificate production.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SolverProofExportArtifactRef {
    pub metadata_sha256: String,
    pub metadata_path: PathBuf,
    pub proof_sha256: String,
    pub proof_path: PathBuf,
}

/// Checked production evidence for one binary-derived VC.
///
/// This is the per-VC payload a proof-grade certificate manifest must carry.
/// It is derived from a validated checked artifact rather than from a
/// `ProofCertificateStatus::Checked` marker.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateProductionEvidence {
    pub dispatch_id: String,
    pub vc_sha256: String,
    pub query_semantics: SolverQuerySemantics,
    pub certificate_sha256: String,
    pub proof_sha256: String,
    #[serde(default)]
    pub proof_export_sha256: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub production_checker_evidence_sha256: Option<String>,
    pub checker: CheckerId,
    pub checker_version: String,
    pub format: ProofFormat,
    pub origin_sha256: String,
    #[serde(default)]
    pub replay: ReplayStatus,
    #[serde(default)]
    pub replay_transcript_digest: Option<String>,
    #[serde(default)]
    pub binary_artifact_digest_identity: BinaryArtifactDigestIdentity,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub source_backpropagation_gate_sha256: String,
    pub assumption_digest: String,
    pub checked_at_unix_ms: u64,
}

/// Real accepted manifest-row identity carried by proof-grade production manifests.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateProductionManifestRowAcceptance {
    pub manifest_identity_sha256: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub production_checker_evidence_sha256: String,
    pub vc_sha256: String,
    pub certificate_sha256: String,
    pub proof_metadata_sha256: String,
    pub replay: ReplayStatus,
    #[serde(default)]
    pub replay_transcript_digest: Option<String>,
    #[serde(default)]
    pub binary_artifact_digest_identity: BinaryArtifactDigestIdentity,
    pub source_backpropagation_gate_sha256: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source_backpropagation_gate_row:
        Option<CheckedBinaryCertificateProductionSourceBackpropagationGateRow>,
}

/// Schema-versioned source gate row carried by strict production manifest rows.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateProductionSourceBackpropagationGateRow {
    pub schema_version: String,
    pub manifest_identity_sha256: String,
    pub source_backpropagation_gate_sha256: String,
    pub vc_sha256: String,
    pub certificate_sha256: String,
    pub certificate_path: PathBuf,
    pub origin_sha256: String,
    pub assumption_digest: String,
    pub replay: ReplayStatus,
    #[serde(default)]
    pub replay_transcript_digest: Option<String>,
    pub selected_image_identity: BinarySelectedImageIdentity,
    pub source_backpropagation_gate: CheckedBinaryCertificateSourceBackpropagationGate,
}

/// One required VC entry in a checked binary certificate production manifest.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateProductionManifestEntry {
    pub dispatch_id: String,
    pub vc_sha256: String,
    #[serde(default)]
    pub origin_sha256: String,
    #[serde(default)]
    pub proof_sha256: String,
    #[serde(default)]
    pub proof_export_sha256: String,
    pub query_semantics: SolverQuerySemantics,
    pub certificate_sha256: String,
    #[serde(default)]
    pub replay: ReplayStatus,
    #[serde(default)]
    pub replay_transcript_digest: Option<String>,
    #[serde(default)]
    pub binary_artifact_digest_identity: BinaryArtifactDigestIdentity,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub source_backpropagation_gate_sha256: String,
    #[serde(default)]
    pub assumption_digest: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub manifest_row_acceptance: Option<CheckedBinaryCertificateProductionManifestRowAcceptance>,
    pub production_evidence: Option<CheckedBinaryCertificateProductionEvidence>,
}

/// Proof-grade manifest for checked binary certificate production.
///
/// Acceptance requires one entry per required VC, and every entry must carry
/// production evidence whose VC, origin, proof, replay, assumption, query, and
/// certificate identities match the manifest entry.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateProductionManifest {
    pub schema_version: String,
    pub required_vcs: usize,
    #[serde(default, skip_serializing_if = "is_false")]
    pub require_manifest_row_acceptance: bool,
    pub entries: Vec<CheckedBinaryCertificateProductionManifestEntry>,
}

/// Input used to build an audit-only production manifest from validated checked artifacts.
///
/// Proof-grade production evaluation requires accepted manifest-row evidence so
/// that the checker invocation, proof export metadata, replay transcript, and
/// source-backpropagation gate state are bound together.
#[derive(Debug, Clone, Copy)]
pub struct CheckedBinaryCertificateProductionManifestInput<'a> {
    pub dispatch: &'a SolverDispatchRecord,
    pub canonical_vc_bytes: &'a [u8],
    pub artifact: &'a CheckedBinaryCertificateArtifact,
}

/// Input used to build a production manifest from accepted manifest rows.
#[derive(Debug, Clone, Copy)]
pub struct CheckedBinaryCertificateProductionManifestAcceptedRowInput<'a> {
    pub manifest_entry: &'a CheckedBinaryCertificateManifestEntry,
    pub acceptance_record: &'a CheckedBinaryCertificateManifestAcceptanceRecord,
}

/// Fail-closed validation result for a checked binary certificate production manifest.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateProductionManifestDecision {
    pub accepted: bool,
    pub rejections: Vec<CheckedBinaryCertificateProductionManifestRejection>,
}

/// Stable reasons a checked binary certificate production manifest cannot be accepted.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum CheckedBinaryCertificateProductionManifestRejection {
    SchemaVersionMismatch {
        expected: String,
        actual: String,
    },
    RequiredVcCoverageIncomplete {
        required_vcs: usize,
        entries: usize,
    },
    MissingProductionEvidence {
        dispatch_id: String,
    },
    MissingManifestRowAcceptance {
        dispatch_id: String,
    },
    MissingSourceBackpropagationGateRow {
        dispatch_id: String,
    },
    ProductionEvidenceMismatch {
        dispatch_id: String,
        field: String,
        expected: String,
        actual: String,
    },
    DuplicateVcProductionEvidence {
        vc_sha256: String,
        first_dispatch_id: String,
        duplicate_dispatch_id: String,
    },
    DuplicateCertificateProductionEvidence {
        certificate_sha256: String,
        first_dispatch_id: String,
        duplicate_dispatch_id: String,
    },
}

/// Deterministic manifest of checked binary certificates for production gates.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateManifest {
    pub schema_version: String,
    pub certificates: Vec<CheckedBinaryCertificateManifestEntry>,
}

/// One checked binary certificate entry in a production manifest.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateManifestEntry {
    pub dispatch_id: String,
    pub vc_sha256: String,
    #[serde(default)]
    pub origin_sha256: String,
    #[serde(default)]
    pub proof_sha256: String,
    #[serde(default)]
    pub proof_export_sha256: String,
    pub certificate_sha256: String,
    pub certificate_path: PathBuf,
    pub format: ProofFormat,
    pub checker: CheckerId,
    pub checker_version: String,
    pub replay: ReplayStatus,
    #[serde(default)]
    pub replay_transcript_digest: Option<String>,
    #[serde(default)]
    pub binary_artifact_digest_identity: BinaryArtifactDigestIdentity,
    pub assumption_digest: String,
}

/// Explicit checker selected for accepting a checked binary certificate row.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateCheckerSelection {
    pub checker: CheckerId,
    pub checker_version: String,
    pub format: ProofFormat,
}

/// Source class for checker evidence attached to a manifest acceptance.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CheckedBinaryCertificateCheckerEvidenceKind {
    Production,
    Synthetic,
    ReadbackOnly,
}

/// Invocation source for checker evidence attached to a manifest acceptance.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CheckedBinaryCertificateCheckerInvocationKind {
    ExternalProcess,
    SyntheticFixture,
    ReadbackOnly,
}

/// Structured transcript identity for an externally executed production checker.
///
/// The helper stores stdout/stderr by digest only. The raw transcripts stay in
/// the caller's audit bundle, while `sha256()` binds command, argv, exit status,
/// and transcript digests into the production evidence invocation digest.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateExternalProcessTranscript {
    pub command: String,
    pub argv: Vec<String>,
    #[serde(default)]
    pub cwd: Option<PathBuf>,
    #[serde(default)]
    pub env: BTreeMap<String, String>,
    #[serde(default)]
    pub proof_artifact_args: Vec<CheckedBinaryCertificateExternalProcessProofArtifactArgument>,
    #[serde(default)]
    pub timeout_policy: Option<CheckedBinaryCertificateExternalCheckerTimeoutPolicy>,
    #[serde(default)]
    pub timed_out: bool,
    pub exit_status: i32,
    #[serde(default)]
    pub stdout_sha256: Option<String>,
    #[serde(default)]
    pub stderr_sha256: Option<String>,
}

/// Explicit timeout policy for a production checker subprocess.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateExternalCheckerTimeoutPolicy {
    pub timeout_ms: u64,
}

/// Structured proof/certificate artifact identity referenced by checker argv.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateExternalProcessProofArtifactArgument {
    pub role: String,
    #[serde(default)]
    pub argv_index: Option<usize>,
    pub value: String,
    #[serde(default)]
    pub sha256: Option<String>,
}

/// Minimal deterministic subprocess runner for production checker evidence.
///
/// The runner does not accept solver output as certificate evidence. It only
/// executes the configured checker with null stdin and a cleared environment,
/// hashes stdout/stderr as streams, and then delegates production acceptance to
/// [`CheckedBinaryCertificateProductionCheckerEvidence::external_process_for_manifest_entry`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedBinaryCertificateExternalCheckerRunner {
    command: PathBuf,
    args: Vec<String>,
    cwd: Option<PathBuf>,
    env: BTreeMap<String, String>,
    proof_artifact_args: Vec<CheckedBinaryCertificateExternalProcessProofArtifactArgument>,
    timeout_policy: Option<CheckedBinaryCertificateExternalCheckerTimeoutPolicy>,
    checker_binary_sha256: String,
    checker_config_sha256: Option<String>,
    checked_at_unix_ms: u64,
}

/// Evidence that a production checker, not a synthetic/readback row, accepted the proof.
///
/// This deliberately binds the selected checker, checker binary/config digests,
/// invocation transcript, solver proof export, and checked artifact identity.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateProductionCheckerEvidence {
    pub kind: CheckedBinaryCertificateCheckerEvidenceKind,
    pub invocation_kind: CheckedBinaryCertificateCheckerInvocationKind,
    pub checker: CheckerId,
    pub checker_version: String,
    pub format: ProofFormat,
    pub checker_binary_sha256: String,
    #[serde(default)]
    pub checker_config_sha256: Option<String>,
    pub invocation_sha256: String,
    #[serde(default)]
    pub stdout_sha256: Option<String>,
    #[serde(default)]
    pub stderr_sha256: Option<String>,
    #[serde(default)]
    pub external_process_transcript: Option<CheckedBinaryCertificateExternalProcessTranscript>,
    pub proof_export_sha256: String,
    pub certificate_sha256: String,
    pub checked_at_unix_ms: u64,
}

/// Normalized solver proof export metadata required for manifest acceptance.
///
/// This intentionally stores [`SolverProofExportMetadata`] rather than raw
/// solver proof bytes. The production acceptance path binds the metadata digest
/// to the manifest row and checked artifact without accepting solver output as
/// certificate evidence.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateSolverProofExportBinding {
    pub metadata: SolverProofExportMetadata,
    pub metadata_sha256: String,
}

/// Replay status and optional transcript digest bound to the checked row.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateReplayTranscriptBinding {
    pub replay: ReplayStatus,
    #[serde(default)]
    pub replay_transcript_digest: Option<String>,
}

/// Stable identity for the content-addressed checked certificate artifact.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateArtifactIdentity {
    pub dispatch_id: String,
    pub vc_sha256: String,
    pub origin_sha256: String,
    pub proof_sha256: String,
    pub proof_export_sha256: String,
    pub certificate_sha256: String,
    pub content_sha256: String,
    pub certificate_path: PathBuf,
    #[serde(default)]
    pub binary_artifact_digest_identity: BinaryArtifactDigestIdentity,
}

/// Dispatch-local proof that checked status came from an accepted manifest row.
///
/// This is written into [`SolverDispatchRecord::diagnostics`] by
/// [`import_checked_certificate_manifest_entry_for_dispatch`]. The proof-grade
/// binary gate treats checked status without this manifest identity as
/// checked-certificate-shaped metadata, not per-VC checked coverage.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateManifestIdentityEntry {
    pub schema_version: String,
    pub manifest_schema_version: String,
    pub checker_selection: CheckedBinaryCertificateCheckerSelection,
    pub replay_transcript: CheckedBinaryCertificateReplayTranscriptBinding,
    pub artifact_identity: CheckedBinaryCertificateArtifactIdentity,
    pub production_checker_evidence_sha256: String,
    #[serde(
        default,
        skip_serializing_if = "CheckedBinaryCertificateSourceBackpropagationGate::is_closed_default"
    )]
    pub source_backpropagation_gate: CheckedBinaryCertificateSourceBackpropagationGate,
}

/// Structured production bindings required to accept a manifest row.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateManifestAcceptanceRequest {
    pub schema_version: String,
    pub checker_selection: CheckedBinaryCertificateCheckerSelection,
    #[serde(default)]
    pub production_checker_evidence: Option<CheckedBinaryCertificateProductionCheckerEvidence>,
    pub solver_proof_export: CheckedBinaryCertificateSolverProofExportBinding,
    pub replay_transcript: CheckedBinaryCertificateReplayTranscriptBinding,
    pub artifact_identity: CheckedBinaryCertificateArtifactIdentity,
    #[serde(
        default,
        skip_serializing_if = "CheckedBinaryCertificateSourceBackpropagationGate::is_closed_default"
    )]
    pub source_backpropagation_gate: CheckedBinaryCertificateSourceBackpropagationGate,
}

/// Stable record emitted after a checked artifact/manifest row is accepted.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateManifestAcceptanceRecord {
    pub schema_version: String,
    pub manifest_schema_version: String,
    pub checker_selection: CheckedBinaryCertificateCheckerSelection,
    #[serde(default)]
    pub production_checker_evidence: Option<CheckedBinaryCertificateProductionCheckerEvidence>,
    pub solver_proof_export: CheckedBinaryCertificateSolverProofExportBinding,
    pub replay_transcript: CheckedBinaryCertificateReplayTranscriptBinding,
    pub artifact_identity: CheckedBinaryCertificateArtifactIdentity,
    #[serde(
        default,
        skip_serializing_if = "CheckedBinaryCertificateSourceBackpropagationGate::is_closed_default"
    )]
    pub source_backpropagation_gate: CheckedBinaryCertificateSourceBackpropagationGate,
}

/// Loaded artifact plus the stable acceptance record that justified import.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedBinaryCertificateManifestAcceptance {
    pub record: CheckedBinaryCertificateManifestAcceptanceRecord,
    pub artifact: CheckedBinaryCertificateArtifact,
}

/// Persisted audit view of an accepted checked-certificate manifest row.
///
/// This is intentionally metadata-only: it stores the manifest row identity and
/// the normalized proof export binding, not raw solver proof bytes.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateAuditExport {
    pub schema_version: String,
    pub manifest_entry: CheckedBinaryCertificateManifestEntry,
    pub acceptance_record: CheckedBinaryCertificateManifestAcceptanceRecord,
}

/// Durable metadata-only bundle for manifest/audit export readback.
///
/// Paths are always relative to the caller-supplied artifact root. The bundle
/// binds the manifest file digest plus each audit export file digest so
/// readback can fail closed on stale or mixed export sets before importing a
/// checked certificate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateAuditExportBundle {
    pub schema_version: String,
    pub manifest_path: PathBuf,
    pub manifest_sha256: String,
    pub audit_exports: Vec<CheckedBinaryCertificateAuditExportBundleEntry>,
}

/// One audit export file recorded in a checked-certificate export bundle.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateAuditExportBundleEntry {
    pub dispatch_id: String,
    pub vc_sha256: String,
    pub origin_sha256: String,
    pub proof_sha256: String,
    pub proof_export_sha256: String,
    pub certificate_sha256: String,
    pub format: ProofFormat,
    pub checker: CheckerId,
    pub checker_version: String,
    pub replay: ReplayStatus,
    #[serde(default)]
    pub replay_transcript_digest: Option<String>,
    #[serde(default)]
    pub binary_artifact_digest_identity: BinaryArtifactDigestIdentity,
    pub assumption_digest: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub manifest_identity_sha256: String,
    #[serde(
        default,
        skip_serializing_if = "CheckedBinaryCertificateSourceBackpropagationGate::is_closed_default"
    )]
    pub source_backpropagation_gate: CheckedBinaryCertificateSourceBackpropagationGate,
    pub audit_export_path: PathBuf,
    pub audit_export_sha256: String,
}

/// Source-backpropagation gate evidence carried by checked-certificate audit records.
///
/// This is deliberately fail-closed: missing fields deserialize to false/empty,
/// and `source_backpropagation_allowed` can validate only when every
/// proof-grade prerequisite is present in the same acceptance record.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateSourceBackpropagationGate {
    #[serde(default = "default_source_backpropagation_gate_schema_version")]
    pub schema_version: String,
    #[serde(default)]
    pub replay_grade_artifact_identity: bool,
    #[serde(default)]
    pub checked_certificate_identity: bool,
    #[serde(default)]
    pub exact_replay_identity: bool,
    #[serde(default)]
    pub accepted_reconstruction_validation: bool,
    #[serde(default)]
    pub accepted_target_validation: bool,
    #[serde(default)]
    pub exact_source_provenance: bool,
    #[serde(default)]
    pub source_provenance: BinarySourceProvenanceSummary,
    /// Unsupported-ledger rows that remain after explicit proof-model consumption/elimination.
    #[serde(default, skip_serializing_if = "UnsupportedLedgerSummary::is_empty")]
    pub unsupported_ledger_summary: UnsupportedLedgerSummary,
    /// Preserved `trust_symbolic.formula` payloads that require target proof-consumer evidence.
    #[serde(default, skip_serializing_if = "is_zero_usize")]
    pub preserved_symbolic_formulas: usize,
    /// True only when target proof semantics explicitly consumed preserved symbolic formulas.
    #[serde(default, skip_serializing_if = "is_false")]
    pub symbolic_formula_consumer_accepted: bool,
    #[serde(default)]
    pub source_backpropagation_allowed: bool,
    #[serde(default)]
    pub blockers: Vec<String>,
}

/// Materialized manifest plus metadata-only audit exports loaded from a bundle.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedBinaryCertificateAuditExportBundleReadback {
    pub bundle: CheckedBinaryCertificateAuditExportBundle,
    pub manifest: CheckedBinaryCertificateManifest,
    pub audit_exports: Vec<CheckedBinaryCertificateAuditExport>,
}

/// Row-oriented validation report for a persisted checked-certificate audit bundle.
///
/// Unlike [`load_checked_certificate_audit_export_bundle`], this keeps validating
/// later rows after a row-local audit export, manifest entry, or artifact binding
/// mismatch. Global bundle or manifest integrity failures still return
/// [`crate::CertError`] because no row can be trusted in those cases.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateAuditExportBundleValidation {
    pub bundle: CheckedBinaryCertificateAuditExportBundle,
    pub manifest: CheckedBinaryCertificateManifest,
    pub rows: Vec<CheckedBinaryCertificateAuditExportBundleValidationRow>,
}

/// Explicit per-VC coverage accounting for a checked-certificate audit bundle.
///
/// A row only contributes to `accepted_vcs` after the bundle entry, manifest row,
/// audit export, acceptance record, and checked artifact all validate. This lets
/// release gates reject a syntactically valid manifest/bundle that omits a
/// required VC or carries a stale row for one of the required VCs.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateAuditExportBundleCoverage {
    pub required_vcs: usize,
    pub accepted_rows: usize,
    pub accepted_vcs: usize,
    pub rejected_rows: usize,
    pub missing_vc_sha256: Vec<String>,
    pub unexpected_vc_sha256: Vec<String>,
    pub duplicate_accepted_vc_sha256: Vec<String>,
    pub complete: bool,
}

/// Accepted or rejected validation result for one audit export bundle row.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[allow(clippy::large_enum_variant)] // both variants are inherently large (full audit-bundle row data); boxing forces heap allocation on every emission
pub enum CheckedBinaryCertificateAuditExportBundleValidationRow {
    Accepted(CheckedBinaryCertificateAuditExportBundleAcceptedRow),
    Rejected(CheckedBinaryCertificateAuditExportBundleRejectedRow),
}

/// Fully validated row from a persisted audit export bundle.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateAuditExportBundleAcceptedRow {
    pub bundle_entry: CheckedBinaryCertificateAuditExportBundleEntry,
    pub manifest_entry: CheckedBinaryCertificateManifestEntry,
    pub audit_export: CheckedBinaryCertificateAuditExport,
    pub acceptance_record: CheckedBinaryCertificateManifestAcceptanceRecord,
    pub artifact: CheckedBinaryCertificateArtifact,
}

/// Machine-readable rejected row from a persisted audit export bundle.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckedBinaryCertificateAuditExportBundleRejectedRow {
    pub dispatch_id: String,
    pub vc_sha256: String,
    pub certificate_sha256: String,
    pub code: CheckedBinaryCertificateAuditExportBundleRejectionCode,
    pub reason: String,
    pub bundle_entry: CheckedBinaryCertificateAuditExportBundleEntry,
    pub manifest_entry: Option<CheckedBinaryCertificateManifestEntry>,
    pub audit_export: Option<CheckedBinaryCertificateAuditExport>,
}

/// Stable rejection code for a row in a persisted audit export bundle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum CheckedBinaryCertificateAuditExportBundleRejectionCode {
    #[serde(rename = "manifest_row_missing")]
    ManifestRowMissing,
    #[serde(rename = "manifest_row_mismatch")]
    ManifestRowMismatch,
    #[serde(rename = "audit_export_unreadable")]
    AuditExportUnreadable,
    #[serde(rename = "audit_export_digest_mismatch")]
    AuditExportDigestMismatch,
    #[serde(rename = "audit_export_malformed")]
    AuditExportMalformed,
    #[serde(rename = "proof_export_mismatch")]
    ProofExportMismatch,
    #[serde(rename = "checker_mismatch")]
    CheckerMismatch,
    #[serde(rename = "replay_mismatch")]
    ReplayMismatch,
    #[serde(rename = "assumption_mismatch")]
    AssumptionMismatch,
    #[serde(rename = "vc_digest_mismatch")]
    VcDigestMismatch,
    #[serde(rename = "artifact_unreadable")]
    ArtifactUnreadable,
    #[serde(rename = "artifact_mismatch")]
    ArtifactMismatch,
    #[serde(rename = "validation_failed")]
    ValidationFailed,
}

impl AsRef<Path> for CheckedBinaryCertificateArtifactRef {
    fn as_ref(&self) -> &Path {
        &self.path
    }
}

impl CheckedBinaryCertificateProductionEvidence {
    pub fn from_checked_artifact(
        artifact: &CheckedBinaryCertificateArtifact,
    ) -> Result<Self, CheckError> {
        artifact.validate_integrity()?;
        let default_source_backpropagation_gate_sha256 =
            source_backpropagation_gate_identity_sha256(
                &CheckedBinaryCertificateSourceBackpropagationGate::default(),
            )?;
        Ok(Self {
            dispatch_id: artifact.dispatch_id.clone(),
            vc_sha256: artifact.vc_sha256.clone(),
            query_semantics: artifact.query_semantics,
            certificate_sha256: artifact.certificate_sha256.clone(),
            proof_sha256: artifact.proof_sha256.clone(),
            proof_export_sha256: artifact.proof_export_sha256.clone(),
            production_checker_evidence_sha256: None,
            checker: artifact.checker.clone(),
            checker_version: artifact.checker_version.clone(),
            format: artifact.format.clone(),
            origin_sha256: artifact.origin_sha256.clone(),
            replay: artifact.replay,
            replay_transcript_digest: artifact.replay_transcript_digest.clone(),
            binary_artifact_digest_identity: artifact.binary_artifact_digest_identity.clone(),
            source_backpropagation_gate_sha256: default_source_backpropagation_gate_sha256,
            assumption_digest: artifact.assumption_digest.clone(),
            checked_at_unix_ms: artifact.checked_at_unix_ms,
        })
    }

    pub fn from_manifest_entry_and_acceptance_record(
        entry: &CheckedBinaryCertificateManifestEntry,
        record: &CheckedBinaryCertificateManifestAcceptanceRecord,
    ) -> Result<Self, CheckError> {
        record.validate_manifest_entry(entry)?;
        let production_checker_evidence = record
            .production_checker_evidence
            .as_ref()
            .ok_or(CheckError::MissingProductionCheckerEvidence)?;
        Ok(Self {
            dispatch_id: entry.dispatch_id.clone(),
            vc_sha256: entry.vc_sha256.clone(),
            query_semantics: record.solver_proof_export.metadata.query_semantics,
            certificate_sha256: entry.certificate_sha256.clone(),
            proof_sha256: entry.proof_sha256.clone(),
            proof_export_sha256: record.solver_proof_export.metadata_sha256.clone(),
            production_checker_evidence_sha256: Some(production_checker_evidence.sha256()?),
            checker: record.checker_selection.checker.clone(),
            checker_version: record.checker_selection.checker_version.clone(),
            format: record.checker_selection.format.clone(),
            origin_sha256: entry.origin_sha256.clone(),
            replay: record.replay_transcript.replay,
            replay_transcript_digest: record.replay_transcript.replay_transcript_digest.clone(),
            binary_artifact_digest_identity: record
                .artifact_identity
                .binary_artifact_digest_identity
                .clone(),
            source_backpropagation_gate_sha256: source_backpropagation_gate_identity_sha256(
                &record.source_backpropagation_gate,
            )?,
            assumption_digest: entry.assumption_digest.clone(),
            checked_at_unix_ms: production_checker_evidence.checked_at_unix_ms,
        })
    }
}

impl CheckedBinaryCertificateProductionSourceBackpropagationGateRow {
    pub fn from_manifest_entry_and_acceptance_record(
        entry: &CheckedBinaryCertificateManifestEntry,
        record: &CheckedBinaryCertificateManifestAcceptanceRecord,
    ) -> Result<Self, CheckError> {
        record.validate_manifest_entry(entry)?;
        let manifest_identity =
            CheckedBinaryCertificateManifestIdentityEntry::from_acceptance_record(record)?;
        let selected_image_identity = record
            .artifact_identity
            .binary_artifact_digest_identity
            .selected_image
            .clone()
            .ok_or_else(|| CheckError::BinaryArtifactDigestIdentityInvalid {
                reason: "missing selected image identity for source-backpropagation gate row"
                    .to_string(),
            })?;
        let row = Self {
            schema_version:
                CHECKED_BINARY_CERTIFICATE_SOURCE_BACKPROPAGATION_GATE_ROW_SCHEMA_VERSION
                    .to_string(),
            manifest_identity_sha256: manifest_identity.sha256()?,
            source_backpropagation_gate_sha256: source_backpropagation_gate_identity_sha256(
                &record.source_backpropagation_gate,
            )?,
            vc_sha256: entry.vc_sha256.clone(),
            certificate_sha256: entry.certificate_sha256.clone(),
            certificate_path: record.artifact_identity.certificate_path.clone(),
            origin_sha256: entry.origin_sha256.clone(),
            assumption_digest: entry.assumption_digest.clone(),
            replay: record.replay_transcript.replay,
            replay_transcript_digest: record.replay_transcript.replay_transcript_digest.clone(),
            selected_image_identity,
            source_backpropagation_gate: record.source_backpropagation_gate.clone(),
        };
        row.validate_structure()?;
        Ok(row)
    }

    pub fn validate_structure(&self) -> Result<(), CheckError> {
        if self.schema_version
            != CHECKED_BINARY_CERTIFICATE_SOURCE_BACKPROPAGATION_GATE_ROW_SCHEMA_VERSION
        {
            return Err(binding_mismatch(
                "source_backpropagation_gate_row.schema_version",
                CHECKED_BINARY_CERTIFICATE_SOURCE_BACKPROPAGATION_GATE_ROW_SCHEMA_VERSION,
                self.schema_version.as_str(),
            ));
        }
        validate_canonical_sha256_hex(
            "source_backpropagation_gate_row.manifest_identity_sha256",
            &self.manifest_identity_sha256,
        )?;
        validate_canonical_sha256_hex(
            "source_backpropagation_gate_row.source_backpropagation_gate_sha256",
            &self.source_backpropagation_gate_sha256,
        )?;
        validate_canonical_sha256_hex(
            "source_backpropagation_gate_row.vc_sha256",
            &self.vc_sha256,
        )?;
        validate_canonical_sha256_hex(
            "source_backpropagation_gate_row.certificate_sha256",
            &self.certificate_sha256,
        )?;
        validate_relative_manifest_path(
            "source_backpropagation_gate_row.certificate_path",
            &self.certificate_path,
        )?;
        validate_manifest_certificate_path_matches_digest(
            "source_backpropagation_gate_row.certificate_path",
            &self.certificate_path,
            &self.certificate_sha256,
        )?;
        validate_canonical_sha256_hex(
            "source_backpropagation_gate_row.origin_sha256",
            &self.origin_sha256,
        )?;
        validate_canonical_sha256_hex(
            "source_backpropagation_gate_row.assumption_digest",
            &self.assumption_digest,
        )?;
        if let Some(replay_transcript_digest) = self.replay_transcript_digest.as_deref() {
            validate_canonical_sha256_hex(
                "source_backpropagation_gate_row.replay_transcript_digest",
                replay_transcript_digest,
            )?;
        }
        validate_selected_image_identity(&self.selected_image_identity)?;
        let computed_gate_sha256 =
            source_backpropagation_gate_identity_sha256(&self.source_backpropagation_gate)?;
        if self.source_backpropagation_gate_sha256 != computed_gate_sha256 {
            return Err(binding_mismatch(
                "source_backpropagation_gate_row.source_backpropagation_gate_sha256",
                computed_gate_sha256,
                self.source_backpropagation_gate_sha256.as_str(),
            ));
        }

        Ok(())
    }
}

impl CheckedBinaryCertificateProductionManifestRowAcceptance {
    pub fn from_manifest_entry_and_acceptance_record(
        entry: &CheckedBinaryCertificateManifestEntry,
        record: &CheckedBinaryCertificateManifestAcceptanceRecord,
    ) -> Result<Self, CheckError> {
        record.validate_manifest_entry(entry)?;
        let identity =
            CheckedBinaryCertificateManifestIdentityEntry::from_acceptance_record(record)?;
        let production_checker_evidence = record
            .production_checker_evidence
            .as_ref()
            .ok_or(CheckError::MissingProductionCheckerEvidence)?;
        let source_backpropagation_gate_row =
            CheckedBinaryCertificateProductionSourceBackpropagationGateRow::from_manifest_entry_and_acceptance_record(
                entry,
                record,
            )?;
        Ok(Self {
            manifest_identity_sha256: identity.sha256()?,
            production_checker_evidence_sha256: production_checker_evidence.sha256()?,
            vc_sha256: entry.vc_sha256.clone(),
            certificate_sha256: entry.certificate_sha256.clone(),
            proof_metadata_sha256: record.solver_proof_export.metadata_sha256.clone(),
            replay: record.replay_transcript.replay,
            replay_transcript_digest: record.replay_transcript.replay_transcript_digest.clone(),
            binary_artifact_digest_identity: record
                .artifact_identity
                .binary_artifact_digest_identity
                .clone(),
            source_backpropagation_gate_sha256: source_backpropagation_gate_identity_sha256(
                &record.source_backpropagation_gate,
            )?,
            source_backpropagation_gate_row: Some(source_backpropagation_gate_row),
        })
    }

    pub fn validate_structure(&self) -> Result<(), CheckError> {
        validate_canonical_sha256_hex(
            "manifest row acceptance manifest_identity_sha256",
            &self.manifest_identity_sha256,
        )?;
        validate_canonical_sha256_hex(
            "manifest row acceptance production_checker_evidence_sha256",
            &self.production_checker_evidence_sha256,
        )?;
        validate_canonical_sha256_hex("manifest row acceptance vc_sha256", &self.vc_sha256)?;
        validate_canonical_sha256_hex(
            "manifest row acceptance certificate_sha256",
            &self.certificate_sha256,
        )?;
        validate_canonical_sha256_hex(
            "manifest row acceptance proof_metadata_sha256",
            &self.proof_metadata_sha256,
        )?;
        if let Some(replay_transcript_digest) = self.replay_transcript_digest.as_deref() {
            validate_canonical_sha256_hex(
                "manifest row acceptance replay_transcript_digest",
                replay_transcript_digest,
            )?;
        }
        validate_binary_artifact_digest_identity(&self.binary_artifact_digest_identity)?;
        validate_canonical_sha256_hex(
            "manifest row acceptance source_backpropagation_gate_sha256",
            &self.source_backpropagation_gate_sha256,
        )?;
        if let Some(source_backpropagation_gate_row) = &self.source_backpropagation_gate_row {
            source_backpropagation_gate_row.validate_structure()?;
        }

        Ok(())
    }
}

impl CheckedBinaryCertificateProductionManifest {
    pub fn from_checked_artifacts(
        required_vcs: usize,
        inputs: &[CheckedBinaryCertificateProductionManifestInput<'_>],
    ) -> Result<Self, CheckError> {
        let mut entries = Vec::with_capacity(inputs.len());

        for input in inputs {
            if dispatch_has_raw_solver_proof_bytes(input.dispatch) {
                return Err(CheckError::RawSolverBytesCannotUpgradeToChecked {
                    dispatch_id: input.dispatch.id.clone(),
                });
            }
            input.artifact.validate_for_dispatch(input.dispatch, input.canonical_vc_bytes)?;
            let production_evidence =
                CheckedBinaryCertificateProductionEvidence::from_checked_artifact(input.artifact)?;
            entries.push(CheckedBinaryCertificateProductionManifestEntry {
                dispatch_id: input.dispatch.id.clone(),
                vc_sha256: stable_sha256_hex(input.canonical_vc_bytes),
                origin_sha256: input.artifact.origin_sha256.clone(),
                proof_sha256: input.artifact.proof_sha256.clone(),
                proof_export_sha256: input.artifact.proof_export_sha256.clone(),
                query_semantics: input.dispatch.query_semantics,
                certificate_sha256: input.artifact.certificate_sha256.clone(),
                replay: input.artifact.replay,
                replay_transcript_digest: input.artifact.replay_transcript_digest.clone(),
                binary_artifact_digest_identity: input
                    .artifact
                    .binary_artifact_digest_identity
                    .clone(),
                source_backpropagation_gate_sha256: production_evidence
                    .source_backpropagation_gate_sha256
                    .clone(),
                assumption_digest: input.artifact.assumption_digest.clone(),
                manifest_row_acceptance: None,
                production_evidence: Some(production_evidence),
            });
        }

        Ok(Self {
            schema_version: CHECKED_BINARY_CERTIFICATE_PRODUCTION_MANIFEST_SCHEMA_VERSION
                .to_string(),
            required_vcs,
            require_manifest_row_acceptance: false,
            entries,
        })
    }

    pub fn from_manifest_acceptance_records(
        required_vcs: usize,
        inputs: &[CheckedBinaryCertificateProductionManifestAcceptedRowInput<'_>],
    ) -> Result<Self, CheckError> {
        let mut entries = Vec::with_capacity(inputs.len());

        for input in inputs {
            let production_evidence =
                CheckedBinaryCertificateProductionEvidence::from_manifest_entry_and_acceptance_record(
                    input.manifest_entry,
                    input.acceptance_record,
                )?;
            let manifest_row_acceptance =
                CheckedBinaryCertificateProductionManifestRowAcceptance::from_manifest_entry_and_acceptance_record(
                    input.manifest_entry,
                    input.acceptance_record,
                )?;
            entries.push(CheckedBinaryCertificateProductionManifestEntry {
                dispatch_id: input.manifest_entry.dispatch_id.clone(),
                vc_sha256: input.manifest_entry.vc_sha256.clone(),
                origin_sha256: input.manifest_entry.origin_sha256.clone(),
                proof_sha256: input.manifest_entry.proof_sha256.clone(),
                proof_export_sha256: input.manifest_entry.proof_export_sha256.clone(),
                query_semantics: input
                    .acceptance_record
                    .solver_proof_export
                    .metadata
                    .query_semantics,
                certificate_sha256: input.manifest_entry.certificate_sha256.clone(),
                replay: input.acceptance_record.replay_transcript.replay,
                replay_transcript_digest: input
                    .acceptance_record
                    .replay_transcript
                    .replay_transcript_digest
                    .clone(),
                binary_artifact_digest_identity: input
                    .acceptance_record
                    .artifact_identity
                    .binary_artifact_digest_identity
                    .clone(),
                source_backpropagation_gate_sha256: production_evidence
                    .source_backpropagation_gate_sha256
                    .clone(),
                assumption_digest: input.manifest_entry.assumption_digest.clone(),
                manifest_row_acceptance: Some(manifest_row_acceptance),
                production_evidence: Some(production_evidence),
            });
        }

        Ok(Self {
            schema_version: CHECKED_BINARY_CERTIFICATE_PRODUCTION_MANIFEST_SCHEMA_VERSION
                .to_string(),
            required_vcs,
            require_manifest_row_acceptance: true,
            entries,
        })
    }

    #[must_use]
    pub fn evaluate(&self) -> CheckedBinaryCertificateProductionManifestDecision {
        evaluate_checked_binary_certificate_production_manifest(self)
    }
}

#[must_use]
pub fn evaluate_checked_binary_certificate_production_manifest(
    manifest: &CheckedBinaryCertificateProductionManifest,
) -> CheckedBinaryCertificateProductionManifestDecision {
    let mut rejections = Vec::new();

    if manifest.schema_version != CHECKED_BINARY_CERTIFICATE_PRODUCTION_MANIFEST_SCHEMA_VERSION {
        rejections.push(
            CheckedBinaryCertificateProductionManifestRejection::SchemaVersionMismatch {
                expected: CHECKED_BINARY_CERTIFICATE_PRODUCTION_MANIFEST_SCHEMA_VERSION.to_string(),
                actual: manifest.schema_version.clone(),
            },
        );
    }

    if manifest.entries.len() != manifest.required_vcs {
        rejections.push(
            CheckedBinaryCertificateProductionManifestRejection::RequiredVcCoverageIncomplete {
                required_vcs: manifest.required_vcs,
                entries: manifest.entries.len(),
            },
        );
    }

    if !manifest.require_manifest_row_acceptance {
        rejections.push(
            CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                dispatch_id: "<manifest>".to_string(),
                field: "require_manifest_row_acceptance".to_string(),
                expected: "true".to_string(),
                actual: "false".to_string(),
            },
        );
    }

    let mut seen_vcs = BTreeMap::<String, String>::new();
    let mut seen_certificates = BTreeMap::<String, String>::new();

    for entry in &manifest.entries {
        if entry.dispatch_id.trim().is_empty() {
            rejections.push(
                CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                    dispatch_id: entry.dispatch_id.clone(),
                    field: "dispatch_id".to_string(),
                    expected: "non-empty manifest identity field".to_string(),
                    actual: "empty".to_string(),
                },
            );
        }
        push_manifest_digest_mismatch(
            &mut rejections,
            entry.dispatch_id.as_str(),
            "vc_sha256",
            entry.vc_sha256.as_str(),
        );
        push_manifest_digest_mismatch(
            &mut rejections,
            entry.dispatch_id.as_str(),
            "origin_sha256",
            entry.origin_sha256.as_str(),
        );
        push_manifest_digest_mismatch(
            &mut rejections,
            entry.dispatch_id.as_str(),
            "proof_sha256",
            entry.proof_sha256.as_str(),
        );
        push_manifest_digest_mismatch(
            &mut rejections,
            entry.dispatch_id.as_str(),
            "proof_export_sha256",
            entry.proof_export_sha256.as_str(),
        );
        push_manifest_digest_mismatch(
            &mut rejections,
            entry.dispatch_id.as_str(),
            "certificate_sha256",
            entry.certificate_sha256.as_str(),
        );
        if let Some(replay_transcript_digest) = entry.replay_transcript_digest.as_deref() {
            push_manifest_digest_mismatch(
                &mut rejections,
                entry.dispatch_id.as_str(),
                "replay_transcript_digest",
                replay_transcript_digest,
            );
        }
        if let Err(err) =
            validate_binary_artifact_digest_identity(&entry.binary_artifact_digest_identity)
        {
            rejections.push(
                CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                    dispatch_id: entry.dispatch_id.clone(),
                    field: "binary_artifact_digest_identity".to_string(),
                    expected: "replay-grade binary artifact digest identity".to_string(),
                    actual: err.to_string(),
                },
            );
        }
        push_manifest_digest_mismatch(
            &mut rejections,
            entry.dispatch_id.as_str(),
            "source_backpropagation_gate_sha256",
            entry.source_backpropagation_gate_sha256.as_str(),
        );
        push_manifest_digest_mismatch(
            &mut rejections,
            entry.dispatch_id.as_str(),
            "assumption_digest",
            entry.assumption_digest.as_str(),
        );

        if entry.query_semantics != SolverQuerySemantics::SatIsCounterexample {
            rejections.push(
                CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                    dispatch_id: entry.dispatch_id.clone(),
                    field: "query_semantics".to_string(),
                    expected: format!("{:?}", SolverQuerySemantics::SatIsCounterexample),
                    actual: format!("{:?}", entry.query_semantics),
                },
            );
        }

        if let Some(first_dispatch_id) =
            seen_vcs.insert(entry.vc_sha256.clone(), entry.dispatch_id.clone())
        {
            rejections.push(
                CheckedBinaryCertificateProductionManifestRejection::DuplicateVcProductionEvidence {
                    vc_sha256: entry.vc_sha256.clone(),
                    first_dispatch_id,
                    duplicate_dispatch_id: entry.dispatch_id.clone(),
                },
            );
        }

        if let Some(first_dispatch_id) =
            seen_certificates.insert(entry.certificate_sha256.clone(), entry.dispatch_id.clone())
        {
            rejections.push(
                CheckedBinaryCertificateProductionManifestRejection::DuplicateCertificateProductionEvidence {
                    certificate_sha256: entry.certificate_sha256.clone(),
                    first_dispatch_id,
                    duplicate_dispatch_id: entry.dispatch_id.clone(),
                },
            );
        }

        let Some(evidence) = &entry.production_evidence else {
            rejections.push(
                CheckedBinaryCertificateProductionManifestRejection::MissingProductionEvidence {
                    dispatch_id: entry.dispatch_id.clone(),
                },
            );
            continue;
        };

        push_manifest_evidence_mismatch(
            &mut rejections,
            entry.dispatch_id.as_str(),
            "dispatch_id",
            entry.dispatch_id.as_str(),
            evidence.dispatch_id.as_str(),
        );
        push_manifest_evidence_mismatch(
            &mut rejections,
            entry.dispatch_id.as_str(),
            "vc_sha256",
            entry.vc_sha256.as_str(),
            evidence.vc_sha256.as_str(),
        );
        push_manifest_evidence_mismatch(
            &mut rejections,
            entry.dispatch_id.as_str(),
            "origin_sha256",
            entry.origin_sha256.as_str(),
            evidence.origin_sha256.as_str(),
        );
        push_manifest_evidence_mismatch(
            &mut rejections,
            entry.dispatch_id.as_str(),
            "proof_sha256",
            entry.proof_sha256.as_str(),
            evidence.proof_sha256.as_str(),
        );
        push_manifest_evidence_mismatch(
            &mut rejections,
            entry.dispatch_id.as_str(),
            "proof_export_sha256",
            entry.proof_export_sha256.as_str(),
            evidence.proof_export_sha256.as_str(),
        );
        push_manifest_digest_mismatch(
            &mut rejections,
            entry.dispatch_id.as_str(),
            "production_evidence.vc_sha256",
            evidence.vc_sha256.as_str(),
        );
        if evidence.query_semantics != entry.query_semantics {
            rejections.push(
                CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                    dispatch_id: entry.dispatch_id.clone(),
                    field: "query_semantics".to_string(),
                    expected: format!("{:?}", entry.query_semantics),
                    actual: format!("{:?}", evidence.query_semantics),
                },
            );
        }
        push_manifest_evidence_mismatch(
            &mut rejections,
            entry.dispatch_id.as_str(),
            "certificate_sha256",
            entry.certificate_sha256.as_str(),
            evidence.certificate_sha256.as_str(),
        );
        if evidence.replay != entry.replay {
            rejections.push(
                CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                    dispatch_id: entry.dispatch_id.clone(),
                    field: "replay".to_string(),
                    expected: format!("{:?}", entry.replay),
                    actual: format!("{:?}", evidence.replay),
                },
            );
        }
        if evidence.replay_transcript_digest != entry.replay_transcript_digest {
            rejections.push(
                CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                    dispatch_id: entry.dispatch_id.clone(),
                    field: "replay_transcript_digest".to_string(),
                    expected: entry
                        .replay_transcript_digest
                        .as_deref()
                        .unwrap_or("<missing>")
                        .to_string(),
                    actual: evidence
                        .replay_transcript_digest
                        .as_deref()
                        .unwrap_or("<missing>")
                        .to_string(),
                },
            );
        }
        if evidence.binary_artifact_digest_identity != entry.binary_artifact_digest_identity {
            let expected =
                binary_artifact_digest_identity_label(&entry.binary_artifact_digest_identity)
                    .unwrap_or_else(|err| err.to_string());
            let actual =
                binary_artifact_digest_identity_label(&evidence.binary_artifact_digest_identity)
                    .unwrap_or_else(|err| err.to_string());
            rejections.push(
                CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                    dispatch_id: entry.dispatch_id.clone(),
                    field: "binary_artifact_digest_identity".to_string(),
                    expected,
                    actual,
                },
            );
        }
        push_manifest_evidence_mismatch(
            &mut rejections,
            entry.dispatch_id.as_str(),
            "source_backpropagation_gate_sha256",
            entry.source_backpropagation_gate_sha256.as_str(),
            evidence.source_backpropagation_gate_sha256.as_str(),
        );
        push_manifest_evidence_mismatch(
            &mut rejections,
            entry.dispatch_id.as_str(),
            "assumption_digest",
            entry.assumption_digest.as_str(),
            evidence.assumption_digest.as_str(),
        );
        push_manifest_digest_mismatch(
            &mut rejections,
            entry.dispatch_id.as_str(),
            "production_evidence.certificate_sha256",
            evidence.certificate_sha256.as_str(),
        );
        push_manifest_digest_mismatch(
            &mut rejections,
            entry.dispatch_id.as_str(),
            "production_evidence.proof_export_sha256",
            evidence.proof_export_sha256.as_str(),
        );
        if let Some(replay_transcript_digest) = evidence.replay_transcript_digest.as_deref() {
            push_manifest_digest_mismatch(
                &mut rejections,
                entry.dispatch_id.as_str(),
                "production_evidence.replay_transcript_digest",
                replay_transcript_digest,
            );
        }
        match evidence.production_checker_evidence_sha256.as_deref() {
            Some(production_checker_evidence_sha256) => push_manifest_digest_mismatch(
                &mut rejections,
                entry.dispatch_id.as_str(),
                "production_evidence.production_checker_evidence_sha256",
                production_checker_evidence_sha256,
            ),
            None if entry.manifest_row_acceptance.is_none() => rejections.push(
                CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                    dispatch_id: entry.dispatch_id.clone(),
                    field: "production_evidence.production_checker_evidence_sha256".to_string(),
                    expected: "external production checker evidence digest".to_string(),
                    actual: "<missing>".to_string(),
                },
            ),
            None => {}
        }
        if let Err(err) =
            validate_binary_artifact_digest_identity(&evidence.binary_artifact_digest_identity)
        {
            rejections.push(
                CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                    dispatch_id: entry.dispatch_id.clone(),
                    field: "production_evidence.binary_artifact_digest_identity".to_string(),
                    expected: "replay-grade binary artifact digest identity".to_string(),
                    actual: err.to_string(),
                },
            );
        }
        push_manifest_digest_mismatch(
            &mut rejections,
            entry.dispatch_id.as_str(),
            "production_evidence.source_backpropagation_gate_sha256",
            evidence.source_backpropagation_gate_sha256.as_str(),
        );

        for (field, value) in [
            ("checker", evidence.checker.as_str()),
            ("checker_version", evidence.checker_version.as_str()),
            ("format", evidence.format.as_str()),
        ] {
            if value.trim().is_empty() {
                rejections.push(
                    CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                        dispatch_id: entry.dispatch_id.clone(),
                        field: field.to_string(),
                        expected: "non-empty production evidence field".to_string(),
                        actual: "empty".to_string(),
                    },
                );
            }
        }
        for (field, value) in [
            ("production_evidence.proof_sha256", evidence.proof_sha256.as_str()),
            ("production_evidence.origin_sha256", evidence.origin_sha256.as_str()),
            ("production_evidence.assumption_digest", evidence.assumption_digest.as_str()),
        ] {
            push_manifest_digest_mismatch(
                &mut rejections,
                entry.dispatch_id.as_str(),
                field,
                value,
            );
        }

        match &entry.manifest_row_acceptance {
            Some(row_acceptance) => validate_production_manifest_row_acceptance(
                &mut rejections,
                entry,
                evidence,
                row_acceptance,
            ),
            None => rejections.push(
                CheckedBinaryCertificateProductionManifestRejection::MissingManifestRowAcceptance {
                    dispatch_id: entry.dispatch_id.clone(),
                },
            ),
        }
    }

    CheckedBinaryCertificateProductionManifestDecision {
        accepted: rejections.is_empty(),
        rejections,
    }
}

impl CheckedBinaryCertificateAuditExportBundleValidation {
    pub fn accepted_rows(
        &self,
    ) -> impl Iterator<Item = &CheckedBinaryCertificateAuditExportBundleAcceptedRow> {
        self.rows.iter().filter_map(|row| match row {
            CheckedBinaryCertificateAuditExportBundleValidationRow::Accepted(row) => Some(row),
            CheckedBinaryCertificateAuditExportBundleValidationRow::Rejected(_) => None,
        })
    }

    pub fn rejected_rows(
        &self,
    ) -> impl Iterator<Item = &CheckedBinaryCertificateAuditExportBundleRejectedRow> {
        self.rows.iter().filter_map(|row| match row {
            CheckedBinaryCertificateAuditExportBundleValidationRow::Accepted(_) => None,
            CheckedBinaryCertificateAuditExportBundleValidationRow::Rejected(row) => Some(row),
        })
    }

    #[must_use]
    pub fn accepted_count(&self) -> usize {
        self.accepted_rows().count()
    }

    #[must_use]
    pub fn rejected_count(&self) -> usize {
        self.rejected_rows().count()
    }

    pub fn checked_vc_coverage_for(
        &self,
        required_vc_sha256: &[String],
    ) -> Result<CheckedBinaryCertificateAuditExportBundleCoverage, CheckError> {
        let mut required = BTreeSet::new();
        for digest in required_vc_sha256 {
            validate_canonical_sha256_hex("required vc_sha256", digest)?;
            if !required.insert(digest.clone()) {
                return Err(CheckError::MalformedProof {
                    reason: format!("duplicate required vc_sha256 `{digest}`"),
                });
            }
        }

        let mut accepted = BTreeSet::new();
        let mut duplicate_accepted = BTreeSet::new();
        let accepted_rows = self.accepted_count();
        let rejected_rows = self.rejected_count();
        for row in self.accepted_rows() {
            let digest = row.manifest_entry.vc_sha256.clone();
            validate_canonical_sha256_hex("accepted audit bundle vc_sha256", &digest)?;
            if !accepted.insert(digest.clone()) {
                duplicate_accepted.insert(digest);
            }
        }

        let missing_vc_sha256 = required.difference(&accepted).cloned().collect::<Vec<_>>();
        let unexpected_vc_sha256 = accepted.difference(&required).cloned().collect::<Vec<_>>();
        let duplicate_accepted_vc_sha256 = duplicate_accepted.into_iter().collect::<Vec<_>>();
        let complete = missing_vc_sha256.is_empty()
            && unexpected_vc_sha256.is_empty()
            && duplicate_accepted_vc_sha256.is_empty()
            && rejected_rows == 0
            && accepted.len() == required.len();

        Ok(CheckedBinaryCertificateAuditExportBundleCoverage {
            required_vcs: required.len(),
            accepted_rows,
            accepted_vcs: accepted.len(),
            rejected_rows,
            missing_vc_sha256,
            unexpected_vc_sha256,
            duplicate_accepted_vc_sha256,
            complete,
        })
    }

    pub fn validate_complete_checked_vc_coverage(
        &self,
        required_vc_sha256: &[String],
    ) -> Result<CheckedBinaryCertificateAuditExportBundleCoverage, CheckError> {
        let coverage = self.checked_vc_coverage_for(required_vc_sha256)?;
        if coverage.complete {
            Ok(coverage)
        } else {
            Err(CheckError::CheckedVcCoverageIncomplete { reason: coverage.incomplete_reason() })
        }
    }
}

impl CheckedBinaryCertificateAuditExportBundleCoverage {
    fn incomplete_reason(&self) -> String {
        format!(
            "required_vcs={}, accepted_vcs={}, accepted_rows={}, rejected_rows={}, missing_vc_sha256={:?}, unexpected_vc_sha256={:?}, duplicate_accepted_vc_sha256={:?}",
            self.required_vcs,
            self.accepted_vcs,
            self.accepted_rows,
            self.rejected_rows,
            self.missing_vc_sha256,
            self.unexpected_vc_sha256,
            self.duplicate_accepted_vc_sha256,
        )
    }
}

impl CheckedBinaryCertificateAuditExportBundleValidationRow {
    #[must_use]
    pub fn accepted(&self) -> bool {
        matches!(self, Self::Accepted(_))
    }

    #[must_use]
    pub fn rejected(&self) -> bool {
        matches!(self, Self::Rejected(_))
    }

    #[must_use]
    pub fn rejection_code(&self) -> Option<CheckedBinaryCertificateAuditExportBundleRejectionCode> {
        match self {
            Self::Accepted(_) => None,
            Self::Rejected(row) => Some(row.code),
        }
    }
}

impl CheckedBinaryCertificateAuditExportBundleRejectedRow {
    fn from_bundle_entry(
        bundle_entry: &CheckedBinaryCertificateAuditExportBundleEntry,
        manifest_entry: Option<CheckedBinaryCertificateManifestEntry>,
        audit_export: Option<CheckedBinaryCertificateAuditExport>,
        code: CheckedBinaryCertificateAuditExportBundleRejectionCode,
        reason: impl Into<String>,
    ) -> Self {
        Self {
            dispatch_id: bundle_entry.dispatch_id.clone(),
            vc_sha256: bundle_entry.vc_sha256.clone(),
            certificate_sha256: bundle_entry.certificate_sha256.clone(),
            code,
            reason: reason.into(),
            bundle_entry: bundle_entry.clone(),
            manifest_entry,
            audit_export,
        }
    }
}

impl CheckedBinaryCertificateAuditExportBundleRejectionCode {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ManifestRowMissing => "manifest_row_missing",
            Self::ManifestRowMismatch => "manifest_row_mismatch",
            Self::AuditExportUnreadable => "audit_export_unreadable",
            Self::AuditExportDigestMismatch => "audit_export_digest_mismatch",
            Self::AuditExportMalformed => "audit_export_malformed",
            Self::ProofExportMismatch => "proof_export_mismatch",
            Self::CheckerMismatch => "checker_mismatch",
            Self::ReplayMismatch => "replay_mismatch",
            Self::AssumptionMismatch => "assumption_mismatch",
            Self::VcDigestMismatch => "vc_digest_mismatch",
            Self::ArtifactUnreadable => "artifact_unreadable",
            Self::ArtifactMismatch => "artifact_mismatch",
            Self::ValidationFailed => "validation_failed",
        }
    }
}

impl CheckedBinaryCertificateManifest {
    #[must_use]
    pub fn new() -> Self {
        Self {
            schema_version: CHECKED_BINARY_CERTIFICATE_MANIFEST_SCHEMA_VERSION.to_string(),
            certificates: Vec::new(),
        }
    }

    pub fn add_certificate(&mut self, entry: CheckedBinaryCertificateManifestEntry) {
        self.certificates.push(entry);
    }

    pub fn from_artifact_refs(
        root: impl AsRef<Path>,
        artifact_refs: &[CheckedBinaryCertificateArtifactRef],
    ) -> Result<Self, crate::CertError> {
        let root = root.as_ref();
        let mut artifact_digests = BTreeSet::new();
        let mut certificates = Vec::with_capacity(artifact_refs.len());

        for artifact_ref in artifact_refs {
            if !artifact_digests.insert(artifact_ref.content_sha256.clone()) {
                return Err(crate::CertError::InvalidCertificate {
                    reason: format!(
                        "duplicate checked certificate artifact ref `{}`",
                        artifact_ref.content_sha256
                    ),
                });
            }

            let artifact = load_checked_certificate_artifact_ref(artifact_ref)?;
            let relative_path = artifact_ref.path.strip_prefix(root).map_err(|_| {
                crate::CertError::InvalidCertificate {
                    reason: format!(
                        "checked certificate artifact path `{}` is outside manifest root `{}`",
                        artifact_ref.path.display(),
                        root.display()
                    ),
                }
            })?;
            certificates.push(CheckedBinaryCertificateManifestEntry::from_artifact(
                &artifact,
                relative_path.to_path_buf(),
            ));
        }

        certificates.sort_by(|left, right| {
            left.certificate_sha256
                .cmp(&right.certificate_sha256)
                .then_with(|| left.vc_sha256.cmp(&right.vc_sha256))
                .then_with(|| left.dispatch_id.cmp(&right.dispatch_id))
        });

        let manifest = Self {
            schema_version: CHECKED_BINARY_CERTIFICATE_MANIFEST_SCHEMA_VERSION.to_string(),
            certificates,
        };
        manifest
            .validate_structure()
            .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
        Ok(manifest)
    }

    pub fn to_json(&self) -> Result<String, crate::CertError> {
        self.validate_structure()
            .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
        serde_json::to_string_pretty(self)
            .map_err(|err| crate::CertError::SerializationFailed { reason: err.to_string() })
    }

    pub fn from_json(json: &str) -> Result<Self, crate::CertError> {
        let manifest: Self = serde_json::from_str(json)
            .map_err(|err| crate::CertError::SerializationFailed { reason: err.to_string() })?;
        manifest
            .validate_structure()
            .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
        Ok(manifest)
    }

    pub fn validate_structure(&self) -> Result<(), CheckError> {
        if self.schema_version != CHECKED_BINARY_CERTIFICATE_MANIFEST_SCHEMA_VERSION {
            return Err(binding_mismatch(
                "manifest.schema_version",
                CHECKED_BINARY_CERTIFICATE_MANIFEST_SCHEMA_VERSION,
                self.schema_version.as_str(),
            ));
        }

        let mut dispatch_ids = BTreeSet::new();
        let mut vc_digests = BTreeSet::new();
        for entry in &self.certificates {
            entry.validate_structure()?;
            if !dispatch_ids.insert(entry.dispatch_id.clone()) {
                return Err(CheckError::MalformedProof {
                    reason: format!(
                        "duplicate checked certificate manifest dispatch_id `{}`",
                        entry.dispatch_id
                    ),
                });
            }
            if !vc_digests.insert(entry.vc_sha256.clone()) {
                return Err(CheckError::MalformedProof {
                    reason: format!(
                        "duplicate checked certificate manifest vc_sha256 `{}`",
                        entry.vc_sha256
                    ),
                });
            }
        }

        Ok(())
    }

    /// Validate that every manifest entry points at an existing checked artifact.
    pub fn validate_files(&self, root: impl AsRef<Path>) -> Result<(), crate::CertError> {
        self.validate_structure()
            .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
        let root = root.as_ref();
        for entry in &self.certificates {
            let path = entry.resolved_certificate_path(root)?;
            if !path.is_file() {
                return Err(crate::CertError::InvalidCertificate {
                    reason: format!(
                        "checked certificate manifest entry `{}` points to missing certificate file `{}`",
                        entry.dispatch_id,
                        path.display()
                    ),
                });
            }
            let artifact = load_checked_certificate_artifact(&path)?;
            entry
                .validate_artifact(&artifact)
                .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
        }

        Ok(())
    }
}

impl Default for CheckedBinaryCertificateManifest {
    fn default() -> Self {
        Self::new()
    }
}

impl CheckedBinaryCertificateManifestEntry {
    #[must_use]
    pub fn from_artifact(
        artifact: &CheckedBinaryCertificateArtifact,
        certificate_path: impl Into<PathBuf>,
    ) -> Self {
        Self {
            dispatch_id: artifact.dispatch_id.clone(),
            vc_sha256: artifact.vc_sha256.clone(),
            origin_sha256: artifact.origin_sha256.clone(),
            proof_sha256: artifact.proof_sha256.clone(),
            proof_export_sha256: artifact.proof_export_sha256.clone(),
            certificate_sha256: artifact.certificate_sha256.clone(),
            certificate_path: certificate_path.into(),
            format: artifact.format.clone(),
            checker: artifact.checker.clone(),
            checker_version: artifact.checker_version.clone(),
            replay: artifact.replay,
            replay_transcript_digest: artifact.replay_transcript_digest.clone(),
            binary_artifact_digest_identity: artifact.binary_artifact_digest_identity.clone(),
            assumption_digest: artifact.assumption_digest.clone(),
        }
    }

    pub fn validate_structure(&self) -> Result<(), CheckError> {
        if self.dispatch_id.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "checked certificate manifest entry is missing dispatch id".to_string(),
            });
        }
        validate_canonical_sha256_hex("manifest vc_sha256", &self.vc_sha256)?;
        validate_canonical_sha256_hex("manifest origin_sha256", &self.origin_sha256)?;
        validate_canonical_sha256_hex("manifest proof_sha256", &self.proof_sha256)?;
        validate_canonical_sha256_hex("manifest proof_export_sha256", &self.proof_export_sha256)?;
        validate_canonical_sha256_hex("manifest certificate_sha256", &self.certificate_sha256)?;
        validate_canonical_sha256_hex("manifest assumption_digest", &self.assumption_digest)?;
        if let Some(replay_transcript_digest) = self.replay_transcript_digest.as_deref() {
            validate_canonical_sha256_hex(
                "manifest replay_transcript_digest",
                replay_transcript_digest,
            )?;
        }
        validate_binary_artifact_digest_identity(&self.binary_artifact_digest_identity)?;
        if self.format.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "checked certificate manifest entry is missing proof format".to_string(),
            });
        }
        if self.checker.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "checked certificate manifest entry is missing checker id".to_string(),
            });
        }
        if self.checker_version.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "checked certificate manifest entry is missing checker version".to_string(),
            });
        }
        validate_relative_manifest_path("certificate_path", &self.certificate_path)?;
        validate_manifest_certificate_path_matches_digest(
            "certificate_path",
            &self.certificate_path,
            &self.certificate_sha256,
        )?;

        Ok(())
    }

    pub fn validate_artifact(
        &self,
        artifact: &CheckedBinaryCertificateArtifact,
    ) -> Result<(), CheckError> {
        artifact.validate_integrity()?;
        if artifact.dispatch_id != self.dispatch_id {
            return Err(binding_mismatch(
                "manifest.dispatch_id",
                self.dispatch_id.as_str(),
                artifact.dispatch_id.as_str(),
            ));
        }
        if artifact.vc_sha256 != self.vc_sha256 {
            return Err(binding_mismatch(
                "manifest.vc_sha256",
                self.vc_sha256.as_str(),
                artifact.vc_sha256.as_str(),
            ));
        }
        if artifact.origin_sha256 != self.origin_sha256 {
            return Err(binding_mismatch(
                "manifest.origin_sha256",
                self.origin_sha256.as_str(),
                artifact.origin_sha256.as_str(),
            ));
        }
        if artifact.proof_sha256 != self.proof_sha256 {
            return Err(binding_mismatch(
                "manifest.proof_sha256",
                self.proof_sha256.as_str(),
                artifact.proof_sha256.as_str(),
            ));
        }
        if artifact.proof_export_sha256 != self.proof_export_sha256 {
            return Err(binding_mismatch(
                "manifest.proof_export_sha256",
                self.proof_export_sha256.as_str(),
                artifact.proof_export_sha256.as_str(),
            ));
        }
        if artifact.certificate_sha256 != self.certificate_sha256 {
            return Err(binding_mismatch(
                "manifest.certificate_sha256",
                self.certificate_sha256.as_str(),
                artifact.certificate_sha256.as_str(),
            ));
        }
        if artifact.format != self.format {
            return Err(binding_mismatch(
                "manifest.format",
                self.format.as_str(),
                artifact.format.as_str(),
            ));
        }
        if artifact.checker != self.checker {
            return Err(binding_mismatch(
                "manifest.checker",
                self.checker.as_str(),
                artifact.checker.as_str(),
            ));
        }
        if artifact.checker_version != self.checker_version {
            return Err(binding_mismatch(
                "manifest.checker_version",
                self.checker_version.as_str(),
                artifact.checker_version.as_str(),
            ));
        }
        if artifact.replay != self.replay {
            return Err(binding_mismatch(
                "manifest.replay",
                format!("{:?}", self.replay),
                format!("{:?}", artifact.replay),
            ));
        }
        if artifact.replay_transcript_digest != self.replay_transcript_digest {
            return Err(binding_mismatch(
                "manifest.replay_transcript_digest",
                format!("{:?}", self.replay_transcript_digest),
                format!("{:?}", artifact.replay_transcript_digest),
            ));
        }
        if artifact.binary_artifact_digest_identity != self.binary_artifact_digest_identity {
            return Err(binding_mismatch(
                "manifest.binary_artifact_digest_identity",
                binary_artifact_digest_identity_label(&self.binary_artifact_digest_identity)?,
                binary_artifact_digest_identity_label(&artifact.binary_artifact_digest_identity)?,
            ));
        }
        if artifact.assumption_digest != self.assumption_digest {
            return Err(CheckError::AssumptionDigestMismatch {
                expected: self.assumption_digest.clone(),
                actual: artifact.assumption_digest.clone(),
            });
        }

        Ok(())
    }

    /// Validate this manifest row against the production inputs that created it.
    pub fn validate_production_bindings(
        &self,
        artifact: &CheckedBinaryCertificateArtifact,
        canonical_vc_bytes: &[u8],
        export: &SolverProofExport,
        expected_checker: &str,
        expected_checker_version: &str,
        expected_replay_transcript_digest: Option<&str>,
    ) -> Result<(), CheckError> {
        self.validate_artifact(artifact)?;

        let actual_vc_sha256 = stable_sha256_hex(canonical_vc_bytes);
        if self.vc_sha256 != actual_vc_sha256 {
            return Err(CheckError::VcDigestMismatch {
                expected: self.vc_sha256.clone(),
                actual: actual_vc_sha256,
            });
        }

        let expected_proof_export_sha256 = export.normalized_metadata_sha256()?;
        if self.proof_export_sha256 != expected_proof_export_sha256 {
            return Err(binding_mismatch(
                "proof_export_sha256",
                expected_proof_export_sha256,
                self.proof_export_sha256.as_str(),
            ));
        }
        if self.proof_sha256 != export.proof_sha256 {
            return Err(binding_mismatch(
                "proof_sha256",
                export.proof_sha256.as_str(),
                self.proof_sha256.as_str(),
            ));
        }
        if self.vc_sha256 != export.vc_sha256 {
            return Err(CheckError::VcDigestMismatch {
                expected: export.vc_sha256.clone(),
                actual: self.vc_sha256.clone(),
            });
        }
        if self.dispatch_id != export.dispatch_id {
            return Err(binding_mismatch(
                "dispatch_id",
                export.dispatch_id.as_str(),
                self.dispatch_id.as_str(),
            ));
        }

        if self.checker != expected_checker {
            return Err(binding_mismatch("checker", expected_checker, self.checker.as_str()));
        }
        if self.checker_version != expected_checker_version {
            return Err(binding_mismatch(
                "checker_version",
                expected_checker_version,
                self.checker_version.as_str(),
            ));
        }

        if let Some(expected_digest) = expected_replay_transcript_digest {
            validate_canonical_sha256_hex("replay_transcript_digest", expected_digest)?;
            if self.replay_transcript_digest.as_deref() != Some(expected_digest) {
                return Err(CheckError::ReplayDigestMismatch {
                    expected: expected_digest.to_string(),
                    actual: self
                        .replay_transcript_digest
                        .as_deref()
                        .unwrap_or("<missing>")
                        .to_string(),
                });
            }
        } else if self.replay_transcript_digest.is_some() {
            return Err(CheckError::ReplayDigestMismatch {
                expected: "<none>".to_string(),
                actual: self.replay_transcript_digest.as_deref().unwrap_or("<missing>").to_string(),
            });
        }

        Ok(())
    }

    fn resolved_certificate_path(&self, root: &Path) -> Result<PathBuf, crate::CertError> {
        validate_relative_manifest_path("certificate_path", &self.certificate_path)
            .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
        Ok(root.join(&self.certificate_path))
    }
}

impl CheckedBinaryCertificateCheckerSelection {
    #[must_use]
    pub fn from_manifest_entry(entry: &CheckedBinaryCertificateManifestEntry) -> Self {
        Self {
            checker: entry.checker.clone(),
            checker_version: entry.checker_version.clone(),
            format: entry.format.clone(),
        }
    }

    pub fn validate_structure(&self) -> Result<(), CheckError> {
        if self.checker.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "checker selection is missing checker id".to_string(),
            });
        }
        if self.checker_version.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "checker selection is missing checker version".to_string(),
            });
        }
        if self.format.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "checker selection is missing proof format".to_string(),
            });
        }

        Ok(())
    }

    fn validate_manifest_entry(
        &self,
        entry: &CheckedBinaryCertificateManifestEntry,
    ) -> Result<(), CheckError> {
        self.validate_structure()?;
        if self.checker != entry.checker {
            return Err(binding_mismatch(
                "checker_selection.checker",
                entry.checker.as_str(),
                self.checker.as_str(),
            ));
        }
        if self.checker_version != entry.checker_version {
            return Err(binding_mismatch(
                "checker_selection.checker_version",
                entry.checker_version.as_str(),
                self.checker_version.as_str(),
            ));
        }
        if self.format != entry.format {
            return Err(binding_mismatch(
                "checker_selection.format",
                entry.format.as_str(),
                self.format.as_str(),
            ));
        }

        Ok(())
    }

    fn validate_artifact(
        &self,
        artifact: &CheckedBinaryCertificateArtifact,
    ) -> Result<(), CheckError> {
        if self.checker != artifact.checker {
            return Err(binding_mismatch(
                "checker_selection.checker",
                artifact.checker.as_str(),
                self.checker.as_str(),
            ));
        }
        if self.checker_version != artifact.checker_version {
            return Err(binding_mismatch(
                "checker_selection.checker_version",
                artifact.checker_version.as_str(),
                self.checker_version.as_str(),
            ));
        }
        if self.format != artifact.format {
            return Err(binding_mismatch(
                "checker_selection.format",
                artifact.format.as_str(),
                self.format.as_str(),
            ));
        }

        Ok(())
    }
}

impl CheckedBinaryCertificateExternalProcessTranscript {
    #[must_use]
    pub fn new<I, S>(
        command: impl Into<String>,
        argv: I,
        exit_status: i32,
        stdout_sha256: Option<String>,
        stderr_sha256: Option<String>,
    ) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        Self {
            command: command.into(),
            argv: argv.into_iter().map(Into::into).collect(),
            cwd: None,
            env: BTreeMap::new(),
            proof_artifact_args: Vec::new(),
            timeout_policy: None,
            timed_out: false,
            exit_status,
            stdout_sha256,
            stderr_sha256,
        }
    }

    #[must_use]
    pub fn with_cwd(mut self, cwd: impl Into<PathBuf>) -> Self {
        self.cwd = Some(cwd.into());
        self
    }

    #[must_use]
    pub fn with_cwd_option(mut self, cwd: Option<PathBuf>) -> Self {
        self.cwd = cwd;
        self
    }

    #[must_use]
    pub fn with_env<I, K, V>(mut self, env: I) -> Self
    where
        I: IntoIterator<Item = (K, V)>,
        K: Into<String>,
        V: Into<String>,
    {
        self.env = env.into_iter().map(|(key, value)| (key.into(), value.into())).collect();
        self
    }

    #[must_use]
    pub fn with_proof_artifact_args<I>(mut self, proof_artifact_args: I) -> Self
    where
        I: IntoIterator<Item = CheckedBinaryCertificateExternalProcessProofArtifactArgument>,
    {
        self.proof_artifact_args = proof_artifact_args.into_iter().collect();
        self
    }

    #[must_use]
    pub fn with_timeout_policy(
        mut self,
        timeout_policy: CheckedBinaryCertificateExternalCheckerTimeoutPolicy,
    ) -> Self {
        self.timeout_policy = Some(timeout_policy);
        self
    }

    #[must_use]
    pub fn with_timeout_policy_option(
        mut self,
        timeout_policy: Option<CheckedBinaryCertificateExternalCheckerTimeoutPolicy>,
    ) -> Self {
        self.timeout_policy = timeout_policy;
        self
    }

    #[must_use]
    pub fn with_timed_out(mut self, timed_out: bool) -> Self {
        self.timed_out = timed_out;
        self
    }

    pub fn add_manifest_entry_proof_artifact_args(
        &mut self,
        entry: &CheckedBinaryCertificateManifestEntry,
    ) {
        let certificate_path = entry.certificate_path.display().to_string();
        if !self.proof_artifact_args.iter().any(|arg| arg.role == "checked_certificate") {
            self.proof_artifact_args.push(
                CheckedBinaryCertificateExternalProcessProofArtifactArgument::new(
                    "checked_certificate",
                    find_argv_index_for_path_suffix(&self.argv, &certificate_path),
                    certificate_path,
                    Some(entry.certificate_sha256.clone()),
                ),
            );
        }
        if !self.proof_artifact_args.iter().any(|arg| arg.role == "solver_proof_export") {
            self.proof_artifact_args.push(
                CheckedBinaryCertificateExternalProcessProofArtifactArgument::new(
                    "solver_proof_export",
                    None,
                    entry.proof_export_sha256.clone(),
                    Some(entry.proof_export_sha256.clone()),
                ),
            );
        }
        if !self.proof_artifact_args.iter().any(|arg| arg.role == "solver_proof_payload") {
            self.proof_artifact_args.push(
                CheckedBinaryCertificateExternalProcessProofArtifactArgument::new(
                    "solver_proof_payload",
                    None,
                    entry.proof_sha256.clone(),
                    Some(entry.proof_sha256.clone()),
                ),
            );
        }
    }

    pub fn validate_success(&self) -> Result<(), CheckError> {
        if self.command.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "external checker transcript is missing command".to_string(),
            });
        }
        if self.argv.is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "external checker transcript is missing argv".to_string(),
            });
        }
        for key in self.env.keys() {
            if key.trim().is_empty() || key.contains('=') {
                return Err(CheckError::MalformedProof {
                    reason: format!("external checker transcript has invalid env key `{key}`"),
                });
            }
        }
        for artifact_arg in &self.proof_artifact_args {
            artifact_arg.validate_structure()?;
        }
        if let Some(timeout_policy) = &self.timeout_policy {
            timeout_policy.validate_structure()?;
        }
        if self.timed_out {
            let timeout_ms =
                self.timeout_policy.as_ref().map(|policy| policy.timeout_ms).unwrap_or(0);
            return Err(CheckError::CheckerExternalProcessTimedOut {
                command: self.command.clone(),
                timeout_ms,
            });
        }
        if self.exit_status != 0 {
            return Err(CheckError::CheckerExternalProcessFailed {
                command: self.command.clone(),
                exit_status: self.exit_status,
            });
        }
        let stdout_sha256 = self.stdout_sha256.as_deref().ok_or_else(|| {
            CheckError::MissingCheckerExternalProcessTranscriptDigest {
                field: "stdout_sha256".to_string(),
            }
        })?;
        let stderr_sha256 = self.stderr_sha256.as_deref().ok_or_else(|| {
            CheckError::MissingCheckerExternalProcessTranscriptDigest {
                field: "stderr_sha256".to_string(),
            }
        })?;
        if stdout_sha256.trim().is_empty() {
            return Err(CheckError::MissingCheckerExternalProcessTranscriptDigest {
                field: "stdout_sha256".to_string(),
            });
        }
        if stderr_sha256.trim().is_empty() {
            return Err(CheckError::MissingCheckerExternalProcessTranscriptDigest {
                field: "stderr_sha256".to_string(),
            });
        }
        validate_canonical_sha256_hex("external checker transcript stdout_sha256", stdout_sha256)?;
        validate_canonical_sha256_hex("external checker transcript stderr_sha256", stderr_sha256)?;
        Ok(())
    }

    pub fn sha256(&self) -> Result<String, CheckError> {
        self.validate_success()?;
        let bytes = serde_json::to_vec(self)
            .map_err(|err| CheckError::CheckerInternalError { reason: err.to_string() })?;
        Ok(stable_sha256_hex(&bytes))
    }
}

impl CheckedBinaryCertificateExternalCheckerTimeoutPolicy {
    #[must_use]
    pub const fn new(timeout_ms: u64) -> Self {
        Self { timeout_ms }
    }

    pub fn validate_structure(&self) -> Result<(), CheckError> {
        if self.timeout_ms == 0 {
            return Err(CheckError::MalformedProof {
                reason: "external checker timeout policy must be greater than zero".to_string(),
            });
        }
        Ok(())
    }
}

impl CheckedBinaryCertificateExternalProcessProofArtifactArgument {
    #[must_use]
    pub fn new(
        role: impl Into<String>,
        argv_index: Option<usize>,
        value: impl Into<String>,
        sha256: Option<String>,
    ) -> Self {
        Self { role: role.into(), argv_index, value: value.into(), sha256 }
    }

    pub fn validate_structure(&self) -> Result<(), CheckError> {
        if self.role.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "external checker proof artifact argument is missing role".to_string(),
            });
        }
        if self.value.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: format!(
                    "external checker proof artifact argument `{}` is missing value",
                    self.role
                ),
            });
        }
        if let Some(sha256) = self.sha256.as_deref() {
            validate_canonical_sha256_hex(
                "external checker proof artifact argument sha256",
                sha256,
            )?;
        }
        Ok(())
    }
}

impl CheckedBinaryCertificateExternalCheckerRunner {
    #[must_use]
    pub fn new<I, S>(
        command: impl Into<PathBuf>,
        args: I,
        checker_binary_sha256: impl Into<String>,
        checked_at_unix_ms: u64,
    ) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        Self {
            command: command.into(),
            args: args.into_iter().map(Into::into).collect(),
            cwd: None,
            env: BTreeMap::new(),
            proof_artifact_args: Vec::new(),
            timeout_policy: None,
            checker_binary_sha256: checker_binary_sha256.into(),
            checker_config_sha256: None,
            checked_at_unix_ms,
        }
    }

    pub fn from_command_path<I, S>(
        command: impl Into<PathBuf>,
        args: I,
        checked_at_unix_ms: u64,
    ) -> Result<Self, CheckError>
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let command = command.into();
        let checker_binary_sha256 =
            sha256_file(&command).map_err(|err| CheckError::CheckerExternalProcessSpawnFailed {
                command: command.to_string_lossy().into_owned(),
                reason: err.to_string(),
            })?;
        Ok(Self::new(command, args, checker_binary_sha256, checked_at_unix_ms))
    }

    #[must_use]
    pub fn with_checker_config_sha256(mut self, checker_config_sha256: impl Into<String>) -> Self {
        self.checker_config_sha256 = Some(checker_config_sha256.into());
        self
    }

    #[must_use]
    pub fn with_current_dir(mut self, cwd: impl Into<PathBuf>) -> Self {
        self.cwd = Some(cwd.into());
        self
    }

    #[must_use]
    pub fn with_env(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.env.insert(key.into(), value.into());
        self
    }

    #[must_use]
    pub fn with_envs<I, K, V>(mut self, env: I) -> Self
    where
        I: IntoIterator<Item = (K, V)>,
        K: Into<String>,
        V: Into<String>,
    {
        self.env.extend(env.into_iter().map(|(key, value)| (key.into(), value.into())));
        self
    }

    #[must_use]
    pub fn with_timeout_ms(mut self, timeout_ms: u64) -> Self {
        self.timeout_policy =
            Some(CheckedBinaryCertificateExternalCheckerTimeoutPolicy::new(timeout_ms));
        self
    }

    #[must_use]
    pub fn with_proof_artifact_arg(
        mut self,
        proof_artifact_arg: CheckedBinaryCertificateExternalProcessProofArtifactArgument,
    ) -> Self {
        self.proof_artifact_args.push(proof_artifact_arg);
        self
    }

    pub fn run_transcript(
        &self,
    ) -> Result<CheckedBinaryCertificateExternalProcessTranscript, CheckError> {
        if self.command.as_os_str().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "external checker runner is missing command".to_string(),
            });
        }
        validate_canonical_sha256_hex(
            "external checker runner checker_binary_sha256",
            &self.checker_binary_sha256,
        )?;
        if let Some(checker_config_sha256) = self.checker_config_sha256.as_deref() {
            validate_canonical_sha256_hex(
                "external checker runner checker_config_sha256",
                checker_config_sha256,
            )?;
        }
        for key in self.env.keys() {
            if key.trim().is_empty() || key.contains('=') {
                return Err(CheckError::MalformedProof {
                    reason: format!("external checker runner has invalid env key `{key}`"),
                });
            }
        }
        for proof_artifact_arg in &self.proof_artifact_args {
            proof_artifact_arg.validate_structure()?;
        }
        if let Some(timeout_policy) = &self.timeout_policy {
            timeout_policy.validate_structure()?;
        }

        let command = self.command.to_string_lossy().into_owned();
        let mut process = Command::new(&self.command);
        process
            .args(&self.args)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .env_clear();
        if let Some(cwd) = &self.cwd {
            process.current_dir(cwd);
        }
        process.envs(&self.env);
        let mut child =
            process.spawn().map_err(|err| CheckError::CheckerExternalProcessSpawnFailed {
                command: command.clone(),
                reason: err.to_string(),
            })?;

        let stdout =
            child.stdout.take().ok_or_else(|| CheckError::CheckerExternalProcessIoFailed {
                command: command.clone(),
                stream: "stdout".to_string(),
                reason: "stdout pipe was not captured".to_string(),
            })?;
        let stderr =
            child.stderr.take().ok_or_else(|| CheckError::CheckerExternalProcessIoFailed {
                command: command.clone(),
                stream: "stderr".to_string(),
                reason: "stderr pipe was not captured".to_string(),
            })?;

        let stdout_digest = spawn_stream_digest(command.clone(), "stdout", stdout);
        let stderr_digest = spawn_stream_digest(command.clone(), "stderr", stderr);
        let (status, timed_out) =
            wait_for_checker_child(&mut child, command.clone(), self.timeout_policy.as_ref())?;
        let stdout_sha256 =
            stdout_digest.join().map_err(|_| CheckError::CheckerExternalProcessIoFailed {
                command: command.clone(),
                stream: "stdout".to_string(),
                reason: "stdout digest worker panicked".to_string(),
            })??;
        let stderr_sha256 =
            stderr_digest.join().map_err(|_| CheckError::CheckerExternalProcessIoFailed {
                command: command.clone(),
                stream: "stderr".to_string(),
                reason: "stderr digest worker panicked".to_string(),
            })??;

        let argv: Vec<String> = std::iter::once(command.clone()).chain(self.args.clone()).collect();
        Ok(CheckedBinaryCertificateExternalProcessTranscript::new(
            command,
            argv,
            status.code().unwrap_or(-1),
            Some(stdout_sha256),
            Some(stderr_sha256),
        ))
        .map(|transcript| {
            transcript
                .with_cwd_option(self.cwd.clone())
                .with_env(self.env.clone())
                .with_proof_artifact_args(self.proof_artifact_args.clone())
                .with_timeout_policy_option(self.timeout_policy.clone())
                .with_timed_out(timed_out)
        })
    }

    pub fn run_for_manifest_entry(
        &self,
        entry: &CheckedBinaryCertificateManifestEntry,
    ) -> Result<CheckedBinaryCertificateProductionCheckerEvidence, CheckError> {
        let mut transcript = self.run_transcript()?;
        transcript.add_manifest_entry_proof_artifact_args(entry);
        CheckedBinaryCertificateProductionCheckerEvidence::external_process_for_manifest_entry(
            entry,
            self.checker_binary_sha256.clone(),
            self.checker_config_sha256.clone(),
            transcript,
            self.checked_at_unix_ms,
        )
    }

    pub fn run_for_manifest_entry_with_artifacts(
        &self,
        entry: &CheckedBinaryCertificateManifestEntry,
        checked_certificate_path: impl AsRef<Path>,
        solver_proof_export_metadata_path: impl AsRef<Path>,
        solver_proof_payload_path: impl AsRef<Path>,
    ) -> Result<CheckedBinaryCertificateProductionCheckerEvidence, CheckError> {
        let checked_certificate_path = checked_certificate_path.as_ref().display().to_string();
        let solver_proof_export_metadata_path =
            solver_proof_export_metadata_path.as_ref().display().to_string();
        let solver_proof_payload_path = solver_proof_payload_path.as_ref().display().to_string();

        let mut runner = self.clone();
        runner.push_checker_arg_with_artifact_ref(
            "--checked-certificate",
            checked_certificate_path,
            CheckedBinaryCertificateExternalProcessProofArtifactArgument::new(
                "checked_certificate",
                None,
                entry.certificate_path.display().to_string(),
                Some(entry.certificate_sha256.clone()),
            ),
        );
        runner.push_checker_arg_with_artifact_ref(
            "--solver-proof-export-metadata",
            solver_proof_export_metadata_path,
            CheckedBinaryCertificateExternalProcessProofArtifactArgument::new(
                "solver_proof_export",
                None,
                entry.proof_export_sha256.clone(),
                Some(entry.proof_export_sha256.clone()),
            ),
        );
        runner.push_checker_arg_with_artifact_ref(
            "--solver-proof-payload",
            solver_proof_payload_path,
            CheckedBinaryCertificateExternalProcessProofArtifactArgument::new(
                "solver_proof_payload",
                None,
                entry.proof_sha256.clone(),
                Some(entry.proof_sha256.clone()),
            ),
        );
        runner.args.extend([
            "--vc-sha256".to_string(),
            entry.vc_sha256.clone(),
            "--origin-sha256".to_string(),
            entry.origin_sha256.clone(),
            "--assumption-digest".to_string(),
            entry.assumption_digest.clone(),
            "--certificate-sha256".to_string(),
            entry.certificate_sha256.clone(),
            "--proof-export-sha256".to_string(),
            entry.proof_export_sha256.clone(),
            "--proof-sha256".to_string(),
            entry.proof_sha256.clone(),
        ]);

        let mut transcript = runner.run_transcript()?;
        transcript.add_manifest_entry_proof_artifact_args(entry);
        CheckedBinaryCertificateProductionCheckerEvidence::external_process_for_manifest_entry(
            entry,
            runner.checker_binary_sha256,
            runner.checker_config_sha256,
            transcript,
            runner.checked_at_unix_ms,
        )
    }

    fn push_checker_arg_with_artifact_ref(
        &mut self,
        flag: &'static str,
        value: String,
        mut proof_artifact_arg: CheckedBinaryCertificateExternalProcessProofArtifactArgument,
    ) {
        self.args.push(flag.to_string());
        self.args.push(value.clone());
        proof_artifact_arg.argv_index = Some(self.args.len());
        proof_artifact_arg.value = value;
        self.proof_artifact_args.push(proof_artifact_arg);
    }
}

impl CheckedBinaryCertificateProductionCheckerEvidence {
    pub fn external_process_for_manifest_entry(
        entry: &CheckedBinaryCertificateManifestEntry,
        checker_binary_sha256: impl Into<String>,
        checker_config_sha256: Option<String>,
        transcript: CheckedBinaryCertificateExternalProcessTranscript,
        checked_at_unix_ms: u64,
    ) -> Result<Self, CheckError> {
        let invocation_sha256 = transcript.sha256()?;
        let stdout_sha256 = transcript.stdout_sha256.clone().ok_or_else(|| {
            CheckError::MissingCheckerExternalProcessTranscriptDigest {
                field: "stdout_sha256".to_string(),
            }
        })?;
        let stderr_sha256 = transcript.stderr_sha256.clone().ok_or_else(|| {
            CheckError::MissingCheckerExternalProcessTranscriptDigest {
                field: "stderr_sha256".to_string(),
            }
        })?;
        let mut evidence = Self::production_for_manifest_entry(
            entry,
            checker_binary_sha256,
            invocation_sha256,
            checked_at_unix_ms,
        );
        evidence.checker_config_sha256 = checker_config_sha256;
        evidence.stdout_sha256 = Some(stdout_sha256);
        evidence.stderr_sha256 = Some(stderr_sha256);
        evidence.external_process_transcript = Some(transcript);
        evidence.validate_production()?;
        Ok(evidence)
    }

    #[must_use]
    pub fn production_for_manifest_entry(
        entry: &CheckedBinaryCertificateManifestEntry,
        checker_binary_sha256: impl Into<String>,
        invocation_sha256: impl Into<String>,
        checked_at_unix_ms: u64,
    ) -> Self {
        Self {
            kind: CheckedBinaryCertificateCheckerEvidenceKind::Production,
            invocation_kind: CheckedBinaryCertificateCheckerInvocationKind::ExternalProcess,
            checker: entry.checker.clone(),
            checker_version: entry.checker_version.clone(),
            format: entry.format.clone(),
            checker_binary_sha256: checker_binary_sha256.into(),
            checker_config_sha256: None,
            invocation_sha256: invocation_sha256.into(),
            stdout_sha256: None,
            stderr_sha256: None,
            external_process_transcript: None,
            proof_export_sha256: entry.proof_export_sha256.clone(),
            certificate_sha256: entry.certificate_sha256.clone(),
            checked_at_unix_ms,
        }
    }

    pub fn validate_structure(&self) -> Result<(), CheckError> {
        if self.checker.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "production checker evidence is missing checker id".to_string(),
            });
        }
        if self.checker_version.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "production checker evidence is missing checker version".to_string(),
            });
        }
        if self.format.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "production checker evidence is missing proof format".to_string(),
            });
        }
        if self.checked_at_unix_ms == 0 {
            return Err(CheckError::MalformedProof {
                reason: "production checker evidence is missing checked_at_unix_ms".to_string(),
            });
        }
        validate_canonical_sha256_hex(
            "production checker evidence checker_binary_sha256",
            &self.checker_binary_sha256,
        )?;
        if let Some(checker_config_sha256) = self.checker_config_sha256.as_deref() {
            validate_canonical_sha256_hex(
                "production checker evidence checker_config_sha256",
                checker_config_sha256,
            )?;
        }
        validate_canonical_sha256_hex(
            "production checker evidence invocation_sha256",
            &self.invocation_sha256,
        )?;
        if let Some(stdout_sha256) = self.stdout_sha256.as_deref() {
            validate_canonical_sha256_hex(
                "production checker evidence stdout_sha256",
                stdout_sha256,
            )?;
        }
        if let Some(stderr_sha256) = self.stderr_sha256.as_deref() {
            validate_canonical_sha256_hex(
                "production checker evidence stderr_sha256",
                stderr_sha256,
            )?;
        }
        validate_canonical_sha256_hex(
            "production checker evidence proof_export_sha256",
            &self.proof_export_sha256,
        )?;
        validate_canonical_sha256_hex(
            "production checker evidence certificate_sha256",
            &self.certificate_sha256,
        )?;

        Ok(())
    }

    pub fn validate_production(&self) -> Result<(), CheckError> {
        self.validate_structure()?;
        if self.kind != CheckedBinaryCertificateCheckerEvidenceKind::Production {
            return Err(CheckError::CheckerEvidenceNotProduction { kind: self.kind });
        }
        if self.invocation_kind != CheckedBinaryCertificateCheckerInvocationKind::ExternalProcess {
            return Err(CheckError::CheckerEvidenceNotExternalInvocation {
                invocation_kind: self.invocation_kind,
            });
        }
        if self.stdout_sha256.is_none() {
            return Err(CheckError::MissingCheckerExternalProcessTranscriptDigest {
                field: "stdout_sha256".to_string(),
            });
        }
        if self.stderr_sha256.is_none() {
            return Err(CheckError::MissingCheckerExternalProcessTranscriptDigest {
                field: "stderr_sha256".to_string(),
            });
        }
        let transcript = self.external_process_transcript.as_ref().ok_or_else(|| {
            CheckError::MissingCheckerExternalProcessTranscriptDigest {
                field: "external_process_transcript".to_string(),
            }
        })?;
        transcript.validate_success()?;
        let transcript_invocation_sha256 = transcript.sha256()?;
        if transcript_invocation_sha256 != self.invocation_sha256 {
            return Err(binding_mismatch(
                "production_checker_evidence.invocation_sha256",
                self.invocation_sha256.as_str(),
                transcript_invocation_sha256.as_str(),
            ));
        }
        if transcript.stdout_sha256 != self.stdout_sha256 {
            return Err(binding_mismatch(
                "production_checker_evidence.stdout_sha256",
                format!("{:?}", self.stdout_sha256),
                format!("{:?}", transcript.stdout_sha256),
            ));
        }
        if transcript.stderr_sha256 != self.stderr_sha256 {
            return Err(binding_mismatch(
                "production_checker_evidence.stderr_sha256",
                format!("{:?}", self.stderr_sha256),
                format!("{:?}", transcript.stderr_sha256),
            ));
        }
        Ok(())
    }

    pub fn sha256(&self) -> Result<String, CheckError> {
        self.validate_structure()?;
        let bytes = serde_json::to_vec(self)
            .map_err(|err| CheckError::CheckerInternalError { reason: err.to_string() })?;
        Ok(stable_sha256_hex(&bytes))
    }

    fn validate_acceptance_parts(
        &self,
        checker_selection: &CheckedBinaryCertificateCheckerSelection,
        solver_proof_export: &CheckedBinaryCertificateSolverProofExportBinding,
        artifact_identity: &CheckedBinaryCertificateArtifactIdentity,
    ) -> Result<(), CheckError> {
        self.validate_production()?;
        if self.checker != checker_selection.checker {
            return Err(binding_mismatch(
                "production_checker_evidence.checker",
                checker_selection.checker.as_str(),
                self.checker.as_str(),
            ));
        }
        if self.checker_version != checker_selection.checker_version {
            return Err(binding_mismatch(
                "production_checker_evidence.checker_version",
                checker_selection.checker_version.as_str(),
                self.checker_version.as_str(),
            ));
        }
        if self.format != checker_selection.format {
            return Err(binding_mismatch(
                "production_checker_evidence.format",
                checker_selection.format.as_str(),
                self.format.as_str(),
            ));
        }
        if self.proof_export_sha256 != solver_proof_export.metadata_sha256 {
            return Err(binding_mismatch(
                "production_checker_evidence.proof_export_sha256",
                solver_proof_export.metadata_sha256.as_str(),
                self.proof_export_sha256.as_str(),
            ));
        }
        if self.certificate_sha256 != artifact_identity.certificate_sha256 {
            return Err(binding_mismatch(
                "production_checker_evidence.certificate_sha256",
                artifact_identity.certificate_sha256.as_str(),
                self.certificate_sha256.as_str(),
            ));
        }

        Ok(())
    }
}

impl CheckedBinaryCertificateSolverProofExportBinding {
    pub fn from_metadata(metadata: SolverProofExportMetadata) -> Result<Self, CheckError> {
        let metadata_sha256 = metadata.sha256()?;
        Ok(Self { metadata, metadata_sha256 })
    }

    pub fn validate_structure(&self) -> Result<(), CheckError> {
        self.metadata.validate_structure()?;
        validate_canonical_sha256_hex(
            "solver proof export binding metadata_sha256",
            &self.metadata_sha256,
        )?;
        let actual_metadata_sha256 = self.metadata.sha256()?;
        if self.metadata_sha256 != actual_metadata_sha256 {
            return Err(binding_mismatch(
                "solver_proof_export.metadata_sha256",
                actual_metadata_sha256,
                self.metadata_sha256.as_str(),
            ));
        }

        Ok(())
    }

    fn validate_manifest_entry(
        &self,
        entry: &CheckedBinaryCertificateManifestEntry,
    ) -> Result<(), CheckError> {
        self.validate_structure()?;
        if self.metadata.dispatch_id != entry.dispatch_id {
            return Err(binding_mismatch(
                "solver_proof_export.dispatch_id",
                entry.dispatch_id.as_str(),
                self.metadata.dispatch_id.as_str(),
            ));
        }
        if self.metadata.vc_sha256 != entry.vc_sha256 {
            return Err(binding_mismatch(
                "solver_proof_export.vc_sha256",
                entry.vc_sha256.as_str(),
                self.metadata.vc_sha256.as_str(),
            ));
        }
        if self.metadata.proof_sha256 != entry.proof_sha256 {
            return Err(binding_mismatch(
                "solver_proof_export.proof_sha256",
                entry.proof_sha256.as_str(),
                self.metadata.proof_sha256.as_str(),
            ));
        }
        if self.metadata_sha256 != entry.proof_export_sha256 {
            return Err(binding_mismatch(
                "solver_proof_export.metadata_sha256",
                entry.proof_export_sha256.as_str(),
                self.metadata_sha256.as_str(),
            ));
        }
        if self.metadata.format != entry.format {
            return Err(binding_mismatch(
                "solver_proof_export.format",
                entry.format.as_str(),
                self.metadata.format.as_str(),
            ));
        }
        if self.metadata.assumption_digest != entry.assumption_digest {
            return Err(CheckError::AssumptionDigestMismatch {
                expected: entry.assumption_digest.clone(),
                actual: self.metadata.assumption_digest.clone(),
            });
        }

        Ok(())
    }

    fn validate_artifact(
        &self,
        artifact: &CheckedBinaryCertificateArtifact,
    ) -> Result<(), CheckError> {
        if self.metadata.vc_sha256 != artifact.vc_sha256 {
            return Err(binding_mismatch(
                "solver_proof_export.vc_sha256",
                artifact.vc_sha256.as_str(),
                self.metadata.vc_sha256.as_str(),
            ));
        }
        if self.metadata.proof_sha256 != artifact.proof_sha256 {
            return Err(binding_mismatch(
                "solver_proof_export.proof_sha256",
                artifact.proof_sha256.as_str(),
                self.metadata.proof_sha256.as_str(),
            ));
        }
        if self.metadata_sha256 != artifact.proof_export_sha256 {
            return Err(binding_mismatch(
                "solver_proof_export.metadata_sha256",
                artifact.proof_export_sha256.as_str(),
                self.metadata_sha256.as_str(),
            ));
        }
        if self.metadata.format != artifact.format {
            return Err(binding_mismatch(
                "solver_proof_export.format",
                artifact.format.as_str(),
                self.metadata.format.as_str(),
            ));
        }
        if self.metadata.query_semantics != artifact.query_semantics {
            return Err(binding_mismatch(
                "solver_proof_export.query_semantics",
                format!("{:?}", artifact.query_semantics),
                format!("{:?}", self.metadata.query_semantics),
            ));
        }
        if self.metadata.assumption_digest != artifact.assumption_digest {
            return Err(CheckError::AssumptionDigestMismatch {
                expected: artifact.assumption_digest.clone(),
                actual: self.metadata.assumption_digest.clone(),
            });
        }

        let payload = normalized_payload_metadata(&artifact.normalized_payload)?;
        if payload.proof_export != self.metadata {
            return Err(binding_mismatch(
                "solver_proof_export.metadata",
                self.metadata_sha256.as_str(),
                payload.proof_export.sha256()?,
            ));
        }

        Ok(())
    }
}

impl CheckedBinaryCertificateReplayTranscriptBinding {
    #[must_use]
    pub fn from_manifest_entry(entry: &CheckedBinaryCertificateManifestEntry) -> Self {
        Self {
            replay: entry.replay,
            replay_transcript_digest: entry.replay_transcript_digest.clone(),
        }
    }

    pub fn validate_structure(&self) -> Result<(), CheckError> {
        if let Some(replay_transcript_digest) = self.replay_transcript_digest.as_deref() {
            validate_canonical_sha256_hex(
                "replay transcript binding replay_transcript_digest",
                replay_transcript_digest,
            )?;
        }

        Ok(())
    }

    fn validate_manifest_entry(
        &self,
        entry: &CheckedBinaryCertificateManifestEntry,
    ) -> Result<(), CheckError> {
        self.validate_structure()?;
        if self.replay != entry.replay {
            return Err(binding_mismatch(
                "replay_transcript.replay",
                format!("{:?}", entry.replay),
                format!("{:?}", self.replay),
            ));
        }
        if self.replay_transcript_digest != entry.replay_transcript_digest {
            return Err(CheckError::ReplayDigestMismatch {
                expected: entry
                    .replay_transcript_digest
                    .as_deref()
                    .unwrap_or("<missing>")
                    .to_string(),
                actual: self.replay_transcript_digest.as_deref().unwrap_or("<missing>").to_string(),
            });
        }

        Ok(())
    }

    fn validate_artifact(
        &self,
        artifact: &CheckedBinaryCertificateArtifact,
    ) -> Result<(), CheckError> {
        if self.replay != artifact.replay {
            return Err(binding_mismatch(
                "replay_transcript.replay",
                format!("{:?}", artifact.replay),
                format!("{:?}", self.replay),
            ));
        }
        if self.replay_transcript_digest != artifact.replay_transcript_digest {
            return Err(CheckError::ReplayDigestMismatch {
                expected: artifact
                    .replay_transcript_digest
                    .as_deref()
                    .unwrap_or("<missing>")
                    .to_string(),
                actual: self.replay_transcript_digest.as_deref().unwrap_or("<missing>").to_string(),
            });
        }

        Ok(())
    }
}

fn default_source_backpropagation_gate_schema_version() -> String {
    CHECKED_BINARY_CERTIFICATE_SOURCE_BACKPROPAGATION_GATE_SCHEMA_VERSION.to_string()
}

fn is_zero_usize(value: &usize) -> bool {
    *value == 0
}

fn is_false(value: &bool) -> bool {
    !*value
}

impl Default for CheckedBinaryCertificateSourceBackpropagationGate {
    fn default() -> Self {
        Self {
            schema_version: default_source_backpropagation_gate_schema_version(),
            replay_grade_artifact_identity: false,
            checked_certificate_identity: false,
            exact_replay_identity: false,
            accepted_reconstruction_validation: false,
            accepted_target_validation: false,
            exact_source_provenance: false,
            source_provenance: BinarySourceProvenanceSummary::default(),
            unsupported_ledger_summary: UnsupportedLedgerSummary::default(),
            preserved_symbolic_formulas: 0,
            symbolic_formula_consumer_accepted: false,
            source_backpropagation_allowed: false,
            blockers: vec!["source_backpropagation_gate_not_evaluated".to_string()],
        }
    }
}

impl CheckedBinaryCertificateSourceBackpropagationGate {
    #[must_use]
    pub fn closed_with_blockers<I, S>(
        source_provenance: BinarySourceProvenanceSummary,
        blockers: I,
    ) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        Self {
            source_provenance,
            blockers: blockers.into_iter().map(Into::into).collect(),
            ..Self::default()
        }
    }

    #[must_use]
    pub fn evaluated(
        source_provenance: BinarySourceProvenanceSummary,
        replay_grade_artifact_identity: bool,
        checked_certificate_identity: bool,
        exact_replay_identity: bool,
        accepted_reconstruction_validation: bool,
        accepted_target_validation: bool,
        exact_source_provenance: bool,
    ) -> Self {
        let mut gate = Self {
            replay_grade_artifact_identity,
            checked_certificate_identity,
            exact_replay_identity,
            accepted_reconstruction_validation,
            accepted_target_validation,
            exact_source_provenance,
            source_provenance,
            source_backpropagation_allowed: false,
            blockers: Vec::new(),
            ..Self::default()
        };
        gate.blockers = gate.prerequisite_blockers();
        gate.source_backpropagation_allowed = gate.blockers.is_empty();
        gate
    }

    /// Attach unsupported-ledger elimination evidence and re-evaluate the gate.
    ///
    /// A non-empty summary means unsupported rows are still unconsumed, so
    /// source backpropagation remains closed even when the other prerequisites
    /// are present.
    #[must_use]
    pub fn with_unsupported_ledger_summary(
        mut self,
        unsupported_ledger_summary: UnsupportedLedgerSummary,
    ) -> Self {
        self.unsupported_ledger_summary = unsupported_ledger_summary;
        self.blockers = self.prerequisite_blockers();
        self.source_backpropagation_allowed = self.blockers.is_empty();
        self
    }

    /// Attach target proof-consumer evidence for preserved symbolic formulas.
    ///
    /// Preserved `trust_symbolic.formula` payloads are proof obligations until
    /// target semantics explicitly consumes them. A non-zero count without
    /// accepted consumer evidence keeps source backpropagation closed.
    #[must_use]
    pub fn with_symbolic_formula_consumer_evidence(
        mut self,
        preserved_symbolic_formulas: usize,
        symbolic_formula_consumer_accepted: bool,
    ) -> Self {
        self.preserved_symbolic_formulas = preserved_symbolic_formulas;
        self.symbolic_formula_consumer_accepted = symbolic_formula_consumer_accepted;
        self.blockers = self.prerequisite_blockers();
        self.source_backpropagation_allowed = self.blockers.is_empty();
        self
    }

    #[must_use]
    pub fn is_closed_default(&self) -> bool {
        self == &Self::default()
    }

    #[must_use]
    pub fn prerequisite_blockers(&self) -> Vec<String> {
        let mut blockers = Vec::new();
        if !self.replay_grade_artifact_identity {
            blockers.push("replay_grade_artifact_identity_missing".to_string());
        }
        if !self.checked_certificate_identity {
            blockers.push("checked_certificate_identity_missing".to_string());
        }
        if !self.exact_replay_identity {
            blockers.push("exact_replay_identity_missing".to_string());
        }
        if !self.accepted_reconstruction_validation {
            blockers.push("accepted_reconstruction_validation_missing".to_string());
        }
        if !self.accepted_target_validation {
            blockers.push("accepted_target_validation_missing".to_string());
        }
        if !self.exact_source_provenance {
            blockers.push("exact_source_provenance_missing".to_string());
        }
        if !self.source_provenance.effective_source_backpropagation_allowed() {
            blockers.push("source_provenance_not_effective".to_string());
        }
        if !self.unsupported_ledger_summary.is_empty() {
            blockers.push("unsupported_ledger_entries_unconsumed".to_string());
        }
        if self.preserved_symbolic_formulas > 0 && !self.symbolic_formula_consumer_accepted {
            blockers.push("trust_symbolic_formula_entries_unconsumed".to_string());
        }
        blockers
    }

    pub fn validate_structure(&self) -> Result<(), CheckError> {
        if self.schema_version
            != CHECKED_BINARY_CERTIFICATE_SOURCE_BACKPROPAGATION_GATE_SCHEMA_VERSION
        {
            return Err(binding_mismatch(
                "source_backpropagation_gate.schema_version",
                CHECKED_BINARY_CERTIFICATE_SOURCE_BACKPROPAGATION_GATE_SCHEMA_VERSION,
                self.schema_version.as_str(),
            ));
        }

        if self.source_backpropagation_allowed {
            let blockers = self.prerequisite_blockers();
            if !blockers.is_empty() {
                return Err(CheckError::SourceBackpropagationGateIncomplete {
                    reason: blockers.join("; "),
                });
            }
            if !self.blockers.is_empty() {
                return Err(CheckError::SourceBackpropagationGateIncomplete {
                    reason: format!(
                        "source_backpropagation_allowed=true but blockers remain: {}",
                        self.blockers.join("; ")
                    ),
                });
            }
        }

        Ok(())
    }

    fn validate_acceptance_parts(
        &self,
        production_checker_evidence: &CheckedBinaryCertificateProductionCheckerEvidence,
        replay_transcript: &CheckedBinaryCertificateReplayTranscriptBinding,
        artifact_identity: &CheckedBinaryCertificateArtifactIdentity,
    ) -> Result<(), CheckError> {
        self.validate_replay_artifact_identity(replay_transcript, artifact_identity)?;
        if !self.source_backpropagation_allowed {
            return Ok(());
        }

        production_checker_evidence.validate_production()?;
        if production_checker_evidence.certificate_sha256 != artifact_identity.certificate_sha256 {
            return Err(binding_mismatch(
                "source_backpropagation_gate.certificate_sha256",
                artifact_identity.certificate_sha256.as_str(),
                production_checker_evidence.certificate_sha256.as_str(),
            ));
        }
        if production_checker_evidence.proof_export_sha256 != artifact_identity.proof_export_sha256
        {
            return Err(binding_mismatch(
                "source_backpropagation_gate.proof_export_sha256",
                artifact_identity.proof_export_sha256.as_str(),
                production_checker_evidence.proof_export_sha256.as_str(),
            ));
        }
        validate_canonical_sha256_hex(
            "source_backpropagation_gate production checker evidence sha256",
            &production_checker_evidence.sha256()?,
        )?;

        Ok(())
    }

    fn validate_replay_artifact_identity(
        &self,
        replay_transcript: &CheckedBinaryCertificateReplayTranscriptBinding,
        artifact_identity: &CheckedBinaryCertificateArtifactIdentity,
    ) -> Result<(), CheckError> {
        self.validate_structure()?;
        if !self.source_backpropagation_allowed {
            return Ok(());
        }

        if !artifact_identity.binary_artifact_digest_identity.digest_identity_allows_replay() {
            return Err(CheckError::SourceBackpropagationGateIncomplete {
                reason: artifact_identity
                    .binary_artifact_digest_identity
                    .digest_identity_blockers()
                    .join("; "),
            });
        }
        if replay_transcript.replay != ReplayStatus::Replayed {
            return Err(CheckError::SourceBackpropagationGateIncomplete {
                reason: "exact replay identity requires replay=Replayed".to_string(),
            });
        }
        if replay_transcript.replay_transcript_digest.is_none() {
            return Err(CheckError::SourceBackpropagationGateIncomplete {
                reason: "exact replay identity requires replay transcript digest".to_string(),
            });
        }
        validate_canonical_sha256_hex(
            "source_backpropagation_gate checked certificate sha256",
            &artifact_identity.certificate_sha256,
        )?;

        Ok(())
    }
}

impl CheckedBinaryCertificateArtifactIdentity {
    #[must_use]
    pub fn from_manifest_entry(entry: &CheckedBinaryCertificateManifestEntry) -> Self {
        Self {
            dispatch_id: entry.dispatch_id.clone(),
            vc_sha256: entry.vc_sha256.clone(),
            origin_sha256: entry.origin_sha256.clone(),
            proof_sha256: entry.proof_sha256.clone(),
            proof_export_sha256: entry.proof_export_sha256.clone(),
            certificate_sha256: entry.certificate_sha256.clone(),
            content_sha256: entry.certificate_sha256.clone(),
            certificate_path: entry.certificate_path.clone(),
            binary_artifact_digest_identity: entry.binary_artifact_digest_identity.clone(),
        }
    }

    pub fn validate_structure(&self) -> Result<(), CheckError> {
        if self.dispatch_id.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "artifact identity is missing dispatch id".to_string(),
            });
        }
        validate_canonical_sha256_hex("artifact identity vc_sha256", &self.vc_sha256)?;
        validate_canonical_sha256_hex("artifact identity origin_sha256", &self.origin_sha256)?;
        validate_canonical_sha256_hex("artifact identity proof_sha256", &self.proof_sha256)?;
        validate_canonical_sha256_hex(
            "artifact identity proof_export_sha256",
            &self.proof_export_sha256,
        )?;
        validate_canonical_sha256_hex(
            "artifact identity certificate_sha256",
            &self.certificate_sha256,
        )?;
        validate_canonical_sha256_hex("artifact identity content_sha256", &self.content_sha256)?;
        if self.content_sha256 != self.certificate_sha256 {
            return Err(binding_mismatch(
                "artifact_identity.content_sha256",
                self.certificate_sha256.as_str(),
                self.content_sha256.as_str(),
            ));
        }
        validate_relative_manifest_path(
            "artifact identity certificate_path",
            &self.certificate_path,
        )?;
        validate_manifest_certificate_path_matches_digest(
            "artifact identity certificate_path",
            &self.certificate_path,
            &self.certificate_sha256,
        )?;
        validate_binary_artifact_digest_identity(&self.binary_artifact_digest_identity)?;

        Ok(())
    }

    fn artifact_ref(
        &self,
        root: impl AsRef<Path>,
    ) -> Result<CheckedBinaryCertificateArtifactRef, CheckError> {
        self.validate_structure()?;
        Ok(CheckedBinaryCertificateArtifactRef {
            content_sha256: self.content_sha256.clone(),
            path: root.as_ref().join(&self.certificate_path),
        })
    }

    fn validate_manifest_entry(
        &self,
        entry: &CheckedBinaryCertificateManifestEntry,
    ) -> Result<(), CheckError> {
        self.validate_structure()?;
        if self.dispatch_id != entry.dispatch_id {
            return Err(binding_mismatch(
                "artifact_identity.dispatch_id",
                entry.dispatch_id.as_str(),
                self.dispatch_id.as_str(),
            ));
        }
        if self.vc_sha256 != entry.vc_sha256 {
            return Err(binding_mismatch(
                "artifact_identity.vc_sha256",
                entry.vc_sha256.as_str(),
                self.vc_sha256.as_str(),
            ));
        }
        if self.origin_sha256 != entry.origin_sha256 {
            return Err(binding_mismatch(
                "artifact_identity.origin_sha256",
                entry.origin_sha256.as_str(),
                self.origin_sha256.as_str(),
            ));
        }
        if self.proof_sha256 != entry.proof_sha256 {
            return Err(binding_mismatch(
                "artifact_identity.proof_sha256",
                entry.proof_sha256.as_str(),
                self.proof_sha256.as_str(),
            ));
        }
        if self.proof_export_sha256 != entry.proof_export_sha256 {
            return Err(binding_mismatch(
                "artifact_identity.proof_export_sha256",
                entry.proof_export_sha256.as_str(),
                self.proof_export_sha256.as_str(),
            ));
        }
        if self.certificate_sha256 != entry.certificate_sha256 {
            return Err(binding_mismatch(
                "artifact_identity.certificate_sha256",
                entry.certificate_sha256.as_str(),
                self.certificate_sha256.as_str(),
            ));
        }
        if self.content_sha256 != entry.certificate_sha256 {
            return Err(binding_mismatch(
                "artifact_identity.content_sha256",
                entry.certificate_sha256.as_str(),
                self.content_sha256.as_str(),
            ));
        }
        if self.certificate_path != entry.certificate_path {
            return Err(binding_mismatch(
                "artifact_identity.certificate_path",
                entry.certificate_path.display().to_string(),
                self.certificate_path.display().to_string(),
            ));
        }
        if self.binary_artifact_digest_identity != entry.binary_artifact_digest_identity {
            return Err(binding_mismatch(
                "artifact_identity.binary_artifact_digest_identity",
                binary_artifact_digest_identity_label(&entry.binary_artifact_digest_identity)?,
                binary_artifact_digest_identity_label(&self.binary_artifact_digest_identity)?,
            ));
        }

        Ok(())
    }

    fn validate_artifact(
        &self,
        artifact: &CheckedBinaryCertificateArtifact,
    ) -> Result<(), CheckError> {
        if self.dispatch_id != artifact.dispatch_id {
            return Err(binding_mismatch(
                "artifact_identity.dispatch_id",
                artifact.dispatch_id.as_str(),
                self.dispatch_id.as_str(),
            ));
        }
        if self.vc_sha256 != artifact.vc_sha256 {
            return Err(binding_mismatch(
                "artifact_identity.vc_sha256",
                artifact.vc_sha256.as_str(),
                self.vc_sha256.as_str(),
            ));
        }
        if self.origin_sha256 != artifact.origin_sha256 {
            return Err(binding_mismatch(
                "artifact_identity.origin_sha256",
                artifact.origin_sha256.as_str(),
                self.origin_sha256.as_str(),
            ));
        }
        if self.proof_sha256 != artifact.proof_sha256 {
            return Err(binding_mismatch(
                "artifact_identity.proof_sha256",
                artifact.proof_sha256.as_str(),
                self.proof_sha256.as_str(),
            ));
        }
        if self.proof_export_sha256 != artifact.proof_export_sha256 {
            return Err(binding_mismatch(
                "artifact_identity.proof_export_sha256",
                artifact.proof_export_sha256.as_str(),
                self.proof_export_sha256.as_str(),
            ));
        }
        if self.certificate_sha256 != artifact.certificate_sha256 {
            return Err(binding_mismatch(
                "artifact_identity.certificate_sha256",
                artifact.certificate_sha256.as_str(),
                self.certificate_sha256.as_str(),
            ));
        }
        if self.content_sha256 != artifact.certificate_sha256 {
            return Err(binding_mismatch(
                "artifact_identity.content_sha256",
                artifact.certificate_sha256.as_str(),
                self.content_sha256.as_str(),
            ));
        }
        if self.binary_artifact_digest_identity != artifact.binary_artifact_digest_identity {
            return Err(binding_mismatch(
                "artifact_identity.binary_artifact_digest_identity",
                binary_artifact_digest_identity_label(&artifact.binary_artifact_digest_identity)?,
                binary_artifact_digest_identity_label(&self.binary_artifact_digest_identity)?,
            ));
        }

        Ok(())
    }
}

impl CheckedBinaryCertificateManifestIdentityEntry {
    pub fn from_acceptance_record(
        record: &CheckedBinaryCertificateManifestAcceptanceRecord,
    ) -> Result<Self, CheckError> {
        record.validate_structure()?;
        let production_checker_evidence = record
            .production_checker_evidence
            .as_ref()
            .ok_or(CheckError::MissingProductionCheckerEvidence)?;
        Ok(Self {
            schema_version: CHECKED_BINARY_CERTIFICATE_MANIFEST_IDENTITY_SCHEMA_VERSION.to_string(),
            manifest_schema_version: record.manifest_schema_version.clone(),
            checker_selection: record.checker_selection.clone(),
            replay_transcript: record.replay_transcript.clone(),
            artifact_identity: record.artifact_identity.clone(),
            production_checker_evidence_sha256: production_checker_evidence.sha256()?,
            source_backpropagation_gate: record.source_backpropagation_gate.clone(),
        })
    }

    pub fn validate_structure(&self) -> Result<(), CheckError> {
        if self.schema_version != CHECKED_BINARY_CERTIFICATE_MANIFEST_IDENTITY_SCHEMA_VERSION {
            return Err(binding_mismatch(
                "checked_certificate_manifest_identity.schema_version",
                CHECKED_BINARY_CERTIFICATE_MANIFEST_IDENTITY_SCHEMA_VERSION,
                self.schema_version.as_str(),
            ));
        }
        if self.manifest_schema_version != CHECKED_BINARY_CERTIFICATE_MANIFEST_SCHEMA_VERSION {
            return Err(binding_mismatch(
                "checked_certificate_manifest_identity.manifest_schema_version",
                CHECKED_BINARY_CERTIFICATE_MANIFEST_SCHEMA_VERSION,
                self.manifest_schema_version.as_str(),
            ));
        }
        self.checker_selection.validate_structure()?;
        self.replay_transcript.validate_structure()?;
        self.artifact_identity.validate_structure()?;
        self.source_backpropagation_gate.validate_structure()?;
        validate_canonical_sha256_hex(
            "checked certificate manifest identity production_checker_evidence_sha256",
            &self.production_checker_evidence_sha256,
        )?;

        Ok(())
    }

    pub fn sha256(&self) -> Result<String, CheckError> {
        self.validate_structure()?;
        serde_json::to_vec(self)
            .map(|bytes| stable_sha256_hex(&bytes))
            .map_err(|err| CheckError::CheckerInternalError { reason: err.to_string() })
    }

    pub fn validate_dispatch_bindings(
        &self,
        dispatch: &SolverDispatchRecord,
    ) -> Result<(), CheckError> {
        self.validate_structure()?;
        let ProofCertificateStatus::Checked { checker: _, format, sha256 } = &dispatch.certificate
        else {
            return Err(CheckError::MalformedProof {
                reason: "checked certificate manifest identity requires checked certificate status"
                    .to_string(),
            });
        };
        if format != &self.checker_selection.format {
            return Err(binding_mismatch(
                "checked_certificate_manifest_identity.format",
                self.checker_selection.format.as_str(),
                format.as_str(),
            ));
        }
        if sha256.as_deref() != Some(self.artifact_identity.certificate_sha256.as_str()) {
            return Err(binding_mismatch(
                "checked_certificate_manifest_identity.certificate_sha256",
                self.artifact_identity.certificate_sha256.as_str(),
                sha256.as_deref().unwrap_or("<missing>"),
            ));
        }

        let production_checker_evidence = dispatch
            .certificate
            .production_checker_evidence()
            .ok_or(CheckError::MissingProductionCheckerEvidence)?;
        if production_checker_evidence.checker != self.checker_selection.checker {
            return Err(binding_mismatch(
                "checked_certificate_manifest_identity.checker",
                self.checker_selection.checker.as_str(),
                production_checker_evidence.checker.as_str(),
            ));
        }
        if production_checker_evidence.checker_version != self.checker_selection.checker_version {
            return Err(binding_mismatch(
                "checked_certificate_manifest_identity.checker_version",
                self.checker_selection.checker_version.as_str(),
                production_checker_evidence.checker_version.as_str(),
            ));
        }
        if production_checker_evidence.production_checker_evidence_sha256
            != self.production_checker_evidence_sha256
        {
            return Err(binding_mismatch(
                "checked_certificate_manifest_identity.production_checker_evidence_sha256",
                self.production_checker_evidence_sha256.as_str(),
                production_checker_evidence.production_checker_evidence_sha256.as_str(),
            ));
        }
        self.source_backpropagation_gate
            .validate_replay_artifact_identity(&self.replay_transcript, &self.artifact_identity)?;

        if dispatch.replay != self.replay_transcript.replay {
            return Err(binding_mismatch(
                "checked_certificate_manifest_identity.replay",
                format!("{:?}", self.replay_transcript.replay),
                format!("{:?}", dispatch.replay),
            ));
        }

        if let Some(origin) = &dispatch.origin {
            let origin_sha256 = digest_binary_origin(origin)?;
            if origin_sha256 != self.artifact_identity.origin_sha256 {
                return Err(binding_mismatch(
                    "checked_certificate_manifest_identity.origin_sha256",
                    self.artifact_identity.origin_sha256.as_str(),
                    origin_sha256,
                ));
            }
        }

        let identity = dispatch.binary_artifact_digest_identity.as_ref().ok_or_else(|| {
            CheckError::BinaryArtifactDigestIdentityInvalid {
                reason: "missing dispatch binary artifact digest identity".to_string(),
            }
        })?;
        validate_binary_artifact_digest_identity(identity)?;
        if identity != &self.artifact_identity.binary_artifact_digest_identity {
            return Err(binding_mismatch(
                "checked_certificate_manifest_identity.binary_artifact_digest_identity",
                binary_artifact_digest_identity_label(
                    &self.artifact_identity.binary_artifact_digest_identity,
                )?,
                binary_artifact_digest_identity_label(identity)?,
            ));
        }

        Ok(())
    }

    pub fn to_dispatch_diagnostic(&self) -> Result<String, CheckError> {
        self.validate_structure()?;
        let json = serde_json::to_string(self)
            .map_err(|err| CheckError::CheckerInternalError { reason: err.to_string() })?;
        Ok(format!("{CHECKED_BINARY_CERTIFICATE_MANIFEST_IDENTITY_DIAGNOSTIC_PREFIX}{json}"))
    }
}

pub(crate) fn checked_certificate_manifest_identity_failures(
    dispatch: &SolverDispatchRecord,
) -> Vec<String> {
    match checked_certificate_manifest_identity_entry(dispatch) {
        Ok(_) => Vec::new(),
        Err(reason) => vec![reason],
    }
}

pub(crate) fn checked_certificate_manifest_identity_entry(
    dispatch: &SolverDispatchRecord,
) -> Result<Option<CheckedBinaryCertificateManifestIdentityEntry>, String> {
    if !matches!(dispatch.certificate, ProofCertificateStatus::Checked { .. }) {
        return Ok(None);
    }

    let diagnostics = dispatch
        .diagnostics
        .iter()
        .filter_map(|diagnostic| {
            diagnostic.strip_prefix(CHECKED_BINARY_CERTIFICATE_MANIFEST_IDENTITY_DIAGNOSTIC_PREFIX)
        })
        .collect::<Vec<_>>();

    match diagnostics.as_slice() {
        [] => Err("missing manifest-backed checked certificate identity".to_string()),
        [json] => {
            let identity =
                serde_json::from_str::<CheckedBinaryCertificateManifestIdentityEntry>(json)
                    .map_err(|err| {
                        format!("checked certificate manifest identity is malformed: {err}")
                    })?;
            identity.validate_dispatch_bindings(dispatch).map_err(|err| err.to_string())?;
            Ok(Some(identity))
        }
        _ => Err("multiple manifest-backed checked certificate identities".to_string()),
    }
}

fn set_checked_certificate_manifest_identity_diagnostic(
    dispatch: &mut SolverDispatchRecord,
    record: &CheckedBinaryCertificateManifestAcceptanceRecord,
) -> Result<(), CheckError> {
    let diagnostic = CheckedBinaryCertificateManifestIdentityEntry::from_acceptance_record(record)?
        .to_dispatch_diagnostic()?;
    dispatch.diagnostics.retain(|diagnostic| {
        !diagnostic.starts_with(CHECKED_BINARY_CERTIFICATE_MANIFEST_IDENTITY_DIAGNOSTIC_PREFIX)
    });
    dispatch.diagnostics.push(diagnostic);
    Ok(())
}

impl CheckedBinaryCertificateManifestAcceptanceRequest {
    pub fn from_manifest_entry_and_solver_proof_export_metadata(
        entry: &CheckedBinaryCertificateManifestEntry,
        metadata: SolverProofExportMetadata,
    ) -> Result<Self, CheckError> {
        Ok(Self {
            schema_version: CHECKED_BINARY_CERTIFICATE_ACCEPTANCE_SCHEMA_VERSION.to_string(),
            checker_selection: CheckedBinaryCertificateCheckerSelection::from_manifest_entry(entry),
            production_checker_evidence: None,
            solver_proof_export: CheckedBinaryCertificateSolverProofExportBinding::from_metadata(
                metadata,
            )?,
            replay_transcript: CheckedBinaryCertificateReplayTranscriptBinding::from_manifest_entry(
                entry,
            ),
            artifact_identity: CheckedBinaryCertificateArtifactIdentity::from_manifest_entry(entry),
            source_backpropagation_gate: CheckedBinaryCertificateSourceBackpropagationGate::default(
            ),
        })
    }

    pub fn with_production_checker_evidence(
        mut self,
        evidence: CheckedBinaryCertificateProductionCheckerEvidence,
    ) -> Result<Self, CheckError> {
        self.production_checker_evidence = Some(evidence);
        self.validate_structure()?;
        Ok(self)
    }

    pub fn with_source_backpropagation_gate(
        mut self,
        gate: CheckedBinaryCertificateSourceBackpropagationGate,
    ) -> Result<Self, CheckError> {
        self.source_backpropagation_gate = gate;
        self.validate_structure()?;
        Ok(self)
    }

    pub fn validate_structure(&self) -> Result<(), CheckError> {
        if self.schema_version != CHECKED_BINARY_CERTIFICATE_ACCEPTANCE_SCHEMA_VERSION {
            return Err(binding_mismatch(
                "acceptance.schema_version",
                CHECKED_BINARY_CERTIFICATE_ACCEPTANCE_SCHEMA_VERSION,
                self.schema_version.as_str(),
            ));
        }
        self.checker_selection.validate_structure()?;
        self.solver_proof_export.validate_structure()?;
        self.replay_transcript.validate_structure()?;
        self.artifact_identity.validate_structure()?;
        let production_checker_evidence = self
            .production_checker_evidence
            .as_ref()
            .ok_or(CheckError::MissingProductionCheckerEvidence)?;
        production_checker_evidence.validate_acceptance_parts(
            &self.checker_selection,
            &self.solver_proof_export,
            &self.artifact_identity,
        )?;
        self.source_backpropagation_gate.validate_acceptance_parts(
            production_checker_evidence,
            &self.replay_transcript,
            &self.artifact_identity,
        )?;
        Ok(())
    }

    fn validate_manifest_entry(
        &self,
        entry: &CheckedBinaryCertificateManifestEntry,
    ) -> Result<(), CheckError> {
        self.validate_structure()?;
        entry.validate_structure()?;
        self.checker_selection.validate_manifest_entry(entry)?;
        self.solver_proof_export.validate_manifest_entry(entry)?;
        self.replay_transcript.validate_manifest_entry(entry)?;
        self.artifact_identity.validate_manifest_entry(entry)?;
        Ok(())
    }

    fn validate_artifact(
        &self,
        artifact: &CheckedBinaryCertificateArtifact,
    ) -> Result<(), CheckError> {
        artifact.validate_integrity()?;
        self.checker_selection.validate_artifact(artifact)?;
        self.solver_proof_export.validate_artifact(artifact)?;
        self.replay_transcript.validate_artifact(artifact)?;
        self.artifact_identity.validate_artifact(artifact)?;
        Ok(())
    }

    fn validate_canonical_vc_bytes(&self, canonical_vc_bytes: &[u8]) -> Result<(), CheckError> {
        let actual_vc_sha256 = stable_sha256_hex(canonical_vc_bytes);
        if self.artifact_identity.vc_sha256 != actual_vc_sha256 {
            return Err(CheckError::VcDigestMismatch {
                expected: self.artifact_identity.vc_sha256.clone(),
                actual: actual_vc_sha256,
            });
        }
        if self.solver_proof_export.metadata.vc_sha256 != self.artifact_identity.vc_sha256 {
            return Err(binding_mismatch(
                "solver_proof_export.vc_sha256",
                self.artifact_identity.vc_sha256.as_str(),
                self.solver_proof_export.metadata.vc_sha256.as_str(),
            ));
        }

        Ok(())
    }

    fn acceptance_record(&self) -> CheckedBinaryCertificateManifestAcceptanceRecord {
        CheckedBinaryCertificateManifestAcceptanceRecord {
            schema_version: CHECKED_BINARY_CERTIFICATE_ACCEPTANCE_SCHEMA_VERSION.to_string(),
            manifest_schema_version: CHECKED_BINARY_CERTIFICATE_MANIFEST_SCHEMA_VERSION.to_string(),
            checker_selection: self.checker_selection.clone(),
            production_checker_evidence: self.production_checker_evidence.clone(),
            solver_proof_export: self.solver_proof_export.clone(),
            replay_transcript: self.replay_transcript.clone(),
            artifact_identity: self.artifact_identity.clone(),
            source_backpropagation_gate: self.source_backpropagation_gate.clone(),
        }
    }
}

impl CheckedBinaryCertificateManifestAcceptanceRecord {
    pub fn validate_structure(&self) -> Result<(), CheckError> {
        if self.schema_version != CHECKED_BINARY_CERTIFICATE_ACCEPTANCE_SCHEMA_VERSION {
            return Err(binding_mismatch(
                "acceptance_record.schema_version",
                CHECKED_BINARY_CERTIFICATE_ACCEPTANCE_SCHEMA_VERSION,
                self.schema_version.as_str(),
            ));
        }
        if self.manifest_schema_version != CHECKED_BINARY_CERTIFICATE_MANIFEST_SCHEMA_VERSION {
            return Err(binding_mismatch(
                "acceptance_record.manifest_schema_version",
                CHECKED_BINARY_CERTIFICATE_MANIFEST_SCHEMA_VERSION,
                self.manifest_schema_version.as_str(),
            ));
        }
        self.checker_selection.validate_structure()?;
        let production_checker_evidence = self
            .production_checker_evidence
            .as_ref()
            .ok_or(CheckError::MissingProductionCheckerEvidence)?;
        self.solver_proof_export.validate_structure()?;
        self.replay_transcript.validate_structure()?;
        self.artifact_identity.validate_structure()?;
        production_checker_evidence.validate_acceptance_parts(
            &self.checker_selection,
            &self.solver_proof_export,
            &self.artifact_identity,
        )?;
        self.source_backpropagation_gate.validate_acceptance_parts(
            production_checker_evidence,
            &self.replay_transcript,
            &self.artifact_identity,
        )?;
        Ok(())
    }

    pub fn validate_manifest_entry(
        &self,
        entry: &CheckedBinaryCertificateManifestEntry,
    ) -> Result<(), CheckError> {
        self.validate_structure()?;
        entry.validate_structure()?;
        self.checker_selection.validate_manifest_entry(entry)?;
        self.solver_proof_export.validate_manifest_entry(entry)?;
        self.replay_transcript.validate_manifest_entry(entry)?;
        self.artifact_identity.validate_manifest_entry(entry)?;
        Ok(())
    }

    pub fn to_acceptance_request(
        &self,
    ) -> Result<CheckedBinaryCertificateManifestAcceptanceRequest, CheckError> {
        self.validate_structure()?;
        Ok(CheckedBinaryCertificateManifestAcceptanceRequest {
            schema_version: self.schema_version.clone(),
            checker_selection: self.checker_selection.clone(),
            production_checker_evidence: self.production_checker_evidence.clone(),
            solver_proof_export: self.solver_proof_export.clone(),
            replay_transcript: self.replay_transcript.clone(),
            artifact_identity: self.artifact_identity.clone(),
            source_backpropagation_gate: self.source_backpropagation_gate.clone(),
        })
    }

    pub fn proof_certificate_status(&self) -> Result<ProofCertificateStatus, CheckError> {
        self.validate_structure()?;
        let evidence = self
            .production_checker_evidence
            .as_ref()
            .ok_or(CheckError::MissingProductionCheckerEvidence)?;
        Ok(ProofCertificateStatus::Checked {
            checker: production_checked_certificate_checker_status(
                &self.checker_selection.checker,
                &self.checker_selection.checker_version,
                &evidence.sha256()?,
            )?,
            format: self.checker_selection.format.clone(),
            sha256: Some(self.artifact_identity.certificate_sha256.clone()),
        })
    }

    pub fn to_json(&self) -> Result<String, crate::CertError> {
        self.validate_structure()
            .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
        serde_json::to_string_pretty(self)
            .map_err(|err| crate::CertError::SerializationFailed { reason: err.to_string() })
    }

    pub fn from_json(json: &str) -> Result<Self, crate::CertError> {
        let record: Self = serde_json::from_str(json)
            .map_err(|err| crate::CertError::SerializationFailed { reason: err.to_string() })?;
        record
            .validate_structure()
            .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
        Ok(record)
    }
}

impl CheckedBinaryCertificateAuditExport {
    pub fn from_manifest_entry_and_record(
        entry: CheckedBinaryCertificateManifestEntry,
        record: CheckedBinaryCertificateManifestAcceptanceRecord,
    ) -> Result<Self, CheckError> {
        let export = Self {
            schema_version: CHECKED_BINARY_CERTIFICATE_AUDIT_EXPORT_SCHEMA_VERSION.to_string(),
            manifest_entry: entry,
            acceptance_record: record,
        };
        export.validate_structure()?;
        Ok(export)
    }

    pub fn from_manifest_acceptance(
        entry: &CheckedBinaryCertificateManifestEntry,
        acceptance: &CheckedBinaryCertificateManifestAcceptance,
    ) -> Result<Self, CheckError> {
        Self::from_manifest_entry_and_record(entry.clone(), acceptance.record.clone())
    }

    pub fn validate_structure(&self) -> Result<(), CheckError> {
        if self.schema_version != CHECKED_BINARY_CERTIFICATE_AUDIT_EXPORT_SCHEMA_VERSION {
            return Err(binding_mismatch(
                "audit_export.schema_version",
                CHECKED_BINARY_CERTIFICATE_AUDIT_EXPORT_SCHEMA_VERSION,
                self.schema_version.as_str(),
            ));
        }
        self.acceptance_record.validate_manifest_entry(&self.manifest_entry)?;
        Ok(())
    }

    pub fn acceptance_request(
        &self,
    ) -> Result<CheckedBinaryCertificateManifestAcceptanceRequest, CheckError> {
        self.validate_structure()?;
        self.acceptance_record.to_acceptance_request()
    }

    pub fn to_json(&self) -> Result<String, crate::CertError> {
        self.validate_structure()
            .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
        serde_json::to_string_pretty(self)
            .map_err(|err| crate::CertError::SerializationFailed { reason: err.to_string() })
    }

    pub fn from_json(json: &str) -> Result<Self, crate::CertError> {
        let export: Self = serde_json::from_str(json)
            .map_err(|err| crate::CertError::SerializationFailed { reason: err.to_string() })?;
        export
            .validate_structure()
            .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
        Ok(export)
    }
}

fn audit_export_manifest_identity_sha256(
    audit_export: &CheckedBinaryCertificateAuditExport,
) -> Result<String, CheckError> {
    audit_export.validate_structure()?;
    let identity = CheckedBinaryCertificateManifestIdentityEntry::from_acceptance_record(
        &audit_export.acceptance_record,
    )?;
    identity.sha256()
}

impl CheckedBinaryCertificateAuditExportBundle {
    pub fn new(
        manifest_sha256: impl Into<String>,
        audit_exports: Vec<CheckedBinaryCertificateAuditExportBundleEntry>,
    ) -> Result<Self, CheckError> {
        let bundle = Self {
            schema_version: CHECKED_BINARY_CERTIFICATE_AUDIT_EXPORT_BUNDLE_SCHEMA_VERSION
                .to_string(),
            manifest_path: checked_certificate_manifest_relative_path(),
            manifest_sha256: manifest_sha256.into(),
            audit_exports,
        };
        bundle.validate_structure()?;
        Ok(bundle)
    }

    pub fn validate_structure(&self) -> Result<(), CheckError> {
        if self.schema_version != CHECKED_BINARY_CERTIFICATE_AUDIT_EXPORT_BUNDLE_SCHEMA_VERSION {
            return Err(binding_mismatch(
                "audit_export_bundle.schema_version",
                CHECKED_BINARY_CERTIFICATE_AUDIT_EXPORT_BUNDLE_SCHEMA_VERSION,
                self.schema_version.as_str(),
            ));
        }
        validate_artifact_root_relative_path(
            "audit_export_bundle.manifest_path",
            &self.manifest_path,
        )?;
        if self.manifest_path != checked_certificate_manifest_relative_path() {
            return Err(binding_mismatch(
                "audit_export_bundle.manifest_path",
                checked_certificate_manifest_relative_path().display().to_string(),
                self.manifest_path.display().to_string(),
            ));
        }
        validate_canonical_sha256_hex(
            "audit_export_bundle.manifest_sha256",
            &self.manifest_sha256,
        )?;

        let mut certificate_digests = BTreeSet::new();
        let mut audit_paths = BTreeSet::new();
        for entry in &self.audit_exports {
            entry.validate_structure()?;
            if !certificate_digests.insert(entry.certificate_sha256.clone()) {
                return Err(CheckError::MalformedProof {
                    reason: format!(
                        "duplicate audit export bundle certificate_sha256 `{}`",
                        entry.certificate_sha256
                    ),
                });
            }
            if !audit_paths.insert(entry.audit_export_path.clone()) {
                return Err(CheckError::MalformedProof {
                    reason: format!(
                        "duplicate audit export bundle path `{}`",
                        entry.audit_export_path.display()
                    ),
                });
            }
        }

        Ok(())
    }

    pub fn to_json(&self) -> Result<String, crate::CertError> {
        self.validate_structure()
            .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
        serde_json::to_string_pretty(self)
            .map_err(|err| crate::CertError::SerializationFailed { reason: err.to_string() })
    }

    pub fn from_json(json: &str) -> Result<Self, crate::CertError> {
        let bundle: Self = serde_json::from_str(json)
            .map_err(|err| crate::CertError::SerializationFailed { reason: err.to_string() })?;
        bundle
            .validate_structure()
            .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
        Ok(bundle)
    }
}

impl CheckedBinaryCertificateAuditExportBundleEntry {
    pub fn from_manifest_entry_and_audit_export_digest(
        entry: &CheckedBinaryCertificateManifestEntry,
        audit_export_sha256: impl Into<String>,
    ) -> Result<Self, CheckError> {
        Self::from_manifest_entry_audit_export_digest_and_source_backpropagation_gate(
            entry,
            audit_export_sha256,
            CheckedBinaryCertificateSourceBackpropagationGate::default(),
        )
    }

    pub fn from_manifest_entry_audit_export_digest_and_source_backpropagation_gate(
        entry: &CheckedBinaryCertificateManifestEntry,
        audit_export_sha256: impl Into<String>,
        source_backpropagation_gate: CheckedBinaryCertificateSourceBackpropagationGate,
    ) -> Result<Self, CheckError> {
        let bundle_entry = Self {
            dispatch_id: entry.dispatch_id.clone(),
            vc_sha256: entry.vc_sha256.clone(),
            origin_sha256: entry.origin_sha256.clone(),
            proof_sha256: entry.proof_sha256.clone(),
            proof_export_sha256: entry.proof_export_sha256.clone(),
            certificate_sha256: entry.certificate_sha256.clone(),
            format: entry.format.clone(),
            checker: entry.checker.clone(),
            checker_version: entry.checker_version.clone(),
            replay: entry.replay,
            replay_transcript_digest: entry.replay_transcript_digest.clone(),
            binary_artifact_digest_identity: entry.binary_artifact_digest_identity.clone(),
            assumption_digest: entry.assumption_digest.clone(),
            manifest_identity_sha256: String::new(),
            source_backpropagation_gate,
            audit_export_path: checked_certificate_audit_export_relative_path(
                &entry.certificate_sha256,
            )?,
            audit_export_sha256: audit_export_sha256.into(),
        };
        bundle_entry.validate_structure()?;
        Ok(bundle_entry)
    }

    pub fn from_audit_export_and_digest(
        audit_export: &CheckedBinaryCertificateAuditExport,
        audit_export_sha256: impl Into<String>,
    ) -> Result<Self, CheckError> {
        let mut bundle_entry =
            Self::from_manifest_entry_audit_export_digest_and_source_backpropagation_gate(
                &audit_export.manifest_entry,
                audit_export_sha256,
                audit_export.acceptance_record.source_backpropagation_gate.clone(),
            )?;
        bundle_entry.manifest_identity_sha256 =
            audit_export_manifest_identity_sha256(audit_export)?;
        bundle_entry.validate_structure()?;
        Ok(bundle_entry)
    }

    pub fn validate_structure(&self) -> Result<(), CheckError> {
        if self.dispatch_id.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "audit export bundle entry is missing dispatch id".to_string(),
            });
        }
        validate_canonical_sha256_hex("audit export bundle vc_sha256", &self.vc_sha256)?;
        validate_canonical_sha256_hex("audit export bundle origin_sha256", &self.origin_sha256)?;
        validate_canonical_sha256_hex("audit export bundle proof_sha256", &self.proof_sha256)?;
        validate_canonical_sha256_hex(
            "audit export bundle proof_export_sha256",
            &self.proof_export_sha256,
        )?;
        validate_canonical_sha256_hex(
            "audit export bundle certificate_sha256",
            &self.certificate_sha256,
        )?;
        validate_canonical_sha256_hex(
            "audit export bundle assumption_digest",
            &self.assumption_digest,
        )?;
        if !self.manifest_identity_sha256.is_empty() {
            validate_canonical_sha256_hex(
                "audit export bundle manifest_identity_sha256",
                &self.manifest_identity_sha256,
            )?;
        }
        validate_canonical_sha256_hex(
            "audit export bundle audit_export_sha256",
            &self.audit_export_sha256,
        )?;
        if let Some(replay_transcript_digest) = self.replay_transcript_digest.as_deref() {
            validate_canonical_sha256_hex(
                "audit export bundle replay_transcript_digest",
                replay_transcript_digest,
            )?;
        }
        validate_binary_artifact_digest_identity(&self.binary_artifact_digest_identity)?;
        self.source_backpropagation_gate.validate_structure()?;
        if self.format.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "audit export bundle entry is missing proof format".to_string(),
            });
        }
        if self.checker.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "audit export bundle entry is missing checker id".to_string(),
            });
        }
        if self.checker_version.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "audit export bundle entry is missing checker version".to_string(),
            });
        }
        validate_artifact_root_relative_path(
            "audit export bundle audit_export_path",
            &self.audit_export_path,
        )?;
        let expected = checked_certificate_audit_export_relative_path(&self.certificate_sha256)?;
        if self.audit_export_path != expected {
            return Err(CheckError::MalformedProof {
                reason: format!(
                    "audit export bundle audit_export_path must match `{}` for certificate_sha256 `{}`",
                    expected.display(),
                    self.certificate_sha256
                ),
            });
        }

        Ok(())
    }

    fn validate_manifest_entry(
        &self,
        entry: &CheckedBinaryCertificateManifestEntry,
    ) -> Result<(), CheckError> {
        self.validate_structure()?;
        if self.dispatch_id != entry.dispatch_id {
            return Err(binding_mismatch(
                "audit_export_bundle.dispatch_id",
                entry.dispatch_id.as_str(),
                self.dispatch_id.as_str(),
            ));
        }
        if self.vc_sha256 != entry.vc_sha256 {
            return Err(binding_mismatch(
                "audit_export_bundle.vc_sha256",
                entry.vc_sha256.as_str(),
                self.vc_sha256.as_str(),
            ));
        }
        if self.origin_sha256 != entry.origin_sha256 {
            return Err(binding_mismatch(
                "audit_export_bundle.origin_sha256",
                entry.origin_sha256.as_str(),
                self.origin_sha256.as_str(),
            ));
        }
        if self.proof_sha256 != entry.proof_sha256 {
            return Err(binding_mismatch(
                "audit_export_bundle.proof_sha256",
                entry.proof_sha256.as_str(),
                self.proof_sha256.as_str(),
            ));
        }
        if self.proof_export_sha256 != entry.proof_export_sha256 {
            return Err(binding_mismatch(
                "audit_export_bundle.proof_export_sha256",
                entry.proof_export_sha256.as_str(),
                self.proof_export_sha256.as_str(),
            ));
        }
        if self.certificate_sha256 != entry.certificate_sha256 {
            return Err(binding_mismatch(
                "audit_export_bundle.certificate_sha256",
                entry.certificate_sha256.as_str(),
                self.certificate_sha256.as_str(),
            ));
        }
        if self.format != entry.format {
            return Err(binding_mismatch(
                "audit_export_bundle.format",
                entry.format.as_str(),
                self.format.as_str(),
            ));
        }
        if self.checker != entry.checker {
            return Err(binding_mismatch(
                "audit_export_bundle.checker",
                entry.checker.as_str(),
                self.checker.as_str(),
            ));
        }
        if self.checker_version != entry.checker_version {
            return Err(binding_mismatch(
                "audit_export_bundle.checker_version",
                entry.checker_version.as_str(),
                self.checker_version.as_str(),
            ));
        }
        if self.replay != entry.replay {
            return Err(binding_mismatch(
                "audit_export_bundle.replay",
                format!("{:?}", entry.replay),
                format!("{:?}", self.replay),
            ));
        }
        if self.replay_transcript_digest != entry.replay_transcript_digest {
            return Err(CheckError::ReplayDigestMismatch {
                expected: entry
                    .replay_transcript_digest
                    .as_deref()
                    .unwrap_or("<missing>")
                    .to_string(),
                actual: self.replay_transcript_digest.as_deref().unwrap_or("<missing>").to_string(),
            });
        }
        if self.binary_artifact_digest_identity != entry.binary_artifact_digest_identity {
            return Err(binding_mismatch(
                "audit_export_bundle.binary_artifact_digest_identity",
                binary_artifact_digest_identity_label(&entry.binary_artifact_digest_identity)?,
                binary_artifact_digest_identity_label(&self.binary_artifact_digest_identity)?,
            ));
        }
        if self.assumption_digest != entry.assumption_digest {
            return Err(CheckError::AssumptionDigestMismatch {
                expected: entry.assumption_digest.clone(),
                actual: self.assumption_digest.clone(),
            });
        }

        Ok(())
    }

    fn validate_audit_export(
        &self,
        audit_export: &CheckedBinaryCertificateAuditExport,
    ) -> Result<(), CheckError> {
        self.validate_manifest_entry(&audit_export.manifest_entry)?;
        audit_export.acceptance_record.validate_manifest_entry(&audit_export.manifest_entry)?;
        if self.source_backpropagation_gate
            != audit_export.acceptance_record.source_backpropagation_gate
        {
            return Err(binding_mismatch(
                "audit_export_bundle.source_backpropagation_gate",
                format!("{:?}", audit_export.acceptance_record.source_backpropagation_gate),
                format!("{:?}", self.source_backpropagation_gate),
            ));
        }
        let manifest_identity_sha256 = audit_export_manifest_identity_sha256(audit_export)?;
        if self.manifest_identity_sha256 != manifest_identity_sha256 {
            return Err(binding_mismatch(
                "audit_export_bundle.manifest_identity_sha256",
                manifest_identity_sha256,
                self.manifest_identity_sha256.as_str(),
            ));
        }
        Ok(())
    }
}

impl CheckedBinaryCertificateArtifact {
    #[must_use]
    pub fn proof_certificate_status(&self) -> ProofCertificateStatus {
        ProofCertificateStatus::Checked {
            checker: self.checker.clone(),
            format: self.format.clone(),
            sha256: Some(self.certificate_sha256.clone()),
        }
    }

    /// Serialize the checked artifact, including the proof/checker binding payload.
    pub fn to_json(&self) -> Result<String, crate::CertError> {
        serde_json::to_string_pretty(self)
            .map_err(|err| crate::CertError::SerializationFailed { reason: err.to_string() })
    }

    /// Reload a checked artifact and fail closed when only summary metadata is present.
    pub fn from_json(json: &str) -> Result<Self, crate::CertError> {
        let artifact: Self = serde_json::from_str(json)
            .map_err(|err| crate::CertError::SerializationFailed { reason: err.to_string() })?;
        artifact
            .validate_integrity()
            .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
        Ok(artifact)
    }

    /// Return the content-addressed path for this checked artifact under `root`.
    pub fn content_addressed_path(&self, root: impl AsRef<Path>) -> Result<PathBuf, CheckError> {
        self.validate_integrity()?;
        Ok(checked_certificate_artifact_path_unchecked(root.as_ref(), &self.certificate_sha256))
    }

    /// Persist this checked artifact under a content-addressed path rooted at `root`.
    pub fn persist_to_dir(&self, root: impl AsRef<Path>) -> Result<PathBuf, crate::CertError> {
        persist_checked_certificate_artifact(root, self)
    }

    /// Load a checked artifact from a JSON file and validate its internal bindings.
    pub fn load_from_file(path: impl AsRef<Path>) -> Result<Self, crate::CertError> {
        load_checked_certificate_artifact(path)
    }

    /// Validate the persisted artifact's internal digest and binding payload.
    pub fn validate_integrity(&self) -> Result<(), CheckError> {
        if self.dispatch_id.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "checked artifact is missing dispatch id".to_string(),
            });
        }
        if self.vc_sha256.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "checked artifact is missing VC digest".to_string(),
            });
        }
        if self.origin_sha256.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "checked artifact is missing binary origin digest".to_string(),
            });
        }
        if self.proof_sha256.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "checked artifact is missing proof payload digest".to_string(),
            });
        }
        if self.proof_export_sha256.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "checked artifact is missing proof export metadata digest".to_string(),
            });
        }
        if self.certificate_sha256.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "checked artifact is missing certificate digest".to_string(),
            });
        }
        validate_canonical_sha256_hex("vc_sha256", &self.vc_sha256)?;
        validate_canonical_sha256_hex("origin_sha256", &self.origin_sha256)?;
        validate_canonical_sha256_hex("proof_sha256", &self.proof_sha256)?;
        validate_canonical_sha256_hex("proof_export_sha256", &self.proof_export_sha256)?;
        validate_canonical_sha256_hex("certificate_sha256", &self.certificate_sha256)?;
        if let Some(replay_transcript_digest) = self.replay_transcript_digest.as_deref() {
            validate_canonical_sha256_hex("replay_transcript_digest", replay_transcript_digest)?;
        }
        validate_binary_artifact_digest_identity(&self.binary_artifact_digest_identity)?;
        if self.format.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "checked artifact is missing proof format".to_string(),
            });
        }
        if self.checker.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "checked artifact is missing checker id".to_string(),
            });
        }
        if self.checker_version.trim().is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "checked artifact is missing checker version".to_string(),
            });
        }
        if self.normalized_payload.is_empty() {
            return Err(CheckError::MalformedProof {
                reason: "checked artifact has no normalized payload".to_string(),
            });
        }

        let actual_certificate_sha256 = stable_sha256_hex(&self.normalized_payload);
        if actual_certificate_sha256 != self.certificate_sha256 {
            return Err(binding_mismatch(
                "certificate_sha256",
                self.certificate_sha256.as_str(),
                actual_certificate_sha256,
            ));
        }

        let payload = normalized_payload_metadata(&self.normalized_payload)?;
        let canonical_payload = serialize_normalized_payload_metadata(&payload)?;
        if self.normalized_payload != canonical_payload {
            return Err(CheckError::MalformedProof {
                reason: "normalized payload is not canonical checked-certificate metadata"
                    .to_string(),
            });
        }
        if payload.schema_version != CHECKED_BINARY_CERTIFICATE_SCHEMA_VERSION {
            return Err(binding_mismatch(
                "schema_version",
                CHECKED_BINARY_CERTIFICATE_SCHEMA_VERSION,
                payload.schema_version,
            ));
        }
        validate_payload_export_metadata_bindings(&payload)?;
        let actual_proof_export_sha256 = payload.proof_export.sha256()?;
        if payload.proof_export_sha256 != actual_proof_export_sha256 {
            return Err(binding_mismatch(
                "proof_export_sha256",
                payload.proof_export_sha256.as_str(),
                actual_proof_export_sha256,
            ));
        }
        if payload.proof_export_sha256 != self.proof_export_sha256 {
            return Err(binding_mismatch(
                "proof_export_sha256",
                self.proof_export_sha256.as_str(),
                payload.proof_export_sha256.as_str(),
            ));
        }
        if payload.dispatch_id != self.dispatch_id {
            return Err(binding_mismatch(
                "dispatch_id",
                self.dispatch_id.as_str(),
                payload.dispatch_id,
            ));
        }
        if payload.vc_sha256 != self.vc_sha256 {
            return Err(binding_mismatch("vc_sha256", self.vc_sha256.as_str(), payload.vc_sha256));
        }
        if payload.proof_sha256 != self.proof_sha256 {
            return Err(binding_mismatch(
                "proof_sha256",
                self.proof_sha256.as_str(),
                payload.proof_sha256,
            ));
        }
        if payload.format != self.format {
            return Err(binding_mismatch("format", self.format.as_str(), payload.format));
        }
        if payload.checker != self.checker {
            return Err(binding_mismatch("checker", self.checker.as_str(), payload.checker));
        }
        if payload.checker_version != self.checker_version {
            return Err(binding_mismatch(
                "checker_version",
                self.checker_version.as_str(),
                payload.checker_version,
            ));
        }
        if payload.query_semantics != self.query_semantics {
            return Err(binding_mismatch(
                "query_semantics",
                format!("{:?}", self.query_semantics),
                format!("{:?}", payload.query_semantics),
            ));
        }
        if payload.replay != self.replay {
            return Err(binding_mismatch(
                "replay",
                format!("{:?}", self.replay),
                format!("{:?}", payload.replay),
            ));
        }
        if let Some(replay_transcript_digest) = payload.replay_transcript_digest.as_deref() {
            validate_canonical_sha256_hex("replay_transcript_digest", replay_transcript_digest)?;
        }
        if payload.replay_transcript_digest != self.replay_transcript_digest {
            return Err(binding_mismatch(
                "replay_transcript_digest",
                format!("{:?}", self.replay_transcript_digest),
                format!("{:?}", payload.replay_transcript_digest),
            ));
        }
        let actual_origin_digest = digest_binary_origin(&self.origin)?;
        if self.origin_sha256 != actual_origin_digest {
            return Err(binding_mismatch(
                "origin_sha256",
                self.origin_sha256.as_str(),
                actual_origin_digest,
            ));
        }
        if payload.binary_origin_digest != actual_origin_digest {
            return Err(binding_mismatch(
                "binary_origin_digest",
                payload.binary_origin_digest,
                actual_origin_digest,
            ));
        }
        validate_binary_artifact_digest_identity(&payload.binary_artifact_digest_identity)?;
        if payload.binary_artifact_digest_identity != self.binary_artifact_digest_identity {
            return Err(binding_mismatch(
                "binary_artifact_digest_identity",
                binary_artifact_digest_identity_label(&self.binary_artifact_digest_identity)?,
                binary_artifact_digest_identity_label(&payload.binary_artifact_digest_identity)?,
            ));
        }
        let actual_assumption_digest = digest_model_assumptions(&self.assumptions);
        if self.assumption_digest != actual_assumption_digest {
            return Err(CheckError::AssumptionDigestMismatch {
                expected: self.assumption_digest.clone(),
                actual: actual_assumption_digest,
            });
        }
        if payload.assumption_digest != self.assumption_digest {
            return Err(CheckError::AssumptionDigestMismatch {
                expected: self.assumption_digest.clone(),
                actual: payload.assumption_digest,
            });
        }

        Ok(())
    }

    /// Validate that this persisted artifact still belongs to the current dispatch and VC.
    pub fn validate_for_dispatch(
        &self,
        dispatch: &SolverDispatchRecord,
        canonical_vc_bytes: &[u8],
    ) -> Result<(), CheckError> {
        self.validate_integrity()?;

        if self.dispatch_id != dispatch.id {
            return Err(binding_mismatch(
                "dispatch_id",
                dispatch.id.as_str(),
                self.dispatch_id.as_str(),
            ));
        }
        let actual_vc_sha256 = stable_sha256_hex(canonical_vc_bytes);
        if self.vc_sha256 != actual_vc_sha256 {
            return Err(CheckError::VcDigestMismatch {
                expected: self.vc_sha256.clone(),
                actual: actual_vc_sha256,
            });
        }
        if dispatch.status != SolverDispatchStatus::Unsat {
            return Err(CheckError::SolverVerdictMismatch { status: dispatch.status });
        }
        if self.query_semantics != dispatch.query_semantics {
            return Err(binding_mismatch(
                "query_semantics",
                format!("{:?}", dispatch.query_semantics),
                format!("{:?}", self.query_semantics),
            ));
        }
        if self.replay != dispatch.replay {
            return Err(binding_mismatch(
                "replay",
                format!("{:?}", dispatch.replay),
                format!("{:?}", self.replay),
            ));
        }
        let dispatch_origin = dispatch.origin.as_ref().ok_or(CheckError::BinaryOriginMissing)?;
        let dispatch_origin_digest = digest_binary_origin(dispatch_origin)?;
        if self.origin_sha256 != dispatch_origin_digest || &self.origin != dispatch_origin {
            return Err(binding_mismatch(
                "binary_origin_digest",
                dispatch_origin_digest,
                digest_binary_origin(&self.origin)?,
            ));
        }
        let dispatch_binary_artifact_digest_identity =
            replay_grade_binary_artifact_digest_identity(dispatch)?;
        if self.binary_artifact_digest_identity != dispatch_binary_artifact_digest_identity {
            return Err(binding_mismatch(
                "binary_artifact_digest_identity",
                binary_artifact_digest_identity_label(&dispatch_binary_artifact_digest_identity)?,
                binary_artifact_digest_identity_label(&self.binary_artifact_digest_identity)?,
            ));
        }
        let actual_assumption_digest = digest_model_assumptions(&dispatch.assumptions);
        if self.assumption_digest != actual_assumption_digest {
            return Err(CheckError::AssumptionDigestMismatch {
                expected: self.assumption_digest.clone(),
                actual: actual_assumption_digest,
            });
        }
        if self.assumptions != dispatch.assumptions {
            return Err(binding_mismatch(
                "assumptions",
                "persisted checked-certificate assumptions",
                "dispatch assumptions",
            ));
        }

        Ok(())
    }

    /// Validate this artifact against a rerun dispatch using stable VC/origin digests.
    ///
    /// Dispatch ids are intentionally not part of this check: they can change across
    /// verify-binary runs as functions are ordered or named differently. The binding
    /// that matters for import is the canonical VC digest plus binary-origin digest,
    /// with solver semantics and model assumptions still checked fail-closed.
    pub fn validate_for_dispatch_by_canonical_digests(
        &self,
        dispatch: &SolverDispatchRecord,
        canonical_vc_bytes: &[u8],
    ) -> Result<(), CheckError> {
        self.validate_integrity()?;

        let actual_vc_sha256 = stable_sha256_hex(canonical_vc_bytes);
        if self.vc_sha256 != actual_vc_sha256 {
            return Err(CheckError::VcDigestMismatch {
                expected: self.vc_sha256.clone(),
                actual: actual_vc_sha256,
            });
        }
        if dispatch.status != SolverDispatchStatus::Unsat {
            return Err(CheckError::SolverVerdictMismatch { status: dispatch.status });
        }
        if self.query_semantics != dispatch.query_semantics {
            return Err(binding_mismatch(
                "query_semantics",
                format!("{:?}", dispatch.query_semantics),
                format!("{:?}", self.query_semantics),
            ));
        }
        if self.replay != dispatch.replay {
            return Err(binding_mismatch(
                "replay",
                format!("{:?}", dispatch.replay),
                format!("{:?}", self.replay),
            ));
        }
        let dispatch_origin = dispatch.origin.as_ref().ok_or(CheckError::BinaryOriginMissing)?;
        let dispatch_origin_digest = digest_binary_origin(dispatch_origin)?;
        if self.origin_sha256 != dispatch_origin_digest {
            return Err(binding_mismatch(
                "origin_sha256",
                dispatch_origin_digest,
                self.origin_sha256.as_str(),
            ));
        }
        let dispatch_binary_artifact_digest_identity =
            replay_grade_binary_artifact_digest_identity(dispatch)?;
        if self.binary_artifact_digest_identity != dispatch_binary_artifact_digest_identity {
            return Err(binding_mismatch(
                "binary_artifact_digest_identity",
                binary_artifact_digest_identity_label(&dispatch_binary_artifact_digest_identity)?,
                binary_artifact_digest_identity_label(&self.binary_artifact_digest_identity)?,
            ));
        }
        let actual_assumption_digest = digest_model_assumptions(&dispatch.assumptions);
        if self.assumption_digest != actual_assumption_digest {
            return Err(CheckError::AssumptionDigestMismatch {
                expected: self.assumption_digest.clone(),
                actual: actual_assumption_digest,
            });
        }

        Ok(())
    }
}

/// Serializable check result for reports and tests.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryCertificateCheckResult {
    pub dispatch_id: String,
    pub checker: CheckerId,
    pub accepted: bool,
    pub certificate: Option<CheckedBinaryCertificateArtifact>,
    pub error: Option<CheckError>,
    pub diagnostics: Vec<String>,
}

impl BinaryCertificateCheckResult {
    #[must_use]
    pub fn accepted(certificate: CheckedBinaryCertificateArtifact) -> Self {
        Self {
            dispatch_id: certificate.dispatch_id.clone(),
            checker: certificate.checker.clone(),
            accepted: true,
            certificate: Some(certificate),
            error: None,
            diagnostics: Vec::new(),
        }
    }

    #[must_use]
    pub fn rejected(
        dispatch_id: impl Into<String>,
        checker: impl Into<CheckerId>,
        error: CheckError,
    ) -> Self {
        Self {
            dispatch_id: dispatch_id.into(),
            checker: checker.into(),
            accepted: false,
            certificate: None,
            error: Some(error),
            diagnostics: Vec::new(),
        }
    }

    #[must_use]
    pub fn raw_solver_bytes_are_audit_only(
        dispatch_id: impl Into<String>,
        raw: &AuditOnlyRawSolverProofBytes,
    ) -> Self {
        Self::rejected(
            dispatch_id,
            raw.solver.clone(),
            CheckError::RawSolverBytesAuditOnly { bytes_sha256: raw.bytes_sha256.clone() },
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Error, Serialize, Deserialize)]
#[non_exhaustive]
pub enum CheckError {
    #[error("unsupported proof format `{format}`")]
    UnsupportedFormat { format: ProofFormat },
    #[error("malformed proof: {reason}")]
    MalformedProof { reason: String },
    #[error("VC digest mismatch: expected {expected}, actual {actual}")]
    VcDigestMismatch { expected: String, actual: String },
    #[error("query semantics are not proof grade: {semantics:?}")]
    QuerySemanticsNotProofGrade { semantics: SolverQuerySemantics },
    #[error("solver verdict mismatch: {status:?}")]
    SolverVerdictMismatch { status: SolverDispatchStatus },
    #[error("assumption digest mismatch: expected {expected}, actual {actual}")]
    AssumptionDigestMismatch { expected: String, actual: String },
    #[error("replay digest mismatch: expected {expected}, actual {actual}")]
    ReplayDigestMismatch { expected: String, actual: String },
    #[error("checker internal error: {reason}")]
    CheckerInternalError { reason: String },
    #[error("raw solver proof bytes are audit-only evidence: {bytes_sha256}")]
    RawSolverBytesAuditOnly { bytes_sha256: String },
    #[error("raw solver proof bytes on dispatch `{dispatch_id}` cannot be upgraded to Checked")]
    RawSolverBytesCannotUpgradeToChecked { dispatch_id: String },
    #[error("missing production checker evidence for checked binary certificate acceptance")]
    MissingProductionCheckerEvidence,
    #[error("checked certificate audit bundle coverage incomplete: {reason}")]
    CheckedVcCoverageIncomplete { reason: String },
    #[error("checker evidence is not production: {kind:?}")]
    CheckerEvidenceNotProduction { kind: CheckedBinaryCertificateCheckerEvidenceKind },
    #[error(
        "checker evidence is not an external production checker invocation: {invocation_kind:?}"
    )]
    CheckerEvidenceNotExternalInvocation {
        invocation_kind: CheckedBinaryCertificateCheckerInvocationKind,
    },
    #[error("external checker process `{command}` failed with exit status {exit_status}")]
    CheckerExternalProcessFailed { command: String, exit_status: i32 },
    #[error("external checker process `{command}` timed out after {timeout_ms}ms")]
    CheckerExternalProcessTimedOut { command: String, timeout_ms: u64 },
    #[error("external checker process `{command}` could not start: {reason}")]
    CheckerExternalProcessSpawnFailed { command: String, reason: String },
    #[error("external checker process `{command}` {stream} I/O failed: {reason}")]
    CheckerExternalProcessIoFailed { command: String, stream: String, reason: String },
    #[error("missing external checker process transcript digest: {field}")]
    MissingCheckerExternalProcessTranscriptDigest { field: String },
    #[error("missing binary origin/provenance for checked certificate")]
    BinaryOriginMissing,
    #[error("binary artifact digest identity is not replay-grade: {reason}")]
    BinaryArtifactDigestIdentityInvalid { reason: String },
    #[error("source backpropagation gate prerequisites incomplete: {reason}")]
    SourceBackpropagationGateIncomplete { reason: String },
    #[error(
        "checked certificate artifact binding mismatch for {field}: expected {expected}, actual {actual}"
    )]
    ArtifactBindingMismatch { field: String, expected: String, actual: String },
}

pub trait BinaryCertificateChecker {
    fn checker_id(&self) -> CheckerId;
    fn supported_formats(&self) -> &[ProofFormat];
    fn check(
        &self,
        request: BinaryCertificateCheckRequest<'_>,
    ) -> Result<CheckedBinaryCertificateArtifact, CheckError>;
}

/// Deterministic structural checker for the production-path boundary.
///
/// This is not a format-specific LRAT/LFSC proof checker. It is the local
/// fail-closed boundary that a production checker implements: all identity and
/// digest bindings must hold before a checked certificate artifact can exist.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructuralBinaryCertificateChecker {
    checker_id: CheckerId,
    checker_version: String,
    supported_formats: Vec<ProofFormat>,
    checked_at_unix_ms: u64,
}

impl StructuralBinaryCertificateChecker {
    #[must_use]
    pub fn new(
        checker_id: impl Into<CheckerId>,
        checker_version: impl Into<String>,
        supported_formats: Vec<ProofFormat>,
        checked_at_unix_ms: u64,
    ) -> Self {
        Self {
            checker_id: checker_id.into(),
            checker_version: checker_version.into(),
            supported_formats,
            checked_at_unix_ms,
        }
    }
}

impl BinaryCertificateChecker for StructuralBinaryCertificateChecker {
    fn checker_id(&self) -> CheckerId {
        self.checker_id.clone()
    }

    fn supported_formats(&self) -> &[ProofFormat] {
        &self.supported_formats
    }

    fn check(
        &self,
        request: BinaryCertificateCheckRequest<'_>,
    ) -> Result<CheckedBinaryCertificateArtifact, CheckError> {
        if !self.supported_formats.contains(&request.export.format) {
            return Err(CheckError::UnsupportedFormat { format: request.export.format.clone() });
        }
        if request.dispatch.status != SolverDispatchStatus::Unsat {
            return Err(CheckError::SolverVerdictMismatch { status: request.dispatch.status });
        }
        if request.dispatch.query_semantics != request.expected_query_semantics
            || request.dispatch.query_semantics != SolverQuerySemantics::SatIsCounterexample
            || request.export.query_semantics != SolverQuerySemantics::SatIsCounterexample
        {
            return Err(CheckError::QuerySemanticsNotProofGrade {
                semantics: request.dispatch.query_semantics,
            });
        }
        request.export.validate_for_dispatch(request.dispatch, request.canonical_vc_bytes)?;

        let actual_vc_sha256 = stable_sha256_hex(request.canonical_vc_bytes);
        if actual_vc_sha256 != request.vc_sha256 {
            return Err(CheckError::VcDigestMismatch {
                expected: request.vc_sha256.to_string(),
                actual: actual_vc_sha256,
            });
        }
        if let Some(replay_transcript_digest) = request.replay_transcript_digest {
            validate_canonical_sha256_hex("replay_transcript_digest", replay_transcript_digest)?;
        }

        let actual_assumption_digest = digest_model_assumptions(request.model_assumptions);
        if actual_assumption_digest != request.assumption_digest
            || actual_assumption_digest != request.export.assumption_digest
        {
            return Err(CheckError::AssumptionDigestMismatch {
                expected: request.assumption_digest.to_string(),
                actual: actual_assumption_digest,
            });
        }

        let origin = request.dispatch.origin.clone().ok_or(CheckError::BinaryOriginMissing)?;
        let binary_artifact_digest_identity =
            replay_grade_binary_artifact_digest_identity(request.dispatch)?;
        let origin_sha256 = digest_binary_origin(&origin)?;
        let proof_export_sha256 = request.export.normalized_metadata_sha256()?;
        let normalized_payload = normalized_certificate_payload(
            request,
            &self.checker_id,
            &self.checker_version,
            self.checked_at_unix_ms,
        )?;
        let certificate_sha256 = stable_sha256_hex(&normalized_payload);

        Ok(CheckedBinaryCertificateArtifact {
            dispatch_id: request.dispatch.id.clone(),
            vc_sha256: actual_vc_sha256,
            origin_sha256,
            proof_sha256: request.export.proof_sha256.clone(),
            proof_export_sha256,
            certificate_sha256,
            format: request.export.format.clone(),
            checker: self.checker_id.clone(),
            checker_version: self.checker_version.clone(),
            query_semantics: request.dispatch.query_semantics,
            replay: request.dispatch.replay,
            replay_transcript_digest: request.replay_transcript_digest.map(ToString::to_string),
            origin,
            binary_artifact_digest_identity,
            normalized_payload,
            dependencies: Vec::new(),
            assumption_digest: request.assumption_digest.to_string(),
            assumptions: request.model_assumptions.to_vec(),
            checked_at_unix_ms: self.checked_at_unix_ms,
            diagnostics: Vec::new(),
        })
    }
}

#[must_use]
pub fn check_binary_certificate(
    checker: &impl BinaryCertificateChecker,
    request: BinaryCertificateCheckRequest<'_>,
) -> BinaryCertificateCheckResult {
    match checker.check(request) {
        Ok(certificate) => BinaryCertificateCheckResult::accepted(certificate),
        Err(error) => BinaryCertificateCheckResult::rejected(
            request.dispatch.id.clone(),
            checker.checker_id(),
            error,
        ),
    }
}

pub fn apply_checked_certificate_to_dispatch(
    dispatch: &mut SolverDispatchRecord,
    artifact: &CheckedBinaryCertificateArtifact,
) {
    dispatch.certificate = artifact.proof_certificate_status();
}

pub fn import_checked_certificate_for_dispatch(
    dispatch: &mut SolverDispatchRecord,
    canonical_vc_bytes: &[u8],
    artifact: &CheckedBinaryCertificateArtifact,
) -> Result<(), CheckError> {
    if dispatch_has_raw_solver_proof_bytes(dispatch) {
        return Err(CheckError::RawSolverBytesCannotUpgradeToChecked {
            dispatch_id: dispatch.id.clone(),
        });
    }
    artifact.validate_for_dispatch(dispatch, canonical_vc_bytes)?;
    apply_checked_certificate_to_dispatch(dispatch, artifact);
    Ok(())
}

pub fn produce_checked_certificate_artifact(
    checker: &impl BinaryCertificateChecker,
    request: BinaryCertificateCheckRequest<'_>,
    artifact_dir: impl AsRef<Path>,
) -> Result<CheckedBinaryCertificateArtifactRef, crate::CertError> {
    let artifact = checker
        .check(request)
        .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
    let path = persist_checked_certificate_artifact(artifact_dir, &artifact)?;
    Ok(CheckedBinaryCertificateArtifactRef { content_sha256: artifact.certificate_sha256, path })
}

pub fn accept_checked_certificate_manifest_entry(
    manifest_root: impl AsRef<Path>,
    canonical_vc_bytes: &[u8],
    entry: &CheckedBinaryCertificateManifestEntry,
    request: &CheckedBinaryCertificateManifestAcceptanceRequest,
) -> Result<CheckedBinaryCertificateManifestAcceptance, crate::CertError> {
    let manifest_root = manifest_root.as_ref();
    request
        .validate_manifest_entry(entry)
        .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
    request
        .validate_canonical_vc_bytes(canonical_vc_bytes)
        .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;

    let artifact_ref = request
        .artifact_identity
        .artifact_ref(manifest_root)
        .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
    let artifact = load_checked_certificate_artifact_ref(&artifact_ref)?;
    entry
        .validate_artifact(&artifact)
        .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
    request
        .validate_artifact(&artifact)
        .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;

    let record = request.acceptance_record();
    record
        .validate_structure()
        .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
    Ok(CheckedBinaryCertificateManifestAcceptance { record, artifact })
}

pub fn import_checked_certificate_manifest_entry_for_dispatch(
    dispatch: &mut SolverDispatchRecord,
    canonical_vc_bytes: &[u8],
    manifest_root: impl AsRef<Path>,
    entry: &CheckedBinaryCertificateManifestEntry,
    request: &CheckedBinaryCertificateManifestAcceptanceRequest,
) -> Result<CheckedBinaryCertificateManifestAcceptanceRecord, crate::CertError> {
    let acceptance = accept_checked_certificate_manifest_entry(
        manifest_root,
        canonical_vc_bytes,
        entry,
        request,
    )?;
    validate_checked_certificate_import_by_canonical_digests(
        dispatch,
        canonical_vc_bytes,
        &acceptance.artifact,
    )
    .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
    dispatch.certificate = acceptance
        .record
        .proof_certificate_status()
        .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
    set_checked_certificate_manifest_identity_diagnostic(dispatch, &acceptance.record)
        .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
    Ok(acceptance.record)
}

pub fn persist_checked_certificate_manifest(
    artifact_root: impl AsRef<Path>,
    manifest: &CheckedBinaryCertificateManifest,
) -> Result<PathBuf, crate::CertError> {
    let json = manifest.to_json()?;
    let path = checked_certificate_manifest_path(artifact_root);
    write_json_file(&path, &json)?;
    Ok(path)
}

pub fn load_checked_certificate_manifest(
    artifact_root: impl AsRef<Path>,
) -> Result<CheckedBinaryCertificateManifest, crate::CertError> {
    let (json, _) = read_root_relative_json(
        artifact_root.as_ref(),
        "checked certificate manifest path",
        &checked_certificate_manifest_relative_path(),
    )?;
    CheckedBinaryCertificateManifest::from_json(&json)
}

pub fn persist_checked_certificate_audit_export_bundle(
    artifact_root: impl AsRef<Path>,
    manifest: &CheckedBinaryCertificateManifest,
    audit_exports: &[CheckedBinaryCertificateAuditExport],
) -> Result<CheckedBinaryCertificateAuditExportBundle, crate::CertError> {
    manifest
        .validate_structure()
        .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
    if manifest.certificates.len() != audit_exports.len() {
        return Err(crate::CertError::InvalidCertificate {
            reason: format!(
                "audit export bundle must contain one audit export per manifest certificate: manifest={}, audit_exports={}",
                manifest.certificates.len(),
                audit_exports.len()
            ),
        });
    }

    let artifact_root = artifact_root.as_ref();
    let manifest_json = manifest.to_json()?;
    let manifest_sha256 = stable_sha256_hex(manifest_json.as_bytes());
    let manifest_path = checked_certificate_manifest_path(artifact_root);
    write_json_file(&manifest_path, &manifest_json)?;

    let mut bundle_entries = Vec::with_capacity(audit_exports.len());
    let mut seen_certificates = BTreeSet::new();
    for audit_export in audit_exports {
        audit_export
            .validate_structure()
            .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
        let manifest_entry = manifest
            .certificates
            .iter()
            .find(|entry| {
                entry.certificate_sha256 == audit_export.manifest_entry.certificate_sha256
            })
            .ok_or_else(|| crate::CertError::InvalidCertificate {
                reason: format!(
                    "audit export bundle entry `{}` has no matching manifest certificate",
                    audit_export.manifest_entry.certificate_sha256
                ),
            })?;
        if &audit_export.manifest_entry != manifest_entry {
            return Err(crate::CertError::InvalidCertificate {
                reason: format!(
                    "audit_export.manifest_entry for certificate `{}` does not match persisted manifest row",
                    manifest_entry.certificate_sha256
                ),
            });
        }
        if !seen_certificates.insert(manifest_entry.certificate_sha256.clone()) {
            return Err(crate::CertError::InvalidCertificate {
                reason: format!(
                    "duplicate audit export for manifest certificate `{}`",
                    manifest_entry.certificate_sha256
                ),
            });
        }

        let audit_export_json = audit_export.to_json()?;
        let audit_export_sha256 = stable_sha256_hex(audit_export_json.as_bytes());
        let audit_export_path = checked_certificate_audit_export_path(
            artifact_root,
            &manifest_entry.certificate_sha256,
        )?;
        write_json_file(&audit_export_path, &audit_export_json)?;
        bundle_entries.push(
            CheckedBinaryCertificateAuditExportBundleEntry::from_audit_export_and_digest(
                audit_export,
                audit_export_sha256,
            )
            .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?,
        );
    }

    bundle_entries.sort_by(|left, right| {
        left.certificate_sha256
            .cmp(&right.certificate_sha256)
            .then_with(|| left.vc_sha256.cmp(&right.vc_sha256))
            .then_with(|| left.dispatch_id.cmp(&right.dispatch_id))
    });
    let bundle = CheckedBinaryCertificateAuditExportBundle::new(manifest_sha256, bundle_entries)
        .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
    let bundle_json = bundle.to_json()?;
    write_json_file(&checked_certificate_audit_export_bundle_path(artifact_root), &bundle_json)?;
    Ok(bundle)
}

pub fn load_checked_certificate_audit_export_bundle(
    artifact_root: impl AsRef<Path>,
) -> Result<CheckedBinaryCertificateAuditExportBundleReadback, crate::CertError> {
    let artifact_root = artifact_root.as_ref();
    let (bundle_json, _) = read_root_relative_json(
        artifact_root,
        "checked certificate audit export bundle path",
        &checked_certificate_audit_export_bundle_relative_path(),
    )?;
    let bundle = CheckedBinaryCertificateAuditExportBundle::from_json(&bundle_json)?;

    let (manifest_json, manifest_sha256) = read_root_relative_json(
        artifact_root,
        "audit export bundle manifest_path",
        &bundle.manifest_path,
    )?;
    if manifest_sha256 != bundle.manifest_sha256 {
        return Err(crate::CertError::InvalidCertificate {
            reason: format!(
                "audit_export_bundle.manifest_sha256 mismatch: expected {}, actual {}",
                bundle.manifest_sha256, manifest_sha256
            ),
        });
    }
    let manifest = CheckedBinaryCertificateManifest::from_json(&manifest_json)?;
    manifest.validate_files(artifact_root)?;

    if manifest.certificates.len() != bundle.audit_exports.len() {
        return Err(crate::CertError::InvalidCertificate {
            reason: format!(
                "audit export bundle must contain one audit export per manifest certificate: manifest={}, audit_exports={}",
                manifest.certificates.len(),
                bundle.audit_exports.len()
            ),
        });
    }

    let mut audit_exports = Vec::with_capacity(bundle.audit_exports.len());
    let mut seen_certificates = BTreeSet::new();
    for bundle_entry in &bundle.audit_exports {
        let manifest_entry = manifest
            .certificates
            .iter()
            .find(|entry| entry.certificate_sha256 == bundle_entry.certificate_sha256)
            .ok_or_else(|| crate::CertError::InvalidCertificate {
                reason: format!(
                    "audit export bundle entry `{}` has no matching manifest certificate",
                    bundle_entry.certificate_sha256
                ),
            })?;
        bundle_entry
            .validate_manifest_entry(manifest_entry)
            .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
        if !seen_certificates.insert(manifest_entry.certificate_sha256.clone()) {
            return Err(crate::CertError::InvalidCertificate {
                reason: format!(
                    "duplicate audit export bundle certificate `{}`",
                    manifest_entry.certificate_sha256
                ),
            });
        }

        let (audit_json, audit_export_sha256) = read_root_relative_json(
            artifact_root,
            "audit export bundle audit_export_path",
            &bundle_entry.audit_export_path,
        )?;
        if audit_export_sha256 != bundle_entry.audit_export_sha256 {
            return Err(crate::CertError::InvalidCertificate {
                reason: format!(
                    "audit_export_bundle.audit_export_sha256 mismatch for certificate `{}`: expected {}, actual {}",
                    bundle_entry.certificate_sha256,
                    bundle_entry.audit_export_sha256,
                    audit_export_sha256
                ),
            });
        }
        let audit_export = CheckedBinaryCertificateAuditExport::from_json(&audit_json)?;
        if audit_export.manifest_entry != *manifest_entry {
            return Err(crate::CertError::InvalidCertificate {
                reason: format!(
                    "audit_export.manifest_entry for certificate `{}` does not match current manifest row",
                    manifest_entry.certificate_sha256
                ),
            });
        }
        bundle_entry
            .validate_audit_export(&audit_export)
            .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
        audit_exports.push(audit_export);
    }

    Ok(CheckedBinaryCertificateAuditExportBundleReadback { bundle, manifest, audit_exports })
}

pub fn load_checked_certificate_audit_export_bundle_rows(
    artifact_root: impl AsRef<Path>,
) -> Result<CheckedBinaryCertificateAuditExportBundleValidation, crate::CertError> {
    let artifact_root = artifact_root.as_ref();
    let (bundle_json, _) = read_root_relative_json(
        artifact_root,
        "checked certificate audit export bundle path",
        &checked_certificate_audit_export_bundle_relative_path(),
    )?;
    let bundle = CheckedBinaryCertificateAuditExportBundle::from_json(&bundle_json)?;

    let (manifest_json, manifest_sha256) = read_root_relative_json(
        artifact_root,
        "audit export bundle manifest_path",
        &bundle.manifest_path,
    )?;
    if manifest_sha256 != bundle.manifest_sha256 {
        return Err(crate::CertError::InvalidCertificate {
            reason: format!(
                "audit_export_bundle.manifest_sha256 mismatch: expected {}, actual {}",
                bundle.manifest_sha256, manifest_sha256
            ),
        });
    }
    let manifest = CheckedBinaryCertificateManifest::from_json(&manifest_json)?;

    let rows = bundle
        .audit_exports
        .iter()
        .map(|bundle_entry| {
            validate_checked_certificate_audit_export_bundle_row(
                artifact_root,
                &manifest,
                bundle_entry,
            )
        })
        .collect();

    Ok(CheckedBinaryCertificateAuditExportBundleValidation { bundle, manifest, rows })
}

pub fn load_checked_certificate_audit_export_bundle_complete_vc_coverage(
    artifact_root: impl AsRef<Path>,
    required_vc_sha256: &[String],
) -> Result<CheckedBinaryCertificateAuditExportBundleCoverage, crate::CertError> {
    let validation = load_checked_certificate_audit_export_bundle_rows(artifact_root)?;
    validation
        .validate_complete_checked_vc_coverage(required_vc_sha256)
        .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })
}

pub fn persist_checked_certificate_audit_export(
    path: impl AsRef<Path>,
    export: &CheckedBinaryCertificateAuditExport,
) -> Result<(), crate::CertError> {
    let path = path.as_ref();
    let json = export.to_json()?;
    write_json_file(path, &json)?;
    Ok(())
}

pub fn load_checked_certificate_audit_export(
    path: impl AsRef<Path>,
) -> Result<CheckedBinaryCertificateAuditExport, crate::CertError> {
    let json = std::fs::read_to_string(path.as_ref())?;
    CheckedBinaryCertificateAuditExport::from_json(&json)
}

fn validate_checked_certificate_audit_export_bundle_row(
    artifact_root: &Path,
    manifest: &CheckedBinaryCertificateManifest,
    bundle_entry: &CheckedBinaryCertificateAuditExportBundleEntry,
) -> CheckedBinaryCertificateAuditExportBundleValidationRow {
    let manifest_entry = match manifest
        .certificates
        .iter()
        .find(|entry| entry.certificate_sha256 == bundle_entry.certificate_sha256)
    {
        Some(entry) => entry.clone(),
        None => {
            return rejected_bundle_row(
                bundle_entry,
                None,
                None,
                CheckedBinaryCertificateAuditExportBundleRejectionCode::ManifestRowMissing,
                format!(
                    "audit export bundle entry `{}` has no matching manifest certificate",
                    bundle_entry.certificate_sha256
                ),
            );
        }
    };

    if let Err(err) = bundle_entry.validate_manifest_entry(&manifest_entry) {
        return rejected_bundle_row(
            bundle_entry,
            Some(manifest_entry),
            None,
            bundle_rejection_code_for_check_error(&err),
            err.to_string(),
        );
    }

    let (audit_json, audit_export_sha256) = match read_root_relative_json(
        artifact_root,
        "audit export bundle audit_export_path",
        &bundle_entry.audit_export_path,
    ) {
        Ok(readback) => readback,
        Err(err) => {
            return rejected_bundle_row(
                bundle_entry,
                Some(manifest_entry),
                None,
                CheckedBinaryCertificateAuditExportBundleRejectionCode::AuditExportUnreadable,
                err.to_string(),
            );
        }
    };
    if audit_export_sha256 != bundle_entry.audit_export_sha256 {
        return rejected_bundle_row(
            bundle_entry,
            Some(manifest_entry),
            None,
            CheckedBinaryCertificateAuditExportBundleRejectionCode::AuditExportDigestMismatch,
            format!(
                "audit_export_bundle.audit_export_sha256 mismatch for certificate `{}`: expected {}, actual {}",
                bundle_entry.certificate_sha256,
                bundle_entry.audit_export_sha256,
                audit_export_sha256
            ),
        );
    }

    let audit_export: CheckedBinaryCertificateAuditExport = match serde_json::from_str(&audit_json)
    {
        Ok(export) => export,
        Err(err) => {
            return rejected_bundle_row(
                bundle_entry,
                Some(manifest_entry),
                None,
                CheckedBinaryCertificateAuditExportBundleRejectionCode::AuditExportMalformed,
                err.to_string(),
            );
        }
    };
    if let Err(err) = audit_export.validate_structure() {
        return rejected_bundle_row(
            bundle_entry,
            Some(manifest_entry),
            Some(audit_export),
            bundle_rejection_code_for_check_error(&err),
            err.to_string(),
        );
    }
    if audit_export.manifest_entry != manifest_entry {
        let code = bundle_rejection_code_for_manifest_audit_mismatch(
            &manifest_entry,
            &audit_export.manifest_entry,
        );
        return rejected_bundle_row(
            bundle_entry,
            Some(manifest_entry.clone()),
            Some(audit_export),
            code,
            format!(
                "audit_export.manifest_entry for certificate `{}` does not match current manifest row",
                manifest_entry.certificate_sha256
            ),
        );
    }
    if let Err(err) = bundle_entry.validate_audit_export(&audit_export) {
        return rejected_bundle_row(
            bundle_entry,
            Some(manifest_entry),
            Some(audit_export),
            bundle_rejection_code_for_check_error(&err),
            err.to_string(),
        );
    }

    let acceptance_request = match audit_export.acceptance_request() {
        Ok(request) => request,
        Err(err) => {
            return rejected_bundle_row(
                bundle_entry,
                Some(manifest_entry),
                Some(audit_export),
                CheckedBinaryCertificateAuditExportBundleRejectionCode::ValidationFailed,
                err.to_string(),
            );
        }
    };
    let artifact_ref = match acceptance_request.artifact_identity.artifact_ref(artifact_root) {
        Ok(artifact_ref) => artifact_ref,
        Err(err) => {
            return rejected_bundle_row(
                bundle_entry,
                Some(manifest_entry),
                Some(audit_export),
                bundle_rejection_code_for_check_error(&err),
                err.to_string(),
            );
        }
    };
    let artifact = match load_checked_certificate_artifact_ref(&artifact_ref) {
        Ok(artifact) => artifact,
        Err(err) => {
            return rejected_bundle_row(
                bundle_entry,
                Some(manifest_entry),
                Some(audit_export),
                bundle_rejection_code_for_artifact_error(&err),
                err.to_string(),
            );
        }
    };
    if let Err(err) = manifest_entry.validate_artifact(&artifact) {
        return rejected_bundle_row(
            bundle_entry,
            Some(manifest_entry),
            Some(audit_export),
            bundle_rejection_code_for_check_error(&err),
            err.to_string(),
        );
    }
    if let Err(err) = acceptance_request.validate_artifact(&artifact) {
        return rejected_bundle_row(
            bundle_entry,
            Some(manifest_entry),
            Some(audit_export),
            bundle_rejection_code_for_check_error(&err),
            err.to_string(),
        );
    }

    let acceptance_record = audit_export.acceptance_record.clone();
    CheckedBinaryCertificateAuditExportBundleValidationRow::Accepted(
        CheckedBinaryCertificateAuditExportBundleAcceptedRow {
            bundle_entry: bundle_entry.clone(),
            manifest_entry,
            audit_export,
            acceptance_record,
            artifact,
        },
    )
}

fn rejected_bundle_row(
    bundle_entry: &CheckedBinaryCertificateAuditExportBundleEntry,
    manifest_entry: Option<CheckedBinaryCertificateManifestEntry>,
    audit_export: Option<CheckedBinaryCertificateAuditExport>,
    code: CheckedBinaryCertificateAuditExportBundleRejectionCode,
    reason: impl Into<String>,
) -> CheckedBinaryCertificateAuditExportBundleValidationRow {
    CheckedBinaryCertificateAuditExportBundleValidationRow::Rejected(
        CheckedBinaryCertificateAuditExportBundleRejectedRow::from_bundle_entry(
            bundle_entry,
            manifest_entry,
            audit_export,
            code,
            reason,
        ),
    )
}

fn bundle_rejection_code_for_artifact_error(
    err: &crate::CertError,
) -> CheckedBinaryCertificateAuditExportBundleRejectionCode {
    match err {
        crate::CertError::IoError { .. } => {
            CheckedBinaryCertificateAuditExportBundleRejectionCode::ArtifactUnreadable
        }
        crate::CertError::SerializationFailed { .. } => {
            CheckedBinaryCertificateAuditExportBundleRejectionCode::ArtifactMismatch
        }
        crate::CertError::InvalidCertificate { reason } => bundle_rejection_code_for_reason(reason)
            .unwrap_or(CheckedBinaryCertificateAuditExportBundleRejectionCode::ArtifactMismatch),
        _ => CheckedBinaryCertificateAuditExportBundleRejectionCode::ValidationFailed,
    }
}

fn bundle_rejection_code_for_check_error(
    err: &CheckError,
) -> CheckedBinaryCertificateAuditExportBundleRejectionCode {
    match err {
        CheckError::VcDigestMismatch { .. } => {
            CheckedBinaryCertificateAuditExportBundleRejectionCode::VcDigestMismatch
        }
        CheckError::AssumptionDigestMismatch { .. } => {
            CheckedBinaryCertificateAuditExportBundleRejectionCode::AssumptionMismatch
        }
        CheckError::ReplayDigestMismatch { .. } => {
            CheckedBinaryCertificateAuditExportBundleRejectionCode::ReplayMismatch
        }
        CheckError::BinaryArtifactDigestIdentityInvalid { .. } => {
            CheckedBinaryCertificateAuditExportBundleRejectionCode::ArtifactMismatch
        }
        CheckError::SourceBackpropagationGateIncomplete { .. } => {
            CheckedBinaryCertificateAuditExportBundleRejectionCode::ValidationFailed
        }
        CheckError::MissingProductionCheckerEvidence
        | CheckError::CheckerEvidenceNotProduction { .. }
        | CheckError::CheckerEvidenceNotExternalInvocation { .. }
        | CheckError::CheckerExternalProcessFailed { .. }
        | CheckError::CheckerExternalProcessTimedOut { .. }
        | CheckError::CheckerExternalProcessSpawnFailed { .. }
        | CheckError::CheckerExternalProcessIoFailed { .. }
        | CheckError::MissingCheckerExternalProcessTranscriptDigest { .. } => {
            CheckedBinaryCertificateAuditExportBundleRejectionCode::CheckerMismatch
        }
        CheckError::ArtifactBindingMismatch { field, .. } => bundle_rejection_code_for_field(field),
        CheckError::MalformedProof { reason } => bundle_rejection_code_for_reason(reason)
            .unwrap_or(CheckedBinaryCertificateAuditExportBundleRejectionCode::ValidationFailed),
        CheckError::BinaryOriginMissing => {
            CheckedBinaryCertificateAuditExportBundleRejectionCode::ArtifactMismatch
        }
        _ => CheckedBinaryCertificateAuditExportBundleRejectionCode::ValidationFailed,
    }
}

fn bundle_rejection_code_for_manifest_audit_mismatch(
    manifest_entry: &CheckedBinaryCertificateManifestEntry,
    audit_entry: &CheckedBinaryCertificateManifestEntry,
) -> CheckedBinaryCertificateAuditExportBundleRejectionCode {
    if manifest_entry.proof_export_sha256 != audit_entry.proof_export_sha256
        || manifest_entry.proof_sha256 != audit_entry.proof_sha256
    {
        CheckedBinaryCertificateAuditExportBundleRejectionCode::ProofExportMismatch
    } else if manifest_entry.checker != audit_entry.checker
        || manifest_entry.checker_version != audit_entry.checker_version
    {
        CheckedBinaryCertificateAuditExportBundleRejectionCode::CheckerMismatch
    } else if manifest_entry.replay != audit_entry.replay
        || manifest_entry.replay_transcript_digest != audit_entry.replay_transcript_digest
    {
        CheckedBinaryCertificateAuditExportBundleRejectionCode::ReplayMismatch
    } else if manifest_entry.binary_artifact_digest_identity
        != audit_entry.binary_artifact_digest_identity
    {
        CheckedBinaryCertificateAuditExportBundleRejectionCode::ArtifactMismatch
    } else if manifest_entry.assumption_digest != audit_entry.assumption_digest {
        CheckedBinaryCertificateAuditExportBundleRejectionCode::AssumptionMismatch
    } else if manifest_entry.vc_sha256 != audit_entry.vc_sha256 {
        CheckedBinaryCertificateAuditExportBundleRejectionCode::VcDigestMismatch
    } else {
        CheckedBinaryCertificateAuditExportBundleRejectionCode::ManifestRowMismatch
    }
}

fn bundle_rejection_code_for_reason(
    reason: &str,
) -> Option<CheckedBinaryCertificateAuditExportBundleRejectionCode> {
    if reason.contains("proof_export")
        || reason.contains("solver_proof_export")
        || reason.contains("proof_sha256")
    {
        Some(CheckedBinaryCertificateAuditExportBundleRejectionCode::ProofExportMismatch)
    } else if reason.contains("checker") {
        Some(CheckedBinaryCertificateAuditExportBundleRejectionCode::CheckerMismatch)
    } else if reason.contains("replay") {
        Some(CheckedBinaryCertificateAuditExportBundleRejectionCode::ReplayMismatch)
    } else if reason.contains("assumption") {
        Some(CheckedBinaryCertificateAuditExportBundleRejectionCode::AssumptionMismatch)
    } else if reason.contains("vc_sha256") || reason.contains("VC digest mismatch") {
        Some(CheckedBinaryCertificateAuditExportBundleRejectionCode::VcDigestMismatch)
    } else if reason.contains("binary_artifact_digest_identity")
        || reason.contains("artifact digest identity")
        || reason.contains("selected image")
        || reason.contains("artifact")
        || reason.contains("certificate")
    {
        Some(CheckedBinaryCertificateAuditExportBundleRejectionCode::ArtifactMismatch)
    } else {
        None
    }
}

fn bundle_rejection_code_for_field(
    field: &str,
) -> CheckedBinaryCertificateAuditExportBundleRejectionCode {
    bundle_rejection_code_for_reason(field)
        .unwrap_or(CheckedBinaryCertificateAuditExportBundleRejectionCode::ValidationFailed)
}

pub fn import_checked_certificate_for_dispatch_by_canonical_digests(
    dispatch: &mut SolverDispatchRecord,
    canonical_vc_bytes: &[u8],
    artifact: &CheckedBinaryCertificateArtifact,
) -> Result<(), CheckError> {
    validate_checked_certificate_import_by_canonical_digests(
        dispatch,
        canonical_vc_bytes,
        artifact,
    )?;
    apply_checked_certificate_to_dispatch(dispatch, artifact);
    Ok(())
}

fn validate_checked_certificate_import_by_canonical_digests(
    dispatch: &SolverDispatchRecord,
    canonical_vc_bytes: &[u8],
    artifact: &CheckedBinaryCertificateArtifact,
) -> Result<(), CheckError> {
    if dispatch_has_raw_solver_proof_bytes(dispatch) {
        return Err(CheckError::RawSolverBytesCannotUpgradeToChecked {
            dispatch_id: dispatch.id.clone(),
        });
    }
    artifact.validate_for_dispatch_by_canonical_digests(dispatch, canonical_vc_bytes)?;
    Ok(())
}

pub fn persist_checked_certificate_artifact(
    root: impl AsRef<Path>,
    artifact: &CheckedBinaryCertificateArtifact,
) -> Result<PathBuf, crate::CertError> {
    artifact
        .validate_integrity()
        .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
    let path =
        checked_certificate_artifact_path(root.as_ref(), artifact.certificate_sha256.as_str())?;
    let json = artifact.to_json()?;
    let parent = path.parent().ok_or_else(|| crate::CertError::IoError {
        reason: format!("content-addressed path has no parent: {}", path.display()),
    })?;
    std::fs::create_dir_all(parent)?;
    let tmp_path = parent.join(format!(".{}.tmp", artifact.certificate_sha256));
    std::fs::write(&tmp_path, json.as_bytes())?;
    std::fs::rename(&tmp_path, &path)?;
    Ok(path)
}

pub fn persist_solver_proof_export_artifacts(
    root: impl AsRef<Path>,
    export: &SolverProofExport,
) -> Result<SolverProofExportArtifactRef, crate::CertError> {
    export
        .normalized_metadata()
        .validate_structure()
        .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
    if export.proof_bytes.is_empty() || stable_sha256_hex(&export.proof_bytes) != export.proof_sha256 {
        return Err(crate::CertError::InvalidCertificate {
            reason: "solver proof export payload is empty or does not match proof_sha256"
                .to_string(),
        });
    }
    validate_sha256_hex(&export.proof_sha256)?;

    let metadata = export.normalized_metadata();
    let metadata_sha256 = metadata
        .sha256()
        .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
    let metadata_json = serde_json::to_vec(&metadata)
        .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;

    let metadata_path = solver_proof_export_metadata_path(root.as_ref(), metadata_sha256.as_str())?;
    let proof_path = solver_proof_export_payload_path(
        root.as_ref(),
        export.proof_sha256.as_str(),
        export.format.as_str(),
    )?;

    write_content_addressed_file(&metadata_path, metadata_sha256.as_str(), &metadata_json)?;
    write_content_addressed_file(&proof_path, export.proof_sha256.as_str(), &export.proof_bytes)?;

    Ok(SolverProofExportArtifactRef {
        metadata_sha256,
        metadata_path,
        proof_sha256: export.proof_sha256.clone(),
        proof_path,
    })
}

pub fn load_checked_certificate_artifact(
    path: impl AsRef<Path>,
) -> Result<CheckedBinaryCertificateArtifact, crate::CertError> {
    let json = std::fs::read_to_string(path.as_ref())?;
    CheckedBinaryCertificateArtifact::from_json(&json)
}

pub fn load_checked_certificate_artifact_ref(
    artifact_ref: &CheckedBinaryCertificateArtifactRef,
) -> Result<CheckedBinaryCertificateArtifact, crate::CertError> {
    validate_content_addressed_artifact_ref_path(artifact_ref)?;
    let artifact = load_checked_certificate_artifact(&artifact_ref.path)?;
    if artifact.certificate_sha256 != artifact_ref.content_sha256 {
        return Err(crate::CertError::InvalidCertificate {
            reason: format!(
                "content-addressed artifact mismatch: expected {}, actual {}",
                artifact_ref.content_sha256, artifact.certificate_sha256
            ),
        });
    }
    Ok(artifact)
}

pub fn load_content_addressed_checked_certificate_artifact(
    root: impl AsRef<Path>,
    certificate_sha256: &str,
) -> Result<CheckedBinaryCertificateArtifact, crate::CertError> {
    let path = checked_certificate_artifact_path(root.as_ref(), certificate_sha256)?;
    let artifact = load_checked_certificate_artifact(path)?;
    if artifact.certificate_sha256 != certificate_sha256 {
        return Err(crate::CertError::InvalidCertificate {
            reason: format!(
                "content-addressed artifact mismatch: expected {}, actual {}",
                certificate_sha256, artifact.certificate_sha256
            ),
        });
    }
    Ok(artifact)
}

pub fn import_content_addressed_checked_certificate_for_dispatch(
    dispatch: &mut SolverDispatchRecord,
    canonical_vc_bytes: &[u8],
    root: impl AsRef<Path>,
    certificate_sha256: &str,
) -> Result<CheckedBinaryCertificateArtifact, crate::CertError> {
    let artifact = load_content_addressed_checked_certificate_artifact(root, certificate_sha256)?;
    import_checked_certificate_for_dispatch(dispatch, canonical_vc_bytes, &artifact)
        .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
    Ok(artifact)
}

pub fn import_checked_certificate_artifact_for_dispatch(
    dispatch: &mut SolverDispatchRecord,
    canonical_vc_bytes: &[u8],
    artifact_ref: &CheckedBinaryCertificateArtifactRef,
) -> Result<CheckedBinaryCertificateArtifact, crate::CertError> {
    let artifact = load_checked_certificate_artifact_ref(artifact_ref)?;
    import_checked_certificate_for_dispatch(dispatch, canonical_vc_bytes, &artifact)
        .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
    Ok(artifact)
}

pub fn checked_certificate_artifact_path(
    root: impl AsRef<Path>,
    certificate_sha256: &str,
) -> Result<PathBuf, crate::CertError> {
    validate_sha256_hex(certificate_sha256)?;
    Ok(checked_certificate_artifact_path_unchecked(root.as_ref(), certificate_sha256))
}

#[must_use]
pub fn checked_certificate_manifest_path(root: impl AsRef<Path>) -> PathBuf {
    root.as_ref().join(checked_certificate_manifest_relative_path())
}

#[must_use]
pub fn checked_certificate_audit_export_bundle_path(root: impl AsRef<Path>) -> PathBuf {
    root.as_ref().join(checked_certificate_audit_export_bundle_relative_path())
}

pub fn checked_certificate_audit_export_path(
    root: impl AsRef<Path>,
    certificate_sha256: &str,
) -> Result<PathBuf, crate::CertError> {
    Ok(root.as_ref().join(
        checked_certificate_audit_export_relative_path(certificate_sha256)
            .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?,
    ))
}

fn sha256_file(path: &Path) -> io::Result<String> {
    stable_sha256_hex_reader(fs::File::open(path)?)
}

fn spawn_stream_digest<R>(
    command: String,
    stream: &'static str,
    reader: R,
) -> thread::JoinHandle<Result<String, CheckError>>
where
    R: Read + Send + 'static,
{
    thread::spawn(move || {
        stable_sha256_hex_reader(reader).map_err(|err| CheckError::CheckerExternalProcessIoFailed {
            command,
            stream: stream.to_string(),
            reason: err.to_string(),
        })
    })
}

fn wait_for_checker_child(
    child: &mut Child,
    command: String,
    timeout_policy: Option<&CheckedBinaryCertificateExternalCheckerTimeoutPolicy>,
) -> Result<(ExitStatus, bool), CheckError> {
    let Some(timeout_policy) = timeout_policy else {
        return child.wait().map(|status| (status, false)).map_err(|err| {
            CheckError::CheckerExternalProcessIoFailed {
                command,
                stream: "exit_status".to_string(),
                reason: err.to_string(),
            }
        });
    };

    timeout_policy.validate_structure()?;
    let timeout = Duration::from_millis(timeout_policy.timeout_ms);
    let start = Instant::now();
    loop {
        if let Some(status) =
            child.try_wait().map_err(|err| CheckError::CheckerExternalProcessIoFailed {
                command: command.clone(),
                stream: "exit_status".to_string(),
                reason: err.to_string(),
            })?
        {
            return Ok((status, false));
        }

        if start.elapsed() >= timeout {
            child.kill().map_err(|err| CheckError::CheckerExternalProcessIoFailed {
                command: command.clone(),
                stream: "kill".to_string(),
                reason: err.to_string(),
            })?;
            let status =
                child.wait().map_err(|err| CheckError::CheckerExternalProcessIoFailed {
                    command,
                    stream: "exit_status".to_string(),
                    reason: err.to_string(),
                })?;
            return Ok((status, true));
        }

        let remaining = timeout.saturating_sub(start.elapsed());
        thread::sleep(remaining.min(Duration::from_millis(10)));
    }
}

fn find_argv_index_for_path_suffix(argv: &[String], path_suffix: &str) -> Option<usize> {
    argv.iter().position(|arg| arg == path_suffix || Path::new(arg).ends_with(path_suffix))
}

pub fn digest_binary_origin(origin: &BinaryOrigin) -> Result<String, CheckError> {
    serde_json::to_vec(origin)
        .map(|bytes| stable_sha256_hex(&bytes))
        .map_err(|err| CheckError::CheckerInternalError { reason: err.to_string() })
}

fn replay_grade_binary_artifact_digest_identity(
    dispatch: &SolverDispatchRecord,
) -> Result<BinaryArtifactDigestIdentity, CheckError> {
    let identity = dispatch.binary_artifact_digest_identity.clone().ok_or_else(|| {
        CheckError::BinaryArtifactDigestIdentityInvalid {
            reason: "missing dispatch binary artifact digest identity".to_string(),
        }
    })?;
    validate_binary_artifact_digest_identity(&identity)?;
    Ok(identity)
}

fn validate_binary_artifact_digest_identity(
    identity: &BinaryArtifactDigestIdentity,
) -> Result<(), CheckError> {
    let blockers = identity.digest_identity_blockers();
    if blockers.is_empty() {
        Ok(())
    } else {
        Err(CheckError::BinaryArtifactDigestIdentityInvalid { reason: blockers.join("; ") })
    }
}

fn validate_selected_image_identity(
    selected: &BinarySelectedImageIdentity,
) -> Result<(), CheckError> {
    let mut blockers = Vec::new();
    if selected.file_size == 0 {
        blockers.push("selected image file size is zero".to_string());
    }
    if !selected.is_canonical_sha256() {
        blockers.push("selected image digest is not canonical SHA-256 hex".to_string());
    }
    if selected.end_offset().is_none() {
        blockers.push("selected image range overflows u64".to_string());
    }

    if blockers.is_empty() {
        Ok(())
    } else {
        Err(CheckError::BinaryArtifactDigestIdentityInvalid { reason: blockers.join("; ") })
    }
}

fn binary_artifact_digest_identity_label(
    identity: &BinaryArtifactDigestIdentity,
) -> Result<String, CheckError> {
    serde_json::to_string(identity)
        .map_err(|err| CheckError::CheckerInternalError { reason: err.to_string() })
}

fn selected_image_identity_label(
    identity: &BinarySelectedImageIdentity,
) -> Result<String, CheckError> {
    serde_json::to_string(identity)
        .map_err(|err| CheckError::CheckerInternalError { reason: err.to_string() })
}

fn source_backpropagation_gate_identity_sha256(
    gate: &CheckedBinaryCertificateSourceBackpropagationGate,
) -> Result<String, CheckError> {
    gate.validate_structure()?;
    serde_json::to_vec(gate)
        .map(|bytes| stable_sha256_hex(&bytes))
        .map_err(|err| CheckError::CheckerInternalError { reason: err.to_string() })
}

pub fn digest_model_assumptions(assumptions: &[ModelAssumption]) -> String {
    match serde_json::to_vec(assumptions) {
        Ok(bytes) => stable_sha256_hex(&bytes),
        Err(err) => stable_sha256_hex(err.to_string().as_bytes()),
    }
}

pub fn production_checked_certificate_checker_status(
    checker: &str,
    checker_version: &str,
    production_checker_evidence_sha256: &str,
) -> Result<String, CheckError> {
    ProofCertificateProductionCheckerEvidenceRef::new(
        checker,
        checker_version,
        production_checker_evidence_sha256,
    )
    .map(|evidence| evidence.legacy_checker_status())
    .map_err(|reason| CheckError::MalformedProof { reason })
}

#[must_use]
pub fn checked_certificate_status_has_production_checker_evidence(checker: &str) -> bool {
    matches!(
        ProofCertificateProductionCheckerEvidenceRef::from_legacy_checker_status(checker),
        trust_types::ProofCertificateProductionCheckerEvidenceStatus::Present { .. }
    )
}

#[must_use]
pub fn checked_certificate_status_production_checker_evidence(
    checker: &str,
) -> Option<ProofCertificateProductionCheckerEvidenceRef> {
    ProofCertificateProductionCheckerEvidenceRef::from_legacy_checker_status(checker).into_present()
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct NormalizedCertificatePayload {
    schema_version: String,
    dispatch_id: String,
    vc_sha256: String,
    proof_sha256: String,
    proof_export_sha256: String,
    proof_export: SolverProofExportMetadata,
    format: String,
    checker: String,
    checker_version: String,
    solver: String,
    backend: Option<String>,
    query_semantics: SolverQuerySemantics,
    replay: ReplayStatus,
    binary_origin_digest: String,
    binary_artifact_digest_identity: BinaryArtifactDigestIdentity,
    assumption_digest: String,
    replay_transcript_digest: Option<String>,
    checked_at_unix_ms: u64,
}

fn normalized_certificate_payload(
    request: BinaryCertificateCheckRequest<'_>,
    checker: &str,
    checker_version: &str,
    checked_at_unix_ms: u64,
) -> Result<Vec<u8>, CheckError> {
    let origin = request.dispatch.origin.as_ref().ok_or(CheckError::BinaryOriginMissing)?;
    let proof_export = request.export.normalized_metadata();
    let proof_export_sha256 = proof_export.sha256()?;
    serialize_normalized_payload_metadata(&NormalizedCertificatePayload {
        schema_version: CHECKED_BINARY_CERTIFICATE_SCHEMA_VERSION.to_string(),
        dispatch_id: request.dispatch.id.clone(),
        vc_sha256: request.vc_sha256.to_string(),
        proof_sha256: request.export.proof_sha256.clone(),
        proof_export_sha256,
        proof_export,
        format: request.export.format.clone(),
        checker: checker.to_string(),
        checker_version: checker_version.to_string(),
        solver: request.export.solver.clone(),
        backend: request.export.backend.clone(),
        query_semantics: request.dispatch.query_semantics,
        replay: request.dispatch.replay,
        binary_origin_digest: digest_binary_origin(origin)?,
        binary_artifact_digest_identity: replay_grade_binary_artifact_digest_identity(
            request.dispatch,
        )?,
        assumption_digest: request.assumption_digest.to_string(),
        replay_transcript_digest: request.replay_transcript_digest.map(ToString::to_string),
        checked_at_unix_ms,
    })
}

fn serialize_normalized_payload_metadata(
    payload: &NormalizedCertificatePayload,
) -> Result<Vec<u8>, CheckError> {
    serde_json::to_vec(payload)
        .map_err(|err| CheckError::CheckerInternalError { reason: err.to_string() })
}

fn normalized_payload_metadata(bytes: &[u8]) -> Result<NormalizedCertificatePayload, CheckError> {
    serde_json::from_slice(bytes).map_err(|err| CheckError::MalformedProof {
        reason: format!("normalized payload is not valid checked-certificate metadata: {err}"),
    })
}

fn validate_payload_export_metadata_bindings(
    payload: &NormalizedCertificatePayload,
) -> Result<(), CheckError> {
    payload.proof_export.validate_structure()?;

    if payload.proof_export.dispatch_id != payload.dispatch_id {
        return Err(binding_mismatch(
            "proof_export.dispatch_id",
            payload.dispatch_id.as_str(),
            payload.proof_export.dispatch_id.as_str(),
        ));
    }
    if payload.proof_export.vc_sha256 != payload.vc_sha256 {
        return Err(binding_mismatch(
            "proof_export.vc_sha256",
            payload.vc_sha256.as_str(),
            payload.proof_export.vc_sha256.as_str(),
        ));
    }
    if payload.proof_export.query_semantics != payload.query_semantics {
        return Err(binding_mismatch(
            "proof_export.query_semantics",
            format!("{:?}", payload.query_semantics),
            format!("{:?}", payload.proof_export.query_semantics),
        ));
    }
    if payload.proof_export.solver != payload.solver {
        return Err(binding_mismatch(
            "proof_export.solver",
            payload.solver.as_str(),
            payload.proof_export.solver.as_str(),
        ));
    }
    if payload.proof_export.backend != payload.backend {
        return Err(binding_mismatch(
            "proof_export.backend",
            format!("{:?}", &payload.backend),
            format!("{:?}", &payload.proof_export.backend),
        ));
    }
    if payload.proof_export.format != payload.format {
        return Err(binding_mismatch(
            "proof_export.format",
            payload.format.as_str(),
            payload.proof_export.format.as_str(),
        ));
    }
    if payload.proof_export.proof_sha256 != payload.proof_sha256 {
        return Err(binding_mismatch(
            "proof_export.proof_sha256",
            payload.proof_sha256.as_str(),
            payload.proof_export.proof_sha256.as_str(),
        ));
    }
    if payload.proof_export.assumption_digest != payload.assumption_digest {
        return Err(CheckError::AssumptionDigestMismatch {
            expected: payload.assumption_digest.clone(),
            actual: payload.proof_export.assumption_digest.clone(),
        });
    }

    Ok(())
}

fn binding_mismatch(
    field: impl Into<String>,
    expected: impl Into<String>,
    actual: impl Into<String>,
) -> CheckError {
    CheckError::ArtifactBindingMismatch {
        field: field.into(),
        expected: expected.into(),
        actual: actual.into(),
    }
}

fn push_manifest_evidence_mismatch(
    rejections: &mut Vec<CheckedBinaryCertificateProductionManifestRejection>,
    dispatch_id: &str,
    field: &str,
    expected: &str,
    actual: &str,
) {
    if expected != actual {
        rejections.push(
            CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                dispatch_id: dispatch_id.to_string(),
                field: field.to_string(),
                expected: expected.to_string(),
                actual: actual.to_string(),
            },
        );
    }
}

fn push_manifest_digest_mismatch(
    rejections: &mut Vec<CheckedBinaryCertificateProductionManifestRejection>,
    dispatch_id: &str,
    field: &str,
    actual: &str,
) {
    if !is_canonical_sha256_hex(actual) {
        rejections.push(
            CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                dispatch_id: dispatch_id.to_string(),
                field: field.to_string(),
                expected: "canonical lowercase sha256 hex digest".to_string(),
                actual: if actual.trim().is_empty() {
                    "empty".to_string()
                } else {
                    actual.to_string()
                },
            },
        );
    }
}

fn validate_production_manifest_row_acceptance(
    rejections: &mut Vec<CheckedBinaryCertificateProductionManifestRejection>,
    entry: &CheckedBinaryCertificateProductionManifestEntry,
    evidence: &CheckedBinaryCertificateProductionEvidence,
    row_acceptance: &CheckedBinaryCertificateProductionManifestRowAcceptance,
) {
    for (field, value) in [
        (
            "manifest_row_acceptance.manifest_identity_sha256",
            row_acceptance.manifest_identity_sha256.as_str(),
        ),
        (
            "manifest_row_acceptance.production_checker_evidence_sha256",
            row_acceptance.production_checker_evidence_sha256.as_str(),
        ),
        ("manifest_row_acceptance.vc_sha256", row_acceptance.vc_sha256.as_str()),
        ("manifest_row_acceptance.certificate_sha256", row_acceptance.certificate_sha256.as_str()),
        (
            "manifest_row_acceptance.proof_metadata_sha256",
            row_acceptance.proof_metadata_sha256.as_str(),
        ),
        (
            "manifest_row_acceptance.source_backpropagation_gate_sha256",
            row_acceptance.source_backpropagation_gate_sha256.as_str(),
        ),
    ] {
        push_manifest_digest_mismatch(rejections, entry.dispatch_id.as_str(), field, value);
    }
    if let Some(replay_transcript_digest) = row_acceptance.replay_transcript_digest.as_deref() {
        push_manifest_digest_mismatch(
            rejections,
            entry.dispatch_id.as_str(),
            "manifest_row_acceptance.replay_transcript_digest",
            replay_transcript_digest,
        );
    }
    if let Err(err) =
        validate_binary_artifact_digest_identity(&row_acceptance.binary_artifact_digest_identity)
    {
        rejections.push(
            CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                dispatch_id: entry.dispatch_id.clone(),
                field: "manifest_row_acceptance.binary_artifact_digest_identity".to_string(),
                expected: "replay-grade binary artifact digest identity".to_string(),
                actual: err.to_string(),
            },
        );
    }

    push_manifest_evidence_mismatch(
        rejections,
        entry.dispatch_id.as_str(),
        "manifest_row_acceptance.vc_sha256",
        entry.vc_sha256.as_str(),
        row_acceptance.vc_sha256.as_str(),
    );
    push_manifest_evidence_mismatch(
        rejections,
        entry.dispatch_id.as_str(),
        "manifest_row_acceptance.certificate_sha256",
        entry.certificate_sha256.as_str(),
        row_acceptance.certificate_sha256.as_str(),
    );
    push_manifest_evidence_mismatch(
        rejections,
        entry.dispatch_id.as_str(),
        "manifest_row_acceptance.proof_metadata_sha256",
        evidence.proof_export_sha256.as_str(),
        row_acceptance.proof_metadata_sha256.as_str(),
    );
    match evidence.production_checker_evidence_sha256.as_deref() {
        Some(production_checker_evidence_sha256) => push_manifest_evidence_mismatch(
            rejections,
            entry.dispatch_id.as_str(),
            "manifest_row_acceptance.production_checker_evidence_sha256",
            production_checker_evidence_sha256,
            row_acceptance.production_checker_evidence_sha256.as_str(),
        ),
        None => rejections.push(
            CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                dispatch_id: entry.dispatch_id.clone(),
                field: "production_evidence.production_checker_evidence_sha256".to_string(),
                expected: "external production checker evidence digest".to_string(),
                actual: "<missing>".to_string(),
            },
        ),
    }
    if row_acceptance.replay != evidence.replay {
        rejections.push(
            CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                dispatch_id: entry.dispatch_id.clone(),
                field: "manifest_row_acceptance.replay".to_string(),
                expected: format!("{:?}", evidence.replay),
                actual: format!("{:?}", row_acceptance.replay),
            },
        );
    }
    if row_acceptance.replay_transcript_digest != evidence.replay_transcript_digest {
        rejections.push(
            CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                dispatch_id: entry.dispatch_id.clone(),
                field: "manifest_row_acceptance.replay_transcript_digest".to_string(),
                expected: evidence
                    .replay_transcript_digest
                    .as_deref()
                    .unwrap_or("<missing>")
                    .to_string(),
                actual: row_acceptance
                    .replay_transcript_digest
                    .as_deref()
                    .unwrap_or("<missing>")
                    .to_string(),
            },
        );
    }
    if row_acceptance.binary_artifact_digest_identity != evidence.binary_artifact_digest_identity {
        let expected =
            binary_artifact_digest_identity_label(&evidence.binary_artifact_digest_identity)
                .unwrap_or_else(|err| err.to_string());
        let actual =
            binary_artifact_digest_identity_label(&row_acceptance.binary_artifact_digest_identity)
                .unwrap_or_else(|err| err.to_string());
        rejections.push(
            CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                dispatch_id: entry.dispatch_id.clone(),
                field: "manifest_row_acceptance.binary_artifact_digest_identity".to_string(),
                expected,
                actual,
            },
        );
    }
    push_manifest_evidence_mismatch(
        rejections,
        entry.dispatch_id.as_str(),
        "manifest_row_acceptance.source_backpropagation_gate_sha256",
        evidence.source_backpropagation_gate_sha256.as_str(),
        row_acceptance.source_backpropagation_gate_sha256.as_str(),
    );
    match row_acceptance.source_backpropagation_gate_row.as_ref() {
        Some(source_backpropagation_gate_row) => validate_production_source_backpropagation_gate_row(
            rejections,
            entry,
            evidence,
            row_acceptance,
            source_backpropagation_gate_row,
        ),
        None => rejections.push(
            CheckedBinaryCertificateProductionManifestRejection::MissingSourceBackpropagationGateRow {
                dispatch_id: entry.dispatch_id.clone(),
            },
        ),
    }
}

fn validate_production_source_backpropagation_gate_row(
    rejections: &mut Vec<CheckedBinaryCertificateProductionManifestRejection>,
    entry: &CheckedBinaryCertificateProductionManifestEntry,
    evidence: &CheckedBinaryCertificateProductionEvidence,
    row_acceptance: &CheckedBinaryCertificateProductionManifestRowAcceptance,
    gate_row: &CheckedBinaryCertificateProductionSourceBackpropagationGateRow,
) {
    if gate_row.schema_version
        != CHECKED_BINARY_CERTIFICATE_SOURCE_BACKPROPAGATION_GATE_ROW_SCHEMA_VERSION
    {
        rejections.push(
            CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                dispatch_id: entry.dispatch_id.clone(),
                field: "manifest_row_acceptance.source_backpropagation_gate_row.schema_version"
                    .to_string(),
                expected: CHECKED_BINARY_CERTIFICATE_SOURCE_BACKPROPAGATION_GATE_ROW_SCHEMA_VERSION
                    .to_string(),
                actual: gate_row.schema_version.clone(),
            },
        );
    }

    for (field, value) in [
        (
            "manifest_row_acceptance.source_backpropagation_gate_row.manifest_identity_sha256",
            gate_row.manifest_identity_sha256.as_str(),
        ),
        (
            "manifest_row_acceptance.source_backpropagation_gate_row.source_backpropagation_gate_sha256",
            gate_row.source_backpropagation_gate_sha256.as_str(),
        ),
        (
            "manifest_row_acceptance.source_backpropagation_gate_row.vc_sha256",
            gate_row.vc_sha256.as_str(),
        ),
        (
            "manifest_row_acceptance.source_backpropagation_gate_row.certificate_sha256",
            gate_row.certificate_sha256.as_str(),
        ),
        (
            "manifest_row_acceptance.source_backpropagation_gate_row.origin_sha256",
            gate_row.origin_sha256.as_str(),
        ),
        (
            "manifest_row_acceptance.source_backpropagation_gate_row.assumption_digest",
            gate_row.assumption_digest.as_str(),
        ),
    ] {
        push_manifest_digest_mismatch(rejections, entry.dispatch_id.as_str(), field, value);
    }
    if let Some(replay_transcript_digest) = gate_row.replay_transcript_digest.as_deref() {
        push_manifest_digest_mismatch(
            rejections,
            entry.dispatch_id.as_str(),
            "manifest_row_acceptance.source_backpropagation_gate_row.replay_transcript_digest",
            replay_transcript_digest,
        );
    }
    if let Err(err) = validate_selected_image_identity(&gate_row.selected_image_identity) {
        rejections
            .push(CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
            dispatch_id: entry.dispatch_id.clone(),
            field:
                "manifest_row_acceptance.source_backpropagation_gate_row.selected_image_identity"
                    .to_string(),
            expected: "replay-grade selected image identity".to_string(),
            actual: err.to_string(),
        });
    }
    if let Err(err) = validate_relative_manifest_path(
        "manifest_row_acceptance.source_backpropagation_gate_row.certificate_path",
        &gate_row.certificate_path,
    )
    .and_then(|_| {
        validate_manifest_certificate_path_matches_digest(
            "manifest_row_acceptance.source_backpropagation_gate_row.certificate_path",
            &gate_row.certificate_path,
            &gate_row.certificate_sha256,
        )
    }) {
        rejections.push(
            CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                dispatch_id: entry.dispatch_id.clone(),
                field: "manifest_row_acceptance.source_backpropagation_gate_row.certificate_path"
                    .to_string(),
                expected: "content-addressed checked certificate path".to_string(),
                actual: err.to_string(),
            },
        );
    }

    push_manifest_evidence_mismatch(
        rejections,
        entry.dispatch_id.as_str(),
        "manifest_row_acceptance.source_backpropagation_gate_row.manifest_identity_sha256",
        row_acceptance.manifest_identity_sha256.as_str(),
        gate_row.manifest_identity_sha256.as_str(),
    );
    push_manifest_evidence_mismatch(
        rejections,
        entry.dispatch_id.as_str(),
        "manifest_row_acceptance.source_backpropagation_gate_row.vc_sha256",
        entry.vc_sha256.as_str(),
        gate_row.vc_sha256.as_str(),
    );
    push_manifest_evidence_mismatch(
        rejections,
        entry.dispatch_id.as_str(),
        "manifest_row_acceptance.source_backpropagation_gate_row.certificate_sha256",
        entry.certificate_sha256.as_str(),
        gate_row.certificate_sha256.as_str(),
    );
    push_manifest_evidence_mismatch(
        rejections,
        entry.dispatch_id.as_str(),
        "manifest_row_acceptance.source_backpropagation_gate_row.origin_sha256",
        evidence.origin_sha256.as_str(),
        gate_row.origin_sha256.as_str(),
    );
    push_manifest_evidence_mismatch(
        rejections,
        entry.dispatch_id.as_str(),
        "manifest_row_acceptance.source_backpropagation_gate_row.assumption_digest",
        evidence.assumption_digest.as_str(),
        gate_row.assumption_digest.as_str(),
    );
    push_manifest_evidence_mismatch(
        rejections,
        entry.dispatch_id.as_str(),
        "manifest_row_acceptance.source_backpropagation_gate_row.source_backpropagation_gate_sha256",
        row_acceptance.source_backpropagation_gate_sha256.as_str(),
        gate_row.source_backpropagation_gate_sha256.as_str(),
    );
    push_manifest_evidence_mismatch(
        rejections,
        entry.dispatch_id.as_str(),
        "manifest_row_acceptance.source_backpropagation_gate_row.source_backpropagation_gate_sha256",
        evidence.source_backpropagation_gate_sha256.as_str(),
        gate_row.source_backpropagation_gate_sha256.as_str(),
    );

    match source_backpropagation_gate_identity_sha256(&gate_row.source_backpropagation_gate) {
        Ok(computed_gate_sha256) => push_manifest_evidence_mismatch(
            rejections,
            entry.dispatch_id.as_str(),
            "manifest_row_acceptance.source_backpropagation_gate_row.source_backpropagation_gate_sha256",
            computed_gate_sha256.as_str(),
            gate_row.source_backpropagation_gate_sha256.as_str(),
        ),
        Err(err) => rejections.push(
            CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                dispatch_id: entry.dispatch_id.clone(),
                field:
                    "manifest_row_acceptance.source_backpropagation_gate_row.source_backpropagation_gate"
                        .to_string(),
                expected: "valid source-backpropagation gate".to_string(),
                actual: err.to_string(),
            },
        ),
    }

    if gate_row.source_backpropagation_gate.source_backpropagation_allowed {
        validate_open_source_backpropagation_replay_contract(
            rejections,
            entry,
            evidence,
            row_acceptance,
            gate_row,
        );
    }

    if gate_row.replay != evidence.replay {
        rejections.push(
            CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                dispatch_id: entry.dispatch_id.clone(),
                field: "manifest_row_acceptance.source_backpropagation_gate_row.replay".to_string(),
                expected: format!("{:?}", evidence.replay),
                actual: format!("{:?}", gate_row.replay),
            },
        );
    }
    if gate_row.replay_transcript_digest != evidence.replay_transcript_digest {
        rejections
            .push(CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
            dispatch_id: entry.dispatch_id.clone(),
            field:
                "manifest_row_acceptance.source_backpropagation_gate_row.replay_transcript_digest"
                    .to_string(),
            expected: evidence
                .replay_transcript_digest
                .as_deref()
                .unwrap_or("<missing>")
                .to_string(),
            actual: gate_row.replay_transcript_digest.as_deref().unwrap_or("<missing>").to_string(),
        });
    }

    match evidence.binary_artifact_digest_identity.selected_image.as_ref() {
        Some(expected_selected_image)
            if expected_selected_image == &gate_row.selected_image_identity => {}
        Some(expected_selected_image) => {
            let expected = selected_image_identity_label(expected_selected_image)
                .unwrap_or_else(|err| err.to_string());
            let actual = selected_image_identity_label(&gate_row.selected_image_identity)
                .unwrap_or_else(|err| err.to_string());
            rejections.push(
                CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                    dispatch_id: entry.dispatch_id.clone(),
                    field:
                        "manifest_row_acceptance.source_backpropagation_gate_row.selected_image_identity"
                            .to_string(),
                    expected,
                    actual,
                },
            );
        }
        None => rejections.push(
            CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                dispatch_id: entry.dispatch_id.clone(),
                field: "production_evidence.binary_artifact_digest_identity.selected_image"
                    .to_string(),
                expected: "selected image identity".to_string(),
                actual: "<missing>".to_string(),
            },
        ),
    }

    let recomputed_identity = CheckedBinaryCertificateManifestIdentityEntry {
        schema_version: CHECKED_BINARY_CERTIFICATE_MANIFEST_IDENTITY_SCHEMA_VERSION.to_string(),
        manifest_schema_version: CHECKED_BINARY_CERTIFICATE_MANIFEST_SCHEMA_VERSION.to_string(),
        checker_selection: CheckedBinaryCertificateCheckerSelection {
            checker: evidence.checker.clone(),
            checker_version: evidence.checker_version.clone(),
            format: evidence.format.clone(),
        },
        replay_transcript: CheckedBinaryCertificateReplayTranscriptBinding {
            replay: gate_row.replay,
            replay_transcript_digest: gate_row.replay_transcript_digest.clone(),
        },
        artifact_identity: CheckedBinaryCertificateArtifactIdentity {
            dispatch_id: entry.dispatch_id.clone(),
            vc_sha256: gate_row.vc_sha256.clone(),
            origin_sha256: gate_row.origin_sha256.clone(),
            proof_sha256: evidence.proof_sha256.clone(),
            proof_export_sha256: evidence.proof_export_sha256.clone(),
            certificate_sha256: gate_row.certificate_sha256.clone(),
            content_sha256: gate_row.certificate_sha256.clone(),
            certificate_path: gate_row.certificate_path.clone(),
            binary_artifact_digest_identity: evidence.binary_artifact_digest_identity.clone(),
        },
        production_checker_evidence_sha256: row_acceptance
            .production_checker_evidence_sha256
            .clone(),
        source_backpropagation_gate: gate_row.source_backpropagation_gate.clone(),
    };
    match recomputed_identity.sha256() {
        Ok(recomputed_manifest_identity_sha256) => push_manifest_evidence_mismatch(
            rejections,
            entry.dispatch_id.as_str(),
            "manifest_row_acceptance.source_backpropagation_gate_row.manifest_identity_sha256",
            recomputed_manifest_identity_sha256.as_str(),
            gate_row.manifest_identity_sha256.as_str(),
        ),
        Err(err) => rejections.push(
            CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                dispatch_id: entry.dispatch_id.clone(),
                field:
                    "manifest_row_acceptance.source_backpropagation_gate_row.manifest_identity_sha256"
                        .to_string(),
                expected: "manifest identity recomputable from source gate row".to_string(),
                actual: err.to_string(),
            },
        ),
    }
}

fn validate_open_source_backpropagation_replay_contract(
    rejections: &mut Vec<CheckedBinaryCertificateProductionManifestRejection>,
    entry: &CheckedBinaryCertificateProductionManifestEntry,
    evidence: &CheckedBinaryCertificateProductionEvidence,
    row_acceptance: &CheckedBinaryCertificateProductionManifestRowAcceptance,
    gate_row: &CheckedBinaryCertificateProductionSourceBackpropagationGateRow,
) {
    for (field, replay) in [
        ("production_evidence.replay", evidence.replay),
        ("manifest_row_acceptance.replay", row_acceptance.replay),
        ("manifest_row_acceptance.source_backpropagation_gate_row.replay", gate_row.replay),
    ] {
        if replay != ReplayStatus::Replayed {
            rejections.push(
                CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                    dispatch_id: entry.dispatch_id.clone(),
                    field: field.to_string(),
                    expected: format!("{:?}", ReplayStatus::Replayed),
                    actual: format!("{:?}", replay),
                },
            );
        }
    }

    for (field, digest) in [
        (
            "production_evidence.replay_transcript_digest",
            evidence.replay_transcript_digest.as_deref(),
        ),
        (
            "manifest_row_acceptance.replay_transcript_digest",
            row_acceptance.replay_transcript_digest.as_deref(),
        ),
        (
            "manifest_row_acceptance.source_backpropagation_gate_row.replay_transcript_digest",
            gate_row.replay_transcript_digest.as_deref(),
        ),
    ] {
        match digest {
            Some(replay_transcript_digest) => {
                push_manifest_digest_mismatch(
                    rejections,
                    entry.dispatch_id.as_str(),
                    field,
                    replay_transcript_digest,
                );
            }
            None => rejections.push(
                CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                    dispatch_id: entry.dispatch_id.clone(),
                    field: field.to_string(),
                    expected: "canonical replay transcript digest".to_string(),
                    actual: "<missing>".to_string(),
                },
            ),
        }
    }

    if !evidence.binary_artifact_digest_identity.digest_identity_allows_replay() {
        rejections.push(
            CheckedBinaryCertificateProductionManifestRejection::ProductionEvidenceMismatch {
                dispatch_id: entry.dispatch_id.clone(),
                field: "production_evidence.binary_artifact_digest_identity".to_string(),
                expected: "replay-grade binary artifact digest identity".to_string(),
                actual: evidence
                    .binary_artifact_digest_identity
                    .digest_identity_blockers()
                    .join("; "),
            },
        );
    }
}

fn checked_certificate_artifact_path_unchecked(root: &Path, certificate_sha256: &str) -> PathBuf {
    root.join(CHECKED_BINARY_CERTIFICATE_ARTIFACT_DIR)
        .join(&certificate_sha256[..2])
        .join(format!("{certificate_sha256}.{CHECKED_BINARY_CERTIFICATE_ARTIFACT_SUFFIX}"))
}

fn checked_certificate_manifest_relative_path() -> PathBuf {
    PathBuf::from(CHECKED_BINARY_CERTIFICATE_ARTIFACT_DIR)
        .join(CHECKED_BINARY_CERTIFICATE_MANIFEST_FILENAME)
}

fn checked_certificate_audit_export_bundle_relative_path() -> PathBuf {
    PathBuf::from(CHECKED_BINARY_CERTIFICATE_ARTIFACT_DIR)
        .join(CHECKED_BINARY_CERTIFICATE_AUDIT_EXPORT_BUNDLE_FILENAME)
}

fn checked_certificate_audit_export_relative_path(
    certificate_sha256: &str,
) -> Result<PathBuf, CheckError> {
    validate_canonical_sha256_hex("audit export certificate_sha256", certificate_sha256)?;
    Ok(PathBuf::from(CHECKED_BINARY_CERTIFICATE_ARTIFACT_DIR)
        .join(CHECKED_BINARY_CERTIFICATE_AUDIT_EXPORT_DIR)
        .join(&certificate_sha256[..2])
        .join(format!("{certificate_sha256}.{CHECKED_BINARY_CERTIFICATE_AUDIT_EXPORT_SUFFIX}")))
}

fn solver_proof_export_metadata_path(
    root: &Path,
    metadata_sha256: &str,
) -> Result<PathBuf, crate::CertError> {
    validate_sha256_hex(metadata_sha256)?;
    Ok(root
        .join(CHECKED_BINARY_CERTIFICATE_ARTIFACT_DIR)
        .join(SOLVER_PROOF_EXPORT_ARTIFACT_DIR)
        .join(SOLVER_PROOF_EXPORT_METADATA_DIR)
        .join(&metadata_sha256[..2])
        .join(format!("{metadata_sha256}.{SOLVER_PROOF_EXPORT_METADATA_SUFFIX}")))
}

fn solver_proof_export_payload_path(
    root: &Path,
    proof_sha256: &str,
    format: &str,
) -> Result<PathBuf, crate::CertError> {
    validate_sha256_hex(proof_sha256)?;
    Ok(root
        .join(CHECKED_BINARY_CERTIFICATE_ARTIFACT_DIR)
        .join(SOLVER_PROOF_EXPORT_ARTIFACT_DIR)
        .join(SOLVER_PROOF_EXPORT_PAYLOAD_DIR)
        .join(&proof_sha256[..2])
        .join(format!(
            "{proof_sha256}.{}.{}",
            safe_proof_format_path_component(format),
            SOLVER_PROOF_EXPORT_PAYLOAD_SUFFIX
        )))
}

fn safe_proof_format_path_component(format: &str) -> String {
    let safe = format
        .chars()
        .filter(|ch| ch.is_ascii_alphanumeric() || matches!(ch, '-' | '_'))
        .collect::<String>();
    if safe.is_empty() { "proof".to_string() } else { safe }
}

fn write_content_addressed_file(
    path: &Path,
    digest: &str,
    bytes: &[u8],
) -> Result<(), crate::CertError> {
    let parent = path.parent().ok_or_else(|| crate::CertError::IoError {
        reason: format!("content-addressed path has no parent: {}", path.display()),
    })?;
    std::fs::create_dir_all(parent)?;
    let tmp_path = parent.join(format!(".{digest}.tmp"));
    std::fs::write(&tmp_path, bytes)?;
    std::fs::rename(&tmp_path, path)?;
    Ok(())
}

fn validate_sha256_hex(value: &str) -> Result<(), crate::CertError> {
    if is_canonical_sha256_hex(value) {
        Ok(())
    } else {
        Err(crate::CertError::InvalidCertificate {
            reason: format!("expected canonical lowercase sha256 hex digest, got `{value}`"),
        })
    }
}

fn validate_canonical_sha256_hex(field: &str, value: &str) -> Result<(), CheckError> {
    if is_canonical_sha256_hex(value) {
        Ok(())
    } else {
        Err(CheckError::MalformedProof {
            reason: format!("{field} is not a canonical lowercase sha256 hex digest"),
        })
    }
}

fn validate_relative_manifest_path(field: &str, path: &Path) -> Result<(), CheckError> {
    if path.as_os_str().is_empty() {
        return Err(CheckError::MalformedProof { reason: format!("{field} is empty") });
    }
    if path.is_absolute() {
        return Err(CheckError::MalformedProof {
            reason: format!("{field} must be relative to the certificate store"),
        });
    }
    if path.components().any(|component| {
        matches!(
            component,
            Component::CurDir | Component::ParentDir | Component::RootDir | Component::Prefix(_)
        )
    }) {
        return Err(CheckError::MalformedProof {
            reason: format!("{field} must not escape the certificate store"),
        });
    }

    Ok(())
}

fn validate_artifact_root_relative_path(field: &str, path: &Path) -> Result<(), CheckError> {
    validate_relative_manifest_path(field, path)?;
    if !path.starts_with(CHECKED_BINARY_CERTIFICATE_ARTIFACT_DIR) {
        return Err(CheckError::MalformedProof {
            reason: format!("{field} must stay under `{CHECKED_BINARY_CERTIFICATE_ARTIFACT_DIR}`"),
        });
    }

    Ok(())
}

fn validate_manifest_certificate_path_matches_digest(
    field: &str,
    path: &Path,
    certificate_sha256: &str,
) -> Result<(), CheckError> {
    let expected = checked_certificate_artifact_path_unchecked(Path::new(""), certificate_sha256);
    if path != expected {
        return Err(CheckError::MalformedProof {
            reason: format!(
                "{field} must match content-addressed path `{}` for manifest.certificate_sha256 `{certificate_sha256}`",
                expected.display()
            ),
        });
    }

    Ok(())
}

fn validate_content_addressed_artifact_ref_path(
    artifact_ref: &CheckedBinaryCertificateArtifactRef,
) -> Result<(), crate::CertError> {
    validate_sha256_hex(&artifact_ref.content_sha256)?;
    if artifact_ref
        .path
        .components()
        .any(|component| matches!(component, Component::CurDir | Component::ParentDir))
    {
        return Err(crate::CertError::InvalidCertificate {
            reason: format!(
                "content-addressed artifact path must not contain relative traversal components: {}",
                artifact_ref.path.display()
            ),
        });
    }

    let expected =
        checked_certificate_artifact_path_unchecked(Path::new(""), &artifact_ref.content_sha256);
    if !artifact_ref.path.ends_with(&expected) {
        return Err(crate::CertError::InvalidCertificate {
            reason: format!(
                "content-addressed artifact path `{}` must end with `{}` for digest `{}`",
                artifact_ref.path.display(),
                expected.display(),
                artifact_ref.content_sha256
            ),
        });
    }

    Ok(())
}

fn read_root_relative_json(
    root: &Path,
    field: &str,
    relative_path: &Path,
) -> Result<(String, String), crate::CertError> {
    validate_artifact_root_relative_path(field, relative_path)
        .map_err(|err| crate::CertError::InvalidCertificate { reason: err.to_string() })?;
    let json = std::fs::read_to_string(root.join(relative_path))?;
    let digest = stable_sha256_hex(json.as_bytes());
    Ok((json, digest))
}

fn write_json_file(path: &Path, json: &str) -> Result<(), crate::CertError> {
    if let Some(parent) = path.parent()
        && !parent.as_os_str().is_empty()
    {
        std::fs::create_dir_all(parent)?;
    }
    std::fs::write(path, json.as_bytes())?;
    Ok(())
}

fn is_canonical_sha256_hex(value: &str) -> bool {
    value.len() == 64
        && value.bytes().all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}

fn dispatch_has_raw_solver_proof_bytes(dispatch: &SolverDispatchRecord) -> bool {
    matches!(dispatch.result, Some(VerificationResult::Proved { proof_certificate: Some(_), .. }))
}
