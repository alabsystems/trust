//! Binary decompilation report adapters.
//!
//! These helpers summarize shared `trust-types` binary decompilation artifacts
//! without changing their trust level. They are independent of `targo-trust`.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use serde::{Deserialize, Serialize};
use trust_types::stable_sha256_hex;
use trust_types::{
    Aarch64AtomicSemanticFact, Aarch64ExclusiveMonitorSemantics, Aarch64SyncBoundaryKind,
    Aarch64SyncBoundarySemanticFact, Aarch64SyncOrdering, Aarch64SyncScope, BinaryAddressRange,
    BinaryArtifactDigest, BinaryArtifactDigestIdentity, BinaryArtifactFormat,
    BinaryArtifactMetadata, BinaryOrigin, BinarySelectedImageIdentity,
    BinarySourceProvenanceDiagnostic, BinarySourceProvenanceSummary, BinaryVerificationStatus,
    BinaryVerificationSummary, DecompilationArtifact, DecompileTarget, DecompiledFunction,
    DecompiledOutput, Formula, MemoryAccessKind, MemoryOrderingSemantics, PreservedSymbolicFormula,
    PreservedSymbolicFormulaEvidence, ProofCertificateProductionCheckerEvidenceStatus,
    ProofCertificateStatus, ReconstructionSummary, ReconstructionValidationRecord,
    ReconstructionValidationStatus, ReplayStatus, SerializableVc, SolverDispatchRecord,
    SolverDispatchStatus, SolverFallbackAttemptEvidence, SolverQuerySemantics,
    SolverTimeoutEvidence, SolverTimeoutEvidenceStatus, Sort, SourceSpan, TargetValidationBlocker,
    TrustLevel, UnsupportedFamilyCount, UnsupportedLedger, VerificationResult,
    collect_free_var_decls,
};

const BINARY_SOURCE_PROVENANCE_ARTIFACT_SCHEMA_VERSION: &str =
    "trust-report.binary-source-provenance-artifact.v1";
const SOURCE_BACKPROPAGATION_GATE_SCHEMA_VERSION: &str =
    "trust-proof-cert.source-backpropagation-gate.v1";

/// Report-friendly summary of a binary decompilation artifact.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct BinaryDecompilationReport {
    /// Shared decompilation artifact schema version.
    pub schema_version: u32,
    /// Binary path when known.
    pub binary_path: Option<String>,
    /// Loader/container format.
    pub format: BinaryArtifactFormat,
    /// Target architecture reported by the artifact.
    pub architecture: String,
    /// Binary entry point when known.
    pub entry_point: Option<u64>,
    /// Display form of `entry_point`, e.g. `0x401000`.
    pub entry_point_display: Option<String>,
    /// Requested decompilation target.
    pub target: DecompileTarget,
    /// Artifact trust level copied exactly from `DecompilationArtifact::trust_level`.
    pub trust_level: TrustLevel,
    /// Exact digest-level identity for the parsed root artifact and selected image.
    #[serde(default)]
    pub digest_identity: BinaryDigestIdentityReport,
    /// Proof-grade gate result for the artifact-level verification evidence.
    pub proof_grade_gate: BinaryProofGradeGateReport,
    /// Unified unresolved blocker ledger for JSON and terminal consumers.
    #[serde(default)]
    pub unresolved_blockers: BinaryUnresolvedBlockerLedgerReport,
    /// Unsupported ledger summary for artifact-level unsupported records.
    pub unsupported: BinaryUnsupportedLedgerReport,
    /// Source provenance recovery and source-backpropagation gate summary.
    #[serde(default)]
    pub source_provenance: BinarySourceProvenanceReport,
    /// Fail-closed source-backpropagation release gate derived from binary evidence.
    #[serde(default)]
    pub source_backpropagation_gate: BinarySourceBackpropagationGateReport,
    /// Reconstructed target-output validation blockers and preserved symbolic formulas.
    #[serde(default)]
    pub reconstruction: BinaryReconstructionReport,
    /// Verification summary for artifact-level binary VCs.
    pub verification: BinaryVerificationReport,
    /// Per-function summaries.
    pub functions: Vec<BinaryFunctionReport>,
}

/// Narrow proof-evidence summary for binary decompilation report/certificate integration.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryDecompilationProofEvidenceReport {
    /// Shared decompilation artifact schema version.
    pub schema_version: u32,
    /// Binary path when known.
    pub binary_path: Option<String>,
    /// Loader/container format.
    pub format: BinaryArtifactFormat,
    /// Target architecture reported by the artifact.
    pub architecture: String,
    /// Artifact trust level copied exactly from `DecompilationArtifact::trust_level`.
    pub trust_level: TrustLevel,
    /// Exact digest-level identity for the parsed root artifact and selected image.
    #[serde(default)]
    pub digest_identity: BinaryDigestIdentityReport,
    /// Combined artifact and verification unsupported ledger records used by the gate.
    pub unsupported_ledger_records: usize,
    /// Required binary VC count reported by the verifier.
    pub total_vcs: usize,
    /// Number of solver dispatch records available as evidence.
    pub solver_dispatches: usize,
    /// Solver dispatch counts grouped by exact dispatch status variant name.
    pub solver_dispatch_status_counts: BTreeMap<String, usize>,
    /// Artifact-level replay status.
    pub replay: ReplayStatus,
    /// Replay counts grouped by exact replay status variant name.
    pub replay_status_counts: BTreeMap<String, usize>,
    /// Checked certificate coverage derived from per-VC dispatch records.
    pub checked_certificate_coverage: BinaryCertificateCheckReport,
    /// Total raw solver proof bytes attached to raw solver results.
    pub raw_solver_proof_byte_count: usize,
    /// Proof-grade gate result for the artifact-level verification evidence.
    pub proof_grade_gate: BinaryProofGradeGateReport,
    /// Unified unresolved blocker ledger for JSON and terminal consumers.
    #[serde(default)]
    pub unresolved_blockers: BinaryUnresolvedBlockerLedgerReport,
}

/// Report-friendly digest identity for the parsed binary artifact.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryDigestIdentityReport {
    /// True only when the root artifact and selected image carry exact canonical digests.
    pub proof_grade_ready: bool,
    /// Root artifact byte length used to bound selected-image ranges.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub root_artifact_byte_len: Option<u64>,
    /// Full root artifact digest.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub root_artifact_digest: Option<BinaryArtifactDigest>,
    /// Selected loader image identity.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub selected_image: Option<BinarySelectedImageIdentityReport>,
    /// Fail-closed digest identity blockers.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub blockers: Vec<String>,
}

/// Report-friendly selected-image digest identity.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinarySelectedImageIdentityReport {
    /// Offset of the selected image inside the root artifact.
    pub file_offset: u64,
    /// Number of file bytes covered by the selected image.
    pub file_size: u64,
    /// Exclusive end offset, when the range does not overflow.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub end_offset: Option<u64>,
    /// SHA-256 digest of the selected image bytes.
    pub sha256: String,
}

/// Report-friendly dispatch-level digest identity used by replay evidence.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryReplayDigestIdentityReport {
    /// True when this dispatch claims `ReplayStatus::Replayed` and must bind replay to exact bytes.
    pub required: bool,
    /// True when digest identity is either not required or is exact enough for replay evidence.
    pub proof_grade_ready: bool,
    /// Digest identity copied from the solver dispatch record.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub identity: Option<BinaryArtifactDigestIdentity>,
    /// Root artifact digest copied into a stable report field for direct JSON consumers.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub root_artifact_digest: Option<BinaryArtifactDigest>,
    /// Selected-image byte range and digest copied into a report field with end-offset detail.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub selected_image_identity: Option<BinarySelectedImageIdentityReport>,
    /// Fail-closed replay digest identity blockers.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub blockers: Vec<String>,
}

/// Report-facing certificate identity for one solver dispatch.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryCheckedCertificateIdentityReport {
    /// True when this dispatch is a proof-required UNSAT VC under counterexample semantics.
    pub required: bool,
    /// True only when the certificate status is checked and carries canonical checker/format/digest identity.
    pub checked_identity_ready: bool,
    /// True only when checked identity and production-checker evidence are both present.
    pub proof_grade_ready: bool,
    /// Stable certificate status label used by terminal output.
    pub status: String,
    /// Checked certificate checker identity, when the dispatch carries one.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub checker: Option<String>,
    /// Certificate format, when present.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub format: Option<String>,
    /// Certificate artifact SHA-256, when present.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sha256: Option<String>,
    /// Manifest/artifact path for unchecked certificate candidates.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub artifact_path: Option<String>,
    /// Production-checker evidence carried by a checked certificate status.
    pub production_checker_evidence: ProofCertificateProductionCheckerEvidenceStatus,
    /// True only when production-checker evidence parsed successfully.
    pub production_checked: bool,
    /// Fail-closed identity blockers for this dispatch.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub blockers: Vec<String>,
}

impl Default for BinaryCheckedCertificateIdentityReport {
    fn default() -> Self {
        Self {
            required: false,
            checked_identity_ready: false,
            proof_grade_ready: false,
            status: "not-requested".to_string(),
            checker: None,
            format: None,
            sha256: None,
            artifact_path: None,
            production_checker_evidence: default_production_checker_evidence_status(),
            production_checked: false,
            blockers: vec![],
        }
    }
}

/// Report-friendly unresolved blocker ledger.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryUnresolvedBlockerLedgerReport {
    /// Total unresolved blocker entries.
    pub total_blockers: usize,
    /// Blocker counts grouped by evidence family.
    #[serde(default)]
    pub by_family: BTreeMap<String, usize>,
    /// Actionable blocker entries.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub entries: Vec<BinaryUnresolvedBlockerReport>,
}

/// One unresolved blocker entry surfaced for hostile-review diagnostics.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryUnresolvedBlockerReport {
    /// Evidence family that owns the blocker, e.g. certificate, replay, digest_identity.
    pub family: String,
    /// Producing stage, when known.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub stage: Option<String>,
    /// Stable feature or rejection kind.
    pub feature: String,
    /// Human-readable reason.
    pub reason: String,
    /// Solver dispatch id, when the blocker is per-VC.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub dispatch_id: Option<String>,
    /// Binary location, when known.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub location: Option<BinaryLocationReport>,
}

/// Report-friendly summary for one recovered binary function.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct BinaryFunctionReport {
    /// Recovered function name.
    pub name: String,
    /// Function entry address.
    pub entry: u64,
    /// Display form of `entry`, e.g. `0x401000`.
    pub entry_display: String,
    /// Optional recovered address range.
    pub address_range: Option<BinaryAddressRangeReport>,
    /// Optional instruction-origin metadata for the function entry.
    pub location: Option<BinaryLocationReport>,
    /// Per-instruction provenance recovered for this function.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub instruction_provenance: Vec<BinaryInstructionProvenanceReport>,
    /// Function trust level copied exactly from `DecompiledFunction::trust_level`.
    pub trust_level: TrustLevel,
    /// Proof-grade gate result for this function's binary VC evidence.
    pub proof_grade_gate: BinaryProofGradeGateReport,
    /// Unsupported ledger summary for this function.
    pub unsupported: BinaryUnsupportedLedgerReport,
    /// Verification summary for this function.
    pub verification: BinaryVerificationReport,
}

/// Report-friendly summary of a binary verification result.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct BinaryVerificationReport {
    /// Overall verification status copied from `BinaryVerificationSummary::status`.
    pub status: BinaryVerificationStatus,
    /// Verification trust level copied exactly from `BinaryVerificationSummary::trust_level`.
    pub trust_level: TrustLevel,
    /// Total VCs reported by the verifier.
    pub total_vcs: usize,
    /// Proved VC count.
    pub proved: usize,
    /// Failed/refuted VC count.
    pub failed: usize,
    /// Unknown VC count.
    pub unknown: usize,
    /// Timed-out VC count.
    pub timeout: usize,
    /// Unsupported VC count.
    pub unsupported: usize,
    /// Rejected VC count.
    pub rejected: usize,
    /// Artifact-level replay status.
    pub replay: ReplayStatus,
    /// Proof-grade gate result for this verification summary.
    pub proof_grade_gate: BinaryProofGradeGateReport,
    /// Unified unresolved blocker ledger for JSON and terminal consumers.
    #[serde(default)]
    pub unresolved_blockers: BinaryUnresolvedBlockerLedgerReport,
    /// Unsupported ledger summary attached to verification.
    pub unsupported_ledger: BinaryUnsupportedLedgerReport,
    /// Solver dispatch counts grouped by exact dispatch status variant name.
    pub vc_status_counts: BTreeMap<String, usize>,
    /// Replay counts grouped by exact replay status variant name.
    pub replay_status_counts: BTreeMap<String, usize>,
    /// Certificate candidate/check coverage derived from per-VC dispatch records.
    pub certificate_checks: BinaryCertificateCheckReport,
    /// Per-VC solver dispatch records.
    pub solver_dispatches: Vec<BinarySolverDispatchReport>,
}

/// Report-friendly summary of a solver dispatch record.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinarySolverDispatchReport {
    /// Stable dispatch id.
    pub id: String,
    /// Function associated with the VC, when known.
    pub function: Option<String>,
    /// Binary instruction location for the VC, when known.
    pub location: Option<BinaryLocationReport>,
    /// Solver name.
    pub solver: String,
    /// Dispatch status copied exactly from the solver dispatch record.
    pub status: SolverDispatchStatus,
    /// Stable display label for the VC kind, even when the full VC is unavailable.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub vc_kind: Option<String>,
    /// Stable per-VC formula summary for schema-aware report consumers.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub vc_formula: Option<BinaryVcFormulaSummaryReport>,
    /// Query semantics copied from the dispatch record.
    pub query_semantics: SolverQuerySemantics,
    /// Result status derived from `VerificationResult`, when a result is attached.
    pub result_status: Option<String>,
    /// Release-facing timeout policy and backend attestation evidence.
    #[serde(default)]
    pub timeout_evidence: BinarySolverTimeoutEvidenceReport,
    /// Per-attempt router fallback evidence for this dispatch.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub fallback_attempts: Vec<SolverFallbackAttemptEvidence>,
    /// Raw dispatch diagnostics preserved for release-gate reviewers.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<String>,
    /// Dispatch-level binary digest identity required before replay can be proof-grade evidence.
    #[serde(default)]
    pub replay_digest_identity: BinaryReplayDigestIdentityReport,
    /// Structured replay boundary evidence extracted from dispatch diagnostics.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub replay_boundary_evidence: Vec<BinaryReplayBoundaryEvidenceReport>,
    /// Proof certificate status copied from the dispatch record.
    pub certificate: ProofCertificateStatus,
    /// Stable checked-certificate identity summary for hostile-review JSON/text consumers.
    #[serde(default)]
    pub checked_certificate_identity: BinaryCheckedCertificateIdentityReport,
    /// True only when certificate evidence has been independently checked.
    pub certificate_checked: bool,
    /// Production-checker evidence carried by the checked certificate status.
    #[serde(default = "default_production_checker_evidence_status")]
    pub production_checker_evidence: ProofCertificateProductionCheckerEvidenceStatus,
    /// True only when the checked certificate carries valid production-checker evidence.
    #[serde(default)]
    pub production_checked: bool,
    /// True when a raw solver proof blob is attached to the raw solver result.
    pub raw_solver_proof_bytes: bool,
    /// Raw solver proof byte length attached to the raw solver result.
    #[serde(default)]
    pub raw_solver_proof_byte_count: usize,
    /// Replay status copied exactly from the dispatch record.
    pub replay: ReplayStatus,
}

/// Report-facing replay evidence for syscall/exception/trap boundaries.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryReplayBoundaryEvidenceReport {
    /// Boundary kind reported by replay, e.g. syscall, exception, or trap.
    pub kind: String,
    /// Architecture whose decoder produced this boundary evidence.
    pub architecture: String,
    /// Boundary instruction address.
    pub instruction_address: u64,
    /// Display form of `instruction_address`, e.g. `0x401010`.
    pub instruction_address_display: String,
    /// Replay trace step that reached the boundary, when known.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub step: Option<u32>,
    /// Exact instruction bytes bound to this boundary.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub instruction_bytes: Vec<u8>,
    /// Hex display form of `instruction_bytes`.
    pub instruction_bytes_hex: String,
    /// Decoded opcode for the boundary instruction.
    pub opcode: String,
    /// Decoder encoding value for the boundary instruction.
    pub encoding: u32,
    /// Boundary immediate value, when decoded.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub immediate: Option<u64>,
    /// Boundary semantics status carried by replay.
    pub semantics: String,
    /// Producer diagnostic explaining the boundary semantics status.
    pub diagnostic: String,
    /// True only when this boundary has an exact semantics witness.
    pub proof_grade_accepted: bool,
    /// Concrete fail-closed reason when `proof_grade_accepted` is false.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_grade_rejection_reason: Option<String>,
}

/// Report-facing timeout policy and backend attestation evidence for one solver dispatch.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinarySolverTimeoutEvidenceReport {
    /// Router/planner timeout budget for this VC dispatch, when one was recorded.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub planned_timeout_ms: Option<u64>,
    /// Timeout budget reported by the backend result, when the backend timed out.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub backend_reported_timeout_ms: Option<u64>,
    /// Stable timeout-evidence classification for release consumers.
    #[serde(default)]
    pub status: BinarySolverTimeoutEvidenceStatus,
    /// Concrete release blocker when timeout evidence is not release-grade.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub release_blocker: Option<String>,
}

impl Default for BinarySolverTimeoutEvidenceReport {
    fn default() -> Self {
        Self {
            planned_timeout_ms: None,
            backend_reported_timeout_ms: None,
            status: BinarySolverTimeoutEvidenceStatus::MissingTimeoutPolicy,
            release_blocker: None,
        }
    }
}

/// Stable timeout-evidence states consumed by binary release reports.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BinarySolverTimeoutEvidenceStatus {
    /// No per-VC timeout policy and no backend timeout attestation were recorded.
    #[default]
    MissingTimeoutPolicy,
    /// A backend reported a timeout but no planned per-VC timeout policy was recorded.
    BackendTimeoutWithoutPlannedPolicy,
    /// A per-VC timeout policy was recorded; no backend timeout attestation was required.
    PolicyRecorded,
    /// A per-VC timeout policy was recorded but the backend result did not attest it.
    MissingBackendAttestation,
    /// Planned and backend-reported timeout budgets agree exactly.
    Matched,
    /// Planned and backend-reported timeout budgets disagree.
    Mismatched,
}

/// Stable report-facing summary of one binary-derived VC formula.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryVcFormulaSummaryReport {
    /// Stable human-readable VC kind label.
    pub kind: String,
    /// Function carried by the serialized VC.
    pub function: String,
    /// Producer-provided VC source/binary span.
    pub location: SourceSpan,
    /// Canonical SMT-LIB2 formula text from `Formula::to_smtlib`.
    pub smtlib: String,
    /// Deterministic Rust debug representation for reviewers and golden tests.
    pub debug: String,
    /// Formula AST node count.
    pub node_count: usize,
    /// Sorted free variable names.
    pub free_variables: Vec<String>,
    /// Sorted free variable declarations with typed sort and SMT-LIB evidence.
    #[serde(default)]
    pub sort_declarations: Vec<BinaryVcFormulaSortDeclarationReport>,
    /// True when the formula uses bitvector operations or sorts.
    pub has_bitvectors: bool,
    /// True when the formula uses array operations or sorts.
    pub has_arrays: bool,
}

/// Report-facing typed sort declaration for one free variable in a VC formula.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryVcFormulaSortDeclarationReport {
    /// Free variable name as it appears in the formula and SMT-LIB text.
    pub name: String,
    /// Structured sort preserved from the typed formula AST.
    pub sort: Sort,
    /// SMT-LIB sort text for direct solver/reviewer consumption.
    pub smtlib_sort: String,
    /// SMT-LIB declaration corresponding to this variable and sort.
    pub smtlib_declaration: String,
}

/// Report-friendly aggregate certificate candidate/check summary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryCertificateCheckReport {
    /// Required binary VC count.
    pub required_vcs: usize,
    /// Number of solver dispatch records considered.
    pub solver_dispatches: usize,
    /// Dispatches with certificate-shaped evidence.
    pub certificate_candidates: usize,
    /// Dispatches with unchecked structural checked-certificate manifest candidates.
    #[serde(default)]
    pub structural_manifest_candidates: usize,
    /// Dispatches with independently checked certificate evidence.
    pub checked_certificates: usize,
    /// Required VCs still missing checked certificate coverage.
    pub missing_checked_certificates: usize,
    /// Dispatches with rejected certificate candidates.
    pub rejected_certificates: usize,
    /// Dispatches with raw solver proof bytes.
    pub raw_solver_proof_bytes: usize,
    /// Total raw solver proof bytes attached to raw solver results.
    #[serde(default)]
    pub raw_solver_proof_byte_count: usize,
    /// True when checked certificates cover every required VC.
    pub checked_certificates_satisfy_coverage: bool,
    /// Raw solver proof bytes never satisfy proof-grade certificate coverage.
    pub raw_solver_proof_bytes_satisfy_coverage: bool,
    /// Structural checked-certificate manifest validation alone never satisfies proof-grade coverage.
    #[serde(default)]
    pub structural_manifest_validation_satisfies_coverage: bool,
    /// Per-dispatch checked-certificate identity blockers that explain missing coverage.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub checked_certificate_identity_blockers: Vec<String>,
    /// Production-manifest status derived from per-VC checked-certificate evidence.
    #[serde(default)]
    pub production_manifest: BinaryCheckedCertificateProductionManifestReport,
}

/// Report-friendly status for checked-certificate production evidence coverage.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryCheckedCertificateProductionManifestReport {
    /// Required binary VC count.
    pub required_vcs: usize,
    /// Number of solver dispatch records considered.
    pub solver_dispatches: usize,
    /// Dispatches with independently checked certificate evidence.
    pub checked_certificates: usize,
    /// Checked dispatches carrying valid production-checker evidence.
    pub production_checked_certificates: usize,
    /// Required VCs still missing valid production-checker evidence.
    pub missing_production_evidence: usize,
    /// Checked dispatches with malformed production-checker evidence.
    pub malformed_production_evidence: usize,
    /// True only when every required VC has checked certificate and production evidence coverage.
    pub accepted: bool,
    /// Stable release blockers explaining why the production manifest is not accepted.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub release_blockers: Vec<String>,
}

/// Report-friendly proof-grade gate result.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryProofGradeGateReport {
    /// True when every proof-grade prerequisite is satisfied.
    pub accepted: bool,
    /// Trust level being evaluated for proof-grade release.
    pub final_trust_level: TrustLevel,
    /// True only when the unsupported ledger is empty.
    pub unsupported_ledger_empty: bool,
    /// True only when every required VC has exactly one proved dispatch result.
    pub all_required_vcs_proved: bool,
    /// True only when every required VC has checked proof-certificate evidence.
    pub checked_certificates_for_all_required_vcs: bool,
    /// True only when every required VC has checked proof-certificate production evidence.
    #[serde(default)]
    pub production_checked_certificates_for_all_required_vcs: bool,
    /// True only when replay records cover every required VC and all replayed.
    pub full_replay_coverage: bool,
    /// True when each required VC satisfies replay semantics: SAT witnesses must
    /// replay exactly, while proved UNSAT VCs may use checked certificate semantics.
    #[serde(default)]
    pub replay_semantics_satisfied: bool,
    /// True only when reconstructed output was validated against lifted binary semantics.
    pub reconstruction_validated: bool,
    /// True only when the selected target output exists, is validated, and has no
    /// target-validation blockers or preserved symbolic formulas left unconsumed.
    #[serde(default)]
    pub target_semantics_consumed: bool,
    /// Required binary VC count reported by the verifier.
    pub required_vcs: usize,
    /// Number of solver dispatch records available to the gate.
    pub solver_dispatches: usize,
    /// Number of required-VC dispatches proved by UNSAT under counterexample semantics.
    pub proved_vcs: usize,
    /// Number of proved dispatches with checked proof-certificate evidence.
    pub checked_certificates: usize,
    /// Number of proved dispatches with checked certificate production evidence.
    #[serde(default)]
    pub production_checked_certificates: usize,
    /// Number of dispatches with successful replay.
    pub replayed_vcs: usize,
    /// Number of proved UNSAT VCs satisfying replay semantics by checked certificate only.
    #[serde(default)]
    pub certificate_only_replay_semantics_vcs: usize,
    /// Number of VCs satisfying replay semantics by exact replay or checked UNSAT certificate.
    #[serde(default)]
    pub replay_semantics_satisfied_vcs: usize,
    /// Number of validated outputs for the selected target.
    #[serde(default)]
    pub validated_target_outputs: usize,
    /// Number of target-validation blockers still attached to the selected target output.
    #[serde(default)]
    pub target_validation_blockers: usize,
    /// Number of preserved `trust_symbolic.formula` payloads requiring target proof-consumer evidence.
    #[serde(default)]
    pub preserved_symbolic_formulas: usize,
    /// True only when no preserved symbolic formulas remain unconsumed by target proof semantics.
    #[serde(default)]
    pub symbolic_formulas_consumed_by_proof_model: bool,
    /// Number of unsupported records in the evaluated ledger.
    pub unsupported_records: usize,
    /// Unsupported records in the evaluated ledger grouped by stable family tag.
    #[serde(default)]
    pub unsupported_by_family: BTreeMap<String, usize>,
    /// Stable unsupported family rows for JSON consumers that prefer arrays over maps.
    #[serde(default)]
    pub unsupported_family_counts: Vec<UnsupportedFamilyCount>,
    /// Number of raw solver proof blobs seen in raw solver results.
    pub raw_solver_proof_bytes: usize,
    /// Total raw solver proof bytes attached to raw solver results.
    #[serde(default)]
    pub raw_solver_proof_byte_count: usize,
    /// Number of typed AArch64 atomic/exclusive semantic scaffold facts visible in the unsupported ledger.
    #[serde(default)]
    pub aarch64_atomic_semantic_fact_count: usize,
    /// True only when every visible AArch64 atomic/exclusive semantic fact has been consumed by a proof model.
    #[serde(default)]
    pub aarch64_atomic_semantic_facts_consumed_by_proof_model: bool,
    /// Conservative per-fact rejection diagnostics while semantics/replay/certificates have not consumed these facts.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub aarch64_atomic_semantic_fact_rejections: Vec<String>,
    /// Number of typed AArch64 barrier/monitor-clear boundary facts visible in the unsupported ledger.
    #[serde(default)]
    pub aarch64_sync_boundary_fact_count: usize,
    /// True only when every visible AArch64 sync-boundary fact has been consumed by a proof model.
    #[serde(default)]
    pub aarch64_sync_boundary_facts_consumed_by_proof_model: bool,
    /// Conservative per-boundary rejection diagnostics while proof semantics have not consumed these facts.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub aarch64_sync_boundary_fact_rejections: Vec<String>,
    /// Release-gate blocker groups split by evidence family for reviewers and JSON consumers.
    #[serde(default)]
    pub blocker_groups: BinaryProofGradeBlockerGroupsReport,
    /// Concrete proof-grade gate rejection reasons.
    pub rejections: Vec<BinaryProofGradeGateRejectionReport>,
}

/// Proof-grade release blockers grouped by the evidence family that must be fixed.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryProofGradeBlockerGroupsReport {
    /// Final trust-level blockers.
    #[serde(default)]
    pub trust_level: Vec<BinaryProofGradeGateRejectionReport>,
    /// Unsupported-ledger blockers.
    #[serde(default)]
    pub unsupported_ledger: Vec<BinaryProofGradeGateRejectionReport>,
    /// Required VC accounting and proof-result blockers.
    #[serde(default)]
    pub verification: Vec<BinaryProofGradeGateRejectionReport>,
    /// Checked certificate coverage blockers.
    #[serde(default)]
    pub certificate: Vec<BinaryProofGradeGateRejectionReport>,
    /// Replay coverage and replay-success blockers.
    #[serde(default)]
    pub replay: Vec<BinaryProofGradeGateRejectionReport>,
    /// Reconstruction compile-back/validation blockers.
    #[serde(default)]
    pub reconstruction: Vec<BinaryProofGradeGateRejectionReport>,
    /// Exact source provenance/source-backpropagation blockers.
    #[serde(default)]
    pub source_provenance: Vec<BinaryProofGradeGateRejectionReport>,
    /// Raw solver proof blobs that are not checked certificates.
    #[serde(default)]
    pub raw_solver_proofs: Vec<BinaryProofGradeGateRejectionReport>,
}

/// Report-friendly proof-grade gate result for a full decompilation artifact.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryDecompilationProofGradeGateReport {
    /// True when the artifact gate and every function gate accepted.
    pub accepted: bool,
    /// Artifact-level proof-grade gate result.
    pub artifact: BinaryProofGradeGateReport,
    /// Per-function proof-grade gate results.
    pub functions: Vec<BinaryFunctionProofGradeGateReport>,
}

/// Report-friendly proof-grade gate result for one recovered function.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryFunctionProofGradeGateReport {
    /// Recovered function name.
    pub name: String,
    /// Function entry address.
    pub entry: u64,
    /// Display form of `entry`, e.g. `0x401000`.
    pub entry_display: String,
    /// Function-level proof-grade gate result.
    pub gate: BinaryProofGradeGateReport,
}

/// Report-friendly reason a binary artifact is not proof-grade.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BinaryProofGradeGateRejectionReport {
    /// The report did not claim proof-grade trust.
    FinalTrustLevelNotProofGrade { found: TrustLevel },
    /// Unsupported binary constructs remain.
    UnsupportedRecordsPresent { count: usize },
    /// Required VC accounting does not cover every expected binary VC exactly once.
    RequiredVcCoverageIncomplete { vc_count: usize, solver_dispatches: usize },
    /// Some expected VCs are missing proved solver results or have non-proved outcomes.
    NonProvedVerificationConditions {
        vc_count: usize,
        total_results: usize,
        proved: usize,
        unproved_vcs: usize,
        non_proved_results: usize,
    },
    /// Some expected VCs are missing checked proof-certificate evidence.
    MissingCheckedProofCertificates {
        vc_count: usize,
        checked_certificates: usize,
        missing_certificates: usize,
    },
    /// Checked-certificate production evidence does not cover every required VC.
    CheckedCertificateProductionManifestIncomplete {
        vc_count: usize,
        production_checked_certificates: usize,
        missing_production_evidence: usize,
        malformed_production_evidence: usize,
    },
    /// No replay status was recorded, so replay is unknown.
    ReplayStatusMissing,
    /// Replay records do not cover every required VC.
    ReplayCoverageIncomplete { vc_count: usize, replay_records: usize, replayed: usize },
    /// At least one replay status is unknown/not attempted.
    ReplayStatusUnknown { not_attempted: usize },
    /// At least one replay was attempted but did not replay successfully.
    ReplayNotSuccessful { failed: usize, spurious: usize },
    /// Replayed dispatches are missing exact root/selected-image digest identity.
    ReplayArtifactDigestIdentityNotExact {
        replayed_vcs: usize,
        ready_replayed_vcs: usize,
        blocked_replayed_vcs: usize,
    },
    /// Replay reached syscall/exception/trap boundaries without exact semantics witnesses.
    ReplayBoundarySemanticsUnsupported { boundary_count: usize, unsupported_boundary_count: usize },
    /// Reconstructed output was not semantically validated against the lifted binary.
    ReconstructionValidationNotValidated { status: ReconstructionValidationStatus },
    /// The selected target output did not prove target-owned semantic consumption of evidence.
    TargetSemanticsNotConsumed {
        target: DecompileTarget,
        validated_outputs: usize,
        target_validation_blockers: usize,
    },
    /// Target-validation blockers remain on the selected target output.
    TargetValidationBlockersPresent { target: DecompileTarget, count: usize },
    /// Preserved `trust_symbolic.formula` payloads remain without an explicit proof consumer.
    SymbolicFormulasNotConsumed { target: DecompileTarget, count: usize },
    /// Exact source provenance is unavailable, so source backpropagation cannot be proof-grade.
    SourceProvenanceNotExact { status: String, exact_mapping_count: usize },
    /// Exact digest-level artifact identity is unavailable or inconsistent.
    DigestIdentityNotExact { blockers: Vec<String> },
    /// Raw solver proof blobs were present; only checked certificate status is proof-grade.
    RawSolverProofBytesPresent { count: usize },
    /// AArch64 atomic/exclusive semantic scaffold facts are present but not yet proof-consumed.
    Aarch64AtomicSemanticFactsNotConsumed {
        count: usize,
        unconsumed: usize,
        missing_witnesses: Vec<String>,
    },
    /// AArch64 barrier/monitor-clear boundary facts are present but not yet proof-consumed.
    Aarch64SyncBoundaryFactsNotConsumed {
        count: usize,
        unconsumed: usize,
        missing_witnesses: Vec<String>,
    },
}

/// Report-friendly unsupported ledger summary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryUnsupportedLedgerReport {
    /// Number of unsupported records in the ledger.
    pub total_records: usize,
    /// Unsupported records grouped by producing stage.
    pub by_stage: BTreeMap<String, usize>,
    /// Unsupported records grouped by feature.
    pub by_feature: BTreeMap<String, usize>,
    /// Unsupported records grouped by stable audit family.
    #[serde(default)]
    pub by_family: BTreeMap<String, usize>,
    /// Stable unsupported family rows for JSON consumers that prefer arrays over maps.
    #[serde(default)]
    pub family_counts: Vec<UnsupportedFamilyCount>,
    /// Typed AArch64 atomic/exclusive semantic facts derived from fail-closed unsupported records.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub aarch64_atomic_semantic_facts: Vec<BinaryAarch64AtomicSemanticFactReport>,
    /// Number of typed AArch64 atomic/exclusive semantic facts surfaced in this ledger.
    #[serde(default)]
    pub aarch64_atomic_semantic_fact_count: usize,
    /// Typed AArch64 barrier/monitor-clear boundary facts derived from fail-closed unsupported records.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub aarch64_sync_boundary_facts: Vec<BinaryAarch64SyncBoundaryFactReport>,
    /// Number of typed AArch64 barrier/monitor-clear boundary facts surfaced in this ledger.
    #[serde(default)]
    pub aarch64_sync_boundary_fact_count: usize,
    /// Binary locations from unsupported records that carry origin metadata.
    pub locations: Vec<BinaryLocationReport>,
}

/// Report-friendly AArch64 atomic/exclusive semantic scaffold fact.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryAarch64AtomicSemanticFactReport {
    /// Binary instruction origin for the fact, when known.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub location: Option<BinaryLocationReport>,
    /// Original opcode associated with the semantic fact.
    pub opcode: String,
    /// Operand text from the unsupported record, when available.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub operand: Option<String>,
    /// Read/write direction implied by the atomic instruction.
    pub access: MemoryAccessKind,
    /// Memory ordering semantics carried by this instruction.
    pub ordering: MemoryOrderingSemantics,
    /// Exclusive monitor action carried by this instruction.
    pub exclusive_monitor: Aarch64ExclusiveMonitorSemantics,
    /// True when the instruction reports a store-conditional status result.
    pub reports_status: bool,
    /// Witnesses that semantics/replay/certificates must account for before proof-grade release.
    pub missing_witnesses: Vec<String>,
    /// Whether a downstream proof model has consumed this scaffold fact.
    pub consumed_by_proof_model: bool,
    /// True only after a downstream proof model consumed this fact and every witness.
    pub proof_grade_accepted: bool,
    /// Conservative release-gate diagnostic while this fact is unconsumed.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_grade_rejection_reason: Option<String>,
}

/// Report-friendly AArch64 barrier/monitor-clear boundary scaffold fact.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryAarch64SyncBoundaryFactReport {
    /// Binary instruction origin for the fact, when known.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub location: Option<BinaryLocationReport>,
    /// Original opcode associated with the boundary fact.
    pub opcode: String,
    /// Operand text from the unsupported record, when available.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub operand: Option<String>,
    /// AArch64 synchronization-boundary instruction class.
    pub kind: Aarch64SyncBoundaryKind,
    /// Shareability/locality scope carried by the boundary.
    pub scope: Aarch64SyncScope,
    /// Ordered access class carried by the boundary.
    pub ordering: Aarch64SyncOrdering,
    /// True when the boundary clears exclusive-monitor state.
    pub clears_exclusive_monitor: bool,
    /// Encoded AArch64 barrier option when known.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub raw_option: Option<u8>,
    /// Witnesses that semantics/replay/certificates must account for before proof-grade release.
    pub missing_witnesses: Vec<String>,
    /// Whether a downstream proof model has consumed this scaffold fact.
    pub consumed_by_proof_model: bool,
    /// True only after a downstream proof model consumed this fact and every witness.
    pub proof_grade_accepted: bool,
    /// Conservative release-gate diagnostic while this fact is unconsumed.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_grade_rejection_reason: Option<String>,
}

/// Report-friendly binary source provenance summary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinarySourceProvenanceReport {
    /// Stable lowercase provenance status reported by the lifter.
    #[serde(default = "default_binary_source_provenance_report_status")]
    pub status: String,
    /// Number of exact address-to-source mappings accepted by the lifter.
    #[serde(default)]
    pub exact_mapping_count: usize,
    /// Number of ambiguous mappings withheld by the lifter.
    #[serde(default)]
    pub ambiguous_mapping_count: usize,
    /// Human-readable diagnostics from provenance recovery.
    #[serde(default)]
    pub diagnostics: Vec<String>,
    /// True only when exact recovered source provenance may be used for source backpropagation.
    #[serde(default)]
    pub source_backpropagation_allowed: bool,
    /// Stable fail-closed reasons explaining why source backpropagation is disabled.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub source_backpropagation_disabled_reasons: Vec<String>,
}

/// Runtime-compatible checked binary source-provenance handoff artifact.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BinarySourceProvenanceArtifactReport {
    /// Stable artifact kind for handoff consumers.
    pub kind: String,
    /// Schema version for this content-addressed source-provenance artifact.
    pub schema_version: String,
    /// Exact source provenance summary copied from the decompilation artifact.
    pub source_provenance: BinarySourceProvenanceSummary,
    /// Digest over the source-provenance handoff records and source gate identity.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source_provenance_artifact_digest: Option<String>,
    /// Artifact-level verification evidence consumed by runtime rewrite gating.
    pub verification: BinaryVerificationSummary,
    /// Reconstruction/target-validation evidence consumed by runtime rewrite gating.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reconstruction: Option<ReconstructionSummary>,
    /// Checked-certificate source-backpropagation gate details.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source_backpropagation_gate: Option<BinarySourceBackpropagationGateDetailsReport>,
    /// Source-backpropagation gate identity digest carried by checked certificate readback.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source_backpropagation_gate_sha256: Option<String>,
    /// Canonical checked provenance rows consumable by `targo trust --rewrite`.
    #[serde(default)]
    pub canonical_binary_provenance: BinarySourceProvenanceRecordsReport,
    /// Fail-closed blockers explaining why no checked exact handoff rows were emitted.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub blockers: Vec<String>,
}

/// Runtime-compatible checked binary source-provenance record set.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinarySourceProvenanceRecordsReport {
    /// Checked exact binary-origin to source mapping rows.
    #[serde(default)]
    pub records: Vec<BinarySourceProvenanceRecordReport>,
}

/// One checked exact binary-origin to source mapping row.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinarySourceProvenanceRecordReport {
    /// Canonical binary instruction origin, including source span.
    pub origin: BinaryOrigin,
    /// Root and selected-image digest identity for the binary bytes.
    pub artifact_digest_identity: BinaryArtifactDigestIdentity,
    /// Source mapping status for the row.
    pub source_status: String,
    /// Checked provenance row status.
    pub provenance_status: String,
    /// Stable row digest over origin, binary digest identity, source status, and proof evidence.
    pub record_digest: String,
    /// Proof evidence identifiers that bind this row to a checked solver dispatch.
    pub proof_evidence: BinarySourceProvenanceProofEvidenceReport,
}

/// Proof evidence identifiers required by runtime source-provenance import.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinarySourceProvenanceProofEvidenceReport {
    /// Solver dispatch id that owns this binary/source row.
    pub solver_dispatch_id: String,
    /// Checked certificate artifact digest for the dispatch.
    pub checked_certificate_sha256: String,
    /// Production checker evidence digest carried by the checked certificate.
    pub production_checker_evidence_sha256: String,
    /// Checked-certificate source-backpropagation gate identity digest.
    pub source_backpropagation_gate_sha256: String,
    /// Exact replay transcript digest for the dispatch.
    pub replay_transcript_digest: String,
}

/// JSON-compatible subset of checked-certificate source-backpropagation gate details.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinarySourceBackpropagationGateDetailsReport {
    /// Source-backpropagation gate schema version.
    pub schema_version: String,
    /// Whether replay-grade artifact identity was accepted.
    pub replay_grade_artifact_identity: bool,
    /// Whether checked certificate identity was accepted.
    pub checked_certificate_identity: bool,
    /// Whether exact replay identity was accepted.
    pub exact_replay_identity: bool,
    /// Whether reconstruction validation was accepted.
    pub accepted_reconstruction_validation: bool,
    /// Whether target validation was accepted.
    pub accepted_target_validation: bool,
    /// Whether exact source provenance was accepted.
    pub exact_source_provenance: bool,
    /// Source provenance summary carried by the gate.
    pub source_provenance: BinarySourceProvenanceSummary,
    /// Producer decision for source backpropagation.
    pub source_backpropagation_allowed: bool,
    /// Producer blockers when source backpropagation was rejected.
    pub blockers: Vec<String>,
    /// Identity digest for the full checked-certificate source gate, when available.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source_backpropagation_gate_sha256: Option<String>,
}

/// Report-friendly source-backpropagation release gate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinarySourceBackpropagationGateReport {
    /// True only when every evidence class required for proof-grade source backpropagation is exact.
    pub accepted: bool,
    /// Stable gate status for JSON consumers.
    pub status: String,
    /// Required source-backpropagation evidence labels, in stable order.
    #[serde(default)]
    pub required_labels: Vec<String>,
    /// Missing/rejected evidence labels, in stable order.
    #[serde(default)]
    pub missing_labels: Vec<String>,
    /// Structured fail-closed blockers.
    #[serde(default)]
    pub blockers: Vec<BinarySourceBackpropagationGateBlockerReport>,
}

/// Structured source-backpropagation gate blocker.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinarySourceBackpropagationGateBlockerReport {
    /// Exact evidence label, e.g. `checked_certificate_identity`.
    pub label: String,
    /// Producing report stage.
    pub stage: String,
    /// Human-readable diagnostic.
    pub detail: String,
}

/// Report-friendly reconstruction summary for binary target outputs.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryReconstructionReport {
    /// Requested reconstruction target.
    #[serde(default)]
    pub target: DecompileTarget,
    /// Cross-output validation status.
    #[serde(default)]
    pub validation: ReconstructionValidationStatus,
    /// Reconstruction trust level copied from the shared artifact.
    #[serde(default)]
    pub trust_level: TrustLevel,
    /// Summary-level reconstruction diagnostics.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<String>,
    /// Per-output diagnostics kept with target/status identity.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub output_diagnostics: Vec<BinaryReconstructionOutputDiagnosticsReport>,
    /// Structured validation/refinement records copied from target outputs.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub validation_records: Vec<ReconstructionValidationRecord>,
    /// Number of target outputs summarized.
    #[serde(default)]
    pub output_count: usize,
    /// Structured blockers that keep target output from proof-grade use.
    #[serde(default)]
    pub target_validation_blockers: Vec<BinaryTargetValidationBlockerReport>,
    /// Total target-validation blocker count.
    #[serde(default)]
    pub target_validation_blocker_count: usize,
    /// Target-validation blockers grouped by producing stage.
    #[serde(default)]
    pub target_validation_blockers_by_stage: BTreeMap<String, usize>,
    /// Target-validation blockers grouped by feature.
    #[serde(default)]
    pub target_validation_blockers_by_feature: BTreeMap<String, usize>,
    /// Structured symbolic formulas preserved for schema-aware consumers.
    #[serde(default)]
    pub preserved_symbolic_formulas: Vec<BinaryPreservedSymbolicFormulaReport>,
    /// Total preserved symbolic formula count.
    #[serde(default)]
    pub preserved_symbolic_formula_count: usize,
    /// Aggregate target proof-consumer status for preserved symbolic formulas.
    #[serde(default)]
    pub symbolic_formula_consumer_status: String,
    /// Residual target proof-consumer blockers for preserved symbolic formulas.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub symbolic_formula_consumer_blockers: Vec<String>,
}

impl Default for BinaryReconstructionReport {
    fn default() -> Self {
        Self {
            target: DecompileTarget::TrustIr,
            validation: ReconstructionValidationStatus::NotAttempted,
            trust_level: TrustLevel::Exploratory,
            diagnostics: vec![],
            output_diagnostics: vec![],
            validation_records: vec![],
            output_count: 0,
            target_validation_blockers: vec![],
            target_validation_blocker_count: 0,
            target_validation_blockers_by_stage: BTreeMap::new(),
            target_validation_blockers_by_feature: BTreeMap::new(),
            preserved_symbolic_formulas: vec![],
            preserved_symbolic_formula_count: 0,
            symbolic_formula_consumer_status: "not_required".to_string(),
            symbolic_formula_consumer_blockers: vec![],
        }
    }
}

/// Report-friendly per-output reconstruction diagnostics.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryReconstructionOutputDiagnosticsReport {
    /// Target output that produced these diagnostics.
    #[serde(default)]
    pub target: DecompileTarget,
    /// Artifact path for this output, when present.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub artifact_path: Option<String>,
    /// Output validation status.
    #[serde(default)]
    pub validation: ReconstructionValidationStatus,
    /// Output trust level.
    #[serde(default)]
    pub trust_level: TrustLevel,
    /// Raw producer diagnostics.
    #[serde(default)]
    pub diagnostics: Vec<String>,
}

/// Report-friendly target-output blocker.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryTargetValidationBlockerReport {
    /// Target output blocked from proof-grade validation.
    #[serde(default)]
    pub target: DecompileTarget,
    /// Function associated with the blocker, when known.
    #[serde(default)]
    pub function: Option<String>,
    /// Stable machine-readable identity assigned by the blocker producer.
    #[serde(default)]
    pub code: String,
    /// Producing stage, e.g. `lift`, `replay`, `canonical_trust_ir`.
    #[serde(default)]
    pub stage: String,
    /// Stable blocker feature.
    #[serde(default)]
    pub feature: String,
    /// Human-readable blocker reason.
    #[serde(default)]
    pub reason: String,
    /// Binary instruction origin for the blocker, when known.
    #[serde(default)]
    pub location: Option<BinaryLocationReport>,
    /// Additional diagnostics from the producer.
    #[serde(default)]
    pub diagnostics: Vec<String>,
}

/// Report-friendly preserved symbolic formula.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryPreservedSymbolicFormulaReport {
    /// Target output that preserved the formula.
    #[serde(default)]
    pub target: DecompileTarget,
    /// Function associated with the formula, when known.
    #[serde(default)]
    pub function: Option<String>,
    /// TrustIr block index, when known.
    #[serde(default)]
    pub block: Option<usize>,
    /// Statement index inside the block, when known.
    #[serde(default)]
    pub statement_index: Option<usize>,
    /// Producer-provided formula location.
    #[serde(default)]
    pub location: String,
    /// Stable evidence identity target consumers must bind before acceptance.
    #[serde(default)]
    pub formula_evidence: PreservedSymbolicFormulaEvidence,
    /// Structured formula payload; consumers must check or reject it explicitly.
    pub formula: Formula,
    /// Formula schema version that proof consumers must explicitly consume.
    #[serde(default)]
    pub formula_schema: String,
    /// Stable SHA-256 digest of the typed formula payload.
    #[serde(default)]
    pub formula_digest: String,
    /// Stable formula origin used to bind target/reconstruction evidence.
    #[serde(default)]
    pub formula_origin: String,
    /// Canonical SMT-LIB2 formula text.
    #[serde(default)]
    pub smtlib: String,
    /// Strict top-level formula sort, when the typed AST has enough metadata.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub formula_sort: Option<Sort>,
    /// SMT-LIB sort text for the top-level formula.
    #[serde(default)]
    pub smtlib_sort: String,
    /// Deterministic Rust debug representation required from schema-aware consumers.
    #[serde(default)]
    pub debug: String,
    /// Sorted free variable declarations with typed sort and SMT-LIB evidence.
    #[serde(default)]
    pub sort_declarations: Vec<BinaryVcFormulaSortDeclarationReport>,
    /// Concrete proof-consumer evidence items required for this formula.
    #[serde(default)]
    pub proof_consumer_obligations: Vec<String>,
    /// True because preserved symbolic formulas must be consumed by target proof semantics.
    #[serde(default = "default_true")]
    pub proof_consumer_required: bool,
    /// Stable per-formula target proof-consumer status.
    #[serde(default)]
    pub proof_consumer_status: String,
    /// Residual proof-consumer blockers for this formula.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub proof_consumer_blockers: Vec<String>,
}

fn default_binary_source_provenance_report_status() -> String {
    "unavailable".to_string()
}

fn default_production_checker_evidence_status() -> ProofCertificateProductionCheckerEvidenceStatus {
    ProofCertificateProductionCheckerEvidenceStatus::Missing
}

fn default_true() -> bool {
    true
}

impl Default for BinarySourceProvenanceReport {
    fn default() -> Self {
        Self {
            status: default_binary_source_provenance_report_status(),
            exact_mapping_count: 0,
            ambiguous_mapping_count: 0,
            diagnostics: vec![],
            source_backpropagation_allowed: false,
            source_backpropagation_disabled_reasons: vec![
                "exact_source_provenance_not_available".to_string(),
                "source_backpropagation_not_enabled_by_producer".to_string(),
            ],
        }
    }
}

impl Default for BinarySourceBackpropagationGateReport {
    fn default() -> Self {
        Self {
            accepted: false,
            status: "rejected".to_string(),
            required_labels: source_backpropagation_required_labels(),
            missing_labels: source_backpropagation_required_labels(),
            blockers: source_backpropagation_missing_evidence_blockers(),
        }
    }
}

const SOURCE_BACKPROPAGATION_GATE_STAGE: &str = "source_backpropagation_gate";
const SOURCE_BACKPROPAGATION_MISSING_RECONSTRUCTION: &str = "missing_reconstruction";
const SOURCE_BACKPROPAGATION_EXACT_SOURCE_PROVENANCE: &str = "exact_source_provenance";
const SOURCE_BACKPROPAGATION_TYPE_OWNERSHIP: &str = "type_ownership";
const SOURCE_BACKPROPAGATION_TARGET_VALIDATION: &str = "target_validation";
const SOURCE_BACKPROPAGATION_CHECKED_CERTIFICATE_IDENTITY: &str = "checked_certificate_identity";
const SOURCE_BACKPROPAGATION_REPLAY_IDENTITY: &str = "replay_identity";

fn source_backpropagation_required_labels() -> Vec<String> {
    [
        SOURCE_BACKPROPAGATION_MISSING_RECONSTRUCTION,
        SOURCE_BACKPROPAGATION_EXACT_SOURCE_PROVENANCE,
        SOURCE_BACKPROPAGATION_TYPE_OWNERSHIP,
        SOURCE_BACKPROPAGATION_TARGET_VALIDATION,
        SOURCE_BACKPROPAGATION_CHECKED_CERTIFICATE_IDENTITY,
        SOURCE_BACKPROPAGATION_REPLAY_IDENTITY,
    ]
    .into_iter()
    .map(str::to_string)
    .collect()
}

fn source_backpropagation_missing_evidence_blockers()
-> Vec<BinarySourceBackpropagationGateBlockerReport> {
    source_backpropagation_required_labels()
        .into_iter()
        .map(|label| {
            source_backpropagation_gate_blocker(
                label.as_str(),
                format!("source backpropagation evidence `{label}` is missing"),
            )
        })
        .collect()
}

impl BinarySourceBackpropagationGateDetailsReport {
    fn from_gate(
        source_provenance: &BinarySourceProvenanceSummary,
        gate: &BinarySourceBackpropagationGateReport,
        source_backpropagation_gate_sha256: Option<String>,
    ) -> Self {
        let missing = |label: &str| gate.missing_labels.iter().any(|missing| missing == label);
        Self {
            schema_version: "trust-proof-cert.source-backpropagation-gate.v1".to_string(),
            replay_grade_artifact_identity: !missing(SOURCE_BACKPROPAGATION_REPLAY_IDENTITY),
            checked_certificate_identity: !missing(
                SOURCE_BACKPROPAGATION_CHECKED_CERTIFICATE_IDENTITY,
            ),
            exact_replay_identity: !missing(SOURCE_BACKPROPAGATION_REPLAY_IDENTITY),
            accepted_reconstruction_validation: !missing(
                SOURCE_BACKPROPAGATION_MISSING_RECONSTRUCTION,
            ),
            accepted_target_validation: !missing(SOURCE_BACKPROPAGATION_TARGET_VALIDATION),
            exact_source_provenance: !missing(SOURCE_BACKPROPAGATION_EXACT_SOURCE_PROVENANCE),
            source_provenance: source_provenance.clone(),
            source_backpropagation_allowed: gate.accepted,
            blockers: gate
                .blockers
                .iter()
                .map(|blocker| format!("{}: {}", blocker.label, blocker.detail))
                .collect(),
            source_backpropagation_gate_sha256,
        }
    }
}

fn build_checked_source_provenance_records(
    artifact: &DecompilationArtifact,
    source_backpropagation_gate_sha256: Option<&str>,
) -> (Vec<BinarySourceProvenanceRecordReport>, Vec<String>) {
    let mut records = Vec::new();
    let mut blockers = Vec::new();

    if !artifact.source_provenance.effective_source_backpropagation_allowed() {
        blockers.push(format!(
            "source provenance is not accepted exact provenance: status={}, exact_mapping_count={}, ambiguous_mapping_count={}, source_backpropagation_allowed={}",
            artifact.source_provenance.status,
            artifact.source_provenance.exact_mapping_count,
            artifact.source_provenance.ambiguous_mapping_count,
            artifact.source_provenance.source_backpropagation_allowed
        ));
    }

    for dispatch in &artifact.verification.solver_dispatch {
        match build_checked_source_provenance_record(dispatch, source_backpropagation_gate_sha256) {
            Ok(record) => records.push(record),
            Err(dispatch_blockers) => blockers.extend(dispatch_blockers),
        }
    }

    if artifact.source_provenance.exact_mapping_count != records.len() {
        blockers.push(format!(
            "source provenance exact_mapping_count={} does not match {} checked exact handoff record(s)",
            artifact.source_provenance.exact_mapping_count,
            records.len()
        ));
    }

    (records, blockers)
}

fn build_checked_source_provenance_record(
    dispatch: &SolverDispatchRecord,
    source_backpropagation_gate_sha256: Option<&str>,
) -> Result<BinarySourceProvenanceRecordReport, Vec<String>> {
    let label =
        if dispatch.id.trim().is_empty() { "<missing-dispatch-id>" } else { dispatch.id.as_str() };
    let mut blockers = Vec::new();

    if !dispatch.canonical_replay_allows_proof_grade() {
        blockers.extend(
            dispatch
                .canonical_replay_blockers()
                .into_iter()
                .map(|blocker| format!("{label}: {blocker}")),
        );
    }

    let Some(origin) = dispatch.origin.clone() else {
        blockers.push(format!("{label}: missing binary origin"));
        return Err(blockers);
    };
    if origin.source.is_none() {
        blockers.push(format!("{label}: missing exact source mapping"));
    } else if origin.span().is_binary() {
        blockers.push(format!("{label}: source mapping is binary-address-only"));
    }

    let Some(artifact_digest_identity) = dispatch.binary_artifact_digest_identity.clone() else {
        blockers.push(format!("{label}: missing binary artifact digest identity"));
        return Err(blockers);
    };
    blockers.extend(
        artifact_digest_identity
            .digest_identity_blockers()
            .into_iter()
            .map(|blocker| format!("{label}: binary artifact digest identity: {blocker}")),
    );

    let proof_evidence = match source_provenance_proof_evidence_for_dispatch(
        dispatch,
        source_backpropagation_gate_sha256,
    ) {
        Ok(proof_evidence) => proof_evidence,
        Err(proof_blockers) => {
            blockers
                .extend(proof_blockers.into_iter().map(|blocker| format!("{label}: {blocker}")));
            return Err(blockers);
        }
    };

    if !blockers.is_empty() {
        return Err(blockers);
    }

    let source_status = "exact".to_string();
    let provenance_status = "checked_exact".to_string();
    let record_digest = match source_provenance_record_digest(
        &origin,
        &artifact_digest_identity,
        &source_status,
        &provenance_status,
        &proof_evidence,
    ) {
        Ok(digest) => digest,
        Err(error) => {
            blockers.push(format!(
                "{label}: could not serialize canonical source-provenance digest material: {error}"
            ));
            return Err(blockers);
        }
    };

    Ok(BinarySourceProvenanceRecordReport {
        origin,
        artifact_digest_identity,
        source_status,
        provenance_status,
        record_digest,
        proof_evidence,
    })
}

fn source_provenance_proof_evidence_for_dispatch(
    dispatch: &SolverDispatchRecord,
    source_backpropagation_gate_sha256: Option<&str>,
) -> Result<BinarySourceProvenanceProofEvidenceReport, Vec<String>> {
    let mut blockers = Vec::new();
    if dispatch.id.trim().is_empty() {
        blockers.push("missing solver dispatch proof evidence id".to_string());
    }

    let checked_certificate_sha256 =
        checked_certificate_sha256(&dispatch.certificate).unwrap_or_default();
    if checked_certificate_sha256.is_empty() {
        blockers.push("missing checked certificate proof evidence id".to_string());
    }

    let production_checker_evidence_sha256 =
        production_checker_evidence_sha256(&dispatch.certificate).unwrap_or_default();
    if production_checker_evidence_sha256.is_empty() {
        blockers.push("missing production checker proof evidence id".to_string());
    }

    let source_backpropagation_gate_sha256 = source_backpropagation_gate_sha256
        .map(str::to_string)
        .or_else(|| extract_source_backpropagation_gate_sha256(&dispatch.diagnostics))
        .unwrap_or_default();
    if source_backpropagation_gate_sha256.is_empty() {
        blockers.push(
            "missing checked certificate source-backpropagation gate proof evidence id".to_string(),
        );
    }

    let replay_transcript_digest =
        extract_replay_transcript_digest(&dispatch.diagnostics).unwrap_or_default();
    if replay_transcript_digest.is_empty() {
        blockers.push("missing exact replay transcript proof evidence id".to_string());
    }

    for (name, digest) in [
        ("checked certificate proof evidence id", checked_certificate_sha256.as_str()),
        ("production checker proof evidence id", production_checker_evidence_sha256.as_str()),
        (
            "checked certificate source-backpropagation gate proof evidence id",
            source_backpropagation_gate_sha256.as_str(),
        ),
        ("exact replay transcript proof evidence id", replay_transcript_digest.as_str()),
    ] {
        if !digest.is_empty() && !is_canonical_sha256_hex(digest) {
            blockers.push(format!("{name} is not canonical SHA-256 hex"));
        }
    }

    if blockers.is_empty() {
        Ok(BinarySourceProvenanceProofEvidenceReport {
            solver_dispatch_id: dispatch.id.clone(),
            checked_certificate_sha256,
            production_checker_evidence_sha256,
            source_backpropagation_gate_sha256,
            replay_transcript_digest,
        })
    } else {
        Err(blockers)
    }
}

fn checked_certificate_sha256(certificate: &ProofCertificateStatus) -> Option<String> {
    match certificate {
        ProofCertificateStatus::Checked { sha256: Some(sha256), .. }
            if is_canonical_sha256_hex(sha256) =>
        {
            Some(sha256.clone())
        }
        _ => None,
    }
}

fn production_checker_evidence_sha256(certificate: &ProofCertificateStatus) -> Option<String> {
    certificate
        .production_checker_evidence()
        .map(|evidence| evidence.production_checker_evidence_sha256)
        .filter(|digest| is_canonical_sha256_hex(digest))
}

fn common_source_backpropagation_gate_sha256(
    dispatches: &[SolverDispatchRecord],
) -> Option<String> {
    let mut digest = None;
    for candidate in dispatches
        .iter()
        .filter_map(|dispatch| extract_source_backpropagation_gate_sha256(&dispatch.diagnostics))
    {
        match &digest {
            Some(existing) if existing != &candidate => return None,
            Some(_) => {}
            None => digest = Some(candidate),
        }
    }
    digest
}

fn extract_source_backpropagation_gate_sha256(diagnostics: &[String]) -> Option<String> {
    extract_sha256_marker(
        diagnostics,
        &[
            "source_backpropagation_gate_sha256",
            "source-backpropagation-gate-sha256",
            "source_backpropagation_gate.sha256",
        ],
    )
}

fn extract_replay_transcript_digest(diagnostics: &[String]) -> Option<String> {
    extract_sha256_marker(
        diagnostics,
        &[
            "replay_transcript_digest",
            "replay_transcript_sha256",
            "exact_replay_transcript_artifact_digest",
        ],
    )
}

fn extract_sha256_marker(diagnostics: &[String], markers: &[&str]) -> Option<String> {
    diagnostics.iter().find_map(|diagnostic| {
        markers.iter().find_map(|marker| {
            diagnostic
                .find(marker)
                .and_then(|index| first_canonical_sha256_hex(&diagnostic[index + marker.len()..]))
        })
    })
}

fn first_canonical_sha256_hex(text: &str) -> Option<String> {
    text.split(|ch: char| !ch.is_ascii_hexdigit())
        .find(|part| is_canonical_sha256_hex(part))
        .map(ToString::to_string)
}

#[derive(Serialize)]
struct BinarySourceProvenanceRecordDigestMaterial<'a> {
    origin: &'a BinaryOrigin,
    artifact_digest_identity: &'a BinaryArtifactDigestIdentity,
    source_status: &'a str,
    provenance_status: &'a str,
    proof_evidence: &'a BinarySourceProvenanceProofEvidenceReport,
}

fn source_provenance_record_digest(
    origin: &BinaryOrigin,
    artifact_digest_identity: &BinaryArtifactDigestIdentity,
    source_status: &str,
    provenance_status: &str,
    proof_evidence: &BinarySourceProvenanceProofEvidenceReport,
) -> Result<String, serde_json::Error> {
    stable_json_sha256(&BinarySourceProvenanceRecordDigestMaterial {
        origin,
        artifact_digest_identity,
        source_status,
        provenance_status,
        proof_evidence,
    })
}

#[derive(Serialize)]
struct BinarySourceProvenanceArtifactDigestMaterial<'a> {
    kind: &'a str,
    schema_version: &'a str,
    source_provenance: &'a BinarySourceProvenanceSummary,
    source_backpropagation_gate_sha256: &'a Option<String>,
    records: &'a [BinarySourceProvenanceRecordReport],
}

fn source_provenance_artifact_digest(
    report: &BinarySourceProvenanceArtifactReport,
) -> Result<String, serde_json::Error> {
    stable_json_sha256(&BinarySourceProvenanceArtifactDigestMaterial {
        kind: &report.kind,
        schema_version: &report.schema_version,
        source_provenance: &report.source_provenance,
        source_backpropagation_gate_sha256: &report.source_backpropagation_gate_sha256,
        records: &report.canonical_binary_provenance.records,
    })
}

fn stable_json_sha256<T: Serialize>(value: &T) -> Result<String, serde_json::Error> {
    serde_json::to_vec(value).map(|bytes| stable_sha256_hex(&bytes))
}

impl BinarySourceProvenanceArtifactReport {
    /// Fail-closed checks for accepting this JSON as a typed view over canonical artifacts.
    ///
    /// This does not trust JSON booleans on their own. It rechecks schema ids,
    /// content-addressed digests, exact source provenance, and every per-row
    /// proof evidence digest before a reviewer/importer treats the handoff as
    /// accepted.
    #[must_use]
    pub fn canonical_artifact_profile_blockers(&self) -> Vec<String> {
        let mut blockers = Vec::new();

        if self.kind != "binary_source_provenance" {
            blockers.push(format!("kind `{}` is not binary_source_provenance", self.kind));
        }
        if self.schema_version != BINARY_SOURCE_PROVENANCE_ARTIFACT_SCHEMA_VERSION {
            blockers.push(format!(
                "schema_version `{}` is not supported; expected `{}`",
                self.schema_version, BINARY_SOURCE_PROVENANCE_ARTIFACT_SCHEMA_VERSION
            ));
        }

        match self.source_provenance_artifact_digest.as_deref() {
            Some(digest) if is_canonical_sha256_uri(digest) => {
                match source_provenance_artifact_digest(self) {
                    Ok(expected) => {
                        let expected = format!("sha256:{expected}");
                        if digest != expected {
                            blockers.push(format!(
                                "source_provenance_artifact_digest mismatch: expected {expected}, actual {digest}"
                            ));
                        }
                    }
                    Err(error) => blockers.push(format!(
                        "source_provenance_artifact_digest could not be recomputed: {error}"
                    )),
                }
            }
            Some(_) => blockers.push(
                "source_provenance_artifact_digest is not canonical lowercase sha256:<hex>"
                    .to_string(),
            ),
            None => blockers.push("source_provenance_artifact_digest is missing".to_string()),
        }

        push_prefixed_profile_blockers(
            &mut blockers,
            "source_provenance",
            self.source_provenance.schema_blockers(),
        );
        if !self.source_provenance.effective_source_backpropagation_allowed() {
            blockers.push(
                "source_provenance is not exact source-backpropagation provenance".to_string(),
            );
        }

        match self.source_backpropagation_gate_sha256.as_deref() {
            Some(digest) if is_canonical_sha256_hex(digest) => {}
            Some(_) => blockers.push(
                "source_backpropagation_gate_sha256 is not canonical lowercase SHA-256 hex"
                    .to_string(),
            ),
            None => blockers.push("source_backpropagation_gate_sha256 is missing".to_string()),
        }

        match &self.source_backpropagation_gate {
            Some(gate) => {
                push_prefixed_profile_blockers(
                    &mut blockers,
                    "source_backpropagation_gate",
                    gate.canonical_artifact_profile_blockers(),
                );
                if gate.source_backpropagation_gate_sha256.as_deref()
                    != self.source_backpropagation_gate_sha256.as_deref()
                {
                    blockers.push(
                        "source_backpropagation_gate_sha256 does not match gate details"
                            .to_string(),
                    );
                }
            }
            None => blockers.push("source_backpropagation_gate is missing".to_string()),
        }

        if self.canonical_binary_provenance.records.is_empty() {
            blockers.push("canonical_binary_provenance.records is empty".to_string());
        }
        if self.source_provenance.exact_mapping_count
            != self.canonical_binary_provenance.records.len()
        {
            blockers.push(format!(
                "source_provenance.exact_mapping_count={} does not match {} canonical record(s)",
                self.source_provenance.exact_mapping_count,
                self.canonical_binary_provenance.records.len()
            ));
        }
        for (index, record) in self.canonical_binary_provenance.records.iter().enumerate() {
            push_prefixed_profile_blockers(
                &mut blockers,
                &format!("canonical_binary_provenance.records[{index}]"),
                record.canonical_artifact_profile_blockers(),
            );
        }
        if !self.blockers.is_empty() {
            blockers
                .push(format!("artifact has unresolved blockers: {}", self.blockers.join("; ")));
        }

        blockers
    }

    /// Whether this source-provenance JSON can be accepted as a canonical artifact view.
    #[must_use]
    pub fn canonical_artifact_profile_allows_acceptance(&self) -> bool {
        self.canonical_artifact_profile_blockers().is_empty()
    }
}

impl BinarySourceBackpropagationGateDetailsReport {
    fn canonical_artifact_profile_blockers(&self) -> Vec<String> {
        let mut blockers = Vec::new();
        if self.schema_version != SOURCE_BACKPROPAGATION_GATE_SCHEMA_VERSION {
            blockers.push(format!(
                "schema_version `{}` is not supported; expected `{}`",
                self.schema_version, SOURCE_BACKPROPAGATION_GATE_SCHEMA_VERSION
            ));
        }
        for (field, accepted) in [
            ("replay_grade_artifact_identity", self.replay_grade_artifact_identity),
            ("checked_certificate_identity", self.checked_certificate_identity),
            ("exact_replay_identity", self.exact_replay_identity),
            ("accepted_reconstruction_validation", self.accepted_reconstruction_validation),
            ("accepted_target_validation", self.accepted_target_validation),
            ("exact_source_provenance", self.exact_source_provenance),
            ("source_backpropagation_allowed", self.source_backpropagation_allowed),
        ] {
            if !accepted {
                blockers.push(format!("{field} is not accepted"));
            }
        }
        push_prefixed_profile_blockers(
            &mut blockers,
            "source_provenance",
            self.source_provenance.schema_blockers(),
        );
        if !self.source_provenance.effective_source_backpropagation_allowed() {
            blockers.push(
                "source_provenance is not exact source-backpropagation provenance".to_string(),
            );
        }
        match self.source_backpropagation_gate_sha256.as_deref() {
            Some(digest) if is_canonical_sha256_hex(digest) => {}
            Some(_) => blockers.push(
                "source_backpropagation_gate_sha256 is not canonical lowercase SHA-256 hex"
                    .to_string(),
            ),
            None => blockers.push("source_backpropagation_gate_sha256 is missing".to_string()),
        }
        if !self.blockers.is_empty() {
            blockers.push(format!("gate has unresolved blockers: {}", self.blockers.join("; ")));
        }
        blockers
    }
}

impl BinarySourceProvenanceRecordReport {
    fn canonical_artifact_profile_blockers(&self) -> Vec<String> {
        let mut blockers = Vec::new();
        push_prefixed_profile_blockers(
            &mut blockers,
            "origin",
            self.origin.canonical_provenance_blockers(),
        );
        if self.origin.source.is_none() || self.origin.span().is_binary() {
            blockers.push("origin does not carry an exact source span".to_string());
        }
        push_prefixed_profile_blockers(
            &mut blockers,
            "artifact_digest_identity",
            self.artifact_digest_identity.digest_identity_blockers(),
        );
        if self.source_status != "exact" {
            blockers.push(format!("source_status `{}` is not exact", self.source_status));
        }
        if self.provenance_status != "checked_exact" {
            blockers.push(format!(
                "provenance_status `{}` is not checked_exact",
                self.provenance_status
            ));
        }
        if !is_canonical_sha256_hex(&self.record_digest) {
            blockers.push("record_digest is not canonical lowercase SHA-256 hex".to_string());
        } else {
            match source_provenance_record_digest(
                &self.origin,
                &self.artifact_digest_identity,
                &self.source_status,
                &self.provenance_status,
                &self.proof_evidence,
            ) {
                Ok(expected) if self.record_digest != expected => blockers.push(format!(
                    "record_digest mismatch: expected {expected}, actual {}",
                    self.record_digest
                )),
                Ok(_) => {}
                Err(error) => blockers.push(format!(
                    "record_digest could not be recomputed from canonical material: {error}"
                )),
            }
        }
        push_prefixed_profile_blockers(
            &mut blockers,
            "proof_evidence",
            self.proof_evidence.canonical_artifact_profile_blockers(),
        );
        blockers
    }
}

impl BinarySourceProvenanceProofEvidenceReport {
    fn canonical_artifact_profile_blockers(&self) -> Vec<String> {
        let mut blockers = Vec::new();
        if self.solver_dispatch_id.trim().is_empty() {
            blockers.push("solver_dispatch_id is missing".to_string());
        }
        for (field, digest) in [
            ("checked_certificate_sha256", self.checked_certificate_sha256.as_str()),
            (
                "production_checker_evidence_sha256",
                self.production_checker_evidence_sha256.as_str(),
            ),
            (
                "source_backpropagation_gate_sha256",
                self.source_backpropagation_gate_sha256.as_str(),
            ),
            ("replay_transcript_digest", self.replay_transcript_digest.as_str()),
        ] {
            if !is_canonical_sha256_hex(digest) {
                blockers.push(format!("{field} is not canonical lowercase SHA-256 hex"));
            }
        }
        blockers
    }
}

fn is_canonical_sha256_uri(value: &str) -> bool {
    value.strip_prefix("sha256:").is_some_and(is_canonical_sha256_hex)
}

fn push_prefixed_profile_blockers(
    blockers: &mut Vec<String>,
    prefix: &str,
    nested_blockers: Vec<String>,
) {
    for blocker in nested_blockers {
        blockers.push(format!("{prefix}: {blocker}"));
    }
}

/// Report-friendly binary instruction location.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryLocationReport {
    /// Binary path when known.
    pub binary_path: Option<String>,
    /// Function entry address when known.
    pub function_entry: Option<u64>,
    /// Display form of `function_entry`, e.g. `0x401000`.
    pub function_entry_display: Option<String>,
    /// Instruction address.
    pub instruction_address: u64,
    /// Display form of `instruction_address`, e.g. `0x401010`.
    pub instruction_address_display: String,
    /// Compatibility source span. Binary-only origins use `binary:0x...`.
    pub source: SourceSpan,
}

/// Report-friendly binary instruction provenance.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryInstructionProvenanceReport {
    /// Binary path when known.
    pub binary_path: Option<String>,
    /// Function entry address when known.
    pub function_entry: Option<u64>,
    /// Display form of `function_entry`, e.g. `0x401000`.
    pub function_entry_display: Option<String>,
    /// Instruction address.
    pub instruction_address: u64,
    /// Display form of `instruction_address`, e.g. `0x401010`.
    pub instruction_address_display: String,
    /// Original instruction size in bytes, when known.
    pub instruction_size: Option<u8>,
    /// Legacy compact instruction encoding, when known.
    pub encoding: Option<u32>,
    /// Original instruction bytes as decoded from the input stream.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub instruction_bytes: Vec<u8>,
    /// Compatibility source span. Binary-only origins use `binary:0x...`.
    pub source: SourceSpan,
}

/// Report-friendly half-open binary address range.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryAddressRangeReport {
    /// Inclusive start address.
    pub start: u64,
    /// Exclusive end address.
    pub end: u64,
    /// Display form of the half-open range.
    pub range_display: String,
}

/// Build a report-friendly summary from a decompilation artifact.
#[must_use]
pub fn build_binary_decompilation_report(
    artifact: &DecompilationArtifact,
) -> BinaryDecompilationReport {
    let artifact_unsupported = combined_unsupported_ledger(
        &artifact.unsupported,
        &artifact.verification.unsupported_ledger,
    );
    let digest_identity = BinaryDigestIdentityReport::from_metadata(&artifact.binary);
    let proof_grade_gate = build_binary_artifact_proof_grade_gate_report(artifact);
    let unsupported = build_binary_unsupported_ledger_report(&artifact.unsupported);
    let source_provenance = BinarySourceProvenanceReport::from_summary(&artifact.source_provenance);
    let reconstruction = BinaryReconstructionReport::from_summary(&artifact.reconstruction);
    let source_backpropagation_gate = build_source_backpropagation_gate_report(
        &proof_grade_gate,
        &source_provenance,
        &reconstruction,
        &artifact.type_fact_source_backpropagation_blockers(),
    );
    let verification = build_binary_verification_report_with_gate(
        &artifact.verification,
        artifact.trust_level,
        &artifact_unsupported,
    );
    let unresolved_blockers = build_decompilation_unresolved_blocker_ledger(
        &proof_grade_gate,
        &digest_identity,
        &artifact.unsupported,
        &source_provenance,
        &source_backpropagation_gate,
        &reconstruction,
        &verification,
    );

    BinaryDecompilationReport {
        schema_version: artifact.schema_version,
        binary_path: artifact.binary.path.clone(),
        format: artifact.binary.format,
        architecture: artifact.binary.architecture.clone(),
        entry_point: artifact.binary.entry_point,
        entry_point_display: artifact.binary.entry_point.map(format_binary_address),
        target: artifact.target.clone(),
        trust_level: artifact.trust_level,
        digest_identity,
        proof_grade_gate,
        unresolved_blockers,
        unsupported,
        source_provenance,
        source_backpropagation_gate,
        reconstruction,
        verification,
        functions: artifact.functions.iter().map(build_binary_function_report).collect(),
    }
}

/// Build a runtime-compatible checked binary source-provenance handoff artifact.
///
/// The artifact is intentionally stricter than the aggregate report summary: it
/// emits checked exact rows only when the solver dispatch carries canonical
/// binary identity, exact source mapping, checked certificate identity,
/// production-checker evidence, source-backpropagation gate identity, and replay
/// transcript identity.
#[must_use]
pub fn build_binary_source_provenance_artifact_report(
    artifact: &DecompilationArtifact,
) -> BinarySourceProvenanceArtifactReport {
    let proof_grade_gate = build_binary_artifact_proof_grade_gate_report(artifact);
    let source_provenance_report =
        BinarySourceProvenanceReport::from_summary(&artifact.source_provenance);
    let reconstruction_report = BinaryReconstructionReport::from_summary(&artifact.reconstruction);
    let source_backpropagation_gate_report = build_source_backpropagation_gate_report(
        &proof_grade_gate,
        &source_provenance_report,
        &reconstruction_report,
        &artifact.type_fact_source_backpropagation_blockers(),
    );
    let source_backpropagation_gate_sha256 =
        common_source_backpropagation_gate_sha256(&artifact.verification.solver_dispatch);
    let source_backpropagation_gate =
        Some(BinarySourceBackpropagationGateDetailsReport::from_gate(
            &artifact.source_provenance,
            &source_backpropagation_gate_report,
            source_backpropagation_gate_sha256.clone(),
        ));
    let (records, mut blockers) = build_checked_source_provenance_records(
        artifact,
        source_backpropagation_gate_sha256.as_deref(),
    );

    if records.is_empty() {
        blockers.push(
            "checked binary source-provenance artifact has no checked exact handoff records"
                .to_string(),
        );
    }

    let canonical_binary_provenance = BinarySourceProvenanceRecordsReport { records };
    let mut report = BinarySourceProvenanceArtifactReport {
        kind: "binary_source_provenance".to_string(),
        schema_version: BINARY_SOURCE_PROVENANCE_ARTIFACT_SCHEMA_VERSION.to_string(),
        source_provenance: artifact.source_provenance.clone(),
        source_provenance_artifact_digest: None,
        verification: artifact.verification.clone(),
        reconstruction: Some(artifact.reconstruction.clone()),
        source_backpropagation_gate,
        source_backpropagation_gate_sha256,
        canonical_binary_provenance,
        blockers,
    };
    match source_provenance_artifact_digest(&report) {
        Ok(digest) => {
            report.source_provenance_artifact_digest = Some(format!("sha256:{digest}"));
        }
        Err(error) => report
            .blockers
            .push(format!("source_provenance_artifact_digest could not be serialized: {error}")),
    }
    report
}

/// Build a narrow proof-evidence summary from a decompilation artifact.
#[must_use]
pub fn build_binary_decompilation_proof_evidence_report(
    artifact: &DecompilationArtifact,
) -> BinaryDecompilationProofEvidenceReport {
    let artifact_unsupported = combined_unsupported_ledger(
        &artifact.unsupported,
        &artifact.verification.unsupported_ledger,
    );
    let verification = build_binary_verification_report_with_gate(
        &artifact.verification,
        artifact.trust_level,
        &artifact_unsupported,
    );
    let digest_identity = BinaryDigestIdentityReport::from_metadata(&artifact.binary);
    let proof_grade_gate = build_binary_artifact_proof_grade_gate_report(artifact);
    let unresolved_blockers = build_decompilation_unresolved_blocker_ledger(
        &proof_grade_gate,
        &digest_identity,
        &artifact.unsupported,
        &BinarySourceProvenanceReport::from_summary(&artifact.source_provenance),
        &build_source_backpropagation_gate_report(
            &proof_grade_gate,
            &BinarySourceProvenanceReport::from_summary(&artifact.source_provenance),
            &BinaryReconstructionReport::from_summary(&artifact.reconstruction),
            &artifact.type_fact_source_backpropagation_blockers(),
        ),
        &BinaryReconstructionReport::from_summary(&artifact.reconstruction),
        &verification,
    );

    BinaryDecompilationProofEvidenceReport {
        schema_version: artifact.schema_version,
        binary_path: artifact.binary.path.clone(),
        format: artifact.binary.format,
        architecture: artifact.binary.architecture.clone(),
        trust_level: artifact.trust_level,
        digest_identity,
        unsupported_ledger_records: artifact_unsupported.records.len(),
        total_vcs: verification.total_vcs,
        solver_dispatches: verification.solver_dispatches.len(),
        solver_dispatch_status_counts: verification.vc_status_counts,
        replay: verification.replay,
        replay_status_counts: verification.replay_status_counts,
        raw_solver_proof_byte_count: verification.certificate_checks.raw_solver_proof_byte_count,
        checked_certificate_coverage: verification.certificate_checks,
        proof_grade_gate,
        unresolved_blockers,
    }
}

/// Build a proof-grade gate report for a full decompilation artifact.
#[must_use]
pub fn build_binary_decompilation_proof_grade_gate_report(
    artifact: &DecompilationArtifact,
) -> BinaryDecompilationProofGradeGateReport {
    let artifact_gate = build_binary_artifact_proof_grade_gate_report(artifact);
    let functions = artifact
        .functions
        .iter()
        .map(|function| {
            let gate = build_binary_function_proof_grade_gate_report(function);
            BinaryFunctionProofGradeGateReport {
                name: function.name.clone(),
                entry: function.entry,
                entry_display: format_binary_address(function.entry),
                gate,
            }
        })
        .collect::<Vec<_>>();
    let accepted =
        artifact_gate.accepted && functions.iter().all(|function| function.gate.accepted);

    BinaryDecompilationProofGradeGateReport { accepted, artifact: artifact_gate, functions }
}

/// Build a report-friendly summary from a binary verification summary.
#[must_use]
pub fn build_binary_verification_report(
    summary: &BinaryVerificationSummary,
) -> BinaryVerificationReport {
    build_binary_verification_report_with_gate(
        summary,
        summary.trust_level,
        &summary.unsupported_ledger,
    )
}

/// Build a proof-grade gate report from shared binary verification evidence.
#[must_use]
pub fn build_binary_proof_grade_gate_report(
    final_trust_level: TrustLevel,
    unsupported_ledger: &UnsupportedLedger,
    summary: &BinaryVerificationSummary,
) -> BinaryProofGradeGateReport {
    let mut proved_vcs = 0;
    let mut checked_certificates = 0;
    let mut production_checked_certificates = 0;
    let mut malformed_production_evidence = 0;
    let mut replayed_vcs = 0;
    let mut certificate_only_replay_semantics_vcs = 0;
    let mut replay_semantics_satisfied_vcs = 0;
    let mut not_attempted = 0;
    let mut spurious = 0;
    let mut failed_replay = 0;
    let mut raw_solver_proof_bytes = 0;
    let mut raw_solver_proof_byte_count = 0;
    let mut replay_digest_identity_ready_vcs = 0;
    let mut replay_digest_identity_blocked_vcs = 0;
    let mut replay_boundary_count = 0;
    let mut unsupported_replay_boundary_count = 0;

    for dispatch in &summary.solver_dispatch {
        let replay_boundary_evidence = extract_replay_boundary_evidence(&dispatch.diagnostics);
        replay_boundary_count += replay_boundary_evidence.len();
        unsupported_replay_boundary_count += replay_boundary_evidence
            .iter()
            .filter(|evidence| !evidence.proof_grade_accepted)
            .count();

        if dispatch_proves_required_vc(dispatch) {
            proved_vcs += 1;
            if dispatch_has_checked_certificate_identity(dispatch) {
                checked_certificates += 1;
                match dispatch.certificate.production_checker_evidence_status() {
                    ProofCertificateProductionCheckerEvidenceStatus::Present { .. } => {
                        production_checked_certificates += 1;
                    }
                    ProofCertificateProductionCheckerEvidenceStatus::Malformed { .. } => {
                        malformed_production_evidence += 1;
                    }
                    ProofCertificateProductionCheckerEvidenceStatus::Missing => {}
                }
            }
        }

        if raw_solver_result_has_certificate_bytes(dispatch.result.as_ref()) {
            raw_solver_proof_bytes += 1;
        }
        raw_solver_proof_byte_count +=
            raw_solver_result_certificate_byte_count(dispatch.result.as_ref());

        match dispatch.replay {
            ReplayStatus::Replayed => {
                replayed_vcs += 1;
                if dispatch.replay_digest_identity_allows_proof_grade() {
                    replay_digest_identity_ready_vcs += 1;
                } else {
                    replay_digest_identity_blocked_vcs += 1;
                }
            }
            ReplayStatus::NotAttempted => not_attempted += 1,
            ReplayStatus::Spurious => spurious += 1,
            ReplayStatus::Failed => failed_replay += 1,
            _ => not_attempted += 1,
        }

        if dispatch_satisfies_replay_semantics(dispatch) {
            replay_semantics_satisfied_vcs += 1;
        }
        if dispatch_satisfies_certificate_only_replay_semantics(dispatch) {
            certificate_only_replay_semantics_vcs += 1;
        }
    }

    let required_vcs = summary.total_vcs;
    let solver_dispatches = summary.solver_dispatch.len();
    let unsupported_records = unsupported_ledger.records.len();
    let unsupported_by_family = unsupported_ledger.family_counts();
    let unsupported_family_counts = unsupported_ledger.family_count_rows();
    let aarch64_atomic_semantic_facts = unsupported_ledger.aarch64_atomic_semantic_facts();
    let aarch64_atomic_semantic_fact_count = aarch64_atomic_semantic_facts.len();
    let aarch64_atomic_semantic_fact_rejections = aarch64_atomic_semantic_facts
        .iter()
        .filter_map(Aarch64AtomicSemanticFact::proof_grade_rejection_reason)
        .collect::<Vec<_>>();
    let aarch64_atomic_semantic_facts_consumed_by_proof_model = aarch64_atomic_semantic_facts
        .iter()
        .all(Aarch64AtomicSemanticFact::proof_grade_gate_accepted);
    let aarch64_sync_boundary_facts = unsupported_ledger.aarch64_sync_boundary_semantic_facts();
    let aarch64_sync_boundary_fact_count = aarch64_sync_boundary_facts.len();
    let aarch64_sync_boundary_fact_rejections = aarch64_sync_boundary_facts
        .iter()
        .filter_map(Aarch64SyncBoundarySemanticFact::proof_grade_rejection_reason)
        .collect::<Vec<_>>();
    let aarch64_sync_boundary_facts_consumed_by_proof_model = aarch64_sync_boundary_facts
        .iter()
        .all(Aarch64SyncBoundarySemanticFact::proof_grade_gate_accepted);
    let non_proved_results = solver_dispatches.saturating_sub(proved_vcs);
    let unproved_vcs = required_vcs.saturating_sub(proved_vcs);
    let missing_certificates = required_vcs.saturating_sub(checked_certificates);
    let missing_production_evidence = required_vcs.saturating_sub(production_checked_certificates);
    let unsupported_ledger_empty = unsupported_records == 0;
    let all_required_vcs_proved =
        solver_dispatches == required_vcs && proved_vcs == required_vcs && non_proved_results == 0;
    let checked_certificates_for_all_required_vcs =
        all_required_vcs_proved && checked_certificates == required_vcs;
    let production_checked_certificates_for_all_required_vcs =
        checked_certificates_for_all_required_vcs
            && production_checked_certificates == required_vcs
            && malformed_production_evidence == 0;
    let full_replay_coverage = solver_dispatches == required_vcs && replayed_vcs == required_vcs;
    let replay_semantics_satisfied =
        solver_dispatches == required_vcs && replay_semantics_satisfied_vcs == required_vcs;

    let mut rejections = Vec::new();
    if final_trust_level != TrustLevel::ProofGrade {
        rejections.push(BinaryProofGradeGateRejectionReport::FinalTrustLevelNotProofGrade {
            found: final_trust_level,
        });
    }
    if !unsupported_ledger_empty {
        rejections.push(BinaryProofGradeGateRejectionReport::UnsupportedRecordsPresent {
            count: unsupported_records,
        });
    }
    if solver_dispatches != required_vcs {
        rejections.push(BinaryProofGradeGateRejectionReport::RequiredVcCoverageIncomplete {
            vc_count: required_vcs,
            solver_dispatches,
        });
    }
    if !all_required_vcs_proved {
        rejections.push(BinaryProofGradeGateRejectionReport::NonProvedVerificationConditions {
            vc_count: required_vcs,
            total_results: solver_dispatches,
            proved: proved_vcs,
            unproved_vcs,
            non_proved_results,
        });
    }
    if missing_certificates > 0 {
        rejections.push(BinaryProofGradeGateRejectionReport::MissingCheckedProofCertificates {
            vc_count: required_vcs,
            checked_certificates,
            missing_certificates,
        });
    }
    if missing_production_evidence > 0 || malformed_production_evidence > 0 {
        rejections.push(
            BinaryProofGradeGateRejectionReport::CheckedCertificateProductionManifestIncomplete {
                vc_count: required_vcs,
                production_checked_certificates,
                missing_production_evidence,
                malformed_production_evidence,
            },
        );
    }
    if solver_dispatches == 0 {
        rejections.push(BinaryProofGradeGateRejectionReport::ReplayStatusMissing);
    } else if !replay_semantics_satisfied {
        if solver_dispatches != required_vcs {
            rejections.push(BinaryProofGradeGateRejectionReport::ReplayCoverageIncomplete {
                vc_count: required_vcs,
                replay_records: solver_dispatches,
                replayed: replayed_vcs,
            });
        }
        if not_attempted > 0 {
            rejections
                .push(BinaryProofGradeGateRejectionReport::ReplayStatusUnknown { not_attempted });
        }
        if failed_replay > 0 || spurious > 0 {
            rejections.push(BinaryProofGradeGateRejectionReport::ReplayNotSuccessful {
                failed: failed_replay,
                spurious,
            });
        }
    }
    if replay_digest_identity_blocked_vcs > 0 {
        rejections.push(
            BinaryProofGradeGateRejectionReport::ReplayArtifactDigestIdentityNotExact {
                replayed_vcs,
                ready_replayed_vcs: replay_digest_identity_ready_vcs,
                blocked_replayed_vcs: replay_digest_identity_blocked_vcs,
            },
        );
    }
    if unsupported_replay_boundary_count > 0 {
        rejections.push(BinaryProofGradeGateRejectionReport::ReplayBoundarySemanticsUnsupported {
            boundary_count: replay_boundary_count,
            unsupported_boundary_count: unsupported_replay_boundary_count,
        });
    }
    if raw_solver_proof_bytes > 0 {
        rejections.push(BinaryProofGradeGateRejectionReport::RawSolverProofBytesPresent {
            count: raw_solver_proof_bytes,
        });
    }
    if !aarch64_atomic_semantic_fact_rejections.is_empty() {
        rejections.push(
            BinaryProofGradeGateRejectionReport::Aarch64AtomicSemanticFactsNotConsumed {
                count: aarch64_atomic_semantic_fact_count,
                unconsumed: aarch64_atomic_semantic_fact_rejections.len(),
                missing_witnesses: aarch64_atomic_missing_witnesses(&aarch64_atomic_semantic_facts),
            },
        );
    }
    if !aarch64_sync_boundary_fact_rejections.is_empty() {
        rejections.push(BinaryProofGradeGateRejectionReport::Aarch64SyncBoundaryFactsNotConsumed {
            count: aarch64_sync_boundary_fact_count,
            unconsumed: aarch64_sync_boundary_fact_rejections.len(),
            missing_witnesses: aarch64_sync_boundary_missing_witnesses(
                &aarch64_sync_boundary_facts,
            ),
        });
    }

    BinaryProofGradeGateReport {
        accepted: rejections.is_empty(),
        final_trust_level,
        unsupported_ledger_empty,
        all_required_vcs_proved,
        checked_certificates_for_all_required_vcs,
        production_checked_certificates_for_all_required_vcs,
        full_replay_coverage,
        replay_semantics_satisfied,
        reconstruction_validated: true,
        target_semantics_consumed: true,
        required_vcs,
        solver_dispatches,
        proved_vcs,
        checked_certificates,
        production_checked_certificates,
        replayed_vcs,
        certificate_only_replay_semantics_vcs,
        replay_semantics_satisfied_vcs,
        validated_target_outputs: 0,
        target_validation_blockers: 0,
        preserved_symbolic_formulas: 0,
        symbolic_formulas_consumed_by_proof_model: true,
        unsupported_records,
        unsupported_by_family,
        unsupported_family_counts,
        raw_solver_proof_bytes,
        raw_solver_proof_byte_count,
        aarch64_atomic_semantic_fact_count,
        aarch64_atomic_semantic_facts_consumed_by_proof_model,
        aarch64_atomic_semantic_fact_rejections,
        aarch64_sync_boundary_fact_count,
        aarch64_sync_boundary_facts_consumed_by_proof_model,
        aarch64_sync_boundary_fact_rejections,
        blocker_groups: build_proof_grade_blocker_groups(&rejections),
        rejections,
    }
}

fn aarch64_atomic_missing_witnesses(facts: &[Aarch64AtomicSemanticFact]) -> Vec<String> {
    let mut witnesses = BTreeSet::new();
    for fact in facts {
        if fact.proof_grade_gate_accepted() {
            continue;
        }
        if fact.missing_witnesses.is_empty() {
            witnesses.insert("proof model consumption".to_string());
        } else {
            witnesses.extend(fact.missing_witnesses.iter().cloned());
        }
    }
    witnesses.into_iter().collect()
}

fn aarch64_sync_boundary_missing_witnesses(
    facts: &[Aarch64SyncBoundarySemanticFact],
) -> Vec<String> {
    let mut witnesses = BTreeSet::new();
    for fact in facts {
        if fact.proof_grade_gate_accepted() {
            continue;
        }
        if fact.missing_witnesses.is_empty() {
            witnesses.insert("proof model consumption".to_string());
        } else {
            witnesses.extend(fact.missing_witnesses.iter().cloned());
        }
    }
    witnesses.into_iter().collect()
}

fn build_binary_artifact_proof_grade_gate_report(
    artifact: &DecompilationArtifact,
) -> BinaryProofGradeGateReport {
    let unsupported = combined_unsupported_ledger(
        &artifact.unsupported,
        &artifact.verification.unsupported_ledger,
    );
    let gate = build_binary_proof_grade_gate_report(
        artifact.trust_level,
        &unsupported,
        &artifact.verification,
    );
    let gate = with_artifact_reconstruction_gate(gate, &artifact.reconstruction);
    let gate = with_source_provenance_gate(gate, &artifact.source_provenance);
    with_digest_identity_gate(gate, &artifact.binary)
}

fn build_binary_function_proof_grade_gate_report(
    function: &DecompiledFunction,
) -> BinaryProofGradeGateReport {
    let unsupported = combined_unsupported_ledger(
        &function.unsupported,
        &function.verification.unsupported_ledger,
    );
    let gate = build_binary_proof_grade_gate_report(
        function.trust_level,
        &unsupported,
        &function.verification,
    );
    with_function_reconstruction_gate(gate, function.output.as_ref())
}

fn combined_unsupported_ledger(
    primary: &UnsupportedLedger,
    verification: &UnsupportedLedger,
) -> UnsupportedLedger {
    let mut records = Vec::with_capacity(primary.records.len() + verification.records.len());
    records.extend(primary.records.iter().cloned());
    records.extend(verification.records.iter().cloned());
    UnsupportedLedger { records }
}

fn with_artifact_reconstruction_gate(
    gate: BinaryProofGradeGateReport,
    reconstruction: &ReconstructionSummary,
) -> BinaryProofGradeGateReport {
    let target = reconstruction.target.clone();
    let status = reconstruction.validation;
    let target_outputs =
        reconstruction.outputs.iter().filter(|output| output.target == target).collect::<Vec<_>>();
    let validated_outputs = target_outputs
        .iter()
        .filter(|output| output.validation == ReconstructionValidationStatus::Validated)
        .count();
    let target_validation_blockers =
        target_outputs.iter().map(|output| output.target_validation_blockers.len()).sum();
    let preserved_symbolic_formulas =
        target_outputs.iter().map(|output| output.preserved_symbolic_formulas.len()).sum();
    let symbolic_formulas_consumed_by_proof_model = target_outputs
        .iter()
        .all(|output| output_symbolic_formulas_consumed_by_proof_model(output));

    with_reconstruction_target_semantics_gate(
        gate,
        target,
        status,
        validated_outputs,
        target_validation_blockers,
        preserved_symbolic_formulas,
        symbolic_formulas_consumed_by_proof_model,
    )
}

fn with_function_reconstruction_gate(
    gate: BinaryProofGradeGateReport,
    output: Option<&DecompiledOutput>,
) -> BinaryProofGradeGateReport {
    let target = output.map_or(DecompileTarget::TrustIr, |output| output.target.clone());
    let status =
        output.map_or(ReconstructionValidationStatus::NotAttempted, |output| output.validation);
    let validated_outputs = usize::from(status == ReconstructionValidationStatus::Validated);
    let target_validation_blockers =
        output.map_or(0, |output| output.target_validation_blockers.len());
    let preserved_symbolic_formulas =
        output.map_or(0, |output| output.preserved_symbolic_formulas.len());
    let symbolic_formulas_consumed_by_proof_model =
        output.is_none_or(output_symbolic_formulas_consumed_by_proof_model);

    with_reconstruction_target_semantics_gate(
        gate,
        target,
        status,
        validated_outputs,
        target_validation_blockers,
        preserved_symbolic_formulas,
        symbolic_formulas_consumed_by_proof_model,
    )
}

fn with_reconstruction_target_semantics_gate(
    mut gate: BinaryProofGradeGateReport,
    target: DecompileTarget,
    status: ReconstructionValidationStatus,
    validated_outputs: usize,
    target_validation_blockers: usize,
    preserved_symbolic_formulas: usize,
    symbolic_formulas_consumed_by_proof_model: bool,
) -> BinaryProofGradeGateReport {
    gate.reconstruction_validated = status == ReconstructionValidationStatus::Validated;
    gate.validated_target_outputs = validated_outputs;
    gate.target_validation_blockers = target_validation_blockers;
    gate.preserved_symbolic_formulas = preserved_symbolic_formulas;
    gate.symbolic_formulas_consumed_by_proof_model = symbolic_formulas_consumed_by_proof_model;
    gate.target_semantics_consumed = gate.reconstruction_validated
        && validated_outputs > 0
        && target_validation_blockers == 0
        && symbolic_formulas_consumed_by_proof_model;
    if !gate.reconstruction_validated {
        gate.rejections.push(
            BinaryProofGradeGateRejectionReport::ReconstructionValidationNotValidated { status },
        );
    }
    if gate.reconstruction_validated && !gate.target_semantics_consumed {
        gate.rejections.push(BinaryProofGradeGateRejectionReport::TargetSemanticsNotConsumed {
            target: target.clone(),
            validated_outputs,
            target_validation_blockers,
        });
    }
    if target_validation_blockers > 0 {
        gate.rejections.push(
            BinaryProofGradeGateRejectionReport::TargetValidationBlockersPresent {
                target: target.clone(),
                count: target_validation_blockers,
            },
        );
    }
    if preserved_symbolic_formulas > 0 && !symbolic_formulas_consumed_by_proof_model {
        gate.rejections.push(BinaryProofGradeGateRejectionReport::SymbolicFormulasNotConsumed {
            target,
            count: preserved_symbolic_formulas,
        });
    }
    refresh_proof_grade_blocker_groups(&mut gate);
    gate.accepted = gate.rejections.is_empty();
    gate
}

fn output_symbolic_formulas_consumed_by_proof_model(output: &DecompiledOutput) -> bool {
    output.preserved_symbolic_formulas.is_empty()
        || output.preserved_symbolic_formulas.iter().all(|formula| {
            symbolic_formula_consumer_blockers_for_formula(output, formula).is_empty()
        })
}

fn symbolic_formula_consumer_diagnostic(diagnostic: &str) -> bool {
    diagnostic.contains("target proof consumer accepted")
        || diagnostic.contains("target proof-consumer accepted")
        || diagnostic.contains("target-consumer=accepted")
        || diagnostic.contains("symbolic-formula-proof-consumer=accepted")
        || diagnostic.contains("trust_symbolic.formula=consumed")
}

fn symbolic_formula_consumer_diagnostic_for_target(
    diagnostic: &str,
    target: &DecompileTarget,
) -> bool {
    if !symbolic_formula_consumer_diagnostic(diagnostic) {
        return false;
    }
    if !diagnostic_has_explicit_target_consumer_acceptance(diagnostic) {
        return true;
    }
    diagnostic_has_target_consumer_acceptance(diagnostic, target)
}

fn symbolic_formula_consumer_diagnostic_for_formula(
    diagnostic: &str,
    target: &DecompileTarget,
    formula: &PreservedSymbolicFormula,
) -> bool {
    symbolic_formula_consumer_diagnostic_for_target(diagnostic, target)
        && formula.matches_schema_aware_consumer_diagnostic(diagnostic)
        && symbolic_formula_consumer_diagnostic_matches_location(diagnostic, formula)
        && symbolic_formula_required_evidence(formula)
            .into_iter()
            .all(|obligation| obligation.diagnostic_satisfied_by(diagnostic))
}

fn symbolic_formula_consumer_diagnostic_matches_location(
    diagnostic: &str,
    formula: &PreservedSymbolicFormula,
) -> bool {
    let function_matches = formula.function.as_ref().is_none_or(|function| {
        diagnostic_has_token(diagnostic, "function", function)
            || diagnostic.contains(&format!("{function}::"))
    });
    let block_matches = formula.block.is_none_or(|block| {
        diagnostic_has_token(diagnostic, "block", &block.to_string())
            || diagnostic.contains(&format!("::bb{block}"))
    });
    let statement_matches = formula.statement_index.is_none_or(|statement_index| {
        diagnostic_has_token(diagnostic, "statement_index", &statement_index.to_string())
            || diagnostic.contains(&format!("::stmt{statement_index}"))
    });
    let location_matches = formula.location.is_empty()
        || diagnostic_has_token(diagnostic, "location", &formula.location)
        || diagnostic.contains(&formula.location);

    function_matches && block_matches && statement_matches && location_matches
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SymbolicFormulaEvidenceRequirement {
    label: String,
    key: Option<String>,
    value: String,
}

impl SymbolicFormulaEvidenceRequirement {
    fn token(label: impl Into<String>, key: impl Into<String>, value: impl Into<String>) -> Self {
        Self { label: label.into(), key: Some(key.into()), value: value.into() }
    }

    fn contains(label: impl Into<String>, value: impl Into<String>) -> Self {
        Self { label: label.into(), key: None, value: value.into() }
    }

    fn diagnostic_satisfied_by(&self, diagnostic: &str) -> bool {
        match &self.key {
            Some(key) => diagnostic_has_token(diagnostic, key, &self.value),
            None => diagnostic.contains(&self.value),
        }
    }
}

fn symbolic_formula_required_evidence(
    formula: &PreservedSymbolicFormula,
) -> Vec<SymbolicFormulaEvidenceRequirement> {
    let mut required = Vec::new();
    let formula_evidence = formula.evidence();
    required.push(SymbolicFormulaEvidenceRequirement::token(
        "formula.schema",
        "formula.schema",
        formula_evidence.schema.clone(),
    ));
    required.push(SymbolicFormulaEvidenceRequirement::token(
        "formula.digest",
        "formula.digest",
        formula_evidence.digest,
    ));
    required.push(SymbolicFormulaEvidenceRequirement::token(
        "formula.origin",
        "formula.origin",
        formula_evidence.origin,
    ));
    match serde_json::to_string(&formula.formula) {
        Ok(formula_json) => required.push(SymbolicFormulaEvidenceRequirement::token(
            "formula_json",
            "formula_json",
            formula_json,
        )),
        Err(error) => required.push(SymbolicFormulaEvidenceRequirement::contains(
            "formula_json_error",
            format!("formula_json_error={error}"),
        )),
    }
    required.push(SymbolicFormulaEvidenceRequirement::token(
        "formula.smtlib2",
        "formula.smtlib2",
        formula.formula.to_smtlib(),
    ));
    required.push(SymbolicFormulaEvidenceRequirement::token(
        "formula.debug",
        "formula.debug",
        format!("{:?}", formula.formula),
    ));
    if let Some(sort) = strict_formula_sort(&formula.formula) {
        required.push(SymbolicFormulaEvidenceRequirement::token(
            "formula.sort",
            "formula.sort",
            sort.to_smtlib(),
        ));
    }
    required.extend(collect_formula_sort_declarations(&formula.formula).into_iter().map(
        |declaration| {
            SymbolicFormulaEvidenceRequirement::contains(
                format!("smtlib declaration for {}", declaration.name),
                declaration.smtlib_declaration,
            )
        },
    ));
    required
}

fn diagnostic_has_token(diagnostic: &str, key: &str, value: &str) -> bool {
    let quoted = format!("{value:?}");
    [
        format!("{key}={value}"),
        format!("{key}=str:{value}"),
        format!("{key}=str:{quoted}"),
        format!("{key}={quoted}"),
    ]
    .iter()
    .any(|needle| diagnostic.contains(needle))
}

fn diagnostic_has_explicit_target_consumer_acceptance(diagnostic: &str) -> bool {
    [
        DecompileTarget::TrustIr,
        DecompileTarget::Rust,
        DecompileTarget::TrustCg,
        DecompileTarget::Wasm,
        DecompileTarget::PseudoSource,
    ]
    .into_iter()
    .any(|target| diagnostic_has_target_consumer_acceptance(diagnostic, &target))
}

fn diagnostic_has_target_consumer_acceptance(diagnostic: &str, target: &DecompileTarget) -> bool {
    target_consumer_acceptance_markers(target)
        .iter()
        .any(|marker| diagnostic_has_target_marker_acceptance(diagnostic, marker))
}

fn target_consumer_acceptance_markers(target: &DecompileTarget) -> Vec<String> {
    match target {
        DecompileTarget::TrustIr => vec!["trust_ir".to_string()],
        DecompileTarget::Rust => vec!["rust".to_string()],
        DecompileTarget::TrustCg => vec!["trust-cg".to_string()],
        DecompileTarget::Wasm => vec!["wasm".to_string()],
        DecompileTarget::PseudoSource => {
            vec!["pseudo-source".to_string(), "pseudo_source".to_string()]
        }
        DecompileTarget::Other(name) => vec![name.to_ascii_lowercase()],
        _ => vec![format!("{target:?}").to_ascii_lowercase()],
    }
}

fn diagnostic_has_target_marker_acceptance(diagnostic: &str, marker: &str) -> bool {
    let diagnostic = diagnostic.to_ascii_lowercase();
    let marker = marker.to_ascii_lowercase();
    [
        format!("{marker} target proof consumer accepted"),
        format!("{marker} target proof-consumer accepted"),
        format!("target={marker}; target proof consumer accepted"),
        format!("target={marker}; target proof-consumer accepted"),
        format!("target={marker} target-consumer=accepted"),
        format!("target={marker}; target-consumer=accepted"),
        format!("target={marker}, target-consumer=accepted"),
        format!("target={marker} symbolic-formula-proof-consumer=accepted"),
        format!("target={marker}; symbolic-formula-proof-consumer=accepted"),
    ]
    .iter()
    .any(|needle| diagnostic.contains(needle))
}

fn target_validation_blocker_is_symbolic_formula_consumer_blocker(
    blocker: &TargetValidationBlocker,
) -> bool {
    let feature = blocker.feature.as_str();
    feature == "symbolic-formula-proof-semantics"
        || feature == "trust_symbolic_formula_not_consumed"
        || (feature.contains("formula")
            && (feature.contains("not-consumed")
                || feature.contains("missing")
                || feature.contains("unavailable")
                || feature.contains("proof-semantics")))
}

fn symbolic_formula_consumer_blockers(output: &DecompiledOutput) -> Vec<String> {
    if output.preserved_symbolic_formulas.is_empty() {
        return Vec::new();
    }

    let mut blockers = output
        .preserved_symbolic_formulas
        .iter()
        .flat_map(|formula| symbolic_formula_consumer_blockers_for_formula(output, formula))
        .collect::<Vec<_>>();
    blockers.sort();
    blockers.dedup();
    blockers
}

fn symbolic_formula_consumer_blockers_for_formula(
    output: &DecompiledOutput,
    formula: &PreservedSymbolicFormula,
) -> Vec<String> {
    let mut blockers = output
        .diagnostics
        .iter()
        .filter(|diagnostic| {
            symbolic_formula_consumer_diagnostic(diagnostic)
                && diagnostic_has_explicit_target_consumer_acceptance(diagnostic)
                && !symbolic_formula_consumer_diagnostic_for_target(diagnostic, &output.target)
        })
        .map(|diagnostic| {
            format!(
                "stale target proof consumer acceptance for {:?}: {}",
                output.target, diagnostic
            )
        })
        .collect::<Vec<_>>();

    blockers.extend(symbolic_formula_schema_blockers(formula));

    blockers.extend(
        output
            .target_validation_blockers
            .iter()
            .filter(|blocker| {
                target_validation_blocker_is_symbolic_formula_consumer_blocker(blocker)
            })
            .map(|blocker| {
                format!(
                    "{}:{}:{}",
                    blocker.stage,
                    blocker.feature,
                    if blocker.reason.is_empty() {
                        "target proof consumer did not accept preserved trust_symbolic.formula"
                    } else {
                        blocker.reason.as_str()
                    }
                )
            }),
    );

    if blockers.is_empty()
        && output.diagnostics.iter().any(|diagnostic| {
            symbolic_formula_consumer_diagnostic_for_formula(diagnostic, &output.target, formula)
        })
    {
        return Vec::new();
    }

    if blockers.is_empty()
        && output.diagnostics.iter().any(|diagnostic| {
            symbolic_formula_consumer_diagnostic_for_target(diagnostic, &output.target)
        })
    {
        blockers.extend(
            symbolic_formula_required_evidence(formula)
                .into_iter()
                .filter(|requirement| {
                    !output
                        .diagnostics
                        .iter()
                        .any(|diagnostic| requirement.diagnostic_satisfied_by(diagnostic))
                })
                .map(|requirement| {
                    format!(
                        "schema-aware target proof consumer did not consume {} for preserved trust_symbolic.formula",
                        requirement.label
                    )
                }),
        );
    }

    if blockers.is_empty() {
        blockers.push(
            "missing target proof consumer for preserved trust_symbolic.formula; schema-aware evidence required"
                .to_string(),
        );
    }
    blockers
}

fn symbolic_formula_schema_blockers(formula: &PreservedSymbolicFormula) -> Vec<String> {
    let mut blockers = Vec::new();
    if serde_json::to_string(&formula.formula).is_err() {
        blockers
            .push("missing formula_json metadata for preserved trust_symbolic.formula".to_string());
    }
    if strict_formula_sort(&formula.formula).is_none() {
        blockers.push(
            "missing strict formula.sort metadata for preserved trust_symbolic.formula".to_string(),
        );
    }
    let smtlib = formula.formula.to_smtlib();
    if smtlib.trim().is_empty() {
        blockers.push(
            "missing formula.smtlib2 metadata for preserved trust_symbolic.formula".to_string(),
        );
    }
    let debug = format!("{:?}", formula.formula);
    if debug.trim().is_empty() {
        blockers.push(
            "missing formula.debug metadata for preserved trust_symbolic.formula".to_string(),
        );
    }

    let mut by_name: BTreeMap<String, BTreeSet<Sort>> = BTreeMap::new();
    for declaration in collect_formula_sort_declarations(&formula.formula) {
        by_name.entry(declaration.name).or_default().insert(declaration.sort);
    }
    for (name, sorts) in by_name {
        if sorts.len() > 1 {
            let rendered = sorts.into_iter().map(|sort| sort.to_smtlib()).collect::<Vec<_>>();
            blockers.push(format!(
                "conflicting SMT-LIB sort declarations for preserved trust_symbolic.formula variable {name}: {}",
                rendered.join(", ")
            ));
        }
    }

    blockers
}

fn with_source_provenance_gate(
    mut gate: BinaryProofGradeGateReport,
    source_provenance: &BinarySourceProvenanceSummary,
) -> BinaryProofGradeGateReport {
    if !source_provenance.has_exact_debug_source_provenance() {
        gate.rejections.push(BinaryProofGradeGateRejectionReport::SourceProvenanceNotExact {
            status: source_provenance.status.clone(),
            exact_mapping_count: source_provenance.exact_mapping_count,
        });
    }
    refresh_proof_grade_blocker_groups(&mut gate);
    gate.accepted = gate.rejections.is_empty();
    gate
}

fn with_digest_identity_gate(
    mut gate: BinaryProofGradeGateReport,
    binary: &BinaryArtifactMetadata,
) -> BinaryProofGradeGateReport {
    let blockers = binary.digest_identity_blockers();
    if !blockers.is_empty() {
        gate.rejections
            .push(BinaryProofGradeGateRejectionReport::DigestIdentityNotExact { blockers });
    }
    refresh_proof_grade_blocker_groups(&mut gate);
    gate.accepted = gate.rejections.is_empty();
    gate
}

fn build_source_backpropagation_gate_report(
    proof_gate: &BinaryProofGradeGateReport,
    source_provenance: &BinarySourceProvenanceReport,
    reconstruction: &BinaryReconstructionReport,
    type_ownership_blockers: &[String],
) -> BinarySourceBackpropagationGateReport {
    let mut blockers = Vec::new();

    if reconstruction.validation != ReconstructionValidationStatus::Validated
        || reconstruction.output_count == 0
    {
        blockers.push(source_backpropagation_gate_blocker(
            SOURCE_BACKPROPAGATION_MISSING_RECONSTRUCTION,
            format!(
                "accepted reconstruction is missing: validation={:?}, outputs={}",
                reconstruction.validation, reconstruction.output_count
            ),
        ));
    }
    if !source_provenance.effective_source_backpropagation_allowed() {
        blockers.push(source_backpropagation_gate_blocker(
            SOURCE_BACKPROPAGATION_EXACT_SOURCE_PROVENANCE,
            format!(
                "exact source provenance is missing: status={}, exact_mapping_count={}, source_backpropagation_allowed={}",
                source_provenance.status,
                source_provenance.exact_mapping_count,
                source_provenance.effective_source_backpropagation_allowed()
            ),
        ));
    }
    if !type_ownership_blockers.is_empty() {
        blockers.push(source_backpropagation_gate_blocker(
            SOURCE_BACKPROPAGATION_TYPE_OWNERSHIP,
            format!(
                "type ownership is not exact for source backpropagation: {}",
                type_ownership_blockers.join("; ")
            ),
        ));
    }
    if !proof_gate.target_semantics_consumed || proof_gate.target_validation_blockers > 0 {
        blockers.push(source_backpropagation_gate_blocker(
            SOURCE_BACKPROPAGATION_TARGET_VALIDATION,
            format!(
                "target validation is not accepted: target_semantics_consumed={}, target_validation_blockers={}, preserved_symbolic_formulas={}",
                proof_gate.target_semantics_consumed,
                proof_gate.target_validation_blockers,
                proof_gate.preserved_symbolic_formulas
            ),
        ));
    }
    if proof_gate.required_vcs == 0
        || !proof_gate.checked_certificates_for_all_required_vcs
        || !proof_gate.production_checked_certificates_for_all_required_vcs
    {
        blockers.push(source_backpropagation_gate_blocker(
            SOURCE_BACKPROPAGATION_CHECKED_CERTIFICATE_IDENTITY,
            format!(
                "checked certificate identity is missing: checked={}/{}, production_checked={}/{}",
                proof_gate.checked_certificates,
                proof_gate.required_vcs,
                proof_gate.production_checked_certificates,
                proof_gate.required_vcs
            ),
        ));
    }
    if proof_gate.required_vcs == 0
        || !proof_gate.full_replay_coverage
        || !proof_gate.replay_semantics_satisfied
        || proof_gate.blocker_groups.replay.iter().any(|rejection| {
            matches!(
                rejection,
                BinaryProofGradeGateRejectionReport::ReplayArtifactDigestIdentityNotExact { .. }
            )
        })
    {
        blockers.push(source_backpropagation_gate_blocker(
            SOURCE_BACKPROPAGATION_REPLAY_IDENTITY,
            format!(
                "replay identity is missing: replayed={}/{}, replay_semantics_satisfied={}, replay_semantics_satisfied_vcs={}",
                proof_gate.replayed_vcs,
                proof_gate.required_vcs,
                proof_gate.replay_semantics_satisfied,
                proof_gate.replay_semantics_satisfied_vcs
            ),
        ));
    }

    let missing_labels = blockers.iter().map(|blocker| blocker.label.clone()).collect::<Vec<_>>();
    let accepted = proof_gate.accepted && blockers.is_empty();

    BinarySourceBackpropagationGateReport {
        accepted,
        status: if accepted { "accepted".to_string() } else { "rejected".to_string() },
        required_labels: source_backpropagation_required_labels(),
        missing_labels,
        blockers,
    }
}

fn source_backpropagation_gate_blocker(
    label: &str,
    detail: impl Into<String>,
) -> BinarySourceBackpropagationGateBlockerReport {
    BinarySourceBackpropagationGateBlockerReport {
        label: label.to_string(),
        stage: SOURCE_BACKPROPAGATION_GATE_STAGE.to_string(),
        detail: detail.into(),
    }
}

fn build_binary_verification_report_with_gate(
    summary: &BinaryVerificationSummary,
    final_trust_level: TrustLevel,
    unsupported_ledger: &UnsupportedLedger,
) -> BinaryVerificationReport {
    let mut vc_status_counts = BTreeMap::new();
    let mut replay_status_counts = BTreeMap::new();
    let mut solver_dispatches = Vec::with_capacity(summary.solver_dispatch.len());

    for dispatch in &summary.solver_dispatch {
        *vc_status_counts.entry(format!("{:?}", dispatch.status)).or_default() += 1;
        *replay_status_counts.entry(format!("{:?}", dispatch.replay)).or_default() += 1;
        solver_dispatches.push(build_solver_dispatch_report(dispatch));
    }
    let proof_grade_gate =
        build_binary_proof_grade_gate_report(final_trust_level, unsupported_ledger, summary);
    let unsupported_ledger_report =
        build_binary_unsupported_ledger_report(&summary.unsupported_ledger);
    let certificate_checks = build_certificate_check_report(summary);
    let unresolved_blockers = build_verification_unresolved_blocker_ledger(
        &proof_grade_gate,
        unsupported_ledger,
        &certificate_checks,
        &solver_dispatches,
    );

    BinaryVerificationReport {
        status: summary.status,
        trust_level: summary.trust_level,
        total_vcs: summary.total_vcs,
        proved: summary.proved,
        failed: summary.failed,
        unknown: summary.unknown,
        timeout: summary.timeout,
        unsupported: summary.unsupported,
        rejected: summary.rejected,
        replay: summary.replay,
        proof_grade_gate,
        unresolved_blockers,
        unsupported_ledger: unsupported_ledger_report,
        vc_status_counts,
        replay_status_counts,
        certificate_checks,
        solver_dispatches,
    }
}

/// Build a report-friendly unsupported ledger summary.
#[must_use]
pub fn build_binary_unsupported_ledger_report(
    ledger: &UnsupportedLedger,
) -> BinaryUnsupportedLedgerReport {
    let aarch64_atomic_semantic_facts = ledger
        .aarch64_atomic_semantic_facts()
        .iter()
        .map(BinaryAarch64AtomicSemanticFactReport::from_fact)
        .collect::<Vec<_>>();
    let aarch64_atomic_semantic_fact_count = aarch64_atomic_semantic_facts.len();
    let aarch64_sync_boundary_facts = ledger
        .aarch64_sync_boundary_semantic_facts()
        .iter()
        .map(BinaryAarch64SyncBoundaryFactReport::from_fact)
        .collect::<Vec<_>>();
    let aarch64_sync_boundary_fact_count = aarch64_sync_boundary_facts.len();
    let mut report = BinaryUnsupportedLedgerReport {
        total_records: ledger.records.len(),
        by_stage: BTreeMap::new(),
        by_feature: BTreeMap::new(),
        by_family: ledger.family_counts(),
        family_counts: ledger.family_count_rows(),
        aarch64_atomic_semantic_facts,
        aarch64_atomic_semantic_fact_count,
        aarch64_sync_boundary_facts,
        aarch64_sync_boundary_fact_count,
        locations: Vec::new(),
    };

    for record in &ledger.records {
        *report.by_stage.entry(record.stage.clone()).or_default() += 1;
        *report.by_feature.entry(record.feature.clone()).or_default() += 1;
        if let Some(origin) = &record.origin {
            report.locations.push(BinaryLocationReport::from_origin(origin));
        }
    }

    report
}

/// Format a binary decompilation artifact as a human-readable summary.
#[must_use]
pub fn format_binary_decompilation_summary(artifact: &DecompilationArtifact) -> String {
    let report = build_binary_decompilation_report(artifact);
    format_binary_decompilation_report(&report)
}

/// Format a report-friendly binary decompilation summary.
#[must_use]
pub fn format_binary_decompilation_report(report: &BinaryDecompilationReport) -> String {
    let mut lines = Vec::new();
    lines.push(format!(
        "Trust binary decompilation report: {} ({:?}, {:?})",
        report.binary_path.as_deref().unwrap_or("<unknown>"),
        report.format,
        report.target
    ));
    lines.push(format!("  Architecture: {}", report.architecture));
    if let Some(entry) = &report.entry_point_display {
        lines.push(format!("  Entry: {entry}"));
    }
    lines.push(format!("  Trust level: {:?}", report.trust_level));
    lines.push(format_digest_identity_summary("  Digest identity", &report.digest_identity));
    lines.push(format_binary_proof_grade_gate_line("  Proof-grade gate", &report.proof_grade_gate));
    append_gate_rejection_details(&mut lines, "  ", "artifact", &report.proof_grade_gate);
    lines.push(format_unresolved_blocker_summary(
        "  Unresolved blockers",
        &report.unresolved_blockers,
    ));
    append_unresolved_blockers(&mut lines, "  ", &report.unresolved_blockers);
    lines.push(format_unsupported_summary("  Unsupported ledger", &report.unsupported));
    lines.push(format_source_provenance_summary("  Source provenance", &report.source_provenance));
    append_source_provenance_diagnostics(&mut lines, "  ", &report.source_provenance);
    lines.push(format_source_backpropagation_gate_summary(
        "  Source backpropagation gate",
        &report.source_backpropagation_gate,
    ));
    append_source_backpropagation_gate_blockers(
        &mut lines,
        "  ",
        &report.source_backpropagation_gate,
    );
    lines.push(format_reconstruction_summary("  Reconstruction", &report.reconstruction));
    append_reconstruction_diagnostics(&mut lines, "  ", &report.reconstruction);
    append_target_validation_blockers(&mut lines, "  ", &report.reconstruction);
    append_preserved_symbolic_formulas(&mut lines, "  ", &report.reconstruction);
    lines.push(format_binary_verification_line("  Verification", &report.verification));
    append_aarch64_atomic_semantic_facts(
        &mut lines,
        "  ",
        "AArch64 atomic semantic facts",
        &report.unsupported,
    );
    append_aarch64_sync_boundary_facts(
        &mut lines,
        "  ",
        "AArch64 sync boundary facts",
        &report.unsupported,
    );
    append_aarch64_atomic_semantic_facts(
        &mut lines,
        "  ",
        "Verification AArch64 atomic semantic facts",
        &report.verification.unsupported_ledger,
    );
    append_aarch64_sync_boundary_facts(
        &mut lines,
        "  ",
        "Verification AArch64 sync boundary facts",
        &report.verification.unsupported_ledger,
    );

    if !report.functions.is_empty() {
        lines.push("  Functions:".to_string());
    }
    for function in &report.functions {
        let range = function
            .address_range
            .as_ref()
            .map(|range| format!(" {}", range.range_display))
            .unwrap_or_default();
        lines.push(format!(
            "    {} @{}{} (trust: {:?})",
            function.name, function.entry_display, range, function.trust_level
        ));
        lines.push(format_binary_proof_grade_gate_line(
            "      Proof-grade gate",
            &function.proof_grade_gate,
        ));
        append_gate_rejection_details(
            &mut lines,
            "      ",
            &format!("function {}", function.name),
            &function.proof_grade_gate,
        );
        lines.push(format_unsupported_summary("      Unsupported ledger", &function.unsupported));
        append_aarch64_atomic_semantic_facts(
            &mut lines,
            "      ",
            "Function AArch64 atomic semantic facts",
            &function.unsupported,
        );
        append_aarch64_sync_boundary_facts(
            &mut lines,
            "      ",
            "Function AArch64 sync boundary facts",
            &function.unsupported,
        );
        lines.push(format_binary_verification_line("      Verification", &function.verification));
    }

    append_dispatch_details(&mut lines, "  ", &report.verification);

    lines.join("\n")
}

/// Format a binary verification summary as human-readable text.
#[must_use]
pub fn format_binary_verification_summary(
    summary: &trust_types::BinaryVerificationSummary,
) -> String {
    let report = build_binary_verification_report(summary);
    format_binary_verification_report(&report)
}

/// Format a report-friendly binary verification summary as human-readable text.
#[must_use]
pub fn format_binary_verification_report(report: &BinaryVerificationReport) -> String {
    let mut lines = Vec::new();
    lines.push(format_binary_verification_line("Binary verification", report));
    lines.push(format_binary_proof_grade_gate_line("Proof-grade gate", &report.proof_grade_gate));
    append_gate_rejection_details(&mut lines, "", "verification", &report.proof_grade_gate);
    lines.push(format_unresolved_blocker_summary(
        "Unresolved blockers",
        &report.unresolved_blockers,
    ));
    append_unresolved_blockers(&mut lines, "", &report.unresolved_blockers);
    lines.push(format_unsupported_summary("Unsupported ledger", &report.unsupported_ledger));
    append_aarch64_atomic_semantic_facts(
        &mut lines,
        "",
        "AArch64 atomic semantic facts",
        &report.unsupported_ledger,
    );
    append_aarch64_sync_boundary_facts(
        &mut lines,
        "",
        "AArch64 sync boundary facts",
        &report.unsupported_ledger,
    );
    append_dispatch_details(&mut lines, "", report);
    lines.join("\n")
}

impl BinaryLocationReport {
    /// Build a report location from shared binary origin metadata.
    #[must_use]
    pub fn from_origin(origin: &BinaryOrigin) -> Self {
        Self {
            binary_path: origin.binary_path.clone(),
            function_entry: origin.function_entry,
            function_entry_display: origin.function_entry.map(format_binary_address),
            instruction_address: origin.instruction_address,
            instruction_address_display: format_binary_address(origin.instruction_address),
            source: origin.span(),
        }
    }
}

impl BinaryAarch64AtomicSemanticFactReport {
    /// Build report metadata from a shared AArch64 atomic/exclusive semantic fact.
    #[must_use]
    pub fn from_fact(fact: &Aarch64AtomicSemanticFact) -> Self {
        Self {
            location: fact.origin.as_ref().map(BinaryLocationReport::from_origin),
            opcode: fact.opcode.clone(),
            operand: fact.operand.clone(),
            access: fact.access,
            ordering: fact.ordering,
            exclusive_monitor: fact.exclusive_monitor,
            reports_status: fact.reports_status,
            missing_witnesses: fact.missing_witnesses.clone(),
            consumed_by_proof_model: fact.consumed_by_proof_model,
            proof_grade_accepted: fact.proof_grade_gate_accepted(),
            proof_grade_rejection_reason: fact.proof_grade_rejection_reason(),
        }
    }
}

impl BinaryAarch64SyncBoundaryFactReport {
    /// Build report metadata from a shared AArch64 barrier/monitor-clear boundary fact.
    #[must_use]
    pub fn from_fact(fact: &Aarch64SyncBoundarySemanticFact) -> Self {
        Self {
            location: fact.origin.as_ref().map(BinaryLocationReport::from_origin),
            opcode: fact.opcode.clone(),
            operand: fact.operand.clone(),
            kind: fact.kind,
            scope: fact.scope,
            ordering: fact.ordering,
            clears_exclusive_monitor: fact.clears_exclusive_monitor,
            raw_option: fact.raw_option,
            missing_witnesses: fact.missing_witnesses.clone(),
            consumed_by_proof_model: fact.consumed_by_proof_model,
            proof_grade_accepted: fact.proof_grade_gate_accepted(),
            proof_grade_rejection_reason: fact.proof_grade_rejection_reason(),
        }
    }
}

impl BinaryInstructionProvenanceReport {
    /// Build report instruction provenance from shared binary origin metadata.
    #[must_use]
    pub fn from_origin(origin: &BinaryOrigin) -> Self {
        Self {
            binary_path: origin.binary_path.clone(),
            function_entry: origin.function_entry,
            function_entry_display: origin.function_entry.map(format_binary_address),
            instruction_address: origin.instruction_address,
            instruction_address_display: format_binary_address(origin.instruction_address),
            instruction_size: origin.instruction_size,
            encoding: origin.encoding,
            instruction_bytes: origin.instruction_bytes.clone(),
            source: origin.span(),
        }
    }
}

impl BinarySourceProvenanceReport {
    /// Build a report summary from the shared artifact provenance summary.
    #[must_use]
    pub fn from_summary(summary: &BinarySourceProvenanceSummary) -> Self {
        let source_backpropagation_allowed = summary.effective_source_backpropagation_allowed();
        Self {
            status: summary.status.clone(),
            exact_mapping_count: summary.exact_mapping_count,
            ambiguous_mapping_count: summary.ambiguous_mapping_count,
            diagnostics: summary.diagnostics.clone(),
            source_backpropagation_allowed,
            source_backpropagation_disabled_reasons: source_backpropagation_disabled_reasons(
                summary,
                source_backpropagation_allowed,
            ),
        }
    }

    /// True only when accepted exact debug/source mappings are present.
    #[must_use]
    pub fn has_exact_debug_source_provenance(&self) -> bool {
        self.status == "exact" && self.exact_mapping_count > 0
    }

    /// Effective source-backpropagation gate after fail-closed validation.
    #[must_use]
    pub fn effective_source_backpropagation_allowed(&self) -> bool {
        self.source_backpropagation_allowed && self.has_exact_debug_source_provenance()
    }

    /// Binary-address diagnostics remain available even when source backpropagation is closed.
    #[must_use]
    pub fn binary_address_diagnostics_allowed(&self) -> bool {
        true
    }

    /// Derived typed diagnostics for the provenance gate.
    #[must_use]
    pub fn typed_diagnostics(&self) -> Vec<BinarySourceProvenanceDiagnostic> {
        BinarySourceProvenanceSummary {
            status: self.status.clone(),
            exact_mapping_count: self.exact_mapping_count,
            ambiguous_mapping_count: self.ambiguous_mapping_count,
            diagnostics: self.diagnostics.clone(),
            source_backpropagation_allowed: self.source_backpropagation_allowed,
        }
        .typed_diagnostics()
    }
}

fn source_backpropagation_disabled_reasons(
    summary: &BinarySourceProvenanceSummary,
    effective_allowed: bool,
) -> Vec<String> {
    if effective_allowed {
        return Vec::new();
    }

    let mut reasons = Vec::new();
    if summary.status != "exact" {
        reasons.push(format!("source_provenance_status_not_exact:{}", summary.status));
    }
    if summary.exact_mapping_count == 0 {
        reasons.push("exact_source_mapping_missing".to_string());
    }
    if !summary.source_backpropagation_allowed {
        reasons.push("source_backpropagation_not_enabled_by_producer".to_string());
    }
    if reasons.is_empty() {
        reasons.push("source_backpropagation_effective_gate_closed".to_string());
    }
    reasons
}

impl BinaryReconstructionReport {
    /// Build a report summary from shared reconstruction output.
    #[must_use]
    pub fn from_summary(summary: &ReconstructionSummary) -> Self {
        let mut report = Self {
            target: summary.target.clone(),
            validation: summary.validation,
            trust_level: summary.trust_level,
            diagnostics: summary.diagnostics.clone(),
            validation_records: summary
                .validated_rust
                .as_ref()
                .map(|validated| validated.validation_records.clone())
                .unwrap_or_default(),
            output_count: summary.outputs.len(),
            ..Self::default()
        };

        for output in &summary.outputs {
            if !output.diagnostics.is_empty() {
                report
                    .output_diagnostics
                    .push(BinaryReconstructionOutputDiagnosticsReport::from_output(output));
            }
            report.validation_records.extend(output.validation_records.iter().cloned());
            let formula_consumer_blockers = symbolic_formula_consumer_blockers(output);
            if !output.preserved_symbolic_formulas.is_empty() {
                if formula_consumer_blockers.is_empty() {
                    if report.symbolic_formula_consumer_status != "blocked" {
                        report.symbolic_formula_consumer_status = "accepted".to_string();
                    }
                } else {
                    report.symbolic_formula_consumer_status = "blocked".to_string();
                    report
                        .symbolic_formula_consumer_blockers
                        .extend(formula_consumer_blockers.clone());
                }
            }

            for blocker in &output.target_validation_blockers {
                *report
                    .target_validation_blockers_by_stage
                    .entry(blocker.stage.clone())
                    .or_default() += 1;
                *report
                    .target_validation_blockers_by_feature
                    .entry(blocker.feature.clone())
                    .or_default() += 1;
                report
                    .target_validation_blockers
                    .push(BinaryTargetValidationBlockerReport::from_blocker(blocker));
            }

            report.preserved_symbolic_formulas.extend(
                output.preserved_symbolic_formulas.iter().map(|formula| {
                    BinaryPreservedSymbolicFormulaReport::from_formula_for_output(
                        formula,
                        output,
                        &formula_consumer_blockers,
                    )
                }),
            );
        }

        report.symbolic_formula_consumer_blockers.sort();
        report.symbolic_formula_consumer_blockers.dedup();
        report.target_validation_blocker_count = report.target_validation_blockers.len();
        report.preserved_symbolic_formula_count = report.preserved_symbolic_formulas.len();
        report
    }
}

impl BinaryReconstructionOutputDiagnosticsReport {
    /// Build output diagnostic metadata from a shared decompiled output.
    #[must_use]
    pub fn from_output(output: &DecompiledOutput) -> Self {
        Self {
            target: output.target.clone(),
            artifact_path: output.artifact_path.clone(),
            validation: output.validation,
            trust_level: output.trust_level,
            diagnostics: output.diagnostics.clone(),
        }
    }
}

impl BinaryTargetValidationBlockerReport {
    /// Build report blocker metadata from a shared target validation blocker.
    #[must_use]
    pub fn from_blocker(blocker: &TargetValidationBlocker) -> Self {
        Self {
            target: blocker.target.clone(),
            function: blocker.function.clone(),
            code: blocker.code.clone(),
            stage: blocker.stage.clone(),
            feature: blocker.feature.clone(),
            reason: blocker.reason.clone(),
            location: blocker.origin.as_ref().map(BinaryLocationReport::from_origin),
            diagnostics: blocker.diagnostics.clone(),
        }
    }
}

impl BinaryPreservedSymbolicFormulaReport {
    /// Build report formula metadata from a shared preserved symbolic formula.
    #[must_use]
    pub fn from_formula(formula: &PreservedSymbolicFormula) -> Self {
        Self::from_formula_with_consumer_status(
            formula,
            "missing",
            vec![
                "missing target proof consumer for preserved trust_symbolic.formula; schema-aware evidence required"
                    .to_string(),
            ],
        )
    }

    fn from_formula_for_output(
        formula: &PreservedSymbolicFormula,
        output: &DecompiledOutput,
        output_blockers: &[String],
    ) -> Self {
        if output_symbolic_formulas_consumed_by_proof_model(output) {
            Self::from_formula_with_consumer_status(formula, "accepted", Vec::new())
        } else {
            let blockers = if output_blockers.is_empty() {
                vec![
                    "missing target proof consumer for preserved trust_symbolic.formula; schema-aware evidence required"
                        .to_string(),
                ]
            } else {
                output_blockers.to_vec()
            };
            Self::from_formula_with_consumer_status(formula, "blocked", blockers)
        }
    }

    fn from_formula_with_consumer_status(
        formula: &PreservedSymbolicFormula,
        proof_consumer_status: &str,
        proof_consumer_blockers: Vec<String>,
    ) -> Self {
        let formula_evidence = formula.evidence();
        let formula_sort = strict_formula_sort(&formula.formula);
        let smtlib_sort = formula_sort.as_ref().map(Sort::to_smtlib).unwrap_or_default();
        let sort_declarations = collect_formula_sort_declarations(&formula.formula);
        let proof_consumer_obligations = symbolic_formula_required_evidence(formula)
            .into_iter()
            .map(|requirement| requirement.label)
            .collect();

        Self {
            target: formula.target.clone(),
            function: formula.function.clone(),
            block: formula.block,
            statement_index: formula.statement_index,
            location: formula.location.clone(),
            formula_evidence: formula_evidence.clone(),
            formula: formula.formula.clone(),
            formula_schema: formula_evidence.schema,
            formula_digest: formula_evidence.digest,
            formula_origin: formula_evidence.origin,
            smtlib: formula.formula.to_smtlib(),
            formula_sort,
            smtlib_sort,
            debug: format!("{:?}", formula.formula),
            sort_declarations,
            proof_consumer_obligations,
            proof_consumer_required: true,
            proof_consumer_status: proof_consumer_status.to_string(),
            proof_consumer_blockers,
        }
    }
}

fn collect_formula_sort_declarations(
    formula: &Formula,
) -> Vec<BinaryVcFormulaSortDeclarationReport> {
    collect_free_var_decls(formula)
        .into_iter()
        .map(|(name, sort)| {
            let smtlib_sort = sort.to_smtlib();
            BinaryVcFormulaSortDeclarationReport {
                smtlib_declaration: format!("(declare-fun {name} () {smtlib_sort})"),
                name,
                sort,
                smtlib_sort,
            }
        })
        .collect()
}

fn strict_formula_sort(formula: &Formula) -> Option<Sort> {
    match formula {
        Formula::Bool(_) => Some(Sort::Bool),
        Formula::Int(_) | Formula::UInt(_) => Some(Sort::Int),
        Formula::BitVec { width, .. } => Some(Sort::BitVec(*width)),
        Formula::Var(_, sort) | Formula::SymVar(_, sort) => Some(sort.clone()),
        Formula::Not(inner) => {
            matches!(strict_formula_sort(inner)?, Sort::Bool).then_some(Sort::Bool)
        }
        Formula::And(terms) | Formula::Or(terms) => terms
            .iter()
            .all(|term| matches!(strict_formula_sort(term), Some(Sort::Bool)))
            .then_some(Sort::Bool),
        Formula::Implies(lhs, rhs) => (matches!(strict_formula_sort(lhs)?, Sort::Bool)
            && matches!(strict_formula_sort(rhs)?, Sort::Bool))
        .then_some(Sort::Bool),
        Formula::Eq(lhs, rhs) => {
            (strict_formula_sort(lhs)? == strict_formula_sort(rhs)?).then_some(Sort::Bool)
        }
        Formula::Lt(lhs, rhs)
        | Formula::Le(lhs, rhs)
        | Formula::Gt(lhs, rhs)
        | Formula::Ge(lhs, rhs) => (strict_formula_sort(lhs)? == Sort::Int
            && strict_formula_sort(rhs)? == Sort::Int)
            .then_some(Sort::Bool),
        Formula::Add(lhs, rhs)
        | Formula::Sub(lhs, rhs)
        | Formula::Mul(lhs, rhs)
        | Formula::Div(lhs, rhs)
        | Formula::Rem(lhs, rhs) => (strict_formula_sort(lhs)? == Sort::Int
            && strict_formula_sort(rhs)? == Sort::Int)
            .then_some(Sort::Int),
        Formula::Neg(inner) => (strict_formula_sort(inner)? == Sort::Int).then_some(Sort::Int),
        Formula::BvAdd(lhs, rhs, width)
        | Formula::BvSub(lhs, rhs, width)
        | Formula::BvMul(lhs, rhs, width)
        | Formula::BvUDiv(lhs, rhs, width)
        | Formula::BvSDiv(lhs, rhs, width)
        | Formula::BvURem(lhs, rhs, width)
        | Formula::BvSRem(lhs, rhs, width)
        | Formula::BvAnd(lhs, rhs, width)
        | Formula::BvOr(lhs, rhs, width)
        | Formula::BvXor(lhs, rhs, width)
        | Formula::BvShl(lhs, rhs, width)
        | Formula::BvLShr(lhs, rhs, width)
        | Formula::BvAShr(lhs, rhs, width) => (strict_formula_sort(lhs)? == Sort::BitVec(*width)
            && strict_formula_sort(rhs)? == Sort::BitVec(*width))
        .then_some(Sort::BitVec(*width)),
        Formula::BvNot(inner, width) => {
            (strict_formula_sort(inner)? == Sort::BitVec(*width)).then_some(Sort::BitVec(*width))
        }
        Formula::BvULt(lhs, rhs, width)
        | Formula::BvULe(lhs, rhs, width)
        | Formula::BvSLt(lhs, rhs, width)
        | Formula::BvSLe(lhs, rhs, width) => (strict_formula_sort(lhs)? == Sort::BitVec(*width)
            && strict_formula_sort(rhs)? == Sort::BitVec(*width))
        .then_some(Sort::Bool),
        Formula::BvToInt(inner, width, _) => {
            (strict_formula_sort(inner)? == Sort::BitVec(*width)).then_some(Sort::Int)
        }
        Formula::IntToBv(inner, width) => {
            (strict_formula_sort(inner)? == Sort::Int).then_some(Sort::BitVec(*width))
        }
        Formula::BvExtract { inner, high, low } => {
            let Sort::BitVec(width) = strict_formula_sort(inner)? else {
                return None;
            };
            (*low <= *high && *high < width).then_some(Sort::BitVec(high - low + 1))
        }
        Formula::BvConcat(lhs, rhs) => {
            let Sort::BitVec(lhs_width) = strict_formula_sort(lhs)? else {
                return None;
            };
            let Sort::BitVec(rhs_width) = strict_formula_sort(rhs)? else {
                return None;
            };
            Some(Sort::BitVec(lhs_width.saturating_add(rhs_width)))
        }
        Formula::BvZeroExt(inner, extra) | Formula::BvSignExt(inner, extra) => {
            let Sort::BitVec(width) = strict_formula_sort(inner)? else {
                return None;
            };
            Some(Sort::BitVec(width.saturating_add(*extra)))
        }
        Formula::Ite(cond, then_formula, else_formula) => {
            if strict_formula_sort(cond)? != Sort::Bool {
                return None;
            }
            let then_sort = strict_formula_sort(then_formula)?;
            (then_sort == strict_formula_sort(else_formula)?).then_some(then_sort)
        }
        Formula::Forall(_, _) | Formula::Exists(_, _) => Some(Sort::Bool),
        Formula::Select(array, index) => {
            let Sort::Array(index_sort, elem_sort) = strict_formula_sort(array)? else {
                return None;
            };
            (index_sort.as_ref() == &strict_formula_sort(index)?).then_some(*elem_sort)
        }
        Formula::Store(array, index, value) => {
            let array_sort = strict_formula_sort(array)?;
            let Sort::Array(index_sort, elem_sort) = &array_sort else {
                return None;
            };
            (index_sort.as_ref() == &strict_formula_sort(index)?
                && elem_sort.as_ref() == &strict_formula_sort(value)?)
                .then_some(array_sort)
        }
        #[allow(unreachable_patterns)]
        _ => None,
    }
}

impl BinaryVcFormulaSummaryReport {
    /// Build a stable report summary from a serialized VC.
    #[must_use]
    pub fn from_vc(vc: &SerializableVc) -> Self {
        let mut node_count = 0;
        vc.formula.visit(&mut |_| {
            node_count += 1;
        });
        let mut free_variables = vc.formula.free_variables().into_iter().collect::<Vec<_>>();
        free_variables.sort();
        let sort_declarations = collect_formula_sort_declarations(&vc.formula);

        Self {
            kind: vc.kind.to_string(),
            function: vc.function.as_str().to_string(),
            location: vc.location.clone(),
            smtlib: vc.formula.to_smtlib(),
            debug: format!("{:?}", vc.formula),
            node_count,
            free_variables,
            sort_declarations,
            has_bitvectors: vc.formula.has_bitvectors(),
            has_arrays: vc.formula.has_arrays(),
        }
    }
}

impl BinaryAddressRangeReport {
    /// Build a report address range from a shared binary address range.
    #[must_use]
    pub fn from_range(range: BinaryAddressRange) -> Self {
        let range_display = format!(
            "[{}, {})",
            format_binary_address(range.start),
            format_binary_address(range.end)
        );
        Self { start: range.start, end: range.end, range_display }
    }
}

impl BinaryDigestIdentityReport {
    /// Build report digest identity from shared binary metadata.
    #[must_use]
    pub fn from_metadata(metadata: &BinaryArtifactMetadata) -> Self {
        let blockers = metadata.digest_identity_blockers();
        Self {
            proof_grade_ready: blockers.is_empty(),
            root_artifact_byte_len: metadata.byte_len,
            root_artifact_digest: metadata.root_artifact_digest.clone(),
            selected_image: metadata
                .selected_image
                .as_ref()
                .map(BinarySelectedImageIdentityReport::from_identity),
            blockers,
        }
    }
}

impl BinarySelectedImageIdentityReport {
    /// Build report selected-image identity from shared binary metadata.
    #[must_use]
    pub fn from_identity(identity: &BinarySelectedImageIdentity) -> Self {
        Self {
            file_offset: identity.file_offset,
            file_size: identity.file_size,
            end_offset: identity.end_offset(),
            sha256: identity.sha256.clone(),
        }
    }
}

fn build_decompilation_unresolved_blocker_ledger(
    gate: &BinaryProofGradeGateReport,
    digest_identity: &BinaryDigestIdentityReport,
    unsupported_ledger: &UnsupportedLedger,
    source_provenance: &BinarySourceProvenanceReport,
    source_backpropagation_gate: &BinarySourceBackpropagationGateReport,
    reconstruction: &BinaryReconstructionReport,
    verification: &BinaryVerificationReport,
) -> BinaryUnresolvedBlockerLedgerReport {
    let mut entries = Vec::new();
    push_gate_rejection_blockers(&mut entries, gate);
    for blocker in &digest_identity.blockers {
        push_blocker(
            &mut entries,
            "digest_identity",
            Some("binary_metadata"),
            "digest_identity_not_exact",
            blocker.clone(),
            None,
            None,
        );
    }
    push_unsupported_record_blockers(&mut entries, unsupported_ledger);
    if !source_provenance.effective_source_backpropagation_allowed() {
        push_blocker(
            &mut entries,
            "source_provenance",
            Some("source_provenance"),
            SOURCE_BACKPROPAGATION_EXACT_SOURCE_PROVENANCE,
            format!(
                "source provenance status={} exact_mapping_count={}",
                source_provenance.status, source_provenance.exact_mapping_count
            ),
            None,
            None,
        );
    }
    for blocker in &source_backpropagation_gate.blockers {
        push_blocker(
            &mut entries,
            "source_backpropagation_gate",
            Some(blocker.stage.clone()),
            blocker.label.clone(),
            blocker.detail.clone(),
            None,
            None,
        );
    }
    for blocker in &reconstruction.target_validation_blockers {
        push_blocker(
            &mut entries,
            "reconstruction",
            Some(blocker.stage.clone()),
            blocker.feature.clone(),
            blocker.reason.clone(),
            None,
            blocker.location.clone(),
        );
    }
    entries.extend(verification.unresolved_blockers.entries.iter().cloned());
    BinaryUnresolvedBlockerLedgerReport::from_entries(entries)
}

fn build_verification_unresolved_blocker_ledger(
    gate: &BinaryProofGradeGateReport,
    unsupported_ledger: &UnsupportedLedger,
    certificate_checks: &BinaryCertificateCheckReport,
    dispatches: &[BinarySolverDispatchReport],
) -> BinaryUnresolvedBlockerLedgerReport {
    let mut entries = Vec::new();
    push_gate_rejection_blockers(&mut entries, gate);
    push_unsupported_record_blockers(&mut entries, unsupported_ledger);
    for blocker in &certificate_checks.production_manifest.release_blockers {
        push_blocker(
            &mut entries,
            "production_manifest",
            Some("certificate"),
            "checked_certificate_production_manifest",
            blocker.clone(),
            None,
            None,
        );
    }
    for dispatch in dispatches {
        if let Some(release_blocker) = &dispatch.timeout_evidence.release_blocker {
            push_blocker(
                &mut entries,
                "timeout_evidence",
                Some("solver"),
                "timeout_policy",
                release_blocker.clone(),
                Some(dispatch.id.clone()),
                dispatch.location.clone(),
            );
        }
        match &dispatch.production_checker_evidence {
            ProofCertificateProductionCheckerEvidenceStatus::Missing
                if dispatch.certificate_checked =>
            {
                push_blocker(
                    &mut entries,
                    "production_manifest",
                    Some("certificate"),
                    "missing_production_checker_evidence",
                    "checked certificate is missing production checker evidence".to_string(),
                    Some(dispatch.id.clone()),
                    dispatch.location.clone(),
                );
            }
            ProofCertificateProductionCheckerEvidenceStatus::Malformed { reason } => {
                push_blocker(
                    &mut entries,
                    "production_manifest",
                    Some("certificate"),
                    "malformed_production_checker_evidence",
                    reason.clone(),
                    Some(dispatch.id.clone()),
                    dispatch.location.clone(),
                );
            }
            ProofCertificateProductionCheckerEvidenceStatus::Missing
            | ProofCertificateProductionCheckerEvidenceStatus::Present { .. } => {}
        }
        for attempt in &dispatch.fallback_attempts {
            if let Some(release_blocker) = &attempt.release_blocker {
                push_blocker(
                    &mut entries,
                    "fallback_attempt",
                    Some("router"),
                    "fallback_attempt_release_blocker",
                    release_blocker.clone(),
                    Some(dispatch.id.clone()),
                    dispatch.location.clone(),
                );
            }
        }
        for blocker in &dispatch.replay_digest_identity.blockers {
            push_blocker(
                &mut entries,
                "replay_digest_identity",
                Some("replay"),
                "replay_artifact_digest_identity_not_exact",
                blocker.clone(),
                Some(dispatch.id.clone()),
                dispatch.location.clone(),
            );
        }
        for evidence in &dispatch.replay_boundary_evidence {
            if let Some(reason) = &evidence.proof_grade_rejection_reason {
                push_blocker(
                    &mut entries,
                    "replay_boundary",
                    Some("replay"),
                    format!("{}_boundary_semantics", evidence.kind),
                    reason.clone(),
                    Some(dispatch.id.clone()),
                    dispatch.location.clone(),
                );
            }
        }
    }
    BinaryUnresolvedBlockerLedgerReport::from_entries(entries)
}

impl BinaryUnresolvedBlockerLedgerReport {
    fn from_entries(entries: Vec<BinaryUnresolvedBlockerReport>) -> Self {
        let mut by_family = BTreeMap::new();
        for entry in &entries {
            *by_family.entry(entry.family.clone()).or_default() += 1;
        }
        Self { total_blockers: entries.len(), by_family, entries }
    }
}

fn push_gate_rejection_blockers(
    entries: &mut Vec<BinaryUnresolvedBlockerReport>,
    gate: &BinaryProofGradeGateReport,
) {
    for rejection in &gate.rejections {
        push_blocker(
            entries,
            gate_rejection_family(rejection),
            Some("proof_grade_gate"),
            gate_rejection_feature(rejection),
            format_gate_rejection(rejection),
            None,
            None,
        );
    }
}

fn push_unsupported_record_blockers(
    entries: &mut Vec<BinaryUnresolvedBlockerReport>,
    unsupported_ledger: &UnsupportedLedger,
) {
    for record in &unsupported_ledger.records {
        push_blocker(
            entries,
            "unsupported_ledger",
            Some(record.stage.clone()),
            record.feature.clone(),
            record
                .opcode
                .as_ref()
                .map(|opcode| format!("unsupported {} opcode {opcode}", record.feature))
                .unwrap_or_else(|| format!("unsupported {}", record.feature)),
            None,
            record.origin.as_ref().map(BinaryLocationReport::from_origin),
        );
    }
}

fn push_blocker(
    entries: &mut Vec<BinaryUnresolvedBlockerReport>,
    family: impl Into<String>,
    stage: Option<impl Into<String>>,
    feature: impl Into<String>,
    reason: impl Into<String>,
    dispatch_id: Option<String>,
    location: Option<BinaryLocationReport>,
) {
    entries.push(BinaryUnresolvedBlockerReport {
        family: family.into(),
        stage: stage.map(Into::into),
        feature: feature.into(),
        reason: reason.into(),
        dispatch_id,
        location,
    });
}

fn build_binary_function_report(function: &DecompiledFunction) -> BinaryFunctionReport {
    let function_unsupported = combined_unsupported_ledger(
        &function.unsupported,
        &function.verification.unsupported_ledger,
    );
    BinaryFunctionReport {
        name: function.name.clone(),
        entry: function.entry,
        entry_display: format_binary_address(function.entry),
        address_range: function.address_range.map(BinaryAddressRangeReport::from_range),
        location: function.origin.as_ref().map(BinaryLocationReport::from_origin),
        instruction_provenance: function
            .instruction_provenance
            .iter()
            .map(BinaryInstructionProvenanceReport::from_origin)
            .collect(),
        trust_level: function.trust_level,
        proof_grade_gate: build_binary_function_proof_grade_gate_report(function),
        unsupported: build_binary_unsupported_ledger_report(&function.unsupported),
        verification: build_binary_verification_report_with_gate(
            &function.verification,
            function.trust_level,
            &function_unsupported,
        ),
    }
}

fn build_solver_dispatch_report(dispatch: &SolverDispatchRecord) -> BinarySolverDispatchReport {
    BinarySolverDispatchReport {
        id: dispatch.id.clone(),
        function: dispatch.function.clone(),
        location: dispatch.origin.as_ref().map(BinaryLocationReport::from_origin),
        solver: dispatch.solver.clone(),
        status: dispatch.status,
        vc_kind: dispatch
            .vc
            .as_ref()
            .map(|vc| vc.kind.to_string())
            .or_else(|| dispatch.vc_kind.as_ref().map(ToString::to_string)),
        vc_formula: dispatch.vc.as_ref().map(BinaryVcFormulaSummaryReport::from_vc),
        query_semantics: dispatch.query_semantics,
        result_status: dispatch.result.as_ref().map(verification_result_status),
        timeout_evidence: build_solver_timeout_evidence_report(dispatch),
        fallback_attempts: dispatch.fallback_attempts.clone(),
        diagnostics: dispatch.diagnostics.clone(),
        replay_digest_identity: BinaryReplayDigestIdentityReport::from_dispatch(dispatch),
        replay_boundary_evidence: extract_replay_boundary_evidence(&dispatch.diagnostics),
        certificate: dispatch.certificate.clone(),
        checked_certificate_identity: BinaryCheckedCertificateIdentityReport::from_dispatch(
            dispatch,
        ),
        certificate_checked: dispatch_has_checked_certificate_identity(dispatch),
        production_checker_evidence: dispatch.certificate.production_checker_evidence_status(),
        production_checked: dispatch_has_production_checked_certificate_identity(dispatch),
        raw_solver_proof_bytes: raw_solver_result_has_certificate_bytes(dispatch.result.as_ref()),
        raw_solver_proof_byte_count: raw_solver_result_certificate_byte_count(
            dispatch.result.as_ref(),
        ),
        replay: dispatch.replay,
    }
}

const EXACT_BOUNDARY_SEMANTICS_WITNESS: &str = "exact_boundary_semantics_witness";

fn extract_replay_boundary_evidence(
    diagnostics: &[String],
) -> Vec<BinaryReplayBoundaryEvidenceReport> {
    diagnostics
        .iter()
        .flat_map(|diagnostic| extract_replay_boundary_evidence_from_diagnostic(diagnostic))
        .collect()
}

fn extract_replay_boundary_evidence_from_diagnostic(
    diagnostic: &str,
) -> Vec<BinaryReplayBoundaryEvidenceReport> {
    let trimmed = diagnostic.trim();
    let mut evidence = Vec::new();

    if let Ok(value) = serde_json::from_str::<serde_json::Value>(trimmed) {
        append_replay_boundary_evidence_from_value(&value, &mut evidence);
    }

    for prefix in [
        "replay_boundary_evidence=",
        "replay_boundary_evidence:",
        "machine_replay.boundary_evidence=",
        "machine_replay.boundary_evidence:",
        "boundary_evidence=",
        "boundary_evidence:",
    ] {
        if let Some(index) = trimmed.find(prefix) {
            let payload = trimmed[index + prefix.len()..].trim();
            if let Ok(value) = serde_json::from_str::<serde_json::Value>(payload) {
                append_replay_boundary_evidence_from_value(&value, &mut evidence);
                break;
            }
        }
    }

    evidence
}

fn append_replay_boundary_evidence_from_value(
    value: &serde_json::Value,
    evidence: &mut Vec<BinaryReplayBoundaryEvidenceReport>,
) {
    match value {
        serde_json::Value::Array(values) => {
            for value in values {
                append_replay_boundary_evidence_from_value(value, evidence);
            }
        }
        serde_json::Value::Object(map) if map.contains_key("kind") => {
            if let Some(report) = replay_boundary_evidence_from_value(value) {
                evidence.push(report);
            }
        }
        serde_json::Value::Object(map) => {
            for key in
                ["boundary_evidence", "replay_boundary_evidence", "machine_replay", "replay_report"]
            {
                if let Some(value) = map.get(key) {
                    append_replay_boundary_evidence_from_value(value, evidence);
                }
            }
        }
        _ => {}
    }
}

fn replay_boundary_evidence_from_value(
    value: &serde_json::Value,
) -> Option<BinaryReplayBoundaryEvidenceReport> {
    let kind = json_string(value, "kind")?;
    let architecture = json_string(value, "architecture")?;
    let instruction_address =
        json_u64(value, "instruction_address").or_else(|| json_u64(value, "address"))?;
    let step = json_u64(value, "step").and_then(|step| u32::try_from(step).ok());
    let instruction_bytes = json_bytes(value, "instruction_bytes");
    let opcode = json_string(value, "opcode").unwrap_or_default();
    let encoding = json_u64(value, "encoding")
        .and_then(|encoding| u32::try_from(encoding).ok())
        .unwrap_or_default();
    let immediate = json_u64(value, "immediate");
    let semantics = json_string(value, "semantics")?;
    let diagnostic = json_string(value, "diagnostic").unwrap_or_default();
    let instruction_address_display = format_binary_address(instruction_address);
    let instruction_bytes_hex = format_hex_bytes(&instruction_bytes);
    let proof_grade_rejection_reason = replay_boundary_rejection_reason(
        &kind,
        &architecture,
        instruction_address,
        step,
        &instruction_bytes,
        &semantics,
    );
    let proof_grade_accepted = proof_grade_rejection_reason.is_none();

    Some(BinaryReplayBoundaryEvidenceReport {
        kind,
        architecture,
        instruction_address,
        instruction_address_display,
        step,
        instruction_bytes,
        instruction_bytes_hex,
        opcode,
        encoding,
        immediate,
        semantics,
        diagnostic,
        proof_grade_accepted,
        proof_grade_rejection_reason,
    })
}

fn replay_boundary_rejection_reason(
    kind: &str,
    architecture: &str,
    instruction_address: u64,
    step: Option<u32>,
    instruction_bytes: &[u8],
    semantics: &str,
) -> Option<String> {
    let mut blockers = Vec::new();
    if semantics != EXACT_BOUNDARY_SEMANTICS_WITNESS {
        blockers.push(format!("missing exact boundary semantics witness (semantics={semantics})"));
    }
    if architecture.is_empty() {
        blockers.push("missing architecture binding".to_string());
    }
    if step.is_none() {
        blockers.push("missing replay step binding".to_string());
    }
    if instruction_bytes.is_empty() {
        blockers.push("missing instruction byte binding".to_string());
    }

    if blockers.is_empty() {
        None
    } else {
        Some(format!(
            "replay boundary kind={kind} at {} is not proof-grade: {}",
            format_binary_address(instruction_address),
            blockers.join("; ")
        ))
    }
}

fn json_string(value: &serde_json::Value, key: &str) -> Option<String> {
    value.get(key)?.as_str().map(ToString::to_string)
}

fn json_u64(value: &serde_json::Value, key: &str) -> Option<u64> {
    let value = value.get(key)?;
    if let Some(number) = value.as_u64() {
        return Some(number);
    }
    let text = value.as_str()?.trim();
    let hex = text.strip_prefix("0x").or_else(|| text.strip_prefix("0X"));
    hex.map_or_else(|| text.parse::<u64>().ok(), |hex| u64::from_str_radix(hex, 16).ok())
}

fn json_bytes(value: &serde_json::Value, key: &str) -> Vec<u8> {
    let Some(value) = value.get(key) else {
        return Vec::new();
    };
    if let Some(values) = value.as_array() {
        return values
            .iter()
            .filter_map(|value| value.as_u64().and_then(|byte| u8::try_from(byte).ok()))
            .collect();
    }
    let Some(text) = value.as_str() else {
        return Vec::new();
    };
    text.split(|ch: char| ch.is_ascii_whitespace() || ch == ',' || ch == ':' || ch == '-')
        .filter(|part| !part.is_empty())
        .filter_map(|part| {
            let hex = part.strip_prefix("0x").or_else(|| part.strip_prefix("0X")).unwrap_or(part);
            u8::from_str_radix(hex, 16).ok()
        })
        .collect()
}

fn format_hex_bytes(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect::<Vec<_>>().join(" ")
}

impl BinaryReplayDigestIdentityReport {
    fn from_dispatch(dispatch: &SolverDispatchRecord) -> Self {
        let required = dispatch.replay == ReplayStatus::Replayed;
        let identity = dispatch.replay_artifact_digest_identity().cloned();
        let root_artifact_digest =
            identity.as_ref().and_then(|identity| identity.root_artifact_digest.clone());
        let selected_image_identity = identity
            .as_ref()
            .and_then(|identity| identity.selected_image.as_ref())
            .map(BinarySelectedImageIdentityReport::from_identity);
        let blockers = if required || identity.is_some() {
            dispatch.replay_digest_identity_blockers()
        } else {
            Vec::new()
        };
        Self {
            required,
            proof_grade_ready: blockers.is_empty(),
            identity,
            root_artifact_digest,
            selected_image_identity,
            blockers,
        }
    }
}

impl BinaryCheckedCertificateIdentityReport {
    fn from_dispatch(dispatch: &SolverDispatchRecord) -> Self {
        let required = dispatch_proves_required_vc(dispatch);
        let production_checker_evidence = dispatch.certificate.production_checker_evidence_status();
        let production_checked = production_checker_evidence.is_present();
        let checked_identity_ready = dispatch_has_checked_certificate_identity(dispatch);
        let mut report = Self {
            required,
            checked_identity_ready,
            proof_grade_ready: checked_identity_ready && production_checked,
            status: proof_certificate_status_label(&dispatch.certificate).to_string(),
            production_checker_evidence,
            production_checked,
            ..Self::default()
        };

        match &dispatch.certificate {
            ProofCertificateStatus::Checked { checker, format, sha256 } => {
                report.checker = Some(checker.clone());
                report.format = Some(format.clone());
                report.sha256 = sha256.clone();
                report.blockers.extend(checked_certificate_identity_blockers(
                    checker,
                    format,
                    sha256.as_deref(),
                ));
                if !report.production_checked {
                    match &report.production_checker_evidence {
                        ProofCertificateProductionCheckerEvidenceStatus::Malformed { reason } => {
                            report
                                .blockers
                                .push(format!("production checker evidence malformed: {reason}"));
                        }
                        ProofCertificateProductionCheckerEvidenceStatus::Missing => {
                            report.blockers.push("production checker evidence missing".to_string());
                        }
                        ProofCertificateProductionCheckerEvidenceStatus::Present { .. } => {}
                    }
                }
            }
            ProofCertificateStatus::Present { format, sha256, artifact_path } => {
                report.format = Some(format.clone());
                report.sha256 = sha256.clone();
                report.artifact_path = artifact_path.clone();
                if structural_manifest_candidate_present(&dispatch.certificate) {
                    report.blockers.push(
                        "structural checked-certificate manifest candidate is not an independently checked certificate identity"
                            .to_string(),
                    );
                } else if required {
                    report
                        .blockers
                        .push("unchecked certificate candidate is not proof-grade".to_string());
                }
            }
            ProofCertificateStatus::Rejected { checker, reason } => {
                report.checker = checker.clone();
                report.blockers.push(format!("checked certificate rejected: {reason}"));
            }
            ProofCertificateStatus::Unavailable { reason } => {
                report.blockers.push(
                    reason
                        .as_ref()
                        .map(|reason| format!("checked certificate unavailable: {reason}"))
                        .unwrap_or_else(|| "checked certificate unavailable".to_string()),
                );
            }
            ProofCertificateStatus::NotRequested => {
                if required {
                    report.blockers.push("checked certificate not requested".to_string());
                }
            }
            _ => {
                if required {
                    report
                        .blockers
                        .push("checked certificate status is not proof-grade".to_string());
                }
            }
        }

        if !required {
            report.blockers.clear();
            report.proof_grade_ready = false;
        }
        report
    }
}

fn build_solver_timeout_evidence_report(
    dispatch: &SolverDispatchRecord,
) -> BinarySolverTimeoutEvidenceReport {
    if let Some(evidence) = &dispatch.timeout_evidence {
        return BinarySolverTimeoutEvidenceReport::from_shared(evidence, &dispatch.id);
    }
    if let Some(evidence) =
        SolverTimeoutEvidence::from_fallback_attempts(&dispatch.fallback_attempts)
    {
        return BinarySolverTimeoutEvidenceReport::from_shared(&evidence, &dispatch.id);
    }

    let planned_timeout_ms = dispatch.timeout_ms;
    let backend_reported_timeout_ms = dispatch.result.as_ref().and_then(|result| match result {
        VerificationResult::Timeout { timeout_ms, .. } => Some(*timeout_ms),
        _ => None,
    });

    let (status, release_blocker) = match (planned_timeout_ms, backend_reported_timeout_ms) {
        (None, None) => (
            BinarySolverTimeoutEvidenceStatus::MissingTimeoutPolicy,
            Some(format!("missing per-VC timeout policy for solver dispatch {}", dispatch.id)),
        ),
        (None, Some(reported)) => (
            BinarySolverTimeoutEvidenceStatus::BackendTimeoutWithoutPlannedPolicy,
            Some(format!(
                "backend reported timeout {reported}ms for solver dispatch {} but no per-VC timeout policy was recorded",
                dispatch.id
            )),
        ),
        (Some(planned), None) => (
            BinarySolverTimeoutEvidenceStatus::MissingBackendAttestation,
            Some(format!(
                "planned timeout {planned}ms for solver dispatch {} was not attested by backend result",
                dispatch.id
            )),
        ),
        (Some(planned), Some(reported)) if planned == reported => {
            (BinarySolverTimeoutEvidenceStatus::Matched, None)
        }
        (Some(planned), Some(reported)) => (
            BinarySolverTimeoutEvidenceStatus::Mismatched,
            Some(format!(
                "planned timeout {planned}ms for solver dispatch {} differs from backend-reported {reported}ms",
                dispatch.id
            )),
        ),
    };

    BinarySolverTimeoutEvidenceReport {
        planned_timeout_ms,
        backend_reported_timeout_ms,
        status,
        release_blocker,
    }
}

impl BinarySolverTimeoutEvidenceReport {
    fn from_shared(evidence: &SolverTimeoutEvidence, dispatch_id: &str) -> Self {
        let status = match evidence.status {
            SolverTimeoutEvidenceStatus::NotApplicable => {
                BinarySolverTimeoutEvidenceStatus::MissingTimeoutPolicy
            }
            SolverTimeoutEvidenceStatus::PolicyRecorded => {
                BinarySolverTimeoutEvidenceStatus::PolicyRecorded
            }
            SolverTimeoutEvidenceStatus::Matched => BinarySolverTimeoutEvidenceStatus::Matched,
            SolverTimeoutEvidenceStatus::MissingPolicyAttestation => {
                BinarySolverTimeoutEvidenceStatus::BackendTimeoutWithoutPlannedPolicy
            }
            SolverTimeoutEvidenceStatus::PolicyMismatch => {
                BinarySolverTimeoutEvidenceStatus::Mismatched
            }
            _ => BinarySolverTimeoutEvidenceStatus::MissingTimeoutPolicy,
        };
        let release_blocker = evidence.release_blocker.clone().or_else(|| match status {
            BinarySolverTimeoutEvidenceStatus::MissingTimeoutPolicy => Some(format!(
                "missing per-VC timeout policy for solver dispatch {dispatch_id}"
            )),
            BinarySolverTimeoutEvidenceStatus::BackendTimeoutWithoutPlannedPolicy => Some(
                format!(
                    "backend reported timeout for solver dispatch {dispatch_id} but no per-VC timeout policy was recorded"
                ),
            ),
            BinarySolverTimeoutEvidenceStatus::Mismatched => Some(format!(
                "planned timeout for solver dispatch {dispatch_id} differs from backend-reported timeout"
            )),
            BinarySolverTimeoutEvidenceStatus::PolicyRecorded
            | BinarySolverTimeoutEvidenceStatus::MissingBackendAttestation
            | BinarySolverTimeoutEvidenceStatus::Matched => None,
        });

        Self {
            planned_timeout_ms: evidence.planned_timeout_ms,
            backend_reported_timeout_ms: evidence.backend_timeout_ms,
            status,
            release_blocker,
        }
    }
}

fn build_certificate_check_report(
    summary: &BinaryVerificationSummary,
) -> BinaryCertificateCheckReport {
    let mut certificate_candidates = 0;
    let mut structural_manifest_candidates = 0;
    let mut checked_certificates = 0;
    let mut production_checked_certificates = 0;
    let mut malformed_production_evidence = 0;
    let mut rejected_certificates = 0;
    let mut raw_solver_proof_bytes = 0;
    let mut raw_solver_proof_byte_count = 0;
    let mut checked_certificate_identity_blockers = Vec::new();

    for dispatch in &summary.solver_dispatch {
        let raw_bytes = raw_solver_result_has_certificate_bytes(dispatch.result.as_ref());
        raw_solver_proof_byte_count +=
            raw_solver_result_certificate_byte_count(dispatch.result.as_ref());
        if certificate_candidate_present(&dispatch.certificate) || raw_bytes {
            certificate_candidates += 1;
        }
        if structural_manifest_candidate_present(&dispatch.certificate) {
            structural_manifest_candidates += 1;
        }
        let identity = BinaryCheckedCertificateIdentityReport::from_dispatch(dispatch);
        checked_certificate_identity_blockers
            .extend(identity.blockers.iter().map(|blocker| format!("{}: {blocker}", dispatch.id)));
        if dispatch_proves_required_vc(dispatch)
            && dispatch_has_checked_certificate_identity(dispatch)
        {
            checked_certificates += 1;
            match dispatch.certificate.production_checker_evidence_status() {
                ProofCertificateProductionCheckerEvidenceStatus::Present { .. } => {
                    production_checked_certificates += 1;
                }
                ProofCertificateProductionCheckerEvidenceStatus::Malformed { .. } => {
                    malformed_production_evidence += 1;
                }
                ProofCertificateProductionCheckerEvidenceStatus::Missing => {}
            }
        }
        if matches!(dispatch.certificate, ProofCertificateStatus::Rejected { .. }) {
            rejected_certificates += 1;
        }
        if raw_bytes {
            raw_solver_proof_bytes += 1;
        }
    }

    let production_manifest = build_certificate_production_manifest_report(
        summary.total_vcs,
        summary.solver_dispatch.len(),
        checked_certificates,
        production_checked_certificates,
        malformed_production_evidence,
    );

    BinaryCertificateCheckReport {
        required_vcs: summary.total_vcs,
        solver_dispatches: summary.solver_dispatch.len(),
        certificate_candidates,
        structural_manifest_candidates,
        checked_certificates,
        missing_checked_certificates: summary.total_vcs.saturating_sub(checked_certificates),
        rejected_certificates,
        raw_solver_proof_bytes,
        raw_solver_proof_byte_count,
        checked_certificates_satisfy_coverage: checked_certificates == summary.total_vcs
            && summary.solver_dispatch.len() == summary.total_vcs,
        raw_solver_proof_bytes_satisfy_coverage: false,
        structural_manifest_validation_satisfies_coverage: false,
        checked_certificate_identity_blockers,
        production_manifest,
    }
}

fn build_certificate_production_manifest_report(
    required_vcs: usize,
    solver_dispatches: usize,
    checked_certificates: usize,
    production_checked_certificates: usize,
    malformed_production_evidence: usize,
) -> BinaryCheckedCertificateProductionManifestReport {
    let missing_production_evidence = required_vcs.saturating_sub(production_checked_certificates);
    let accepted = solver_dispatches == required_vcs
        && checked_certificates == required_vcs
        && production_checked_certificates == required_vcs
        && malformed_production_evidence == 0;
    let mut release_blockers = Vec::new();
    if solver_dispatches != required_vcs {
        release_blockers.push(format!(
            "production manifest dispatch coverage incomplete: {solver_dispatches}/{required_vcs}"
        ));
    }
    if checked_certificates != required_vcs {
        release_blockers.push(format!(
            "production manifest requires checked certificates for every VC: {checked_certificates}/{required_vcs}"
        ));
    }
    if missing_production_evidence > 0 {
        release_blockers.push(format!(
            "production checker evidence missing for {missing_production_evidence} required VCs"
        ));
    }
    if malformed_production_evidence > 0 {
        release_blockers.push(format!(
            "production checker evidence malformed for {malformed_production_evidence} checked certificates"
        ));
    }

    BinaryCheckedCertificateProductionManifestReport {
        required_vcs,
        solver_dispatches,
        checked_certificates,
        production_checked_certificates,
        missing_production_evidence,
        malformed_production_evidence,
        accepted,
        release_blockers,
    }
}

fn format_binary_verification_line(label: &str, report: &BinaryVerificationReport) -> String {
    format!(
        "{label}: {:?} (trust: {:?}, replay: {:?}) | VCs: {} total, {} proved, {} failed, {} unknown, {} timeout, {} unsupported, {} rejected",
        report.status,
        report.trust_level,
        report.replay,
        report.total_vcs,
        report.proved,
        report.failed,
        report.unknown,
        report.timeout,
        report.unsupported,
        report.rejected
    )
}

fn format_binary_proof_grade_gate_line(label: &str, gate: &BinaryProofGradeGateReport) -> String {
    let status = if gate.accepted { "accepted" } else { "rejected" };
    let mut line = format!(
        "{label}: {status} | unsupported_empty={}, vcs_proved={}, checked_certs={}, production_checked_certs={}, replay_coverage={}, replay_semantics={}, reconstruction_validated={}, target_semantics_consumed={} ({}/{} proved, {}/{} checked, {}/{} production_checked, {}/{} replayed, {}/{} replay_semantics, cert_only_replay_semantics={}, target_outputs={}, target_blockers={}, preserved_symbolic_formulas={}, symbolic_formulas_consumed={}, raw_solver_proofs={}, raw_solver_proof_byte_count={}, aarch64_atomic_semantic_facts={}, aarch64_atomic_facts_consumed={}, aarch64_sync_boundary_facts={}, aarch64_sync_boundary_facts_consumed={})",
        gate.unsupported_ledger_empty,
        gate.all_required_vcs_proved,
        gate.checked_certificates_for_all_required_vcs,
        gate.production_checked_certificates_for_all_required_vcs,
        gate.full_replay_coverage,
        gate.replay_semantics_satisfied,
        gate.reconstruction_validated,
        gate.target_semantics_consumed,
        gate.proved_vcs,
        gate.required_vcs,
        gate.checked_certificates,
        gate.required_vcs,
        gate.production_checked_certificates,
        gate.required_vcs,
        gate.replayed_vcs,
        gate.required_vcs,
        gate.replay_semantics_satisfied_vcs,
        gate.required_vcs,
        gate.certificate_only_replay_semantics_vcs,
        gate.validated_target_outputs,
        gate.target_validation_blockers,
        gate.preserved_symbolic_formulas,
        gate.symbolic_formulas_consumed_by_proof_model,
        gate.raw_solver_proof_bytes,
        gate.raw_solver_proof_byte_count,
        gate.aarch64_atomic_semantic_fact_count,
        gate.aarch64_atomic_semantic_facts_consumed_by_proof_model,
        gate.aarch64_sync_boundary_fact_count,
        gate.aarch64_sync_boundary_facts_consumed_by_proof_model
    );
    if !gate.unsupported_by_family.is_empty() {
        let _ = write!(
            line,
            ", unsupported_families={{{}}}",
            format_counts(&gate.unsupported_by_family)
        );
    }
    line
}

fn format_unsupported_summary(label: &str, report: &BinaryUnsupportedLedgerReport) -> String {
    let mut line = format!("{label}: {} records", report.total_records);
    if !report.by_stage.is_empty() {
        let _ = write!(line, " by stage {{{}}}", format_counts(&report.by_stage));
    }
    if !report.by_feature.is_empty() {
        let _ = write!(line, " by feature {{{}}}", format_counts(&report.by_feature));
    }
    if !report.by_family.is_empty() {
        let _ = write!(line, " by family {{{}}}", format_counts(&report.by_family));
    }
    if report.aarch64_atomic_semantic_fact_count > 0 {
        let _ = write!(
            line,
            " aarch64_atomic_semantic_facts={}",
            report.aarch64_atomic_semantic_fact_count
        );
    }
    if report.aarch64_sync_boundary_fact_count > 0 {
        let _ = write!(
            line,
            " aarch64_sync_boundary_facts={}",
            report.aarch64_sync_boundary_fact_count
        );
    }
    line
}

fn format_digest_identity_summary(label: &str, report: &BinaryDigestIdentityReport) -> String {
    let status = if report.proof_grade_ready { "accepted" } else { "rejected" };
    let root = report
        .root_artifact_digest
        .as_ref()
        .map(|digest| format!("{}:{}", digest.algorithm, digest.value))
        .unwrap_or_else(|| "missing".to_string());
    let selected = report
        .selected_image
        .as_ref()
        .map(|identity| {
            let end = identity
                .end_offset
                .map(|end| end.to_string())
                .unwrap_or_else(|| "overflow".to_string());
            format!("[{}, {}) sha256={}", identity.file_offset, end, identity.sha256)
        })
        .unwrap_or_else(|| "missing".to_string());
    let blockers =
        if report.blockers.is_empty() { "none".to_string() } else { report.blockers.join("; ") };
    format!(
        "{label}: {status} | root_bytes={:?}, root_digest={}, selected_image={}, blockers={}",
        report.root_artifact_byte_len, root, selected, blockers
    )
}

fn format_unresolved_blocker_summary(
    label: &str,
    report: &BinaryUnresolvedBlockerLedgerReport,
) -> String {
    let mut line = format!("{label}: {} blockers", report.total_blockers);
    if !report.by_family.is_empty() {
        let _ = write!(line, " by family {{{}}}", format_counts(&report.by_family));
    }
    line
}

fn format_source_provenance_summary(label: &str, report: &BinarySourceProvenanceReport) -> String {
    let disabled_reasons = if report.source_backpropagation_disabled_reasons.is_empty() {
        "none".to_string()
    } else {
        report.source_backpropagation_disabled_reasons.join(", ")
    };
    format!(
        "{label}: {} (exact={}, ambiguous={}, source_backpropagation_allowed={}, binary_address_diagnostics_allowed={}, disabled_reasons=[{}])",
        report.status,
        report.exact_mapping_count,
        report.ambiguous_mapping_count,
        report.effective_source_backpropagation_allowed(),
        report.binary_address_diagnostics_allowed(),
        disabled_reasons
    )
}

fn format_source_backpropagation_gate_summary(
    label: &str,
    report: &BinarySourceBackpropagationGateReport,
) -> String {
    format!(
        "{label}: {} (accepted={}, required=[{}], missing=[{}])",
        report.status,
        report.accepted,
        report.required_labels.join(", "),
        report.missing_labels.join(", ")
    )
}

fn format_reconstruction_summary(label: &str, report: &BinaryReconstructionReport) -> String {
    let mut line = format!(
        "{label}: {:?} (target: {:?}, trust: {:?}, outputs={}, diagnostics={}, output_diagnostics={}, validation_records={}, target_validation_blockers={}, preserved_symbolic_formulas={}, symbolic_formula_consumer_status={})",
        report.validation,
        report.target,
        report.trust_level,
        report.output_count,
        report.diagnostics.len(),
        report.output_diagnostics.len(),
        report.validation_records.len(),
        report.target_validation_blocker_count,
        report.preserved_symbolic_formula_count,
        report.symbolic_formula_consumer_status
    );
    if !report.target_validation_blockers_by_stage.is_empty() {
        let _ = write!(
            line,
            " by stage {{{}}}",
            format_counts(&report.target_validation_blockers_by_stage)
        );
    }
    if !report.target_validation_blockers_by_feature.is_empty() {
        let _ = write!(
            line,
            " by feature {{{}}}",
            format_counts(&report.target_validation_blockers_by_feature)
        );
    }
    if !report.symbolic_formula_consumer_blockers.is_empty() {
        let _ = write!(
            line,
            " formula consumer blockers [{}]",
            report.symbolic_formula_consumer_blockers.join("; ")
        );
    }
    line
}

fn append_reconstruction_diagnostics(
    lines: &mut Vec<String>,
    indent: &str,
    report: &BinaryReconstructionReport,
) {
    for diagnostic in &report.diagnostics {
        lines.push(format!("{indent}Reconstruction diagnostic: {diagnostic}"));
    }
    for output in &report.output_diagnostics {
        let artifact = output
            .artifact_path
            .as_ref()
            .map(|path| format!(" artifact={path}"))
            .unwrap_or_default();
        lines.push(format!(
            "{indent}Reconstruction output diagnostics: target={:?}, validation={:?}, trust={:?}{}",
            output.target, output.validation, output.trust_level, artifact
        ));
        for diagnostic in &output.diagnostics {
            lines.push(format!("{indent}  output diagnostic: {diagnostic}"));
        }
    }
    for record in &report.validation_records {
        let function = record
            .function
            .as_ref()
            .map(|function| format!(" function={function}"))
            .unwrap_or_default();
        let lifted = record
            .lifted_function
            .as_ref()
            .map(|function| format!(" lifted={function}"))
            .unwrap_or_default();
        let reconstructed = record
            .reconstructed_function
            .as_ref()
            .map(|function| format!(" reconstructed={function}"))
            .unwrap_or_default();
        lines.push(format!(
            "{indent}Reconstruction validation record: target={:?}{}{}{}, candidate={:?}, status={:?}, trust={:?}, evidence={:?}",
            record.target,
            function,
            lifted,
            reconstructed,
            record.candidate,
            record.status,
            record.trust_level,
            record.evidence
        ));
        if let Some(forward) = &record.forward {
            lines.push(format!(
                "{indent}  forward refinement: status={:?}, vcs={}, counterexamples={}, proof_certificates={}",
                forward.status, forward.vc_count, forward.counterexamples, forward.proof_certificates
            ));
            for diagnostic in &forward.diagnostics {
                lines.push(format!("{indent}    forward diagnostic: {diagnostic}"));
            }
        }
        if let Some(reverse) = &record.reverse {
            lines.push(format!(
                "{indent}  reverse refinement: status={:?}, vcs={}, counterexamples={}, proof_certificates={}",
                reverse.status, reverse.vc_count, reverse.counterexamples, reverse.proof_certificates
            ));
            for diagnostic in &reverse.diagnostics {
                lines.push(format!("{indent}    reverse diagnostic: {diagnostic}"));
            }
        }
        for diagnostic in &record.diagnostics {
            lines.push(format!("{indent}  validation diagnostic: {diagnostic}"));
        }
    }
}

fn append_source_provenance_diagnostics(
    lines: &mut Vec<String>,
    indent: &str,
    report: &BinarySourceProvenanceReport,
) {
    for diagnostic in report.typed_diagnostics() {
        lines.push(format!(
            "{indent}Source provenance diagnostic: {} | source_backpropagation_allowed={}, binary_address_diagnostics_allowed={} | {}",
            diagnostic.kind.label(),
            diagnostic.source_backpropagation_allowed,
            diagnostic.binary_address_diagnostics_allowed,
            diagnostic.message
        ));
    }
}

fn append_source_backpropagation_gate_blockers(
    lines: &mut Vec<String>,
    indent: &str,
    report: &BinarySourceBackpropagationGateReport,
) {
    for blocker in &report.blockers {
        lines.push(format!(
            "{indent}Source backpropagation blocker: {} stage={} | {}",
            blocker.label, blocker.stage, blocker.detail
        ));
    }
}

fn append_target_validation_blockers(
    lines: &mut Vec<String>,
    indent: &str,
    report: &BinaryReconstructionReport,
) {
    if report.target_validation_blockers.is_empty() {
        return;
    }

    lines.push(format!("{indent}Target validation blockers:"));
    for blocker in &report.target_validation_blockers {
        let function = blocker
            .function
            .as_ref()
            .map(|function| format!(" function={function}"))
            .unwrap_or_default();
        let location = blocker
            .location
            .as_ref()
            .map(|loc| format!(" @{}", loc.instruction_address_display))
            .unwrap_or_default();
        lines.push(format!(
            "{indent}  {:?}/{}/{}{}{} | {}",
            blocker.target, blocker.stage, blocker.feature, function, location, blocker.reason
        ));
        for diagnostic in &blocker.diagnostics {
            lines.push(format!("{indent}    target validation diagnostic: {diagnostic}"));
        }
    }
}

fn append_preserved_symbolic_formulas(
    lines: &mut Vec<String>,
    indent: &str,
    report: &BinaryReconstructionReport,
) {
    if report.preserved_symbolic_formulas.is_empty() {
        return;
    }

    lines.push(format!("{indent}Preserved symbolic formulas:"));
    for formula in &report.preserved_symbolic_formulas {
        let function = formula
            .function
            .as_ref()
            .map(|function| format!(" function={function}"))
            .unwrap_or_default();
        let block = formula.block.map(|block| format!(" block={block}")).unwrap_or_default();
        let statement = formula
            .statement_index
            .map(|statement| format!(" statement={statement}"))
            .unwrap_or_default();
        let sort_declarations = format_formula_sort_declarations(&formula.sort_declarations);
        lines.push(format!(
            "{indent}  {:?}{}{}{} {} | proof_consumer={}, schema={}, sort={}, digest={}, origin={}, declarations=[{}], smtlib={}, formula={:?}",
            formula.target,
            function,
            block,
            statement,
            formula.location,
            formula.proof_consumer_status,
            formula.formula_schema,
            if formula.smtlib_sort.is_empty() { "missing" } else { formula.smtlib_sort.as_str() },
            formula.formula_digest,
            formula.formula_origin,
            sort_declarations,
            formula.smtlib,
            formula.formula
        ));
        for blocker in &formula.proof_consumer_blockers {
            lines.push(format!("{indent}    symbolic formula consumer blocker: {blocker}"));
        }
    }
}

fn append_aarch64_atomic_semantic_facts(
    lines: &mut Vec<String>,
    indent: &str,
    label: &str,
    report: &BinaryUnsupportedLedgerReport,
) {
    if report.aarch64_atomic_semantic_facts.is_empty() {
        return;
    }

    lines.push(format!("{indent}{label}:"));
    for fact in &report.aarch64_atomic_semantic_facts {
        let location = fact
            .location
            .as_ref()
            .map(|loc| format!(" @{}", loc.instruction_address_display))
            .unwrap_or_default();
        let operand =
            fact.operand.as_ref().map(|operand| format!(" operand={operand}")).unwrap_or_default();
        let missing = if fact.missing_witnesses.is_empty() {
            "none".to_string()
        } else {
            fact.missing_witnesses.join(", ")
        };
        lines.push(format!(
            "{indent}  {}{}{} | access={:?}, ordering={:?}, exclusive_monitor={:?}, reports_status={}, consumed_by_proof_model={}, proof_grade_accepted={}, missing_witnesses={}",
            fact.opcode,
            location,
            operand,
            fact.access,
            fact.ordering,
            fact.exclusive_monitor,
            fact.reports_status,
            fact.consumed_by_proof_model,
            fact.proof_grade_accepted,
            missing
        ));
        if let Some(reason) = &fact.proof_grade_rejection_reason {
            lines.push(format!("{indent}    atomic fact blocker: {reason}"));
        }
    }
}

fn append_aarch64_sync_boundary_facts(
    lines: &mut Vec<String>,
    indent: &str,
    label: &str,
    report: &BinaryUnsupportedLedgerReport,
) {
    if report.aarch64_sync_boundary_facts.is_empty() {
        return;
    }

    lines.push(format!("{indent}{label}:"));
    for fact in &report.aarch64_sync_boundary_facts {
        let location = fact
            .location
            .as_ref()
            .map(|loc| format!(" @{}", loc.instruction_address_display))
            .unwrap_or_default();
        let operand =
            fact.operand.as_ref().map(|operand| format!(" operand={operand}")).unwrap_or_default();
        let raw_option =
            fact.raw_option.map(|option| format!(" raw_option=0x{option:x}")).unwrap_or_default();
        let missing = if fact.missing_witnesses.is_empty() {
            "none".to_string()
        } else {
            fact.missing_witnesses.join(", ")
        };
        lines.push(format!(
            "{indent}  {}{}{}{} | kind={:?}, scope={:?}, ordering={:?}, clears_exclusive_monitor={}, consumed_by_proof_model={}, proof_grade_accepted={}, missing_witnesses={}",
            fact.opcode,
            location,
            operand,
            raw_option,
            fact.kind,
            fact.scope,
            fact.ordering,
            fact.clears_exclusive_monitor,
            fact.consumed_by_proof_model,
            fact.proof_grade_accepted,
            missing
        ));
        if let Some(reason) = &fact.proof_grade_rejection_reason {
            lines.push(format!("{indent}    sync boundary fact blocker: {reason}"));
        }
    }
}

fn append_gate_rejection_details(
    lines: &mut Vec<String>,
    indent: &str,
    subject: &str,
    gate: &BinaryProofGradeGateReport,
) {
    if gate.rejections.is_empty() {
        return;
    }

    lines.push(format!(
        "{indent}Proof-grade blocker groups for {subject}: {}",
        format_proof_grade_blocker_groups(&gate.blocker_groups)
    ));
    lines.push(format!("{indent}Proof-grade gate rejections for {subject}:"));
    for rejection in &gate.rejections {
        lines.push(format!("{indent}  {}", format_gate_rejection(rejection)));
    }
}

fn append_unresolved_blockers(
    lines: &mut Vec<String>,
    indent: &str,
    report: &BinaryUnresolvedBlockerLedgerReport,
) {
    if report.entries.is_empty() {
        return;
    }

    lines.push(format!("{indent}Unresolved blocker ledger:"));
    for blocker in &report.entries {
        let stage =
            blocker.stage.as_ref().map(|stage| format!(" stage={stage}")).unwrap_or_default();
        let dispatch = blocker
            .dispatch_id
            .as_ref()
            .map(|dispatch_id| format!(" dispatch={dispatch_id}"))
            .unwrap_or_default();
        let location = blocker
            .location
            .as_ref()
            .map(|loc| format!(" @{}", loc.instruction_address_display))
            .unwrap_or_default();
        lines.push(format!(
            "{indent}  {}/{}{}{}{} | {}",
            blocker.family, blocker.feature, stage, dispatch, location, blocker.reason
        ));
    }
}

fn format_proof_grade_blocker_groups(groups: &BinaryProofGradeBlockerGroupsReport) -> String {
    let entries = [
        ("trust_level", groups.trust_level.len()),
        ("unsupported_ledger", groups.unsupported_ledger.len()),
        ("verification", groups.verification.len()),
        ("certificate", groups.certificate.len()),
        ("replay", groups.replay.len()),
        ("reconstruction", groups.reconstruction.len()),
        ("source_provenance", groups.source_provenance.len()),
        ("raw_solver_proofs", groups.raw_solver_proofs.len()),
    ]
    .into_iter()
    .filter(|(_, count)| *count > 0)
    .map(|(label, count)| format!("{label}={count}"))
    .collect::<Vec<_>>();

    if entries.is_empty() { "none".to_string() } else { entries.join(", ") }
}

fn gate_rejection_family(rejection: &BinaryProofGradeGateRejectionReport) -> &'static str {
    match rejection {
        BinaryProofGradeGateRejectionReport::FinalTrustLevelNotProofGrade { .. } => "trust_level",
        BinaryProofGradeGateRejectionReport::UnsupportedRecordsPresent { .. } => {
            "unsupported_ledger"
        }
        BinaryProofGradeGateRejectionReport::RequiredVcCoverageIncomplete { .. }
        | BinaryProofGradeGateRejectionReport::NonProvedVerificationConditions { .. } => {
            "verification"
        }
        BinaryProofGradeGateRejectionReport::MissingCheckedProofCertificates { .. }
        | BinaryProofGradeGateRejectionReport::CheckedCertificateProductionManifestIncomplete {
            ..
        } => "certificate",
        BinaryProofGradeGateRejectionReport::ReplayStatusMissing
        | BinaryProofGradeGateRejectionReport::ReplayCoverageIncomplete { .. }
        | BinaryProofGradeGateRejectionReport::ReplayStatusUnknown { .. }
        | BinaryProofGradeGateRejectionReport::ReplayNotSuccessful { .. }
        | BinaryProofGradeGateRejectionReport::ReplayArtifactDigestIdentityNotExact { .. }
        | BinaryProofGradeGateRejectionReport::ReplayBoundarySemanticsUnsupported { .. } => {
            "replay"
        }
        BinaryProofGradeGateRejectionReport::ReconstructionValidationNotValidated { .. }
        | BinaryProofGradeGateRejectionReport::TargetSemanticsNotConsumed { .. }
        | BinaryProofGradeGateRejectionReport::TargetValidationBlockersPresent { .. }
        | BinaryProofGradeGateRejectionReport::SymbolicFormulasNotConsumed { .. } => {
            "reconstruction"
        }
        BinaryProofGradeGateRejectionReport::SourceProvenanceNotExact { .. } => "source_provenance",
        BinaryProofGradeGateRejectionReport::DigestIdentityNotExact { .. } => "digest_identity",
        BinaryProofGradeGateRejectionReport::RawSolverProofBytesPresent { .. } => {
            "raw_solver_proofs"
        }
        BinaryProofGradeGateRejectionReport::Aarch64AtomicSemanticFactsNotConsumed { .. } => {
            "unsupported_ledger"
        }
        BinaryProofGradeGateRejectionReport::Aarch64SyncBoundaryFactsNotConsumed { .. } => {
            "unsupported_ledger"
        }
    }
}

fn gate_rejection_feature(rejection: &BinaryProofGradeGateRejectionReport) -> &'static str {
    match rejection {
        BinaryProofGradeGateRejectionReport::FinalTrustLevelNotProofGrade { .. } => {
            "final_trust_level_not_proof_grade"
        }
        BinaryProofGradeGateRejectionReport::UnsupportedRecordsPresent { .. } => {
            "unsupported_records_present"
        }
        BinaryProofGradeGateRejectionReport::RequiredVcCoverageIncomplete { .. } => {
            "required_vc_coverage_incomplete"
        }
        BinaryProofGradeGateRejectionReport::NonProvedVerificationConditions { .. } => {
            "non_proved_verification_conditions"
        }
        BinaryProofGradeGateRejectionReport::MissingCheckedProofCertificates { .. } => {
            "missing_checked_proof_certificates"
        }
        BinaryProofGradeGateRejectionReport::CheckedCertificateProductionManifestIncomplete {
            ..
        } => "checked_certificate_production_manifest_incomplete",
        BinaryProofGradeGateRejectionReport::ReplayStatusMissing => "replay_status_missing",
        BinaryProofGradeGateRejectionReport::ReplayCoverageIncomplete { .. } => {
            "replay_coverage_incomplete"
        }
        BinaryProofGradeGateRejectionReport::ReplayStatusUnknown { .. } => "replay_status_unknown",
        BinaryProofGradeGateRejectionReport::ReplayNotSuccessful { .. } => "replay_not_successful",
        BinaryProofGradeGateRejectionReport::ReplayArtifactDigestIdentityNotExact { .. } => {
            "replay_artifact_digest_identity_not_exact"
        }
        BinaryProofGradeGateRejectionReport::ReplayBoundarySemanticsUnsupported { .. } => {
            "replay_boundary_semantics_unsupported"
        }
        BinaryProofGradeGateRejectionReport::ReconstructionValidationNotValidated { .. } => {
            "reconstruction_validation_not_validated"
        }
        BinaryProofGradeGateRejectionReport::TargetSemanticsNotConsumed { .. } => {
            "target_semantics_not_consumed"
        }
        BinaryProofGradeGateRejectionReport::TargetValidationBlockersPresent { .. } => {
            "target_validation_blockers_present"
        }
        BinaryProofGradeGateRejectionReport::SymbolicFormulasNotConsumed { .. } => {
            "trust_symbolic_formula_not_consumed"
        }
        BinaryProofGradeGateRejectionReport::SourceProvenanceNotExact { .. } => {
            "source_provenance_not_exact"
        }
        BinaryProofGradeGateRejectionReport::DigestIdentityNotExact { .. } => {
            "digest_identity_not_exact"
        }
        BinaryProofGradeGateRejectionReport::RawSolverProofBytesPresent { .. } => {
            "raw_solver_proof_bytes_present"
        }
        BinaryProofGradeGateRejectionReport::Aarch64AtomicSemanticFactsNotConsumed { .. } => {
            "aarch64_atomic_semantic_facts_not_consumed"
        }
        BinaryProofGradeGateRejectionReport::Aarch64SyncBoundaryFactsNotConsumed { .. } => {
            "aarch64_sync_boundary_facts_not_consumed"
        }
    }
}

fn refresh_proof_grade_blocker_groups(gate: &mut BinaryProofGradeGateReport) {
    gate.blocker_groups = build_proof_grade_blocker_groups(&gate.rejections);
}

fn build_proof_grade_blocker_groups(
    rejections: &[BinaryProofGradeGateRejectionReport],
) -> BinaryProofGradeBlockerGroupsReport {
    let mut groups = BinaryProofGradeBlockerGroupsReport::default();

    for rejection in rejections {
        match rejection {
            BinaryProofGradeGateRejectionReport::FinalTrustLevelNotProofGrade { .. } => {
                groups.trust_level.push(rejection.clone());
            }
            BinaryProofGradeGateRejectionReport::UnsupportedRecordsPresent { .. } => {
                groups.unsupported_ledger.push(rejection.clone());
            }
            BinaryProofGradeGateRejectionReport::Aarch64AtomicSemanticFactsNotConsumed {
                ..
            }
            | BinaryProofGradeGateRejectionReport::Aarch64SyncBoundaryFactsNotConsumed {
                ..
            } => {
                groups.unsupported_ledger.push(rejection.clone());
            }
            BinaryProofGradeGateRejectionReport::RequiredVcCoverageIncomplete { .. }
            | BinaryProofGradeGateRejectionReport::NonProvedVerificationConditions { .. } => {
                groups.verification.push(rejection.clone());
            }
            BinaryProofGradeGateRejectionReport::MissingCheckedProofCertificates { .. } => {
                groups.certificate.push(rejection.clone());
            }
            BinaryProofGradeGateRejectionReport::CheckedCertificateProductionManifestIncomplete {
                ..
            } => {
                groups.certificate.push(rejection.clone());
            }
            BinaryProofGradeGateRejectionReport::ReplayStatusMissing
            | BinaryProofGradeGateRejectionReport::ReplayCoverageIncomplete { .. }
            | BinaryProofGradeGateRejectionReport::ReplayStatusUnknown { .. }
            | BinaryProofGradeGateRejectionReport::ReplayNotSuccessful { .. }
            | BinaryProofGradeGateRejectionReport::ReplayArtifactDigestIdentityNotExact {
                ..
            }
            | BinaryProofGradeGateRejectionReport::ReplayBoundarySemanticsUnsupported {
                ..
            } => {
                groups.replay.push(rejection.clone());
            }
            BinaryProofGradeGateRejectionReport::ReconstructionValidationNotValidated { .. }
            | BinaryProofGradeGateRejectionReport::TargetSemanticsNotConsumed { .. }
            | BinaryProofGradeGateRejectionReport::TargetValidationBlockersPresent { .. }
            | BinaryProofGradeGateRejectionReport::SymbolicFormulasNotConsumed { .. } => {
                groups.reconstruction.push(rejection.clone());
            }
            BinaryProofGradeGateRejectionReport::SourceProvenanceNotExact { .. } => {
                groups.source_provenance.push(rejection.clone());
            }
            BinaryProofGradeGateRejectionReport::DigestIdentityNotExact { .. } => {
                groups.source_provenance.push(rejection.clone());
            }
            BinaryProofGradeGateRejectionReport::RawSolverProofBytesPresent { .. } => {
                groups.raw_solver_proofs.push(rejection.clone());
            }
        }
    }

    groups
}

fn format_gate_rejection(rejection: &BinaryProofGradeGateRejectionReport) -> String {
    match rejection {
        BinaryProofGradeGateRejectionReport::FinalTrustLevelNotProofGrade { found } => {
            format!("final trust is not ProofGrade: found {found:?}")
        }
        BinaryProofGradeGateRejectionReport::UnsupportedRecordsPresent { count } => {
            format!("unsupported records present: {count}")
        }
        BinaryProofGradeGateRejectionReport::RequiredVcCoverageIncomplete {
            vc_count,
            solver_dispatches,
        } => format!("required VC coverage incomplete: {solver_dispatches}/{vc_count} dispatches"),
        BinaryProofGradeGateRejectionReport::NonProvedVerificationConditions {
            vc_count,
            total_results,
            proved,
            unproved_vcs,
            non_proved_results,
        } => format!(
            "non-proved verification conditions: {proved}/{vc_count} proved, {total_results} dispatches, {unproved_vcs} unproved required VCs, {non_proved_results} non-proved dispatches"
        ),
        BinaryProofGradeGateRejectionReport::MissingCheckedProofCertificates {
            vc_count,
            checked_certificates,
            missing_certificates,
        } => format!(
            "missing checked proof certificates: {missing_certificates} missing ({checked_certificates}/{vc_count} checked)"
        ),
        BinaryProofGradeGateRejectionReport::CheckedCertificateProductionManifestIncomplete {
            vc_count,
            production_checked_certificates,
            missing_production_evidence,
            malformed_production_evidence,
        } => format!(
            "checked certificate production manifest incomplete: {production_checked_certificates}/{vc_count} production checked, {missing_production_evidence} missing, {malformed_production_evidence} malformed"
        ),
        BinaryProofGradeGateRejectionReport::ReplayStatusMissing => {
            "replay status missing".to_string()
        }
        BinaryProofGradeGateRejectionReport::ReplayCoverageIncomplete {
            vc_count,
            replay_records,
            replayed,
        } => format!(
            "replay coverage incomplete: {replay_records}/{vc_count} records, {replayed} replayed"
        ),
        BinaryProofGradeGateRejectionReport::ReplayStatusUnknown { not_attempted } => {
            format!("replay status unknown: {not_attempted} not attempted")
        }
        BinaryProofGradeGateRejectionReport::ReplayNotSuccessful { failed, spurious } => {
            format!("replay not successful: {failed} failed, {spurious} spurious")
        }
        BinaryProofGradeGateRejectionReport::ReplayArtifactDigestIdentityNotExact {
            replayed_vcs,
            ready_replayed_vcs,
            blocked_replayed_vcs,
        } => format!(
            "replay artifact digest identity not exact: {ready_replayed_vcs}/{replayed_vcs} replayed dispatches ready, {blocked_replayed_vcs} blocked"
        ),
        BinaryProofGradeGateRejectionReport::ReplayBoundarySemanticsUnsupported {
            boundary_count,
            unsupported_boundary_count,
        } => format!(
            "replay boundary semantics unsupported: {unsupported_boundary_count}/{boundary_count} syscall/exception/trap boundaries lack exact semantics witnesses"
        ),
        BinaryProofGradeGateRejectionReport::ReconstructionValidationNotValidated { status } => {
            format!("reconstruction validation not proof-grade: {status:?}")
        }
        BinaryProofGradeGateRejectionReport::TargetSemanticsNotConsumed {
            target,
            validated_outputs,
            target_validation_blockers,
        } => format!(
            "target semantics not proof-grade: target={target:?}, validated_outputs={validated_outputs}, target_validation_blockers={target_validation_blockers}"
        ),
        BinaryProofGradeGateRejectionReport::TargetValidationBlockersPresent { target, count } => {
            format!("target validation blockers present: target={target:?}, count={count}")
        }
        BinaryProofGradeGateRejectionReport::SymbolicFormulasNotConsumed { target, count } => {
            format!(
                "trust_symbolic.formula payloads not proof-consumed: target={target:?}, count={count}"
            )
        }
        BinaryProofGradeGateRejectionReport::SourceProvenanceNotExact {
            status,
            exact_mapping_count,
        } => format!(
            "source provenance not proof-grade: status={status}, exact_mapping_count={exact_mapping_count}"
        ),
        BinaryProofGradeGateRejectionReport::DigestIdentityNotExact { blockers } => {
            format!("binary digest identity not proof-grade: {}", blockers.join("; "))
        }
        BinaryProofGradeGateRejectionReport::RawSolverProofBytesPresent { count } => {
            format!("raw solver proof bytes present: {count}")
        }
        BinaryProofGradeGateRejectionReport::Aarch64AtomicSemanticFactsNotConsumed {
            count,
            unconsumed,
            missing_witnesses,
        } => format!(
            "AArch64 atomic semantic facts not proof-consumed: {unconsumed}/{count} unconsumed; semantics/replay/certificates must account for witnesses: {}",
            missing_witnesses.join(", ")
        ),
        BinaryProofGradeGateRejectionReport::Aarch64SyncBoundaryFactsNotConsumed {
            count,
            unconsumed,
            missing_witnesses,
        } => format!(
            "AArch64 sync boundary facts not proof-consumed: {unconsumed}/{count} unconsumed; semantics/replay/certificates must account for witnesses: {}",
            missing_witnesses.join(", ")
        ),
    }
}

fn append_dispatch_details(
    lines: &mut Vec<String>,
    indent: &str,
    report: &BinaryVerificationReport,
) {
    if report.solver_dispatches.is_empty() {
        return;
    }

    lines.push(format!(
        "{indent}Certificate checks: {}/{} accepted checked certificates, {} production checked, {} certificate-shaped candidates, {} structural manifest candidates, {} missing checked certificates, identity_blockers={}, raw_solver_proofs={}, raw_solver_proof_byte_count={} (raw_satisfies_coverage={}, manifest_structural_satisfies_coverage={}, production_manifest_accepted={}, missing_production_evidence={}, malformed_production_evidence={})",
        report.certificate_checks.checked_certificates,
        report.certificate_checks.required_vcs,
        report
            .certificate_checks
            .production_manifest
            .production_checked_certificates,
        report.certificate_checks.certificate_candidates,
        report.certificate_checks.structural_manifest_candidates,
        report.certificate_checks.missing_checked_certificates,
        report.certificate_checks.checked_certificate_identity_blockers.len(),
        report.certificate_checks.raw_solver_proof_bytes,
        report.certificate_checks.raw_solver_proof_byte_count,
        report.certificate_checks.raw_solver_proof_bytes_satisfy_coverage,
        report.certificate_checks.structural_manifest_validation_satisfies_coverage,
        report.certificate_checks.production_manifest.accepted,
        report.certificate_checks.production_manifest.missing_production_evidence,
        report.certificate_checks.production_manifest.malformed_production_evidence
    ));
    lines.push(format!("{indent}VC dispatches:"));
    for dispatch in &report.solver_dispatches {
        let location = dispatch
            .location
            .as_ref()
            .map(|loc| format!(" @{}", loc.instruction_address_display))
            .unwrap_or_default();
        let result = dispatch
            .result_status
            .as_ref()
            .map(|status| format!(", result: {status}"))
            .unwrap_or_default();
        let raw_solver = if dispatch.raw_solver_proof_bytes {
            format!(", raw solver proof bytes: {}", dispatch.raw_solver_proof_byte_count)
        } else {
            String::new()
        };
        lines.push(format!(
            "{indent}  {}{}: {:?} ({}, semantics: {:?}, cert: {}, production: {}{}, replay: {:?}{result})",
            dispatch.id,
            location,
            dispatch.status,
            dispatch.solver,
            dispatch.query_semantics,
            proof_certificate_status_label(&dispatch.certificate),
            production_checker_evidence_label(&dispatch.production_checker_evidence),
            raw_solver,
            dispatch.replay
        ));
        for diagnostic in &dispatch.diagnostics {
            lines.push(format!("{indent}    dispatch diagnostic: {diagnostic}"));
        }
        if let Some(detail) =
            production_checker_evidence_detail(&dispatch.production_checker_evidence)
        {
            lines.push(format!("{indent}    production evidence: {detail}"));
        }
        if dispatch.checked_certificate_identity.required
            || !dispatch.checked_certificate_identity.blockers.is_empty()
            || dispatch.checked_certificate_identity.checked_identity_ready
        {
            lines.push(format!(
                "{indent}    checked certificate identity: {}",
                format_checked_certificate_identity_summary(&dispatch.checked_certificate_identity)
            ));
            for blocker in &dispatch.checked_certificate_identity.blockers {
                lines
                    .push(format!("{indent}      checked certificate identity blocker: {blocker}"));
            }
        }
        if let Some(formula) = &dispatch.vc_formula {
            let sort_declarations = format_formula_sort_declarations(&formula.sort_declarations);
            lines.push(format!(
                "{indent}    formula: kind={}, nodes={}, free_vars=[{}], sorts=[{}], bitvectors={}, arrays={}, smtlib={}",
                formula.kind,
                formula.node_count,
                formula.free_variables.join(", "),
                sort_declarations,
                formula.has_bitvectors,
                formula.has_arrays,
                formula.smtlib
            ));
        } else if let Some(kind) = &dispatch.vc_kind {
            lines.push(format!("{indent}    formula: kind={kind}, unavailable"));
        }
        if dispatch.replay_digest_identity.required
            || dispatch.replay_digest_identity.identity.is_some()
            || !dispatch.replay_digest_identity.blockers.is_empty()
        {
            lines.push(format!(
                "{indent}    replay digest identity: {}",
                format_replay_digest_identity_summary(&dispatch.replay_digest_identity)
            ));
            for blocker in &dispatch.replay_digest_identity.blockers {
                lines.push(format!("{indent}      replay digest blocker: {blocker}"));
            }
        }
        for evidence in &dispatch.replay_boundary_evidence {
            lines.push(format!(
                "{indent}    replay boundary: kind={}, arch={}, address={}, step={:?}, opcode={}, encoding={}, bytes=[{}], semantics={}, proof_grade_accepted={}",
                evidence.kind,
                evidence.architecture,
                evidence.instruction_address_display,
                evidence.step,
                evidence.opcode,
                evidence.encoding,
                evidence.instruction_bytes_hex,
                evidence.semantics,
                evidence.proof_grade_accepted
            ));
            if let Some(reason) = &evidence.proof_grade_rejection_reason {
                lines.push(format!("{indent}      replay boundary blocker: {reason}"));
            }
        }
        for attempt in &dispatch.fallback_attempts {
            lines.push(format!(
                "{indent}    fallback attempt #{}: solver={}, status={:?}, planned_timeout_ms={:?}, backend_timeout_ms={:?}, error={}, release_blocker={}",
                attempt.attempt_index,
                attempt.solver,
                attempt.status,
                attempt.planned_timeout_ms,
                attempt.backend_timeout_ms,
                attempt.error.as_deref().unwrap_or("none"),
                attempt.release_blocker.as_deref().unwrap_or("none")
            ));
        }
    }
}

fn format_counts(counts: &BTreeMap<String, usize>) -> String {
    counts.iter().map(|(key, value)| format!("{key}: {value}")).collect::<Vec<_>>().join(", ")
}

fn format_replay_digest_identity_summary(report: &BinaryReplayDigestIdentityReport) -> String {
    let status = if report.proof_grade_ready { "accepted" } else { "rejected" };
    let root = report
        .root_artifact_digest
        .as_ref()
        .map(|digest| format!("{}:{}", digest.algorithm, digest.value))
        .unwrap_or_else(|| "missing".to_string());
    let selected_image = report
        .selected_image_identity
        .as_ref()
        .map(|selected| {
            let end = selected
                .end_offset
                .map(|end| end.to_string())
                .unwrap_or_else(|| "overflow".to_string());
            format!(
                "range=[{}, {}), size={}, sha256={}",
                selected.file_offset, end, selected.file_size, selected.sha256
            )
        })
        .unwrap_or_else(|| "missing".to_string());
    format!(
        "{status} | required={}, root_digest={}, selected_image={}, blockers={}",
        report.required,
        root,
        selected_image,
        report.blockers.len()
    )
}

fn format_checked_certificate_identity_summary(
    report: &BinaryCheckedCertificateIdentityReport,
) -> String {
    let status = if report.proof_grade_ready {
        "accepted"
    } else if report.checked_identity_ready {
        "checked-only"
    } else {
        "rejected"
    };
    let checker = report.checker.as_deref().unwrap_or("missing");
    let format = report.format.as_deref().unwrap_or("missing");
    let sha256 = report.sha256.as_deref().unwrap_or("missing");
    let artifact_path = report.artifact_path.as_deref().unwrap_or("none");
    format!(
        "{status} | required={}, cert_status={}, checker={}, format={}, sha256={}, artifact_path={}, production={}, blockers={}",
        report.required,
        report.status,
        checker,
        format,
        sha256,
        artifact_path,
        production_checker_evidence_label(&report.production_checker_evidence),
        report.blockers.len()
    )
}

fn verification_result_status(result: &VerificationResult) -> String {
    result.outcome().as_str().to_string()
}

fn dispatch_proves_required_vc(dispatch: &SolverDispatchRecord) -> bool {
    dispatch.status == SolverDispatchStatus::Unsat
        && dispatch.query_semantics == SolverQuerySemantics::SatIsCounterexample
}

fn dispatch_satisfies_certificate_only_replay_semantics(dispatch: &SolverDispatchRecord) -> bool {
    dispatch_proves_required_vc(dispatch)
        && dispatch.replay == ReplayStatus::NotAttempted
        && dispatch_has_checked_certificate_identity(dispatch)
}

fn dispatch_satisfies_replay_semantics(dispatch: &SolverDispatchRecord) -> bool {
    match (dispatch.status, dispatch.query_semantics) {
        (SolverDispatchStatus::Sat, SolverQuerySemantics::SatIsCounterexample) => {
            dispatch.replay == ReplayStatus::Replayed
        }
        (SolverDispatchStatus::Unsat, SolverQuerySemantics::SatIsCounterexample) => {
            dispatch.replay == ReplayStatus::Replayed
                || dispatch_satisfies_certificate_only_replay_semantics(dispatch)
        }
        _ => false,
    }
}

fn dispatch_has_checked_certificate_identity(dispatch: &SolverDispatchRecord) -> bool {
    checked_certificate_status_has_canonical_identity(&dispatch.certificate)
}

fn dispatch_has_production_checked_certificate_identity(dispatch: &SolverDispatchRecord) -> bool {
    dispatch_has_checked_certificate_identity(dispatch)
        && dispatch.certificate.is_production_checked()
}

fn checked_certificate_status_has_canonical_identity(status: &ProofCertificateStatus) -> bool {
    matches!(
        status,
        ProofCertificateStatus::Checked { checker, format, sha256 }
            if !checker.trim().is_empty()
                && !format.trim().is_empty()
                && sha256.as_deref().is_some_and(is_canonical_sha256_hex)
    )
}

fn raw_solver_result_has_certificate_bytes(result: Option<&VerificationResult>) -> bool {
    matches!(result, Some(VerificationResult::Proved { proof_certificate: Some(_), .. }))
}

fn raw_solver_result_certificate_byte_count(result: Option<&VerificationResult>) -> usize {
    match result {
        Some(VerificationResult::Proved { proof_certificate: Some(bytes), .. }) => bytes.len(),
        _ => 0,
    }
}

fn certificate_candidate_present(status: &ProofCertificateStatus) -> bool {
    matches!(
        status,
        ProofCertificateStatus::Present { .. }
            | ProofCertificateStatus::Checked { .. }
            | ProofCertificateStatus::Rejected { .. }
    )
}

fn structural_manifest_candidate_present(status: &ProofCertificateStatus) -> bool {
    match status {
        ProofCertificateStatus::Present { format, artifact_path, .. } => {
            format.contains("checked-binary-certificate")
                || artifact_path
                    .as_deref()
                    .is_some_and(|path| path.contains("manifest") || path.contains('#'))
        }
        _ => false,
    }
}

fn checked_certificate_identity_blockers(
    checker: &str,
    format: &str,
    sha256: Option<&str>,
) -> Vec<String> {
    let mut blockers = Vec::new();
    if checker.trim().is_empty() {
        blockers.push("checked certificate checker is missing".to_string());
    }
    if format.trim().is_empty() {
        blockers.push("checked certificate format is missing".to_string());
    }
    match sha256 {
        Some(value) if is_canonical_sha256_hex(value) => {}
        Some(_) => blockers
            .push("checked certificate sha256 is not canonical lowercase SHA-256 hex".to_string()),
        None => blockers.push("checked certificate sha256 is missing".to_string()),
    }
    blockers
}

fn proof_certificate_status_label(status: &ProofCertificateStatus) -> &'static str {
    match status {
        ProofCertificateStatus::Checked { .. }
            if checked_certificate_status_has_canonical_identity(status) =>
        {
            "checked"
        }
        ProofCertificateStatus::Checked { .. } => "checked-invalid",
        ProofCertificateStatus::Present { .. } => "present-unchecked",
        ProofCertificateStatus::Unavailable { .. } => "unavailable",
        ProofCertificateStatus::Rejected { .. } => "rejected",
        ProofCertificateStatus::NotRequested => "not-requested",
        _ => "unknown",
    }
}

fn production_checker_evidence_label(
    status: &ProofCertificateProductionCheckerEvidenceStatus,
) -> &'static str {
    match status {
        ProofCertificateProductionCheckerEvidenceStatus::Missing => "missing",
        ProofCertificateProductionCheckerEvidenceStatus::Malformed { .. } => "malformed",
        ProofCertificateProductionCheckerEvidenceStatus::Present { .. } => "present",
    }
}

fn production_checker_evidence_detail(
    status: &ProofCertificateProductionCheckerEvidenceStatus,
) -> Option<String> {
    match status {
        ProofCertificateProductionCheckerEvidenceStatus::Present { evidence } => Some(format!(
            "checker={} version={} sha256={}",
            evidence.checker, evidence.checker_version, evidence.production_checker_evidence_sha256
        )),
        ProofCertificateProductionCheckerEvidenceStatus::Malformed { reason } => {
            Some(format!("malformed: {reason}"))
        }
        ProofCertificateProductionCheckerEvidenceStatus::Missing => None,
    }
}

fn is_canonical_sha256_hex(value: &str) -> bool {
    value.len() == 64
        && value.bytes().all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}

fn format_binary_address(address: u64) -> String {
    format!("0x{address:x}")
}

fn format_formula_sort_declarations(
    declarations: &[BinaryVcFormulaSortDeclarationReport],
) -> String {
    declarations
        .iter()
        .map(|decl| format!("{}:{}", decl.name, decl.smtlib_sort))
        .collect::<Vec<_>>()
        .join(", ")
}

#[cfg(test)]
mod tests {
    use trust_types::{
        BinaryArtifactMetadata, BinaryFactConfidence, BinaryFactEvidence, BinaryFactSubject,
        BinarySourceProvenanceDiagnosticKind, BinaryTypeFact, BinaryVerificationSummary,
        Counterexample, CounterexampleValue, DecompileTarget, DecompiledOutput,
        PreservedSymbolicFormula, ProofCertificateStatus, ProofStrength,
        ReconstructionCandidateKind, ReconstructionSummary, ReconstructionValidationEvidence,
        ReconstructionValidationRecord, SerializableVc, Sort, SourceSpan, Symbol,
        TargetValidationBlocker, Ty, UNSUPPORTED_FAMILY_AARCH64_EXCEPTION_BOUNDARY,
        UNSUPPORTED_FAMILY_AARCH64_MEMORY_ORDER_BOUNDARY,
        UNSUPPORTED_FAMILY_BINARY_REPLAY_INSTRUCTION_IDENTITY, UnsupportedRecord, VcKind,
    };

    use super::*;

    fn origin(address: u64) -> BinaryOrigin {
        BinaryOrigin {
            binary_path: Some("fixtures/tiny".to_string()),
            function_entry: Some(0x401000),
            instruction_address: address,
            instruction_size: Some(4),
            encoding: Some(0x9090_9090),
            instruction_bytes: vec![0x90, 0x90, 0x90, 0x90],
            source: None,
        }
    }

    fn source_span() -> SourceSpan {
        SourceSpan {
            file: "src/recovered.rs".to_string(),
            line_start: 3,
            col_start: 5,
            line_end: 3,
            col_end: 17,
        }
    }

    fn sourceful_origin(address: u64) -> BinaryOrigin {
        BinaryOrigin { source: Some(source_span()), ..origin(address) }
    }

    fn unsupported_record(stage: &str, feature: &str, address: u64) -> UnsupportedRecord {
        UnsupportedRecord {
            stage: stage.to_string(),
            architecture: Some("x86_64".to_string()),
            origin: Some(origin(address)),
            opcode: Some("ud2".to_string()),
            operand: None,
            feature: feature.to_string(),
        }
    }

    fn unsupported_arch_record(
        stage: &str,
        architecture: &str,
        opcode: &str,
        feature: &str,
        address: u64,
    ) -> UnsupportedRecord {
        UnsupportedRecord {
            stage: stage.to_string(),
            architecture: Some(architecture.to_string()),
            origin: Some(origin(address)),
            opcode: Some(opcode.to_string()),
            operand: None,
            feature: feature.to_string(),
        }
    }

    #[test]
    fn decompilation_report_serializes_instruction_provenance() {
        let movabs_bytes = vec![0x48, 0xB8, 0x78, 0x56, 0x34, 0x12, 0, 0, 0, 0];
        let movabs_origin = BinaryOrigin {
            instruction_size: Some(10),
            encoding: Some(0xB8),
            instruction_bytes: movabs_bytes.clone(),
            ..origin(0x401000)
        };
        let artifact = DecompilationArtifact {
            functions: vec![DecompiledFunction {
                name: "return_imm".to_string(),
                entry: 0x401000,
                origin: Some(movabs_origin.clone()),
                instruction_provenance: vec![movabs_origin.clone()],
                ..Default::default()
            }],
            ..Default::default()
        };

        let report = build_binary_decompilation_report(&artifact);
        let provenance = report.functions[0]
            .instruction_provenance
            .first()
            .expect("instruction provenance should be reported");
        assert_eq!(provenance.instruction_address, 0x401000);
        assert_eq!(provenance.instruction_address_display, "0x401000");
        assert_eq!(provenance.instruction_size, Some(10));
        assert_eq!(provenance.encoding, Some(0xB8));
        assert_eq!(provenance.instruction_bytes, movabs_bytes);

        let json = serde_json::to_value(&report).expect("report should serialize");
        assert_eq!(
            json["functions"][0]["instruction_provenance"][0]["instruction_address_display"],
            "0x401000"
        );
        assert_eq!(
            json["functions"][0]["instruction_provenance"][0]["instruction_bytes"],
            serde_json::json!([0x48, 0xB8, 0x78, 0x56, 0x34, 0x12, 0, 0, 0, 0])
        );
    }

    fn checked_dispatch(id: &str, function: &str, address: u64) -> SolverDispatchRecord {
        SolverDispatchRecord {
            id: id.to_string(),
            function: Some(function.to_string()),
            origin: Some(origin(address)),
            solver: "ay".to_string(),
            status: SolverDispatchStatus::Unsat,
            certificate: ProofCertificateStatus::Checked {
                checker: production_checker_status(id),
                format: "lfsc".to_string(),
                sha256: Some(test_sha256_hex(id)),
            },
            replay: ReplayStatus::Replayed,
            binary_artifact_digest_identity: Some(exact_binary_digest_identity()),
            timeout_evidence: SolverTimeoutEvidence::from_timeouts(Some(250), None),
            ..Default::default()
        }
    }

    fn checked_source_provenance_dispatch(
        id: &str,
        function: &str,
        address: u64,
    ) -> SolverDispatchRecord {
        let mut dispatch = checked_dispatch(id, function, address);
        dispatch.origin = Some(sourceful_origin(address));
        dispatch.diagnostics = vec![
            format!(
                "checked proof-cert readback row accepted for proof-grade release; source_backpropagation_gate_sha256={}",
                test_sha256_hex("source gate")
            ),
            format!(
                "exact_replay_transcript_artifact_digest=accepted:sha256={}",
                test_sha256_hex("replay transcript")
            ),
        ];
        dispatch
    }

    fn schema_aware_symbolic_formula_consumer_diagnostic(
        formula: &PreservedSymbolicFormula,
    ) -> String {
        let target_marker = target_consumer_acceptance_markers(&formula.target)
            .into_iter()
            .next()
            .expect("target has an acceptance marker");
        let formula_json =
            serde_json::to_string(&formula.formula).expect("formula should serialize");
        let formula_smtlib = formula.formula.to_smtlib();
        let formula_sort = strict_formula_sort(&formula.formula)
            .expect("test formula should have a strict sort")
            .to_smtlib();
        let formula_evidence = formula.evidence();
        let formula_debug = format!("{:?}", formula.formula);
        let declarations = collect_formula_sort_declarations(&formula.formula)
            .into_iter()
            .map(|declaration| declaration.smtlib_declaration)
            .collect::<Vec<_>>()
            .join("; ");
        let function = formula.function.as_deref().unwrap_or("unknown");
        let block = formula.block.unwrap_or(usize::MAX);
        let statement_index = formula.statement_index.unwrap_or(usize::MAX);

        format!(
            "target={target_marker}; symbolic-formula-proof-consumer=accepted; target-consumer=accepted; trust_symbolic.formula=consumed; function={function}; block={block}; statement_index={statement_index}; location={}; formula.schema={}; formula_json={formula_json}; formula.smtlib2={formula_smtlib}; formula.sort={formula_sort}; formula.digest={}; formula.origin={}; formula.debug={formula_debug}; {declarations}",
            formula.location,
            formula_evidence.schema,
            formula_evidence.digest,
            formula_evidence.origin
        )
    }

    fn production_checker_status(value: &str) -> String {
        format!(
            "ay-cert-check@2026.04;production_checker_evidence_sha256={}",
            test_sha256_hex(&format!("{value}:production"))
        )
    }

    fn test_sha256_hex(value: &str) -> String {
        let mut hash = 0xcbf2_9ce4_8422_2325_u64;
        for byte in value.bytes() {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
        }
        format!("{hash:064x}")
    }

    fn exact_binary_metadata() -> BinaryArtifactMetadata {
        let digest = test_sha256_hex("fixtures/tiny/root");
        BinaryArtifactMetadata {
            path: Some("fixtures/tiny".to_string()),
            format: BinaryArtifactFormat::Elf,
            architecture: "x86_64".to_string(),
            entry_point: Some(0x401000),
            byte_len: Some(16),
            root_artifact_digest: Some(BinaryArtifactDigest::sha256(digest.clone())),
            selected_image: Some(BinarySelectedImageIdentity {
                file_offset: 0,
                file_size: 16,
                sha256: digest,
            }),
            ..Default::default()
        }
    }

    fn exact_binary_digest_identity() -> BinaryArtifactDigestIdentity {
        BinaryArtifactDigestIdentity::from_metadata(&exact_binary_metadata())
            .expect("exact test metadata should carry replay digest identity")
    }

    const REAL_DEBUG_BINARY_PATH: &str = "fixtures/real-debug/line-table.elf";
    const REAL_DEBUG_FUNCTION_ENTRY: u64 = 0x400010;
    const REAL_DEBUG_INSTRUCTION_SIZE: usize = 4;

    fn real_debug_line_program_fixture() -> Vec<u8> {
        decode_hex_fixture(include_str!("fixtures/real_debug_line_program_v4.hex"))
    }

    fn decode_hex_fixture(text: &str) -> Vec<u8> {
        let hex = text.chars().filter(|ch| !ch.is_whitespace()).collect::<String>();
        assert_eq!(hex.len() % 2, 0, "hex fixture must contain complete bytes");
        (0..hex.len())
            .step_by(2)
            .map(|index| {
                u8::from_str_radix(&hex[index..index + 2], 16)
                    .expect("hex fixture contains non-hex digit")
            })
            .collect()
    }

    fn build_real_debug_elf_fixture() -> Vec<u8> {
        let debug_line = real_debug_line_program_fixture();
        let text = [0x90_u8; 0x20];
        let shstrtab = b"\0.text\0.shstrtab\0.symtab\0.strtab\0.debug_info\0.debug_abbrev\0.debug_str\0.debug_line\0";
        let strtab = b"\0_start\0main\0";
        let mut buf = Vec::new();

        write_elf_header(&mut buf, 0);
        write_elf_program_header(&mut buf, 0);

        let text_off = buf.len() as u64;
        buf.extend_from_slice(&text);
        pad_to(&mut buf, 8);
        let shstrtab_off = buf.len() as u64;
        buf.extend_from_slice(shstrtab);
        pad_to(&mut buf, 8);
        let strtab_off = buf.len() as u64;
        buf.extend_from_slice(strtab);
        pad_to(&mut buf, 8);
        let symtab_off = buf.len() as u64;
        write_elf_sym(&mut buf, 0, 0, 0, 0, 0);
        write_elf_sym(&mut buf, 1, (1 << 4) | 2, 1, 0x400000, 16);
        write_elf_sym(&mut buf, 8, (1 << 4) | 2, 1, REAL_DEBUG_FUNCTION_ENTRY, 16);
        pad_to(&mut buf, 8);
        let debug_info_off = buf.len() as u64;
        let debug_abbrev_off = buf.len() as u64;
        let debug_str_off = buf.len() as u64;
        let debug_line_off = buf.len() as u64;
        buf.extend_from_slice(&debug_line);
        pad_to(&mut buf, 8);
        let shdr_off = buf.len() as u64;

        write_elf_shdr(&mut buf, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
        write_elf_shdr(&mut buf, 1, 1, 0x6, 0x400000, text_off, text.len() as u64, 0, 0, 16, 0);
        write_elf_shdr(&mut buf, 7, 3, 0, 0, shstrtab_off, shstrtab.len() as u64, 0, 0, 1, 0);
        write_elf_shdr(&mut buf, 17, 2, 0, 0, symtab_off, 72, 4, 1, 8, 24);
        write_elf_shdr(&mut buf, 25, 3, 0, 0, strtab_off, strtab.len() as u64, 0, 0, 1, 0);
        write_elf_shdr(&mut buf, 33, 1, 0, 0, debug_info_off, 0, 0, 0, 1, 0);
        write_elf_shdr(&mut buf, 45, 1, 0, 0, debug_abbrev_off, 0, 0, 0, 1, 0);
        write_elf_shdr(&mut buf, 59, 1, 0, 0, debug_str_off, 0, 0, 0, 1, 0);
        write_elf_shdr(&mut buf, 70, 1, 0, 0, debug_line_off, debug_line.len() as u64, 0, 0, 1, 0);

        patch_u64_le(&mut buf, 40, shdr_off);
        let file_size = buf.len() as u64;
        patch_u64_le(&mut buf, 0x40 + 32, file_size);
        patch_u64_le(&mut buf, 0x40 + 40, file_size);
        buf
    }

    fn write_elf_header(buf: &mut Vec<u8>, shdr_off: u64) {
        buf.extend_from_slice(&[0x7f, b'E', b'L', b'F']);
        buf.push(2);
        buf.push(1);
        buf.push(1);
        buf.push(0);
        buf.extend_from_slice(&[0u8; 8]);
        buf.extend_from_slice(&2u16.to_le_bytes());
        buf.extend_from_slice(&0x3e_u16.to_le_bytes());
        buf.extend_from_slice(&1u32.to_le_bytes());
        buf.extend_from_slice(&0x400000_u64.to_le_bytes());
        buf.extend_from_slice(&0x40_u64.to_le_bytes());
        buf.extend_from_slice(&shdr_off.to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes());
        buf.extend_from_slice(&64u16.to_le_bytes());
        buf.extend_from_slice(&56u16.to_le_bytes());
        buf.extend_from_slice(&1u16.to_le_bytes());
        buf.extend_from_slice(&64u16.to_le_bytes());
        buf.extend_from_slice(&9u16.to_le_bytes());
        buf.extend_from_slice(&2u16.to_le_bytes());
    }

    fn write_elf_program_header(buf: &mut Vec<u8>, file_size: u64) {
        buf.extend_from_slice(&1u32.to_le_bytes());
        buf.extend_from_slice(&5u32.to_le_bytes());
        buf.extend_from_slice(&0u64.to_le_bytes());
        buf.extend_from_slice(&0x400000_u64.to_le_bytes());
        buf.extend_from_slice(&0x400000_u64.to_le_bytes());
        buf.extend_from_slice(&file_size.to_le_bytes());
        buf.extend_from_slice(&file_size.to_le_bytes());
        buf.extend_from_slice(&0x1000_u64.to_le_bytes());
    }

    fn patch_u64_le(bytes: &mut [u8], offset: usize, value: u64) {
        bytes[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
    }

    fn pad_to(buf: &mut Vec<u8>, align: usize) {
        while !buf.len().is_multiple_of(align) {
            buf.push(0);
        }
    }

    fn write_elf_sym(buf: &mut Vec<u8>, name: u32, info: u8, shndx: u16, value: u64, size: u64) {
        buf.extend_from_slice(&name.to_le_bytes());
        buf.push(info);
        buf.push(0);
        buf.extend_from_slice(&shndx.to_le_bytes());
        buf.extend_from_slice(&value.to_le_bytes());
        buf.extend_from_slice(&size.to_le_bytes());
    }

    #[allow(clippy::too_many_arguments)]
    fn write_elf_shdr(
        buf: &mut Vec<u8>,
        name: u32,
        typ: u32,
        flags: u64,
        addr: u64,
        offset: u64,
        size: u64,
        link: u32,
        info: u32,
        align: u64,
        entsize: u64,
    ) {
        buf.extend_from_slice(&name.to_le_bytes());
        buf.extend_from_slice(&typ.to_le_bytes());
        buf.extend_from_slice(&flags.to_le_bytes());
        buf.extend_from_slice(&addr.to_le_bytes());
        buf.extend_from_slice(&offset.to_le_bytes());
        buf.extend_from_slice(&size.to_le_bytes());
        buf.extend_from_slice(&link.to_le_bytes());
        buf.extend_from_slice(&info.to_le_bytes());
        buf.extend_from_slice(&align.to_le_bytes());
        buf.extend_from_slice(&entsize.to_le_bytes());
    }

    fn real_debug_parse_fixture() -> trust_binary_parse::BinaryParseResult {
        let bytes = build_real_debug_elf_fixture();
        trust_binary_parse::parse_binary_with_identity(&bytes)
            .expect("real debug ELF fixture should parse")
    }

    fn real_debug_metadata(
        parsed: &trust_binary_parse::BinaryParseResult,
    ) -> BinaryArtifactMetadata {
        BinaryArtifactMetadata {
            path: Some(REAL_DEBUG_BINARY_PATH.to_string()),
            format: BinaryArtifactFormat::Elf,
            image_kind: trust_types::BinaryImageKind::Executable,
            architecture: parsed.binary.architecture.name().to_string(),
            entry_point: parsed.binary.entry_point,
            byte_len: Some(parsed.identity.artifact_size),
            build_id: parsed.binary.build_id().map(str::to_string),
            root_artifact_digest: Some(BinaryArtifactDigest::sha256(
                parsed.identity.artifact.value.clone(),
            )),
            selected_image: Some(BinarySelectedImageIdentity {
                file_offset: parsed.identity.selected_image.file_offset,
                file_size: parsed.identity.selected_image.file_size,
                sha256: parsed.identity.selected_image.sha256.clone(),
            }),
            segments: parsed
                .binary
                .segments()
                .iter()
                .map(|segment| trust_types::BinarySegment {
                    name: segment.name.clone(),
                    virtual_range: BinaryAddressRange {
                        start: segment.virtual_address,
                        end: segment.virtual_end(),
                    },
                    file_offset: segment.file_offset,
                    file_size: segment.file_size,
                    permissions: segment.permissions,
                })
                .collect(),
            symbols: parsed
                .binary
                .symbols
                .iter()
                .map(|symbol| trust_types::BinarySymbol {
                    name: symbol.name.clone(),
                    address: symbol.address,
                    size: Some(symbol.size),
                    kind: if symbol.is_function {
                        trust_types::BinarySymbolKind::Function
                    } else {
                        trust_types::BinarySymbolKind::Unknown
                    },
                })
                .collect(),
            ..Default::default()
        }
    }

    fn real_debug_source_provenance(
        parsed: &trust_binary_parse::BinaryParseResult,
    ) -> BinarySourceProvenanceSummary {
        let debug_source = parsed.binary.debug_source();
        BinarySourceProvenanceSummary {
            status: debug_source.status.name().to_string(),
            exact_mapping_count: debug_source.exact_mapping_count,
            ambiguous_mapping_count: debug_source.ambiguous_mapping_count,
            diagnostics: debug_source.diagnostics.clone(),
            source_backpropagation_allowed: debug_source.status
                == trust_binary_parse::DebugSourceProvenanceStatus::Exact
                && debug_source.exact_mapping_count > 0
                && debug_source.ambiguous_mapping_count == 0,
        }
    }

    fn real_debug_source_span(mapping: &trust_binary_parse::SourceMappingInfo) -> SourceSpan {
        let line = u32::try_from(mapping.line).expect("fixture line fits u32");
        let col_start = u32::try_from(mapping.column.max(1)).expect("fixture column fits u32");
        SourceSpan {
            file: mapping.file.clone(),
            line_start: line,
            col_start,
            line_end: line,
            col_end: col_start.saturating_add(1),
        }
    }

    fn real_debug_origin(
        parsed: &trust_binary_parse::BinaryParseResult,
        mapping: &trust_binary_parse::SourceMappingInfo,
    ) -> BinaryOrigin {
        let instruction_bytes = parsed
            .binary
            .bytes_at_va(mapping.binary_address, REAL_DEBUG_INSTRUCTION_SIZE)
            .expect("fixture source mapping should point into .text")
            .to_vec();
        let encoding = (instruction_bytes.len() == 4).then(|| {
            u32::from_le_bytes([
                instruction_bytes[0],
                instruction_bytes[1],
                instruction_bytes[2],
                instruction_bytes[3],
            ])
        });
        BinaryOrigin {
            binary_path: Some(REAL_DEBUG_BINARY_PATH.to_string()),
            function_entry: Some(REAL_DEBUG_FUNCTION_ENTRY),
            instruction_address: mapping.binary_address,
            instruction_size: Some(REAL_DEBUG_INSTRUCTION_SIZE as u8),
            encoding,
            instruction_bytes,
            source: Some(real_debug_source_span(mapping)),
        }
    }

    fn checked_real_debug_dispatches(
        parsed: &trust_binary_parse::BinaryParseResult,
        digest_identity: BinaryArtifactDigestIdentity,
    ) -> Vec<SolverDispatchRecord> {
        let source_gate_sha256 = test_sha256_hex("real debug source gate");
        parsed
            .binary
            .source_mappings()
            .iter()
            .enumerate()
            .map(|(index, mapping)| {
                let id = format!("real-debug-source-provenance:vc{index}");
                SolverDispatchRecord {
                    id: id.clone(),
                    function: Some("main".to_string()),
                    origin: Some(real_debug_origin(parsed, mapping)),
                    solver: "ay".to_string(),
                    status: SolverDispatchStatus::Unsat,
                    certificate: ProofCertificateStatus::Checked {
                        checker: production_checker_status(&id),
                        format: "lfsc".to_string(),
                        sha256: Some(test_sha256_hex(&id)),
                    },
                    replay: ReplayStatus::Replayed,
                    binary_artifact_digest_identity: Some(digest_identity.clone()),
                    timeout_evidence: SolverTimeoutEvidence::from_timeouts(Some(250), None),
                    diagnostics: vec![
                        format!(
                            "checked proof-cert readback row accepted for proof-grade release; source_backpropagation_gate_sha256={source_gate_sha256}"
                        ),
                        format!(
                            "exact_replay_transcript_artifact_digest=accepted:sha256={}",
                            test_sha256_hex(&format!("{id}:replay"))
                        ),
                    ],
                    ..Default::default()
                }
            })
            .collect()
    }

    fn real_debug_decompilation_artifact() -> DecompilationArtifact {
        let parsed = real_debug_parse_fixture();
        let binary = real_debug_metadata(&parsed);
        let digest_identity = BinaryArtifactDigestIdentity::from_metadata(&binary)
            .expect("real debug fixture should carry digest identity");
        let dispatches = checked_real_debug_dispatches(&parsed, digest_identity);
        let mut verification = verification_summary(dispatches.len(), dispatches);
        verification.proof_certificate = verification.solver_dispatch[0].certificate.clone();
        DecompilationArtifact {
            binary,
            verification,
            reconstruction: validated_reconstruction(),
            source_provenance: real_debug_source_provenance(&parsed),
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        }
    }

    fn checked_certificate_only_dispatch(
        id: &str,
        function: &str,
        address: u64,
    ) -> SolverDispatchRecord {
        let mut dispatch = checked_dispatch(id, function, address);
        dispatch.replay = ReplayStatus::NotAttempted;
        dispatch
    }

    fn raw_unchecked_unreplayed_dispatch(
        id: &str,
        function: &str,
        address: u64,
    ) -> SolverDispatchRecord {
        SolverDispatchRecord {
            id: id.to_string(),
            function: Some(function.to_string()),
            origin: Some(origin(address)),
            solver: "ay".to_string(),
            status: SolverDispatchStatus::Unsat,
            result: Some(VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(b"raw solver proof bytes".to_vec()),
                solver_warnings: None,
                native_proof_envelope: None,
            }),
            certificate: ProofCertificateStatus::Present {
                format: "lfsc".to_string(),
                sha256: Some(format!("{id}-raw-sha256")),
                artifact_path: None,
            },
            replay: ReplayStatus::NotAttempted,
            ..Default::default()
        }
    }

    fn manifest_candidate_dispatch(id: &str, function: &str, address: u64) -> SolverDispatchRecord {
        SolverDispatchRecord {
            id: id.to_string(),
            function: Some(function.to_string()),
            origin: Some(origin(address)),
            solver: "ay".to_string(),
            status: SolverDispatchStatus::Unsat,
            certificate: ProofCertificateStatus::Present {
                format: "checked-binary-certificate@1".to_string(),
                sha256: Some(format!("{id}-manifest-sha256")),
                artifact_path: Some(
                    "checked-cert-manifest.json#certificates/main.vc0.checked.json".to_string(),
                ),
            },
            replay: ReplayStatus::Replayed,
            binary_artifact_digest_identity: Some(exact_binary_digest_identity()),
            ..Default::default()
        }
    }

    fn verification_summary(
        required_vcs: usize,
        dispatches: Vec<SolverDispatchRecord>,
    ) -> BinaryVerificationSummary {
        let mut summary = BinaryVerificationSummary::from_solver_dispatch(dispatches);
        summary.total_vcs = required_vcs;
        summary.trust_level = TrustLevel::ProofGrade;
        summary
    }

    fn proof_grade_function(
        name: &str,
        entry: u64,
        required_vcs: usize,
        dispatches: Vec<SolverDispatchRecord>,
    ) -> DecompiledFunction {
        DecompiledFunction {
            name: name.to_string(),
            entry,
            verification: verification_summary(required_vcs, dispatches),
            output: Some(validated_output()),
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        }
    }

    fn validated_output() -> DecompiledOutput {
        DecompiledOutput {
            validation: ReconstructionValidationStatus::Validated,
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        }
    }

    fn validated_reconstruction() -> ReconstructionSummary {
        ReconstructionSummary {
            validation: ReconstructionValidationStatus::Validated,
            trust_level: TrustLevel::ProofGrade,
            outputs: vec![validated_output()],
            ..Default::default()
        }
    }

    fn validated_reconstruction_with_target_semantics_blocker() -> ReconstructionSummary {
        ReconstructionSummary {
            target: DecompileTarget::TrustIr,
            validation: ReconstructionValidationStatus::Validated,
            trust_level: TrustLevel::ProofGrade,
            outputs: vec![DecompiledOutput {
                target: DecompileTarget::TrustIr,
                validation: ReconstructionValidationStatus::Validated,
                trust_level: TrustLevel::ProofGrade,
                target_validation_blockers: vec![TargetValidationBlocker {
                    target: DecompileTarget::TrustIr,
                    function: Some("main".to_string()),
                    code: "binary-provenance-not-consumed-by-target-semantics".to_string(),
                    stage: "trust-wasm-bridge::target-validation".to_string(),
                    feature: "binary-provenance-not-consumed-by-target-semantics".to_string(),
                    reason: "canonical input claimed target_semantics_consumed=true, but target semantics have not consumed binary provenance".to_string(),
                    origin: Some(origin(0x401010)),
                    diagnostics: vec![
                        "binary_provenance.input_claim.target_semantics_consumed=true".to_string(),
                        "binary_provenance.consumption.target_semantics_consumed=false"
                            .to_string(),
                        "proof-grade=false".to_string(),
                    ],
                }],
                ..Default::default()
            }],
            ..Default::default()
        }
    }

    fn exact_source_provenance() -> BinarySourceProvenanceSummary {
        BinarySourceProvenanceSummary {
            status: "exact".to_string(),
            exact_mapping_count: 2,
            ambiguous_mapping_count: 0,
            diagnostics: vec![],
            source_backpropagation_allowed: true,
        }
    }

    fn exact_source_provenance_one() -> BinarySourceProvenanceSummary {
        BinarySourceProvenanceSummary { exact_mapping_count: 1, ..exact_source_provenance() }
    }

    #[test]
    fn binary_source_provenance_artifact_fixture_carries_checked_exact_handoff() {
        let dispatch =
            checked_source_provenance_dispatch("source-provenance:vc0", "main", 0x401010);
        let mut verification = verification_summary(1, vec![dispatch]);
        verification.proof_certificate = verification.solver_dispatch[0].certificate.clone();
        let artifact = DecompilationArtifact {
            binary: exact_binary_metadata(),
            verification,
            reconstruction: validated_reconstruction(),
            source_provenance: exact_source_provenance_one(),
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        };

        let report = build_binary_source_provenance_artifact_report(&artifact);
        let json = serde_json::to_value(&report).expect("source provenance artifact serializes");
        let expected: serde_json::Value = serde_json::from_str(include_str!(
            "fixtures/binary_source_provenance_handoff_golden.json"
        ))
        .expect("golden source provenance handoff fixture parses");

        assert!(report.blockers.is_empty(), "{:?}", report.blockers);
        assert_eq!(report.kind, "binary_source_provenance");
        assert_eq!(report.canonical_binary_provenance.records.len(), 1);
        assert_eq!(
            report.canonical_binary_provenance.records[0].origin.binary_path.as_deref(),
            Some("fixtures/tiny")
        );
        assert_eq!(report.canonical_binary_provenance.records[0].source_status, "exact");
        assert_eq!(
            report.canonical_binary_provenance.records[0].provenance_status,
            "checked_exact"
        );
        assert_eq!(
            report.canonical_binary_provenance.records[0]
                .proof_evidence
                .source_backpropagation_gate_sha256,
            test_sha256_hex("source gate")
        );
        assert!(
            report.canonical_artifact_profile_allows_acceptance(),
            "{:?}",
            report.canonical_artifact_profile_blockers()
        );
        if let Ok(write_to) = std::env::var("TRUST_REPORT_REGEN_SOURCE_PROVENANCE_GOLDEN") {
            let pretty =
                serde_json::to_string_pretty(&json).expect("source provenance JSON regenerate");
            std::fs::write(&write_to, format!("{pretty}\n")).unwrap_or_else(|e| {
                panic!("could not write regenerated golden to {write_to}: {e}")
            });
            eprintln!("REGENERATED GOLDEN: {write_to}");
        }
        let expected_report: BinarySourceProvenanceArtifactReport =
            serde_json::from_value(expected.clone())
                .expect("golden source provenance handoff fixture deserializes");
        assert!(
            expected_report.canonical_artifact_profile_allows_acceptance(),
            "{:?}",
            expected_report.canonical_artifact_profile_blockers()
        );
        assert_eq!(json, expected);
    }

    #[test]
    fn binary_source_provenance_artifact_real_debug_fixture_carries_checked_exact_handoff() {
        let artifact = real_debug_decompilation_artifact();

        assert_eq!(artifact.source_provenance.status, "exact");
        assert_eq!(artifact.source_provenance.exact_mapping_count, 2);
        assert!(artifact.source_provenance.source_backpropagation_allowed);

        let report = build_binary_source_provenance_artifact_report(&artifact);
        let json = serde_json::to_value(&report).expect("source provenance artifact serializes");

        assert!(report.blockers.is_empty(), "{:?}", report.blockers);
        assert_eq!(report.kind, "binary_source_provenance");
        assert_eq!(report.canonical_binary_provenance.records.len(), 2);
        let first = &report.canonical_binary_provenance.records[0];
        assert_eq!(first.origin.binary_path.as_deref(), Some(REAL_DEBUG_BINARY_PATH));
        assert_eq!(first.origin.function_entry, Some(REAL_DEBUG_FUNCTION_ENTRY));
        assert_eq!(first.origin.instruction_address, REAL_DEBUG_FUNCTION_ENTRY);
        assert_eq!(first.origin.instruction_size, Some(REAL_DEBUG_INSTRUCTION_SIZE as u8));
        assert_eq!(first.origin.instruction_bytes, vec![0x90, 0x90, 0x90, 0x90]);
        assert_eq!(
            first.origin.source.as_ref().expect("debug source span").file,
            "src/real_debug.rs"
        );
        assert_eq!(
            first
                .artifact_digest_identity
                .root_artifact_digest
                .as_ref()
                .expect("root digest")
                .algorithm,
            "sha256"
        );
        assert!(
            report.canonical_artifact_profile_allows_acceptance(),
            "{:?}",
            report.canonical_artifact_profile_blockers()
        );

        let expected: serde_json::Value = serde_json::from_str(include_str!(
            "fixtures/binary_source_provenance_real_debug_golden.json"
        ))
        .expect("golden real debug source provenance handoff fixture parses");
        let expected_report: BinarySourceProvenanceArtifactReport =
            serde_json::from_value(expected.clone())
                .expect("golden real debug source provenance handoff fixture deserializes");
        assert!(
            expected_report.canonical_artifact_profile_allows_acceptance(),
            "{:?}",
            expected_report.canonical_artifact_profile_blockers()
        );

        if std::env::var_os("TRUST_REPORT_PRINT_REAL_DEBUG_SOURCE_PROVENANCE").is_some() {
            eprintln!(
                "{}",
                serde_json::to_string_pretty(&json)
                    .expect("source provenance JSON should serialize")
            );
        }
        if let Ok(write_to) =
            std::env::var("TRUST_REPORT_REGEN_REAL_DEBUG_SOURCE_PROVENANCE_GOLDEN")
        {
            let pretty = serde_json::to_string_pretty(&json)
                .expect("real-debug source provenance JSON regenerate");
            std::fs::write(&write_to, format!("{pretty}\n")).unwrap_or_else(|e| {
                panic!("could not write regenerated golden to {write_to}: {e}")
            });
            eprintln!("REGENERATED GOLDEN: {write_to}");
        }
        assert_eq!(json, expected);
    }

    #[test]
    fn binary_source_provenance_artifact_profile_rejects_noncanonical_and_stale_fields() {
        let fixture: serde_json::Value = serde_json::from_str(include_str!(
            "fixtures/binary_source_provenance_handoff_golden.json"
        ))
        .expect("golden source provenance handoff fixture parses");

        let mut missing_schema_version = fixture.clone();
        missing_schema_version.as_object_mut().expect("fixture object").remove("schema_version");
        let err =
            serde_json::from_value::<BinarySourceProvenanceArtifactReport>(missing_schema_version)
                .expect_err("schema_version is required");
        assert!(err.to_string().contains("schema_version"));

        let mut stale_artifact_schema = fixture.clone();
        stale_artifact_schema["schema_version"] =
            serde_json::json!("trust-report.binary-source-provenance-artifact.v0");
        let stale_artifact: BinarySourceProvenanceArtifactReport =
            serde_json::from_value(stale_artifact_schema)
                .expect("stale schema fixture remains typed JSON");
        let stale_blockers = stale_artifact.canonical_artifact_profile_blockers();
        assert!(
            stale_blockers.iter().any(|blocker| blocker.contains("schema_version")
                && blocker.contains("binary-source-provenance-artifact.v0")),
            "{stale_blockers:?}"
        );
        assert!(
            stale_blockers
                .iter()
                .any(|blocker| blocker.contains("source_provenance_artifact_digest mismatch")),
            "{stale_blockers:?}"
        );

        let mut noncanonical_artifact_digest = fixture.clone();
        noncanonical_artifact_digest["source_provenance_artifact_digest"] = serde_json::json!(
            "sha256:EF544A80F219118F18889CE0657CDE20C37808676B9A2922B879E4DD7579C05C"
        );
        let noncanonical_artifact: BinarySourceProvenanceArtifactReport =
            serde_json::from_value(noncanonical_artifact_digest)
                .expect("noncanonical digest fixture remains typed JSON");
        let noncanonical_blockers = noncanonical_artifact.canonical_artifact_profile_blockers();
        assert!(
            noncanonical_blockers.iter().any(|blocker| {
                blocker.contains(
                    "source_provenance_artifact_digest is not canonical lowercase sha256:<hex>",
                )
            }),
            "{noncanonical_blockers:?}"
        );

        let mut stale_gate_schema = fixture.clone();
        stale_gate_schema["source_backpropagation_gate"]["schema_version"] =
            serde_json::json!("trust-proof-cert.source-backpropagation-gate.v0");
        let stale_gate: BinarySourceProvenanceArtifactReport =
            serde_json::from_value(stale_gate_schema)
                .expect("stale gate fixture remains typed JSON");
        let stale_gate_blockers = stale_gate.canonical_artifact_profile_blockers();
        assert!(
            stale_gate_blockers.iter().any(|blocker| {
                blocker.contains("source_backpropagation_gate: schema_version")
                    && blocker.contains("source-backpropagation-gate.v0")
            }),
            "{stale_gate_blockers:?}"
        );

        let mut noncanonical_proof_digest = fixture.clone();
        noncanonical_proof_digest["canonical_binary_provenance"]["records"][0]["proof_evidence"]
            ["checked_certificate_sha256"] =
            serde_json::json!(test_sha256_hex("source-provenance:vc0").to_uppercase());
        let noncanonical_proof: BinarySourceProvenanceArtifactReport =
            serde_json::from_value(noncanonical_proof_digest)
                .expect("noncanonical proof fixture remains typed JSON");
        let noncanonical_proof_blockers = noncanonical_proof.canonical_artifact_profile_blockers();
        assert!(
            noncanonical_proof_blockers.iter().any(|blocker| {
                blocker.contains(
                    "proof_evidence: checked_certificate_sha256 is not canonical lowercase SHA-256 hex",
                )
            }),
            "{noncanonical_proof_blockers:?}"
        );

        let mut missing_gate_acceptance = fixture.clone();
        missing_gate_acceptance["source_backpropagation_gate"]
            .as_object_mut()
            .expect("source gate object")
            .remove("replay_grade_artifact_identity");
        let err =
            serde_json::from_value::<BinarySourceProvenanceArtifactReport>(missing_gate_acceptance)
                .expect_err("source gate acceptance fields are required");
        assert!(err.to_string().contains("replay_grade_artifact_identity"));

        let err = serde_json::from_value::<BinaryReplayDigestIdentityReport>(serde_json::json!({
            "proof_grade_ready": true
        }))
        .expect_err("replay identity required flag is not implicitly defaulted");
        assert!(err.to_string().contains("required"));

        let err =
            serde_json::from_value::<BinaryCheckedCertificateIdentityReport>(serde_json::json!({
                "required": true,
                "checked_identity_ready": true,
                "status": "checked",
                "production_checker_evidence": {
                    "status": "present",
                    "evidence": {
                        "checker": "ay-cert-check",
                        "checker_version": "2026.04",
                        "production_checker_evidence_sha256": test_sha256_hex("source-provenance:vc0:production")
                    }
                },
                "production_checked": true
            }))
            .expect_err("checked certificate proof_grade_ready is not implicitly defaulted");
        assert!(err.to_string().contains("proof_grade_ready"));
    }

    #[test]
    fn binary_source_backpropagation_gate_accepts_only_exact_evidence() {
        let artifact = DecompilationArtifact {
            binary: exact_binary_metadata(),
            verification: verification_summary(
                1,
                vec![checked_dispatch("source-backprop:vc0", "main", 0x401010)],
            ),
            reconstruction: validated_reconstruction(),
            source_provenance: exact_source_provenance(),
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        };

        let report = build_binary_decompilation_report(&artifact);

        assert!(report.proof_grade_gate.accepted);
        assert!(report.source_backpropagation_gate.accepted);
        assert_eq!(report.source_backpropagation_gate.status, "accepted");
        assert!(report.source_backpropagation_gate.missing_labels.is_empty());
        assert!(report.source_backpropagation_gate.blockers.is_empty());

        let json = serde_json::to_value(&report).expect("report serializes");
        assert_eq!(json["source_backpropagation_gate"]["accepted"], true);
        assert_eq!(
            json["source_backpropagation_gate"]["required_labels"],
            serde_json::json!([
                "missing_reconstruction",
                "exact_source_provenance",
                "type_ownership",
                "target_validation",
                "checked_certificate_identity",
                "replay_identity"
            ])
        );

        let text = format_binary_decompilation_report(&report);
        assert!(text.contains("Source backpropagation gate: accepted"));
        assert!(text.contains("missing=[]"));
    }

    #[test]
    fn binary_source_backpropagation_gate_surfaces_type_ownership_blockers() {
        let artifact = DecompilationArtifact {
            binary: exact_binary_metadata(),
            verification: verification_summary(
                1,
                vec![checked_dispatch("source-backprop:vc0", "main", 0x401010)],
            ),
            reconstruction: validated_reconstruction(),
            source_provenance: exact_source_provenance(),
            trust_level: TrustLevel::ProofGrade,
            type_facts: vec![BinaryTypeFact {
                subject: BinaryFactSubject::Parameter { function: "main".to_string(), index: 0 },
                recovered_ty: Some(Ty::u64()),
                origin: Some(BinaryOrigin {
                    source: Some(SourceSpan::binary_address(0x401010)),
                    ..origin(0x401010)
                }),
                evidence: BinaryFactEvidence::DebugInfo,
                confidence: BinaryFactConfidence::Validated,
                ..Default::default()
            }],
            ..Default::default()
        };

        let report = build_binary_decompilation_report(&artifact);

        assert!(!report.source_backpropagation_gate.accepted);
        assert_eq!(
            report.source_backpropagation_gate.missing_labels,
            vec![SOURCE_BACKPROPAGATION_TYPE_OWNERSHIP.to_string()]
        );
        assert!(report.source_backpropagation_gate.blockers.iter().any(|blocker| {
            blocker.label == SOURCE_BACKPROPAGATION_TYPE_OWNERSHIP
                && blocker.detail.contains("binary-address-only")
        }));
        let text = format_binary_decompilation_report(&report);
        assert!(text.contains("Source backpropagation blocker: type_ownership"));
    }

    #[test]
    fn preserved_symbolic_formula_without_consumer_rejects_proof_grade() {
        let symbolic_formula = Formula::BvAdd(
            Box::new(Formula::Var("x0".to_string(), Sort::BitVec(64))),
            Box::new(Formula::BitVec { value: 1, width: 64 }),
            64,
        );
        let artifact = DecompilationArtifact {
            binary: exact_binary_metadata(),
            verification: verification_summary(
                1,
                vec![checked_dispatch("symbolic-formula:vc0", "main", 0x401030)],
            ),
            reconstruction: ReconstructionSummary {
                target: DecompileTarget::TrustIr,
                validation: ReconstructionValidationStatus::Validated,
                trust_level: TrustLevel::ProofGrade,
                outputs: vec![DecompiledOutput {
                    target: DecompileTarget::TrustIr,
                    validation: ReconstructionValidationStatus::Validated,
                    trust_level: TrustLevel::ProofGrade,
                    preserved_symbolic_formulas: vec![PreservedSymbolicFormula {
                        target: DecompileTarget::TrustIr,
                        function: Some("main".to_string()),
                        block: Some(0),
                        statement_index: Some(1),
                        location: "bb0[1].rvalue".to_string(),
                        formula: symbolic_formula.clone(),
                    }],
                    ..Default::default()
                }],
                ..Default::default()
            },
            source_provenance: exact_source_provenance(),
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        };

        let report = build_binary_decompilation_report(&artifact);
        let json = serde_json::to_value(&report).expect("report serializes");
        let text = format_binary_decompilation_report(&report);

        assert!(!report.proof_grade_gate.accepted);
        assert!(report.proof_grade_gate.reconstruction_validated);
        assert!(!report.proof_grade_gate.target_semantics_consumed);
        assert_eq!(report.proof_grade_gate.target_validation_blockers, 0);
        assert_eq!(report.proof_grade_gate.preserved_symbolic_formulas, 1);
        assert!(!report.proof_grade_gate.symbolic_formulas_consumed_by_proof_model);
        assert!(report.proof_grade_gate.rejections.iter().any(|rejection| {
            matches!(
                rejection,
                BinaryProofGradeGateRejectionReport::SymbolicFormulasNotConsumed {
                    target,
                    count: 1
                } if *target == DecompileTarget::TrustIr
            )
        }));
        assert_eq!(report.reconstruction.preserved_symbolic_formula_count, 1);
        assert_eq!(report.reconstruction.symbolic_formula_consumer_status, "blocked");
        assert!(
            report
                .reconstruction
                .symbolic_formula_consumer_blockers
                .iter()
                .any(|blocker| blocker.contains("missing target proof consumer"))
        );
        assert_eq!(
            report.reconstruction.preserved_symbolic_formulas[0].proof_consumer_status,
            "blocked"
        );
        assert!(
            report.reconstruction.preserved_symbolic_formulas[0]
                .proof_consumer_blockers
                .iter()
                .any(|blocker| blocker.contains("trust_symbolic.formula"))
        );
        assert_eq!(report.unresolved_blockers.by_family.get("reconstruction").copied(), Some(2));
        assert!(report.unresolved_blockers.entries.iter().any(|entry| {
            entry.family == "reconstruction"
                && entry.feature == "trust_symbolic_formula_not_consumed"
                && entry.reason.contains("trust_symbolic.formula")
        }));
        assert!(report.source_backpropagation_gate.blockers.iter().any(|blocker| {
            blocker.label == SOURCE_BACKPROPAGATION_TARGET_VALIDATION
                && blocker.detail.contains("preserved_symbolic_formulas=1")
        }));

        assert_eq!(json["proof_grade_gate"]["accepted"], false);
        assert_eq!(json["proof_grade_gate"]["preserved_symbolic_formulas"], 1);
        assert_eq!(json["proof_grade_gate"]["symbolic_formulas_consumed_by_proof_model"], false);
        assert_eq!(json["reconstruction"]["preserved_symbolic_formula_count"], 1);
        assert_eq!(json["reconstruction"]["symbolic_formula_consumer_status"], "blocked");
        assert_eq!(
            json["reconstruction"]["preserved_symbolic_formulas"][0]["proof_consumer_status"],
            "blocked"
        );
        let json_formula: Formula = serde_json::from_value(
            json["reconstruction"]["preserved_symbolic_formulas"][0]["formula"].clone(),
        )
        .expect("preserved formula remains structured");
        assert_eq!(json_formula, symbolic_formula);

        assert!(text.contains("preserved_symbolic_formulas=1"));
        assert!(text.contains("symbolic_formulas_consumed=false"));
        assert!(text.contains("symbolic_formula_consumer_status=blocked"));
        assert!(text.contains("proof_consumer=blocked"));
        assert!(text.contains("symbolic formula consumer blocker"));
        assert!(text.contains("trust_symbolic.formula payloads not proof-consumed"));
    }

    #[test]
    fn preserved_symbolic_formula_with_consumer_evidence_populates_proof_gate_reports() {
        let symbolic_formula = Formula::BvAdd(
            Box::new(Formula::Var("x0".to_string(), Sort::BitVec(64))),
            Box::new(Formula::BitVec { value: 1, width: 64 }),
            64,
        );
        let preserved_formula = PreservedSymbolicFormula {
            target: DecompileTarget::TrustCg,
            function: Some("main".to_string()),
            block: Some(0),
            statement_index: Some(1),
            location: "main::bb0::stmt1".to_string(),
            formula: symbolic_formula.clone(),
        };
        let artifact = DecompilationArtifact {
            binary: exact_binary_metadata(),
            verification: verification_summary(
                1,
                vec![checked_dispatch("symbolic-formula-consumed:vc0", "main", 0x401030)],
            ),
            reconstruction: ReconstructionSummary {
                target: DecompileTarget::TrustCg,
                validation: ReconstructionValidationStatus::Validated,
                trust_level: TrustLevel::ProofGrade,
                outputs: vec![DecompiledOutput {
                    target: DecompileTarget::TrustCg,
                    validation: ReconstructionValidationStatus::Validated,
                    trust_level: TrustLevel::ProofGrade,
                    preserved_symbolic_formulas: vec![preserved_formula.clone()],
                    diagnostics: vec![schema_aware_symbolic_formula_consumer_diagnostic(
                        &preserved_formula,
                    )],
                    ..Default::default()
                }],
                ..Default::default()
            },
            source_provenance: exact_source_provenance(),
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        };

        let report = build_binary_decompilation_report(&artifact);
        let evidence = build_binary_decompilation_proof_evidence_report(&artifact);
        let gate_report = build_binary_decompilation_proof_grade_gate_report(&artifact);
        let json = serde_json::to_value(&report).expect("report serializes");

        assert!(report.proof_grade_gate.accepted, "{:?}", report.proof_grade_gate.rejections);
        assert!(report.proof_grade_gate.target_semantics_consumed);
        assert_eq!(report.proof_grade_gate.preserved_symbolic_formulas, 1);
        assert!(report.proof_grade_gate.symbolic_formulas_consumed_by_proof_model);
        assert!(!report.proof_grade_gate.rejections.iter().any(|rejection| matches!(
            rejection,
            BinaryProofGradeGateRejectionReport::SymbolicFormulasNotConsumed { .. }
        )));
        assert_eq!(report.reconstruction.preserved_symbolic_formula_count, 1);
        assert_eq!(report.reconstruction.symbolic_formula_consumer_status, "accepted");
        assert_eq!(
            report.reconstruction.preserved_symbolic_formulas[0].proof_consumer_status,
            "accepted"
        );
        assert_eq!(
            report.reconstruction.preserved_symbolic_formulas[0].smtlib,
            "(bvadd x0 (_ bv1 64))"
        );
        assert_eq!(
            report.reconstruction.preserved_symbolic_formulas[0].smtlib_sort,
            "(_ BitVec 64)"
        );
        assert_eq!(
            report.reconstruction.preserved_symbolic_formulas[0].sort_declarations[0]
                .smtlib_declaration,
            "(declare-fun x0 () (_ BitVec 64))"
        );
        assert!(report.reconstruction.symbolic_formula_consumer_blockers.is_empty());
        assert!(!report.unresolved_blockers.entries.iter().any(|entry| {
            entry.family == "reconstruction"
                && entry.feature == "trust_symbolic_formula_not_consumed"
        }));

        assert!(evidence.proof_grade_gate.accepted);
        assert_eq!(evidence.proof_grade_gate.preserved_symbolic_formulas, 1);
        assert!(evidence.proof_grade_gate.symbolic_formulas_consumed_by_proof_model);
        assert!(gate_report.artifact.accepted);
        assert_eq!(gate_report.artifact.preserved_symbolic_formulas, 1);
        assert!(gate_report.artifact.symbolic_formulas_consumed_by_proof_model);

        assert_eq!(json["proof_grade_gate"]["preserved_symbolic_formulas"], 1);
        assert_eq!(json["proof_grade_gate"]["symbolic_formulas_consumed_by_proof_model"], true);
        assert_eq!(json["reconstruction"]["preserved_symbolic_formula_count"], 1);
        assert_eq!(json["reconstruction"]["symbolic_formula_consumer_status"], "accepted");
        assert_eq!(
            json["reconstruction"]["preserved_symbolic_formulas"][0]["proof_consumer_status"],
            "accepted"
        );
        assert_eq!(
            json["reconstruction"]["preserved_symbolic_formulas"][0]["smtlib"],
            "(bvadd x0 (_ bv1 64))"
        );
        assert_eq!(
            json["reconstruction"]["preserved_symbolic_formulas"][0]["sort_declarations"][0]["smtlib_declaration"],
            "(declare-fun x0 () (_ BitVec 64))"
        );
        let json_formula: Formula = serde_json::from_value(
            json["reconstruction"]["preserved_symbolic_formulas"][0]["formula"].clone(),
        )
        .expect("preserved formula remains structured");
        assert_eq!(json_formula, symbolic_formula);
    }

    #[test]
    fn preserved_symbolic_formula_consumer_requires_smtlib_declarations() {
        let symbolic_formula = Formula::BvAdd(
            Box::new(Formula::Var("x0".to_string(), Sort::BitVec(64))),
            Box::new(Formula::BitVec { value: 1, width: 64 }),
            64,
        );
        let preserved_formula = PreservedSymbolicFormula {
            target: DecompileTarget::TrustCg,
            function: Some("main".to_string()),
            block: Some(0),
            statement_index: Some(1),
            location: "main::bb0::stmt1".to_string(),
            formula: symbolic_formula,
        };
        let mut diagnostic = schema_aware_symbolic_formula_consumer_diagnostic(&preserved_formula);
        diagnostic = diagnostic
            .replace("; (declare-fun x0 () (_ BitVec 64))", "")
            .replace("(declare-fun x0 () (_ BitVec 64))", "");

        let artifact = DecompilationArtifact {
            binary: exact_binary_metadata(),
            verification: verification_summary(
                1,
                vec![checked_dispatch("symbolic-formula-decl-missing:vc0", "main", 0x401030)],
            ),
            reconstruction: ReconstructionSummary {
                target: DecompileTarget::TrustCg,
                validation: ReconstructionValidationStatus::Validated,
                trust_level: TrustLevel::ProofGrade,
                outputs: vec![DecompiledOutput {
                    target: DecompileTarget::TrustCg,
                    validation: ReconstructionValidationStatus::Validated,
                    trust_level: TrustLevel::ProofGrade,
                    preserved_symbolic_formulas: vec![preserved_formula],
                    diagnostics: vec![diagnostic],
                    ..Default::default()
                }],
                ..Default::default()
            },
            source_provenance: exact_source_provenance(),
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        };

        let report = build_binary_decompilation_report(&artifact);
        let json = serde_json::to_value(&report).expect("report serializes");

        assert!(!report.proof_grade_gate.accepted);
        assert!(!report.proof_grade_gate.symbolic_formulas_consumed_by_proof_model);
        assert_eq!(
            report.reconstruction.preserved_symbolic_formulas[0].proof_consumer_status,
            "blocked"
        );
        assert!(
            report
                .reconstruction
                .symbolic_formula_consumer_blockers
                .iter()
                .any(|blocker| { blocker.contains("did not consume smtlib declaration for x0") })
        );
        assert_eq!(
            json["reconstruction"]["preserved_symbolic_formulas"][0]["sort_declarations"][0]["smtlib_declaration"],
            "(declare-fun x0 () (_ BitVec 64))"
        );
    }

    #[test]
    fn preserved_symbolic_formula_rejects_stale_cross_target_consumer_evidence() {
        let symbolic_formula = Formula::Bool(true);
        let stale_acceptance = "trust-cg target proof consumer accepted scalar Bool(true) slice: main::bb0::stmt1; source-handoff target=Wasm still requires bridge-owned Wasm consumer evidence".to_string();
        let artifact = DecompilationArtifact {
            binary: exact_binary_metadata(),
            target: DecompileTarget::Wasm,
            verification: verification_summary(
                1,
                vec![checked_dispatch("wasm-stale-consumer:vc0", "main", 0x401030)],
            ),
            reconstruction: ReconstructionSummary {
                target: DecompileTarget::Wasm,
                validation: ReconstructionValidationStatus::Validated,
                trust_level: TrustLevel::ProofGrade,
                outputs: vec![DecompiledOutput {
                    target: DecompileTarget::Wasm,
                    validation: ReconstructionValidationStatus::Validated,
                    trust_level: TrustLevel::ProofGrade,
                    preserved_symbolic_formulas: vec![PreservedSymbolicFormula {
                        target: DecompileTarget::Wasm,
                        function: Some("main".to_string()),
                        block: Some(0),
                        statement_index: Some(1),
                        location: "main::bb0::stmt1".to_string(),
                        formula: symbolic_formula.clone(),
                    }],
                    diagnostics: vec![stale_acceptance],
                    target_validation_blockers: vec![TargetValidationBlocker {
                        target: DecompileTarget::Wasm,
                        function: Some("main".to_string()),
                        code: "wasm-source-handoff-target-consumer-stale".to_string(),
                        stage: "trust-wasm-bridge::source-handoff".to_string(),
                        feature: "wasm-source-handoff-target-consumer-stale".to_string(),
                        reason: "Wasm source handoff has no bridge-owned target proof consumer evidence; trust_cg acceptance is stale".to_string(),
                        origin: Some(origin(0x401030)),
                        diagnostics: vec![
                            "selected target=Wasm".to_string(),
                            "stale source-handoff consumer=trust-cg".to_string(),
                        ],
                    }],
                    ..Default::default()
                }],
                ..Default::default()
            },
            source_provenance: exact_source_provenance(),
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        };

        let report = build_binary_decompilation_report(&artifact);
        let json = serde_json::to_value(&report).expect("report serializes");
        let text = format_binary_decompilation_report(&report);

        assert!(!report.proof_grade_gate.accepted);
        assert!(!report.proof_grade_gate.target_semantics_consumed);
        assert_eq!(report.proof_grade_gate.target_validation_blockers, 1);
        assert_eq!(report.proof_grade_gate.preserved_symbolic_formulas, 1);
        assert!(!report.proof_grade_gate.symbolic_formulas_consumed_by_proof_model);
        assert!(report.proof_grade_gate.rejections.iter().any(|rejection| matches!(
            rejection,
            BinaryProofGradeGateRejectionReport::TargetValidationBlockersPresent {
                target,
                count: 1
            } if *target == DecompileTarget::Wasm
        )));
        assert!(report.proof_grade_gate.rejections.iter().any(|rejection| matches!(
            rejection,
            BinaryProofGradeGateRejectionReport::SymbolicFormulasNotConsumed {
                target,
                count: 1
            } if *target == DecompileTarget::Wasm
        )));
        assert_eq!(report.reconstruction.symbolic_formula_consumer_status, "blocked");
        assert_eq!(
            report.reconstruction.target_validation_blockers_by_feature["wasm-source-handoff-target-consumer-stale"],
            1
        );
        assert!(
            report
                .reconstruction
                .symbolic_formula_consumer_blockers
                .iter()
                .any(|blocker| blocker.contains("stale target proof consumer acceptance")
                    && blocker.contains("trust-cg target proof consumer accepted"))
        );
        assert_eq!(
            report.reconstruction.preserved_symbolic_formulas[0].proof_consumer_status,
            "blocked"
        );
        assert_eq!(
            report.source_backpropagation_gate.missing_labels,
            vec!["target_validation".to_string()]
        );

        assert_eq!(json["proof_grade_gate"]["accepted"], false);
        assert_eq!(json["proof_grade_gate"]["target_semantics_consumed"], false);
        assert_eq!(json["reconstruction"]["symbolic_formula_consumer_status"], "blocked");
        assert_eq!(
            json["reconstruction"]["target_validation_blockers_by_feature"]["wasm-source-handoff-target-consumer-stale"],
            1
        );
        assert!(
            json["reconstruction"]["symbolic_formula_consumer_blockers"][0]
                .as_str()
                .expect("stale consumer blocker")
                .contains("stale target proof consumer acceptance")
        );
        assert!(text.contains("formula consumer blockers [stale target proof consumer"));
        assert!(text.contains(
            "Wasm/trust-wasm-bridge::source-handoff/wasm-source-handoff-target-consumer-stale"
        ));
    }

    #[test]
    fn binary_source_backpropagation_gate_names_missing_evidence_fail_closed() {
        let artifact = DecompilationArtifact {
            trust_level: TrustLevel::ProofGrade,
            source_provenance: BinarySourceProvenanceSummary {
                status: "unavailable".to_string(),
                exact_mapping_count: 0,
                ambiguous_mapping_count: 0,
                diagnostics: vec!["no debug/source map".to_string()],
                source_backpropagation_allowed: true,
            },
            ..Default::default()
        };

        let report = build_binary_decompilation_report(&artifact);
        let missing = &report.source_backpropagation_gate.missing_labels;

        assert!(!report.source_backpropagation_gate.accepted);
        assert_eq!(
            missing,
            &vec![
                "missing_reconstruction".to_string(),
                "exact_source_provenance".to_string(),
                "target_validation".to_string(),
                "checked_certificate_identity".to_string(),
                "replay_identity".to_string(),
            ]
        );
        assert!(report.unresolved_blockers.by_family.contains_key("source_backpropagation_gate"));
        assert!(report.unresolved_blockers.entries.iter().any(|entry| {
            entry.family == "source_provenance"
                && entry.feature == "exact_source_provenance"
                && entry.reason.contains("source provenance status=unavailable")
        }));
        assert!(
            !report
                .unresolved_blockers
                .entries
                .iter()
                .any(|entry| entry.feature == "source_backpropagation_closed")
        );
        assert!(report.source_backpropagation_gate.blockers.iter().any(|blocker| {
            blocker.label == "checked_certificate_identity"
                && blocker.detail.contains("checked certificate identity is missing")
        }));

        let text = format_binary_decompilation_report(&report);
        for label in missing {
            assert!(
                text.contains(label),
                "source-backprop blocker label `{label}` was not visible:\n{text}"
            );
        }
        assert!(text.contains("Source backpropagation blocker: replay_identity"));
    }

    #[test]
    fn binary_source_backpropagation_gate_distinguishes_target_validation_blocker() {
        let artifact = DecompilationArtifact {
            binary: exact_binary_metadata(),
            verification: verification_summary(
                1,
                vec![checked_dispatch("source-backprop:vc0", "main", 0x401010)],
            ),
            reconstruction: validated_reconstruction_with_target_semantics_blocker(),
            source_provenance: exact_source_provenance(),
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        };

        let report = build_binary_decompilation_report(&artifact);

        assert!(!report.source_backpropagation_gate.accepted);
        assert_eq!(
            report.source_backpropagation_gate.missing_labels,
            vec!["target_validation".to_string()]
        );
        assert!(report.source_backpropagation_gate.blockers.iter().any(|blocker| {
            blocker.label == "target_validation"
                && blocker.detail.contains("target_semantics_consumed=false")
        }));
    }

    #[test]
    fn binary_report_preserves_non_proof_trust_even_when_vcs_are_proved() {
        let artifact = DecompilationArtifact {
            binary: BinaryArtifactMetadata {
                path: Some("fixtures/tiny".to_string()),
                format: BinaryArtifactFormat::Elf,
                architecture: "x86_64".to_string(),
                entry_point: Some(0x401000),
                ..Default::default()
            },
            target: DecompileTarget::Rust,
            verification: trust_types::BinaryVerificationSummary {
                status: BinaryVerificationStatus::Proved,
                trust_level: TrustLevel::Partial,
                total_vcs: 1,
                proved: 1,
                replay: ReplayStatus::Replayed,
                solver_dispatch: vec![SolverDispatchRecord {
                    id: "main:vc0".to_string(),
                    function: Some("main".to_string()),
                    origin: Some(origin(0x401010)),
                    solver: "ay".to_string(),
                    status: SolverDispatchStatus::Unsat,
                    result: Some(VerificationResult::Proved {
                        solver: "ay".into(),
                        time_ms: 2,
                        strength: ProofStrength::smt_unsat(),
                        proof_certificate: Some(b"raw solver proof bytes".to_vec()),
                        solver_warnings: None,
                        native_proof_envelope: None,
                    }),
                    replay: ReplayStatus::Replayed,
                    ..Default::default()
                }],
                ..Default::default()
            },
            trust_level: TrustLevel::Partial,
            ..Default::default()
        };

        let report = build_binary_decompilation_report(&artifact);
        assert_eq!(report.trust_level, TrustLevel::Partial);
        assert_eq!(report.verification.trust_level, TrustLevel::Partial);
        assert_eq!(report.verification.status, BinaryVerificationStatus::Proved);
        assert_eq!(report.verification.proved, 1);
        assert_eq!(report.verification.replay, ReplayStatus::Replayed);
        assert!(!report.proof_grade_gate.accepted);
        assert_eq!(report.proof_grade_gate.raw_solver_proof_bytes, 1);
        assert_eq!(report.proof_grade_gate.raw_solver_proof_byte_count, 22);
        assert_eq!(report.proof_grade_gate.checked_certificates, 0);
        assert!(report.verification.solver_dispatches[0].raw_solver_proof_bytes);
        assert_eq!(report.verification.solver_dispatches[0].raw_solver_proof_byte_count, 22);
        assert!(!report.verification.solver_dispatches[0].certificate_checked);

        let text = format_binary_decompilation_report(&report);
        assert!(text.contains("Trust level: Partial"));
        assert!(!text.contains("Trust level: ProofGrade"));
        assert!(text.contains("Proof-grade gate: rejected"));
        assert!(text.contains("raw_solver_proofs=1"));
        assert!(text.contains("raw_solver_proof_byte_count=22"));
        assert!(text.contains("Verification: Proved (trust: Partial, replay: Replayed)"));
        assert!(text.contains("main:vc0 @0x401010: Unsat"));
    }

    #[test]
    fn decompilation_proof_grade_report_rejects_mixed_function_missing_coverage() {
        let good = checked_dispatch("good:vc0", "good", 0x401010);
        let raw_bad = raw_unchecked_unreplayed_dispatch("bad:vc0", "bad", 0x402010);
        let artifact = DecompilationArtifact {
            verification: verification_summary(3, vec![good.clone(), raw_bad.clone()]),
            functions: vec![
                proof_grade_function("good", 0x401000, 1, vec![good]),
                proof_grade_function("bad", 0x402000, 2, vec![raw_bad]),
            ],
            reconstruction: validated_reconstruction(),
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        };

        let report = build_binary_decompilation_proof_grade_gate_report(&artifact);

        assert!(!report.accepted);
        assert!(!report.artifact.accepted);
        assert_eq!(report.artifact.required_vcs, 3);
        assert_eq!(report.artifact.solver_dispatches, 2);
        assert_eq!(report.artifact.proved_vcs, 2);
        assert_eq!(report.artifact.checked_certificates, 1);
        assert_eq!(report.artifact.raw_solver_proof_bytes, 1);
        assert_eq!(report.artifact.raw_solver_proof_byte_count, 22);
        assert!(report.artifact.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryProofGradeGateRejectionReport::MissingCheckedProofCertificates {
                    vc_count: 3,
                    checked_certificates: 1,
                    missing_certificates: 2,
                }
            )
        }));
        assert!(report.artifact.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryProofGradeGateRejectionReport::ReplayCoverageIncomplete {
                    vc_count: 3,
                    replay_records: 2,
                    replayed: 1,
                }
            )
        }));

        assert_eq!(report.functions.len(), 2);
        assert!(report.functions[0].gate.accepted);
        let bad = &report.functions[1];
        assert_eq!(bad.name, "bad");
        assert_eq!(bad.entry, 0x402000);
        assert_eq!(bad.entry_display, "0x402000");
        assert!(!bad.gate.accepted);
        assert_eq!(bad.gate.raw_solver_proof_bytes, 1);
        assert_eq!(bad.gate.raw_solver_proof_byte_count, 22);
        assert_eq!(bad.gate.checked_certificates, 0);
        assert!(bad.gate.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryProofGradeGateRejectionReport::MissingCheckedProofCertificates {
                    vc_count: 2,
                    checked_certificates: 0,
                    missing_certificates: 2,
                }
            )
        }));
        assert!(bad.gate.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryProofGradeGateRejectionReport::ReplayCoverageIncomplete {
                    vc_count: 2,
                    replay_records: 1,
                    replayed: 0,
                }
            )
        }));
    }

    #[test]
    fn proof_grade_gate_report_json_uses_stable_field_names() {
        let good = checked_dispatch("good:vc0", "good", 0x401010);
        let raw_bad = raw_unchecked_unreplayed_dispatch("bad:vc0", "bad", 0x402010);
        let artifact = DecompilationArtifact {
            verification: verification_summary(3, vec![good, raw_bad]),
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        };
        let report = build_binary_decompilation_proof_grade_gate_report(&artifact);

        let json = serde_json::to_value(&report.artifact).expect("gate report should serialize");
        for field in [
            "required_vcs",
            "solver_dispatches",
            "checked_certificates",
            "production_checked_certificates",
            "production_checked_certificates_for_all_required_vcs",
            "replayed_vcs",
            "certificate_only_replay_semantics_vcs",
            "replay_semantics_satisfied_vcs",
            "replay_semantics_satisfied",
            "target_semantics_consumed",
            "validated_target_outputs",
            "target_validation_blockers",
            "raw_solver_proof_bytes",
            "raw_solver_proof_byte_count",
            "blocker_groups",
            "accepted",
            "rejections",
        ] {
            assert!(json.get(field).is_some(), "missing stable field {field}: {json}");
        }
        assert_eq!(json["required_vcs"], 3);
        assert_eq!(json["solver_dispatches"], 2);
        assert_eq!(json["checked_certificates"], 1);
        assert_eq!(json["production_checked_certificates"], 1);
        assert_eq!(json["production_checked_certificates_for_all_required_vcs"], false);
        assert_eq!(json["replayed_vcs"], 1);
        assert_eq!(json["certificate_only_replay_semantics_vcs"], 0);
        assert_eq!(json["replay_semantics_satisfied_vcs"], 1);
        assert_eq!(json["replay_semantics_satisfied"], false);
        assert_eq!(json["target_semantics_consumed"], false);
        assert_eq!(json["validated_target_outputs"], 0);
        assert_eq!(json["target_validation_blockers"], 0);
        assert_eq!(json["raw_solver_proof_bytes"], 1);
        assert_eq!(json["raw_solver_proof_byte_count"], 22);
        assert_eq!(json["accepted"], false);
        assert!(!json["rejections"].as_array().expect("rejections array").is_empty());
    }

    #[test]
    fn proof_grade_gate_report_groups_blockers_by_release_evidence_family() {
        let raw_dispatch = raw_unchecked_unreplayed_dispatch("main:vc0", "main", 0x401010);
        let failed_dispatch = SolverDispatchRecord {
            id: "main:vc1".to_string(),
            function: Some("main".to_string()),
            origin: Some(origin(0x401014)),
            solver: "ay".to_string(),
            status: SolverDispatchStatus::Sat,
            query_semantics: SolverQuerySemantics::SatIsCounterexample,
            result: Some(VerificationResult::Failed {
                solver: "ay".into(),
                time_ms: 3,
                counterexample: None,
            }),
            replay: ReplayStatus::Failed,
            ..Default::default()
        };
        let artifact = DecompilationArtifact {
            unsupported: UnsupportedLedger {
                records: vec![unsupported_record("lift", "unsupported opcode", 0x401010)],
            },
            verification: verification_summary(3, vec![raw_dispatch, failed_dispatch]),
            trust_level: TrustLevel::Partial,
            ..Default::default()
        };

        let report = build_binary_decompilation_report(&artifact);
        let gate = &report.proof_grade_gate;

        assert!(!gate.accepted);
        assert_eq!(gate.blocker_groups.trust_level.len(), 1);
        assert_eq!(gate.blocker_groups.unsupported_ledger.len(), 1);
        assert_eq!(gate.blocker_groups.verification.len(), 2);
        assert_eq!(gate.blocker_groups.certificate.len(), 2);
        assert_eq!(gate.blocker_groups.replay.len(), 3);
        assert_eq!(gate.blocker_groups.reconstruction.len(), 1);
        assert_eq!(gate.blocker_groups.source_provenance.len(), 2);
        assert_eq!(gate.blocker_groups.raw_solver_proofs.len(), 1);

        let json = serde_json::to_value(gate).expect("gate report should serialize");
        assert_eq!(json["blocker_groups"]["trust_level"].as_array().unwrap().len(), 1);
        assert_eq!(json["blocker_groups"]["unsupported_ledger"].as_array().unwrap().len(), 1);
        assert_eq!(json["blocker_groups"]["verification"].as_array().unwrap().len(), 2);
        assert_eq!(json["blocker_groups"]["certificate"].as_array().unwrap().len(), 2);
        assert_eq!(json["blocker_groups"]["replay"].as_array().unwrap().len(), 3);
        assert_eq!(json["blocker_groups"]["reconstruction"].as_array().unwrap().len(), 1);
        assert_eq!(json["blocker_groups"]["source_provenance"].as_array().unwrap().len(), 2);
        assert_eq!(json["blocker_groups"]["raw_solver_proofs"].as_array().unwrap().len(), 1);

        let text = format_binary_decompilation_report(&report);
        assert!(text.contains(
            "Proof-grade blocker groups for artifact: trust_level=1, unsupported_ledger=1, verification=2, certificate=2, replay=3, reconstruction=1, source_provenance=2, raw_solver_proofs=1"
        ));
        assert!(text.contains("missing checked proof certificates: 3 missing (0/3 checked)"));
        assert!(text.contains("replay not successful: 1 failed, 0 spurious"));
    }

    #[test]
    fn binary_decompilation_proof_evidence_report_carries_shared_schema_fields_fail_closed() {
        let raw_dispatch = raw_unchecked_unreplayed_dispatch("main:vc0", "main", 0x401010);
        let artifact = DecompilationArtifact {
            binary: BinaryArtifactMetadata {
                path: Some("fixtures/tiny".to_string()),
                format: BinaryArtifactFormat::Elf,
                architecture: "x86_64".to_string(),
                entry_point: Some(0x401000),
                ..Default::default()
            },
            unsupported: UnsupportedLedger {
                records: vec![unsupported_record("lift", "unsupported opcode", 0x401010)],
            },
            verification: verification_summary(1, vec![raw_dispatch]),
            reconstruction: validated_reconstruction(),
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        };

        let evidence = build_binary_decompilation_proof_evidence_report(&artifact);
        let json = serde_json::to_value(&evidence).expect("evidence report serializes");

        assert_eq!(evidence.binary_path.as_deref(), Some("fixtures/tiny"));
        assert_eq!(evidence.format, BinaryArtifactFormat::Elf);
        assert_eq!(evidence.architecture, "x86_64");
        assert_eq!(evidence.trust_level, TrustLevel::ProofGrade);
        assert_eq!(evidence.unsupported_ledger_records, 1);
        assert_eq!(evidence.total_vcs, 1);
        assert_eq!(evidence.solver_dispatches, 1);
        assert_eq!(evidence.solver_dispatch_status_counts["Unsat"], 1);
        assert_eq!(evidence.replay, ReplayStatus::NotAttempted);
        assert_eq!(evidence.replay_status_counts["NotAttempted"], 1);
        assert_eq!(evidence.checked_certificate_coverage.checked_certificates, 0);
        assert_eq!(evidence.checked_certificate_coverage.missing_checked_certificates, 1);
        assert_eq!(evidence.checked_certificate_coverage.raw_solver_proof_bytes, 1);
        assert_eq!(evidence.checked_certificate_coverage.raw_solver_proof_byte_count, 22);
        assert_eq!(evidence.raw_solver_proof_byte_count, 22);
        assert!(!evidence.proof_grade_gate.accepted);
        assert_eq!(evidence.proof_grade_gate.raw_solver_proof_byte_count, 22);

        assert!(json.get("format").is_some());
        assert!(json.get("architecture").is_some());
        assert_eq!(json["unsupported_ledger_records"], 1);
        assert_eq!(json["solver_dispatches"], 1);
        assert_eq!(json["replay"], "NotAttempted");
        assert_eq!(json["checked_certificate_coverage"]["raw_solver_proof_byte_count"], 22);
        assert_eq!(json["raw_solver_proof_byte_count"], 22);
        assert_eq!(json["proof_grade_gate"]["accepted"], false);
    }

    #[test]
    fn binary_decompilation_terminal_report_includes_per_function_gate_rejections() {
        let good = checked_dispatch("good:vc0", "good", 0x401010);
        let raw_bad = raw_unchecked_unreplayed_dispatch("bad:vc0", "bad", 0x402010);
        let artifact = DecompilationArtifact {
            verification: verification_summary(3, vec![good.clone(), raw_bad.clone()]),
            functions: vec![
                proof_grade_function("good", 0x401000, 1, vec![good]),
                proof_grade_function("bad", 0x402000, 2, vec![raw_bad]),
            ],
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        };
        let report = build_binary_decompilation_report(&artifact);

        let text = format_binary_decompilation_report(&report);

        assert!(text.contains("bad @0x402000"));
        assert!(text.contains("Proof-grade gate rejections for function bad:"));
        assert!(text.contains("missing checked proof certificates: 2 missing (0/2 checked)"));
        assert!(text.contains("replay coverage incomplete: 1/2 records, 0 replayed"));
        assert!(text.contains("raw_solver_proofs=1"));
    }

    #[test]
    fn decompilation_proof_grade_report_accepts_synthetic_proof_grade_artifact() {
        let main = checked_dispatch("main:vc0", "main", 0x401010);
        let helper = checked_dispatch("helper:vc0", "helper", 0x402010);
        let artifact = DecompilationArtifact {
            binary: exact_binary_metadata(),
            verification: verification_summary(2, vec![main.clone(), helper.clone()]),
            functions: vec![
                proof_grade_function("main", 0x401000, 1, vec![main]),
                proof_grade_function("helper", 0x402000, 1, vec![helper]),
            ],
            reconstruction: validated_reconstruction(),
            source_provenance: exact_source_provenance(),
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        };

        let report = build_binary_decompilation_proof_grade_gate_report(&artifact);

        assert!(report.accepted, "{:?}", report);
        assert!(report.artifact.accepted);
        assert_eq!(report.artifact.required_vcs, 2);
        assert_eq!(report.artifact.checked_certificates, 2);
        assert!(report.artifact.reconstruction_validated);
        assert_eq!(report.artifact.raw_solver_proof_bytes, 0);
        assert_eq!(report.artifact.raw_solver_proof_byte_count, 0);
        assert_eq!(report.functions.len(), 2);
        assert!(report.functions.iter().all(|function| function.gate.accepted));
    }

    #[test]
    fn binary_decompilation_json_exposes_proof_grade_evidence_metadata() {
        let main = checked_dispatch("main:vc0", "main", 0x401010);
        let helper = checked_dispatch("helper:vc0", "helper", 0x401020);
        let artifact = DecompilationArtifact {
            binary: exact_binary_metadata(),
            verification: verification_summary(2, vec![main, helper]),
            reconstruction: validated_reconstruction(),
            source_provenance: exact_source_provenance(),
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        };

        let report = build_binary_decompilation_report(&artifact);
        let json = serde_json::to_value(&report).expect("binary report should serialize");

        assert_eq!(json["proof_grade_gate"]["accepted"], true);
        assert_eq!(json["proof_grade_gate"]["checked_certificates"], 2);
        assert_eq!(json["proof_grade_gate"]["replayed_vcs"], 2);
        assert_eq!(json["proof_grade_gate"]["unsupported_records"], 0);
        assert_eq!(json["source_provenance"]["status"], "exact");
        assert_eq!(json["source_provenance"]["exact_mapping_count"], 2);
        assert_eq!(json["source_provenance"]["source_backpropagation_allowed"], true);
        assert_eq!(json["verification"]["replay_status_counts"]["Replayed"], 2);
        assert_eq!(json["verification"]["certificate_checks"]["checked_certificates"], 2);
        assert_eq!(
            json["verification"]["certificate_checks"]["checked_certificates_satisfy_coverage"],
            true
        );

        let dispatches =
            json["verification"]["solver_dispatches"].as_array().expect("solver dispatch array");
        assert_eq!(dispatches.len(), 2);
        assert_eq!(
            dispatches[0]["certificate"]["Checked"]["checker"],
            production_checker_status("main:vc0")
        );
        assert_eq!(dispatches[0]["certificate"]["Checked"]["format"], "lfsc");
        assert_eq!(dispatches[0]["certificate"]["Checked"]["sha256"], test_sha256_hex("main:vc0"));
        assert_eq!(dispatches[0]["certificate_checked"], true);
        assert_eq!(dispatches[0]["production_checked"], true);
        assert_eq!(
            json["verification"]["certificate_checks"]["production_manifest"]["accepted"],
            true
        );
        assert_eq!(json["digest_identity"]["proof_grade_ready"], true);
        assert_eq!(json["unresolved_blockers"]["total_blockers"], 0);
        assert_eq!(dispatches[0]["replay"], "Replayed");
    }

    #[test]
    fn binary_decompilation_json_rejects_proof_grade_when_required_evidence_is_missing() {
        let mut missing_certificate = checked_dispatch("missing-cert:vc0", "main", 0x401010);
        missing_certificate.certificate = ProofCertificateStatus::Present {
            format: "lfsc".to_string(),
            sha256: Some("missing-cert:vc0-sha256".to_string()),
            artifact_path: None,
        };

        let mut missing_replay = checked_dispatch("missing-replay:vc0", "main", 0x401020);
        missing_replay.status = SolverDispatchStatus::Sat;
        missing_replay.replay = ReplayStatus::NotAttempted;

        let cases = [
            (
                "checked certificate",
                DecompilationArtifact {
                    verification: verification_summary(1, vec![missing_certificate]),
                    reconstruction: validated_reconstruction(),
                    source_provenance: exact_source_provenance(),
                    trust_level: TrustLevel::ProofGrade,
                    ..Default::default()
                },
                "MissingCheckedProofCertificates",
            ),
            (
                "exact replay",
                DecompilationArtifact {
                    verification: verification_summary(1, vec![missing_replay]),
                    reconstruction: validated_reconstruction(),
                    source_provenance: exact_source_provenance(),
                    trust_level: TrustLevel::ProofGrade,
                    ..Default::default()
                },
                "ReplayStatusUnknown",
            ),
            (
                "unsupported ledger",
                DecompilationArtifact {
                    unsupported: UnsupportedLedger {
                        records: vec![unsupported_record("lift", "unsupported opcode", 0x401030)],
                    },
                    verification: verification_summary(
                        1,
                        vec![checked_dispatch("unsupported:vc0", "main", 0x401030)],
                    ),
                    reconstruction: validated_reconstruction(),
                    source_provenance: exact_source_provenance(),
                    trust_level: TrustLevel::ProofGrade,
                    ..Default::default()
                },
                "UnsupportedRecordsPresent",
            ),
            (
                "source provenance",
                DecompilationArtifact {
                    verification: verification_summary(
                        1,
                        vec![checked_dispatch("provenance:vc0", "main", 0x401040)],
                    ),
                    reconstruction: validated_reconstruction(),
                    source_provenance: BinarySourceProvenanceSummary {
                        status: "unavailable".to_string(),
                        exact_mapping_count: 0,
                        ambiguous_mapping_count: 0,
                        diagnostics: vec!["debug source unavailable".to_string()],
                        source_backpropagation_allowed: false,
                    },
                    trust_level: TrustLevel::ProofGrade,
                    ..Default::default()
                },
                "SourceProvenanceNotExact",
            ),
        ];

        for (missing, artifact, rejection) in cases {
            let json = serde_json::to_value(build_binary_decompilation_report(&artifact))
                .expect("binary report should serialize");

            assert_eq!(
                json["proof_grade_gate"]["accepted"], false,
                "missing {missing} must not overclaim accepted proof-grade: {json}"
            );
            assert!(
                json["proof_grade_gate"]["rejections"]
                    .as_array()
                    .expect("rejections array")
                    .iter()
                    .any(|reason| reason.get(rejection).is_some()),
                "missing {missing} should emit {rejection}: {json}"
            );
        }
    }

    #[test]
    fn binary_report_accepts_proof_grade_only_with_checked_certs_and_replay() {
        let summary = BinaryVerificationSummary {
            status: BinaryVerificationStatus::Proved,
            trust_level: TrustLevel::ProofGrade,
            total_vcs: 1,
            proved: 1,
            replay: ReplayStatus::Replayed,
            solver_dispatch: vec![SolverDispatchRecord {
                id: "main:vc0".to_string(),
                function: Some("main".to_string()),
                origin: Some(origin(0x401010)),
                solver: "ay".to_string(),
                status: SolverDispatchStatus::Unsat,
                certificate: ProofCertificateStatus::Checked {
                    checker: production_checker_status("main:vc0"),
                    format: "lfsc".to_string(),
                    sha256: Some(test_sha256_hex("main:vc0")),
                },
                replay: ReplayStatus::Replayed,
                binary_artifact_digest_identity: Some(exact_binary_digest_identity()),
                ..Default::default()
            }],
            ..Default::default()
        };

        let report = build_binary_verification_report(&summary);

        assert!(report.proof_grade_gate.accepted, "{:?}", report.proof_grade_gate.rejections);
        assert_eq!(report.proof_grade_gate.proved_vcs, 1);
        assert_eq!(report.proof_grade_gate.checked_certificates, 1);
        assert_eq!(report.proof_grade_gate.production_checked_certificates, 1);
        assert_eq!(report.proof_grade_gate.replayed_vcs, 1);
        assert_eq!(report.certificate_checks.certificate_candidates, 1);
        assert_eq!(report.certificate_checks.checked_certificates, 1);
        assert_eq!(report.certificate_checks.missing_checked_certificates, 0);
        assert_eq!(report.certificate_checks.raw_solver_proof_byte_count, 0);
        assert!(report.certificate_checks.checked_certificates_satisfy_coverage);
        assert!(!report.certificate_checks.raw_solver_proof_bytes_satisfy_coverage);
        assert!(!report.certificate_checks.structural_manifest_validation_satisfies_coverage);
        assert!(report.certificate_checks.production_manifest.accepted);
        assert!(report.solver_dispatches[0].certificate_checked);
        assert!(report.solver_dispatches[0].production_checked);

        let text = format_binary_verification_report(&report);
        assert!(text.contains("Proof-grade gate: accepted"));
        assert!(text.contains("Certificate checks: 1/1 accepted checked certificates"));
        assert!(text.contains("cert: checked"));
    }

    #[test]
    fn binary_report_includes_stable_per_vc_formula_summary() {
        let formula = Formula::Eq(
            Box::new(Formula::BvAdd(
                Box::new(Formula::Var("z".to_string(), Sort::BitVec(64))),
                Box::new(Formula::Var("a".to_string(), Sort::BitVec(64))),
                64,
            )),
            Box::new(Formula::BitVec { value: 1, width: 64 }),
        );
        let mut dispatch = checked_dispatch("main:formula", "main", 0x401010);
        dispatch.vc = Some(SerializableVc {
            kind: VcKind::Assertion { message: "binary equivalence".to_string() },
            function: Symbol::intern("main"),
            location: SourceSpan::binary_address(0x401010),
            formula,
            contract_metadata: None,
            obligation: None,
        });

        let summary = BinaryVerificationSummary {
            status: BinaryVerificationStatus::Proved,
            trust_level: TrustLevel::ProofGrade,
            total_vcs: 1,
            proved: 1,
            replay: ReplayStatus::Replayed,
            solver_dispatch: vec![dispatch],
            ..Default::default()
        };

        let report = build_binary_verification_report(&summary);
        let formula_report = report.solver_dispatches[0]
            .vc_formula
            .as_ref()
            .expect("formula summary should be present");
        assert_eq!(
            report.solver_dispatches[0].vc_kind.as_deref(),
            Some("assertion: binary equivalence")
        );
        assert_eq!(formula_report.kind, "assertion: binary equivalence");
        assert_eq!(formula_report.function, "main");
        assert_eq!(formula_report.location.file, "binary:0x401010");
        assert_eq!(formula_report.smtlib, "(= (bvadd z a) (_ bv1 64))");
        assert_eq!(formula_report.free_variables, vec!["a", "z"]);
        assert_eq!(formula_report.sort_declarations.len(), 2);
        assert_eq!(formula_report.sort_declarations[0].name, "a");
        assert_eq!(formula_report.sort_declarations[0].sort, Sort::BitVec(64));
        assert_eq!(formula_report.sort_declarations[0].smtlib_sort, "(_ BitVec 64)");
        assert_eq!(
            formula_report.sort_declarations[0].smtlib_declaration,
            "(declare-fun a () (_ BitVec 64))"
        );
        assert_eq!(formula_report.sort_declarations[1].name, "z");
        assert_eq!(formula_report.sort_declarations[1].sort, Sort::BitVec(64));
        assert_eq!(formula_report.sort_declarations[1].smtlib_sort, "(_ BitVec 64)");
        assert_eq!(
            formula_report.sort_declarations[1].smtlib_declaration,
            "(declare-fun z () (_ BitVec 64))"
        );
        assert_eq!(formula_report.node_count, 5);
        assert!(formula_report.has_bitvectors);
        assert!(!formula_report.has_arrays);
        assert_eq!(
            formula_report.debug,
            "Eq(BvAdd(Var(\"z\", BitVec(64)), Var(\"a\", BitVec(64)), 64), BitVec { value: 1, width: 64 })"
        );

        let json = serde_json::to_value(&report).expect("report serializes");
        assert_eq!(json["solver_dispatches"][0]["vc_kind"], "assertion: binary equivalence");
        assert_eq!(
            json["solver_dispatches"][0]["vc_formula"]["smtlib"],
            "(= (bvadd z a) (_ bv1 64))"
        );
        assert_eq!(json["solver_dispatches"][0]["vc_formula"]["free_variables"][0], "a");
        assert_eq!(json["solver_dispatches"][0]["vc_formula"]["free_variables"][1], "z");
        assert_eq!(json["solver_dispatches"][0]["vc_formula"]["sort_declarations"][0]["name"], "a");
        assert_eq!(
            json["solver_dispatches"][0]["vc_formula"]["sort_declarations"][0]["sort"]["BitVec"],
            64
        );
        assert_eq!(
            json["solver_dispatches"][0]["vc_formula"]["sort_declarations"][0]["smtlib_sort"],
            "(_ BitVec 64)"
        );
        assert_eq!(
            json["solver_dispatches"][0]["vc_formula"]["sort_declarations"][0]["smtlib_declaration"],
            "(declare-fun a () (_ BitVec 64))"
        );
        assert_eq!(json["solver_dispatches"][0]["vc_formula"]["node_count"], 5);
        assert_eq!(json["solver_dispatches"][0]["vc_formula"]["has_bitvectors"], true);
        assert_eq!(json["solver_dispatches"][0]["vc_formula"]["has_arrays"], false);

        let text = format_binary_verification_report(&report);
        assert!(text.contains("formula: kind=assertion: binary equivalence"));
        assert!(text.contains("free_vars=[a, z]"));
        assert!(text.contains("sorts=[a:(_ BitVec 64), z:(_ BitVec 64)]"));
        assert!(text.contains("smtlib=(= (bvadd z a) (_ bv1 64))"));
    }

    #[test]
    fn binary_verification_report_distinguishes_timeout_attestation_missing_from_matched() {
        let summary = BinaryVerificationSummary {
            status: BinaryVerificationStatus::Mixed,
            trust_level: TrustLevel::Partial,
            total_vcs: 2,
            proved: 1,
            timeout: 1,
            solver_dispatch: vec![
                SolverDispatchRecord {
                    id: "main:proved-missing-attestation".to_string(),
                    function: Some("main".to_string()),
                    origin: Some(origin(0x401010)),
                    solver: "ay".to_string(),
                    status: SolverDispatchStatus::Unsat,
                    timeout_ms: Some(250),
                    result: Some(VerificationResult::Proved {
                        solver: "ay".into(),
                        time_ms: 4,
                        strength: ProofStrength::smt_unsat(),
                        proof_certificate: None,
                        solver_warnings: None,
                        native_proof_envelope: None,
                    }),
                    replay: ReplayStatus::Replayed,
                    ..Default::default()
                },
                SolverDispatchRecord {
                    id: "main:timeout-matched".to_string(),
                    function: Some("main".to_string()),
                    origin: Some(origin(0x401014)),
                    solver: "ay".to_string(),
                    status: SolverDispatchStatus::Timeout,
                    timeout_ms: Some(250),
                    result: Some(VerificationResult::Timeout {
                        solver: "ay".into(),
                        timeout_ms: 250,
                    }),
                    replay: ReplayStatus::NotAttempted,
                    ..Default::default()
                },
            ],
            ..Default::default()
        };

        let report = build_binary_verification_report(&summary);

        let missing = report
            .solver_dispatches
            .iter()
            .find(|dispatch| dispatch.id == "main:proved-missing-attestation")
            .expect("missing-attestation dispatch should be reported");
        assert_eq!(
            missing.timeout_evidence.status,
            BinarySolverTimeoutEvidenceStatus::MissingBackendAttestation
        );
        assert_eq!(missing.timeout_evidence.planned_timeout_ms, Some(250));
        assert_eq!(missing.timeout_evidence.backend_reported_timeout_ms, None);
        assert!(
            missing
                .timeout_evidence
                .release_blocker
                .as_deref()
                .expect("missing backend attestation should block release")
                .contains("was not attested by backend result")
        );

        let matched = report
            .solver_dispatches
            .iter()
            .find(|dispatch| dispatch.id == "main:timeout-matched")
            .expect("matched timeout dispatch should be reported");
        assert_eq!(matched.timeout_evidence.status, BinarySolverTimeoutEvidenceStatus::Matched);
        assert_eq!(matched.timeout_evidence.planned_timeout_ms, Some(250));
        assert_eq!(matched.timeout_evidence.backend_reported_timeout_ms, Some(250));
        assert_eq!(matched.timeout_evidence.release_blocker, None);

        let json = serde_json::to_value(&report).expect("report serializes");
        let dispatches = json["solver_dispatches"].as_array().expect("dispatches array");
        let missing_json = dispatches
            .iter()
            .find(|dispatch| dispatch["id"] == "main:proved-missing-attestation")
            .expect("missing-attestation dispatch should serialize");
        assert_eq!(missing_json["timeout_evidence"]["status"], "missing_backend_attestation");
        assert_eq!(
            missing_json["timeout_evidence"]["release_blocker"],
            "planned timeout 250ms for solver dispatch main:proved-missing-attestation was not attested by backend result"
        );

        let matched_json = dispatches
            .iter()
            .find(|dispatch| dispatch["id"] == "main:timeout-matched")
            .expect("matched timeout dispatch should serialize");
        assert_eq!(matched_json["timeout_evidence"]["status"], "matched");
        assert!(matched_json["timeout_evidence"].get("release_blocker").is_none());
    }

    #[test]
    fn binary_report_exposes_router_fallback_attempt_evidence() {
        let dispatch = SolverDispatchRecord {
            id: "main:vc0".to_string(),
            function: Some("main".to_string()),
            origin: Some(origin(0x401010)),
            solver: "fallback".to_string(),
            backend: Some("ay".to_string()),
            status: SolverDispatchStatus::Timeout,
            query_semantics: SolverQuerySemantics::SatIsCounterexample,
            result: Some(VerificationResult::Timeout { solver: "ay".into(), timeout_ms: 5000 }),
            elapsed_ms: Some(5000),
            timeout_ms: Some(100),
            replay: ReplayStatus::NotAttempted,
            diagnostics: vec![
                "router fallback attempt evidence exists before report handoff".to_string(),
                "planned timeout 100ms differed from backend-reported 5000ms".to_string(),
            ],
            fallback_attempts: vec![SolverFallbackAttemptEvidence {
                attempt_index: 0,
                retry_index: Some(0),
                solver: "ay".to_string(),
                backend: Some("ay".to_string()),
                policy: Some("primary".to_string()),
                status: SolverDispatchStatus::Timeout,
                planned_timeout_ms: Some(100),
                backend_timeout_ms: Some(5000),
                elapsed_ms: Some(5000),
                error: Some("timeout".to_string()),
                release_blocker: Some("timeout_policy_mismatch".to_string()),
            }],
            ..Default::default()
        };
        let summary = BinaryVerificationSummary {
            status: BinaryVerificationStatus::Timeout,
            trust_level: TrustLevel::Partial,
            total_vcs: 1,
            timeout: 1,
            solver_dispatch: vec![dispatch],
            ..Default::default()
        };

        let report = build_binary_verification_report(&summary);
        let json = serde_json::to_value(&report).expect("report serializes");
        let dispatch_json = &json["solver_dispatches"][0];

        assert_eq!(report.solver_dispatches[0].result_status.as_deref(), Some("timeout"));
        assert_eq!(report.solver_dispatches[0].fallback_attempts.len(), 1);
        assert_eq!(dispatch_json["solver"], "fallback");
        assert_eq!(dispatch_json["result_status"], "timeout");
        assert_eq!(dispatch_json["fallback_attempts"][0]["solver"], "ay");
        assert_eq!(dispatch_json["fallback_attempts"][0]["planned_timeout_ms"], 100);
        assert_eq!(dispatch_json["fallback_attempts"][0]["backend_timeout_ms"], 5000);
        assert_eq!(
            dispatch_json["fallback_attempts"][0]["release_blocker"],
            "timeout_policy_mismatch"
        );
        assert_eq!(dispatch_json["timeout_evidence"]["status"], "mismatched");
        assert_eq!(json["unresolved_blockers"]["by_family"]["fallback_attempt"], 1);
        assert_eq!(
            dispatch_json["diagnostics"][0],
            "router fallback attempt evidence exists before report handoff"
        );
        assert_eq!(
            dispatch_json["diagnostics"][1],
            "planned timeout 100ms differed from backend-reported 5000ms"
        );
        assert!(dispatch_json.get("timeout_ms").is_none());

        let text = format_binary_verification_report(&report);
        assert!(text.contains("main:vc0 @0x401010: Timeout"));
        assert!(text.contains("fallback attempt #0: solver=ay"));
        assert!(text.contains("planned_timeout_ms=Some(100)"));
        assert!(text.contains("backend_timeout_ms=Some(5000)"));
        assert!(text.contains("timeout_policy_mismatch"));
        assert!(text.contains("fallback_attempt/fallback_attempt_release_blocker"));
    }

    #[test]
    fn binary_report_surfaces_syscall_boundary_evidence_and_fails_closed() {
        let mut dispatch = checked_dispatch("main:vc0", "main", 0x401010);
        dispatch.diagnostics.push(format!(
            "replay_boundary_evidence={}",
            serde_json::json!({
                "kind": "syscall",
                "architecture": "x86_64",
                "instruction_address": 0x401010_u64,
                "step": 7,
                "instruction_bytes": [0x0f, 0x05],
                "opcode": "SYSCALL",
                "encoding": 0,
                "semantics": "unsupported_no_exact_witness",
                "diagnostic": "syscall boundary unsupported_no_exact_witness"
            })
        ));
        let summary = verification_summary(1, vec![dispatch]);

        let report = build_binary_verification_report(&summary);
        let json = serde_json::to_value(&report).expect("report serializes");
        let boundary = &report.solver_dispatches[0].replay_boundary_evidence[0];

        assert_eq!(report.solver_dispatches[0].replay_boundary_evidence.len(), 1);
        assert_eq!(boundary.kind, "syscall");
        assert_eq!(boundary.architecture, "x86_64");
        assert_eq!(boundary.instruction_address, 0x401010);
        assert_eq!(boundary.instruction_address_display, "0x401010");
        assert_eq!(boundary.step, Some(7));
        assert_eq!(boundary.instruction_bytes, vec![0x0f, 0x05]);
        assert_eq!(boundary.instruction_bytes_hex, "0f 05");
        assert_eq!(boundary.semantics, "unsupported_no_exact_witness");
        assert!(!boundary.proof_grade_accepted);
        assert!(
            boundary
                .proof_grade_rejection_reason
                .as_deref()
                .expect("unsupported boundary has rejection")
                .contains("missing exact boundary semantics witness")
        );
        assert!(!report.proof_grade_gate.accepted);
        assert!(report.proof_grade_gate.rejections.iter().any(|rejection| matches!(
            rejection,
            BinaryProofGradeGateRejectionReport::ReplayBoundarySemanticsUnsupported {
                boundary_count: 1,
                unsupported_boundary_count: 1
            }
        )));
        assert_eq!(json["solver_dispatches"][0]["replay_boundary_evidence"][0]["kind"], "syscall");
        assert_eq!(
            json["solver_dispatches"][0]["replay_boundary_evidence"][0]["instruction_bytes"],
            serde_json::json!([0x0f, 0x05])
        );
        assert_eq!(
            json["solver_dispatches"][0]["replay_boundary_evidence"][0]["proof_grade_accepted"],
            false
        );
        assert_eq!(
            json["proof_grade_gate"]["blocker_groups"]["replay"].as_array().unwrap().len(),
            1
        );
        assert_eq!(json["unresolved_blockers"]["by_family"]["replay_boundary"], 1);

        let text = format_binary_verification_report(&report);
        assert!(text.contains("replay boundary: kind=syscall"));
        assert!(text.contains("arch=x86_64"));
        assert!(text.contains("address=0x401010"));
        assert!(text.contains("bytes=[0f 05]"));
        assert!(text.contains("semantics=unsupported_no_exact_witness"));
        assert!(text.contains("proof_grade_accepted=false"));
        assert!(text.contains("replay_boundary/syscall_boundary_semantics"));
    }

    #[test]
    fn binary_report_extracts_nested_exception_boundary_evidence() {
        let mut dispatch = checked_dispatch("trap:vc0", "trap", 0x401020);
        dispatch.diagnostics.push(
            serde_json::json!({
                "replay_report": {
                    "machine_replay": {
                        "boundary_evidence": [{
                            "kind": "exception",
                            "architecture": "aarch64",
                            "instruction_address": "0x401020",
                            "step": 3,
                            "instruction_bytes": "01 00 00 d4",
                            "opcode": "SVC",
                            "encoding": 0xd4000001_u32,
                            "immediate": 1,
                            "semantics": "unsupported_no_exact_witness",
                            "diagnostic": "exception boundary unsupported_no_exact_witness"
                        }]
                    }
                }
            })
            .to_string(),
        );
        let summary = verification_summary(1, vec![dispatch]);

        let report = build_binary_verification_report(&summary);
        let boundary = &report.solver_dispatches[0].replay_boundary_evidence[0];

        assert_eq!(boundary.kind, "exception");
        assert_eq!(boundary.architecture, "aarch64");
        assert_eq!(boundary.instruction_address, 0x401020);
        assert_eq!(boundary.step, Some(3));
        assert_eq!(boundary.instruction_bytes, vec![0x01, 0x00, 0x00, 0xd4]);
        assert_eq!(boundary.instruction_bytes_hex, "01 00 00 d4");
        assert_eq!(boundary.immediate, Some(1));
        assert!(!boundary.proof_grade_accepted);
        assert!(!report.proof_grade_gate.accepted);
        assert_eq!(report.unresolved_blockers.by_family.get("replay_boundary"), Some(&1));
    }

    #[test]
    fn binary_report_exposes_digest_identity_production_manifest_and_unresolved_blockers() {
        let mut dispatch = checked_dispatch("main:vc0", "main", 0x401010);
        dispatch.certificate = ProofCertificateStatus::Checked {
            checker: "ay-cert-check".to_string(),
            format: "lfsc".to_string(),
            sha256: Some(test_sha256_hex("main:vc0")),
        };
        let artifact = DecompilationArtifact {
            binary: BinaryArtifactMetadata {
                path: Some("fixtures/tiny".to_string()),
                format: BinaryArtifactFormat::Elf,
                architecture: "x86_64".to_string(),
                entry_point: Some(0x401000),
                byte_len: Some(16),
                ..Default::default()
            },
            verification: verification_summary(1, vec![dispatch]),
            reconstruction: validated_reconstruction(),
            source_provenance: exact_source_provenance(),
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        };

        let report = build_binary_decompilation_report(&artifact);
        let json = serde_json::to_value(&report).expect("report serializes");
        let text = format_binary_decompilation_report(&report);

        assert!(!report.proof_grade_gate.accepted);
        assert!(!report.digest_identity.proof_grade_ready);
        assert!(
            report
                .digest_identity
                .blockers
                .iter()
                .any(|blocker| blocker.contains("missing root artifact SHA-256 digest"))
        );
        assert!(!report.verification.certificate_checks.production_manifest.accepted);
        assert_eq!(
            report.verification.certificate_checks.production_manifest.missing_production_evidence,
            1
        );
        assert!(
            report
                .unresolved_blockers
                .by_family
                .get("digest_identity")
                .copied()
                .unwrap_or_default()
                >= 1
        );
        assert!(
            report
                .unresolved_blockers
                .by_family
                .get("production_manifest")
                .copied()
                .unwrap_or_default()
                >= 1
        );

        assert_eq!(json["digest_identity"]["proof_grade_ready"], false);
        assert_eq!(
            json["verification"]["certificate_checks"]["production_manifest"]["accepted"],
            false
        );
        assert_eq!(
            json["verification"]["solver_dispatches"][0]["production_checker_evidence"]["status"],
            "missing"
        );
        assert!(
            json["unresolved_blockers"]["entries"]
                .as_array()
                .unwrap()
                .iter()
                .any(|entry| entry["family"] == "digest_identity")
        );
        assert!(
            json["unresolved_blockers"]["entries"]
                .as_array()
                .unwrap()
                .iter()
                .any(|entry| entry["family"] == "production_manifest")
        );

        assert!(text.contains("Digest identity: rejected"));
        assert!(text.contains("production_manifest_accepted=false"));
        assert!(text.contains("Unresolved blocker ledger:"));
        assert!(text.contains("digest_identity/digest_identity_not_exact"));
        assert!(text.contains("production_manifest/missing_production_checker_evidence"));
    }

    #[test]
    fn binary_report_golden_surfaces_dispatch_replay_digest_identity() {
        let ready = checked_dispatch("main:vc0", "main", 0x401010);
        let mut missing = checked_dispatch("main:vc1", "main", 0x401014);
        missing.binary_artifact_digest_identity = None;
        let summary = BinaryVerificationSummary {
            status: BinaryVerificationStatus::Proved,
            trust_level: TrustLevel::ProofGrade,
            total_vcs: 2,
            proved: 2,
            replay: ReplayStatus::Replayed,
            solver_dispatch: vec![ready, missing],
            ..Default::default()
        };

        let report = build_binary_verification_report(&summary);
        let json = serde_json::to_value(&report).expect("report serializes");
        let text = format_binary_verification_report(&report);
        let dispatches =
            json["solver_dispatches"].as_array().expect("solver dispatches should serialize");
        let replay_digest_entries = json["unresolved_blockers"]["entries"]
            .as_array()
            .expect("unresolved entries should serialize")
            .iter()
            .filter(|entry| entry["family"] == "replay_digest_identity")
            .map(|entry| {
                serde_json::json!({
                    "family": entry["family"],
                    "stage": entry["stage"],
                    "feature": entry["feature"],
                    "dispatch_id": entry["dispatch_id"],
                    "location": entry["location"]["instruction_address_display"],
                    "reason": entry["reason"],
                })
            })
            .collect::<Vec<_>>();
        let rejection_kinds = json["proof_grade_gate"]["rejections"]
            .as_array()
            .expect("gate rejections should serialize")
            .iter()
            .map(|rejection| {
                rejection
                    .as_object()
                    .and_then(|object| object.keys().next())
                    .expect("rejection should serialize as enum object")
                    .clone()
            })
            .collect::<Vec<_>>();
        let snapshot = serde_json::json!({
            "proof_grade_gate": {
                "accepted": json["proof_grade_gate"]["accepted"],
                "replayed_vcs": json["proof_grade_gate"]["replayed_vcs"],
                "blocker_group_counts": {
                    "replay": json["proof_grade_gate"]["blocker_groups"]["replay"].as_array().unwrap().len(),
                },
                "rejection_kinds": rejection_kinds,
            },
            "unresolved_blockers": {
                "total_blockers": json["unresolved_blockers"]["total_blockers"],
                "replay_digest_identity": json["unresolved_blockers"]["by_family"]["replay_digest_identity"],
                "entries": replay_digest_entries,
            },
            "dispatches": dispatches
                .iter()
                .map(|dispatch| serde_json::json!({
                    "id": dispatch["id"],
                    "replay": dispatch["replay"],
                    "required": dispatch["replay_digest_identity"]["required"],
                    "proof_grade_ready": dispatch["replay_digest_identity"]["proof_grade_ready"],
                    "root_digest": dispatch["replay_digest_identity"]["identity"]["root_artifact_digest"]["value"],
                    "root_digest_report": dispatch["replay_digest_identity"]["root_artifact_digest"]["value"],
                    "selected_image_range": {
                        "file_offset": dispatch["replay_digest_identity"]["selected_image_identity"]["file_offset"],
                        "file_size": dispatch["replay_digest_identity"]["selected_image_identity"]["file_size"],
                        "end_offset": dispatch["replay_digest_identity"]["selected_image_identity"]["end_offset"],
                    },
                    "selected_image_sha256": dispatch["replay_digest_identity"]["identity"]["selected_image"]["sha256"],
                    "selected_image_sha256_report": dispatch["replay_digest_identity"]["selected_image_identity"]["sha256"],
                    "blockers": dispatch["replay_digest_identity"]["blockers"],
                }))
                .collect::<Vec<_>>(),
            "text_markers": [
                "replay artifact digest identity not exact: 1/2 replayed dispatches ready, 1 blocked",
                "main:vc0 @0x401010: Unsat",
                "replay digest identity: accepted | required=true, root_digest=sha256:000000000000000000000000000000000000000000000000aefe5a1e579a9dab",
                "selected_image=range=[0, 16), size=16, sha256=000000000000000000000000000000000000000000000000aefe5a1e579a9dab",
                "main:vc1 @0x401014: Unsat",
                "replay digest identity: rejected | required=true, root_digest=missing, selected_image=missing, blockers=1",
                "replay digest blocker: missing dispatch binary artifact digest identity",
                "replay_digest_identity/replay_artifact_digest_identity_not_exact stage=replay dispatch=main:vc1 @0x401014",
            ],
        });
        let expected: serde_json::Value = serde_json::from_str(include_str!(
            "fixtures/binary_replay_digest_identity_golden.json"
        ))
        .expect("parse binary replay digest identity golden");

        assert_eq!(snapshot, expected);
        assert!(!report.proof_grade_gate.accepted);
        assert_eq!(report.unresolved_blockers.by_family["replay_digest_identity"], 1);
        assert!(!report.solver_dispatches[1].replay_digest_identity.proof_grade_ready);

        for marker in expected["text_markers"].as_array().expect("text markers") {
            assert!(
                text.contains(marker.as_str().expect("text marker string")),
                "missing text marker `{marker}` in report:\n{text}"
            );
        }
    }

    #[test]
    fn binary_report_golden_rejects_forged_target_semantic_consumption() {
        let dispatch = checked_dispatch("main:vc0", "main", 0x401010);
        let artifact = DecompilationArtifact {
            binary: exact_binary_metadata(),
            verification: verification_summary(1, vec![dispatch]),
            reconstruction: validated_reconstruction_with_target_semantics_blocker(),
            source_provenance: exact_source_provenance(),
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        };

        let report = build_binary_decompilation_report(&artifact);
        let json = serde_json::to_value(&report).expect("report serializes");
        let text = format_binary_decompilation_report(&report);
        let rejection_kinds = json["proof_grade_gate"]["rejections"]
            .as_array()
            .expect("gate rejections should serialize")
            .iter()
            .map(|rejection| {
                rejection
                    .as_object()
                    .and_then(|object| object.keys().next())
                    .expect("rejection should serialize as enum object")
                    .clone()
            })
            .collect::<Vec<_>>();
        let unresolved_entries = json["unresolved_blockers"]["entries"]
            .as_array()
            .expect("unresolved entries should serialize")
            .iter()
            .map(|entry| {
                serde_json::json!({
                    "family": entry["family"],
                    "stage": entry["stage"],
                    "feature": entry["feature"],
                    "location": entry["location"]["instruction_address_display"],
                    "reason": entry["reason"],
                })
            })
            .collect::<Vec<_>>();
        let snapshot = serde_json::json!({
            "proof_grade_gate": {
                "accepted": json["proof_grade_gate"]["accepted"],
                "reconstruction_validated": json["proof_grade_gate"]["reconstruction_validated"],
                "target_semantics_consumed": json["proof_grade_gate"]["target_semantics_consumed"],
                "validated_target_outputs": json["proof_grade_gate"]["validated_target_outputs"],
                "target_validation_blockers": json["proof_grade_gate"]["target_validation_blockers"],
                "blocker_group_counts": {
                    "reconstruction": json["proof_grade_gate"]["blocker_groups"]["reconstruction"].as_array().unwrap().len(),
                },
                "rejection_kinds": rejection_kinds,
            },
            "unresolved_blockers": {
                "total_blockers": json["unresolved_blockers"]["total_blockers"],
                "reconstruction": json["unresolved_blockers"]["by_family"]["reconstruction"],
                "entries": unresolved_entries,
            },
            "reconstruction": {
                "validation": json["reconstruction"]["validation"],
                "target_validation_blocker_count": json["reconstruction"]["target_validation_blocker_count"],
                "target_validation_blockers_by_feature": json["reconstruction"]["target_validation_blockers_by_feature"],
            },
            "text_markers": [
                "target_semantics_consumed=false",
                "target semantics not proof-grade: target=TrustIr, validated_outputs=1, target_validation_blockers=1",
                "target validation blockers present: target=TrustIr, count=1",
                "TrustIr/trust-wasm-bridge::target-validation/binary-provenance-not-consumed-by-target-semantics function=main @0x401010",
                "reconstruction/target_validation_blockers_present stage=proof_grade_gate",
                "source_backpropagation_gate/target_validation stage=source_backpropagation_gate",
                "reconstruction/binary-provenance-not-consumed-by-target-semantics stage=trust-wasm-bridge::target-validation @0x401010",
            ],
        });
        let expected: serde_json::Value = serde_json::from_str(include_str!(
            "fixtures/binary_target_semantics_consumption_golden.json"
        ))
        .expect("parse binary target semantics consumption golden");

        assert_eq!(snapshot, expected);
        assert!(!report.proof_grade_gate.accepted);
        assert!(report.proof_grade_gate.reconstruction_validated);
        assert!(!report.proof_grade_gate.target_semantics_consumed);
        assert_eq!(report.proof_grade_gate.validated_target_outputs, 1);
        assert_eq!(report.proof_grade_gate.target_validation_blockers, 1);

        for marker in expected["text_markers"].as_array().expect("text markers") {
            assert!(
                text.contains(marker.as_str().expect("text marker string")),
                "missing text marker `{marker}` in report:\n{text}"
            );
        }
    }

    #[test]
    fn binary_report_release_golden_preserves_blocker_groups_and_formula_summaries() {
        let formula = Formula::Eq(
            Box::new(Formula::BvAdd(
                Box::new(Formula::Var("z".to_string(), Sort::BitVec(64))),
                Box::new(Formula::Var("a".to_string(), Sort::BitVec(64))),
                64,
            )),
            Box::new(Formula::BitVec { value: 1, width: 64 }),
        );
        let mut checked = checked_dispatch("entry:vc0", "entry", 0x401010);
        checked.vc = Some(SerializableVc {
            kind: VcKind::Assertion { message: "release formula".to_string() },
            function: Symbol::intern("entry"),
            location: SourceSpan::binary_address(0x401010),
            formula,
            contract_metadata: None,
            obligation: None,
        });
        let mut raw = raw_unchecked_unreplayed_dispatch("entry:vc1", "entry", 0x401014);
        raw.vc = Some(SerializableVc {
            kind: VcKind::Assertion { message: "raw candidate".to_string() },
            function: Symbol::intern("entry"),
            location: SourceSpan::binary_address(0x401014),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        });

        let artifact = DecompilationArtifact {
            binary: BinaryArtifactMetadata {
                path: Some("fixtures/tiny".to_string()),
                format: BinaryArtifactFormat::Elf,
                architecture: "x86_64".to_string(),
                entry_point: Some(0x401000),
                ..Default::default()
            },
            unsupported: UnsupportedLedger {
                records: vec![unsupported_record("lift", "unsupported opcode", 0x401020)],
            },
            source_provenance: BinarySourceProvenanceSummary {
                status: "unavailable".to_string(),
                exact_mapping_count: 0,
                ambiguous_mapping_count: 0,
                diagnostics: vec![
                    "exact debug/source provenance is unavailable; diagnostics remain binary-address-only"
                        .to_string(),
                ],
                source_backpropagation_allowed: true,
            },
            verification: verification_summary(3, vec![checked, raw]),
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        };

        let report = build_binary_decompilation_report(&artifact);
        let json = serde_json::to_value(&report).expect("report serializes");
        let dispatches = json["verification"]["solver_dispatches"]
            .as_array()
            .expect("solver dispatches should serialize");
        let rejection_kinds = json["proof_grade_gate"]["rejections"]
            .as_array()
            .expect("gate rejections should serialize")
            .iter()
            .map(|rejection| {
                rejection
                    .as_object()
                    .and_then(|object| object.keys().next())
                    .expect("rejection should serialize as enum object")
                    .clone()
            })
            .collect::<Vec<_>>();
        let snapshot = serde_json::json!({
            "proof_grade_gate": {
                "accepted": json["proof_grade_gate"]["accepted"],
                "required_vcs": json["proof_grade_gate"]["required_vcs"],
                "solver_dispatches": json["proof_grade_gate"]["solver_dispatches"],
                "proved_vcs": json["proof_grade_gate"]["proved_vcs"],
                "checked_certificates": json["proof_grade_gate"]["checked_certificates"],
                "replayed_vcs": json["proof_grade_gate"]["replayed_vcs"],
                "replay_semantics_satisfied_vcs": json["proof_grade_gate"]["replay_semantics_satisfied_vcs"],
                "raw_solver_proof_bytes": json["proof_grade_gate"]["raw_solver_proof_bytes"],
                "raw_solver_proof_byte_count": json["proof_grade_gate"]["raw_solver_proof_byte_count"],
                "blocker_group_counts": {
                    "trust_level": json["proof_grade_gate"]["blocker_groups"]["trust_level"].as_array().unwrap().len(),
                    "unsupported_ledger": json["proof_grade_gate"]["blocker_groups"]["unsupported_ledger"].as_array().unwrap().len(),
                    "verification": json["proof_grade_gate"]["blocker_groups"]["verification"].as_array().unwrap().len(),
                    "certificate": json["proof_grade_gate"]["blocker_groups"]["certificate"].as_array().unwrap().len(),
                    "replay": json["proof_grade_gate"]["blocker_groups"]["replay"].as_array().unwrap().len(),
                    "reconstruction": json["proof_grade_gate"]["blocker_groups"]["reconstruction"].as_array().unwrap().len(),
                    "source_provenance": json["proof_grade_gate"]["blocker_groups"]["source_provenance"].as_array().unwrap().len(),
                    "raw_solver_proofs": json["proof_grade_gate"]["blocker_groups"]["raw_solver_proofs"].as_array().unwrap().len(),
                },
                "rejection_kinds": rejection_kinds,
            },
            "formula_summaries": dispatches
                .iter()
                .map(|dispatch| serde_json::json!({
                    "id": dispatch["id"],
                    "kind": dispatch["vc_formula"]["kind"],
                    "function": dispatch["vc_formula"]["function"],
                    "location_file": dispatch["vc_formula"]["location"]["file"],
                    "smtlib": dispatch["vc_formula"]["smtlib"],
                    "debug": dispatch["vc_formula"]["debug"],
                    "node_count": dispatch["vc_formula"]["node_count"],
                    "free_variables": dispatch["vc_formula"]["free_variables"],
                    "sort_declarations": dispatch["vc_formula"]["sort_declarations"],
                    "has_bitvectors": dispatch["vc_formula"]["has_bitvectors"],
                    "has_arrays": dispatch["vc_formula"]["has_arrays"],
                }))
                .collect::<Vec<_>>(),
            "text_markers": [
                "Proof-grade blocker groups for artifact: unsupported_ledger=1, verification=2, certificate=2, replay=2, reconstruction=1, source_provenance=2, raw_solver_proofs=1",
                "formula: kind=assertion: release formula, nodes=5, free_vars=[a, z], sorts=[a:(_ BitVec 64), z:(_ BitVec 64)], bitvectors=true, arrays=false, smtlib=(= (bvadd z a) (_ bv1 64))",
                "formula: kind=assertion: raw candidate, nodes=1, free_vars=[], sorts=[], bitvectors=false, arrays=false, smtlib=false",
            ],
        });
        let expected: serde_json::Value = serde_json::from_str(include_str!(
            "fixtures/binary_proof_grade_blocker_formula_golden.json"
        ))
        .expect("parse binary proof-grade blocker/formula golden");

        assert_eq!(snapshot, expected);

        let text = format_binary_decompilation_report(&report);
        for marker in expected["text_markers"].as_array().expect("text markers") {
            assert!(
                text.contains(marker.as_str().expect("text marker string")),
                "missing text marker `{marker}` in report:\n{text}"
            );
        }
    }

    #[test]
    fn binary_report_rejects_checked_status_without_canonical_digest() {
        let summary = BinaryVerificationSummary {
            status: BinaryVerificationStatus::Proved,
            trust_level: TrustLevel::ProofGrade,
            total_vcs: 1,
            proved: 1,
            replay: ReplayStatus::Replayed,
            solver_dispatch: vec![SolverDispatchRecord {
                id: "main:vc0".to_string(),
                function: Some("main".to_string()),
                origin: Some(origin(0x401010)),
                solver: "ay".to_string(),
                status: SolverDispatchStatus::Unsat,
                certificate: ProofCertificateStatus::Checked {
                    checker: "ay-cert-check".to_string(),
                    format: "lfsc".to_string(),
                    sha256: Some("vc0-sha256".to_string()),
                },
                replay: ReplayStatus::Replayed,
                ..Default::default()
            }],
            ..Default::default()
        };

        let report = build_binary_verification_report(&summary);
        let text = format_binary_verification_report(&report);

        assert!(!report.proof_grade_gate.accepted);
        assert_eq!(report.proof_grade_gate.checked_certificates, 0);
        assert_eq!(report.certificate_checks.certificate_candidates, 1);
        assert_eq!(report.certificate_checks.checked_certificates, 0);
        assert_eq!(report.certificate_checks.missing_checked_certificates, 1);
        assert!(!report.certificate_checks.checked_certificates_satisfy_coverage);
        assert!(!report.solver_dispatches[0].certificate_checked);
        assert!(!report.solver_dispatches[0].checked_certificate_identity.checked_identity_ready);
        assert!(
            report.solver_dispatches[0]
                .checked_certificate_identity
                .blockers
                .iter()
                .any(|blocker| blocker.contains("not canonical lowercase SHA-256"))
        );
        assert!(!report.certificate_checks.raw_solver_proof_bytes_satisfy_coverage);
        assert!(!report.certificate_checks.structural_manifest_validation_satisfies_coverage);
        assert!(report.proof_grade_gate.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryProofGradeGateRejectionReport::MissingCheckedProofCertificates {
                    vc_count: 1,
                    checked_certificates: 0,
                    missing_certificates: 1,
                }
            )
        }));
        assert!(text.contains("cert: checked-invalid"));
        assert!(text.contains("checked certificate identity: rejected"));
        assert!(text.contains(
            "checked certificate identity blocker: checked certificate sha256 is not canonical"
        ));
    }

    #[test]
    fn binary_proof_grade_report_keeps_unsupported_separate_from_cert_and_replay() {
        let summary = BinaryVerificationSummary {
            status: BinaryVerificationStatus::Proved,
            trust_level: TrustLevel::ProofGrade,
            total_vcs: 1,
            proved: 1,
            replay: ReplayStatus::Replayed,
            unsupported_ledger: UnsupportedLedger {
                records: vec![unsupported_record("lift", "unsupported opcode", 0x401010)],
            },
            solver_dispatch: vec![checked_dispatch("main:vc0", "main", 0x401010)],
            ..Default::default()
        };

        let report = build_binary_verification_report(&summary);
        let json = serde_json::to_value(&report).expect("report serializes");

        assert!(!report.proof_grade_gate.accepted);
        assert_eq!(report.proof_grade_gate.unsupported_records, 1);
        assert!(!report.proof_grade_gate.unsupported_ledger_empty);
        assert!(report.proof_grade_gate.all_required_vcs_proved);
        assert!(report.proof_grade_gate.checked_certificates_for_all_required_vcs);
        assert!(report.proof_grade_gate.full_replay_coverage);
        assert!(report.proof_grade_gate.replay_semantics_satisfied);
        assert_eq!(report.proof_grade_gate.checked_certificates, 1);
        assert_eq!(report.proof_grade_gate.replayed_vcs, 1);
        assert_eq!(
            report.proof_grade_gate.rejections,
            vec![BinaryProofGradeGateRejectionReport::UnsupportedRecordsPresent { count: 1 }]
        );

        assert_eq!(report.unsupported_ledger.total_records, 1);
        assert_eq!(report.certificate_checks.checked_certificates, 1);
        assert_eq!(report.certificate_checks.missing_checked_certificates, 0);
        assert!(report.certificate_checks.checked_certificates_satisfy_coverage);
        assert_eq!(report.replay_status_counts["Replayed"], 1);
        assert_eq!(json["proof_grade_gate"]["unsupported_records"], 1);
        assert_eq!(json["proof_grade_gate"]["checked_certificates"], 1);
        assert_eq!(json["proof_grade_gate"]["replayed_vcs"], 1);
        assert_eq!(json["certificate_checks"]["missing_checked_certificates"], 0);
    }

    #[test]
    fn certificate_report_keeps_manifest_structural_validation_separate_from_checked_coverage() {
        let summary = BinaryVerificationSummary {
            status: BinaryVerificationStatus::Proved,
            trust_level: TrustLevel::ProofGrade,
            total_vcs: 1,
            proved: 1,
            replay: ReplayStatus::Replayed,
            solver_dispatch: vec![manifest_candidate_dispatch("main:vc0", "main", 0x401010)],
            ..Default::default()
        };

        let report = build_binary_verification_report(&summary);
        let json = serde_json::to_value(&report).expect("report serializes");
        let text = format_binary_verification_report(&report);

        assert!(!report.proof_grade_gate.accepted);
        assert_eq!(report.certificate_checks.certificate_candidates, 1);
        assert_eq!(report.certificate_checks.structural_manifest_candidates, 1);
        assert_eq!(report.certificate_checks.checked_certificates, 0);
        assert_eq!(report.certificate_checks.missing_checked_certificates, 1);
        assert_eq!(report.certificate_checks.checked_certificate_identity_blockers.len(), 1);
        assert_eq!(
            report.solver_dispatches[0].checked_certificate_identity.artifact_path.as_deref(),
            Some("checked-cert-manifest.json#certificates/main.vc0.checked.json")
        );
        assert!(
            report.solver_dispatches[0]
                .checked_certificate_identity
                .blockers
                .iter()
                .any(|blocker| blocker.contains("structural checked-certificate manifest"))
        );
        assert!(!report.certificate_checks.checked_certificates_satisfy_coverage);
        assert!(!report.certificate_checks.raw_solver_proof_bytes_satisfy_coverage);
        assert!(!report.certificate_checks.structural_manifest_validation_satisfies_coverage);
        assert!(report.proof_grade_gate.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryProofGradeGateRejectionReport::MissingCheckedProofCertificates {
                    vc_count: 1,
                    checked_certificates: 0,
                    missing_certificates: 1,
                }
            )
        }));
        assert_eq!(
            json["certificate_checks"]["structural_manifest_validation_satisfies_coverage"],
            false
        );
        assert_eq!(json["certificate_checks"]["structural_manifest_candidates"], 1);
        assert_eq!(
            json["solver_dispatches"][0]["checked_certificate_identity"]["proof_grade_ready"],
            false
        );
        assert_eq!(
            json["solver_dispatches"][0]["checked_certificate_identity"]["artifact_path"],
            "checked-cert-manifest.json#certificates/main.vc0.checked.json"
        );
        assert!(text.contains("Certificate checks: 0/1 accepted checked certificates"));
        assert!(text.contains("1 certificate-shaped candidates"));
        assert!(text.contains("1 structural manifest candidates"));
        assert!(text.contains("identity_blockers=1"));
        assert!(text.contains("checked certificate identity: rejected"));
        assert!(text.contains("structural checked-certificate manifest candidate"));
        assert!(text.contains("manifest_structural_satisfies_coverage=false"));
        assert!(text.contains("missing checked proof certificates: 1 missing (0/1 checked)"));
    }

    #[test]
    fn binary_report_keeps_all_proof_evidence_axes_separate_when_mixed() {
        let mut raw_checked = checked_dispatch("raw:vc0", "main", 0x401014);
        raw_checked.result = Some(VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: 2,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: Some(b"raw solver proof bytes".to_vec()),
            solver_warnings: None,
            native_proof_envelope: None,
        });

        let summary = BinaryVerificationSummary {
            status: BinaryVerificationStatus::Proved,
            trust_level: TrustLevel::ProofGrade,
            total_vcs: 3,
            proved: 3,
            replay: ReplayStatus::Replayed,
            unsupported_ledger: UnsupportedLedger {
                records: vec![unsupported_record("lift", "unsupported opcode", 0x401020)],
            },
            solver_dispatch: vec![
                checked_dispatch("checked:vc0", "main", 0x401010),
                raw_checked,
                manifest_candidate_dispatch("manifest:vc0", "main", 0x401018),
            ],
            ..Default::default()
        };

        let report = build_binary_verification_report(&summary);
        let json = serde_json::to_value(&report).expect("report serializes");
        let text = format_binary_verification_report(&report);

        assert!(!report.proof_grade_gate.accepted);
        assert_eq!(report.proof_grade_gate.unsupported_records, 1);
        assert!(!report.proof_grade_gate.unsupported_ledger_empty);
        assert!(report.proof_grade_gate.all_required_vcs_proved);
        assert!(!report.proof_grade_gate.checked_certificates_for_all_required_vcs);
        assert!(report.proof_grade_gate.full_replay_coverage);
        assert!(report.proof_grade_gate.replay_semantics_satisfied);
        assert_eq!(report.proof_grade_gate.checked_certificates, 2);
        assert_eq!(report.proof_grade_gate.replayed_vcs, 3);
        assert_eq!(report.proof_grade_gate.raw_solver_proof_bytes, 1);
        assert_eq!(report.proof_grade_gate.raw_solver_proof_byte_count, 22);
        assert_eq!(
            report.proof_grade_gate.rejections,
            vec![
                BinaryProofGradeGateRejectionReport::UnsupportedRecordsPresent { count: 1 },
                BinaryProofGradeGateRejectionReport::MissingCheckedProofCertificates {
                    vc_count: 3,
                    checked_certificates: 2,
                    missing_certificates: 1,
                },
                BinaryProofGradeGateRejectionReport::CheckedCertificateProductionManifestIncomplete {
                    vc_count: 3,
                    production_checked_certificates: 2,
                    missing_production_evidence: 1,
                    malformed_production_evidence: 0,
                },
                BinaryProofGradeGateRejectionReport::RawSolverProofBytesPresent { count: 1 },
            ]
        );

        assert_eq!(report.certificate_checks.required_vcs, 3);
        assert_eq!(report.certificate_checks.certificate_candidates, 3);
        assert_eq!(report.certificate_checks.checked_certificates, 2);
        assert_eq!(report.certificate_checks.missing_checked_certificates, 1);
        assert_eq!(report.certificate_checks.raw_solver_proof_bytes, 1);
        assert_eq!(report.certificate_checks.raw_solver_proof_byte_count, 22);
        assert!(!report.certificate_checks.checked_certificates_satisfy_coverage);
        assert!(!report.certificate_checks.raw_solver_proof_bytes_satisfy_coverage);
        assert!(!report.certificate_checks.structural_manifest_validation_satisfies_coverage);
        assert_eq!(report.unsupported_ledger.total_records, 1);
        assert_eq!(report.replay_status_counts["Replayed"], 3);

        assert_eq!(json["proof_grade_gate"]["unsupported_records"], 1);
        assert_eq!(json["proof_grade_gate"]["checked_certificates"], 2);
        assert_eq!(json["proof_grade_gate"]["replayed_vcs"], 3);
        assert_eq!(json["proof_grade_gate"]["raw_solver_proof_bytes"], 1);
        assert_eq!(
            json["certificate_checks"]["structural_manifest_validation_satisfies_coverage"],
            false
        );
        assert_eq!(json["certificate_checks"]["raw_solver_proof_bytes_satisfy_coverage"], false);
        assert_eq!(json["replay_status_counts"]["Replayed"], 3);

        assert!(text.contains("unsupported records present: 1"));
        assert!(text.contains("missing checked proof certificates: 1 missing (2/3 checked)"));
        assert!(text.contains("raw solver proof bytes present: 1"));
        assert!(text.contains("replay_coverage=true"));
        assert!(text.contains("manifest_structural_satisfies_coverage=false"));
    }

    #[test]
    fn binary_decompilation_report_keeps_release_blockers_visible() {
        let checked = checked_dispatch("checked:vc0", "entry", 0x401010);
        let manifest = manifest_candidate_dispatch("manifest:vc1", "entry", 0x401014);
        let mut missing_replay = checked_dispatch("sat:vc2", "entry", 0x401018);
        missing_replay.status = SolverDispatchStatus::Sat;
        missing_replay.replay = ReplayStatus::NotAttempted;
        missing_replay.certificate = ProofCertificateStatus::NotRequested;

        let symbolic_formula = Formula::BvAdd(
            Box::new(Formula::Var("x0".to_string(), Sort::BitVec(64))),
            Box::new(Formula::BitVec { value: 1, width: 64 }),
            64,
        );
        let blocker_origin = origin(0x401020);
        let blocker = |stage: &str, feature: &str, reason: &str| TargetValidationBlocker {
            target: DecompileTarget::TrustIr,
            function: Some("entry".to_string()),
            code: feature.to_string(),
            stage: stage.to_string(),
            feature: feature.to_string(),
            reason: reason.to_string(),
            origin: Some(blocker_origin.clone()),
            diagnostics: vec![reason.to_string()],
        };
        let reconstruction_output = DecompiledOutput {
            target: DecompileTarget::TrustIr,
            validation: ReconstructionValidationStatus::Failed,
            trust_level: TrustLevel::Rejected,
            target_validation_blockers: vec![
                blocker("lift", "unsupported_machine_semantics", "unsupported system register"),
                blocker("replay", "missing_replay", "solver result was not replayed"),
                blocker(
                    "certificate",
                    "missing_checked_certificate",
                    "manifest import is not checked certificate coverage",
                ),
                blocker(
                    "canonical_trust_ir",
                    "symbolic_formula_loss",
                    "symbolic formula must remain structured",
                ),
            ],
            preserved_symbolic_formulas: vec![PreservedSymbolicFormula {
                target: DecompileTarget::TrustIr,
                function: Some("entry".to_string()),
                block: Some(0),
                statement_index: Some(1),
                location: "bb0[1].rvalue".to_string(),
                formula: symbolic_formula.clone(),
            }],
            ..Default::default()
        };
        let artifact = DecompilationArtifact {
            binary: BinaryArtifactMetadata {
                path: Some("fixtures/tiny".to_string()),
                format: BinaryArtifactFormat::Elf,
                architecture: "x86_64".to_string(),
                entry_point: Some(0x401000),
                ..Default::default()
            },
            unsupported: UnsupportedLedger {
                records: vec![unsupported_record("lift", "unsupported opcode", 0x401020)],
            },
            source_provenance: BinarySourceProvenanceSummary {
                status: "unavailable".to_string(),
                exact_mapping_count: 0,
                ambiguous_mapping_count: 0,
                diagnostics: vec![
                    "exact debug/source provenance is unavailable; diagnostics remain binary-address-only"
                        .to_string(),
                ],
                source_backpropagation_allowed: true,
            },
            verification: verification_summary(3, vec![checked, manifest, missing_replay]),
            reconstruction: ReconstructionSummary {
                target: DecompileTarget::TrustIr,
                outputs: vec![reconstruction_output],
                validation: ReconstructionValidationStatus::Failed,
                trust_level: TrustLevel::Rejected,
                ..Default::default()
            },
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        };

        let report = build_binary_decompilation_report(&artifact);
        let json = serde_json::to_value(&report).expect("report serializes");
        let text = format_binary_decompilation_report(&report);

        assert!(!report.proof_grade_gate.accepted);
        assert_eq!(report.proof_grade_gate.unsupported_records, 1);
        assert_eq!(report.proof_grade_gate.checked_certificates, 1);
        assert_eq!(report.proof_grade_gate.replayed_vcs, 2);
        assert!(!report.source_provenance.source_backpropagation_allowed);
        assert_eq!(report.reconstruction.target_validation_blocker_count, 4);
        assert_eq!(report.reconstruction.preserved_symbolic_formula_count, 1);
        assert_eq!(
            report.reconstruction.target_validation_blockers_by_feature["symbolic_formula_loss"],
            1
        );

        for rejection in [
            "UnsupportedRecordsPresent",
            "NonProvedVerificationConditions",
            "MissingCheckedProofCertificates",
            "ReplayStatusUnknown",
            "ReconstructionValidationNotValidated",
            "SourceProvenanceNotExact",
        ] {
            assert!(
                json["proof_grade_gate"]["rejections"]
                    .as_array()
                    .expect("rejections array")
                    .iter()
                    .any(|reason| reason.get(rejection).is_some()),
                "missing separate rejection {rejection}: {json}"
            );
        }

        assert_eq!(json["unsupported"]["total_records"], 1);
        assert_eq!(json["source_provenance"]["source_backpropagation_allowed"], false);
        assert_eq!(json["verification"]["certificate_checks"]["certificate_candidates"], 2);
        assert_eq!(json["verification"]["certificate_checks"]["checked_certificates"], 1);
        assert_eq!(
            json["verification"]["certificate_checks"]["structural_manifest_validation_satisfies_coverage"],
            false
        );
        assert_eq!(json["verification"]["replay_status_counts"]["NotAttempted"], 1);
        assert_eq!(json["reconstruction"]["target_validation_blocker_count"], 4);
        assert_eq!(
            json["reconstruction"]["target_validation_blockers_by_feature"]["symbolic_formula_loss"],
            1
        );
        assert_eq!(json["reconstruction"]["preserved_symbolic_formula_count"], 1);
        let json_formula: Formula = serde_json::from_value(
            json["reconstruction"]["preserved_symbolic_formulas"][0]["formula"].clone(),
        )
        .expect("preserved formula remains structured");
        assert_eq!(json_formula, symbolic_formula);

        assert!(text.contains("unsupported records present: 1"));
        assert!(text.contains("missing checked proof certificates: 2 missing (1/3 checked)"));
        assert!(text.contains("replay status unknown: 1 not attempted"));
        assert!(text.contains("Source provenance: unavailable"));
        assert!(text.contains("source_backpropagation_allowed=false"));
        assert!(text.contains("Certificate checks: 1/3 accepted checked certificates"));
        assert!(text.contains("2 certificate-shaped candidates"));
        assert!(text.contains("manifest_structural_satisfies_coverage=false"));
        assert!(text.contains("Reconstruction: Failed"));
        assert!(text.contains("target_validation_blockers=4"));
        assert!(text.contains("preserved_symbolic_formulas=1"));
        assert!(text.contains("Target validation blockers:"));
        assert!(text.contains("TrustIr/canonical_trust_ir/symbolic_formula_loss"));
        assert!(text.contains("Preserved symbolic formulas:"));
        assert!(text.contains("formula=BvAdd"));
    }

    #[test]
    fn binary_decompilation_report_preserves_readback_effect_and_refinement_residuals() {
        let mut dispatch = checked_dispatch("readback:vc0", "entry", 0x401010);
        dispatch.diagnostics = vec![
            "checked proof-cert readback row accepted for proof-grade release; manifest_identity_sha256=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa; source_backpropagation_gate_sha256=bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".to_string(),
            "source-backprop blocked: bounded machine replay could not produce concrete scalar memory_write effect witness for AArch64 instruction 0x401010 at machine trace step 0: concrete scalar memory address/width evidence is required for source backprop".to_string(),
        ];

        let blocker = TargetValidationBlocker {
            target: DecompileTarget::TrustCg,
            function: Some("entry".to_string()),
            code: "binary-proof-obligation-pending-refinement-metadata".to_string(),
            stage: "trust-cg-bridge::target-validation".to_string(),
            feature: "binary-proof-obligation-pending-refinement-metadata".to_string(),
            reason: "trust-cg target proof consumer consumed binary proof inputs, but bidirectional refinement metadata is still pending".to_string(),
            origin: Some(origin(0x401010)),
            diagnostics: vec![
                "binary_proof_obligation.state=target-consumed-pending-refinement".to_string(),
                "required-evidence=bidirectional_refinement_metadata".to_string(),
            ],
        };
        let validation_record = ReconstructionValidationRecord {
            target: DecompileTarget::TrustCg,
            function: Some("entry".to_string()),
            lifted_function: Some("entry::lifted".to_string()),
            reconstructed_function: Some("entry::trust_cg".to_string()),
            candidate: ReconstructionCandidateKind::StructuredTrustIr,
            status: ReconstructionValidationStatus::Unknown,
            trust_level: TrustLevel::Rejected,
            evidence: vec![ReconstructionValidationEvidence::BidirectionalTrustIrRefinement],
            diagnostics: vec![
                "bidirectional refinement residual: reverse implication not checked".to_string(),
            ],
            ..Default::default()
        };
        let artifact = DecompilationArtifact {
            binary: exact_binary_metadata(),
            target: DecompileTarget::TrustCg,
            verification: verification_summary(1, vec![dispatch]),
            reconstruction: ReconstructionSummary {
                target: DecompileTarget::TrustCg,
                validation: ReconstructionValidationStatus::Validated,
                trust_level: TrustLevel::Rejected,
                diagnostics: vec![
                    "reconstruction residual: target consumed but refinement metadata pending"
                        .to_string(),
                ],
                outputs: vec![DecompiledOutput {
                    target: DecompileTarget::TrustCg,
                    artifact_path: Some("fixtures/readback.ll2.json".to_string()),
                    validation: ReconstructionValidationStatus::Validated,
                    trust_level: TrustLevel::Rejected,
                    diagnostics: vec![
                        "binary_proof_obligation.state=target-consumed-pending-refinement"
                            .to_string(),
                    ],
                    target_validation_blockers: vec![blocker],
                    validation_records: vec![validation_record],
                    ..Default::default()
                }],
                ..Default::default()
            },
            source_provenance: exact_source_provenance(),
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        };

        let report = build_binary_decompilation_report(&artifact);
        let json = serde_json::to_value(&report).expect("report serializes");
        let text = format_binary_decompilation_report(&report);

        assert!(!report.proof_grade_gate.accepted);
        assert_eq!(
            json["verification"]["solver_dispatches"][0]["diagnostics"][0],
            "checked proof-cert readback row accepted for proof-grade release; manifest_identity_sha256=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa; source_backpropagation_gate_sha256=bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
        );
        assert!(
            json["verification"]["solver_dispatches"][0]["diagnostics"][1]
                .as_str()
                .expect("dispatch diagnostic")
                .contains("concrete scalar memory")
        );
        assert_eq!(
            json["verification"]["solver_dispatches"][0]["checked_certificate_identity"]["proof_grade_ready"],
            true
        );
        assert_eq!(
            json["verification"]["solver_dispatches"][0]["checked_certificate_identity"]["production_checked"],
            true
        );
        assert!(
            json["reconstruction"]["diagnostics"][0]
                .as_str()
                .expect("reconstruction diagnostic")
                .contains("refinement metadata pending")
        );
        assert_eq!(json["reconstruction"]["output_diagnostics"][0]["target"], "TrustCg");
        assert!(
            json["reconstruction"]["output_diagnostics"][0]["diagnostics"][0]
                .as_str()
                .expect("output diagnostic")
                .contains("target-consumed-pending-refinement")
        );
        assert_eq!(
            json["reconstruction"]["validation_records"][0]["candidate"],
            "StructuredTrustIr"
        );
        assert!(
            json["reconstruction"]["validation_records"][0]["diagnostics"][0]
                .as_str()
                .expect("validation record diagnostic")
                .contains("bidirectional refinement residual")
        );
        assert_eq!(
            json["reconstruction"]["target_validation_blockers"][0]["diagnostics"][1],
            "required-evidence=bidirectional_refinement_metadata"
        );
        assert_eq!(
            json["reconstruction"]["target_validation_blockers"][0]["code"],
            "binary-proof-obligation-pending-refinement-metadata"
        );
        assert!(text.contains("dispatch diagnostic: checked proof-cert readback row accepted"));
        assert!(text.contains("dispatch diagnostic: source-backprop blocked"));
        assert!(text.contains("Reconstruction diagnostic: reconstruction residual"));
        assert!(text.contains("Reconstruction output diagnostics: target=TrustCg"));
        assert!(text.contains("Reconstruction validation record: target=TrustCg"));
        assert!(text.contains(
            "target validation diagnostic: required-evidence=bidirectional_refinement_metadata"
        ));
    }

    #[test]
    fn binary_report_accepts_unsat_certificate_only_replay_semantics() {
        let summary = BinaryVerificationSummary {
            status: BinaryVerificationStatus::Proved,
            trust_level: TrustLevel::ProofGrade,
            total_vcs: 1,
            proved: 1,
            replay: ReplayStatus::NotAttempted,
            solver_dispatch: vec![checked_certificate_only_dispatch("main:vc0", "main", 0x401010)],
            ..Default::default()
        };

        let report = build_binary_verification_report(&summary);

        assert!(report.proof_grade_gate.accepted, "{:?}", report.proof_grade_gate.rejections);
        assert!(report.proof_grade_gate.all_required_vcs_proved);
        assert!(report.proof_grade_gate.checked_certificates_for_all_required_vcs);
        assert!(!report.proof_grade_gate.full_replay_coverage);
        assert!(report.proof_grade_gate.replay_semantics_satisfied);
        assert_eq!(report.proof_grade_gate.replayed_vcs, 0);
        assert_eq!(report.proof_grade_gate.certificate_only_replay_semantics_vcs, 1);
        assert_eq!(report.proof_grade_gate.replay_semantics_satisfied_vcs, 1);
        assert!(!report.proof_grade_gate.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryProofGradeGateRejectionReport::ReplayCoverageIncomplete { .. }
                    | BinaryProofGradeGateRejectionReport::ReplayStatusUnknown { .. }
                    | BinaryProofGradeGateRejectionReport::ReplayNotSuccessful { .. }
            )
        }));

        let text = format_binary_verification_report(&report);
        assert!(text.contains("Proof-grade gate: accepted"));
        assert!(text.contains("replay_coverage=false"));
        assert!(text.contains("replay_semantics=true"));
        assert!(text.contains("cert_only_replay_semantics=1"));
    }

    #[test]
    fn binary_report_gate_rejects_missing_required_vc_coverage() {
        let summary = BinaryVerificationSummary {
            status: BinaryVerificationStatus::Mixed,
            trust_level: TrustLevel::ProofGrade,
            total_vcs: 2,
            proved: 1,
            replay: ReplayStatus::Replayed,
            solver_dispatch: vec![SolverDispatchRecord {
                id: "main:vc0".to_string(),
                function: Some("main".to_string()),
                origin: Some(origin(0x401010)),
                solver: "ay".to_string(),
                status: SolverDispatchStatus::Unsat,
                certificate: ProofCertificateStatus::Checked {
                    checker: "ay-cert-check".to_string(),
                    format: "lfsc".to_string(),
                    sha256: Some(test_sha256_hex("main:vc0")),
                },
                replay: ReplayStatus::Replayed,
                ..Default::default()
            }],
            ..Default::default()
        };

        let report = build_binary_verification_report(&summary);

        assert!(!report.proof_grade_gate.accepted);
        assert_eq!(report.proof_grade_gate.required_vcs, 2);
        assert_eq!(report.proof_grade_gate.solver_dispatches, 1);
        assert!(report.proof_grade_gate.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryProofGradeGateRejectionReport::RequiredVcCoverageIncomplete {
                    vc_count: 2,
                    solver_dispatches: 1,
                }
            )
        }));
        assert!(report.proof_grade_gate.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryProofGradeGateRejectionReport::NonProvedVerificationConditions {
                    vc_count: 2,
                    total_results: 1,
                    proved: 1,
                    unproved_vcs: 1,
                    non_proved_results: 0,
                }
            )
        }));
        assert!(report.proof_grade_gate.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryProofGradeGateRejectionReport::ReplayCoverageIncomplete {
                    vc_count: 2,
                    replay_records: 1,
                    replayed: 1,
                }
            )
        }));
    }

    #[test]
    fn decompilation_report_gate_rejects_unvalidated_reconstruction_in_json_and_terminal() {
        let dispatch = checked_dispatch("main:vc0", "main", 0x401010);
        let artifact = DecompilationArtifact {
            verification: verification_summary(1, vec![dispatch.clone()]),
            functions: vec![DecompiledFunction {
                output: Some(DecompiledOutput {
                    validation: ReconstructionValidationStatus::Unknown,
                    ..validated_output()
                }),
                ..proof_grade_function("main", 0x401000, 1, vec![dispatch])
            }],
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        };

        let report = build_binary_decompilation_report(&artifact);
        let json = serde_json::to_value(&report.proof_grade_gate).expect("gate serializes");
        let text = format_binary_decompilation_report(&report);

        assert!(!report.proof_grade_gate.accepted);
        assert_eq!(json["reconstruction_validated"], false);
        assert!(
            json["rejections"]
                .as_array()
                .expect("rejections array")
                .iter()
                .any(|reason| reason.get("ReconstructionValidationNotValidated").is_some())
        );
        assert!(text.contains("reconstruction_validated=false"));
        assert!(text.contains("reconstruction validation not proof-grade: NotAttempted"));
        assert!(text.contains("reconstruction validation not proof-grade: Unknown"));
    }

    #[test]
    fn binary_report_gate_rejects_raw_solver_proof_bytes_explicitly() {
        let mut dispatch = checked_dispatch("main:vc0", "main", 0x401010);
        dispatch.result = Some(VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: 2,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: Some(b"raw solver proof bytes".to_vec()),
            solver_warnings: None,
            native_proof_envelope: None,
        });
        let summary = BinaryVerificationSummary {
            status: BinaryVerificationStatus::Proved,
            trust_level: TrustLevel::ProofGrade,
            total_vcs: 1,
            proved: 1,
            replay: ReplayStatus::Replayed,
            solver_dispatch: vec![dispatch],
            ..Default::default()
        };

        let report = build_binary_verification_report(&summary);
        let json = serde_json::to_value(&report.proof_grade_gate).expect("gate serializes");
        let report_json = serde_json::to_value(&report).expect("report serializes");
        let text = format_binary_verification_report(&report);

        assert!(!report.proof_grade_gate.accepted);
        assert_eq!(report.certificate_checks.certificate_candidates, 1);
        assert_eq!(report.certificate_checks.checked_certificates, 1);
        assert_eq!(report.certificate_checks.raw_solver_proof_bytes, 1);
        assert_eq!(report.certificate_checks.raw_solver_proof_byte_count, 22);
        assert_eq!(report.solver_dispatches[0].raw_solver_proof_byte_count, 22);
        assert_eq!(report.proof_grade_gate.raw_solver_proof_byte_count, 22);
        assert!(report.certificate_checks.checked_certificates_satisfy_coverage);
        assert!(!report.certificate_checks.raw_solver_proof_bytes_satisfy_coverage);
        assert!(!report.certificate_checks.structural_manifest_validation_satisfies_coverage);
        assert!(report.proof_grade_gate.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryProofGradeGateRejectionReport::RawSolverProofBytesPresent { count: 1 }
            )
        }));
        assert!(
            json["rejections"]
                .as_array()
                .expect("rejections array")
                .iter()
                .any(|reason| reason.get("RawSolverProofBytesPresent").is_some())
        );
        assert_eq!(report_json["certificate_checks"]["checked_certificates"], 1);
        assert_eq!(
            report_json["certificate_checks"]["raw_solver_proof_bytes_satisfy_coverage"],
            false
        );
        assert_eq!(
            report_json["certificate_checks"]["structural_manifest_validation_satisfies_coverage"],
            false
        );
        assert!(text.contains("raw solver proof bytes present: 1"));
        assert!(text.contains("raw_satisfies_coverage=false"));
        assert!(text.contains("manifest_structural_satisfies_coverage=false"));
    }

    #[test]
    fn binary_report_includes_unsupported_counts_and_binary_locations() {
        let artifact = DecompilationArtifact {
            binary: BinaryArtifactMetadata {
                path: Some("fixtures/tiny".to_string()),
                architecture: "x86_64".to_string(),
                entry_point: Some(0x401000),
                ..Default::default()
            },
            source_provenance: BinarySourceProvenanceSummary {
                status: "unavailable".to_string(),
                exact_mapping_count: 0,
                ambiguous_mapping_count: 0,
                diagnostics: vec![
                    "exact debug/source provenance is unavailable; diagnostics remain binary-address-only"
                        .to_string(),
                ],
                source_backpropagation_allowed: false,
            },
            unsupported: UnsupportedLedger {
                records: vec![
                    unsupported_record("lift", "unsupported opcode", 0x401010),
                    unsupported_record("decompile", "unresolved edge", 0x401020),
                ],
            },
            verification: trust_types::BinaryVerificationSummary {
                unsupported_ledger: UnsupportedLedger {
                    records: vec![unsupported_record("verify", "unsupported vc", 0x401030)],
                },
                unsupported: 1,
                ..Default::default()
            },
            functions: vec![DecompiledFunction {
                name: "main".to_string(),
                entry: 0x401000,
                address_range: Some(BinaryAddressRange { start: 0x401000, end: 0x401040 }),
                origin: Some(origin(0x401000)),
                unsupported: UnsupportedLedger {
                    records: vec![unsupported_record("lift", "unsupported opcode", 0x401018)],
                },
                trust_level: TrustLevel::Exploratory,
                ..Default::default()
            }],
            trust_level: TrustLevel::Exploratory,
            ..Default::default()
        };

        let report = build_binary_decompilation_report(&artifact);
        assert_eq!(report.trust_level, TrustLevel::Exploratory);
        assert_eq!(report.entry_point_display.as_deref(), Some("0x401000"));
        assert_eq!(report.source_provenance.status, "unavailable");
        assert_eq!(report.source_provenance.exact_mapping_count, 0);
        assert_eq!(report.source_provenance.ambiguous_mapping_count, 0);
        assert!(!report.source_provenance.source_backpropagation_allowed);
        assert_eq!(report.unsupported.total_records, 2);
        assert_eq!(report.unsupported.by_stage["lift"], 1);
        assert_eq!(report.unsupported.by_feature["unresolved edge"], 1);
        assert_eq!(report.unsupported.locations[0].instruction_address_display, "0x401010");
        assert_eq!(report.verification.unsupported_ledger.total_records, 1);
        assert_eq!(
            report.verification.unsupported_ledger.locations[0].instruction_address,
            0x401030
        );
        assert_eq!(report.functions[0].entry_display, "0x401000");
        assert_eq!(
            report.functions[0].address_range.as_ref().expect("range").range_display,
            "[0x401000, 0x401040)"
        );
        assert_eq!(report.functions[0].unsupported.total_records, 1);

        let text = format_binary_decompilation_report(&report);
        assert!(text.contains("Unsupported ledger: 2 records"));
        assert!(text.contains("Source provenance: unavailable"));
        assert!(text.contains("source_backpropagation_allowed=false"));
        assert!(text.contains("main @0x401000 [0x401000, 0x401040)"));
    }

    #[test]
    fn binary_report_surfaces_unsupported_family_counts_in_json_and_text() {
        let artifact = DecompilationArtifact {
            unsupported: UnsupportedLedger {
                records: vec![
                    unsupported_arch_record(
                        "lift",
                        "aarch64",
                        "svc #0",
                        "unsupported exception boundary",
                        0x401010,
                    ),
                    unsupported_arch_record(
                        "lift",
                        "aarch64",
                        "dmb ish",
                        "unsupported memory-order barrier",
                        0x401014,
                    ),
                ],
            },
            verification: BinaryVerificationSummary {
                unsupported_ledger: UnsupportedLedger {
                    records: vec![unsupported_arch_record(
                        "replay",
                        "aarch64",
                        "ret",
                        "missing instruction bytes for exact replay identity",
                        0x401018,
                    )],
                },
                unsupported: 1,
                ..Default::default()
            },
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        };

        let report = build_binary_decompilation_report(&artifact);
        assert_eq!(report.unsupported.by_family[UNSUPPORTED_FAMILY_AARCH64_EXCEPTION_BOUNDARY], 1);
        assert_eq!(
            report.unsupported.by_family[UNSUPPORTED_FAMILY_AARCH64_MEMORY_ORDER_BOUNDARY],
            1
        );
        assert_eq!(
            report.verification.unsupported_ledger.by_family
                [UNSUPPORTED_FAMILY_BINARY_REPLAY_INSTRUCTION_IDENTITY],
            1
        );
        assert_eq!(
            report.proof_grade_gate.unsupported_by_family
                [UNSUPPORTED_FAMILY_AARCH64_EXCEPTION_BOUNDARY],
            1
        );
        assert_eq!(
            report.proof_grade_gate.unsupported_by_family
                [UNSUPPORTED_FAMILY_AARCH64_MEMORY_ORDER_BOUNDARY],
            1
        );
        assert_eq!(
            report.proof_grade_gate.unsupported_by_family
                [UNSUPPORTED_FAMILY_BINARY_REPLAY_INSTRUCTION_IDENTITY],
            1
        );
        assert_eq!(report.proof_grade_gate.unsupported_family_counts.len(), 3);

        let json = serde_json::to_value(&report).expect("report serializes");
        assert_eq!(
            json["unsupported"]["by_family"][UNSUPPORTED_FAMILY_AARCH64_EXCEPTION_BOUNDARY],
            1
        );
        assert_eq!(
            json["verification"]["unsupported_ledger"]["by_family"]
                [UNSUPPORTED_FAMILY_BINARY_REPLAY_INSTRUCTION_IDENTITY],
            1
        );
        assert_eq!(
            json["proof_grade_gate"]["unsupported_by_family"]
                [UNSUPPORTED_FAMILY_AARCH64_MEMORY_ORDER_BOUNDARY],
            1
        );
        assert_eq!(
            json["proof_grade_gate"]["unsupported_family_counts"][0]["family"],
            UNSUPPORTED_FAMILY_AARCH64_EXCEPTION_BOUNDARY
        );

        let text = format_binary_decompilation_report(&report);
        assert!(text.contains(
            "by family {binary.aarch64.exception_boundary: 1, binary.aarch64.memory_order_boundary: 1}"
        ));
        assert!(text.contains(
            "unsupported_families={binary.aarch64.exception_boundary: 1, binary.aarch64.memory_order_boundary: 1, binary.replay.instruction_identity: 1}"
        ));
    }

    #[test]
    fn binary_report_golden_surfaces_aarch64_atomic_semantic_facts_fail_closed() {
        let dispatch = checked_dispatch("main:vc0", "main", 0x401010);
        let artifact = DecompilationArtifact {
            binary: exact_binary_metadata(),
            unsupported: UnsupportedLedger {
                records: vec![
                    UnsupportedRecord {
                        operand: Some("[x0]".to_string()),
                        ..unsupported_arch_record(
                            "lift",
                            "aarch64",
                            "LDAXR",
                            "unsupported AArch64 atomic/exclusive memory-order semantics",
                            0x401014,
                        )
                    },
                    UnsupportedRecord {
                        operand: Some("w1, [x0]".to_string()),
                        ..unsupported_arch_record(
                            "lift",
                            "aarch64",
                            "STLXR",
                            "unsupported AArch64 atomic/exclusive memory-order semantics",
                            0x401018,
                        )
                    },
                ],
            },
            verification: verification_summary(1, vec![dispatch]),
            reconstruction: validated_reconstruction(),
            source_provenance: exact_source_provenance(),
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        };

        let report = build_binary_decompilation_report(&artifact);
        let json = serde_json::to_value(&report).expect("report serializes");
        let text = format_binary_decompilation_report(&report);
        let rejection_kinds = json["proof_grade_gate"]["rejections"]
            .as_array()
            .expect("gate rejections should serialize")
            .iter()
            .map(|rejection| {
                rejection
                    .as_object()
                    .and_then(|object| object.keys().next())
                    .expect("rejection should serialize as enum object")
                    .clone()
            })
            .collect::<Vec<_>>();
        let facts = json["unsupported"]["aarch64_atomic_semantic_facts"]
            .as_array()
            .expect("atomic facts should serialize");
        let snapshot = serde_json::json!({
            "proof_grade_gate": {
                "accepted": json["proof_grade_gate"]["accepted"],
                "unsupported_records": json["proof_grade_gate"]["unsupported_records"],
                "aarch64_atomic_semantic_fact_count": json["proof_grade_gate"]["aarch64_atomic_semantic_fact_count"],
                "aarch64_atomic_semantic_facts_consumed_by_proof_model": json["proof_grade_gate"]["aarch64_atomic_semantic_facts_consumed_by_proof_model"],
                "aarch64_atomic_semantic_fact_rejections": json["proof_grade_gate"]["aarch64_atomic_semantic_fact_rejections"],
                "blocker_group_counts": {
                    "unsupported_ledger": json["proof_grade_gate"]["blocker_groups"]["unsupported_ledger"].as_array().unwrap().len(),
                },
                "rejection_kinds": rejection_kinds,
            },
            "unsupported": {
                "total_records": json["unsupported"]["total_records"],
                "aarch64_atomic_semantic_fact_count": json["unsupported"]["aarch64_atomic_semantic_fact_count"],
                "memory_order_family": json["unsupported"]["by_family"][UNSUPPORTED_FAMILY_AARCH64_MEMORY_ORDER_BOUNDARY],
                "facts": facts
                    .iter()
                    .map(|fact| serde_json::json!({
                        "opcode": fact["opcode"],
                        "operand": fact["operand"],
                        "location": fact["location"]["instruction_address_display"],
                        "access": fact["access"],
                        "ordering": fact["ordering"],
                        "exclusive_monitor": fact["exclusive_monitor"],
                        "reports_status": fact["reports_status"],
                        "consumed_by_proof_model": fact["consumed_by_proof_model"],
                        "proof_grade_accepted": fact["proof_grade_accepted"],
                        "missing_witnesses": fact["missing_witnesses"],
                    }))
                    .collect::<Vec<_>>(),
            },
            "unresolved_blockers": {
                "unsupported_ledger": json["unresolved_blockers"]["by_family"]["unsupported_ledger"],
                "entries": json["unresolved_blockers"]["entries"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .filter(|entry| entry["feature"] == "aarch64_atomic_semantic_facts_not_consumed")
                    .map(|entry| serde_json::json!({
                        "family": entry["family"],
                        "stage": entry["stage"],
                        "feature": entry["feature"],
                        "reason": entry["reason"],
                    }))
                    .collect::<Vec<_>>(),
            },
            "text_markers": [
                "aarch64_atomic_semantic_facts=2",
                "aarch64_atomic_facts_consumed=false",
                "AArch64 atomic semantic facts:",
                "LDAXR @0x401014 operand=[x0] | access=Read, ordering=Acquire, exclusive_monitor=LoadReserve",
                "STLXR @0x401018 operand=w1, [x0] | access=Write, ordering=Release, exclusive_monitor=StoreConditional, reports_status=true",
                "AArch64 LDAXR semantic fact is present but not proof-consumed",
                "AArch64 atomic semantic facts not proof-consumed: 2/2 unconsumed",
                "unsupported_ledger/aarch64_atomic_semantic_facts_not_consumed stage=proof_grade_gate",
            ],
        });
        let expected: serde_json::Value = serde_json::from_str(include_str!(
            "fixtures/binary_aarch64_atomic_semantic_facts_golden.json"
        ))
        .expect("parse binary AArch64 atomic semantic facts golden");

        assert_eq!(snapshot, expected);
        assert!(!report.proof_grade_gate.accepted);
        assert_eq!(report.unsupported.aarch64_atomic_semantic_fact_count, 2);
        assert_eq!(report.proof_grade_gate.aarch64_atomic_semantic_fact_count, 2);
        assert!(!report.proof_grade_gate.aarch64_atomic_semantic_facts_consumed_by_proof_model);
        assert!(report.proof_grade_gate.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryProofGradeGateRejectionReport::Aarch64AtomicSemanticFactsNotConsumed {
                    count: 2,
                    unconsumed: 2,
                    ..
                }
            )
        }));

        for marker in expected["text_markers"].as_array().expect("text markers") {
            assert!(
                text.contains(marker.as_str().expect("text marker string")),
                "missing text marker `{marker}` in report:\n{text}"
            );
        }
    }

    #[test]
    fn binary_report_surfaces_aarch64_sync_boundary_facts_fail_closed() {
        let dispatch = checked_dispatch("main:vc0", "main", 0x401010);
        let artifact = DecompilationArtifact {
            binary: exact_binary_metadata(),
            unsupported: UnsupportedLedger {
                records: vec![
                    UnsupportedRecord {
                        operand: Some("ish".to_string()),
                        ..unsupported_arch_record(
                            "lift",
                            "aarch64",
                            "DMB",
                            "unsupported AArch64 memory-order boundary; kind=DataMemoryBarrier; scope=InnerShareable; ordering=LoadsAndStores; clears_exclusive_monitor=false; raw_option=0xb",
                            0x401014,
                        )
                    },
                    UnsupportedRecord {
                        operand: Some("sy".to_string()),
                        ..unsupported_arch_record(
                            "lift",
                            "aarch64",
                            "ISB",
                            "unsupported AArch64 memory-order boundary; kind=InstructionSynchronizationBarrier; scope=FullSystem; ordering=InstructionStream; clears_exclusive_monitor=false; raw_option=0xf",
                            0x401018,
                        )
                    },
                ],
            },
            verification: verification_summary(1, vec![dispatch]),
            reconstruction: validated_reconstruction(),
            source_provenance: exact_source_provenance(),
            trust_level: TrustLevel::ProofGrade,
            ..Default::default()
        };

        let report = build_binary_decompilation_report(&artifact);
        let json = serde_json::to_value(&report).expect("report serializes");
        let text = format_binary_decompilation_report(&report);
        let facts = json["unsupported"]["aarch64_sync_boundary_facts"]
            .as_array()
            .expect("sync boundary facts should serialize");

        assert!(!report.proof_grade_gate.accepted);
        assert_eq!(report.unsupported.aarch64_sync_boundary_fact_count, 2);
        assert_eq!(report.proof_grade_gate.aarch64_sync_boundary_fact_count, 2);
        assert!(!report.proof_grade_gate.aarch64_sync_boundary_facts_consumed_by_proof_model);
        assert_eq!(facts[0]["opcode"], "DMB");
        assert_eq!(facts[0]["operand"], "ish");
        assert_eq!(facts[0]["kind"], "DataMemoryBarrier");
        assert_eq!(facts[0]["scope"], "InnerShareable");
        assert_eq!(facts[0]["ordering"], "LoadsAndStores");
        assert_eq!(facts[0]["raw_option"], 0xb);
        assert_eq!(facts[0]["clears_exclusive_monitor"], false);
        assert!(
            facts[0]["missing_witnesses"]
                .as_array()
                .expect("missing witnesses")
                .iter()
                .any(|witness| witness == "shareability scope propagation")
        );
        assert_eq!(facts[1]["kind"], "InstructionSynchronizationBarrier");
        assert_eq!(facts[1]["ordering"], "InstructionStream");
        assert!(
            facts[1]["missing_witnesses"]
                .as_array()
                .expect("missing witnesses")
                .iter()
                .any(|witness| witness == "pipeline flush witness")
        );
        assert!(report.proof_grade_gate.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryProofGradeGateRejectionReport::Aarch64SyncBoundaryFactsNotConsumed {
                    count: 2,
                    unconsumed: 2,
                    ..
                }
            )
        }));
        assert!(
            json["unresolved_blockers"]["entries"]
                .as_array()
                .expect("unresolved entries")
                .iter()
                .any(|entry| entry["feature"] == "aarch64_sync_boundary_facts_not_consumed")
        );
        assert!(text.contains("aarch64_sync_boundary_facts=2"));
        assert!(text.contains("aarch64_sync_boundary_facts_consumed=false"));
        assert!(text.contains("AArch64 sync boundary facts:"));
        assert!(text.contains(
            "DMB @0x401014 operand=ish raw_option=0xb | kind=DataMemoryBarrier, scope=InnerShareable"
        ));
        assert!(text.contains("AArch64 DMB sync boundary fact is present but not proof-consumed"));
        assert!(text.contains("AArch64 sync boundary facts not proof-consumed: 2/2 unconsumed"));
        assert!(text.contains(
            "unsupported_ledger/aarch64_sync_boundary_facts_not_consumed stage=proof_grade_gate"
        ));
    }

    #[test]
    fn binary_source_provenance_report_preserves_backpropagation_gate() {
        let exact = BinarySourceProvenanceReport::from_summary(&BinarySourceProvenanceSummary {
            status: "exact".to_string(),
            exact_mapping_count: 2,
            ambiguous_mapping_count: 0,
            diagnostics: vec![],
            source_backpropagation_allowed: true,
        });
        assert_eq!(exact.status, "exact");
        assert_eq!(exact.exact_mapping_count, 2);
        assert!(exact.source_backpropagation_allowed);

        let ambiguous =
            BinarySourceProvenanceReport::from_summary(&BinarySourceProvenanceSummary {
                status: "ambiguous".to_string(),
                exact_mapping_count: 0,
                ambiguous_mapping_count: 3,
                diagnostics: vec!["ambiguous rows withheld".to_string()],
                source_backpropagation_allowed: false,
            });
        assert_eq!(ambiguous.status, "ambiguous");
        assert_eq!(ambiguous.ambiguous_mapping_count, 3);
        assert_eq!(ambiguous.diagnostics, vec!["ambiguous rows withheld"]);
        assert!(!ambiguous.source_backpropagation_allowed);
    }

    #[test]
    fn binary_source_provenance_report_fail_closes_binary_address_only_backpropagation() {
        let report = BinarySourceProvenanceReport::from_summary(&BinarySourceProvenanceSummary {
            status: "unavailable".to_string(),
            exact_mapping_count: 0,
            ambiguous_mapping_count: 0,
            diagnostics: vec![
                "exact debug/source provenance is unavailable; diagnostics remain binary-address-only"
                    .to_string(),
            ],
            source_backpropagation_allowed: true,
        });

        assert!(!report.source_backpropagation_allowed);
        assert!(!report.effective_source_backpropagation_allowed());
        assert!(report.binary_address_diagnostics_allowed());
        assert_eq!(
            report.source_backpropagation_disabled_reasons,
            vec![
                "source_provenance_status_not_exact:unavailable".to_string(),
                "exact_source_mapping_missing".to_string(),
            ]
        );

        let diagnostics = report.typed_diagnostics();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].kind, BinarySourceProvenanceDiagnosticKind::BinaryAddressOnly);
        assert!(!diagnostics[0].source_backpropagation_allowed);
        assert!(diagnostics[0].binary_address_diagnostics_allowed);
    }

    #[test]
    fn binary_report_renders_binary_address_only_provenance_gate_diagnostic() {
        let artifact = DecompilationArtifact {
            source_provenance: BinarySourceProvenanceSummary {
                status: "unavailable".to_string(),
                exact_mapping_count: 0,
                ambiguous_mapping_count: 0,
                diagnostics: vec![
                    "exact debug/source provenance is unavailable; diagnostics remain binary-address-only"
                        .to_string(),
                ],
                source_backpropagation_allowed: true,
            },
            ..Default::default()
        };

        let text = format_binary_decompilation_summary(&artifact);
        assert!(text.contains("source_backpropagation_allowed=false"));
        assert!(text.contains("binary_address_diagnostics_allowed=true"));
        assert!(text.contains(
            "disabled_reasons=[source_provenance_status_not_exact:unavailable, exact_source_mapping_missing]"
        ));
        assert!(text.contains("Source provenance diagnostic: binary_address_only"));
        assert!(text.contains("diagnostics remain binary-address-only"));
    }

    #[test]
    fn binary_verification_report_preserves_vc_and_replay_statuses() {
        let summary = trust_types::BinaryVerificationSummary {
            status: BinaryVerificationStatus::Mixed,
            trust_level: TrustLevel::Partial,
            total_vcs: 4,
            proved: 1,
            failed: 1,
            unknown: 1,
            timeout: 1,
            replay: ReplayStatus::NotAttempted,
            solver_dispatch: vec![
                SolverDispatchRecord {
                    id: "main:unsat".to_string(),
                    function: Some("main".to_string()),
                    origin: Some(origin(0x401010)),
                    solver: "ay".to_string(),
                    status: SolverDispatchStatus::Unsat,
                    result: Some(VerificationResult::Proved {
                        solver: "ay".into(),
                        time_ms: 1,
                        strength: ProofStrength::smt_unsat(),
                        proof_certificate: None,
                        solver_warnings: None,
                        native_proof_envelope: None,
                    }),
                    replay: ReplayStatus::Replayed,
                    ..Default::default()
                },
                SolverDispatchRecord {
                    id: "main:sat".to_string(),
                    function: Some("main".to_string()),
                    origin: Some(origin(0x401014)),
                    solver: "ay".to_string(),
                    status: SolverDispatchStatus::Sat,
                    result: Some(VerificationResult::Failed {
                        solver: "ay".into(),
                        time_ms: 3,
                        counterexample: Some(Counterexample::new(vec![(
                            "rax".to_string(),
                            CounterexampleValue::Uint(7),
                        )])),
                    }),
                    replay: ReplayStatus::Failed,
                    ..Default::default()
                },
                SolverDispatchRecord {
                    id: "main:unknown".to_string(),
                    function: Some("main".to_string()),
                    origin: Some(origin(0x401018)),
                    solver: "ay".to_string(),
                    status: SolverDispatchStatus::Unknown,
                    result: Some(VerificationResult::Unknown {
                        solver: "ay".into(),
                        time_ms: 5,
                        reason: "quantifier".to_string(),
                    }),
                    replay: ReplayStatus::NotAttempted,
                    ..Default::default()
                },
                SolverDispatchRecord {
                    id: "main:timeout".to_string(),
                    function: Some("main".to_string()),
                    origin: Some(origin(0x40101c)),
                    solver: "ay".to_string(),
                    status: SolverDispatchStatus::Timeout,
                    result: Some(VerificationResult::Timeout {
                        solver: "ay".into(),
                        timeout_ms: 10,
                    }),
                    replay: ReplayStatus::NotAttempted,
                    ..Default::default()
                },
            ],
            ..Default::default()
        };

        let report = build_binary_verification_report(&summary);
        assert_eq!(report.status, BinaryVerificationStatus::Mixed);
        assert_eq!(report.trust_level, TrustLevel::Partial);
        assert_eq!(report.total_vcs, 4);
        assert_eq!(report.vc_status_counts["Unsat"], 1);
        assert_eq!(report.vc_status_counts["Sat"], 1);
        assert_eq!(report.vc_status_counts["Unknown"], 1);
        assert_eq!(report.vc_status_counts["Timeout"], 1);
        assert_eq!(report.replay_status_counts["Replayed"], 1);
        assert_eq!(report.replay_status_counts["Failed"], 1);
        assert_eq!(report.replay_status_counts["NotAttempted"], 2);
        assert_eq!(report.solver_dispatches[1].result_status.as_deref(), Some("failed"));
        assert_eq!(
            report.solver_dispatches[2].location.as_ref().expect("location").source.file,
            "binary:0x401018"
        );

        let text = format_binary_verification_report(&report);
        assert!(text.contains(
            "VCs: 4 total, 1 proved, 1 failed, 1 unknown, 1 timeout, 0 unsupported, 0 rejected"
        ));
        assert!(text.contains("main:sat @0x401014: Sat"));
        assert!(text.contains("replay: Failed, result: failed"));
    }
}
