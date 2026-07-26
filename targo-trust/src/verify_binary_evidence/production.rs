// Checked-certificate production: produce, persist, and audit-export the
// per-VC checked certificate artifacts.

use std::collections::BTreeMap;
use std::path::Path;

use trust_proof_cert::{
    AuditOnlyRawSolverProofBytes, BinaryCertificateCheckRequest, BinaryCertificateCheckResult,
    CheckError, CheckedBinaryCertificateAuditExport,
    CheckedBinaryCertificateAuditExportBundleEntry, CheckedBinaryCertificateExternalCheckerRunner,
    CheckedBinaryCertificateManifestAcceptanceRecord,
    CheckedBinaryCertificateManifestAcceptanceRequest, CheckedBinaryCertificateManifestEntry,
    StructuralBinaryCertificateChecker, import_checked_certificate_manifest_entry_for_dispatch,
    persist_solver_proof_export_artifacts, produce_checked_certificate_artifact,
};
use trust_types::{
    BinaryArtifactDigestIdentity, ProofCertificateStatus, ReplayStatus, SolverDispatchRecord,
    VerificationResult,
};

use super::{
    CheckedCertificateCheckRecord, CheckedCertificateExportRowRecord,
    CheckedCertificateProductionBlockerRecord, CheckedCertificateProofExportRecord,
    LoadedNormalizedSolverProofExportArtifact, RawSolverProofByteEvidence,
    checked_certificate_replay_digest_identity_record,
    dispatch_binary_artifact_digest_identity_acceptance_blockers, has_solver_proof_bytes,
    is_canonical_sha256_hex, persist_normalized_solver_proof_export_artifact, stable_json_sha256,
};
use crate::input_limits::{MAX_SAVED_PROOF_REPORT_BYTES, read_bounded_utf8_file};

#[derive(Debug, Clone)]
pub(super) struct DispatchCanonicalBinding {
    pub(super) canonical_vc_bytes: Vec<u8>,
    pub(super) vc_sha256: String,
    pub(super) origin_sha256: String,
}

impl DispatchCanonicalBinding {
    pub(super) fn new(
        canonical_vc_bytes: Vec<u8>,
        vc_sha256: String,
        origin_sha256: String,
    ) -> Self {
        Self { canonical_vc_bytes, vc_sha256, origin_sha256 }
    }
}

#[derive(Debug, Clone)]
pub(super) struct NormalizedProofExportCandidate {
    pub(super) format: String,
    pub(super) proof_sha256: String,
    pub(super) artifact_path: Option<String>,
}

#[derive(Debug, Clone)]
pub(super) struct CheckedCertificateProductionCandidate {
    pub(super) dispatch_index: usize,
    pub(super) dispatch: SolverDispatchRecord,
    pub(super) binding: DispatchCanonicalBinding,
    pub(super) proof_export: NormalizedProofExportCandidate,
    pub(super) proof_export_artifact: LoadedNormalizedSolverProofExportArtifact,
    pub(super) replay_transcript_digest: Option<String>,
}

#[derive(Debug, Clone)]
pub(super) struct CheckedCertificateProductionSuccess {
    pub(super) dispatch_id: String,
    pub(super) artifact_path: String,
    pub(super) proof_export_metadata_path: String,
    pub(super) proof_export_payload_path: String,
    pub(super) certificate_sha256: String,
    pub(super) manifest_entry: CheckedBinaryCertificateManifestEntry,
    pub(super) acceptance_record: CheckedBinaryCertificateManifestAcceptanceRecord,
    pub(super) manifest_identity_sha256: String,
    pub(super) source_backpropagation_gate_sha256: Option<String>,
    pub(super) replay_transcript_digest: Option<String>,
    pub(super) binary_artifact_digest_identity: BinaryArtifactDigestIdentity,
    pub(super) replay: ReplayStatus,
    pub(super) checker: String,
    pub(super) checker_version: String,
    pub(super) format: String,
    pub(super) production_checker_evidence_sha256: String,
    pub(super) proof_export_artifact_sha256: String,
    pub(super) proof_export_artifact_path: String,
    pub(super) external_checker_binary_sha256: String,
    pub(super) external_checker_invocation_sha256: String,
    pub(super) external_checker_stdout_sha256: Option<String>,
    pub(super) external_checker_stderr_sha256: Option<String>,
}

pub(super) fn normalized_proof_export_present(
    record: &SolverDispatchRecord,
) -> Option<NormalizedProofExportCandidate> {
    if has_solver_proof_bytes(record) {
        return None;
    }

    match &record.certificate {
        ProofCertificateStatus::Present { format, sha256: Some(proof_sha256), artifact_path }
            if !format.trim().is_empty() && format != "solver-native" =>
        {
            Some(NormalizedProofExportCandidate {
                format: format.clone(),
                proof_sha256: proof_sha256.clone(),
                artifact_path: artifact_path.clone(),
            })
        }
        _ => None,
    }
}

pub(super) fn raw_solver_proof_byte_evidence(
    record: &SolverDispatchRecord,
) -> Option<RawSolverProofByteEvidence> {
    let Some(VerificationResult::Proved { solver, proof_certificate: Some(bytes), .. }) =
        &record.result
    else {
        return None;
    };
    let format = match &record.certificate {
        ProofCertificateStatus::Present { format, .. } if !format.trim().is_empty() => {
            Some(format.clone())
        }
        _ => None,
    };
    let raw = AuditOnlyRawSolverProofBytes::new(*solver, format, bytes);
    Some(RawSolverProofByteEvidence {
        solver: raw.solver,
        format: raw.format,
        sha256: raw.bytes_sha256,
        byte_len: raw.byte_len,
        audit_only: true,
    })
}

pub(super) struct ProofExportRecordInput<'a> {
    pub(super) dispatch: &'a SolverDispatchRecord,
    pub(super) binding: Option<&'a DispatchCanonicalBinding>,
    pub(super) proof_export_present: Option<&'a NormalizedProofExportCandidate>,
    pub(super) proof_export: Option<&'a NormalizedProofExportCandidate>,
    pub(super) proof_export_artifact: Option<&'a LoadedNormalizedSolverProofExportArtifact>,
    pub(super) raw_proof: Option<&'a RawSolverProofByteEvidence>,
    pub(super) checked: bool,
    pub(super) blocker_codes: &'a [String],
}

pub(super) fn proof_export_record(
    input: ProofExportRecordInput<'_>,
) -> CheckedCertificateProofExportRecord {
    let ProofExportRecordInput {
        dispatch,
        binding,
        proof_export_present,
        proof_export,
        proof_export_artifact,
        raw_proof,
        checked,
        blocker_codes,
    } = input;

    let status = if checked {
        "already_checked"
    } else if raw_proof.is_some() {
        "blocked_raw_solver_bytes"
    } else if proof_export_present
        .as_ref()
        .is_some_and(|export| !is_canonical_sha256_hex(&export.proof_sha256))
    {
        "blocked_noncanonical_digest"
    } else if proof_export_present.is_some()
        && proof_export_artifact.is_none()
        && blocker_codes.iter().any(|code| code.starts_with("normalized-proof-export"))
    {
        "blocked_invalid_normalized_export"
    } else if proof_export.is_some() {
        "available"
    } else if binding.is_none() {
        "blocked_missing_canonical_binding"
    } else {
        "missing"
    };

    CheckedCertificateProofExportRecord {
        dispatch_id: dispatch.id.clone(),
        function: dispatch.function.clone(),
        solver: dispatch.solver.clone(),
        backend: dispatch.backend.clone(),
        canonical_binding: binding.is_some(),
        vc_sha256: binding.map(|binding| binding.vc_sha256.clone()),
        origin_sha256: binding.map(|binding| binding.origin_sha256.clone()),
        status: status.to_string(),
        format: proof_export_present.map(|export| export.format.clone()),
        proof_sha256: proof_export_present.map(|export| export.proof_sha256.clone()),
        proof_export_metadata_sha256: proof_export_artifact
            .map(|loaded| loaded.artifact.proof_export_metadata_sha256.clone()),
        proof_export_artifact_sha256: proof_export_artifact
            .map(|loaded| loaded.content_sha256.clone()),
        proof_export_content_addressed: proof_export_artifact.map(|_| true),
        artifact_path: proof_export_present.and_then(|export| export.artifact_path.clone()),
        proof_export_metadata_path: None,
        proof_export_payload_path: None,
        checked_certificate_artifact_path: None,
        raw_solver_proof_bytes: raw_proof.cloned(),
        blocker_codes: blocker_codes.to_vec(),
    }
}

pub(super) fn certificate_check_record(
    dispatch: &SolverDispatchRecord,
    proof_export_present: Option<&NormalizedProofExportCandidate>,
    proof_export: Option<&NormalizedProofExportCandidate>,
    raw_proof: Option<&RawSolverProofByteEvidence>,
    checked: bool,
    blocker_codes: &[String],
) -> CheckedCertificateCheckRecord {
    let digest_identity_blockers =
        dispatch_binary_artifact_digest_identity_acceptance_blockers(dispatch);
    if !digest_identity_blockers.is_empty() {
        let mut blocker_codes = blocker_codes.to_vec();
        if !blocker_codes.iter().any(|code| code == "binary-artifact-digest-identity-invalid") {
            blocker_codes.push("binary-artifact-digest-identity-invalid".to_string());
        }
        return CheckedCertificateCheckRecord {
            dispatch_id: dispatch.id.clone(),
            function: dispatch.function.clone(),
            status: "rejected".to_string(),
            certificate_status: proof_certificate_status_label(&dispatch.certificate),
            checker: None,
            format: proof_export_present.map(|export| export.format.clone()),
            certificate_sha256: None,
            manifest_identity_sha256: None,
            source_backpropagation_gate_sha256: None,
            replay_transcript_digest: None,
            binary_artifact_digest_identity: dispatch.binary_artifact_digest_identity.clone(),
            replay_digest_identity: checked_certificate_replay_digest_identity_record(
                dispatch.replay,
                None,
                dispatch.binary_artifact_digest_identity.clone(),
            ),
            production_checker_evidence_sha256: None,
            external_checker_binary_sha256: None,
            external_checker_invocation_sha256: None,
            external_checker_stdout_sha256: None,
            external_checker_stderr_sha256: None,
            error_kind: Some("binary-artifact-digest-identity-invalid".to_string()),
            diagnostic: Some(format!(
                "checked-certificate proof-grade evidence rejected: {}",
                digest_identity_blockers.join("; ")
            )),
            blocker_codes,
        };
    }

    if checked {
        let (checker, format, certificate_sha256) = match &dispatch.certificate {
            ProofCertificateStatus::Checked { checker, format, sha256 } => {
                (Some(checker.clone()), Some(format.clone()), sha256.clone())
            }
            _ => (None, None, None),
        };
        return CheckedCertificateCheckRecord {
            dispatch_id: dispatch.id.clone(),
            function: dispatch.function.clone(),
            status: "checked".to_string(),
            certificate_status: proof_certificate_status_label(&dispatch.certificate),
            checker,
            format,
            certificate_sha256,
            manifest_identity_sha256: None,
            source_backpropagation_gate_sha256: None,
            replay_transcript_digest: None,
            binary_artifact_digest_identity: dispatch.binary_artifact_digest_identity.clone(),
            replay_digest_identity: checked_certificate_replay_digest_identity_record(
                dispatch.replay,
                None,
                dispatch.binary_artifact_digest_identity.clone(),
            ),
            production_checker_evidence_sha256: None,
            external_checker_binary_sha256: None,
            external_checker_invocation_sha256: None,
            external_checker_stdout_sha256: None,
            external_checker_stderr_sha256: None,
            error_kind: None,
            diagnostic: None,
            blocker_codes: blocker_codes.to_vec(),
        };
    }

    if let Some(raw) = raw_proof {
        let audit = AuditOnlyRawSolverProofBytes {
            solver: raw.solver.clone(),
            format: raw.format.clone(),
            bytes_sha256: raw.sha256.clone(),
            byte_len: raw.byte_len,
        };
        let check = BinaryCertificateCheckResult::raw_solver_bytes_are_audit_only(
            dispatch.id.clone(),
            &audit,
        );
        let error = check.error.as_ref();
        return CheckedCertificateCheckRecord {
            dispatch_id: dispatch.id.clone(),
            function: dispatch.function.clone(),
            status: "rejected".to_string(),
            certificate_status: proof_certificate_status_label(&dispatch.certificate),
            checker: Some(check.checker.clone()),
            format: raw.format.clone(),
            certificate_sha256: None,
            manifest_identity_sha256: None,
            source_backpropagation_gate_sha256: None,
            replay_transcript_digest: None,
            binary_artifact_digest_identity: dispatch.binary_artifact_digest_identity.clone(),
            replay_digest_identity: checked_certificate_replay_digest_identity_record(
                dispatch.replay,
                None,
                dispatch.binary_artifact_digest_identity.clone(),
            ),
            production_checker_evidence_sha256: None,
            external_checker_binary_sha256: None,
            external_checker_invocation_sha256: None,
            external_checker_stdout_sha256: None,
            external_checker_stderr_sha256: None,
            error_kind: error.map(check_error_kind).map(str::to_string),
            diagnostic: error.map(ToString::to_string),
            blocker_codes: blocker_codes.to_vec(),
        };
    }

    if let Some(proof_export) = proof_export_present
        .as_ref()
        .filter(|export| !is_canonical_sha256_hex(&export.proof_sha256))
    {
        return CheckedCertificateCheckRecord {
            dispatch_id: dispatch.id.clone(),
            function: dispatch.function.clone(),
            status: "rejected".to_string(),
            certificate_status: proof_certificate_status_label(&dispatch.certificate),
            checker: None,
            format: Some(proof_export.format.clone()),
            certificate_sha256: None,
            manifest_identity_sha256: None,
            source_backpropagation_gate_sha256: None,
            replay_transcript_digest: None,
            binary_artifact_digest_identity: dispatch.binary_artifact_digest_identity.clone(),
            replay_digest_identity: checked_certificate_replay_digest_identity_record(
                dispatch.replay,
                None,
                dispatch.binary_artifact_digest_identity.clone(),
            ),
            production_checker_evidence_sha256: None,
            external_checker_binary_sha256: None,
            external_checker_invocation_sha256: None,
            external_checker_stdout_sha256: None,
            external_checker_stderr_sha256: None,
            error_kind: Some("normalized-proof-export-digest-noncanonical".to_string()),
            diagnostic: Some(format!(
                "normalized solver proof export digest is not canonical lowercase SHA-256 hex: {}",
                proof_export.proof_sha256
            )),
            blocker_codes: blocker_codes.to_vec(),
        };
    }

    if let Some(proof_export_blocker_code) = blocker_codes.iter().find(|code| {
        code.starts_with("normalized-proof-export")
            && code.as_str() != "normalized-proof-export-missing"
    }) {
        return CheckedCertificateCheckRecord {
            dispatch_id: dispatch.id.clone(),
            function: dispatch.function.clone(),
            status: "rejected".to_string(),
            certificate_status: proof_certificate_status_label(&dispatch.certificate),
            checker: None,
            format: proof_export_present.map(|export| export.format.clone()),
            certificate_sha256: None,
            manifest_identity_sha256: None,
            source_backpropagation_gate_sha256: None,
            replay_transcript_digest: None,
            binary_artifact_digest_identity: dispatch.binary_artifact_digest_identity.clone(),
            replay_digest_identity: checked_certificate_replay_digest_identity_record(
                dispatch.replay,
                None,
                dispatch.binary_artifact_digest_identity.clone(),
            ),
            production_checker_evidence_sha256: None,
            external_checker_binary_sha256: None,
            external_checker_invocation_sha256: None,
            external_checker_stdout_sha256: None,
            external_checker_stderr_sha256: None,
            error_kind: Some(proof_export_blocker_code.clone()),
            diagnostic: Some(
                "normalized solver proof export artifact is missing, malformed, stale, or not content-addressed"
                    .to_string(),
            ),
            blocker_codes: blocker_codes.to_vec(),
        };
    }

    if let Some(replay_blocker_code) = blocker_codes.iter().find(|code| {
        matches!(
            code.as_str(),
            "replay-transcript-digest-missing" | "replay-transcript-digest-noncanonical"
        )
    }) {
        let diagnostic = if replay_blocker_code == "replay-transcript-digest-noncanonical" {
            "replayed solver dispatch has a noncanonical replay transcript digest"
        } else {
            "replayed solver dispatch is missing a canonical replay transcript digest"
        };
        return CheckedCertificateCheckRecord {
            dispatch_id: dispatch.id.clone(),
            function: dispatch.function.clone(),
            status: "rejected".to_string(),
            certificate_status: proof_certificate_status_label(&dispatch.certificate),
            checker: None,
            format: proof_export_present.map(|export| export.format.clone()),
            certificate_sha256: None,
            manifest_identity_sha256: None,
            source_backpropagation_gate_sha256: None,
            replay_transcript_digest: None,
            binary_artifact_digest_identity: dispatch.binary_artifact_digest_identity.clone(),
            replay_digest_identity: checked_certificate_replay_digest_identity_record(
                dispatch.replay,
                None,
                dispatch.binary_artifact_digest_identity.clone(),
            ),
            production_checker_evidence_sha256: None,
            external_checker_binary_sha256: None,
            external_checker_invocation_sha256: None,
            external_checker_stdout_sha256: None,
            external_checker_stderr_sha256: None,
            error_kind: Some(replay_blocker_code.clone()),
            diagnostic: Some(diagnostic.to_string()),
            blocker_codes: blocker_codes.to_vec(),
        };
    }

    let (status, diagnostic) = if proof_export.is_some() {
        (
            "blocked_checker_selection_missing",
            Some(
                "normalized solver proof export is available, but no production checker is selected"
                    .to_string(),
            ),
        )
    } else {
        (
            "not_run",
            Some(
                "certificate check did not run because no normalized solver proof export exists"
                    .to_string(),
            ),
        )
    };

    CheckedCertificateCheckRecord {
        dispatch_id: dispatch.id.clone(),
        function: dispatch.function.clone(),
        status: status.to_string(),
        certificate_status: proof_certificate_status_label(&dispatch.certificate),
        checker: None,
        format: proof_export.map(|export| export.format.clone()),
        certificate_sha256: None,
        manifest_identity_sha256: None,
        source_backpropagation_gate_sha256: None,
        replay_transcript_digest: None,
        binary_artifact_digest_identity: dispatch.binary_artifact_digest_identity.clone(),
        replay_digest_identity: checked_certificate_replay_digest_identity_record(
            dispatch.replay,
            None,
            dispatch.binary_artifact_digest_identity.clone(),
        ),
        production_checker_evidence_sha256: None,
        external_checker_binary_sha256: None,
        external_checker_invocation_sha256: None,
        external_checker_stdout_sha256: None,
        external_checker_stderr_sha256: None,
        error_kind: None,
        diagnostic,
        blocker_codes: blocker_codes.to_vec(),
    }
}

pub(super) fn produce_one_checked_certificate_artifact(
    export_dir: &Path,
    checker_id: &str,
    checker_version: &str,
    checked_at_unix_ms: u64,
    runner: &CheckedBinaryCertificateExternalCheckerRunner,
    candidate: &CheckedCertificateProductionCandidate,
    dispatch: &mut SolverDispatchRecord,
) -> Result<CheckedCertificateProductionSuccess, CheckedCertificateProductionBlockerRecord> {
    let checker = StructuralBinaryCertificateChecker::new(
        checker_id.to_string(),
        checker_version.to_string(),
        vec![candidate.proof_export.format.clone()],
        checked_at_unix_ms,
    );
    let export = candidate.proof_export_artifact.artifact.proof_export.clone();
    let mut request = BinaryCertificateCheckRequest::from_export(
        &candidate.dispatch,
        &candidate.binding.canonical_vc_bytes,
        &export,
    );
    request.replay_transcript_digest = candidate.replay_transcript_digest.as_deref();
    let normalized_proof_export_path = persist_normalized_solver_proof_export_artifact(
        export_dir,
        &candidate.proof_export_artifact.artifact,
    )
    .map_err(|error| {
        production_blocker_record(
            "normalized-proof-export-persist-failed",
            "checked-certificate-production",
            Some(candidate.dispatch.id.clone()),
            format!(
                "normalized proof export artifact durable publication failed for dispatch {}: {}",
                candidate.dispatch.id, error.detail
            ),
            ["normalized_solver_proof_export"],
        )
    })?;
    let proof_export_artifact_ref = persist_solver_proof_export_artifacts(export_dir, &export)
        .map_err(|error| {
            production_blocker_record(
                "normalized-proof-export-persist-failed",
                "checked-certificate-production",
                Some(candidate.dispatch.id.clone()),
                format!(
                    "normalized proof export artifact persist failed for dispatch {}: {error}",
                    candidate.dispatch.id
                ),
                ["normalized_solver_proof_export"],
            )
        })?;
    let artifact_ref = produce_checked_certificate_artifact(&checker, request, export_dir)
        .map_err(|error| {
            production_blocker_record(
                "checked-certificate-production-failed",
                "checked-certificate-production",
                Some(candidate.dispatch.id.clone()),
                format!(
                    "checked certificate production failed for dispatch {}: {error}",
                    candidate.dispatch.id
                ),
                ["checker_success", "checked_certificate_artifact"],
            )
        })?;
    let artifact_json = read_bounded_utf8_file(&artifact_ref.path, MAX_SAVED_PROOF_REPORT_BYTES)
        .map_err(|error| {
            production_blocker_record(
                "checked-certificate-artifact-readback-failed",
                "checked-certificate-production",
                Some(candidate.dispatch.id.clone()),
                format!(
                    "checked certificate artifact readback failed for dispatch {}: {error}",
                    candidate.dispatch.id
                ),
                ["checked_certificate_artifact"],
            )
        })?;
    let artifact = trust_proof_cert::CheckedBinaryCertificateArtifact::from_json(&artifact_json)
        .map_err(|error| {
            production_blocker_record(
                "checked-certificate-artifact-readback-failed",
                "checked-certificate-production",
                Some(candidate.dispatch.id.clone()),
                format!(
                    "checked certificate artifact readback failed for dispatch {}: {error}",
                    candidate.dispatch.id
                ),
                ["checked_certificate_artifact"],
            )
        })?;
    if artifact.certificate_sha256 != artifact_ref.content_sha256 {
        return Err(production_blocker_record(
            "checked-certificate-artifact-readback-failed",
            "checked-certificate-production",
            Some(candidate.dispatch.id.clone()),
            format!(
                "checked certificate artifact readback digest mismatch for dispatch {}: expected {}, actual {}",
                candidate.dispatch.id, artifact_ref.content_sha256, artifact.certificate_sha256
            ),
            ["checked_certificate_artifact"],
        ));
    }
    let relative_artifact_path = artifact_ref.path.strip_prefix(export_dir).map_err(|_| {
        production_blocker_record(
            "checked-certificate-artifact-path-invalid",
            "checked-certificate-production",
            Some(candidate.dispatch.id.clone()),
            format!(
                "checked certificate artifact path `{}` is outside export dir `{}`",
                artifact_ref.path.display(),
                export_dir.display()
            ),
            ["checked_certificate_artifact"],
        )
    })?;
    let entry = CheckedBinaryCertificateManifestEntry::from_artifact(
        &artifact,
        relative_artifact_path.to_path_buf(),
    );
    let production_evidence = runner
        .run_for_manifest_entry_with_artifacts(
            &entry,
            &artifact_ref.path,
            &proof_export_artifact_ref.metadata_path,
            &proof_export_artifact_ref.proof_path,
        )
        .map_err(|error| {
            production_blocker_record(
                "production-checker-evidence-failed",
                "checked-certificate-production",
                Some(candidate.dispatch.id.clone()),
                format!(
                    "production checked-certificate checker failed for dispatch {}: {error}",
                    candidate.dispatch.id
                ),
                ["production_checker_evidence"],
            )
        })?;
    let production_checker_evidence_sha256 = production_evidence.sha256().map_err(|error| {
        production_blocker_record(
            "production-checker-evidence-invalid",
            "checked-certificate-production",
            Some(candidate.dispatch.id.clone()),
            format!(
                "production checked-certificate checker evidence is invalid for dispatch {}: {error}",
                candidate.dispatch.id
            ),
            ["production_checker_evidence"],
        )
    })?;
    let external_checker_binary_sha256 = production_evidence.checker_binary_sha256.clone();
    let external_checker_invocation_sha256 = production_evidence.invocation_sha256.clone();
    let external_checker_stdout_sha256 = production_evidence.stdout_sha256.clone();
    let external_checker_stderr_sha256 = production_evidence.stderr_sha256.clone();
    let acceptance_request =
        CheckedBinaryCertificateManifestAcceptanceRequest::from_manifest_entry_and_solver_proof_export_metadata(
            &entry,
            export.normalized_metadata(),
        )
        .and_then(|request| request.with_production_checker_evidence(production_evidence))
        .map_err(|error| {
            production_blocker_record(
                "checked-certificate-acceptance-request-invalid",
                "checked-certificate-production",
                Some(candidate.dispatch.id.clone()),
                format!(
                    "checked certificate production acceptance request is invalid for dispatch {}: {error}",
                    candidate.dispatch.id
                ),
                ["checked_certificate_manifest", "production_checker_evidence"],
            )
        })?;
    let acceptance_record = import_checked_certificate_manifest_entry_for_dispatch(
        dispatch,
        &candidate.binding.canonical_vc_bytes,
        export_dir,
        &entry,
        &acceptance_request,
    )
    .map_err(|error| {
        production_blocker_record(
            "checked-certificate-import-failed",
            "checked-certificate-production",
            Some(candidate.dispatch.id.clone()),
            format!(
                "produced checked certificate could not be imported for dispatch {}: {error}",
                candidate.dispatch.id
            ),
            ["checked_certificate_artifact", "production_checker_evidence"],
        )
    })?;
    let audit_export = CheckedBinaryCertificateAuditExport::from_manifest_entry_and_record(
        entry.clone(),
        acceptance_record.clone(),
    )
    .map_err(|error| {
        production_blocker_record(
            "checked-certificate-audit-export-build-failed",
            "checked-certificate-production",
            Some(candidate.dispatch.id.clone()),
            format!(
                "checked certificate audit export could not include dispatch {}: {error}",
                candidate.dispatch.id
            ),
            ["checked_certificate_audit_export"],
        )
    })?;
    let audit_export_json = audit_export.to_json().map_err(|error| {
        production_blocker_record(
            "checked-certificate-audit-export-build-failed",
            "checked-certificate-production",
            Some(candidate.dispatch.id.clone()),
            format!(
                "checked certificate audit export could not serialize dispatch {}: {error}",
                candidate.dispatch.id
            ),
            ["checked_certificate_audit_export"],
        )
    })?;
    let manifest_identity_sha256 =
        CheckedBinaryCertificateAuditExportBundleEntry::from_audit_export_and_digest(
            &audit_export,
            trust_types::digest::stable_sha256_hex(audit_export_json.as_bytes()),
        )
        .map(|entry| entry.manifest_identity_sha256)
        .map_err(|error| {
            production_blocker_record(
                "checked-certificate-manifest-identity-invalid",
                "checked-certificate-production",
                Some(candidate.dispatch.id.clone()),
                format!(
                    "checked certificate manifest identity is invalid for dispatch {}: {error}",
                    candidate.dispatch.id
                ),
                ["checked_certificate_manifest_identity"],
            )
        })?;

    Ok(CheckedCertificateProductionSuccess {
        dispatch_id: candidate.dispatch.id.clone(),
        artifact_path: artifact_ref.path.display().to_string(),
        proof_export_metadata_path: proof_export_artifact_ref.metadata_path.display().to_string(),
        proof_export_payload_path: proof_export_artifact_ref.proof_path.display().to_string(),
        certificate_sha256: artifact.certificate_sha256,
        manifest_entry: entry,
        source_backpropagation_gate_sha256: stable_json_sha256(
            &acceptance_record.source_backpropagation_gate,
        ),
        replay_transcript_digest: acceptance_record
            .replay_transcript
            .replay_transcript_digest
            .clone(),
        binary_artifact_digest_identity: artifact.binary_artifact_digest_identity,
        replay: artifact.replay,
        acceptance_record,
        manifest_identity_sha256,
        checker: checker_id.to_string(),
        checker_version: checker_version.to_string(),
        format: candidate.proof_export.format.clone(),
        production_checker_evidence_sha256,
        proof_export_artifact_sha256: candidate.proof_export_artifact.content_sha256.clone(),
        proof_export_artifact_path: normalized_proof_export_path.display().to_string(),
        external_checker_binary_sha256,
        external_checker_invocation_sha256,
        external_checker_stdout_sha256,
        external_checker_stderr_sha256,
    })
}

pub(super) fn production_export_row_record(
    success: &CheckedCertificateProductionSuccess,
    audit_export: &CheckedBinaryCertificateAuditExport,
) -> Result<CheckedCertificateExportRowRecord, CheckedCertificateProductionBlockerRecord> {
    let selected_image_identity = audit_export
        .acceptance_record
        .artifact_identity
        .binary_artifact_digest_identity
        .selected_image
        .clone()
        .ok_or_else(|| {
            production_blocker_record(
                "selected-image-identity-missing",
                "checked-certificate-production",
                Some(success.dispatch_id.clone()),
                format!(
                    "checked certificate export row for dispatch {} is missing selected-image identity",
                    success.dispatch_id
                ),
                ["selected_image_digest_identity"],
            )
        })?;
    let audit_export_json = audit_export.to_json().map_err(|error| {
        production_blocker_record(
            "checked-certificate-export-row-invalid",
            "checked-certificate-production",
            Some(success.dispatch_id.clone()),
            format!(
                "checked certificate export row could not serialize dispatch {}: {error}",
                success.dispatch_id
            ),
            ["checked_certificate_audit_export"],
        )
    })?;
    let audit_export_sha256 = trust_types::digest::stable_sha256_hex(audit_export_json.as_bytes());
    let bundle_entry =
        CheckedBinaryCertificateAuditExportBundleEntry::from_audit_export_and_digest(
            audit_export,
            audit_export_sha256.clone(),
        )
        .map_err(|error| {
            production_blocker_record(
                "checked-certificate-export-row-invalid",
                "checked-certificate-production",
                Some(success.dispatch_id.clone()),
                format!(
                    "checked certificate export row is invalid for dispatch {}: {error}",
                    success.dispatch_id
                ),
                ["checked_certificate_audit_export"],
            )
        })?;
    let source_backpropagation_gate_sha256 =
        stable_json_sha256(&bundle_entry.source_backpropagation_gate).ok_or_else(|| {
            production_blocker_record(
                "source-backpropagation-gate-identity-missing",
                "checked-certificate-production",
                Some(success.dispatch_id.clone()),
                format!(
                    "checked certificate export row for dispatch {} has no source-backpropagation gate identity",
                    success.dispatch_id
                ),
                ["checked_certificate_source_backpropagation_gate"],
            )
        })?;
    Ok(CheckedCertificateExportRowRecord {
        dispatch_id: bundle_entry.dispatch_id,
        vc_sha256: bundle_entry.vc_sha256,
        origin_sha256: bundle_entry.origin_sha256,
        assumption_digest: bundle_entry.assumption_digest,
        query_semantics: audit_export
            .acceptance_record
            .solver_proof_export
            .metadata
            .query_semantics,
        replay: bundle_entry.replay,
        replay_transcript_digest: bundle_entry.replay_transcript_digest,
        proof_sha256: bundle_entry.proof_sha256,
        proof_export_sha256: bundle_entry.proof_export_sha256,
        proof_export_artifact_sha256: success.proof_export_artifact_sha256.clone(),
        proof_export_artifact_path: success.proof_export_artifact_path.clone(),
        certificate_sha256: bundle_entry.certificate_sha256,
        certificate_path: success.manifest_entry.certificate_path.clone(),
        checked_certificate_artifact_path: success.artifact_path.clone(),
        manifest_identity_sha256: bundle_entry.manifest_identity_sha256,
        source_backpropagation_gate_sha256,
        source_backpropagation_gate: bundle_entry.source_backpropagation_gate,
        binary_artifact_digest_identity: bundle_entry.binary_artifact_digest_identity,
        selected_image_identity,
        checker: bundle_entry.checker,
        checker_version: bundle_entry.checker_version,
        format: bundle_entry.format,
        production_checker_evidence_sha256: success.production_checker_evidence_sha256.clone(),
        audit_export_path: bundle_entry.audit_export_path,
        audit_export_sha256,
    })
}

pub(super) struct CheckedCertificateProductionInventory<'a> {
    pub(super) required_vcs: usize,
    pub(super) candidate_dispatches: usize,
    pub(super) proof_export_candidates: usize,
    pub(super) exported_artifacts: usize,
    pub(super) proof_export_records: &'a [CheckedCertificateProofExportRecord],
    pub(super) export_row_records: &'a [CheckedCertificateExportRowRecord],
}

pub(super) fn validate_checked_certificate_required_vc_production_inventory(
    inventory: CheckedCertificateProductionInventory<'_>,
    blockers: &mut Vec<String>,
    blocker_records: &mut Vec<CheckedCertificateProductionBlockerRecord>,
) {
    let CheckedCertificateProductionInventory {
        required_vcs,
        candidate_dispatches,
        proof_export_candidates,
        exported_artifacts,
        proof_export_records,
        export_row_records,
    } = inventory;

    if required_vcs == 0 {
        return;
    }

    if candidate_dispatches != required_vcs {
        push_checked_certificate_inventory_blocker(
            blockers,
            blocker_records,
            "checked-certificate-required-vc-inventory-incomplete",
            format!(
                "checked certificate production saw {candidate_dispatches} proved required VC dispatch(es), expected required_vcs={required_vcs}"
            ),
            ["required_binary_vc_inventory", "solver_dispatch", "checked_certificate_artifact"],
        );
    }
    if proof_export_candidates != required_vcs {
        push_checked_certificate_inventory_blocker(
            blockers,
            blocker_records,
            "normalized-proof-export-coverage-incomplete",
            format!(
                "normalized solver proof exports cover {proof_export_candidates} required VC dispatch(es), expected required_vcs={required_vcs}"
            ),
            [
                "normalized_solver_proof_export",
                "content_addressed_proof_export",
                "required_binary_vc_inventory",
            ],
        );
    }
    if exported_artifacts != required_vcs {
        push_checked_certificate_inventory_blocker(
            blockers,
            blocker_records,
            "checked-certificate-export-coverage-incomplete",
            format!(
                "checked certificate exports cover {exported_artifacts} required VC dispatch(es), expected required_vcs={required_vcs}"
            ),
            [
                "checked_certificate_artifact",
                "production_checker_evidence",
                "required_binary_vc_inventory",
            ],
        );
    }
    if export_row_records.len() != exported_artifacts {
        push_checked_certificate_inventory_blocker(
            blockers,
            blocker_records,
            "checked-certificate-export-row-coverage-incomplete",
            format!(
                "checked certificate export rows cover {} exported artifact(s), expected exported_artifacts={exported_artifacts}",
                export_row_records.len()
            ),
            [
                "checked_certificate_audit_export",
                "checked_certificate_manifest",
                "production_checker_evidence",
            ],
        );
    }

    let mut proof_export_paths = BTreeMap::new();
    for record in proof_export_records {
        let Some(path) = record.artifact_path.as_deref().filter(|path| !path.trim().is_empty())
        else {
            continue;
        };
        if let Some(first_dispatch_id) =
            proof_export_paths.insert(path.to_string(), record.dispatch_id.clone())
        {
            push_checked_certificate_inventory_blocker(
                blockers,
                blocker_records,
                "duplicate-normalized-proof-export-path",
                format!(
                    "normalized proof export artifact path `{path}` is shared by dispatches `{first_dispatch_id}` and `{}`",
                    record.dispatch_id
                ),
                [
                    "normalized_solver_proof_export",
                    "content_addressed_proof_export",
                    "per_vc_proof_export_identity",
                ],
            );
        }
    }

    let mut proof_export_artifacts = BTreeMap::new();
    for record in proof_export_records {
        let Some(artifact_sha256) = record.proof_export_artifact_sha256.as_deref() else {
            continue;
        };
        if let Some(first_dispatch_id) =
            proof_export_artifacts.insert(artifact_sha256.to_string(), record.dispatch_id.clone())
        {
            push_checked_certificate_inventory_blocker(
                blockers,
                blocker_records,
                "duplicate-normalized-proof-export-artifact",
                format!(
                    "normalized proof export artifact sha256 `{artifact_sha256}` is shared by dispatches `{first_dispatch_id}` and `{}`",
                    record.dispatch_id
                ),
                [
                    "normalized_solver_proof_export",
                    "content_addressed_proof_export",
                    "per_vc_proof_export_identity",
                ],
            );
        }
    }

    let mut export_row_identities = BTreeMap::new();
    for row in export_row_records {
        let identity = format!("{}:{}:{}", row.vc_sha256, row.origin_sha256, row.assumption_digest);
        if let Some(first_dispatch_id) =
            export_row_identities.insert(identity.clone(), row.dispatch_id.clone())
        {
            push_checked_certificate_inventory_blocker(
                blockers,
                blocker_records,
                "duplicate-checked-certificate-export-row-identity",
                format!(
                    "checked certificate export row identity `{identity}` is shared by dispatches `{first_dispatch_id}` and `{}`",
                    row.dispatch_id
                ),
                [
                    "checked_certificate_audit_export",
                    "checked_certificate_manifest",
                    "per_vc_certificate_identity",
                ],
            );
        }
    }
}

fn push_checked_certificate_inventory_blocker(
    blockers: &mut Vec<String>,
    blocker_records: &mut Vec<CheckedCertificateProductionBlockerRecord>,
    code: impl Into<String>,
    detail: String,
    evidence_required: impl IntoIterator<Item = &'static str>,
) {
    blockers.push(detail.clone());
    blocker_records.push(production_blocker_record(
        code,
        "checked-certificate-production",
        None,
        detail,
        evidence_required,
    ));
}

pub(super) fn push_dispatch_blocker(
    blocker_records: &mut Vec<CheckedCertificateProductionBlockerRecord>,
    dispatch_blocker_codes: &mut Vec<String>,
    dispatch: &SolverDispatchRecord,
    code: impl Into<String>,
    stage: &'static str,
    detail: impl Into<String>,
    evidence_required: impl IntoIterator<Item = &'static str>,
) {
    let code = code.into();
    dispatch_blocker_codes.push(code.clone());
    blocker_records.push(production_blocker_record(
        code,
        stage,
        Some(dispatch.id.clone()),
        detail,
        evidence_required,
    ));
}

pub(super) fn production_blocker_record(
    code: impl Into<String>,
    stage: &'static str,
    dispatch_id: Option<String>,
    detail: impl Into<String>,
    evidence_required: impl IntoIterator<Item = &'static str>,
) -> CheckedCertificateProductionBlockerRecord {
    CheckedCertificateProductionBlockerRecord {
        code: code.into(),
        stage: stage.to_string(),
        dispatch_id,
        detail: detail.into(),
        evidence_required: evidence_required.into_iter().map(str::to_string).collect(),
    }
}

fn proof_certificate_status_label(status: &ProofCertificateStatus) -> String {
    match status {
        ProofCertificateStatus::NotRequested => "not_requested",
        ProofCertificateStatus::Unavailable { .. } => "unavailable",
        ProofCertificateStatus::Present { .. } => "present",
        ProofCertificateStatus::Checked { .. } => "checked",
        ProofCertificateStatus::Rejected { .. } => "rejected",
        _ => "unknown",
    }
    .to_string()
}

fn check_error_kind(error: &CheckError) -> &'static str {
    match error {
        CheckError::UnsupportedFormat { .. } => "unsupported_format",
        CheckError::MalformedProof { .. } => "malformed_proof",
        CheckError::VcDigestMismatch { .. } => "vc_digest_mismatch",
        CheckError::QuerySemanticsNotProofGrade { .. } => "query_semantics_not_proof_grade",
        CheckError::SolverVerdictMismatch { .. } => "solver_verdict_mismatch",
        CheckError::AssumptionDigestMismatch { .. } => "assumption_digest_mismatch",
        CheckError::ReplayDigestMismatch { .. } => "replay_digest_mismatch",
        CheckError::CheckerInternalError { .. } => "checker_internal_error",
        CheckError::RawSolverBytesAuditOnly { .. } => "raw_solver_bytes_audit_only",
        CheckError::RawSolverBytesCannotUpgradeToChecked { .. } => {
            "raw_solver_bytes_cannot_upgrade_to_checked"
        }
        CheckError::BinaryOriginMissing => "binary_origin_missing",
        CheckError::ArtifactBindingMismatch { .. } => "artifact_binding_mismatch",
        _ => "unknown_check_error",
    }
}
