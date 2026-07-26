// Normalized solver proof export artifact: build, validate, persist, and load.

use std::path::Path;
use std::path::PathBuf;

#[cfg(test)]
use trust_proof_cert::SolverProofExport;
use trust_proof_cert::{
    CheckedBinaryCertificateSourceBackpropagationGate, digest_model_assumptions,
};
use trust_types::SolverDispatchRecord;

use crate::durable_io::atomic_write_private;
use crate::input_limits::{MAX_SAVED_PROOF_REPORT_BYTES, read_bounded_file};

#[cfg(test)]
use super::dispatch_binary_artifact_digest_identity_acceptance_blockers;
use super::{
    LoadedNormalizedSolverProofExportArtifact, NORMALIZED_SOLVER_PROOF_EXPORT_ARTIFACT_SCHEMA,
    NORMALIZED_SOLVER_PROOF_EXPORT_ARTIFACT_SUFFIX, NormalizedSolverProofExportArtifact,
    NormalizedSolverProofExportArtifactError, dispatch_canonical_binding, is_canonical_sha256_hex,
    stable_json_sha256,
};

pub(crate) fn normalized_solver_proof_export_artifact_path(
    root: &Path,
    content_sha256: &str,
) -> PathBuf {
    root.join("normalized-solver-proof-exports")
        .join(&content_sha256[..2])
        .join(format!("{content_sha256}.{NORMALIZED_SOLVER_PROOF_EXPORT_ARTIFACT_SUFFIX}"))
}

#[cfg(test)]
pub(crate) struct NormalizedSolverProofExportArtifactInput<'a> {
    pub(crate) dispatch: &'a SolverDispatchRecord,
    pub(crate) canonical_vc_bytes: &'a [u8],
    pub(crate) format: &'a str,
    pub(crate) proof_bytes: Vec<u8>,
    pub(crate) solver_version: Option<String>,
    pub(crate) exported_at_unix_ms: u64,
    pub(crate) replay_transcript_digest: Option<&'a str>,
    pub(crate) source_backpropagation_gate: &'a CheckedBinaryCertificateSourceBackpropagationGate,
}

#[cfg(test)]
pub(crate) fn build_normalized_solver_proof_export_artifact(
    input: NormalizedSolverProofExportArtifactInput<'_>,
) -> Result<NormalizedSolverProofExportArtifact, NormalizedSolverProofExportArtifactError> {
    let NormalizedSolverProofExportArtifactInput {
        dispatch,
        canonical_vc_bytes,
        format,
        proof_bytes,
        solver_version,
        exported_at_unix_ms,
        replay_transcript_digest,
        source_backpropagation_gate,
    } = input;
    let export = SolverProofExport::new(
        dispatch,
        canonical_vc_bytes,
        format,
        proof_bytes,
        solver_version,
        exported_at_unix_ms,
    );
    normalized_solver_proof_export_artifact_from_export(
        dispatch,
        canonical_vc_bytes,
        export,
        replay_transcript_digest,
        source_backpropagation_gate,
    )
}

#[cfg(test)]
pub(crate) fn normalized_solver_proof_export_artifact_from_export(
    dispatch: &SolverDispatchRecord,
    canonical_vc_bytes: &[u8],
    proof_export: SolverProofExport,
    replay_transcript_digest: Option<&str>,
    source_backpropagation_gate: &CheckedBinaryCertificateSourceBackpropagationGate,
) -> Result<NormalizedSolverProofExportArtifact, NormalizedSolverProofExportArtifactError> {
    proof_export
        .validate_for_dispatch(dispatch, canonical_vc_bytes)
        .map_err(|error| normalized_proof_export_error(
            "normalized-proof-export-binding-mismatch",
            format!(
                "normalized proof export for dispatch {} is not bound to the current solver dispatch: {error}",
                dispatch.id
            ),
        ))?;
    let binding = dispatch_canonical_binding(dispatch).ok_or_else(|| {
        normalized_proof_export_error(
            "normalized-proof-export-binding-mismatch",
            format!(
                "normalized proof export for dispatch {} cannot bind missing canonical VC or binary origin",
                dispatch.id
            ),
        )
    })?;
    let digest_identity_blockers =
        dispatch_binary_artifact_digest_identity_acceptance_blockers(dispatch);
    if !digest_identity_blockers.is_empty() {
        return Err(normalized_proof_export_error(
            "normalized-proof-export-selected-image-missing",
            format!(
                "normalized proof export for dispatch {} is missing accepted binary artifact/selected-image identity: {}",
                dispatch.id,
                digest_identity_blockers.join("; ")
            ),
        ));
    }
    let binary_artifact_digest_identity =
        dispatch.binary_artifact_digest_identity.clone().ok_or_else(|| {
            normalized_proof_export_error(
                "normalized-proof-export-selected-image-missing",
                format!(
                    "normalized proof export for dispatch {} is missing binary artifact digest identity",
                    dispatch.id
                ),
            )
        })?;
    let selected_image_identity =
        binary_artifact_digest_identity.selected_image.clone().ok_or_else(|| {
            normalized_proof_export_error(
                "normalized-proof-export-selected-image-missing",
                format!(
                    "normalized proof export for dispatch {} is missing selected-image identity",
                    dispatch.id
                ),
            )
        })?;
    let source_backpropagation_gate_sha256 =
        stable_json_sha256(source_backpropagation_gate).ok_or_else(|| {
            normalized_proof_export_error(
                "normalized-proof-export-source-gate-invalid",
                format!(
                    "normalized proof export for dispatch {} could not digest source-backpropagation gate state",
                    dispatch.id
                ),
            )
        })?;
    let proof_export_metadata_sha256 =
        proof_export.normalized_metadata_sha256().map_err(|error| {
            normalized_proof_export_error(
                "normalized-proof-export-metadata-invalid",
                format!(
                    "normalized proof export metadata for dispatch {} is invalid: {error}",
                    dispatch.id
                ),
            )
        })?;
    let assumption_digest = digest_model_assumptions(&dispatch.assumptions);
    if proof_export.assumption_digest != assumption_digest {
        return Err(normalized_proof_export_error(
            "normalized-proof-export-assumption-mismatch",
            format!(
                "normalized proof export for dispatch {} is bound to assumption digest {} but dispatch assumptions digest to {}",
                dispatch.id, proof_export.assumption_digest, assumption_digest
            ),
        ));
    }
    if let Some(digest) = replay_transcript_digest {
        if !is_canonical_sha256_hex(digest) {
            return Err(normalized_proof_export_error(
                "normalized-proof-export-replay-digest-noncanonical",
                format!(
                    "normalized proof export for dispatch {} has noncanonical replay transcript digest: {digest}",
                    dispatch.id
                ),
            ));
        }
    }

    let artifact = NormalizedSolverProofExportArtifact {
        schema_version: NORMALIZED_SOLVER_PROOF_EXPORT_ARTIFACT_SCHEMA.to_string(),
        dispatch_id: dispatch.id.clone(),
        vc_sha256: binding.vc_sha256,
        origin_sha256: binding.origin_sha256,
        assumption_digest,
        query_semantics: dispatch.query_semantics,
        replay: dispatch.replay,
        replay_transcript_digest: replay_transcript_digest.map(str::to_string),
        binary_artifact_digest_identity,
        selected_image_identity,
        source_backpropagation_gate_sha256,
        source_backpropagation_gate: source_backpropagation_gate.clone(),
        format: proof_export.format.clone(),
        proof_sha256: proof_export.proof_sha256.clone(),
        proof_byte_len: proof_export.proof_bytes.len(),
        proof_export_metadata_sha256,
        proof_export,
    };
    validate_normalized_solver_proof_export_artifact(
        &artifact,
        dispatch,
        canonical_vc_bytes,
        artifact.format.as_str(),
        artifact.proof_sha256.as_str(),
        replay_transcript_digest,
        source_backpropagation_gate,
    )?;
    Ok(artifact)
}

pub(crate) fn persist_normalized_solver_proof_export_artifact(
    root: &Path,
    artifact: &NormalizedSolverProofExportArtifact,
) -> Result<PathBuf, NormalizedSolverProofExportArtifactError> {
    validate_normalized_solver_proof_export_artifact_structure(artifact)?;
    let bytes = normalized_solver_proof_export_artifact_canonical_bytes(artifact)?;
    let content_sha256 = trust_types::digest::stable_sha256_hex(&bytes);
    let path = normalized_solver_proof_export_artifact_path(root, &content_sha256);
    atomic_write_private(&path, &bytes).map_err(|error| {
        normalized_proof_export_error(
            "normalized-proof-export-write-failed",
            format!(
                "normalized proof export artifact `{}` could not be written: {error}",
                path.display()
            ),
        )
    })?;
    Ok(path)
}

pub(crate) fn load_normalized_solver_proof_export_artifact(
    path: &Path,
    dispatch: &SolverDispatchRecord,
    canonical_vc_bytes: &[u8],
    expected_format: &str,
    expected_proof_sha256: &str,
    replay_transcript_digest: Option<&str>,
    source_backpropagation_gate: &CheckedBinaryCertificateSourceBackpropagationGate,
) -> Result<LoadedNormalizedSolverProofExportArtifact, NormalizedSolverProofExportArtifactError> {
    let bytes = read_bounded_file(path, MAX_SAVED_PROOF_REPORT_BYTES).map_err(|error| {
        normalized_proof_export_error(
            "normalized-proof-export-unreadable",
            format!(
                "normalized proof export artifact `{}` for dispatch {} is not readable: {error}",
                path.display(),
                dispatch.id
            ),
        )
    })?;
    let artifact: NormalizedSolverProofExportArtifact =
        serde_json::from_slice(&bytes).map_err(|error| {
            normalized_proof_export_error(
                "normalized-proof-export-not-normalized",
                format!(
                    "normalized proof export artifact `{}` for dispatch {} is not targo-trust normalized JSON; raw solver proof bytes are not accepted: {error}",
                    path.display(),
                    dispatch.id
                ),
            )
        })?;
    let canonical_bytes = normalized_solver_proof_export_artifact_canonical_bytes(&artifact)?;
    if bytes != canonical_bytes {
        return Err(normalized_proof_export_error(
            "normalized-proof-export-not-canonical",
            format!(
                "normalized proof export artifact `{}` for dispatch {} is not canonical JSON; raw or reformatted proof bytes cannot be promoted",
                path.display(),
                dispatch.id
            ),
        ));
    }
    let content_sha256 = trust_types::digest::stable_sha256_hex(&canonical_bytes);
    validate_normalized_solver_proof_export_content_address(path, &content_sha256)?;
    validate_normalized_solver_proof_export_artifact(
        &artifact,
        dispatch,
        canonical_vc_bytes,
        expected_format,
        expected_proof_sha256,
        replay_transcript_digest,
        source_backpropagation_gate,
    )?;
    Ok(LoadedNormalizedSolverProofExportArtifact { artifact, content_sha256 })
}

fn validate_normalized_solver_proof_export_artifact(
    artifact: &NormalizedSolverProofExportArtifact,
    dispatch: &SolverDispatchRecord,
    canonical_vc_bytes: &[u8],
    expected_format: &str,
    expected_proof_sha256: &str,
    replay_transcript_digest: Option<&str>,
    source_backpropagation_gate: &CheckedBinaryCertificateSourceBackpropagationGate,
) -> Result<(), NormalizedSolverProofExportArtifactError> {
    validate_normalized_solver_proof_export_artifact_structure(artifact)?;
    artifact
        .proof_export
        .validate_for_dispatch(dispatch, canonical_vc_bytes)
        .map_err(|error| normalized_proof_export_error(
            "normalized-proof-export-binding-mismatch",
            format!(
                "normalized proof export artifact for dispatch {} is not bound to the current solver dispatch: {error}",
                dispatch.id
            ),
        ))?;
    let binding = dispatch_canonical_binding(dispatch).ok_or_else(|| {
        normalized_proof_export_error(
            "normalized-proof-export-binding-mismatch",
            format!(
                "normalized proof export artifact for dispatch {} cannot bind missing canonical VC or binary origin",
                dispatch.id
            ),
        )
    })?;
    let expected_assumption_digest = digest_model_assumptions(&dispatch.assumptions);
    let expected_source_gate_sha256 =
        stable_json_sha256(source_backpropagation_gate).ok_or_else(|| {
            normalized_proof_export_error(
                "normalized-proof-export-source-gate-invalid",
                format!(
                    "normalized proof export artifact for dispatch {} could not digest source-backpropagation gate state",
                    dispatch.id
                ),
            )
        })?;
    let expected_metadata_sha256 =
        artifact.proof_export.normalized_metadata_sha256().map_err(|error| {
            normalized_proof_export_error(
                "normalized-proof-export-metadata-invalid",
                format!(
                    "normalized proof export metadata for dispatch {} is invalid: {error}",
                    dispatch.id
                ),
            )
        })?;
    let expected_identity = dispatch.binary_artifact_digest_identity.clone().ok_or_else(|| {
        normalized_proof_export_error(
            "normalized-proof-export-selected-image-missing",
            format!(
                "normalized proof export artifact for dispatch {} is missing binary artifact digest identity",
                dispatch.id
            ),
        )
    })?;
    let expected_selected_image = expected_identity.selected_image.clone().ok_or_else(|| {
        normalized_proof_export_error(
            "normalized-proof-export-selected-image-missing",
            format!(
                "normalized proof export artifact for dispatch {} is missing selected-image identity",
                dispatch.id
            ),
        )
    })?;

    for (field, expected, actual) in [
        (
            "schema_version",
            NORMALIZED_SOLVER_PROOF_EXPORT_ARTIFACT_SCHEMA,
            artifact.schema_version.as_str(),
        ),
        ("dispatch_id", dispatch.id.as_str(), artifact.dispatch_id.as_str()),
        ("vc_sha256", binding.vc_sha256.as_str(), artifact.vc_sha256.as_str()),
        ("origin_sha256", binding.origin_sha256.as_str(), artifact.origin_sha256.as_str()),
        (
            "assumption_digest",
            expected_assumption_digest.as_str(),
            artifact.assumption_digest.as_str(),
        ),
        ("format", expected_format, artifact.format.as_str()),
        ("proof_sha256", expected_proof_sha256, artifact.proof_sha256.as_str()),
        (
            "proof_export_metadata_sha256",
            expected_metadata_sha256.as_str(),
            artifact.proof_export_metadata_sha256.as_str(),
        ),
        (
            "source_backpropagation_gate_sha256",
            expected_source_gate_sha256.as_str(),
            artifact.source_backpropagation_gate_sha256.as_str(),
        ),
    ] {
        if expected != actual {
            return Err(normalized_proof_export_error(
                "normalized-proof-export-binding-mismatch",
                format!(
                    "normalized proof export artifact for dispatch {} has {field}={actual}, expected {expected}",
                    dispatch.id
                ),
            ));
        }
    }
    if artifact.query_semantics != dispatch.query_semantics {
        return Err(normalized_proof_export_error(
            "normalized-proof-export-binding-mismatch",
            format!(
                "normalized proof export artifact for dispatch {} has query_semantics={:?}, expected {:?}",
                dispatch.id, artifact.query_semantics, dispatch.query_semantics
            ),
        ));
    }
    if artifact.replay != dispatch.replay {
        return Err(normalized_proof_export_error(
            "normalized-proof-export-binding-mismatch",
            format!(
                "normalized proof export artifact for dispatch {} has replay={:?}, expected {:?}",
                dispatch.id, artifact.replay, dispatch.replay
            ),
        ));
    }
    let expected_replay_transcript_digest = replay_transcript_digest.map(str::to_string);
    if artifact.replay_transcript_digest != expected_replay_transcript_digest {
        return Err(normalized_proof_export_error(
            "normalized-proof-export-replay-digest-mismatch",
            format!(
                "normalized proof export artifact for dispatch {} has replay_transcript_digest={:?}, expected {:?}",
                dispatch.id, artifact.replay_transcript_digest, expected_replay_transcript_digest
            ),
        ));
    }
    if artifact.binary_artifact_digest_identity != expected_identity {
        return Err(normalized_proof_export_error(
            "normalized-proof-export-selected-image-mismatch",
            format!(
                "normalized proof export artifact for dispatch {} has binary artifact digest identity that does not match the selected dispatch image",
                dispatch.id
            ),
        ));
    }
    if artifact.selected_image_identity != expected_selected_image {
        return Err(normalized_proof_export_error(
            "normalized-proof-export-selected-image-mismatch",
            format!(
                "normalized proof export artifact for dispatch {} has selected-image identity that does not match the selected dispatch image",
                dispatch.id
            ),
        ));
    }
    if artifact.source_backpropagation_gate != *source_backpropagation_gate {
        return Err(normalized_proof_export_error(
            "normalized-proof-export-source-gate-mismatch",
            format!(
                "normalized proof export artifact for dispatch {} is not bound to the selected source-backpropagation gate state",
                dispatch.id
            ),
        ));
    }
    if artifact.proof_byte_len != artifact.proof_export.proof_bytes.len() {
        return Err(normalized_proof_export_error(
            "normalized-proof-export-binding-mismatch",
            format!(
                "normalized proof export artifact for dispatch {} has proof_byte_len={} but proof export contains {} byte(s)",
                dispatch.id,
                artifact.proof_byte_len,
                artifact.proof_export.proof_bytes.len()
            ),
        ));
    }

    Ok(())
}

fn validate_normalized_solver_proof_export_artifact_structure(
    artifact: &NormalizedSolverProofExportArtifact,
) -> Result<(), NormalizedSolverProofExportArtifactError> {
    for (field, value) in [
        ("vc_sha256", artifact.vc_sha256.as_str()),
        ("origin_sha256", artifact.origin_sha256.as_str()),
        ("assumption_digest", artifact.assumption_digest.as_str()),
        ("proof_sha256", artifact.proof_sha256.as_str()),
        ("proof_export_metadata_sha256", artifact.proof_export_metadata_sha256.as_str()),
        (
            "source_backpropagation_gate_sha256",
            artifact.source_backpropagation_gate_sha256.as_str(),
        ),
    ] {
        if !is_canonical_sha256_hex(value) {
            return Err(normalized_proof_export_error(
                "normalized-proof-export-digest-noncanonical",
                format!(
                    "normalized proof export artifact field {field} is not canonical lowercase SHA-256 hex: {value}"
                ),
            ));
        }
    }
    if artifact.dispatch_id.trim().is_empty() {
        return Err(normalized_proof_export_error(
            "normalized-proof-export-binding-mismatch",
            "normalized proof export artifact is missing dispatch id",
        ));
    }
    if artifact.format.trim().is_empty() || artifact.format == "solver-native" {
        return Err(normalized_proof_export_error(
            "normalized-proof-export-format-missing",
            format!(
                "normalized proof export artifact has invalid proof format `{}`",
                artifact.format
            ),
        ));
    }
    if artifact.proof_byte_len == 0 {
        return Err(normalized_proof_export_error(
            "normalized-proof-export-empty",
            "normalized proof export artifact has empty proof payload",
        ));
    }
    if let Some(replay_transcript_digest) = artifact.replay_transcript_digest.as_deref() {
        if !is_canonical_sha256_hex(replay_transcript_digest) {
            return Err(normalized_proof_export_error(
                "normalized-proof-export-replay-digest-noncanonical",
                format!(
                    "normalized proof export artifact replay_transcript_digest is not canonical lowercase SHA-256 hex: {replay_transcript_digest}"
                ),
            ));
        }
    }
    if !artifact.binary_artifact_digest_identity.digest_identity_blockers().is_empty() {
        return Err(normalized_proof_export_error(
            "normalized-proof-export-selected-image-missing",
            format!(
                "normalized proof export artifact binary artifact digest identity is not accepted: {}",
                artifact.binary_artifact_digest_identity.digest_identity_blockers().join("; ")
            ),
        ));
    }
    if artifact.selected_image_identity.file_size == 0
        || !artifact.selected_image_identity.is_canonical_sha256()
        || artifact.selected_image_identity.end_offset().is_none()
    {
        return Err(normalized_proof_export_error(
            "normalized-proof-export-selected-image-missing",
            "normalized proof export artifact selected-image identity is not replay-grade",
        ));
    }
    artifact.source_backpropagation_gate.validate_structure().map_err(|error| {
        normalized_proof_export_error(
            "normalized-proof-export-source-gate-invalid",
            format!(
                "normalized proof export artifact source-backpropagation gate is invalid: {error}"
            ),
        )
    })?;
    Ok(())
}

fn normalized_solver_proof_export_artifact_canonical_bytes(
    artifact: &NormalizedSolverProofExportArtifact,
) -> Result<Vec<u8>, NormalizedSolverProofExportArtifactError> {
    serde_json::to_vec(artifact).map_err(|error| {
        normalized_proof_export_error(
            "normalized-proof-export-serialization-failed",
            format!("normalized proof export artifact could not serialize canonically: {error}"),
        )
    })
}

fn validate_normalized_solver_proof_export_content_address(
    path: &Path,
    content_sha256: &str,
) -> Result<(), NormalizedSolverProofExportArtifactError> {
    let expected_file_name =
        format!("{content_sha256}.{NORMALIZED_SOLVER_PROOF_EXPORT_ARTIFACT_SUFFIX}");
    let actual_file_name = path.file_name().and_then(|name| name.to_str()).unwrap_or_default();
    if actual_file_name != expected_file_name {
        return Err(normalized_proof_export_error(
            "normalized-proof-export-content-address-missing",
            format!(
                "normalized proof export artifact `{}` is not content-addressed: expected file name `{expected_file_name}` for sha256={content_sha256}",
                path.display()
            ),
        ));
    }
    Ok(())
}

pub(super) fn normalized_proof_export_error(
    code: impl Into<String>,
    detail: impl Into<String>,
) -> NormalizedSolverProofExportArtifactError {
    NormalizedSolverProofExportArtifactError { code: code.into(), detail: detail.into() }
}
