// Loaded checked-certificate metadata aggregation.

use trust_proof_cert::{
    CheckedBinaryCertificateArtifact, CheckedBinaryCertificateSourceBackpropagationGate,
};

use super::{
    CheckedCertificateReplayDigestIdentityRecord, LoadedCheckedCertificateArtifact,
    checked_certificate_replay_digest_identity_record, stable_json_sha256,
};

#[derive(Debug, Clone)]
pub(super) struct CheckedCertificateLoadedMetadata {
    pub(super) source_backpropagation_gate: CheckedBinaryCertificateSourceBackpropagationGate,
    pub(super) manifest_identity_sha256: Option<String>,
    pub(super) source_backpropagation_gate_sha256: Option<String>,
    pub(super) replay_transcript_digest: Option<String>,
    pub(super) replay_digest_identity: CheckedCertificateReplayDigestIdentityRecord,
    pub(super) production_checker_evidence_sha256: Option<String>,
}

impl CheckedCertificateLoadedMetadata {
    pub(super) fn from_artifact_and_gate(
        artifact: &CheckedBinaryCertificateArtifact,
        source_backpropagation_gate: Option<CheckedBinaryCertificateSourceBackpropagationGate>,
        manifest_identity_sha256: Option<String>,
        source_backpropagation_gate_sha256: Option<String>,
        replay_transcript_digest: Option<String>,
        production_checker_evidence_sha256: Option<String>,
    ) -> Self {
        let replay_transcript_digest =
            replay_transcript_digest.or_else(|| artifact.replay_transcript_digest.clone());
        let source_backpropagation_gate_was_present =
            source_backpropagation_gate.is_some() || source_backpropagation_gate_sha256.is_some();
        let source_backpropagation_gate = source_backpropagation_gate.unwrap_or_default();
        let source_backpropagation_gate_sha256 = source_backpropagation_gate_sha256.or_else(|| {
            source_backpropagation_gate_was_present
                .then(|| stable_json_sha256(&source_backpropagation_gate))
                .flatten()
        });
        let replay_digest_identity = checked_certificate_replay_digest_identity_record(
            artifact.replay,
            replay_transcript_digest.clone(),
            Some(artifact.binary_artifact_digest_identity.clone()),
        );
        Self {
            source_backpropagation_gate,
            manifest_identity_sha256,
            source_backpropagation_gate_sha256,
            replay_transcript_digest,
            replay_digest_identity,
            production_checker_evidence_sha256,
        }
    }
}

pub(super) fn loaded_checked_certificate_metadata(
    row: &LoadedCheckedCertificateArtifact,
) -> CheckedCertificateLoadedMetadata {
    CheckedCertificateLoadedMetadata::from_artifact_and_gate(
        &row.artifact,
        Some(row.source_backpropagation_gate.clone()),
        row.manifest_identity_sha256.clone(),
        row.source_backpropagation_gate_sha256.clone(),
        row.replay_transcript_digest.clone(),
        row.production_checker_evidence_sha256.clone(),
    )
}
