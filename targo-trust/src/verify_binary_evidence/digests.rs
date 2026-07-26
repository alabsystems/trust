// Digest, identity, and canonical-SHA-256 helpers used across the binary
// verification evidence pipeline.

use serde::Serialize;
use trust_types::{BinaryArtifactDigestIdentity, ReplayStatus};

use super::CheckedCertificateReplayDigestIdentityRecord;

pub(crate) fn binary_artifact_digest_identity_is_empty(
    identity: &BinaryArtifactDigestIdentity,
) -> bool {
    !identity.has_any_identity()
}

pub(super) fn stable_json_sha256<T: Serialize>(value: &T) -> Option<String> {
    serde_json::to_vec(value).ok().map(|bytes| trust_types::digest::stable_sha256_hex(&bytes))
}

pub(super) fn production_checker_evidence_status_label(
    production_checker_evidence_sha256: Option<&str>,
) -> &'static str {
    if production_checker_evidence_sha256.is_some_and(|sha| !sha.trim().is_empty()) {
        "present"
    } else {
        "missing"
    }
}

pub(crate) fn checked_certificate_replay_digest_identity_record(
    replay: ReplayStatus,
    replay_transcript_digest: Option<String>,
    binary_artifact_digest_identity: Option<BinaryArtifactDigestIdentity>,
) -> CheckedCertificateReplayDigestIdentityRecord {
    let mut blockers = Vec::new();
    if replay != ReplayStatus::Replayed {
        blockers.push("checked certificate replay was not completed".to_string());
    }
    match replay_transcript_digest.as_deref() {
        Some(digest) if is_canonical_sha256_hex(digest) => {}
        Some(_) => blockers.push(
            "checked certificate replay transcript digest is not canonical SHA-256 hex".to_string(),
        ),
        None => {
            blockers.push("checked certificate replay transcript digest is missing".to_string())
        }
    }
    match &binary_artifact_digest_identity {
        Some(identity) => blockers.extend(identity.digest_identity_blockers()),
        None => blockers
            .push("checked certificate binary artifact digest identity is missing".to_string()),
    }
    let status = if blockers.is_empty() { "accepted" } else { "rejected" };
    CheckedCertificateReplayDigestIdentityRecord {
        status: status.to_string(),
        replay: replay_status_label(replay).to_string(),
        replay_transcript_digest,
        binary_artifact_digest_identity,
        blockers,
    }
}

pub(super) fn is_canonical_sha256_hex(value: &str) -> bool {
    value.len() == 64
        && value.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

pub(super) fn replay_status_label(status: ReplayStatus) -> &'static str {
    match status {
        ReplayStatus::NotAttempted => "not_attempted",
        ReplayStatus::Replayed => "replayed",
        ReplayStatus::Spurious => "spurious",
        ReplayStatus::Failed => "failed",
        _ => "unknown",
    }
}
