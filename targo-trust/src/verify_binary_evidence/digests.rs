// Digest, identity, and canonical-SHA-256 helpers used across the binary
// verification evidence pipeline.

use serde::Serialize;
use trust_types::{BinaryArtifactDigestIdentity, ReplayStatus, SerializableVc};

use super::CheckedCertificateReplayDigestIdentityRecord;

pub(crate) fn binary_artifact_digest_identity_is_empty(
    identity: &BinaryArtifactDigestIdentity,
) -> bool {
    !identity.has_any_identity()
}

/// The ONE spelling of the canonical verification-condition bytes that a checked
/// binary certificate is bound to (`vc_sha256`, and every digest derived from it).
///
/// This deliberately routes through [`trust_types::stable_model_json_bytes`]
/// rather than calling `serde_json::to_vec` here. A hash domain that spells its
/// own `serde_json` re-serializes every future additive
/// `#[serde(default)] Option<_>` field as `,"<key>":null` and moves already-audited
/// certificate digests for a change that carries no information — which is exactly
/// what `VerificationCondition::obligation` did to the three checked-certificate
/// goldens in this crate. The canonical form omits those defaults and keeps every
/// `Some` hash-visible, so the pins that shipped before a field existed stay
/// bit-for-bit valid while a populated field is still part of VC identity.
///
/// This is not only about the goldens. A checked-certificate artifact persists
/// `vc_sha256`, and import re-derives the binding from the LIVE dispatch VC and
/// requires equality (see `VerifyBinaryEvidence::import_checked_certificate_artifacts`).
/// A digest that moves when a default-valued field is added therefore silently
/// unbinds every certificate already on disk. Canonicalizing here keeps the
/// pre-field artifacts matching, which is the behaviour their audit assumed.
///
/// Every producer of canonical VC bytes in targo-trust must call this; two
/// spellings would make a certificate fail to bind to the dispatch that produced it.
pub(crate) fn canonical_vc_bytes(vc: &SerializableVc) -> Option<Vec<u8>> {
    trust_types::stable_model_json_bytes(vc).ok()
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
