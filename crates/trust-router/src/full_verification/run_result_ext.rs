//! Router-side typed extraction helpers for `VerificationRunResult`.
//!
//! The public verifier-api envelope already carries obligations, evidence,
//! skipped reasons, artifacts, and manifest dispositions. This extension trait
//! joins those fields by obligation so compiler transport can consume blockers
//! without scraping human diagnostics.

use serde::{Deserialize, Serialize};
use trust_verifier_api::{
    EvidenceArtifact, EvidenceArtifactKind, EvidenceDisposition, EvidenceStatus, ObligationKind,
    ProofStrength, SkipReason, TrustObligation, VerificationRunResult,
};

use super::native_trust_ir::NativeTrustIrObligationIdentity;
use super::routing::{ObligationRoute, obligation_route};

pub trait FullVerificationRunResultExt {
    /// Return one structured full-verification evidence view per requested
    /// obligation, preserving request order.
    #[must_use]
    fn full_verification_obligation_evidence(&self) -> Vec<FullVerificationObligationEvidence>;

    /// Return only release-blocking per-obligation evidence issues.
    #[must_use]
    fn full_verification_blockers(&self) -> Vec<FullVerificationEvidenceBlocker> {
        self.full_verification_obligation_evidence()
            .into_iter()
            .flat_map(|obligation| obligation.blockers)
            .collect()
    }
}

impl FullVerificationRunResultExt for VerificationRunResult {
    fn full_verification_obligation_evidence(&self) -> Vec<FullVerificationObligationEvidence> {
        let manifest = self.to_manifest();
        self.requested_obligations
            .iter()
            .map(|obligation| {
                let route = obligation_route(obligation);
                let primary_suite = route.map(|route| route.primary.name().to_string());
                let skipped = self
                    .skipped
                    .iter()
                    .find(|skipped| skipped.obligation_id == obligation.obligation_id)
                    .cloned();
                let decisions = manifest
                    .accepted_evidence
                    .iter()
                    .chain(manifest.rejected_evidence.iter())
                    .filter(|decision| decision.obligation_id == obligation.obligation_id)
                    .map(|decision| FullVerificationEvidenceDecision {
                        evidence_id: decision.evidence_id.clone(),
                        status: decision.status,
                        proof_strength: decision.proof_strength.clone(),
                        disposition: decision.disposition,
                        reason: decision.reason.clone(),
                        artifacts: decision.artifacts.clone(),
                        diagnostics: decision.diagnostics.clone(),
                    })
                    .collect::<Vec<_>>();
                let native_trust_ir = route
                    .and_then(|route| native_trust_ir_evidence_view(obligation, route, &decisions));
                let blockers = full_verification_blockers_for_obligation(
                    obligation,
                    route,
                    skipped.as_ref(),
                    &decisions,
                    native_trust_ir.as_ref(),
                );

                FullVerificationObligationEvidence {
                    obligation_id: obligation.obligation_id.clone(),
                    kind: obligation.kind.clone(),
                    primary_suite,
                    decisions,
                    skipped: skipped.map(|skipped| skipped.reason),
                    native_trust_ir,
                    blockers,
                }
            })
            .collect()
    }
}

/// Joined evidence view for one requested full-verification obligation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FullVerificationObligationEvidence {
    pub obligation_id: String,
    pub kind: ObligationKind,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub primary_suite: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub decisions: Vec<FullVerificationEvidenceDecision>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub skipped: Option<SkipReason>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub native_trust_ir: Option<FullVerificationNativeTrustIrEvidence>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub blockers: Vec<FullVerificationEvidenceBlocker>,
}

impl FullVerificationObligationEvidence {
    /// True only when the composite full verifier accepted proof-grade evidence
    /// for this obligation.
    #[must_use]
    pub fn has_accepted_proof(&self) -> bool {
        self.decisions
            .iter()
            .any(|decision| decision.disposition == EvidenceDisposition::AcceptedProof)
    }
}

/// Manifest evidence decision with the corresponding evidence diagnostics.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FullVerificationEvidenceDecision {
    pub evidence_id: String,
    pub status: EvidenceStatus,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_strength: Option<ProofStrength>,
    pub disposition: EvidenceDisposition,
    pub reason: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub artifacts: Vec<EvidenceArtifact>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<String>,
}

/// Native TrustIr artifact identity observed on a full-verification obligation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FullVerificationNativeTrustIrEvidence {
    pub expected_suite: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub declared_suite: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub request_id: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_obligation_id: Option<u32>,
    pub bundle_artifact_present: bool,
    pub request_artifact_present: bool,
    pub proof_obligation_artifact_present: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub identity_error: Option<String>,
}

impl FullVerificationNativeTrustIrEvidence {
    /// True when the result carries the bundle, request, and proof-obligation
    /// artifacts needed to bind proof evidence to a typed native TrustIr request.
    #[must_use]
    pub fn has_matching_artifacts(&self) -> bool {
        self.bundle_artifact_present
            && self.request_artifact_present
            && self.proof_obligation_artifact_present
            && self.identity_error.is_none()
    }
}

/// Typed blocker that prevents a requested obligation from being accepted.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum FullVerificationEvidenceBlocker {
    MissingEvidence {
        obligation_id: String,
    },
    Skipped {
        obligation_id: String,
        reason: SkipReason,
    },
    UnsupportedEvidence {
        obligation_id: String,
        evidence_id: String,
    },
    PolicyRejected {
        obligation_id: String,
        evidence_id: String,
        disposition: EvidenceDisposition,
        reason: String,
    },
    NativeTrustIrArtifactMismatch {
        obligation_id: String,
        expected_suite: String,
        request_id: Option<u32>,
        proof_obligation_id: Option<u32>,
        identity_error: Option<String>,
    },
}

fn full_verification_blockers_for_obligation(
    obligation: &TrustObligation,
    route: Option<ObligationRoute>,
    skipped: Option<&trust_verifier_api::SkippedObligation>,
    decisions: &[FullVerificationEvidenceDecision],
    native_trust_ir: Option<&FullVerificationNativeTrustIrEvidence>,
) -> Vec<FullVerificationEvidenceBlocker> {
    let mut blockers = Vec::new();
    if let Some(skipped) = skipped {
        blockers.push(FullVerificationEvidenceBlocker::Skipped {
            obligation_id: obligation.obligation_id.clone(),
            reason: skipped.reason.clone(),
        });
    }
    if decisions.is_empty() && skipped.is_none() {
        blockers.push(FullVerificationEvidenceBlocker::MissingEvidence {
            obligation_id: obligation.obligation_id.clone(),
        });
    }

    for decision in decisions {
        if decision.status == EvidenceStatus::Unsupported {
            blockers.push(FullVerificationEvidenceBlocker::UnsupportedEvidence {
                obligation_id: obligation.obligation_id.clone(),
                evidence_id: decision.evidence_id.clone(),
            });
        }
        if decision.disposition != EvidenceDisposition::AcceptedProof {
            blockers.push(FullVerificationEvidenceBlocker::PolicyRejected {
                obligation_id: obligation.obligation_id.clone(),
                evidence_id: decision.evidence_id.clone(),
                disposition: decision.disposition,
                reason: decision.reason.clone(),
            });
        }
    }

    if route.is_some_and(|route| route.primary.requires_trust_ir_native_bundle())
        && decisions.iter().any(|decision| decision.status == EvidenceStatus::Proved)
        && native_trust_ir.is_some_and(|native_trust_ir| !native_trust_ir.has_matching_artifacts())
    {
        let native_trust_ir = native_trust_ir.expect("checked is_some");
        blockers.push(FullVerificationEvidenceBlocker::NativeTrustIrArtifactMismatch {
            obligation_id: obligation.obligation_id.clone(),
            expected_suite: native_trust_ir.expected_suite.clone(),
            request_id: native_trust_ir.request_id,
            proof_obligation_id: native_trust_ir.proof_obligation_id,
            identity_error: native_trust_ir.identity_error.clone(),
        });
    }

    blockers
}

fn native_trust_ir_evidence_view(
    obligation: &TrustObligation,
    route: ObligationRoute,
    decisions: &[FullVerificationEvidenceDecision],
) -> Option<FullVerificationNativeTrustIrEvidence> {
    if !route.primary.requires_trust_ir_native_bundle() {
        return None;
    }

    let identity = NativeTrustIrObligationIdentity::from_obligation(obligation, route.primary);
    let (declared_suite, request_id, proof_obligation_id, identity_error) = match identity {
        Ok(identity) => {
            (identity.suite, identity.request_id, Some(identity.proof_obligation_id), None)
        }
        Err(error) => (None, None, None, Some(error)),
    };
    let has_native_trust_ir_artifact = decisions.iter().any(|decision| {
        decision
            .artifacts
            .iter()
            .any(|artifact| artifact.uri.starts_with("trust_ir-native://verification-bundle/"))
    });
    let has_native_trust_ir_diagnostic = decisions.iter().any(|decision| {
        decision.diagnostics.iter().any(|diagnostic| diagnostic.contains("TrustIr native"))
    });
    if declared_suite.is_none()
        && request_id.is_none()
        && proof_obligation_id.is_none()
        && !has_native_trust_ir_artifact
        && !has_native_trust_ir_diagnostic
    {
        return None;
    }

    let expected_suite = route.primary.name().to_string();
    let artifacts = decisions.iter().flat_map(|decision| decision.artifacts.iter());
    let mut bundle_artifact_present = false;
    let mut request_artifact_present = false;
    let mut proof_obligation_artifact_present = false;
    for artifact in artifacts {
        if artifact.kind == EvidenceArtifactKind::EngineInput
            && native_trust_ir_bundle_uri(&artifact.uri)
        {
            bundle_artifact_present = true;
        }
        if artifact.kind == EvidenceArtifactKind::EngineInput
            && request_id.is_some_and(|request_id| {
                native_trust_ir_request_uri(&artifact.uri, &expected_suite, request_id)
            })
        {
            request_artifact_present = true;
        }
        if artifact.kind == EvidenceArtifactKind::NormalizedObligation
            && request_id.zip(proof_obligation_id).is_some_and(|(request_id, proof_id)| {
                native_trust_ir_proof_uri(&artifact.uri, &expected_suite, request_id, proof_id)
            })
        {
            proof_obligation_artifact_present = true;
        }
    }

    Some(FullVerificationNativeTrustIrEvidence {
        expected_suite,
        declared_suite,
        request_id,
        proof_obligation_id,
        bundle_artifact_present,
        request_artifact_present,
        proof_obligation_artifact_present,
        identity_error,
    })
}

const NATIVE_TRUST_IR_URI_PREFIX: &str = "trust_ir-native://verification-bundle/";

fn native_trust_ir_bundle_uri(uri: &str) -> bool {
    let Some(remainder) = uri.strip_prefix(NATIVE_TRUST_IR_URI_PREFIX) else {
        return false;
    };
    let segments = remainder.split('/').collect::<Vec<_>>();
    matches!(segments.as_slice(), [bundle_digest] if canonical_sha256_hex(bundle_digest))
}

fn native_trust_ir_request_uri(uri: &str, suite: &str, request_id: u32) -> bool {
    let Some(remainder) = uri.strip_prefix(NATIVE_TRUST_IR_URI_PREFIX) else {
        return false;
    };
    let segments = remainder.split('/').collect::<Vec<_>>();
    matches!(
        segments.as_slice(),
        [bundle_digest, actual_suite, "request", actual_request_id, request_digest]
            if canonical_sha256_hex(bundle_digest)
                && *actual_suite == suite
                && canonical_u32_segment(actual_request_id, request_id)
                && canonical_sha256_hex(request_digest)
    )
}

fn native_trust_ir_proof_uri(uri: &str, suite: &str, request_id: u32, proof_id: u32) -> bool {
    let Some(remainder) = uri.strip_prefix(NATIVE_TRUST_IR_URI_PREFIX) else {
        return false;
    };
    let segments = remainder.split('/').collect::<Vec<_>>();
    matches!(
        segments.as_slice(),
        [
            bundle_digest,
            actual_suite,
            "request",
            actual_request_id,
            request_digest,
            "proof",
            actual_proof_id,
            proof_digest,
        ] if canonical_sha256_hex(bundle_digest)
            && *actual_suite == suite
            && canonical_u32_segment(actual_request_id, request_id)
            && canonical_sha256_hex(request_digest)
            && canonical_u32_segment(actual_proof_id, proof_id)
            && canonical_sha256_hex(proof_digest)
    )
}

fn canonical_u32_segment(segment: &str, expected: u32) -> bool {
    segment.parse::<u32>() == Ok(expected) && segment == expected.to_string()
}

fn canonical_sha256_hex(value: &str) -> bool {
    value.len() == 64
        && value.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}
