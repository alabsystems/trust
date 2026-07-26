//! Evidence acceptance / rejection policy for the full verifier.

use trust_verifier_api::{
    EngineManifest, EvidenceArtifactKind, EvidenceStatus, ObligationEvidence, TrustObligation,
};

use super::native_trust_ir::{
    DirectTrustVcProofReceipt, NativeTrustIrEvidenceIndex, native_trust_ir_artifact_match,
};
use super::policy::FullVerificationPolicy;
use super::routing::{ObligationRoute, PrimaryEngine, ProofFamily};

pub(super) fn select_evidence(
    obligation: &TrustObligation,
    bundle: &trust_verifier_api::TrustContractBundle,
    route: ObligationRoute,
    evidence: &[&ObligationEvidence],
    policy: FullVerificationPolicy,
    native_trust_ir: Option<&NativeTrustIrEvidenceIndex>,
    direct_trust_vc_receipt: Option<&DirectTrustVcProofReceipt>,
) -> Option<ObligationEvidence> {
    // Engines may return more than one distinct evidence row for an
    // obligation. A counterexample and a proof for the same claim are a hard
    // semantic conflict, not competing candidates from which the router may
    // pick the first acceptable proof.
    if evidence_has_proved_failed_conflict(obligation, evidence) {
        return None;
    }
    evidence
        .iter()
        .copied()
        .find(|item| {
            item.obligation_id == obligation.obligation_id
                && item.status == EvidenceStatus::Proved
                && evidence_satisfies_policy(
                    obligation,
                    bundle,
                    route,
                    item,
                    policy,
                    native_trust_ir,
                    direct_trust_vc_receipt,
                )
        })
        .cloned()
}

pub(super) fn evidence_has_proved_failed_conflict(
    obligation: &TrustObligation,
    evidence: &[&ObligationEvidence],
) -> bool {
    let mut proved = false;
    let mut failed = false;
    for item in
        evidence.iter().copied().filter(|item| item.obligation_id == obligation.obligation_id)
    {
        proved |= item.status == EvidenceStatus::Proved;
        failed |= item.status == EvidenceStatus::Failed;
        if proved && failed {
            return true;
        }
    }
    false
}

pub(super) fn evidence_satisfies_policy(
    obligation: &TrustObligation,
    bundle: &trust_verifier_api::TrustContractBundle,
    route: ObligationRoute,
    evidence: &ObligationEvidence,
    policy: FullVerificationPolicy,
    native_trust_ir: Option<&NativeTrustIrEvidenceIndex>,
    direct_trust_vc_receipt: Option<&DirectTrustVcProofReceipt>,
) -> bool {
    let Some(strength) = evidence.proof_strength.as_ref() else {
        return false;
    };
    if policy.reject_bounded_proofs && strength.is_bounded() {
        return false;
    }
    if !route.accepts_strength(strength) {
        return false;
    }
    if !obligation
        .required_strength
        .as_ref()
        .is_none_or(|required| strength.satisfies_requirement(required))
    {
        return false;
    }
    // `require_proof_artifacts` controls the ordinary public artifact policy;
    // it is not an authority-mode switch.  The dedicated direct TrustVC
    // namespace is backed by an in-process, non-public receipt and must remain
    // receipt-exclusive even when callers disable ordinary artifact checks.
    if evidence_uses_reserved_direct_trust_vc_namespace(evidence) {
        return direct_trust_vc_evidence_is_privately_authorized(
            route,
            bundle,
            obligation,
            evidence,
            direct_trust_vc_receipt,
        );
    }
    !policy.require_proof_artifacts
        || evidence_satisfies_full_artifact_policy(
            route,
            evidence,
            bundle,
            obligation,
            native_trust_ir,
            direct_trust_vc_receipt,
        )
}

pub(super) fn evidence_satisfies_full_artifact_policy(
    route: ObligationRoute,
    evidence: &ObligationEvidence,
    bundle: &trust_verifier_api::TrustContractBundle,
    obligation: &TrustObligation,
    native_trust_ir: Option<&NativeTrustIrEvidenceIndex>,
    direct_trust_vc_receipt: Option<&DirectTrustVcProofReceipt>,
) -> bool {
    // The direct certificate namespace is receipt-exclusive. A public
    // lookalike must never borrow an unrelated native TrustIr artifact match
    // for the same obligation identity through the ordinary fallback arm.
    if evidence_uses_reserved_direct_trust_vc_namespace(evidence) {
        return direct_trust_vc_evidence_is_privately_authorized(
            route,
            bundle,
            obligation,
            evidence,
            direct_trust_vc_receipt,
        );
    }
    evidence_satisfies_route_artifact_policy(route, evidence)
        && native_trust_ir_artifact_match(native_trust_ir, route, obligation).is_ok()
}

pub(super) fn evidence_uses_reserved_direct_trust_vc_namespace(
    evidence: &ObligationEvidence,
) -> bool {
    evidence.evidence_id.starts_with("trust-vc:direct-mir-memory:")
        || evidence.artifacts.iter().any(|artifact| {
            artifact.uri.starts_with(
                trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_PROOF_CERTIFICATE_URI_PREFIX,
            )
        })
}

pub(super) fn direct_trust_vc_evidence_is_privately_authorized(
    route: ObligationRoute,
    bundle: &trust_verifier_api::TrustContractBundle,
    obligation: &TrustObligation,
    evidence: &ObligationEvidence,
    direct_trust_vc_receipt: Option<&DirectTrustVcProofReceipt>,
) -> bool {
    route.primary == PrimaryEngine::TrustVc
        && direct_trust_vc_receipt
            .is_some_and(|receipt| receipt.matches(bundle, obligation, evidence))
}

pub(super) fn evidence_satisfies_route_artifact_policy(
    route: ObligationRoute,
    evidence: &ObligationEvidence,
) -> bool {
    if !evidence.satisfies_proof_artifact_policy() {
        return false;
    }
    let has = |kind| evidence.artifacts.iter().any(|artifact| artifact.kind == kind);
    match route.proof_family {
        ProofFamily::TrustMcReachability => {
            has(EvidenceArtifactKind::SolverTranscript)
                && has(EvidenceArtifactKind::ReplayLog)
                && has(EvidenceArtifactKind::ProofCheckReport)
        }
        ProofFamily::TyTemporal | ProofFamily::TrustWpFunctional => {
            has(EvidenceArtifactKind::SolverTranscript)
                && has(EvidenceArtifactKind::ProofCheckReport)
        }
        ProofFamily::TrustVcOwnership => has(EvidenceArtifactKind::ProofCertificate),
    }
}

pub(super) fn rejected_primary_evidence(
    obligation: &TrustObligation,
    evidence: &[&ObligationEvidence],
) -> Option<ObligationEvidence> {
    [
        EvidenceStatus::Failed,
        EvidenceStatus::Timeout,
        EvidenceStatus::Canceled,
        EvidenceStatus::Unsupported,
        EvidenceStatus::Unknown,
        EvidenceStatus::Proved,
    ]
    .into_iter()
    .find_map(|status| {
        evidence
            .iter()
            .copied()
            .find(|item| item.obligation_id == obligation.obligation_id && item.status == status)
            .cloned()
    })
}

pub(super) fn rejected_primary_evidence_reason(
    obligation: &TrustObligation,
    bundle: &trust_verifier_api::TrustContractBundle,
    route: ObligationRoute,
    evidence: &ObligationEvidence,
    native_trust_ir: Option<&NativeTrustIrEvidenceIndex>,
    direct_trust_vc_receipt: Option<&DirectTrustVcProofReceipt>,
) -> String {
    match evidence.status {
        EvidenceStatus::Proved => match evidence.proof_strength.as_ref() {
            Some(strength) if strength.is_bounded() => {
                "bounded proof is diagnostic-only in full verification".to_string()
            }
            Some(strength) if !route.accepts_strength(strength) => format!(
                "proof strength {:?} does not satisfy route requirement {}",
                strength,
                route.required_strength_description()
            ),
            Some(strength) => {
                if let Some(required) = obligation.required_strength.as_ref()
                    && !strength.satisfies_requirement(required)
                {
                    return format!(
                        "proof strength {:?} does not satisfy explicit obligation requirement {:?}",
                        strength, required
                    );
                }
                if !evidence_satisfies_route_artifact_policy(route, evidence) {
                    return "proved evidence failed the exact owner-bound materialization DAG and route-specific artifact policy".to_string();
                }
                if evidence_uses_reserved_direct_trust_vc_namespace(evidence)
                    && !direct_trust_vc_evidence_is_privately_authorized(
                        route,
                        bundle,
                        obligation,
                        evidence,
                        direct_trust_vc_receipt,
                    )
                {
                    return "direct TrustVC certificate evidence lacked the matching private post-solve receipt"
                        .to_string();
                }
                if direct_trust_vc_evidence_is_privately_authorized(
                    route,
                    bundle,
                    obligation,
                    evidence,
                    direct_trust_vc_receipt,
                ) {
                    return "proved evidence was not acceptable to full-verification policy"
                        .to_string();
                }
                if let Err(reason) =
                    native_trust_ir_artifact_match(native_trust_ir, route, obligation)
                {
                    return reason;
                }
                "proved evidence was not acceptable to full-verification policy".to_string()
            }
            None => "proved evidence did not include proof strength".to_string(),
        },
        EvidenceStatus::Failed => "primary evidence found a counterexample".to_string(),
        EvidenceStatus::Unknown => "primary evidence was unknown".to_string(),
        EvidenceStatus::Timeout => "primary evidence timed out".to_string(),
        EvidenceStatus::Canceled => "primary evidence was canceled".to_string(),
        EvidenceStatus::Unsupported => "primary evidence was unsupported".to_string(),
        _ => "primary evidence had an unrecognized status".to_string(),
    }
}

pub(super) fn missing_primary_evidence_reason(
    manifest: &EngineManifest,
    obligation: &TrustObligation,
) -> String {
    format!(
        "primary owner {}@{} returned no evidence for obligation {}; full verification does not allow silently dropped obligations",
        manifest.name, manifest.version, obligation.obligation_id
    )
}
