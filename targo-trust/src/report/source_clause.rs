//! Live publication requires replay as well as the shared structural checks.
use super::*;

pub(super) fn proof_evidence_report(
    result: &VerificationResult,
    structured: Option<&crate::types::StructuredTransportEvidence>,
    materialization_root: Option<&Path>,
) -> Option<ObligationProofEvidenceReport> {
    if !result.outcome.is_proved() {
        return None;
    }
    let structured = structured?;
    let proof = structured.proof_evidence.as_ref()?;
    let payload = trust_types::source_clause_certificate_payload(
        proof,
        structured.obligation_id.as_deref(),
        structured.identity.as_ref(),
        structured.claim_digest_sha256.as_deref(),
        structured.original_vc_snapshot.as_deref(),
        materialization_root,
    )
    .ok()?;
    let certificate = trust_types::json_depth::from_slice_deep::<
        trust_certify::source_clause_proof::SourceClauseCertificate,
    >(&payload)
    .ok()?;
    let expected_input =
        structured.original_vc_snapshot.as_ref()?.typed_input_digest_sha256.as_deref()?;
    if trust_certify::source_clause_proof::source_clause_input_digest_sha256(
        &certificate.source,
        &certificate.inferred_returns,
    )
    .as_deref()
        != Some(expected_input)
    {
        return None;
    }
    let checked = trust_certify::source_clause_proof::replay_source_clause(&certificate).ok()?;
    // The checked fact must emit this exact evidence, not a corrected owner,
    // different grade, different body group or rebound certificate.
    let mut expected = checked.transport_evidence()?;
    if serde_json::to_vec(checked.certificate()).ok()? != payload {
        return None;
    }
    // Storage may be inline or path-backed under the caller's trusted root;
    // the shared validator already checked these exact bytes and framing.
    expected.artifacts[0].materialization = proof.artifacts[0].materialization.clone();
    if &expected != proof {
        return None;
    }
    Some(ObligationProofEvidenceReport {
        suite: Some(proof.suite.clone()),
        backend: proof.backend.clone(),
        request_id: None,
        proof_id: proof.proof_id.clone(),
        native_id: None,
        status: Some(proof.status),
        provenance: ObligationEvidenceProvenanceReport::NativeBackend {
            verifier: proof.backend.clone(),
        },
        strength: checked.proof_strength(),
        evidence: ProofEvidence::from(checked.proof_strength()),
        proof_certificate: None,
        native_trust_ir: None,
        artifacts: proof.artifacts.clone(),
        diagnostics: vec![],
        solver_warnings: None,
    })
}
