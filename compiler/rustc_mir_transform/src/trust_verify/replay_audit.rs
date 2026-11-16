// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 OR MIT.

//! Observations of an admitted proof's reuse, never proof authority. A receipt
//! is paired with the selected sweep evidence, checked at the row boundary,
//! and erased if any final publication rewrite withdraws that row's proof.

use trust_types::{
    Outcome, TransportEvidenceDiagnostic, TransportEvidenceDiagnosticSeverity,
    TransportObligationResult, TransportProofStatus, VerificationCondition,
};

use super::{ResultObligationBinding, ResultProofAuthority};

pub(super) const CODE: &str = "clean_kernel_replay_audit_v1";

fn remove(diagnostics: &mut Vec<TransportEvidenceDiagnostic>) {
    diagnostics.retain(|diagnostic| diagnostic.code != CODE);
}

/// Called only after final row IDs and claim digests have been assigned. The
/// reserved observation is never inherited from submitted transport data.
pub(super) fn attach(
    row: &mut TransportObligationResult,
    index: usize,
    vc: &VerificationCondition,
    binding: Option<&ResultObligationBinding>,
    authority: Option<&ResultProofAuthority>,
) {
    if let Some(native) = &mut row.native_trust_ir {
        remove(&mut native.diagnostics);
    }
    if let Some(proof) = &mut row.proof_evidence {
        remove(&mut proof.diagnostics);
    }
    let Some(
        authority @ ResultProofAuthority::KernelCertified {
            evidence,
            replay_audit: Some(audit),
            ..
        },
    ) = authority
    else {
        return;
    };
    if authority.kernel_evidence_for(index, vc, binding).is_none()
        || !audit.matches(vc, evidence)
        || !has_published_kernel_proof(row)
    {
        return;
    }
    let (Some(obligation_id), Some(claim_digest)) = (&row.obligation_id, &row.claim_digest_sha256)
    else {
        return;
    };
    let Ok(detail) = serde_json::to_string(&serde_json::json!({
        "version": 1,
        "subject": vc.function.as_str(),
        "obligation_id": obligation_id,
        "claim_digest_sha256": claim_digest,
        "replay": audit,
    })) else {
        return;
    };
    row.proof_evidence.as_mut().unwrap().diagnostics.push(TransportEvidenceDiagnostic {
        code: CODE.to_string(),
        severity: TransportEvidenceDiagnosticSeverity::Info,
        message: "Observed reuse of this admitted kernel proof; diagnostic data, not authority"
            .to_string(),
        detail: Some(detail),
    });
}

fn has_published_kernel_proof(row: &TransportObligationResult) -> bool {
    row.outcome == Outcome::Proved
        && row.grade.as_ref().is_some_and(|grade| {
            grade.discharge == trust_types::authority_grade::GradeDischarge::KernelReferenceChecked
        })
        && row.proof_evidence.as_ref().is_some_and(|proof| {
            proof.suite == "trust-certify"
                && proof.backend == "clean-kernel"
                && proof.status == TransportProofStatus::Proved
                && proof.strength.as_ref().is_some_and(|strength| {
                    strength.assurance == trust_types::AssuranceLevel::Certified
                })
                && proof.evidence.as_ref().is_some_and(trust_types::ProofEvidence::is_certified)
                && !proof.diagnostics.iter().any(|diagnostic| {
                    diagnostic.severity == TransportEvidenceDiagnosticSeverity::Error
                })
                && proof.artifacts.len() == 1
                && proof.artifacts[0].kind == "clean_cic"
                && proof.artifacts[0].metadata.is_some()
        })
}

/// Run after the materialization and line-budget rewrites, before any public
/// output. This only removes diagnostics; it cannot grant or withdraw credit.
pub(super) fn retain_published(rows: &mut [TransportObligationResult]) {
    for row in rows {
        if let Some(native) = &mut row.native_trust_ir {
            remove(&mut native.diagnostics);
        }
        let admitted = has_published_kernel_proof(row);
        let id = row.obligation_id.as_deref();
        let claim = row.claim_digest_sha256.as_deref();
        if let Some(proof) = &mut row.proof_evidence {
            let count =
                proof.diagnostics.iter().filter(|diagnostic| diagnostic.code == CODE).count();
            proof.diagnostics.retain(|diagnostic| {
                diagnostic.code != CODE
                    || (admitted
                        && count == 1
                        && diagnostic.detail.as_deref().is_some_and(|detail| {
                            serde_json::from_str::<serde_json::Value>(detail).ok().is_some_and(
                                |value| {
                                    value.get("version").and_then(serde_json::Value::as_u64)
                                        == Some(1)
                                        && id.is_some()
                                        && value
                                            .get("obligation_id")
                                            .and_then(serde_json::Value::as_str)
                                            == id
                                        && claim.is_some()
                                        && value
                                            .get("claim_digest_sha256")
                                            .and_then(serde_json::Value::as_str)
                                            == claim
                                },
                            )
                        }))
            });
        }
    }
}

/// The budget API returns an already serialized payload. Erase observations
/// before its first serialization and inside its rewrite callback, so neither
/// the returned bytes nor the final row diagnostics retain a withheld proof's
/// observation. The ordinary budget policy and recount callback are unchanged.
pub(super) fn fit_function_result(
    result: &mut trust_types::FunctionTransportResult,
    budget: u64,
    framing: trust_types::transport_budget::TransportLineFraming,
    fallback_location: Option<trust_types::SourceSpan>,
    restate: &mut dyn FnMut(&mut trust_types::FunctionTransportResult),
) -> Result<trust_types::transport_budget::FittedTransportLine, serde_json::Error> {
    retain_published(&mut result.results);
    trust_types::transport_budget::fit_function_result(
        result,
        budget,
        framing,
        fallback_location,
        &mut |result| {
            restate(result);
            retain_published(&mut result.results);
        },
    )
}
