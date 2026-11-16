//! Structural publication of checked source-clause composition certificates.
//!
//! These checks bind serialized evidence to its original source row. They do
//! not replay the proof and never restore authority to a saved report.

use super::*;

pub const SOURCE_CLAUSE_PROOF_SCHEMA: &str = "trust.source-clause-body-proof.v1";
pub const EXPANDED_SOURCE_CLAUSE_PROOF_SCHEMA: &str = "trust.source-clause-body-proof.v2";
pub const SOURCE_CLAUSE_PROOF_SUITE: &str = "trust-source-contract";
pub const SOURCE_CLAUSE_PROOF_BACKEND: &str = "checked-body-composition";

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CertificateIdentity {
    schema: String,
    source: SourceIdentity,
    #[serde(rename = "body_proofs")]
    _body_proofs: IgnoredAny,
    #[serde(rename = "inferred_returns")]
    _inferred_returns: IgnoredAny,
}

// The existing typed VC codec retains the full formula, including wide integer
// literals. The proof checker alone interprets the function, contracts, body
// proof group and callee derivations; this projection cannot accept a proof.
#[derive(Deserialize)]
struct SourceIdentity {
    obligation_id: String,
    #[serde(default)]
    source_text_sha256: Option<String>,
    #[serde(default)]
    expanded_function_identity: Option<crate::expanded_function_identity::ExpandedFunctionIdentity>,
    source_vc: VerificationCondition,
    overflow_checks: bool,
    target: String,
}

fn certificate_payload(
    artifacts: &[TransportEvidenceArtifact],
    owner: Option<&str>,
    trusted_root: Option<&Path>,
) -> Result<Vec<u8>, String> {
    let owner = owner
        .filter(|owner| canonical_proof_artifact_owner(owner))
        .ok_or("source-clause certificate owner is not canonical")?;
    let [artifact] = artifacts else {
        return Err("source-clause proof requires exactly one certificate".into());
    };
    let digest = artifact
        .digest
        .as_ref()
        .filter(|digest| is_canonical_sha256_digest(digest))
        .ok_or("source-clause certificate requires a canonical SHA-256 digest")?;
    if artifact.kind != "ProofCertificate"
        || !matches!(
            artifact.format.as_deref(),
            Some(SOURCE_CLAUSE_PROOF_SCHEMA | EXPANDED_SOURCE_CLAUSE_PROOF_SCHEMA)
        )
        || artifact.artifact_id.as_deref()
            != Some(format!("source-clause:v1:{}", digest.value).as_str())
        || artifact.uri.as_deref()
            != Some(
                format!("trust-source-contract://{owner}/certificate/sha256/{}", digest.value)
                    .as_str(),
            )
        || artifact.metadata.is_some()
    {
        return Err("source-clause certificate kind, format, identity or URI mismatch".into());
    }
    let materialization =
        artifact.materialization.as_ref().ok_or("source-clause certificate is not materialized")?;
    let binding = format!("trust-source-clause:{owner}");
    if materialization.proof_binding_id != binding
        || !materialization.referenced_artifacts.is_empty()
    {
        return Err("source-clause certificate binding or references mismatch".into());
    }
    let bytes = match trusted_root {
        Some(root) => materialization.decoded_bytes_at_root(digest, root),
        None if materialization.matches_sha256_digest(digest) => materialization.decoded_bytes(),
        None => return Err("source-clause certificate bytes differ from digest".into()),
    }?;
    let payload = transport_bound_payload(&bytes, &artifact.kind, owner, &binding, &[])
        .ok_or("source-clause certificate envelope differs from owner")?;
    let certificate: CertificateIdentity = crate::json_depth::from_slice_deep(payload)
        .map_err(|error| format!("invalid source-clause certificate identity: {error}"))?;
    let source_identity_valid = match (
        &certificate.source.source_text_sha256,
        &certificate.source.expanded_function_identity,
    ) {
        (Some(digest), None) => {
            certificate.schema == SOURCE_CLAUSE_PROOF_SCHEMA
                && crate::digest::is_stable_sha256_hex(digest)
        }
        (None, Some(expanded)) => {
            certificate.schema == EXPANDED_SOURCE_CLAUSE_PROOF_SCHEMA && expanded.is_well_formed()
        }
        _ => false,
    };
    if !source_identity_valid
        || artifact.format.as_deref() != Some(certificate.schema.as_str())
        || certificate.source.obligation_id != owner
    {
        return Err("source-clause certificate schema or source owner mismatch".into());
    }
    Ok(payload.to_vec())
}

pub(super) fn topology_defect(
    artifacts: &[TransportEvidenceArtifact],
    owner: Option<&str>,
    trusted_root: Option<&Path>,
) -> Option<String> {
    certificate_payload(artifacts, owner, trusted_root).err()
}

/// Return the immutable typed certificate payload after structural and exact
/// source-row binding checks. The typed body/DAG digest is an opaque outer
/// identity here. Before granting live publication, callers must rederive it
/// using `trust_certify::source_clause_proof::source_clause_input_digest_sha256`
/// and replay with `trust_certify::source_clause_proof::replay_source_clause`.
pub fn source_clause_certificate_payload(
    proof: &TransportProofEvidence,
    owner: Option<&str>,
    identity: Option<&crate::obligation_identity::ObligationIdentity>,
    claim_digest_sha256: Option<&str>,
    snapshot: Option<&crate::OriginalVcSnapshot>,
    trusted_root: Option<&Path>,
) -> Result<Vec<u8>, String> {
    if proof.suite != SOURCE_CLAUSE_PROOF_SUITE
        || proof.backend != SOURCE_CLAUSE_PROOF_BACKEND
        || proof.status != TransportProofStatus::Proved
        || proof.request_id.is_some()
        || proof.native_id.is_some()
        || proof.strength.as_ref() != Some(&ProofStrength::deductive())
        || proof.evidence.as_ref() != Some(&ProofEvidence::from(ProofStrength::deductive()))
        || !proof.diagnostics.is_empty()
    {
        return Err("source-clause proof identity or fixed Deductive/Sound grade mismatch".into());
    }
    let payload = certificate_payload(&proof.artifacts, owner, trusted_root)?;
    if proof.proof_id != proof.artifacts[0].artifact_id {
        return Err("source-clause proof ID differs from certificate ID".into());
    }
    let certificate: CertificateIdentity = crate::json_depth::from_slice_deep(&payload)
        .map_err(|error| format!("invalid source-clause certificate identity: {error}"))?;
    let source = certificate.source;
    let identity = identity.ok_or("source-clause proof has no outer function identity")?;
    if identity.function_source_sha256 != source.source_text_sha256
        || identity.expanded_function_identity != source.expanded_function_identity
    {
        return Err("source-clause certificate differs from outer function source".into());
    }
    if source
        .expanded_function_identity
        .as_ref()
        .is_some_and(|expanded| expanded.function_path != identity.def_path())
    {
        return Err("source-clause expanded function differs from outer obligation key".into());
    }
    let snapshot = snapshot.ok_or("source-clause proof has no original VC snapshot")?;
    if snapshot.expanded_function_identity != source.expanded_function_identity {
        return Err(
            "source-clause certificate differs from outer expanded function identity".into()
        );
    }
    if !snapshot
        .typed_input_digest_sha256
        .as_deref()
        .is_some_and(crate::digest::is_stable_sha256_hex)
    {
        return Err("source-clause proof has no outer typed-input identity".into());
    }
    let vc = snapshot.decode_for_row(
        owner.ok_or("missing source owner")?,
        claim_digest_sha256.ok_or("missing source claim digest")?,
    )?;
    if snapshot.overflow_checks != source.overflow_checks
        || snapshot.target != source.target
        || crate::original_vc_snapshot::bounded_original_vc_json(&vc)
            .zip(crate::original_vc_snapshot::bounded_original_vc_json(&source.source_vc))
            .is_none_or(|(outer, inner)| outer != inner)
    {
        return Err(
            "source-clause certificate differs from complete original VC or semantics".into()
        );
    }
    Ok(payload)
}
