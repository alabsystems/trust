use sha2::{Digest, Sha256};

pub(crate) fn proved_result(
    typed_kind: trust_types::VcKind,
    function: &str,
    request_id: &str,
    proof_id: &str,
) -> trust_types::TransportObligationResult {
    let kind = typed_kind.transport_tag();
    let description = typed_kind.description();
    let owner = format!("{kind}:{function}:0");
    let native_id = format!("trust_ir-native-trust-wp-request-{request_id}-proof-{proof_id}");
    let normalized = bound_proof_artifact(
        "NormalizedObligation",
        b"exact normalized test obligation",
        &native_id,
        &owner,
        Vec::new(),
    );
    let transcript = bound_proof_artifact(
        "SolverTranscript",
        b"exact test solver transcript",
        &native_id,
        &owner,
        vec![artifact_reference(&normalized)],
    );
    let check = bound_proof_artifact(
        "ProofCheckReport",
        b"exact test proof-check report",
        &native_id,
        &owner,
        vec![artifact_reference(&transcript)],
    );
    let strength = trust_types::ProofStrength::deductive();

    trust_types::TransportObligationResult {
        obligation_id: Some(owner),
        claim_digest_sha256: Some(
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".to_string(),
        ),
        kind,
        typed_kind: Some(Box::new(typed_kind)),
        description,
        location: None,
        outcome: trust_types::Outcome::Proved,
        solver: "trust-full-verifier".to_string(),
        time_ms: 1,
        counterexample: None,
        counterexample_model: None,
        reason: None,
        design_mandate: false,
        native_trust_ir: Some(native_evidence(request_id, proof_id, &native_id)),
        proof_evidence: Some(trust_types::TransportProofEvidence {
            suite: "trust-wp".to_string(),
            backend: "trust-wp".to_string(),
            request_id: Some(request_id.to_string()),
            proof_id: Some(proof_id.to_string()),
            native_id: Some(native_id),
            status: trust_types::TransportProofStatus::Proved,
            strength: Some(strength.clone()),
            evidence: Some(trust_types::ProofEvidence::from(strength)),
            artifacts: vec![normalized, transcript, check],
            diagnostics: Vec::new(),
        }),
        monitor: None,
    }
}

#[allow(dead_code)] // Included by tests that only need the proved fixture.
pub(crate) fn failed_result(
    kind: &str,
    description: &str,
    function: &str,
    request_id: &str,
    proof_id: &str,
    counterexample: &str,
) -> trust_types::TransportObligationResult {
    let owner = format!("{kind}:{function}:0");
    let native_id = format!("trust_ir-native-trust-wp-request-{request_id}-proof-{proof_id}");
    trust_types::TransportObligationResult {
        obligation_id: Some(owner),
        claim_digest_sha256: None,
        kind: kind.to_string(),
        typed_kind: None,
        description: description.to_string(),
        location: None,
        outcome: trust_types::Outcome::Failed,
        solver: "trust-full-verifier".to_string(),
        time_ms: 1,
        counterexample: Some(counterexample.to_string()),
        counterexample_model: None,
        reason: None,
        design_mandate: false,
        native_trust_ir: Some(native_evidence(request_id, proof_id, &native_id)),
        proof_evidence: None,
        monitor: None,
    }
}

fn native_evidence(
    request_id: &str,
    proof_id: &str,
    native_id: &str,
) -> trust_types::TransportNativeTrustIrEvidence {
    trust_types::TransportNativeTrustIrEvidence {
        suite: "trust-wp".to_string(),
        backend: "trust-wp".to_string(),
        request_id: Some(request_id.to_string()),
        native_id: Some(native_id.to_string()),
        present: true,
        artifacts: native_trust_ir_artifacts(request_id, proof_id, native_id),
        diagnostics: Vec::new(),
    }
}

fn native_trust_ir_artifacts(
    request_id: &str,
    proof_id: &str,
    native_id: &str,
) -> Vec<trust_types::TransportEvidenceArtifact> {
    let bundle = native_materialization(
        "bundle",
        None,
        None,
        serde_json::json!({"bundle": "exact"}),
        native_id,
        Vec::new(),
    );
    let bundle_uri = format!("trust_ir-native://verification-bundle/{}", bundle.1.value);
    let request = native_materialization(
        "request",
        Some(request_id),
        None,
        serde_json::json!({"request": "exact"}),
        native_id,
        vec![trust_types::TransportArtifactReference {
            kind: "EngineInput".to_string(),
            digest: bundle.1.clone(),
        }],
    );
    let request_uri = format!("{bundle_uri}/trust-wp/request/{request_id}/{}", request.1.value);
    let normalized = native_materialization(
        "normalized_obligation",
        Some(request_id),
        Some(proof_id),
        serde_json::json!({"obligation": "exact"}),
        native_id,
        vec![trust_types::TransportArtifactReference {
            kind: "EngineInput".to_string(),
            digest: request.1.clone(),
        }],
    );
    let normalized_uri = format!("{request_uri}/proof/{proof_id}/{}", normalized.1.value);

    vec![
        materialized_artifact("EngineInput", "trust_ir-json", bundle, bundle_uri),
        materialized_artifact("EngineInput", "trust_ir-json", request, request_uri),
        materialized_artifact("NormalizedObligation", "trust_ir-json", normalized, normalized_uri),
    ]
}

fn native_materialization(
    role: &str,
    request_id: Option<&str>,
    proof_id: Option<&str>,
    payload: serde_json::Value,
    native_id: &str,
    references: Vec<trust_types::TransportArtifactReference>,
) -> (trust_types::TransportArtifactMaterialization, trust_types::TransportArtifactDigest) {
    let mut value = serde_json::json!({
        "schema": trust_types::NATIVE_TRUST_IR_MATERIALIZATION_SCHEMA,
        "role": role,
        "suite": if role == "bundle" { None } else { Some("trust-wp") },
        "request_id": request_id,
        "proof_id": proof_id,
        "payload": payload,
    });
    canonicalize_json(&mut value);
    let bytes = serde_json::to_vec(&value).expect("serialize test native materialization");
    let digest = sha256_digest(&bytes);
    let materialization = trust_types::TransportArtifactMaterialization::from_exact_bytes(
        &bytes, native_id, references,
    )
    .expect("valid test native materialization");
    (materialization, digest)
}

fn bound_proof_artifact(
    kind: &str,
    payload: &[u8],
    binding: &str,
    owner: &str,
    mut references: Vec<trust_types::TransportArtifactReference>,
) -> trust_types::TransportEvidenceArtifact {
    const MAGIC: &[u8] = b"trust.evidence-artifact-binding-envelope.v1\0";
    references.sort();
    let mut bytes = MAGIC.to_vec();
    let push = |bytes: &mut Vec<u8>, value: &[u8]| {
        bytes.extend_from_slice(&(value.len() as u32).to_be_bytes());
        bytes.extend_from_slice(value);
    };
    push(&mut bytes, kind.as_bytes());
    push(&mut bytes, owner.as_bytes());
    push(&mut bytes, binding.as_bytes());
    bytes.extend_from_slice(&(references.len() as u32).to_be_bytes());
    for reference in &references {
        push(&mut bytes, reference.kind.as_bytes());
        push(&mut bytes, reference.digest.algorithm.as_bytes());
        push(&mut bytes, reference.digest.value.as_bytes());
    }
    bytes.extend_from_slice(&(payload.len() as u64).to_be_bytes());
    bytes.extend_from_slice(payload);
    let digest = sha256_digest(&bytes);
    let materialization = trust_types::TransportArtifactMaterialization::from_exact_bytes(
        &bytes, binding, references,
    )
    .expect("valid test bound proof materialization");
    materialized_artifact(
        kind,
        "binary",
        (materialization, digest.clone()),
        format!("artifact://test-proof/{kind}/{}", digest.value),
    )
}

fn materialized_artifact(
    kind: &str,
    format: &str,
    materialized: (
        trust_types::TransportArtifactMaterialization,
        trust_types::TransportArtifactDigest,
    ),
    uri: String,
) -> trust_types::TransportEvidenceArtifact {
    trust_types::TransportEvidenceArtifact {
        kind: kind.to_string(),
        format: Some(format.to_string()),
        artifact_id: Some(kind.to_string()),
        digest: Some(materialized.1),
        uri: Some(uri),
        materialization: Some(materialized.0),
        metadata: None,
    }
}

fn artifact_reference(
    artifact: &trust_types::TransportEvidenceArtifact,
) -> trust_types::TransportArtifactReference {
    trust_types::TransportArtifactReference {
        kind: artifact.kind.clone(),
        digest: artifact.digest.clone().expect("test artifact digest"),
    }
}

fn sha256_digest(bytes: &[u8]) -> trust_types::TransportArtifactDigest {
    trust_types::TransportArtifactDigest {
        algorithm: "sha256".to_string(),
        value: format!("{:x}", Sha256::digest(bytes)),
    }
}

fn canonicalize_json(value: &mut serde_json::Value) {
    match value {
        serde_json::Value::Array(values) => {
            for value in values {
                canonicalize_json(value);
            }
        }
        serde_json::Value::Object(object) => {
            let old = std::mem::take(object);
            let mut entries = old.into_iter().collect::<Vec<_>>();
            entries.sort_by(|left, right| left.0.cmp(&right.0));
            for (key, mut value) in entries {
                canonicalize_json(&mut value);
                object.insert(key, value);
            }
        }
        _ => {}
    }
}
