//! Structural publication checks for the modern compound native body-WP certificate.
//! This projects identity from the certificate; it neither interprets MIR nor replays a proof.

use trust_ir_contract::body_wp_identity::{
    NATIVE_BODY_WP_SCHEMA as SCHEMA, native_body_wp_bundle_id, native_body_wp_id_selects_request,
};

use super::*;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Certificate {
    statement: Statement,
    replay: String,
    accepted: bool,
    authority: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Statement {
    schema: String,
    bundle_id: String,
    obligation_id: String,
    request: RequestIdentity,
    module_digest: NativeDigest,
    source_digest: NativeDigest,
    results: Vec<ResultIdentity>,
    // This structural publication reader grants no authority from diagnostic
    // witness data. The native verifier independently checks its typed schema
    // and correspondence before minting the compiler's private proof fact.
    #[serde(default, rename = "translation_witness")]
    _translation_witness: Option<IgnoredAny>,
}

// Only the selected identity is interpreted here. The native engine owns the
// complete request, body, derivation and evidence schemas and already replayed
// them before minting the compiler's private publication fact.
#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct RequestIdentity {
    id: u32,
    mode: String,
    obligations: Vec<u32>,
    #[serde(rename = "function")]
    _function: u32,
    #[serde(rename = "lineage_roots")]
    _lineage_roots: Vec<u32>,
    #[serde(rename = "options")]
    _options: serde_json::Value,
    #[serde(rename = "provenance")]
    _provenance: serde_json::Value,
    #[serde(rename = "diagnostics")]
    _diagnostics: serde_json::Value,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct NativeDigest {
    algorithm: String,
    bytes: [u8; 32],
}

impl NativeDigest {
    fn valid(&self) -> bool {
        self.algorithm == "Sha256" && self.bytes.iter().any(|byte| *byte != 0)
    }
}

#[derive(Deserialize)]
struct ResultIdentity {
    api_version: String,
    bundle_id: String,
    status: String,
    obligation_results: Vec<ObligationIdentity>,
}

#[derive(Deserialize)]
struct ObligationIdentity {
    obligation_id: String,
    status: VerifiedStatus,
}

#[derive(Deserialize)]
enum VerifiedStatus {
    #[serde(rename = "verified")]
    Verified(IgnoredAny),
}

/// Check the modern body-WP certificate and its exact selected native identity.
/// A successful structural check grants no verifier or saved-report authority.
pub fn modern_body_wp_proof_defect(
    artifacts: &[TransportEvidenceArtifact],
    obligation_id: Option<&str>,
    request_id: Option<&str>,
    proof_id: Option<&str>,
    strength: &ProofStrength,
    evidence: &ProofEvidence,
    native: &TransportNativeTrustIrEvidence,
    trusted_root: Option<&Path>,
) -> Option<String> {
    if *strength != ProofStrength::deductive()
        || (*evidence != ProofEvidence::from(ProofStrength::deductive())
            && *evidence != ProofEvidence::new(ReasoningKind::Deductive, AssuranceLevel::Sound))
    {
        return Some("modern body-WP evidence must be exactly Deductive/Sound".into());
    }
    let parsed = |value: Option<&str>| {
        value.and_then(|value| {
            value.parse::<u32>().ok().filter(|number| number.to_string() == value)
        })
    };
    let (Some(request_id), Some(proof_id)) = (parsed(request_id), parsed(proof_id)) else {
        return Some("modern body-WP native request/proof IDs are not canonical u32 values".into());
    };
    let statement = match certificate_statement(artifacts, obligation_id, trusted_root) {
        Ok(statement) => statement,
        Err(error) => return Some(error),
    };
    if statement.request.id != request_id || statement.request.obligations != [proof_id] {
        return Some("modern body-WP selected IDs differ from the outer native identity".into());
    }
    native_statement_defect(&statement, native, trusted_root)
}

pub(super) fn certificate_identity(
    artifacts: &[TransportEvidenceArtifact],
    obligation_id: Option<&str>,
    trusted_root: Option<&Path>,
) -> Result<(u32, u32), String> {
    let statement = certificate_statement(artifacts, obligation_id, trusted_root)?;
    Ok((statement.request.id, statement.request.obligations[0]))
}

fn certificate_statement(
    artifacts: &[TransportEvidenceArtifact],
    obligation_id: Option<&str>,
    trusted_root: Option<&Path>,
) -> Result<Statement, String> {
    let owner = obligation_id
        .filter(|owner| canonical_proof_artifact_owner(owner))
        .ok_or("modern body-WP public obligation owner is not canonical")?;
    let [artifact] = artifacts else {
        return Err("modern body-WP requires exactly one compound proof certificate".into());
    };
    let digest = artifact
        .digest
        .as_ref()
        .filter(|digest| is_canonical_sha256_digest(digest))
        .ok_or("modern body-WP certificate has no canonical SHA-256 digest")?;
    if artifact.kind != "ProofCertificate"
        || artifact.uri.as_deref()
            != Some(
                format!("trust-wp-body://{owner}/certificate/sha256/{}", digest.value,).as_str(),
            )
    {
        return Err(
            "modern body-WP certificate URI/kind does not bind its public owner and digest".into(),
        );
    }
    let materialization = artifact
        .materialization
        .as_ref()
        .ok_or("modern body-WP certificate has no materialization")?;
    let binding = format!("trust-wp-body:{owner}");
    if materialization.proof_binding_id != binding
        || !materialization.referenced_artifacts.is_empty()
    {
        return Err(
            "modern body-WP certificate has the wrong owner binding or extra references".into()
        );
    }
    let bytes = match trusted_root {
        Some(root) => materialization.decoded_bytes_at_root(digest, root),
        None if materialization.matches_sha256_digest(digest) => materialization.decoded_bytes(),
        None => return Err("modern body-WP certificate bytes do not match their digest".into()),
    }?;
    let payload = transport_bound_payload(
        &bytes,
        &artifact.kind,
        owner,
        &binding,
        &materialization.referenced_artifacts,
    )
    .ok_or("modern body-WP certificate envelope does not bind the exact public owner")?;
    let certificate: Certificate = serde_json::from_slice(payload)
        .map_err(|error| format!("invalid modern body-WP certificate: {error}"))?;
    let statement = certificate.statement;
    if !certificate.accepted
        || certificate.authority != "Trusted; not Clean-kernel certified"
        || certificate.replay
            != "rederive WP from original typed body and contract; replay native pure evidence"
        || statement.schema != SCHEMA
        || statement.obligation_id != owner
        || statement.bundle_id.is_empty()
        || !statement.module_digest.valid()
        || !statement.source_digest.valid()
        || statement.request.mode != "WeakestPrecondition"
    {
        return Err(
            "modern body-WP certificate header is not the accepted native body family".into()
        );
    }
    let [proof_id] = statement.request.obligations.as_slice() else {
        return Err("modern body-WP request does not select exactly one proof obligation".into());
    };
    let [result] = statement.results.as_slice() else {
        return Err("modern body-WP certificate does not carry exactly one result".into());
    };
    let [obligation] = result.obligation_results.as_slice() else {
        return Err("modern body-WP result does not carry exactly one obligation".into());
    };
    if result.api_version != "trust-wp.verify-bundle.v1"
        || result.status != "verified"
        || !native_body_wp_id_selects_request(&result.bundle_id, statement.request.id)
        || obligation.obligation_id
            != format!("trust-ir-r{}-proof-{proof_id}", statement.request.id)
    {
        return Err("modern body-WP result differs from its selected native obligation".into());
    }
    let VerifiedStatus::Verified(_) = &obligation.status;
    Ok(statement)
}

fn native_statement_defect(
    statement: &Statement,
    native: &TransportNativeTrustIrEvidence,
    trusted_root: Option<&Path>,
) -> Option<String> {
    let request_id = statement.request.id.to_string();
    let proof_id = statement.request.obligations[0];
    let expected_native_id =
        format!("trust_ir-native-trust-wp-request-{request_id}-proof-{proof_id}");
    let native_valid = match trusted_root {
        Some(root) => native_trust_ir_artifact_shape_is_publishable_at_root(native, root),
        None => native_trust_ir_artifact_shape_is_publishable(native),
    };
    if !native_valid
        || !native.present
        || native.suite != "trust-wp"
        || native.backend != "trust-wp"
        || native.request_id.as_deref() != Some(request_id.as_str())
        || native.native_id.as_deref() != Some(expected_native_id.as_str())
    {
        return Some(
            "modern body-WP native artifact identity is not the selected WP request".into(),
        );
    }
    let mut bundle = None;
    let mut request = None;
    for artifact in &native.artifacts {
        let Some(materialization) = artifact.materialization.as_ref() else {
            continue;
        };
        let Some(digest) = artifact.digest.as_ref() else {
            continue;
        };
        if let Some(value) = native_materialization_payload(
            materialization,
            digest,
            trusted_root,
            "bundle",
            None,
            None,
            None,
        ) {
            bundle = Some(value);
        }
        if let Some(value) = native_materialization_payload(
            materialization,
            digest,
            trusted_root,
            "request",
            Some("trust-wp"),
            Some(&request_id),
            None,
        ) {
            request = value.get("TrustWp").cloned();
        }
    }
    let Some(bundle) = bundle else {
        return Some("modern body-WP has no native bundle payload".into());
    };
    // Decode the complete self-describing transport through the same IR-owned
    // codec as the producer. Replay atoms may reference module formulas; the
    // codec restores only exact references and verifies their payload digests.
    let original =
        match trust_ir::request::transport::rehydrate_native_bundle_transport_payload(&bundle) {
            Ok(bundle) => bundle,
            Err(error) => {
                return Some(format!(
                    "modern body-WP native input identity cannot be decoded: {error}"
                ));
            }
        };
    // Bundle::stable_digest represents the module by its recorded digest. Bind
    // that field to the actual module before it can bind the full input.
    // Use the writer's own refusal check before its infallible digest, as native
    // bundle validation does; a producer-internal type has no wire identity.
    if !original.module.wire_image_refusals().is_empty() {
        return Some("modern body-WP native module has no wire identity".into());
    }
    if original.module.stable_digest() != original.trust_ir_module_digest {
        return Some("modern body-WP native module differs from its recorded digest".into());
    }
    let Ok(bundle) = serde_json::to_value(&original) else {
        return Some("modern body-WP native input identity could not be encoded".into());
    };
    let Ok(certificate_request) = serde_json::to_value(&statement.request) else {
        return Some("modern body-WP request identity could not be encoded".into());
    };
    let (Ok(module_digest), Ok(source_digest)) = (
        serde_json::to_value(&statement.module_digest),
        serde_json::to_value(&statement.source_digest),
    ) else {
        return Some("modern body-WP digest identity could not be encoded".into());
    };
    if request.as_ref() != Some(&certificate_request)
        || bundle.get("trust_ir_module_digest") != Some(&module_digest)
        || bundle.get("provenance").and_then(|value| value.get("source_digest"))
            != Some(&source_digest)
    {
        return Some(
            "modern body-WP statement differs from its native request/module/source".into(),
        );
    }
    let matching_requests =
        bundle.get("requests").and_then(serde_json::Value::as_array).is_some_and(|requests| {
            let mut selected =
                requests.iter().filter_map(|value| value.get("TrustWp")).filter(|value| {
                    value.get("id").and_then(serde_json::Value::as_u64)
                        == Some(statement.request.id as u64)
                });
            selected.next() == Some(&certificate_request) && selected.next().is_none()
        });
    let matching_proofs = bundle
        .get("module")
        .and_then(|value| value.get("proof_obligations"))
        .and_then(serde_json::Value::as_array)
        .is_some_and(|proofs| {
            let mut selected = proofs.iter().filter(|proof| {
                proof.get("id").and_then(serde_json::Value::as_u64) == Some(proof_id as u64)
            });
            selected.next().is_some_and(|proof| {
                proof
                    .get("source")
                    .and_then(|value| value.get("public"))
                    .and_then(|value| value.get("obligation_id"))
                    .and_then(serde_json::Value::as_str)
                    == Some(statement.obligation_id.as_str())
            }) && selected.next().is_none()
        });
    let Some(module_name) = bundle
        .get("module")
        .and_then(|value| value.get("name"))
        .and_then(serde_json::Value::as_str)
    else {
        return Some("modern body-WP native module has no name".into());
    };
    let module_name = module_name.to_owned();
    if !matching_requests || !matching_proofs {
        return Some(
            "modern body-WP statement is not the exact native body/request/result identity".into(),
        );
    }
    // The v2 producer binds the complete canonical native-input identity, not
    // just its displayed module name and request number. Use the same owner
    // and complete original input as native TrustWP; work selection above
    // must not prune unselected requests from its identity. A digest-shaped
    // suffix is insufficient. This checks identity, never admission or replay.
    let input = original.stable_digest();
    if input.algorithm != trust_ir::proof::ProofDigestAlgorithm::Sha256
        || statement.results[0].bundle_id
            != native_body_wp_bundle_id(&module_name, statement.request.id, &input.bytes)
    {
        return Some(
            "modern body-WP result does not bind the complete original native input".into(),
        );
    }
    None
}
