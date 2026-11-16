//! Checked correspondence from an authored clause to a complete proved body group.
//! The translation stays trusted: this authority is exactly Trusted/Deductive.

use std::borrow::Cow;
use std::sync::Arc;

use serde::{Deserialize, Serialize};
use trust_types::{CompilerContractBundle, VerifiableFunction, VerificationCondition};
use trust_verifier_api::TrustContractBundle;

use crate::inferred_return_proof::{
    InferredReturnProofGraph, graph_within_depth_gate, replay_inferred_return_graph_on_stack,
};

pub const SCHEMA: &str = "trust.source-clause-body-proof.v1";
pub const EXPANDED_SCHEMA: &str = "trust.source-clause-body-proof.v2";

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceClauseInput {
    pub function: VerifiableFunction,
    pub compiler_contracts: CompilerContractBundle,
    pub public_bundle: TrustContractBundle,
    pub obligation_id: String,
    pub source_contract_index: usize,
    pub stable_crate_id: u64,
    pub crate_name: String,
    pub target_pointer_width_bits: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source_text_sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub expanded_function_identity:
        Option<trust_types::expanded_function_identity::ExpandedFunctionIdentity>,
    pub source_vc: VerificationCondition,
    pub verification_conditions: Vec<VerificationCondition>,
    pub overflow_checks: bool,
    pub target: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceBodyProof {
    pub vc_index: usize,
    pub public_obligation_id: String,
    pub claim_digest_sha256: String,
    pub vc: VerificationCondition,
    pub evidence: trust_ir::ProofEvidence,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceClauseCertificate {
    pub schema: String,
    pub source: SourceClauseInput,
    pub body_proofs: Vec<SourceBodyProof>,
    pub inferred_returns: InferredReturnProofGraph,
}

/// Identity of the original typed question, independently of its proof.
///
/// The compiler records this from its actual captured source inputs before
/// checking a certificate. Publication must compare the certificate's input
/// projection with that externally bound identity; computing a hash from a
/// presented certificate alone grants no source authority. All source fields,
/// including the complete public context, and every callee body/edge are kept.
/// Proof payloads are excluded so a retained question may acquire a new proof.
pub fn source_clause_input_digest_sha256(
    source: &SourceClauseInput,
    inferred_returns: &InferredReturnProofGraph,
) -> Option<String> {
    if !source_within_depth_gate(source) || !graph_within_depth_gate(inferred_returns) {
        return None;
    }
    crate::on_certify_stack_if_needed(|| source_clause_input_digest_on_stack(source, inferred_returns))
}

fn source_clause_input_digest_on_stack(
    source: &SourceClauseInput,
    inferred_returns: &InferredReturnProofGraph,
) -> Option<String> {
    #[derive(Serialize)]
    struct Node<'a> {
        identity: &'a trust_types::CalleeIdentity,
        function: &'a VerifiableFunction,
        children: &'a [trust_types::CalleeIdentity],
    }
    #[derive(Serialize)]
    struct Input<'a> {
        schema: &'static str,
        source: &'a SourceClauseInput,
        inferred_returns: Vec<Node<'a>>,
    }
    let input = Input {
        schema: "trust.source-clause-input.v1",
        source,
        inferred_returns: inferred_returns
            .nodes
            .iter()
            .map(|node| Node {
                identity: &node.identity,
                function: &node.function,
                children: &node.children,
            })
            .collect(),
    };
    // Direct typed serialization preserves wide integers and the existing
    // deterministic BTreeMap/vector representation; do not pass through Value.
    Some(trust_types::stable_sha256_hex(&serde_json::to_vec(&input).ok()?))
}

/// Only replay can construct this fact; serializing its input is not authority.
#[derive(Debug, Clone)]
pub struct CheckedSourceClauseProof {
    certificate: Arc<SourceClauseCertificate>,
    digest: String,
}

impl CheckedSourceClauseProof {
    pub fn certificate(&self) -> &SourceClauseCertificate {
        &self.certificate
    }
    pub fn digest(&self) -> &str {
        &self.digest
    }
    pub fn proof_strength(&self) -> trust_types::ProofStrength {
        trust_types::ProofStrength::deductive()
    }
    /// Encode the checked fact using the existing canonical artifact envelope.
    pub fn transport_evidence(&self) -> Option<trust_types::TransportProofEvidence> {
        crate::on_certify_stack_if_needed(|| self.transport_evidence_on_stack())
    }

    fn transport_evidence_on_stack(&self) -> Option<trust_types::TransportProofEvidence> {
        let owner = &self.certificate.source.obligation_id;
        let payload = serde_json::to_vec(self.certificate()).ok()?;
        let binding = format!("trust-source-clause:{owner}");
        let (materialization, hash) =
            trust_verifier_api::EvidenceArtifactMaterialization::new_bound(
                trust_verifier_api::EvidenceArtifactKind::ProofCertificate,
                &payload,
                &binding,
                owner,
                vec![],
            )?;
        let proof_id = format!("source-clause:v1:{}", hash.value);
        let artifact = trust_types::TransportEvidenceArtifact {
            kind: "ProofCertificate".into(),
            format: Some(self.certificate.schema.clone()),
            artifact_id: Some(proof_id.clone()),
            digest: Some(trust_types::TransportArtifactDigest {
                algorithm: hash.algorithm,
                value: hash.value.clone(),
            }),
            uri: Some(format!("trust-source-contract://{owner}/certificate/sha256/{}", hash.value)),
            materialization: trust_types::TransportArtifactMaterialization::from_exact_bytes(
                materialization.bytes(),
                binding,
                vec![],
            ),
            metadata: None,
        };
        artifact.materialization.as_ref()?;
        Some(trust_types::TransportProofEvidence {
            suite: "trust-source-contract".into(),
            backend: "checked-body-composition".into(),
            request_id: None,
            proof_id: Some(proof_id),
            native_id: None,
            status: trust_types::TransportProofStatus::Proved,
            strength: Some(self.proof_strength()),
            evidence: Some(trust_types::ProofEvidence::from(self.proof_strength())),
            artifacts: vec![artifact],
            diagnostics: vec![],
        })
    }
}

pub fn replay_source_clause(
    certificate: &SourceClauseCertificate,
) -> Result<CheckedSourceClauseProof, String> {
    // Public replay is also called from small worker/libtest threads. Bundle
    // regeneration normalizes the entire original VC before kernel replay;
    // guarding only the later kernel entry leaves this earlier recursion on
    // the caller's stack. Retained malformed formulas still refuse first.
    if !source_within_depth_gate(&certificate.source)
        || !certificate.body_proofs.iter().all(|body| crate::vc_within_depth_gate(&body.vc))
        || !graph_within_depth_gate(&certificate.inferred_returns)
    {
        return Err("source clause formula exceeds replay depth bound".into());
    }
    crate::on_certify_stack_if_needed(|| Some(replay_source_clause_on_stack(certificate)))
        .ok_or_else(|| "source clause replay worker did not complete".to_string())?
}

fn source_within_depth_gate(source: &SourceClauseInput) -> bool {
    source
        .function
        .preconditions
        .iter()
        .chain(&source.function.postconditions)
        .chain(source.compiler_contracts.typed_propositions.iter().map(|p| &p.formula))
        .all(crate::violation_within_depth_gate)
        && crate::vc_within_depth_gate(&source.source_vc)
        && source.verification_conditions.iter().all(crate::vc_within_depth_gate)
}

/// Older certificates retain the producer's original JSON key order inside
/// typed VC payload text. Compare that one encoding through the shared typed
/// decoder, without changing the retained input, its digest, or any other field.
fn exact_public_context_view<'a>(
    expected: &TrustContractBundle,
    actual: &'a TrustContractBundle,
) -> Result<Cow<'a, TrustContractBundle>, String> {
    if expected == actual {
        return Ok(Cow::Borrowed(actual));
    }
    let mut view = actual.clone();
    for row in &mut view.obligations {
        let mut schemas =
            row.metadata.iter().filter(|entry| entry.key == "trust.vc.formula.schema");
        if schemas.next().map(|entry| entry.value.as_str())
            != Some(trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION)
            || schemas.next().is_some()
        {
            continue;
        }
        for entry in row.metadata.iter_mut().filter(|entry| entry.key == "trust.vc.formula.payload")
        {
            // Decode directly into the existing typed schema first so duplicate
            // typed fields refuse. Keep the original JSON value for comparison:
            // deserializing only the typed value could silently drop extra keys.
            let predicate: trust_verifier_api::TrustSpecPredicate =
                trust_types::json_depth::from_str_deep(&entry.value)
                    .map_err(|error| format!("invalid retained typed VC payload: {error}"))?;
            predicate.validate()?;
            let mut value: serde_json::Value = trust_types::json_depth::from_str_deep(&entry.value)
                .map_err(|error| format!("invalid retained VC JSON: {error}"))?;
            trust_types::canonicalize_json_in_place(&mut value);
            entry.value = trust_types::json_depth::into_string_owned_on_deep_stack(value)
                .map_err(|error| format!("cannot encode retained typed VC payload: {error}"))?;
        }
    }
    if &view != expected {
        return Err("complete public semantic context differs from typed producer".into());
    }
    Ok(Cow::Owned(view))
}

fn replay_source_clause_on_stack(
    certificate: &SourceClauseCertificate,
) -> Result<CheckedSourceClauseProof, String> {
    let source = &certificate.source;
    let source_valid = match (&source.source_text_sha256, &source.expanded_function_identity) {
        (Some(text), None) => {
            certificate.schema == SCHEMA && trust_types::digest::is_stable_sha256_hex(text)
        }
        (None, Some(expanded)) => {
            certificate.schema == EXPANDED_SCHEMA
                && expanded.matches_input(&source.function, &source.compiler_contracts)
                && expanded.function_def_path_hash[0] == source.stable_crate_id
        }
        _ => false,
    };
    if !source_valid {
        return Err("invalid source-clause schema or source text identity".into());
    }
    source.public_bundle.validate()?;
    let expected = trust_source_contract::function_to_verifier_api_bundle_with_compiler_identity(
        &source.function,
        &source.compiler_contracts,
        &source.verification_conditions,
        &source.crate_name,
        source.stable_crate_id,
        source.target_pointer_width_bits,
    );
    let catalog = trust_source_contract::contract_bundle_to_verifier_api_with_compiler_identity(
        &source.function,
        &source.compiler_contracts,
        &source.crate_name,
        source.stable_crate_id,
        source.target_pointer_width_bits,
    );
    // Regeneration can remain structurally complete for a tiny body even
    // after its cooperative budget trips. Completeness is not permission to
    // consume results produced past the original function's bound.
    if trust_types::verify_budget::exhausted_readonly() {
        return Err("source-clause regeneration exceeded the function verification budget".into());
    }
    // No global assumptions, dependencies, publication fields or unselected
    // semantic rows may drift. Routing augmentations need an exact checked
    // projection before they can be admitted here.
    let public_context = exact_public_context_view(&expected, &source.public_bundle)?;
    let original = catalog
        .obligations
        .iter()
        .find(|o| o.obligation_id == source.obligation_id)
        .ok_or("source obligation absent from original typed catalog")?;
    let actual = public_context
        .obligations
        .iter()
        .find(|o| o.obligation_id == source.obligation_id)
        .ok_or("source obligation absent from retained public bundle")?;
    if !trust_source_contract::public_obligation_preserves_source(original, actual) {
        return Err("public source obligation does not preserve original typed claim".into());
    }
    let contract_id = original.contract_id.as_deref().ok_or("source obligation has no contract")?;
    if trust_source_contract::verifier_source_contract_id(
        &source.function,
        &source.compiler_contracts,
        source.source_contract_index,
    )
    .as_deref()
        != Some(contract_id)
    {
        return Err("selected source index differs from the public clause".into());
    }
    let original_contract = catalog
        .contracts
        .iter()
        .find(|c| c.contract_id == contract_id)
        .ok_or("source contract absent")?;
    let actual_contract = public_context
        .contracts
        .iter()
        .find(|c| c.contract_id == contract_id)
        .ok_or("retained source contract absent")?;
    if !trust_source_contract::public_contract_preserves_source(original_contract, actual_contract)
    {
        return Err("public source predicate differs from exact typed query".into());
    }
    let expected_marker = trust_source_contract::boolean_ensures_source_marker(
        &source.function,
        source.source_contract_index,
    )
    .ok_or("source index is not an authored ensures clause")?;
    if serde_json::to_vec(&expected_marker).map_err(|e| e.to_string())?
        != serde_json::to_vec(&source.source_vc).map_err(|e| e.to_string())?
    {
        return Err("source row differs from the complete original authored marker".into());
    }
    let checked_calls = if certificate.inferred_returns.nodes.is_empty() {
        None
    } else {
        Some(replay_inferred_return_graph_on_stack(&certificate.inferred_returns)?)
    };
    let inputs = checked_calls
        .as_ref()
        .map(|calls| calls.inputs_for(&source.function).ok_or("missing exact inferred call fact"))
        .transpose()?;
    let group = trust_source_contract::exact_ensures_body_group(
        &source.function,
        &source.compiler_contracts,
        source.source_contract_index,
        &source.verification_conditions,
        source.target_pointer_width_bits,
        inputs.as_deref(),
    )
    .ok_or("source clause does not match a complete original body-VC group")?;
    // The exact group performs another generation after catalog validation.
    // Apply the same mandatory consumer checkpoint before checking/spending it.
    if trust_types::verify_budget::exhausted_readonly() {
        return Err("source-clause regeneration exceeded the function verification budget".into());
    }
    if group.body_indices().is_empty()
        || certificate.body_proofs.is_empty()
        || group.body_indices().len() != certificate.body_proofs.len()
    {
        return Err("source body proof group is incomplete".into());
    }
    for (index, body) in group.body_indices().iter().zip(&certificate.body_proofs) {
        let original_bytes = serde_json::to_vec(&source.verification_conditions[*index])
            .map_err(|e| e.to_string())?;
        let proof_bytes = serde_json::to_vec(&body.vc).map_err(|e| e.to_string())?;
        if *index != body.vc_index || original_bytes != proof_bytes {
            return Err("body proof differs from its exact generated VC".into());
        }
        let identity = trust_source_contract::verifier_vc_content_identity_with_crate_name(
            &source.function,
            *index,
            &body.vc,
            &source.crate_name,
        );
        if identity.obligation_id != body.public_obligation_id {
            return Err("body proof public identity differs from typed producer".into());
        }
        let original_body = expected
            .obligations
            .iter()
            .find(|o| o.obligation_id == body.public_obligation_id)
            .ok_or("body obligation absent from typed producer")?;
        let actual_body = public_context
            .obligations
            .iter()
            .find(|o| o.obligation_id == body.public_obligation_id)
            .ok_or("body obligation absent from public bundle")?;
        if !trust_source_contract::public_obligation_preserves_source(original_body, actual_body) {
            return Err("public body obligation differs from its original VC".into());
        }
        let digest = trust_types::original_vc_snapshot::exact_vc_claim_digest_sha256(
            &body.vc,
            source.overflow_checks,
            Some(&source.target),
        )
        .ok_or("body VC has no canonical claim identity")?;
        if digest != body.claim_digest_sha256
            || !crate::replay_presented_vc_evidence(&body.vc, &body.evidence)
        {
            return Err("body certificate or claim digest refused".into());
        }
    }
    let bytes = serde_json::to_vec(certificate).map_err(|e| e.to_string())?;
    Ok(CheckedSourceClauseProof {
        certificate: Arc::new(certificate.clone()),
        digest: trust_types::stable_sha256_hex(&bytes),
    })
}
