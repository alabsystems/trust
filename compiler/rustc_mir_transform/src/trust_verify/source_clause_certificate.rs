//! Trust: publish the existing source-clause derivation only with a checked,
//! self-contained source/body/callee proof graph. No additional authority class.

use trust_certify::source_clause_proof::{
    CheckedSourceClauseProof, SourceBodyProof, SourceClauseCertificate, SourceClauseInput,
};

use super::*;

/// Live compiler capture and its checked proof stay separate: the input
/// identity is measured before replay, never recovered from a proof artifact.
#[derive(Clone, Debug)]
pub(super) struct Publication {
    proof: CheckedSourceClauseProof,
    typed_input_digest: String,
    expanded_function_identity:
        Option<trust_types::expanded_function_identity::ExpandedFunctionIdentity>,
}

impl Publication {
    pub(super) fn expanded_function_identity(
        &self,
    ) -> Option<&trust_types::expanded_function_identity::ExpandedFunctionIdentity> {
        self.expanded_function_identity.as_ref()
    }
    pub(super) fn typed_input_digest(&self) -> &str {
        &self.typed_input_digest
    }
}

fn clear_attachments(authorities: &mut [Option<ResultProofAuthority>]) {
    for authority in authorities {
        if let Some(ResultProofAuthority::ExactSourceClauseDischarge { certificate, .. }) =
            authority
        {
            *certificate = None;
        }
    }
}

pub(super) fn attach(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    function: &trust_types::VerifiableFunction,
    contracts: &trust_types::CompilerContractBundle,
    bundle: &trust_verifier_api::TrustContractBundle,
    source_question_bundle: Option<&trust_verifier_api::TrustContractBundle>,
    vcs: &[VerificationCondition],
    results: &[(VerificationCondition, VerificationResult)],
    bindings: &[Option<ResultObligationBinding>],
    authorities: &mut [Option<ResultProofAuthority>],
) {
    // Inputs disappearing or changing cannot retain an earlier publication
    // fact. The underlying exact-group authority is separately reconstructed.
    clear_attachments(authorities);
    let Some(source_question_bundle) = source_question_bundle else { return };
    if !authorities.iter().any(|authority| {
        matches!(authority, Some(ResultProofAuthority::ExactSourceClauseDischarge { .. }))
    }) {
        return;
    }
    let Some(owner) = body.source.def_id().as_local() else { return };
    let source_text_sha256 = transport_function_source_digest(tcx, owner);
    let expanded_function_identity =
        expanded_function_identity::capture(tcx, owner, function, contracts);
    if source_text_sha256.is_none() == expanded_function_identity.is_none() {
        return;
    }
    let Some(graph) = inferred_return::proof_graph_for(tcx, function) else { return };
    let target = verification_target_key(tcx.sess);
    let mut updates = Vec::new();
    for (index, authority) in authorities.iter().enumerate() {
        let Some(ResultProofAuthority::ExactSourceClauseDischarge { binding, body_proofs, .. }) =
            authority
        else {
            continue;
        };
        let Some((source_vc, _)) = results.get(index) else { continue };
        let Some(source_identity) =
            source_clause_marker_identity(bundle, &binding.canonical_obligation)
        else {
            continue;
        };
        if source_identity.kind != SourceClauseKind::Ensures {
            continue;
        }
        if !selected_source_preserved(source_question_bundle, bundle, &binding.public_obligation_id)
        {
            continue;
        }
        let proofs = body_proofs
            .iter()
            .map(|proof| {
                let body_index = proof.row.index;
                let (body_vc, _) = results.get(body_index)?;
                let body_binding = bindings.get(body_index)?.as_ref()?;
                let evidence = authorities
                    .get(body_index)?
                    .as_ref()?
                    .kernel_evidence_for(body_index, body_vc, Some(body_binding))?
                    .clone();
                let mut original = vcs.iter().enumerate().filter(|(_, vc)| {
                    serde_json::to_vec(vc).ok() == serde_json::to_vec(body_vc).ok()
                });
                let (vc_index, vc) = original.next()?;
                if original.next().is_some() {
                    return None;
                }
                Some(SourceBodyProof {
                    vc_index,
                    public_obligation_id: proof.public_obligation_id.clone(),
                    claim_digest_sha256:
                        trust_types::original_vc_snapshot::exact_vc_claim_digest_sha256(
                            vc,
                            tcx.sess.overflow_checks(),
                            Some(&target),
                        )?,
                    vc: vc.clone(),
                    evidence,
                })
            })
            .collect::<Option<Vec<_>>>();
        let Some(mut proofs) = proofs else { continue };
        proofs.sort_by_key(|proof| proof.vc_index);
        let source = SourceClauseInput {
            function: function.clone(),
            compiler_contracts: contracts.clone(),
            public_bundle: source_question_bundle.clone(),
            obligation_id: binding.public_obligation_id.clone(),
            source_contract_index: source_identity.index,
            stable_crate_id: tcx.stable_crate_id(body.source.def_id().krate).as_u64(),
            crate_name: tcx.crate_name(body.source.def_id().krate).to_string(),
            target_pointer_width_bits: monitor_target_pointer_width(tcx).ok().map(|w| w.bits()),
            source_text_sha256: source_text_sha256.clone(),
            expanded_function_identity: expanded_function_identity.clone(),
            source_vc: source_vc.clone(),
            verification_conditions: vcs.to_vec(),
            overflow_checks: tcx.sess.overflow_checks(),
            target: target.clone(),
        };
        let Some(typed_input_digest) =
            trust_certify::source_clause_proof::source_clause_input_digest_sha256(&source, &graph)
        else {
            continue;
        };
        let certificate = SourceClauseCertificate {
            schema: if expanded_function_identity.is_some() {
                trust_certify::source_clause_proof::EXPANDED_SCHEMA
            } else {
                trust_certify::source_clause_proof::SCHEMA
            }
            .into(),
            source,
            body_proofs: proofs,
            inferred_returns: graph.clone(),
        };
        match trust_certify::source_clause_proof::replay_source_clause(&certificate) {
            Ok(proof) => updates.push((
                index,
                Publication {
                    proof,
                    typed_input_digest,
                    expanded_function_identity: expanded_function_identity.clone(),
                },
            )),
            Err(reason) => debug!(
                "Trust: source clause {} remains unpublishable: {}",
                binding.public_obligation_id, reason
            ),
        }
    }
    for (index, proof) in updates {
        if let Some(ResultProofAuthority::ExactSourceClauseDischarge { certificate, .. }) =
            authorities[index].as_mut()
        {
            *certificate = Some(proof);
        }
    }
}

fn selected_source_preserved(
    original: &trust_verifier_api::TrustContractBundle,
    routed: &trust_verifier_api::TrustContractBundle,
    owner: &str,
) -> bool {
    if original.bundle_id != routed.bundle_id || original.subject != routed.subject {
        return false;
    }
    let unique_obligation = |bundle: &trust_verifier_api::TrustContractBundle| {
        let mut rows = bundle.obligations.iter().filter(|row| row.obligation_id == owner);
        let row = rows.next()?;
        rows.next().is_none().then_some(row.clone())
    };
    let (Some(before), Some(after)) = (unique_obligation(original), unique_obligation(routed))
    else {
        return false;
    };
    if !trust_source_contract::public_obligation_preserves_source(&before, &after) {
        return false;
    }
    let Some(contract_id) = before.contract_id else { return false };
    let unique_contract = |bundle: &trust_verifier_api::TrustContractBundle| {
        let mut rows = bundle.contracts.iter().filter(|row| row.contract_id == contract_id);
        let row = rows.next()?;
        rows.next().is_none().then_some(row.clone())
    };
    let (Some(before), Some(after)) = (unique_contract(original), unique_contract(routed)) else {
        return false;
    };
    trust_source_contract::public_contract_preserves_source(&before, &after)
}

pub(super) fn transport(publication: &Publication) -> Option<TransportProofEvidence> {
    publication.proof.transport_evidence()
}

// Trust: out-of-line unit tests, as tidy's `unit_tests` check requires.
#[cfg(test)]
mod tests;
