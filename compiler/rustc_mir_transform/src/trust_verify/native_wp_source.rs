//! Carry authored postcondition bindings from the existing query/HIR model.

use trust_thir_lower::contract_carry::{
    ClauseContext, ClauseRole, ContractBodyRecord, carry_clause,
};

use super::*;

const RAW_POSTCONDITION: &str = "trust.ir.raw-source-postcondition.v1";

/// The carry's path is crate-relative. Bind its source query to the extractor's
/// qualified identity using the same actual DefId, without reconstructing a name.
pub(super) struct CapturedSource {
    pub(super) function_path: String,
    pub(super) body: ContractBodyRecord,
}

pub(super) fn capture(
    tcx: TyCtxt<'_>,
    owner: rustc_span::def_id::LocalDefId,
    ir_param_count: Option<u32>,
) -> Option<CapturedSource> {
    let body = trust_thir_lower::contract_carry::capture_contract_body(tcx, owner, ir_param_count)?;
    Some(CapturedSource {
        function_path: trust_mir_extract::safe_def_path_str(tcx, owner.to_def_id()),
        body,
    })
}

pub(super) fn is_query_bound(obligation: &trust_verifier_api::TrustObligation) -> bool {
    obligation.kind == trust_verifier_api::ObligationKind::Postcondition
        && exactly_one_metadata_value(&obligation.metadata, RAW_POSTCONDITION)
            == Some("query-bound")
}

/// Compiler-private projection of an independently checked native WP fact.
/// Its constructor is the exact-input check in `apply_authorities` below.
#[derive(Debug, Clone)]
pub(super) struct Authority {
    row: ExactResultRowIdentity,
    binding: ResultObligationBinding,
    result: ExactLiveCompilerProvedResult,
    evidence_id: String,
    evidence_digest: String,
    _proof: trust_router::full_verification::CheckedNativeWpProof,
}

impl Authority {
    pub(super) fn matches_row(
        &self,
        index: usize,
        vc: &VerificationCondition,
        binding: Option<&ResultObligationBinding>,
    ) -> bool {
        exact_result_row_identity(index, vc).as_ref() == Some(&self.row)
            && binding == Some(&self.binding)
    }

    pub(super) fn matches_result(&self, result: &VerificationResult) -> bool {
        self.result.matches(result)
    }

    pub(super) fn evidence_id(&self) -> &str {
        &self.evidence_id
    }

    pub(super) fn bind_transport_identity(&self, transport: &mut TransportObligationResult) {
        let request = self._proof.native_request_id();
        let proof = self._proof.native_proof_id();
        let native_id = native_trust_ir_proof_unit_id("trust-wp", request, proof);
        if let Some(native) = &mut transport.native_trust_ir {
            native.suite = "trust-wp".into();
            native.backend = "trust-wp".into();
            native.request_id = Some(request.to_string());
            native.native_id = Some(native_id.clone());
        }
        if let Some(evidence) = &mut transport.proof_evidence {
            evidence.suite = "trust-wp".into();
            evidence.backend = "trust-wp".into();
            evidence.request_id = Some(request.to_string());
            evidence.proof_id = Some(proof.to_string());
            evidence.native_id = Some(native_id);
        }
    }

    pub(super) fn matches_evidence(
        &self,
        evidence: &trust_verifier_api::ObligationEvidence,
    ) -> bool {
        evidence.obligation_id == self.binding.public_obligation_id
            && serde_json::to_vec(evidence).is_ok_and(|bytes| {
                domain_length_bound_sha256_hex("trust.native-wp.accepted-evidence.v1", &bytes)
                    == self.evidence_digest
            })
    }
}

/// Spend the checked proof after generic catalog-placeholder resets. Neither
/// a public `Proved` label nor the placeholder's Boolean formula grants entry.
pub(super) fn apply_authorities(
    bundle: &trust_verifier_api::TrustContractBundle,
    native: Option<&trust_ir_bridge::NativeVerificationBundle>,
    run: &trust_verifier_api::VerificationRunResult,
    facts: Option<&BTreeMap<String, trust_router::full_verification::CheckedNativeWpProof>>,
    results: &mut [(VerificationCondition, VerificationResult)],
    bindings: &[Option<ResultObligationBinding>],
    authorities: &mut [Option<ResultProofAuthority>],
) -> usize {
    // Every invocation reconstructs this authority family from the supplied
    // facts. A missing/changed fact set must not leave an old token available
    // for a later generic result promotion, even if its row was moved.
    for (index, authority) in authorities.iter_mut().enumerate() {
        if matches!(authority, Some(ResultProofAuthority::NativeWpSource { .. })) {
            *authority = None;
            if let Some((_, result)) = results.get_mut(index)
                && matches!(
                    result,
                    VerificationResult::Proved { .. } | VerificationResult::Unknown { .. }
                )
            {
                *result = exact_source_clause_pending_result();
            }
        }
    }
    let (Some(native), Some(facts)) = (native, facts) else { return 0 };
    if results.len() != bindings.len() || results.len() != authorities.len() {
        return 0;
    }
    let mut applied = 0;
    for (index, ((vc, result), binding)) in results.iter_mut().zip(bindings).enumerate() {
        if !matches!(result, VerificationResult::Unknown { .. } | VerificationResult::Proved { .. })
        {
            continue;
        }
        let Some(binding) = binding.as_ref() else { continue };
        if authorities[index].as_ref().is_some_and(|authority| {
            authority.is_static_proof_for(index, vc, result, Some(binding))
                && !matches!(authority, ResultProofAuthority::ExactSourceClauseDischarge { .. })
        }) {
            continue;
        }
        let obligation = &binding.canonical_obligation;
        if !binding.matches_row(index, vc)
            || exactly_one_metadata_value(&obligation.metadata, RAW_POSTCONDITION)
                != Some("query-bound")
            || source_clause_marker_identity(bundle, obligation).is_none()
        {
            continue;
        }
        let Some(fact) = facts.get(&obligation.obligation_id) else { continue };
        let mut evidence = run
            .evidence
            .iter()
            .filter(|evidence| evidence.obligation_id == obligation.obligation_id);
        let Some(evidence_row) = evidence.next() else { continue };
        if evidence.next().is_some()
            || evidence_row.status != trust_verifier_api::EvidenceStatus::Proved
            || evidence_row.proof_strength.as_ref() != Some(&fact.proof_strength())
            || !fact.matches(bundle, native, obligation, evidence_row)
        {
            continue;
        }
        let proved = legacy_result_from_api_evidence(evidence_row);
        let Some(snapshot) = ExactLiveCompilerProvedResult::from_result(&proved) else { continue };
        let Some(row) = exact_result_row_identity(index, vc) else { continue };
        let Ok(bytes) = serde_json::to_vec(evidence_row) else { continue };
        *result = proved;
        authorities[index] = Some(ResultProofAuthority::NativeWpSource {
            authority: Authority {
                row,
                binding: binding.clone(),
                result: snapshot,
                _proof: fact.clone(),
                evidence_id: evidence_row.evidence_id.clone(),
                evidence_digest: domain_length_bound_sha256_hex(
                    "trust.native-wp.accepted-evidence.v1",
                    &bytes,
                ),
            },
        });
        applied += 1;
    }
    applied
}

/// This runs before native identities are minted. Actual return-VC records are
/// untouched: only their separate authored source catalog row is preserved as
/// a positive postcondition rather than re-encoded as a violation formula.
pub(super) fn attach(
    module: &trust_ir::Module,
    func: &trust_types::VerifiableFunction,
    bundle: &mut trust_verifier_api::TrustContractBundle,
    source: Option<&CapturedSource>,
) -> Result<(), String> {
    let Some(captured) = source else { return Ok(()) };
    let source = &captured.body;
    if captured.function_path != func.def_path
        || source.binding_refusal.is_some()
        || source.refusal.is_some()
    {
        return Ok(());
    }
    let function_id = native_trust_ir_function_id(module, func)?;
    let function = module.function_by_id(function_id).ok_or("missing authored-contract body")?;
    let signature = module.func_type(function.ty).ok_or("missing authored-contract signature")?;
    if source.ir_param_count != u32::try_from(signature.params.len()).ok() {
        return Ok(());
    }
    let context = ClauseContext {
        params: &source.params,
        binding_refusal: source.binding_refusal,
        param_tys: &signature.params,
        return_tys: &signature.returns,
        pointer_bits: None,
        header: None,
    };
    let mut updates = Vec::new();
    for (index, obligation) in bundle.obligations.iter().enumerate() {
        if exactly_one_obligation_context(obligation)
            .and_then(|context| context.function)
            .is_none_or(|function| function.path != func.def_path)
        {
            continue;
        }
        let Some(identity) = source_clause_marker_identity(bundle, obligation) else { continue };
        if identity.kind != SourceClauseKind::Ensures {
            continue;
        }
        let mut clauses = source.clauses.iter().filter(|clause| {
            clause.role == ClauseRole::Ensures && clause.ordinal as usize == identity.index
        });
        let Some(clause) = clauses.next() else { continue };
        if clauses.next().is_some() {
            continue;
        }
        let Some(contract_index) = bundle
            .contracts
            .iter()
            .position(|contract| contract.contract_id == identity.contract_id)
        else {
            continue;
        };
        let contract = &bundle.contracts[contract_index];
        let Ok(statement) =
            canonical_monitor_static_proposition(TrustContractKind::Ensures, &clause.predicate)
        else {
            continue;
        };
        let digest = trust_types::typed_contract_proposition_digest(
            &statement.formula,
            &statement.variable_domains,
        );
        // The public source record must be the exact indexed compiler query
        // clause. The source span or an inferred display name is insufficient.
        if exactly_one_metadata_value(
            &contract.metadata,
            TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY,
        ) != Some(digest.as_str())
            || exactly_one_metadata_value(
                &obligation.metadata,
                TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY,
            ) != Some(digest.as_str())
        {
            continue;
        }
        // Digest metadata alone cannot authenticate the actual public claim:
        // the predicate may have changed while its old metadata was retained.
        // Reuse the original emitter on this query-owned proposition, rather
        // than adding a second public-formula decoder.
        let Some(source_contract) = func.contracts.get(identity.index) else { continue };
        let rustc_middle::mir::trust_contract::TrustContractPredicateKind::Typed { text, .. } =
            &clause.predicate
        else {
            continue;
        };
        if source_contract.kind != trust_types::ContractKind::Ensures
            || source_contract.body != text.as_str()
        {
            continue;
        }
        let expected_source =
            trust_types::CompilerContractBundle::new(vec![source_contract.clone()])
                .with_typed_propositions(vec![trust_types::CompilerContractProposition {
                    source_contract_index: 0,
                    kind: source_contract.kind,
                    body: source_contract.body.clone(),
                    formula: statement.formula.clone(),
                    variable_domains: statement.variable_domains.clone(),
                }]);
        // Trust: Reuse the query-only projection that the direct producer also consumes.
        let Some((expected_predicate, _, _)) =
            trust_source_contract::compiler_typed_contract_predicate(&expected_source, 0)
        else {
            continue;
        };
        if expected_predicate != contract.predicate {
            continue;
        }
        let carried = carry_clause(clause, &context);
        if carried.opaque_reason.is_some() {
            continue;
        }
        // Preserve the exact query names. In particular, the compiler's
        // public TrustSpec retains `_0` as a variable; it is not the codec's
        // distinct explicit-result node.
        let bindings = carried.formula.bindings;
        let names = bindings.iter().map(|(name, _)| name).collect::<BTreeSet<_>>();
        if names.len() != bindings.len() {
            continue;
        }
        let encoded = serde_json::to_string(&bindings).map_err(|error| error.to_string())?;
        updates.push((index, contract_index, encoded));
    }
    for (index, contract_index, encoded) in updates {
        let obligation = &mut bundle.obligations[index];
        obligation.metadata.retain(|entry| !body_violation_metadata(&entry.key));
        set_obligation_metadata(obligation, RAW_POSTCONDITION, "query-bound".into());
        let metadata = &mut bundle.contracts[contract_index].metadata;
        metadata
            .retain(|entry| entry.key != trust_verifier_api::TRUST_IR_CLAUSE_BINDINGS_METADATA_KEY);
        metadata.push(trust_verifier_api::MetadataEntry {
            key: trust_verifier_api::TRUST_IR_CLAUSE_BINDINGS_METADATA_KEY.into(),
            value: encoded,
        });
    }
    Ok(())
}

fn body_violation_metadata(key: &str) -> bool {
    matches!(
        key,
        "trust.contract.body_vcs.formula.v1"
            | "trust.vc.digest.sha256"
            | "trust.vc.formula.schema"
            | "trust.vc.formula.sort"
            | "trust.vc.formula.smtlib2"
            | "trust.vc.formula.payload"
            | "trust.vc.formula.pruned"
            | "trust.vc.formula.payload.dropped_bytes"
            | "trust.vc.formula.smtlib2.omitted_bytes"
    )
}

pub(super) fn formula(
    contracts: &[trust_verifier_api::TrustContract],
    obligation: &trust_verifier_api::TrustObligation,
) -> Result<Option<trust_ir::ProofFormula>, String> {
    if !is_query_bound(obligation) {
        return Ok(None);
    }
    let contract = contracts
        .iter()
        .find(|contract| Some(&contract.contract_id) == obligation.contract_id.as_ref())
        .ok_or("query-bound postcondition lost its public source contract")?;
    let predicate =
        trust_verifier_api::TrustSpecPredicate::from_contract_predicate(&contract.predicate)
            .map_err(|error| error.to_string())?
            .ok_or("query-bound postcondition has no typed public predicate")?;
    let Ok(mut formula) =
        trust_router::full_verification::trust_wp_native_formula_from_trust_spec(&predicate)
    else {
        return Ok(None);
    };
    let encoded = exactly_one_metadata_value(
        &contract.metadata,
        trust_verifier_api::TRUST_IR_CLAUSE_BINDINGS_METADATA_KEY,
    )
    .ok_or("query-bound postcondition lost its clause bindings")?;
    formula.bindings = serde_json::from_str(encoded).map_err(|error| error.to_string())?;
    Ok(Some(formula))
}
