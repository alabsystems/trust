//! Native WP questions over a staged direct-contract clone, never source authority.
//!
//! The source producer supplies its query-owned public inventory and the exact
//! installed proof-row correspondence. This boundary reuses the public formula
//! codec, clause bindings and native request planner; it decodes no Rust/MIR.

use std::collections::{BTreeMap, BTreeSet};

use trust_ir::{
    Module, ProofDigest, ProofId, ProofObligationSourceRange, PublicObligationIdentity,
};
use trust_verifier_api::{
    ContractKind, ObligationKind, TRUST_IR_CLAUSE_BINDINGS_METADATA_KEY, TrustContractBundle,
    TrustSpecPredicate,
};

use crate::native_shadow_request::{
    DirectShadowBundle, DirectShadowContractClaim, direct_shadow_bundle_with_contract_claims,
};

/// Immutable images emitted together from one compiler query. Serialized
/// copies remain candidate data and convey no source-generation authority.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct DirectContractShadowQuestion {
    pub proof_id: ProofId,
    pub public_obligation_id: String,
    pub assertion_id: String,
    pub carried_clause: trust_ir::ProofFormula,
    pub public_semantic_digest: String,
}

/// Construct diagnostic questions from the direct producer's staged contract
/// rows. Each pair names a proof id and one exact public postcondition id.
/// Every public row and every installed contract row must be accounted for.
/// The caller must retain the returned shadow disclosure; its results cannot
/// authorize compiler rows, source fidelity, codegen or certificate promotion.
pub fn direct_contract_shadow_verification_bundle(
    module: Module,
    public: &TrustContractBundle,
    bindings: &[DirectContractShadowQuestion],
) -> Result<DirectShadowBundle, String> {
    let errors = trust_ir_build::validate_module(&module);
    if !errors.is_empty() {
        return Err(format!("direct contract shadow refuses an invalid staged module: {errors:?}"));
    }
    public.validate()?;
    if bindings.is_empty() || bindings.len() != public.obligations.len() {
        return Err("direct contract shadow requires the complete nonempty public inventory".into());
    }
    let mut claims = BTreeMap::new();
    let mut public_ids = BTreeSet::new();
    for question in bindings {
        let proof_id = &question.proof_id;
        let public_id = &question.public_obligation_id;
        if !public_ids.insert(public_id) || claims.contains_key(proof_id) {
            return Err("direct contract shadow has duplicate proof/public correspondence".into());
        }
        let row = module
            .proof_obligations
            .iter()
            .find(|row| row.id == *proof_id)
            .ok_or("direct contract shadow names a missing proof row")?;
        let source = row.source.as_ref().ok_or("direct contract row has no source identity")?;
        if source.source_id != "trust-thir-lower/contract@1"
            || row.kind != trust_ir::ObligationKind::Postcondition
            || row.status != trust_ir::ProofStatus::Pending
            || source.public.is_some()
        {
            return Err(
                "direct contract shadow requires an unenriched Pending authored postcondition"
                    .into(),
            );
        }
        let carried = row.formula.as_ref().ok_or("direct contract row has no carried clause")?;
        if carried.schema != "trust.contract-clause@1"
            || carried != &question.carried_clause
            || source.assertion_id != question.assertion_id
        {
            return Err("direct contract shadow refuses opaque or foreign carried clauses".into());
        }
        let obligation = public
            .obligations
            .iter()
            .find(|row| row.obligation_id == *public_id)
            .ok_or("direct contract shadow has no matching public obligation")?;
        if obligation.kind != ObligationKind::Postcondition || !obligation.summary_facts.is_empty()
        {
            return Err(
                "direct contract shadow accepts postconditions without imported premises".into()
            );
        }
        let contract = public
            .contracts
            .iter()
            .find(|contract| obligation.contract_id.as_ref() == Some(&contract.contract_id))
            .ok_or("direct contract shadow has no matching authored contract")?;
        if contract.kind != ContractKind::Ensures {
            return Err("direct contract shadow requires an authored ensures clause".into());
        }
        let encoded: Vec<_> = contract
            .metadata
            .iter()
            .filter(|entry| entry.key == TRUST_IR_CLAUSE_BINDINGS_METADATA_KEY)
            .collect();
        if encoded.len() != 1 {
            return Err("direct contract shadow requires one exact clause-binding table".into());
        }
        let clause_bindings: Vec<(String, trust_ir::proof::ClauseBinding)> =
            serde_json::from_str(&encoded[0].value).map_err(|error| error.to_string())?;
        if clause_bindings != carried.bindings {
            return Err("direct contract shadow public/installed clause bindings differ".into());
        }
        let predicate = TrustSpecPredicate::from_contract_predicate(&contract.predicate)
            .map_err(|error| error.to_string())?
            .ok_or("direct contract shadow requires the original typed public predicate")?;
        let payload = trust_verifier_api::trust_spec_native_formula::
            trust_spec_predicate_to_trust_formula_payload(&predicate)?;
        let mut formula = trust_ir::ProofFormula::new("trust_wp.trust-formula.v1", payload);
        formula.bindings = clause_bindings;
        let digest = public.canonical_obligation_semantic_digest_sha256(obligation)?;
        if digest != question.public_semantic_digest {
            return Err("direct contract shadow public question changed after query capture".into());
        }
        let bytes = (0..32)
            .map(|index| u8::from_str_radix(&digest[index * 2..index * 2 + 2], 16))
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| error.to_string())?;
        let file =
            obligation.source.file.as_ref().ok_or("direct contract has no query source file")?;
        let range = ProofObligationSourceRange {
            file: u32::try_from(
                module
                    .files
                    .iter()
                    .position(|entry| entry == file)
                    .ok_or("query source file is absent from the direct module")?,
            )
            .map_err(|_| "query file index exceeds u32")?,
            start_line: obligation.source.line.ok_or("direct contract has no query source line")?,
            start_col: obligation
                .source
                .column
                .ok_or("direct contract has no query source column")?,
            end_line: obligation
                .source
                .end_line
                .ok_or("direct contract has no query source end line")?,
            end_col: obligation
                .source
                .end_column
                .ok_or("direct contract has no query source end column")?,
        };
        claims.insert(
            *proof_id,
            DirectShadowContractClaim {
                public: PublicObligationIdentity {
                    obligation_id: public_id.clone(),
                    semantic_digest: ProofDigest::sha256(
                        bytes.try_into().map_err(|_| "canonical digest must decode to 32 bytes")?,
                    ),
                },
                formula,
                range,
            },
        );
    }
    let installed = module
        .proof_obligations
        .iter()
        .filter(|row| {
            row.source
                .as_ref()
                .is_some_and(|source| source.source_id == "trust-thir-lower/contract@1")
        })
        .count();
    if installed != claims.len() {
        return Err("direct contract shadow refuses unaccounted installed contract rows".into());
    }
    direct_shadow_bundle_with_contract_claims(module, &claims).map_err(|error| error.to_string())
}

#[cfg(test)]
#[path = "direct_contract_shadow_tests.rs"]
mod tests;
