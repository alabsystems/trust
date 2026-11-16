//! Exact public metadata correspondence before compiler-owned monitor attachment.
//! This pure match grants no authority: the compiler independently requires
//! its live kernel-checked record and an exact fresh reference.
use crate::{
    TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY,
    TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY, TRUST_SOURCE_DIGEST_METADATA_KEY,
};
const TRUST_MONITOR_STATUS_METADATA_KEY: &str = "trust.monitor.status";
const TRUST_MONITOR_REASON_METADATA_KEY: &str = "trust.monitor.reason";
const TRUST_MONITOR_PREDICATE_DIGEST_METADATA_KEY: &str = "trust.monitor.predicate_digest";
const TRUST_CONTRACT_LOWERING_METADATA_KEY: &str = "trust.contract.lowering";
fn exactly_one_metadata_value<'a>(
    entries: &'a [trust_verifier_api::MetadataEntry],
    key: &str,
) -> Option<&'a str> {
    let mut values = entries.iter().filter(|entry| entry.key == key);
    let value = values.next()?;
    values.next().is_none().then_some(value.value.as_str())
}
fn canonical_sha256_hex_segment(value: &str) -> bool {
    value.len() == 64
        && value.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}
/// Check only source metadata correspondence, not proof or monitor authority.
pub fn source_monitor_metadata_matches_contract(
    contract: &trust_verifier_api::TrustContract,
    obligation: &trust_verifier_api::TrustObligation,
) -> bool {
    use trust_verifier_api::{ContractKind, ObligationKind};

    if obligation.contract_id.as_deref() != Some(contract.contract_id.as_str())
        || !matches!(
            (&contract.kind, &obligation.kind),
            (ContractKind::Requires, ObligationKind::Precondition)
                | (ContractKind::Ensures, ObligationKind::Postcondition)
                | (ContractKind::Invariant, ObligationKind::Invariant)
                | (ContractKind::LoopInvariant, ObligationKind::LoopInvariant)
                | (ContractKind::Asserts, ObligationKind::Assertion | ObligationKind::Termination)
                | (ContractKind::Refinement, ObligationKind::Refinement)
                | (
                    ContractKind::Temporal,
                    ObligationKind::TemporalSafety | ObligationKind::Liveness
                )
        )
    {
        return false;
    }
    let contract_digest = exactly_one_metadata_value(
        &contract.metadata,
        TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY,
    );
    let obligation_digest = exactly_one_metadata_value(
        &obligation.metadata,
        TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY,
    );
    let contract_typed_proposition = exactly_one_metadata_value(
        &contract.metadata,
        TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY,
    );
    let obligation_typed_proposition = exactly_one_metadata_value(
        &obligation.metadata,
        TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY,
    );
    let contract_lowering =
        exactly_one_metadata_value(&contract.metadata, TRUST_CONTRACT_LOWERING_METADATA_KEY);
    let obligation_lowering =
        exactly_one_metadata_value(&obligation.metadata, TRUST_CONTRACT_LOWERING_METADATA_KEY);
    let mut metadata_keys = std::collections::BTreeSet::new();
    let unique_obligation_metadata =
        obligation.metadata.iter().all(|entry| metadata_keys.insert(entry.key.as_str()));
    // Absence is permitted for legacy untyped source rows. Ambiguity is not
    // absence: a duplicated optional field must not become None == None.
    let unique_contract_typed_proposition = contract
        .metadata
        .iter()
        .filter(|entry| entry.key == TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY)
        .count()
        <= 1;
    contract_digest == obligation_digest
        && contract_digest.is_some_and(canonical_sha256_hex_segment)
        && contract_typed_proposition == obligation_typed_proposition
        && contract_typed_proposition.is_none_or(|digest| {
            digest.strip_prefix("sha256:").is_some_and(canonical_sha256_hex_segment)
        })
        && exactly_one_metadata_value(&contract.metadata, TRUST_SOURCE_DIGEST_METADATA_KEY)
            == exactly_one_metadata_value(&obligation.metadata, TRUST_SOURCE_DIGEST_METADATA_KEY)
        && exactly_one_metadata_value(&contract.metadata, TRUST_SOURCE_DIGEST_METADATA_KEY)
            .is_some_and(canonical_sha256_hex_segment)
        && contract_lowering == obligation_lowering
        && contract_lowering.is_some_and(|lowering| !lowering.trim().is_empty())
        && unique_obligation_metadata
        && unique_contract_typed_proposition
        && obligation.metadata.iter().all(|entry| {
            matches!(
                entry.key.as_str(),
                trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY
                    | TRUST_CONTRACT_LOWERING_METADATA_KEY
                    | TRUST_SOURCE_DIGEST_METADATA_KEY
                    | TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY
                    | TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY
                    | TRUST_MONITOR_STATUS_METADATA_KEY
                    | TRUST_MONITOR_REASON_METADATA_KEY
                    | TRUST_MONITOR_PREDICATE_DIGEST_METADATA_KEY
            )
        })
}
