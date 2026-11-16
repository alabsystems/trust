//! Correspondence for non-proving body declines and their authored question.
//!
//! This is data binding, not proof, freshness, or monitor authority. The
//! compiler must additionally authenticate the complete current fresh carrier
//! and its independent kernel-checked monitor record before using it.

use serde::Serialize;

use super::*;

pub const SOURCE_BODY_DECLINE_METADATA_KEY: &str = "trust.vc.source_body_decline.v1";
pub const SOURCE_BODY_DECLINE_ROLE: &str = "postcondition_body_declined";
const SCHEMA: &str = "trust.source-body-decline.v1";

/// Exact canonical source proposition selected for a fresh decline claim.
/// This borrowed correspondence cannot be deserialized as an authority token.
#[derive(Debug)]
pub struct ValidatedSourceBodyDecline<'a> {
    source_contract_index: usize,
    cause: trust_types::ContractBodyDeclineCause,
    contract: &'a Contract,
    proposition: &'a trust_types::CompilerContractProposition,
}

impl ValidatedSourceBodyDecline<'_> {
    pub fn source_contract_index(&self) -> usize {
        self.source_contract_index
    }
    pub fn cause(&self) -> trust_types::ContractBodyDeclineCause {
        self.cause
    }
    pub fn contract(&self) -> &Contract {
        self.contract
    }
    pub fn proposition(&self) -> &trust_types::CompilerContractProposition {
        self.proposition
    }
}

/// Check source correspondence only. The caller must own and seal the fresh
/// producer output; a submitted or serialized VC is not freshness authority.
pub fn validated_source_body_decline<'a>(
    function: &'a VerifiableFunction,
    compiler_contracts: &'a CompilerContractBundle,
    vc: &VerificationCondition,
) -> Option<ValidatedSourceBodyDecline<'a>> {
    let decline = vc.kind.declined_contract_body()?;
    match decline.cause {
        trust_types::ContractBodyDeclineCause::UnconstrainedReturnCall => {}
    }
    let metadata = vc.contract_metadata?;
    if !metadata.has_ensures
        || metadata.source_contract_index != Some(decline.source_contract_index)
        || vc.formula != Formula::Bool(true)
        || vc.obligation.is_some()
        || (vc.function.as_str() != function.name && vc.function.as_str() != function.def_path)
    {
        return None;
    }
    let contract =
        canonical_source_contract(function, compiler_contracts, decline.source_contract_index)?;
    if contract.kind != TrustTypesContractKind::Ensures {
        return None;
    }
    let proposition =
        compiler_contracts.typed_proposition(decline.source_contract_index, contract)?;
    if proposition.formula != decline.source_predicate
        || !proposition.variable_domains.iter().any(|domain| domain.name == "_0")
        || !source_domains_match_declared_scalars(function, &proposition.variable_domains)
    {
        return None;
    }
    Some(ValidatedSourceBodyDecline {
        source_contract_index: decline.source_contract_index,
        cause: decline.cause,
        contract,
        proposition,
    })
}

fn source_domains_match_declared_scalars(
    function: &VerifiableFunction,
    domains: &[trust_types::CompilerContractVariableDomain],
) -> bool {
    use trust_types::CompilerContractValueDomain as Domain;
    domains.iter().all(|domain| {
        let mut locals = function.body.locals.iter().filter(|local| {
            if domain.name == "_0" {
                return local.index == 0;
            }
            local.index > 0
                && local.index <= function.body.arg_count
                && trust_vcgen::local_var_name(function, local) == domain.name
        });
        let Some(local) = locals.next() else { return false };
        if locals.next().is_some() || (local.index == 0 && local.ty != function.body.return_ty) {
            return false;
        }
        match (&local.ty, domain.domain) {
            (Ty::Bool, Domain::Bool) => true,
            (
                Ty::Int { width, signed },
                Domain::MachineInt { width: source_width, signed: source_signed },
            ) => {
                matches!(*width, 8 | 16 | 32 | 64 | 128)
                    && *width == source_width
                    && *signed == source_signed
            }
            // Pointer-sized, mathematical, aggregate and projected carriers
            // need their own exact declared-type relation, never an Int guess.
            _ => false,
        }
    })
}

#[derive(Serialize)]
struct SourceBodyDeclinePayload<'a> {
    schema: &'static str,
    cause: trust_types::ContractBodyDeclineCause,
    function: &'a FunctionContext,
    source_digest: &'a str,
    contract_id: &'a str,
    source: &'a SourceSpan,
    proposition: &'a trust_types::CompilerContractProposition,
}

pub(crate) struct SourceBodyDeclineTransport {
    pub contract_id: String,
    pub metadata: Vec<MetadataEntry>,
}

/// Compare a retained decline question with its canonical source contract.
/// This is not authority: the compiler must also match its independent current
/// constructor reference, exact VC carrier, execution context and live monitor.
pub fn source_body_decline_metadata_matches_contract(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
    vc: &VerificationCondition,
    function_context: &FunctionContext,
    contract: &TrustContract,
    obligation: &TrustObligation,
) -> bool {
    if !matches!(&obligation.kind, ObligationKind::Custom { namespace, name }
        if namespace == "trust.vc" && name == "declined_contract_body")
        || contract.kind != ContractKind::Ensures
        || function_context.path != function.def_path
        || function_context.crate_name.trim().is_empty()
    {
        return false;
    }
    let source_digest = verifier_source_digest(function);
    let Some(expected) = source_body_decline_transport(
        function,
        compiler_contracts,
        vc,
        function_context,
        &source_digest,
        None,
    ) else {
        return false;
    };
    if obligation.contract_id.as_deref() != Some(expected.contract_id.as_str())
        || contract.contract_id != expected.contract_id
        || obligation.source != source_location(&vc.location)
        || validated_source_body_decline(function, compiler_contracts, vc)
            .is_none_or(|bound| contract.source != source_location(&bound.contract.span))
    {
        return false;
    }
    let one = |metadata: &[MetadataEntry], key: &str, expected: &str| {
        metadata
            .iter()
            .filter(|entry| entry.key == key)
            .map(|entry| entry.value.as_str())
            .eq(std::iter::once(expected))
    };
    // The full question is independent of target elaboration. Its predicate
    // digest is checked against the separately authenticated public contract,
    // whose target elaboration belongs to the compiler's constructor reference.
    if !expected.metadata.iter().all(|entry| {
        entry.key == TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY
            || one(&obligation.metadata, &entry.key, &entry.value)
    }) || ![
        "trust.contract.lowering",
        TRUST_SOURCE_DIGEST_METADATA_KEY,
        TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY,
    ]
    .into_iter()
    .all(|key| {
        let expected = if key == TRUST_SOURCE_DIGEST_METADATA_KEY {
            Some(source_digest.as_str())
        } else {
            expected
                .metadata
                .iter()
                .find(|entry| entry.key == key)
                .map(|entry| entry.value.as_str())
        };
        expected.is_some_and(|value| {
            one(&contract.metadata, key, value) && one(&obligation.metadata, key, value)
        })
    }) {
        return false;
    }
    let mut contract_digests = contract
        .metadata
        .iter()
        .filter(|entry| entry.key == TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY)
        .map(|entry| entry.value.as_str());
    let Some(contract_digest) = contract_digests.next() else {
        return false;
    };
    if contract_digests.next().is_some()
        || contract_digest.len() != 64
        || !contract_digest
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return false;
    }
    one(&obligation.metadata, TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY, contract_digest)
}

pub(crate) fn source_body_decline_transport(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
    vc: &VerificationCondition,
    function_context: &FunctionContext,
    source_digest: &str,
    target_pointer_width_bits: Option<u32>,
) -> Option<SourceBodyDeclineTransport> {
    vc.kind.declined_contract_body()?;
    if trust_types::verify_budget::exhausted_readonly() {
        return None;
    }
    let bound = validated_source_body_decline(function, compiler_contracts, vc)?;
    let contract_id = contract_id(function, bound.source_contract_index, bound.contract);
    let (predicate, _, lowering) = lower_contract_predicate(
        function,
        bound.contract,
        Some(bound.proposition),
        target_pointer_width_bits,
    );
    let predicate_digest = contract_predicate_digest(
        function,
        bound.source_contract_index,
        bound.contract,
        &predicate,
    );
    let payload = SourceBodyDeclinePayload {
        schema: SCHEMA,
        cause: bound.cause,
        function: function_context,
        source_digest,
        contract_id: &contract_id,
        source: &bound.contract.span,
        proposition: bound.proposition,
    };
    // Keep serialization, canonicalization and temporary JSON destruction on
    // the established deep codec stack. The borrowed typed input drops in O(1).
    let (bytes, proposition_digest) = trust_types::json_depth::encode_owned_on_deep_stack(
        &payload,
        |value| {
            let bytes = trust_types::canonical_json_bytes(value)?;
            let digest = trust_types::typed_contract_proposition_digest(
                &value.proposition.formula,
                &value.proposition.variable_domains,
            );
            Ok((bytes, digest))
        },
        |_| {},
    )
    .ok()?;
    if trust_types::verify_budget::exhausted_readonly() {
        return None;
    }
    if bytes.len() > MAX_TRANSPORT_METADATA_VALUE_BYTES {
        return None;
    }
    let payload = String::from_utf8(bytes).ok()?;
    let metadata = vec![
        MetadataEntry { key: "trust.contract.lowering".into(), value: lowering.into() },
        MetadataEntry {
            key: TRUST_VC_SOURCE_CONTRACT_INDEX_METADATA_KEY.into(),
            value: bound.source_contract_index.to_string(),
        },
        MetadataEntry {
            key: TRUST_VC_SOURCE_CONTRACT_ROLE_METADATA_KEY.into(),
            value: SOURCE_BODY_DECLINE_ROLE.into(),
        },
        MetadataEntry {
            key: TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY.into(),
            value: predicate_digest,
        },
        MetadataEntry {
            key: TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY.into(),
            value: proposition_digest,
        },
        MetadataEntry { key: SOURCE_BODY_DECLINE_METADATA_KEY.into(), value: payload },
    ];
    Some(SourceBodyDeclineTransport { contract_id, metadata })
}
