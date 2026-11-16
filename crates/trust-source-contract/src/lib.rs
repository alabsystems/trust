//! Shared conversion from the typed Trust program and compiler contracts to public verifier input.
//!
//! This is a transitional bridge for batteries-on strict verification: it preserves the
//! compiler-owned contract path and creates per-contract public verifier
//! obligations without allowing source scraping or compatibility evidence to
//! satisfy the full-verification gate.

mod body_decline;
#[cfg(test)]
mod body_decline_tests;
mod correspondence;
mod function_scan;
pub use body_decline::{
    SOURCE_BODY_DECLINE_METADATA_KEY, SOURCE_BODY_DECLINE_ROLE, ValidatedSourceBodyDecline,
    source_body_decline_metadata_matches_contract, validated_source_body_decline,
};
mod monitor_binding;

mod mir_bool_assignment;
mod mir_nominal_constructor;
use std::collections::{BTreeMap, BTreeSet};

pub use correspondence::{
    ExactEnsuresBodyGroup, boolean_ensures_source_marker, exact_boolean_ensures_body_group,
    exact_boolean_ensures_body_group_with_inferred_calls, exact_ensures_body_group,
    exact_unsigned_select_ensures_body_group, exact_unsigned_straight_line_ensures_body_group,
    public_contract_preserves_source, public_obligation_preserves_source,
    verifier_source_contract_id,
};
pub use mir_bool_assignment::{MirBoolAssignment, observe_mir_bool_assignment};
pub use mir_nominal_constructor::{MirNominalConstructor, observe_mir_nominal_constructor};
pub use monitor_binding::source_monitor_metadata_matches_contract;
use serde_json::{Value as JsonValue, json};
use trust_types::{
    CompilerContractBundle, Contract, ContractKind as TrustTypesContractKind, Formula,
    HighLevelSpecAttr, Operand, Place, Projection, Rvalue, Sort, SourceSpan, SpecBinOp, SpecExpr,
    SpecUnaryOp, Statement, TRUST_SYMBOLIC_FORMULA_SCHEMA, Terminator, TrustProofEngineHint,
    TrustProofExecutionMode, TrustProofItem, TrustProofItemKind, TrustProofItemSource, Ty, VcKind,
    VerifiableFunction, VerificationCondition, check_formula_sort, infer_sort, parse_spec_attr,
    stable_sha256_hex,
};
use trust_verifier_api::{
    BundleSubject, ContractKind, ContractPredicate, FunctionContext, MetadataEntry,
    ObligationContext, ObligationKind, ObligationOrigin, ObligationProducer, ProofStrength,
    ReasoningKind, SourceLocation, TrustContract, TrustContractBundle, TrustObligation,
    TrustSpecBinaryOp, TrustSpecBvBinaryOp, TrustSpecBvUnaryOp, TrustSpecExpr, TrustSpecPredicate,
    TrustSpecQuantifier, TrustSpecScalarSort, TrustSpecSort, TrustSpecUnaryOp, TrustSpecVariable,
    TrustSpecVariableOrigin,
};

/// Compiler query marker shared by extraction and public source correspondence.
pub const LOWERED_COMPILER_CONTRACT_PREFIX: &str = "__trust_lowered_compiler_contract__:";
pub use trust_types::assumption::UNSUPPORTED_COMPILER_CONTRACT_PREFIX;

const TRUST_VC_HARDENED_CATEGORY_METADATA_KEY: &str = "trust.vc.hardened.category";
const TRUST_VC_HARDENED_FAMILY_METADATA_KEY: &str = "trust.vc.hardened.family";
const TRUST_VC_HARDENED_CALLEE_METADATA_KEY: &str = "trust.vc.hardened.callee";
const TRUST_VC_HARDENED_DETAIL_METADATA_KEY: &str = "trust.vc.hardened.detail";
// Both namespaces are ALIASED from the owning vocabulary crate, never
// re-declared: a local spelling could drift from the admitted list and
// silently split a lane in two.
use trust_verifier_api::TRUST_VC_HARDENED_OBLIGATION_NAMESPACE as TRUST_VC_HARDENED_NAMESPACE;
// Trust (P0 false-proof fix): namespace for the `UnboundedAllocation` (#nia-oom)
// capacity obligation. Deliberately NOT `trust.vc.hardened`, so the capacity
// check can never inherit a native whole-function CHC "safe" verdict that never
// modeled the allocation budget (the recorded P0). The namespace's ONLY native
// route is the trust-vc MIR-memory proof-unit + replayable-certificate lane
// (`trust_vc_formula_obligation`, the BoundsCheck precedent), whose predicate IS
// the negated `count >= ceiling` VC; the front-line ay/interval lane still
// solves the same formula per-VC.
use trust_verifier_api::TRUST_VC_UNBOUNDED_ALLOCATION_OBLIGATION_NAMESPACE as TRUST_VC_UNBOUNDED_ALLOCATION_NAMESPACE;
const TRUST_SOURCE_DIGEST_METADATA_KEY: &str = "trust.mir-extract.source.digest.sha256";
/// Compiler-owned crate disambiguator carried by authority-bearing bundles.
///
/// The value is exactly sixteen lowercase hexadecimal digits. It is paired
/// with a stable-ID-bearing bundle ID: metadata alone is not present in a
/// verifier run envelope and therefore cannot prevent cross-crate replay.
pub const TRUST_COMPILER_STABLE_CRATE_ID_METADATA_KEY: &str = "trust.compiler.stable_crate_id.v1";
const UNRESOLVED_COMPATIBILITY_CRATE_NAME: &str = "@trust-unresolved-crate";
const TRUST_VC_DIGEST_METADATA_KEY: &str = "trust.vc.digest.sha256";
const TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY: &str = "trust.vc.formula.payload";
/// Set (to the discarded byte count) when a typed payload lowered successfully but was
/// dropped for exceeding the transport ceiling. Distinguishes that row from one whose VC
/// never lowered at all — without it the two are byte-identical.
pub(crate) const TRUST_VC_FORMULA_PAYLOAD_DROPPED_METADATA_KEY: &str =
    "trust.vc.formula.payload.dropped_bytes";
/// Trust (T4, 2026-10-10): set (to the discarded byte count) when a VC's SMT-LIB
/// rendering alone exceeds the transport ceiling and the row's
/// `trust.vc.formula.smtlib2` value was replaced by
/// [`TRUST_VC_FORMULA_SMTLIB_OMITTED_PREFIX`]`…`. Such a row carries no formula
/// any engine can read (its typed payload is withheld too), so every transport
/// engine declines it; it is recorded rather than silent for the same reason
/// as [`TRUST_VC_FORMULA_PAYLOAD_DROPPED_METADATA_KEY`].
pub(crate) const TRUST_VC_FORMULA_SMTLIB_OMITTED_METADATA_KEY: &str =
    "trust.vc.formula.smtlib2.omitted_bytes";
/// The prefix of the `trust.vc.formula.smtlib2` value that stands in for an
/// SMT-LIB rendering over the transport ceiling. Deliberately NOT an SMT-LIB term
/// (no parser accepts a bare `trust-omitted-smtlib2:` token) and never `false`,
/// the default-admission row's reserved value.
pub(crate) const TRUST_VC_FORMULA_SMTLIB_OMITTED_PREFIX: &str = "trust-omitted-smtlib2:";
const TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY: &str = "trust.contract.predicate.digest.sha256";
const TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY: &str =
    "trust.contract.typed_proposition.digest.sha256";
const TRUST_VC_SOURCE_CONTRACT_INDEX_METADATA_KEY: &str = "trust.vc.source_contract_index.v1";
const TRUST_VC_SOURCE_CONTRACT_ROLE_METADATA_KEY: &str = "trust.vc.source_contract_role.v1";
const TRUST_VC_CONDITION_ORIGIN_METADATA_KEY: &str = "trust_vc.condition_origin";
const TRUST_VC_CONDITION_ORIGIN_METADATA_VALUE: &str = "TypedTrustVcExpr";
const TRUST_VC_PROOF_OBLIGATION_METADATA_KEY: &str = "trust_vc.proof_obligation";
const TRUST_VC_PROOF_OBLIGATION_METADATA_VALUE: &str = "TypedProofObligation";
const TRUST_VC_OWNERSHIP_CONTEXT_METADATA_KEY: &str = "trust_vc.ownership_context";
const TRUST_VC_OWNERSHIP_CONTEXT_METADATA_VALUE: &str = "typed";
const TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY: &str = "trust_vc.mir_memory.proof_unit";
const TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_METADATA_KEY: &str =
    "trust_vc.mir_memory.proof_unit.schema";
const TRUST_VC_MIR_MEMORY_PROOF_UNIT_UNSUPPORTED_METADATA_KEY: &str =
    "trust_vc.mir_memory.proof_unit.unsupported_reason";
const TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_VERSION: &str = "trust_vc.mir-memory-proof-unit.v1";
const UNMODELED_CONTRACT_ARITHMETIC_LOWERING: &str = "unsupported_machine_arithmetic";
use trust_types::UNPAIRED_LOOP_CONTRACT_PREFIX;
const TRUST_EXACT_LOOP_CONTRACT_VC_REPLACEMENTS_METADATA_KEY: &str =
    "trust.contract.loop_clause.exact_vc_replacements.v1";

#[derive(Debug, Clone)]
struct ValidatedVcSourceContractBinding {
    index: usize,
    contract_id: String,
    predicate_digest: String,
    role: &'static str,
}

/// Canonical authored clauses exposed by the verifier bundle. Whole-function
/// clauses retain their compiler-dense slots. First-class loop clauses occupy
/// the immediately following slots only after the bound function contract is
/// checked against the compiler loop record; malformed/missing bindings are
/// omitted fail-closed and their generated UnsupportedMir row remains visible.
fn verifier_api_source_contracts<'a>(
    function: &'a VerifiableFunction,
    compiler_contracts: &'a CompilerContractBundle,
) -> Vec<(usize, &'a Contract)> {
    let mut contracts: Vec<_> = compiler_contracts.contracts.iter().enumerate().collect();
    let base = compiler_contracts.contracts.len();
    for (loop_index, spec) in compiler_contracts.loop_contracts.iter().enumerate() {
        let index = base + loop_index;
        if let Some(contract) = function
            .contracts
            .get(index)
            .filter(|contract| bound_loop_contract_matches_spec(contract, spec))
        {
            contracts.push((index, contract));
        }
    }
    contracts
}

fn bound_loop_contract_matches_spec(
    contract: &Contract,
    spec: &trust_types::LoopContractSpec,
) -> bool {
    let kind_matches = matches!(
        (contract.kind, spec.kind),
        (TrustTypesContractKind::LoopInvariant, trust_types::LoopContractKind::Invariant)
            | (TrustTypesContractKind::Decreases, trust_types::LoopContractKind::Decreases)
    );
    if !kind_matches || contract.span != spec.span {
        return false;
    }
    contract.body.strip_prefix(UNPAIRED_LOOP_CONTRACT_PREFIX).is_some_and(|body| body == spec.body)
        || parsed_loop_contract_body(&contract.body).is_some_and(|(header, body)| {
            spec.mir_header == Some(header) && body.trim() == spec.body.trim()
        })
}

fn parsed_loop_contract_body(body: &str) -> Option<(usize, &str)> {
    let (header, body) = body.strip_prefix("bb")?.split_once(':')?;
    Some((header.parse::<usize>().ok()?, body))
}

fn normalized_compiler_contract_body(body: &str) -> &str {
    body.trim().strip_prefix(LOWERED_COMPILER_CONTRACT_PREFIX).unwrap_or(body.trim()).trim()
}

fn canonical_source_contract<'a>(
    function: &'a VerifiableFunction,
    compiler_contracts: &'a CompilerContractBundle,
    index: usize,
) -> Option<&'a Contract> {
    if let Some(compiler_contract) = compiler_contracts.contracts.get(index) {
        let function_contract = function.contracts.get(index)?;
        return (function_contract == compiler_contract).then_some(compiler_contract);
    }
    let loop_index = index.checked_sub(compiler_contracts.contracts.len())?;
    let spec = compiler_contracts.loop_contracts.get(loop_index)?;
    function
        .contracts
        .get(index)
        .filter(|contract| bound_loop_contract_matches_spec(contract, spec))
}

fn vc_source_contract_role(
    vc: &VerificationCondition,
    contract: &Contract,
) -> Option<&'static str> {
    match (&vc.kind, contract.kind) {
        (VcKind::Postcondition, TrustTypesContractKind::Ensures) => Some("postcondition"),
        (
            VcKind::LoopInvariantInitiation { header_block, .. },
            TrustTypesContractKind::LoopInvariant,
        ) if parsed_loop_contract_body(&contract.body)
            .is_some_and(|(header, _)| header == *header_block) =>
        {
            Some("loop_invariant_initiation")
        }
        (
            VcKind::LoopInvariantConsecution { header_block, .. },
            TrustTypesContractKind::LoopInvariant,
        ) if parsed_loop_contract_body(&contract.body)
            .is_some_and(|(header, _)| header == *header_block) =>
        {
            Some("loop_invariant_consecution")
        }
        (VcKind::NonTermination { context, measure }, TrustTypesContractKind::Decreases)
            if context == "loop-decreases" =>
        {
            parsed_loop_contract_body(&contract.body)
                .is_some_and(|(_, body)| normalized_compiler_contract_body(body) == measure.trim())
                .then_some("loop_decreases")
        }
        (VcKind::NonTermination { context, measure }, TrustTypesContractKind::Decreases)
            if context == "recursion" =>
        {
            (!contract.body.starts_with(UNPAIRED_LOOP_CONTRACT_PREFIX)
                && parsed_loop_contract_body(&contract.body).is_none()
                && normalized_compiler_contract_body(&contract.body) == measure.trim())
            .then_some("recursion_decreases")
        }
        _ => None,
    }
}

pub(crate) fn validated_vc_source_contract_index_and_role(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
    vc: &VerificationCondition,
) -> Option<(usize, &'static str)> {
    let index = vc.contract_metadata?.source_contract_index?;
    let contract = canonical_source_contract(function, compiler_contracts, index)?;
    let role = vc_source_contract_role(vc, contract)?;
    Some((index, role))
}

fn validated_vc_source_contract_binding(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
    vc: &VerificationCondition,
    target_pointer_width_bits: Option<u32>,
    cached_contracts: Option<&trust_types::fx::FxHashMap<usize, (String, String)>>,
) -> Option<ValidatedVcSourceContractBinding> {
    let (index, role) =
        validated_vc_source_contract_index_and_role(function, compiler_contracts, vc)?;
    if let Some((contract_id, predicate_digest)) = cached_contracts.and_then(|m| m.get(&index)) {
        return Some(ValidatedVcSourceContractBinding {
            index,
            contract_id: contract_id.clone(),
            predicate_digest: predicate_digest.clone(),
            role,
        });
    }
    let contract = canonical_source_contract(function, compiler_contracts, index)?;
    let (predicate, _, _) = lower_contract_predicate(
        function,
        contract,
        compiler_contracts.typed_proposition(index, contract),
        target_pointer_width_bits,
    );
    Some(ValidatedVcSourceContractBinding {
        index,
        contract_id: contract_id(function, index, contract),
        predicate_digest: contract_predicate_digest(function, index, contract, &predicate),
        role,
    })
}

/// Regenerate definition-site `#[requires]` bookkeeping rows from the current
/// function and retain only rows whose dense source-clause provenance is exact.
/// This is deliberately fresh-context authority: a caller-supplied VC that
/// merely looks like `self + false` is not enough to suppress an obligation.
fn exact_definition_site_precondition_rows(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
) -> Vec<VerificationCondition> {
    if !compiler_contracts
        .contracts
        .iter()
        .any(|contract| matches!(contract.kind, TrustTypesContractKind::Requires))
    {
        return Vec::new();
    }
    trust_vcgen::generate_vcs(function)
        .into_iter()
        .filter(|vc| {
            definition_site_precondition_has_exact_source(function, compiler_contracts, vc)
        })
        .collect()
}

fn definition_site_precondition_has_exact_source(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
    vc: &VerificationCondition,
) -> bool {
    let Some(source_index) =
        vc.contract_metadata.and_then(|metadata| metadata.source_contract_index)
    else {
        return false;
    };
    let Some(contract) = canonical_source_contract(function, compiler_contracts, source_index)
    else {
        return false;
    };
    matches!(contract.kind, TrustTypesContractKind::Requires)
        && contract.span == vc.location
        && vc.function.as_str() == function.name
        && matches!(&vc.kind, VcKind::Precondition { callee } if callee == &function.name)
        && matches!(vc.formula, Formula::Bool(false))
}

fn exact_vc_payload(vc: &VerificationCondition) -> Option<Vec<u8>> {
    serde_json::to_vec(vc).ok()
}

fn exact_vc_payload_counts(rows: &[VerificationCondition]) -> BTreeMap<Vec<u8>, usize> {
    let mut counts = BTreeMap::new();
    for row in rows {
        if let Some(payload) = exact_vc_payload(row) {
            *counts.entry(payload).or_default() += 1;
        }
    }
    counts
}

/// Indices of supplied compiler VCs that are emitted as public VC obligations.
///
/// The only excluded rows are exact, uniquely regenerated definition-site
/// `#[requires]` bookkeeping VCs. Their authored contract marker remains public
/// and is handled as a modular entry assumption. Exposing this classifier keeps
/// compiler-side fresh-inventory sealing in exact parity with bundle emission.
#[must_use]
pub fn verifier_api_emitted_vc_indices(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
    supplied_vcs: &[VerificationCondition],
) -> Vec<usize> {
    if !supplied_vcs
        .iter()
        .any(|vc| definition_site_precondition_has_exact_source(function, compiler_contracts, vc))
    {
        return (0..supplied_vcs.len()).collect();
    }
    let regenerated_rows = exact_definition_site_precondition_rows(function, compiler_contracts);
    if regenerated_rows.is_empty() {
        return (0..supplied_vcs.len()).collect();
    }
    let regenerated_counts = exact_vc_payload_counts(&regenerated_rows);
    let mut supplied_payloads: Vec<Option<Vec<u8>>> = Vec::with_capacity(supplied_vcs.len());
    let mut supplied_counts = BTreeMap::new();
    for vc in supplied_vcs {
        if definition_site_precondition_has_exact_source(function, compiler_contracts, vc) {
            let payload = exact_vc_payload(vc);
            if let Some(ref bytes) = payload {
                *supplied_counts.entry(bytes.clone()).or_default() += 1;
            }
            supplied_payloads.push(payload);
        } else {
            supplied_payloads.push(None);
        }
    }
    supplied_payloads
        .into_iter()
        .enumerate()
        .filter_map(|(index, payload)| {
            let is_unique_fresh = payload.as_ref().is_some_and(|payload| {
                supplied_counts.get(payload) == Some(&1)
                    && regenerated_counts.get(payload) == Some(&1)
            });
            (!is_unique_fresh).then_some(index)
        })
        .collect()
}

/// Require an unambiguous one-to-one match between every freshly regenerated
/// row for one source-clause role and the supplied carrier.
///
/// A production row may be retained raw by interval discharge or dispatched
/// in the exact compiler-augmented shape. The choice is per row. Fresh and
/// supplied payloads must nevertheless be unique, and every supplied row must
/// map to exactly one fresh call site/role. This deliberately fails closed if
/// two fresh rows are byte-indistinguishable: such a carrier cannot establish
/// which semantic site it covers.
fn exact_fresh_source_role_rows_match(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
    supplied_vcs: &[VerificationCondition],
    source_index: usize,
    required_role: &str,
    raw_vcs: &[VerificationCondition],
    augmented_vcs: &[VerificationCondition],
    target_pointer_width_bits: Option<u32>,
) -> bool {
    if raw_vcs.len() != augmented_vcs.len() {
        return false;
    }
    // A modelled subset of the returns is not the whole authored clause.
    // Consult the regenerated owner output, so omitting a decline from the
    // supplied carrier cannot manufacture a complete body-violation formula.
    // Declines never enter the ordinary role/proof group below.
    if required_role == "postcondition"
        && raw_vcs.iter().any(|vc| {
            vc.kind
                .declined_contract_body()
                .is_some_and(|decline| decline.source_contract_index == source_index)
        })
    {
        return false;
    }

    let _ = target_pointer_width_bits;
    let mut expected_choices = Vec::new();
    for (raw, augmented) in raw_vcs.iter().zip(augmented_vcs) {
        let Some((raw_index, raw_role)) =
            validated_vc_source_contract_index_and_role(function, compiler_contracts, raw)
        else {
            continue;
        };
        if raw_index != source_index || raw_role != required_role {
            continue;
        };
        let Some((augmented_index, augmented_role)) =
            validated_vc_source_contract_index_and_role(function, compiler_contracts, augmented)
        else {
            return false;
        };
        if augmented_index != source_index || augmented_role != required_role {
            return false;
        }
        let (Some(raw_payload), Some(augmented_payload)) =
            (exact_vc_payload(raw), exact_vc_payload(augmented))
        else {
            return false;
        };
        expected_choices.push((raw_payload, augmented_payload));
    }
    if expected_choices.is_empty() {
        return false;
    }

    // Payload -> unique fresh semantic row. Reject overlap between distinct
    // fresh rows even when it occurs across raw/augmented spellings.
    let mut expected_by_payload: BTreeMap<&[u8], usize> = BTreeMap::new();
    for (expected_index, (raw, augmented)) in expected_choices.iter().enumerate() {
        for payload in [raw.as_slice(), augmented.as_slice()] {
            if expected_by_payload
                .insert(payload, expected_index)
                .is_some_and(|previous| previous != expected_index)
            {
                return false;
            }
        }
    }

    let supplied = supplied_vcs
        .iter()
        .filter(|vc| {
            validated_vc_source_contract_index_and_role(function, compiler_contracts, vc)
                == Some((source_index, required_role))
        })
        .collect::<Vec<_>>();
    if supplied.len() != expected_choices.len() {
        return false;
    }

    let mut supplied_payloads = BTreeSet::new();
    let mut matched_expected = BTreeSet::new();
    for supplied in supplied {
        let Some(payload) = exact_vc_payload(supplied) else {
            return false;
        };
        let Some(expected_index) = expected_by_payload.get(payload.as_slice()).copied() else {
            return false;
        };
        if !supplied_payloads.insert(payload) {
            return false;
        }
        if !matched_expected.insert(expected_index) {
            return false;
        }
    }
    matched_expected.len() == expected_choices.len()
}

/// Canonical body-violation formulas for authored `ensures` catalog rows.
///
/// A catalog predicate is the positive source claim, not an error condition.
/// Native CHC input must instead encode the disjunction of every fresh
/// source-bound return violation. Require the same exact, complete production
/// row bijection as loop-clause replacement; no missing, duplicate, stale or
/// source-repointed carrier may supply a clause formula. The caller retains
/// the catalog row and must match it to its independent compiler reference
/// before attaching these public semantic bytes. Nothing here grants proof
/// authority or changes the later source-clause discharge rules.
/// The digest identifies this whole clause and its complete body provenance,
/// rather than borrowing one return row's VC identity. Attach it before native
/// public-claim identities are minted so the typed CHC binding can retain it.
#[must_use]
pub fn verifier_api_source_clause_body_formula_metadata(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
    supplied_vcs: &[VerificationCondition],
    crate_name: &str,
    target_pointer_width_bits: Option<u32>,
) -> BTreeMap<usize, Vec<MetadataEntry>> {
    let mut formulas = BTreeMap::new();
    if !compiler_contracts
        .contracts
        .iter()
        .any(|contract| contract.kind == TrustTypesContractKind::Ensures)
    {
        return formulas;
    }
    let Some((raw, augmented)) =
        trust_vcgen::regenerate_postcondition_production_variants(function)
    else {
        return formulas;
    };
    let source_digest = verifier_source_digest(function);
    for (source_index, contract) in verifier_api_source_contracts(function, compiler_contracts) {
        if contract.kind != TrustTypesContractKind::Ensures
            || !exact_fresh_source_role_rows_match(
                function,
                compiler_contracts,
                supplied_vcs,
                source_index,
                "postcondition",
                &raw,
                &augmented,
                target_pointer_width_bits,
            )
        {
            continue;
        }
        let rows = supplied_vcs
            .iter()
            .enumerate()
            .filter(|(_, vc)| {
                validated_vc_source_contract_index_and_role(function, compiler_contracts, vc)
                    == Some((source_index, "postcondition"))
            })
            .collect::<Vec<_>>();
        let violation = if rows.len() == 1 {
            rows[0].1.formula.clone()
        } else {
            Formula::Or(rows.iter().map(|(_, vc)| vc.formula.clone()).collect())
        };
        // Reuse the one selected-formula lowering, including unsigned-machine
        // widening, transport ceilings and the refutation-blocking pruned flag.
        let payload = vc_formula_payload_for(function, &VcKind::Postcondition, &violation);
        if payload.typed_payload.is_none() {
            continue;
        }
        let body_identities = rows
            .iter()
            .map(|(index, vc)| {
                let identity = verifier_vc_content_identity_with_source_digest_and_crate_name(
                    function,
                    *index,
                    vc,
                    &source_digest,
                    crate_name,
                );
                json!({"obligation_id": identity.obligation_id, "digest": identity.digest})
            })
            .collect::<Vec<_>>();
        let provenance = json!({
            "source_contract_index": source_index,
            "body_vcs": body_identities,
        })
        .to_string();
        if provenance.len() > MAX_TRANSPORT_METADATA_VALUE_BYTES {
            continue;
        }
        let mut metadata = payload.into_metadata();
        metadata.push(MetadataEntry {
            key: "trust.contract.body_vcs.formula.v1".to_string(),
            value: provenance,
        });
        let digest = stable_json_digest(&json!({
            "schema": "trust-mir-extract.source-clause-body-vc-digest.v1",
            "source_digest": source_digest,
            "crate_name": crate_name,
            "source_contract_index": source_index,
            "source_contract": contract,
            "target_pointer_width_bits": target_pointer_width_bits,
            "formula_metadata": &metadata,
        }));
        metadata
            .push(MetadataEntry { key: TRUST_VC_DIGEST_METADATA_KEY.to_string(), value: digest });
        formulas.insert(source_index, metadata);
    }
    formulas
}

/// Return source-clause indices whose standalone contract marker can be
/// replaced by exact fresh body proof rows in this bundle.
///
/// A loop invariant is not a globally true predicate: its proof consists of
/// one initiation and one consecution VC. Likewise, an authored loop
/// `decreases` clause is owned by its reconstructed strict-decrease VC, while
/// a function-recursion `decreases` clause owns one row for every recursive
/// call site. The generic contract catalog cannot prove these clauses in
/// isolation, but we must not remove a fail-closed marker merely because
/// caller-supplied rows look plausible. Regenerate VCs from the exact function
/// and require a byte-semantic bijection, with exact compiler source binding,
/// for every role/call site. Missing, duplicate, stale, or forged rows leave
/// the marker visible.
fn exact_fresh_loop_contract_vc_replacements(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
    supplied_vcs: &[VerificationCondition],
    feedback: &[trust_vcgen::LoopInvariantFeedbackCandidate],
    target_pointer_width_bits: Option<u32>,
) -> BTreeSet<usize> {
    if compiler_contracts.loop_contracts.is_empty()
        && !compiler_contracts.contracts.iter().any(|contract| {
            matches!(
                contract.kind,
                TrustTypesContractKind::LoopInvariant | TrustTypesContractKind::Decreases
            )
        })
    {
        return BTreeSet::new();
    }
    let Some((raw_vcs, augmented_vcs)) =
        trust_vcgen::regenerate_loop_contract_production_variants(function, feedback)
    else {
        return BTreeSet::new();
    };
    let source_contracts = verifier_api_source_contracts(function, compiler_contracts);
    let needs_recursion_reconstruction = source_contracts.iter().any(|(_, contract)| {
        matches!(contract.kind, TrustTypesContractKind::Decreases)
            && parsed_loop_contract_body(&contract.body).is_none()
            && !contract.body.starts_with(UNPAIRED_LOOP_CONTRACT_PREFIX)
    });
    let recursion_variants = if needs_recursion_reconstruction {
        trust_vcgen::regenerate_recursion_decreases_production_variants(function)
    } else {
        Some((Vec::new(), Vec::new()))
    };
    let Some((raw_recursion_vcs, augmented_recursion_vcs)) = recursion_variants else {
        return BTreeSet::new();
    };
    let mut replacements = BTreeSet::new();

    for (index, contract) in source_contracts {
        // Abstract interpretation partitions rows individually: discharged
        // rows remain raw while undischargeable rows are interval-augmented
        // before solver dispatch. One real production carrier can therefore
        // mix the two exact spellings across roles/call sites.
        let exact_for_every_role = match contract.kind {
            TrustTypesContractKind::LoopInvariant => {
                ["loop_invariant_initiation", "loop_invariant_consecution"].iter().all(|role| {
                    exact_fresh_source_role_rows_match(
                        function,
                        compiler_contracts,
                        supplied_vcs,
                        index,
                        role,
                        &raw_vcs,
                        &augmented_vcs,
                        target_pointer_width_bits,
                    )
                })
            }
            TrustTypesContractKind::Decreases
                if parsed_loop_contract_body(&contract.body).is_some() =>
            {
                exact_fresh_source_role_rows_match(
                    function,
                    compiler_contracts,
                    supplied_vcs,
                    index,
                    "loop_decreases",
                    &raw_vcs,
                    &augmented_vcs,
                    target_pointer_width_bits,
                )
            }
            TrustTypesContractKind::Decreases
                if !contract.body.starts_with(UNPAIRED_LOOP_CONTRACT_PREFIX) =>
            {
                exact_fresh_source_role_rows_match(
                    function,
                    compiler_contracts,
                    supplied_vcs,
                    index,
                    "recursion_decreases",
                    &raw_recursion_vcs,
                    &augmented_recursion_vcs,
                    target_pointer_width_bits,
                )
            }
            _ => false,
        };

        if exact_for_every_role {
            replacements.insert(index);
        }
    }

    replacements
}

/// Convert compiler-owned contract data into the public verifier API shape.
#[doc(hidden)]
#[deprecated(
    note = "compatibility-only crate-name inference; use contract_bundle_to_verifier_api_with_compiler_identity for compiler authority"
)]
#[allow(deprecated)]
#[must_use]
pub fn contract_bundle_to_verifier_api(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
) -> TrustContractBundle {
    let crate_name = crate_name_from_def_path(&function.def_path);
    contract_bundle_to_verifier_api_with_crate_name(function, compiler_contracts, &crate_name)
}

/// Convert compiler-owned contract data using a caller-supplied display crate
/// name.
///
/// Rust qualified paths such as `<crate::Type as crate::Trait>::method` do not
/// encode one unambiguous owner that this transport layer can safely infer.
/// This preserves one spelling consistently in the subject and obligation
/// contexts, but a crate name does not distinguish same-name rustc crate
/// instances and therefore cannot carry compiler authority.
#[doc(hidden)]
#[deprecated(
    note = "crate name is not a rustc crate-instance authority; use contract_bundle_to_verifier_api_with_compiler_identity"
)]
#[must_use]
pub fn contract_bundle_to_verifier_api_with_crate_name(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
    crate_name: &str,
) -> TrustContractBundle {
    // No target pointer width is nameable through this compatibility surface;
    // pointer-sized quantifier binders fail closed (see
    // `spec_quantifier_sort_domain`).
    contract_bundle_to_verifier_api_for_target(function, compiler_contracts, crate_name, None)
}

/// Shared bundle constructor carrying the compilation target's pointer width
/// (in bits) for pointer-sized spec binders. `None` fails those binders closed.
fn contract_bundle_to_verifier_api_for_target(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
    crate_name: &str,
    target_pointer_width_bits: Option<u32>,
) -> TrustContractBundle {
    let source_digest = verifier_source_digest(function);
    let function_context = function_context_with_crate_name(function, crate_name);
    let mut lowered_contracts = trust_types::fx::FxHashMap::default();
    contract_bundle_to_verifier_api_for_target_with_context(
        function,
        compiler_contracts,
        &function_context,
        &source_digest,
        target_pointer_width_bits,
        &mut lowered_contracts,
    )
}

fn contract_bundle_to_verifier_api_for_target_with_context(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
    function_context: &FunctionContext,
    source_digest: &str,
    target_pointer_width_bits: Option<u32>,
    lowered_contracts: &mut trust_types::fx::FxHashMap<usize, (String, String)>,
) -> TrustContractBundle {
    let mut bundle = TrustContractBundle::empty(
        format!(
            "trust-contracts:{}",
            trust_types::canonical_artifact_id_component(&function.def_path)
        ),
        BundleSubject::Function {
            crate_name: function_context.crate_name.clone(),
            path: function.def_path.clone(),
        },
    );
    bundle.metadata.push(MetadataEntry {
        key: "trust.full_verification.source".to_string(),
        value: "compiler_contract_bundle".to_string(),
    });
    bundle.metadata.push(MetadataEntry {
        key: TRUST_SOURCE_DIGEST_METADATA_KEY.to_string(),
        value: source_digest.to_string(),
    });

    for (index, contract) in verifier_api_source_contracts(function, compiler_contracts) {
        let contract_id = contract_id(function, index, contract);
        let source = source_location(&contract.span);
        let typed_proposition = compiler_contracts.typed_proposition(index, contract);
        let typed_proposition_digest = typed_proposition.map(|proposition| {
            trust_types::typed_contract_proposition_digest(
                &proposition.formula,
                &proposition.variable_domains,
            )
        });
        let Some((api_kind, obligation_kind)) = contract_kind(contract.kind) else {
            bundle.obligations.push(unsupported_contract_obligation(
                function,
                function_context,
                index,
                contract,
                source,
                None,
                None,
                typed_proposition_digest,
                format!("unsupported compiler contract kind {:?}", contract.kind),
            ));
            continue;
        };

        let (predicate, unsupported_reason, lowering) = lower_contract_predicate(
            function,
            contract,
            typed_proposition,
            target_pointer_width_bits,
        );
        let predicate_schema = predicate_schema(&predicate);
        let predicate_digest = contract_predicate_digest(function, index, contract, &predicate);
        lowered_contracts.insert(index, (contract_id.clone(), predicate_digest.clone()));
        let mut metadata = vec![MetadataEntry {
            key: "trust.contract.kind".to_string(),
            value: contract.kind.attr_name().to_string(),
        }];
        metadata.push(MetadataEntry {
            key: "trust.contract.lowering".to_string(),
            value: lowering.to_string(),
        });
        if let Some(reason) = &unsupported_reason {
            metadata.push(MetadataEntry {
                key: "trust.contract.unsupported_reason".to_string(),
                value: reason.clone(),
            });
        }
        if let Some(schema) = &predicate_schema {
            metadata.push(MetadataEntry {
                key: "trust.contract.predicate.schema".to_string(),
                value: schema.clone(),
            });
        }
        metadata.extend([
            MetadataEntry {
                key: TRUST_SOURCE_DIGEST_METADATA_KEY.to_string(),
                value: source_digest.to_string(),
            },
            MetadataEntry {
                key: TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY.to_string(),
                value: predicate_digest.clone(),
            },
        ]);
        if let Some(digest) = typed_proposition_digest.as_ref() {
            metadata.push(MetadataEntry {
                key: TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY.to_string(),
                value: digest.clone(),
            });
        }

        bundle.contracts.push(TrustContract {
            contract_id: contract_id.clone(),
            kind: api_kind,
            predicate,
            source: source.clone(),
            metadata,
        });

        if let Some(reason) = unsupported_reason {
            // An authored clause that cannot be represented in the typed public
            // proposition lane is a specification-elaboration failure, not a
            // missing definition-site proof. Keep one contract-bound,
            // fail-closed marker for every kind. This preserves the exact clause
            // identity (and any certified-monitor status) through transport and
            // prevents an independently generated VC from hiding the malformed
            // annotation. Unsupported evidence never receives proof authority.
            bundle.obligations.push(unsupported_contract_obligation(
                function,
                function_context,
                index,
                contract,
                source,
                Some(contract_id),
                Some(predicate_digest),
                typed_proposition_digest,
                reason,
            ));
            continue;
        }

        let obligation_context = obligation_context_metadata(
            function_context,
            ObligationOrigin::Contract {
                contract_id: contract_id.clone(),
                contract_kind: api_kind,
                contract_index: index,
                predicate_schema,
            },
        );
        let mut obligation_metadata = vec![
            obligation_context,
            MetadataEntry {
                key: "trust.contract.lowering".to_string(),
                value: lowering.to_string(),
            },
            MetadataEntry {
                key: TRUST_SOURCE_DIGEST_METADATA_KEY.to_string(),
                value: source_digest.to_string(),
            },
            MetadataEntry {
                key: TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY.to_string(),
                value: predicate_digest,
            },
        ];
        if let Some(digest) = typed_proposition_digest {
            obligation_metadata.push(MetadataEntry {
                key: TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY.to_string(),
                value: digest,
            });
        }
        bundle.obligations.push(TrustObligation {
            obligation_id: obligation_id(function, index, &obligation_kind),
            kind: obligation_kind,
            contract_id: Some(contract_id),
            proof_item_id: None,
            source,
            description: format!("prove {} contract", contract.kind.attr_name()),
            required_strength: Some(ProofStrength::deductive()),
            summary_facts: Vec::new(),
            metadata: obligation_metadata,
        });
    }

    for (index, proof_item) in compiler_contracts.proof_items.iter().enumerate() {
        bundle.obligations.push(proof_item_obligation(
            function,
            function_context,
            index,
            proof_item,
        ));
    }

    bundle
}

/// Convert compiler-owned contracts with the complete rustc crate identity.
///
/// `crate_name` remains the diagnostic/display identity used by the public
/// schema. `stable_crate_id` is the independently compiler-owned authority
/// identity and is bound into both bundle metadata and the bundle ID so a
/// verifier response from a same-name crate instance cannot be replayed.
///
/// `target_pointer_width_bits` is the compilation target's pointer width from
/// `tcx.data_layout.pointer_size().bits()`; it gives `usize`/`isize` quantifier
/// binders their exact domain. `None` — or any width outside the supported
/// 16/32/64 set — keeps those binders failing closed.
#[must_use]
pub fn contract_bundle_to_verifier_api_with_compiler_identity(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
    crate_name: &str,
    stable_crate_id: u64,
    target_pointer_width_bits: Option<u32>,
) -> TrustContractBundle {
    let mut bundle = contract_bundle_to_verifier_api_for_target(
        function,
        compiler_contracts,
        crate_name,
        target_pointer_width_bits,
    );
    bind_compiler_crate_identity(&mut bundle, function, stable_crate_id);
    bundle
}

/// Convert compiler-owned contracts and generated VCs into one public verifier bundle.
///
/// Contract obligations keep their contract IDs. Generated VCs retain only the
/// exact source or compiler-synthetic contract reference required by their
/// public proof claim; there is no generic annotation-only fallback that could
/// replace a language/runtime-safety obligation.
#[doc(hidden)]
#[deprecated(
    note = "compatibility-only crate-name inference; use function_to_verifier_api_bundle_with_compiler_identity for compiler authority"
)]
#[allow(deprecated)]
#[must_use]
pub fn function_to_verifier_api_bundle(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
    vcs: &[VerificationCondition],
) -> TrustContractBundle {
    let crate_name = crate_name_from_def_path(&function.def_path);
    function_to_verifier_api_bundle_with_crate_name(function, compiler_contracts, vcs, &crate_name)
}

/// Convert contracts and VCs using one caller-supplied display crate name.
/// This does not distinguish same-name rustc crate instances.
#[doc(hidden)]
#[deprecated(
    note = "crate name is not a rustc crate-instance authority; use function_to_verifier_api_bundle_with_compiler_identity"
)]
#[allow(deprecated)]
#[must_use]
pub fn function_to_verifier_api_bundle_with_crate_name(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
    vcs: &[VerificationCondition],
    crate_name: &str,
) -> TrustContractBundle {
    function_to_verifier_api_bundle_with_loop_feedback_candidates_and_crate_name(
        function,
        compiler_contracts,
        vcs,
        &[],
        crate_name,
    )
}

/// Convert contracts and VCs with the complete rustc crate identity.
///
/// `target_pointer_width_bits` follows the
/// [`contract_bundle_to_verifier_api_with_compiler_identity`] contract: the
/// target's pointer width in bits, or `None` to fail pointer-sized quantifier
/// binders closed.
#[must_use]
pub fn function_to_verifier_api_bundle_with_compiler_identity(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
    vcs: &[VerificationCondition],
    crate_name: &str,
    stable_crate_id: u64,
    target_pointer_width_bits: Option<u32>,
) -> TrustContractBundle {
    function_to_verifier_api_bundle_with_loop_feedback_candidates_and_compiler_identity(
        function,
        compiler_contracts,
        vcs,
        &[],
        crate_name,
        stable_crate_id,
        target_pointer_width_bits,
    )
}

/// Exact content identity written into a generated VC obligation.
///
/// Consumers that still hold the fresh compiler-owned VC can use this value to
/// revalidate the public obligation before re-keying verifier evidence.  The
/// digest deliberately uses the same formula lowering (including any sound
/// widening/pruning choice) as
/// [`function_to_verifier_api_bundle_with_compiler_identity`]; callers must not
/// attempt to reproduce that private lowering independently. This is a
/// content identity, not detached crate-instance authority: compiler re-keying
/// must additionally validate the stable-ID-bearing bundle envelope produced
/// by a `*_with_compiler_identity` constructor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifierVcContentIdentity {
    /// Canonical digest stored under `trust.vc.digest.sha256`.
    pub digest: String,
    /// Formula schema stored in both typed context and VC metadata.
    pub formula_schema: String,
    /// Exact function context stored in the typed obligation context.
    pub function: FunctionContext,
    /// Stable VC-kind tag stored in the typed obligation context.
    pub vc_kind: String,
    /// Canonical public obligation id generated for this VC row.
    pub obligation_id: String,
    /// Canonical public obligation classification generated from the VC kind.
    pub obligation_kind: ObligationKind,
    /// Canonical public description generated from the VC kind.
    pub description: String,
    /// Minimum proof strength required by the public VC row.
    pub required_strength: Option<ProofStrength>,
    /// Digest of the complete compiler-owned function source carrier.
    pub source_digest: String,
    /// Exact public formula sort metadata.
    pub formula_sort: String,
    /// Exact public SMT-LIB formula metadata.
    pub formula_smtlib: String,
    /// Exact optional typed formula payload metadata.
    pub formula_payload: Option<String>,
    /// Whether the typed payload was produced by sound violation pruning.
    pub formula_pruned: bool,
    /// Exact TrustVC MIR-memory proof-unit metadata generated for this row.
    ///
    /// This is empty for non-TrustVC obligations, contains the complete
    /// schema/origin/payload family for supported rows, or the single exact
    /// unsupported-reason entry when no proof unit can be generated.
    pub mir_memory_metadata: Vec<MetadataEntry>,
    /// Exact native-ty temporal model/property metadata generated for this row.
    pub temporal_metadata: Vec<MetadataEntry>,
    /// Exact native verifier formula-routing metadata generated for this row.
    pub engine_formula_metadata: Vec<MetadataEntry>,
    /// Exact hardened-obligation routing metadata generated for this row.
    pub hardened_metadata: Vec<MetadataEntry>,
}

/// Recompute the exact digest and formula schema emitted for one fresh VC.
#[must_use]
#[doc(hidden)]
#[deprecated(
    note = "compatibility-only crate-name inference; use verifier_vc_content_identity_with_crate_name"
)]
pub fn verifier_vc_content_identity(
    function: &VerifiableFunction,
    index: usize,
    vc: &VerificationCondition,
) -> VerifierVcContentIdentity {
    let crate_name = crate_name_from_def_path(&function.def_path);
    verifier_vc_content_identity_with_crate_name(function, index, vc, &crate_name)
}

/// Recompute the exact identity emitted for one fresh VC using the
/// compiler-owned crate name stored in its typed function context.
#[must_use]
pub fn verifier_vc_content_identity_with_crate_name(
    function: &VerifiableFunction,
    index: usize,
    vc: &VerificationCondition,
    crate_name: &str,
) -> VerifierVcContentIdentity {
    let source_digest = verifier_source_digest(function);
    verifier_vc_content_identity_with_source_digest_and_crate_name(
        function,
        index,
        vc,
        &source_digest,
        crate_name,
    )
}

/// Recompute one VC identity while reusing a source digest already computed
/// for `function`.
///
/// This is equivalent to [`verifier_vc_content_identity`] when
/// `source_digest` came from [`verifier_source_digest`]. It lets consumers
/// validate a whole bundle without serializing and hashing the complete MIR
/// function once per obligation.
#[must_use]
#[doc(hidden)]
#[deprecated(
    note = "compatibility-only crate-name inference; use verifier_vc_content_identity_with_source_digest_and_crate_name"
)]
pub fn verifier_vc_content_identity_with_source_digest(
    function: &VerifiableFunction,
    index: usize,
    vc: &VerificationCondition,
    source_digest: &str,
) -> VerifierVcContentIdentity {
    let crate_name = crate_name_from_def_path(&function.def_path);
    verifier_vc_content_identity_with_source_digest_and_crate_name(
        function,
        index,
        vc,
        source_digest,
        &crate_name,
    )
}

/// Recompute one VC identity while reusing a source digest and preserving the
/// exact compiler-owned crate name in its typed function context.
#[must_use]
pub fn verifier_vc_content_identity_with_source_digest_and_crate_name(
    function: &VerifiableFunction,
    index: usize,
    vc: &VerificationCondition,
    source_digest: &str,
    crate_name: &str,
) -> VerifierVcContentIdentity {
    let obligation_kind = vc_obligation_kind(&vc.kind);
    let (payload, mir_memory_metadata) = vc_transport_for(function, vc, index, &obligation_kind);
    let obligation_id = format!(
        "vc:{}:{}:{}",
        trust_types::canonical_artifact_id_component(&function.def_path),
        obligation_kind_label(&obligation_kind),
        index
    );
    let temporal_metadata = ty_temporal_model_metadata(&vc.kind);
    let engine_formula_metadata =
        vc_engine_formula_metadata(&obligation_kind, &vc.kind, &payload.schema);
    let hardened_metadata = hardened_vc_metadata(&vc.kind);
    VerifierVcContentIdentity {
        digest: vc_content_digest(function, index, vc, &payload),
        formula_schema: payload.schema,
        function: function_context_with_crate_name(function, crate_name),
        vc_kind: vc_kind_label(&vc.kind),
        obligation_id,
        required_strength: trust_vc_mir_memory_required_strength(&obligation_kind),
        obligation_kind,
        description: vc.kind.description(),
        source_digest: source_digest.to_string(),
        formula_sort: payload.sort,
        formula_smtlib: payload.smtlib,
        formula_payload: payload.typed_payload,
        formula_pruned: payload.pruned,
        mir_memory_metadata,
        temporal_metadata,
        engine_formula_metadata,
        hardened_metadata,
    }
}

/// Convert contracts and VCs while structurally recognizing E5 rows rebuilt
/// with exact, function-bound E4 feedback candidates.
///
/// Candidates are non-authoritative semantic data. This public conversion
/// returns an equally public bundle and cannot mint proof authority; the
/// compiler calls it only after admitting each candidate through its own
/// crate-private E4 capability. An empty slice recognizes only exact first-pass
/// raw/interval-augmented rows.
#[doc(hidden)]
#[deprecated(
    note = "compatibility-only crate-name inference; use function_to_verifier_api_bundle_with_loop_feedback_candidates_and_compiler_identity for compiler authority"
)]
#[allow(deprecated)]
#[must_use]
pub fn function_to_verifier_api_bundle_with_loop_feedback_candidates(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
    vcs: &[VerificationCondition],
    feedback: &[trust_vcgen::LoopInvariantFeedbackCandidate],
) -> TrustContractBundle {
    let crate_name = crate_name_from_def_path(&function.def_path);
    function_to_verifier_api_bundle_with_loop_feedback_candidates_and_crate_name(
        function,
        compiler_contracts,
        vcs,
        feedback,
        &crate_name,
    )
}

/// Convert contracts and VCs with loop feedback while preserving one
/// caller-supplied display crate name. This does not distinguish same-name
/// rustc crate instances.
#[doc(hidden)]
#[deprecated(
    note = "crate name is not a rustc crate-instance authority; use function_to_verifier_api_bundle_with_loop_feedback_candidates_and_compiler_identity"
)]
#[must_use]
pub fn function_to_verifier_api_bundle_with_loop_feedback_candidates_and_crate_name(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
    vcs: &[VerificationCondition],
    feedback: &[trust_vcgen::LoopInvariantFeedbackCandidate],
    crate_name: &str,
) -> TrustContractBundle {
    // No target pointer width is nameable through this compatibility surface;
    // pointer-sized quantifier binders fail closed (see
    // `spec_quantifier_sort_domain`).
    function_to_verifier_api_bundle_for_target(
        function,
        compiler_contracts,
        vcs,
        feedback,
        crate_name,
        None,
    )
}

/// Shared contracts+VCs bundle constructor carrying the compilation target's
/// pointer width (in bits) for pointer-sized spec binders. `None` fails those
/// binders closed. One width flows through every predicate lowering in the
/// bundle — contract rows and VC source-contract bindings alike — so predicate
/// digests never diverge within a build.
fn function_to_verifier_api_bundle_for_target(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
    vcs: &[VerificationCondition],
    feedback: &[trust_vcgen::LoopInvariantFeedbackCandidate],
    crate_name: &str,
    target_pointer_width_bits: Option<u32>,
) -> TrustContractBundle {
    let function_context = function_context_with_crate_name(function, crate_name);
    let source_digest = verifier_source_digest(function);
    let mut lowered_contracts = trust_types::fx::FxHashMap::default();
    let mut bundle = contract_bundle_to_verifier_api_for_target_with_context(
        function,
        compiler_contracts,
        &function_context,
        &source_digest,
        target_pointer_width_bits,
        &mut lowered_contracts,
    );
    let emitted_vc_indices = verifier_api_emitted_vc_indices(function, compiler_contracts, vcs);
    let all_vcs_emitted = emitted_vc_indices.len() == vcs.len();
    let exact_loop_contract_replacements = exact_fresh_loop_contract_vc_replacements(
        function,
        compiler_contracts,
        vcs,
        feedback,
        target_pointer_width_bits,
    );
    if !exact_loop_contract_replacements.is_empty() {
        let replacement_contract_ids = exact_loop_contract_replacements
            .iter()
            .filter_map(|index| {
                lowered_contracts.get(index).map(|(cid, _)| cid.clone()).or_else(|| {
                    canonical_source_contract(function, compiler_contracts, *index)
                        .map(|contract| contract_id(function, *index, contract))
                })
            })
            .collect::<BTreeSet<_>>();
        bundle.obligations.retain(|obligation| {
            !obligation.contract_id.as_ref().is_some_and(|id| replacement_contract_ids.contains(id))
        });
        bundle.metadata.push(MetadataEntry {
            key: TRUST_EXACT_LOOP_CONTRACT_VC_REPLACEMENTS_METADATA_KEY.to_string(),
            value: exact_loop_contract_replacements
                .iter()
                .map(usize::to_string)
                .collect::<Vec<_>>()
                .join(","),
        });
    }

    let def_path_id = trust_types::canonical_artifact_id_component(&function.def_path);
    let narrow_index = std::cell::OnceCell::new();
    let memory_scan = std::cell::OnceCell::new();
    let mut excluded_definition_site_preconditions = 0usize;
    for (index, vc) in vcs.iter().enumerate() {
        // Definition-site `#[requires]` bookkeeping VCs are `Bool(false)`
        // (trivially-UNSAT violation = trivially proved) for legacy counting;
        // the native lane misreads the formula as a CLAIM ("typed predicate is
        // false") and FAILS them, falsely failing every contracted function.
        // Exclude them here only after byte-semantic regeneration from this
        // exact function and unique source-indexed matching in both carriers.
        // Recursive self-call VCs, forged source indices, stale rows, and
        // duplicates all remain visible and therefore fail closed. The
        // exclusion is recorded in bundle metadata below, never silent.
        if !all_vcs_emitted && emitted_vc_indices.binary_search(&index).is_err() {
            excluded_definition_site_preconditions += 1;
            continue;
        }
        let obligation_kind = vc_obligation_kind(&vc.kind);
        let vc_kind_tag = vc_kind_label(&vc.kind);
        let (vc_formula_payload, mir_memory_metadata) = vc_transport_for_cached(
            function,
            vc,
            index,
            &obligation_kind,
            &def_path_id,
            &narrow_index,
            &memory_scan,
        );
        let formula_schema = Some(vc_formula_payload.schema.clone());
        let vc_digest = vc_content_digest(function, index, vc, &vc_formula_payload);
        let mut metadata = vec![
            obligation_context_metadata(
                &function_context,
                ObligationOrigin::VerificationCondition {
                    vc_kind: vc_kind_tag.clone(),
                    vc_index: index,
                    formula_schema,
                },
            ),
            MetadataEntry { key: "trust.vc.kind".to_string(), value: vc_kind_tag },
            MetadataEntry {
                key: TRUST_SOURCE_DIGEST_METADATA_KEY.to_string(),
                value: source_digest.clone(),
            },
            MetadataEntry { key: TRUST_VC_DIGEST_METADATA_KEY.to_string(), value: vc_digest },
        ];
        metadata.extend(hardened_vc_metadata(&vc.kind));
        metadata.extend(ty_temporal_model_metadata(&vc.kind));
        metadata.extend(vc_engine_formula_metadata(
            &obligation_kind,
            &vc.kind,
            &vc_formula_payload.schema,
        ));
        metadata.extend(vc_formula_payload.into_metadata());
        metadata.extend(mir_memory_metadata);
        let required_strength = trust_vc_mir_memory_required_strength(&obligation_kind);
        let source_contract_binding = validated_vc_source_contract_binding(
            function,
            compiler_contracts,
            vc,
            target_pointer_width_bits,
            Some(&lowered_contracts),
        );
        // A body decline binds its authored question, but deliberately does
        // not enter the ordinary body-proof role/translation relation above.
        let source_decline_binding = body_decline::source_body_decline_transport(
            function,
            compiler_contracts,
            vc,
            &function_context,
            &source_digest,
            target_pointer_width_bits,
        );
        if let Some(binding) = &source_contract_binding {
            metadata.extend([
                MetadataEntry {
                    key: TRUST_VC_SOURCE_CONTRACT_INDEX_METADATA_KEY.to_string(),
                    value: binding.index.to_string(),
                },
                MetadataEntry {
                    key: TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY.to_string(),
                    value: binding.predicate_digest.clone(),
                },
                MetadataEntry {
                    key: TRUST_VC_SOURCE_CONTRACT_ROLE_METADATA_KEY.to_string(),
                    value: binding.role.to_string(),
                },
            ]);
        }
        if let Some(binding) = &source_decline_binding {
            metadata.extend(binding.metadata.iter().cloned());
        }
        bundle.obligations.push(TrustObligation {
            obligation_id: format!(
                "vc:{}:{}:{}",
                def_path_id,
                obligation_kind_label(&obligation_kind),
                index
            ),
            kind: obligation_kind,
            contract_id: source_contract_binding
                .map(|binding| binding.contract_id)
                .or_else(|| source_decline_binding.map(|binding| binding.contract_id)),
            proof_item_id: None,
            source: source_location(&vc.location),
            description: vc.kind.description(),
            required_strength,
            summary_facts: Vec::new(),
            metadata,
        });
    }

    if excluded_definition_site_preconditions > 0 {
        bundle.metadata.push(MetadataEntry {
            key: "trust.contract.definition_site_preconditions_excluded".to_string(),
            value: excluded_definition_site_preconditions.to_string(),
        });
    }

    bundle
}

/// Convert contracts and VCs with loop feedback and the complete rustc crate
/// identity.
///
/// `target_pointer_width_bits` follows the
/// [`contract_bundle_to_verifier_api_with_compiler_identity`] contract: the
/// target's pointer width in bits, or `None` to fail pointer-sized quantifier
/// binders closed.
#[must_use]
pub fn function_to_verifier_api_bundle_with_loop_feedback_candidates_and_compiler_identity(
    function: &VerifiableFunction,
    compiler_contracts: &CompilerContractBundle,
    vcs: &[VerificationCondition],
    feedback: &[trust_vcgen::LoopInvariantFeedbackCandidate],
    crate_name: &str,
    stable_crate_id: u64,
    target_pointer_width_bits: Option<u32>,
) -> TrustContractBundle {
    let mut bundle = function_to_verifier_api_bundle_for_target(
        function,
        compiler_contracts,
        vcs,
        feedback,
        crate_name,
        target_pointer_width_bits,
    );
    bind_compiler_crate_identity(&mut bundle, function, stable_crate_id);
    bundle
}

/// Project one exact compiler-owned typed contract into the public predicate schema.
///
/// This reads the query bundle alone: no MIR body, source-text fallback or inferred
/// local names participate. Missing, duplicate or stale proposition provenance
/// returns `None`. An exact proposition outside the supported semantic fragment
/// returns the same visible Unsupported predicate as the ordinary catalog path.
/// The output describes a question and grants no proof authority.
#[must_use]
pub fn compiler_typed_contract_predicate(
    compiler_contracts: &CompilerContractBundle,
    source_contract_index: usize,
) -> Option<(ContractPredicate, Option<String>, &'static str)> {
    let contract = compiler_contracts.contracts.get(source_contract_index)?;
    let proposition = compiler_contracts.typed_proposition(source_contract_index, contract)?;
    Some(lower_typed_contract_predicate(contract, proposition))
}

fn lower_typed_contract_predicate(
    contract: &Contract,
    proposition: &trust_types::CompilerContractProposition,
) -> (ContractPredicate, Option<String>, &'static str) {
    // A compiler-owned typed proposition is the structural semantic carrier;
    // its source text is diagnostics only. Prefer that exact indexed formula
    // over reparsing the spelling through the narrower public source AST. This
    // is what lets native `xs.len()` cross as its unambiguous `xs_len` leaf
    // without pretending a method call is a field projection. The existing
    // typed-proposition digest binds source index, formula, and exact source
    // domains. An arithmetic clause whose variable-domain sidecar resolves to
    // ONE machine width/signedness is lowered at that DECLARED width with
    // wrapping BV semantics (ratified L1 rule 4 — the type-directed Machine{w}
    // reading; `Int`-sort arithmetic would re-derive the `result + 1 > result`
    // false positive, a widened non-wrapping BV likewise). Anything the
    // machine elaboration cannot express keeps the visible fail-closed
    // `unsupported_machine_arithmetic` row. The one Int-exact exception is an
    // unsigned bare variable `%` a positive in-domain literal: the shared
    // definedness check retains its original typed formula and digest.
    if typed_formula_uses_unmodeled_machine_arithmetic(
        &proposition.formula,
        &proposition.variable_domains,
    ) {
        if let Some(machine) = machine_width_proposition_formula(proposition) {
            if let Some(predicate) = trust_spec_predicate_from_formula(&machine) {
                if let Ok(predicate) = predicate.into_contract_predicate() {
                    return (predicate, None, "typed_proposition_machine_width");
                }
            }
        }
        let reason = format!(
            "compiler-lowered contract predicate `{}` uses arithmetic whose domain is not preserved by the verifier API",
            contract.body
        );
        return (
            ContractPredicate::Unsupported { reason: reason.clone() },
            Some(reason),
            UNMODELED_CONTRACT_ARITHMETIC_LOWERING,
        );
    }
    if let Some(predicate) = trust_spec_predicate_from_formula(&proposition.formula) {
        match predicate.into_contract_predicate() {
            Ok(predicate) => return (predicate, None, "typed_proposition"),
            Err(error) => {
                let reason = format!(
                    "compiler-owned typed proposition for `{}` could not be serialized: {error}",
                    contract.body
                );
                return (
                    ContractPredicate::Unsupported { reason: reason.clone() },
                    Some(reason),
                    "unsupported",
                );
            }
        }
    }
    let reason = format!(
        "compiler-owned typed proposition for `{}` is outside the public verifier formula subset",
        contract.body
    );
    return (
        ContractPredicate::Unsupported { reason: reason.clone() },
        Some(reason),
        "unsupported",
    );
}

fn lower_contract_predicate(
    function: &VerifiableFunction,
    contract: &Contract,
    typed_proposition: Option<&trust_types::CompilerContractProposition>,
    target_pointer_width_bits: Option<u32>,
) -> (ContractPredicate, Option<String>, &'static str) {
    if let Some(reason) = contract.body.strip_prefix(UNSUPPORTED_COMPILER_CONTRACT_PREFIX) {
        let reason = format!(
            "compiler contract predicate was not lowered into a typed verifier formula: {reason}"
        );
        return (
            ContractPredicate::Unsupported { reason: reason.clone() },
            Some(reason),
            "unsupported",
        );
    }

    if let Some(proposition) = typed_proposition {
        return lower_typed_contract_predicate(contract, proposition);
    }

    if let Some(body) = contract.body.strip_prefix(LOWERED_COMPILER_CONTRACT_PREFIX) {
        return lower_simple_contract_expr(function, contract, body, target_pointer_width_bits);
    }

    match contract.body.trim() {
        "true" => (trust_ir_bool_literal(true), None, "bool_literal"),
        "false" => (trust_ir_bool_literal(false), None, "bool_literal"),
        "" => {
            let reason = "empty compiler contract predicate was not lowered".to_string();
            (ContractPredicate::Unsupported { reason: reason.clone() }, Some(reason), "unsupported")
        }
        body => {
            let reason = format!(
                "compiler contract predicate `{body}` was not lowered into a typed verifier formula"
            );
            (ContractPredicate::Unsupported { reason: reason.clone() }, Some(reason), "unsupported")
        }
    }
}

fn typed_formula_uses_unmodeled_machine_arithmetic(
    formula: &Formula,
    variable_domains: &[trust_types::CompilerContractVariableDomain],
) -> bool {
    if trust_types::unsigned_literal_remainder_is_exact(formula, |name| {
        use trust_types::CompilerContractValueDomain as Domain;
        let mut matches = variable_domains.iter().filter(|row| row.name == name);
        let row = matches.next()?;
        if matches.next().is_some() {
            return None;
        }
        match row.domain {
            Domain::MachineInt { width, signed } => Some((width, signed)),
            // Match vcgen's fixed-width fragment. Its function carrier has no
            // target pointer width, so a pointer-sized source stays refused.
            _ => None,
        }
    }) {
        return false;
    }
    // No outer variable-domain entry authorizes a similarly named bound Int.
    let variable_domains = if matches!(formula, Formula::Forall(..) | Formula::Exists(..)) {
        &[]
    } else {
        variable_domains
    };
    matches!(
        formula,
        Formula::Add(..)
            | Formula::Sub(..)
            | Formula::Mul(..)
            | Formula::Div(..)
            | Formula::Rem(..)
            | Formula::Neg(..)
    ) || !trust_types::all_formula_children(formula, |child| {
        !typed_formula_uses_unmodeled_machine_arithmetic(child, variable_domains)
    })
}

/// Lower an arithmetic-bearing compiler proposition into its declared-width
/// Machine{w} (wrapping BV) reading — ratified L1 rule 4's type-directed
/// domain. `None` (the caller keeps the visible fail-closed row) unless every
/// non-`Bool` variable in the domain sidecar shares ONE `(width, signed)`
/// machine domain, every literal has a pattern at that width, and the clause
/// stays inside the wrap-exact fragment: `+`/`-`/`*`/unary `-`, comparisons
/// (signedness-corrected), equality, boolean connectives. Spec-level `/` is
/// refused; `%` requires a positive representable literal divisor — SMT's
/// total operations assign trapping inputs a value. The shared literal-remainder
/// check excludes zero and signed MIN % -1 for every dividend in this domain.
fn machine_width_proposition_formula(
    proposition: &trust_types::CompilerContractProposition,
) -> Option<Formula> {
    use trust_types::CompilerContractValueDomain as Domain;
    let mut machine: Option<(u32, bool)> = None;
    let mut bools = std::collections::BTreeSet::new();
    for row in &proposition.variable_domains {
        match row.domain {
            Domain::Bool => {
                bools.insert(row.name.as_str());
            }
            // This lane rewrites a proposition into DECLARED-WIDTH machine
            // integer arithmetic. A float has no such width, and the two's
            // complement pattern below would be a type confusion over its bits,
            // so the whole proposition declines rather than translating part of
            // it — the same fail-closed answer a mathematical int gets.
            Domain::MathematicalInt | Domain::Float { .. } => return None,
            Domain::PointerSizedInt { width, signed } | Domain::MachineInt { width, signed } => {
                match machine {
                    None => machine = Some((width, signed)),
                    Some(existing) if existing == (width, signed) => {}
                    Some(_) => return None,
                }
            }
        }
    }
    let (width, signed) = machine?;
    machine_width_translate_prop(&proposition.formula, width, signed, &bools)
}

/// The literal's `width`-bit two's-complement pattern, `None` when out of the
/// declared domain. Stored non-negative so downstream bridges never see a sign.
fn machine_width_literal_pattern(value: i128, width: u32, signed: bool) -> Option<i128> {
    if width == 0 || width > 128 {
        return None;
    }
    if signed {
        let min = if width == 128 { i128::MIN } else { -(1_i128 << (width - 1)) };
        let max = if width == 128 { i128::MAX } else { (1_i128 << (width - 1)) - 1 };
        if value < min || value > max {
            return None;
        }
    } else {
        if value < 0 {
            return None;
        }
        if width < 128 && u128::try_from(value).ok()? >= (1_u128 << width) {
            return None;
        }
    }
    if value >= 0 {
        return Some(value);
    }
    if width == 128 {
        return None;
    }
    Some(value + (1_i128 << width))
}

fn machine_width_translate_prop(
    formula: &Formula,
    width: u32,
    signed: bool,
    bools: &std::collections::BTreeSet<&str>,
) -> Option<Formula> {
    let prop = |f: &Formula| machine_width_translate_prop(f, width, signed, bools);
    let value = |f: &Formula| machine_width_translate_value(f, width, signed, bools);
    let value_pair = |a: &Formula, b: &Formula| -> Option<(Box<Formula>, Box<Formula>)> {
        Some((Box::new(value(a)?), Box::new(value(b)?)))
    };
    let is_prop_operand = |f: &Formula| -> bool {
        match f {
            Formula::Bool(_)
            | Formula::Not(_)
            | Formula::And(_)
            | Formula::Or(_)
            | Formula::Implies(..)
            | Formula::Eq(..)
            | Formula::Lt(..)
            | Formula::Le(..)
            | Formula::Gt(..)
            | Formula::Ge(..) => true,
            Formula::Var(name, _) => bools.contains(name.as_str()),
            Formula::SymVar(sym, _) => bools.contains(sym.as_str()),
            _ => false,
        }
    };
    Some(match formula {
        Formula::Bool(b) => Formula::Bool(*b),
        Formula::Var(name, _) if bools.contains(name.as_str()) => {
            Formula::Var(name.clone(), Sort::Bool)
        }
        Formula::SymVar(sym, _) if bools.contains(sym.as_str()) => {
            Formula::Var(sym.as_str().to_string(), Sort::Bool)
        }
        Formula::Not(a) => Formula::Not(Box::new(prop(a)?)),
        Formula::And(xs) => Formula::And(xs.iter().map(prop).collect::<Option<Vec<_>>>()?),
        Formula::Or(xs) => Formula::Or(xs.iter().map(prop).collect::<Option<Vec<_>>>()?),
        Formula::Implies(a, b) => Formula::Implies(Box::new(prop(a)?), Box::new(prop(b)?)),
        Formula::Eq(a, b) => {
            if is_prop_operand(a) || is_prop_operand(b) {
                Formula::Eq(Box::new(prop(a)?), Box::new(prop(b)?))
            } else {
                let (a, b) = value_pair(a, b)?;
                Formula::Eq(a, b)
            }
        }
        Formula::Lt(a, b) => {
            let (a, b) = value_pair(a, b)?;
            if signed { Formula::BvSLt(a, b, width) } else { Formula::BvULt(a, b, width) }
        }
        Formula::Le(a, b) => {
            let (a, b) = value_pair(a, b)?;
            if signed { Formula::BvSLe(a, b, width) } else { Formula::BvULe(a, b, width) }
        }
        Formula::Gt(a, b) => {
            let (a, b) = value_pair(a, b)?;
            if signed { Formula::BvSLt(b, a, width) } else { Formula::BvULt(b, a, width) }
        }
        Formula::Ge(a, b) => {
            let (a, b) = value_pair(a, b)?;
            if signed { Formula::BvSLe(b, a, width) } else { Formula::BvULe(b, a, width) }
        }
        _ => return None,
    })
}

fn machine_width_translate_value(
    formula: &Formula,
    width: u32,
    signed: bool,
    bools: &std::collections::BTreeSet<&str>,
) -> Option<Formula> {
    let value = |f: &Formula| machine_width_translate_value(f, width, signed, bools);
    let value_pair = |a: &Formula, b: &Formula| -> Option<(Box<Formula>, Box<Formula>)> {
        Some((Box::new(value(a)?), Box::new(value(b)?)))
    };
    Some(match formula {
        Formula::Var(name, _) if !bools.contains(name.as_str()) => {
            Formula::Var(name.clone(), Sort::BitVec(width))
        }
        Formula::SymVar(sym, _) if !bools.contains(sym.as_str()) => {
            Formula::Var(sym.as_str().to_string(), Sort::BitVec(width))
        }
        Formula::Int(n) => {
            Formula::BitVec { value: machine_width_literal_pattern(*n, width, signed)?, width }
        }
        Formula::UInt(n) => Formula::BitVec {
            value: machine_width_literal_pattern(i128::try_from(*n).ok()?, width, signed)?,
            width,
        },
        Formula::Add(a, b) => {
            let (a, b) = value_pair(a, b)?;
            Formula::BvAdd(a, b, width)
        }
        Formula::Sub(a, b) => {
            let (a, b) = value_pair(a, b)?;
            Formula::BvSub(a, b, width)
        }
        Formula::Mul(a, b) => {
            let (a, b) = value_pair(a, b)?;
            Formula::BvMul(a, b, width)
        }
        Formula::Rem(a, b) if trust_types::is_total_machine_remainder_divisor(b, width, signed) => {
            let (a, b) = value_pair(a, b)?;
            if signed { Formula::BvSRem(a, b, width) } else { Formula::BvURem(a, b, width) }
        }
        Formula::Neg(a) => Formula::BvSub(
            Box::new(Formula::BitVec { value: 0, width }),
            Box::new(value(a)?),
            width,
        ),
        _ => return None,
    })
}

fn lower_simple_contract_expr(
    function: &VerifiableFunction,
    contract: &Contract,
    body: &str,
    target_pointer_width_bits: Option<u32>,
) -> (ContractPredicate, Option<String>, &'static str) {
    let attr = parse_spec_attr(contract.kind.attr_name(), body);
    let Ok(attr) = attr else {
        let reason = format!(
            "compiler-lowered contract predicate `{body}` is outside the verifier API subset"
        );
        return (
            ContractPredicate::Unsupported { reason: reason.clone() },
            Some(reason),
            "unsupported",
        );
    };
    let supported_kind = matches!(
        (&attr, contract.kind),
        (HighLevelSpecAttr::Requires(_), TrustTypesContractKind::Requires)
            | (HighLevelSpecAttr::Ensures(_), TrustTypesContractKind::Ensures)
    );
    if !supported_kind {
        let reason = format!(
            "compiler-lowered contract predicate `{body}` has mismatched contract kind {:?}",
            contract.kind
        );
        return (
            ContractPredicate::Unsupported { reason: reason.clone() },
            Some(reason),
            "unsupported",
        );
    }

    let spec_expr = match &attr {
        HighLevelSpecAttr::Requires(expr)
        | HighLevelSpecAttr::Ensures(expr)
        | HighLevelSpecAttr::Invariant(expr)
        | HighLevelSpecAttr::Decreases(expr) => expr,
        HighLevelSpecAttr::Pure | HighLevelSpecAttr::Trusted => {
            let reason = format!(
                "compiler-lowered contract predicate `{body}` is not an expression predicate"
            );
            return (
                ContractPredicate::Unsupported { reason: reason.clone() },
                Some(reason),
                "unsupported",
            );
        }
        _ => {
            let reason = format!(
                "compiler-lowered contract predicate `{body}` uses an unsupported spec attribute"
            );
            return (
                ContractPredicate::Unsupported { reason: reason.clone() },
                Some(reason),
                "unsupported",
            );
        }
    };

    // The public TrustSpec payload has only one undifferentiated `Int` sort.
    // Lowering a Rust-machine clause such as `x + 1 > x` through it would turn
    // wrapping arithmetic into a mathematical tautology and could let the full
    // verifier regain proof authority after vcgen correctly declined the same
    // clause.  Until this bridge carries the source domain/width, reject every
    // arithmetic node recursively.  This is intentionally conservative for
    // future explicit `int`/`nat` source terms: losing a proof is sound; giving
    // a machine term the wrong arithmetic is not.
    if spec_expr_uses_unmodeled_machine_arithmetic(spec_expr) {
        let reason = format!(
            "compiler-lowered contract predicate `{body}` uses arithmetic whose domain is not preserved by the verifier API"
        );
        return (
            ContractPredicate::Unsupported { reason: reason.clone() },
            Some(reason),
            UNMODELED_CONTRACT_ARITHMETIC_LOWERING,
        );
    }

    match trust_spec_predicate(function, spec_expr, target_pointer_width_bits) {
        Ok(predicate) => (predicate, None, "spec_expr"),
        Err(reason) => {
            let reason =
                format!("compiler-lowered contract predicate `{body}` is untyped: {reason}");
            (ContractPredicate::Unsupported { reason: reason.clone() }, Some(reason), "unsupported")
        }
    }
}

fn spec_expr_uses_unmodeled_machine_arithmetic(expr: &SpecExpr) -> bool {
    match expr {
        SpecExpr::BinOp { lhs, op, rhs } => {
            matches!(
                op,
                SpecBinOp::Add | SpecBinOp::Sub | SpecBinOp::Mul | SpecBinOp::Div | SpecBinOp::Mod
            ) || spec_expr_uses_unmodeled_machine_arithmetic(lhs)
                || spec_expr_uses_unmodeled_machine_arithmetic(rhs)
        }
        SpecExpr::UnaryOp { op, expr } => {
            matches!(op, SpecUnaryOp::Neg) || spec_expr_uses_unmodeled_machine_arithmetic(expr)
        }
        SpecExpr::FnCall { args, .. } => {
            args.iter().any(spec_expr_uses_unmodeled_machine_arithmetic)
        }
        SpecExpr::Forall { body, .. } | SpecExpr::Exists { body, .. } | SpecExpr::Old(body) => {
            spec_expr_uses_unmodeled_machine_arithmetic(body)
        }
        SpecExpr::Field { base, .. } | SpecExpr::MethodCall { base, .. } => {
            spec_expr_uses_unmodeled_machine_arithmetic(base)
        }
        SpecExpr::Index { base, index } | SpecExpr::Implies { lhs: base, rhs: index } => {
            spec_expr_uses_unmodeled_machine_arithmetic(base)
                || spec_expr_uses_unmodeled_machine_arithmetic(index)
        }
        // `SpecExpr::FloatLit` lands here: a negative float literal such as
        // `-(1.0e30)` is folded by the spec parser into sign-flipped literal
        // bits before reaching this check, so it is a constant, not
        // arithmetic. `Neg` applied to any non-literal float expression still
        // arrives as `UnaryOp { op: Neg, .. }` and is rejected above.
        _ => false,
    }
}

fn trust_ir_bool_literal(value: bool) -> ContractPredicate {
    TrustSpecPredicate::new(TrustSpecExpr::bool_literal(value), Vec::new())
        .into_contract_predicate()
        .expect("typed bool predicate serializes")
}

fn trust_spec_predicate(
    function: &VerifiableFunction,
    expr: &SpecExpr,
    target_pointer_width_bits: Option<u32>,
) -> Result<ContractPredicate, String> {
    let mut lowerer = SpecExprLowerer::new(function, target_pointer_width_bits);
    let root = lowerer.lower_expr(expr, Some(TrustSpecSort::Bool))?;
    if root.sort != TrustSpecSort::Bool {
        return Err(format!("predicate root has sort {:?}, expected bool", root.sort));
    }
    let predicate = TrustSpecPredicate::new(root, lowerer.into_variables());
    predicate.into_contract_predicate().map_err(|err| err.to_string())
}

struct SpecExprLowerer {
    locals: BTreeMap<String, (TrustSpecSort, usize)>,
    return_sort: Option<TrustSpecSort>,
    variables: BTreeMap<String, TrustSpecVariable>,
    quantified: BTreeMap<String, TrustSpecSort>,
    /// Compilation-target pointer width for `usize`/`isize` binders; `None`
    /// (the caller could not name the target) fails those binders closed.
    target_pointer_width_bits: Option<u32>,
}

impl SpecExprLowerer {
    fn new(function: &VerifiableFunction, target_pointer_width_bits: Option<u32>) -> Self {
        let locals = function
            .body
            .locals
            .iter()
            .filter_map(|local| {
                let name = local.name.as_ref()?;
                let sort = ty_to_spec_sort(&local.ty)?;
                Some((name.clone(), (sort, local.index)))
            })
            .collect();
        Self {
            locals,
            return_sort: ty_to_spec_sort(&function.body.return_ty),
            variables: BTreeMap::new(),
            quantified: BTreeMap::new(),
            target_pointer_width_bits,
        }
    }

    fn into_variables(self) -> Vec<TrustSpecVariable> {
        self.variables.into_values().collect()
    }

    fn lower_expr(
        &mut self,
        expr: &SpecExpr,
        expected: Option<TrustSpecSort>,
    ) -> Result<TrustSpecExpr, String> {
        let lowered = match expr {
            SpecExpr::BoolLit(value) => TrustSpecExpr::bool_literal(*value),
            SpecExpr::IntLit(value) => TrustSpecExpr::int_literal(value.to_string()),
            SpecExpr::UIntLit(value) => TrustSpecExpr::int_literal(value.to_string()),
            // `SpecExpr::FloatLit` always carries IEEE-754 binary64 bits (the
            // spec parser folds `-<literal>` into sign-flipped bits before it
            // reaches this converter), so the raw bits transfer exactly —
            // never through a decimal round-trip. An f32-typed context is NOT
            // narrowed here: the sort mismatch fails the contract closed
            // rather than re-rounding the constant.
            SpecExpr::FloatLit(bits) => TrustSpecExpr::float_literal(*bits, 11, 53),
            SpecExpr::Var(name) => {
                let (sort, origin) = self.variable_sort(name, expected)?;
                self.record_variable(name, sort, origin)?;
                TrustSpecExpr::variable(name.clone(), sort)
            }
            SpecExpr::UnaryOp { op, expr } => match op {
                SpecUnaryOp::Not => {
                    let expr = self.lower_expr(expr, Some(TrustSpecSort::Bool))?;
                    TrustSpecExpr::unary(TrustSpecUnaryOp::Not, expr)
                }
                SpecUnaryOp::Neg => {
                    let expr = self.lower_expr(expr, Some(TrustSpecSort::Int))?;
                    TrustSpecExpr::unary(TrustSpecUnaryOp::Neg, expr)
                }
                _ => return Err("unsupported unary spec operator".to_string()),
            },
            SpecExpr::BinOp { lhs, op, rhs } => self.lower_binary_expr(lhs, *op, rhs)?,
            SpecExpr::Implies { lhs, rhs } => {
                let lhs = self.lower_expr(lhs, Some(TrustSpecSort::Bool))?;
                let rhs = self.lower_expr(rhs, Some(TrustSpecSort::Bool))?;
                TrustSpecExpr::binary(TrustSpecBinaryOp::Implies, lhs, rhs)
            }
            SpecExpr::Old(inner) => {
                let inner = self.lower_expr(inner, expected)?;
                TrustSpecExpr::old(inner)
            }
            SpecExpr::Result => {
                let sort = self
                    .return_sort
                    .or(expected)
                    .ok_or_else(|| "cannot infer `result` sort".to_string())?;
                TrustSpecExpr::result(sort)
            }
            SpecExpr::Field { base, field } => {
                let sort = expected
                    .ok_or_else(|| format!("cannot infer sort for field access `.{field}`"))?;
                let base = self.lower_expr(base, None)?;
                TrustSpecExpr::field(base, field.clone(), sort)
            }
            SpecExpr::MethodCall { method, .. } => {
                // A call and a field projection are different semantic nodes.
                // The current public verifier schema has no typed method-call
                // carrier, so aliasing `x.m()` to `x.m` would let downstream
                // proof engines interpret a call as an uninterpreted selector.
                return Err(format!(
                    "method call `.{method}()` has no distinct typed verifier payload yet"
                ));
            }
            SpecExpr::Index { base, index } => {
                let sort = expected
                    .ok_or_else(|| "cannot infer sort for indexed expression".to_string())?;
                let base = self.lower_expr(base, None)?;
                let index = self.lower_expr(index, Some(TrustSpecSort::Int))?;
                TrustSpecExpr::index(base, index, sort)
            }
            SpecExpr::Forall { var, ty, body } => self.lower_quantifier(true, var, ty, body)?,
            SpecExpr::Exists { var, ty, body } => self.lower_quantifier(false, var, ty, body)?,
            SpecExpr::FnCall { name, .. } => {
                return Err(format!("function call `{name}` has no typed verifier payload yet"));
            }
            _ => return Err("unsupported spec expression node".to_string()),
        };

        ensure_expected_sort(&lowered, expected)?;
        Ok(lowered)
    }

    fn lower_binary_expr(
        &mut self,
        lhs: &SpecExpr,
        op: SpecBinOp,
        rhs: &SpecExpr,
    ) -> Result<TrustSpecExpr, String> {
        let op =
            spec_binary_op(op).ok_or_else(|| "unsupported binary spec operator".to_string())?;
        let (lhs_expected, rhs_expected) = match op {
            // Arithmetic never types floats: float `Add`/`Sub`/`Mul`/`Div`
            // need rounding-mode semantics the public IR does not carry, and
            // the recursive `spec_expr_uses_unmodeled_machine_arithmetic`
            // rejection upstream already refused those nodes.
            TrustSpecBinaryOp::Add
            | TrustSpecBinaryOp::Sub
            | TrustSpecBinaryOp::Mul
            | TrustSpecBinaryOp::Div
            | TrustSpecBinaryOp::Mod => (Some(TrustSpecSort::Int), Some(TrustSpecSort::Int)),
            // Ordered comparisons default to Int; when either operand is
            // hinted at an IEEE float sort (an f32/f64 local or a float
            // literal), require that exact float sort on BOTH sides. A
            // mixed-format comparison then fails the sort check closed.
            TrustSpecBinaryOp::Lt
            | TrustSpecBinaryOp::Le
            | TrustSpecBinaryOp::Gt
            | TrustSpecBinaryOp::Ge => match self.equality_operand_sort(lhs, rhs) {
                Some(sort @ TrustSpecSort::Float { .. }) => (Some(sort), Some(sort)),
                _ => (Some(TrustSpecSort::Int), Some(TrustSpecSort::Int)),
            },
            TrustSpecBinaryOp::And | TrustSpecBinaryOp::Or | TrustSpecBinaryOp::Implies => {
                (Some(TrustSpecSort::Bool), Some(TrustSpecSort::Bool))
            }
            TrustSpecBinaryOp::Eq | TrustSpecBinaryOp::Ne => {
                let sort = self.equality_operand_sort(lhs, rhs).unwrap_or(TrustSpecSort::Int);
                (Some(sort), Some(sort))
            }
            _ => return Err("unsupported Trust spec binary operator".to_string()),
        };
        let lhs = self.lower_expr(lhs, lhs_expected)?;
        let rhs = self.lower_expr(rhs, rhs_expected)?;
        Ok(TrustSpecExpr::binary(op, lhs, rhs))
    }

    fn lower_quantifier(
        &mut self,
        is_forall: bool,
        var: &str,
        ty: &str,
        body: &SpecExpr,
    ) -> Result<TrustSpecExpr, String> {
        let (sort, domain) = spec_quantifier_sort_domain(ty, self.target_pointer_width_bits)
            .ok_or_else(|| format!("quantified variable `{var}` has unsupported type `{ty}`"))?;
        let previous = self.quantified.insert(var.to_string(), sort);
        self.record_variable(var, sort, TrustSpecVariableOrigin::Quantified)?;
        let body = self.lower_expr(body, Some(TrustSpecSort::Bool));
        if let Some(previous) = previous {
            self.quantified.insert(var.to_string(), previous);
        } else {
            self.quantified.remove(var);
        }
        let mut body = body?;
        if let Some(domain) = domain {
            let guard = domain.guard(TrustSpecExpr::variable(var, sort));
            body = TrustSpecExpr::binary(
                if is_forall { TrustSpecBinaryOp::Implies } else { TrustSpecBinaryOp::And },
                guard,
                body,
            );
        }
        Ok(TrustSpecExpr::quantifier(
            if is_forall { TrustSpecQuantifier::Forall } else { TrustSpecQuantifier::Exists },
            var.to_string(),
            sort,
            body,
        ))
    }

    fn variable_sort(
        &self,
        name: &str,
        expected: Option<TrustSpecSort>,
    ) -> Result<(TrustSpecSort, TrustSpecVariableOrigin), String> {
        if let Some(sort) = self.quantified.get(name).copied() {
            return Ok((sort, TrustSpecVariableOrigin::Quantified));
        }
        if let Some((sort, index)) = self.locals.get(name).copied() {
            return Ok((sort, TrustSpecVariableOrigin::Local { index }));
        }
        expected
            .map(|sort| (sort, TrustSpecVariableOrigin::Inferred))
            .ok_or_else(|| format!("cannot infer sort for variable `{name}`"))
    }

    fn record_variable(
        &mut self,
        name: &str,
        sort: TrustSpecSort,
        origin: TrustSpecVariableOrigin,
    ) -> Result<(), String> {
        if let Some(existing) = self.variables.get(name) {
            if existing.sort != sort {
                return Err(format!(
                    "variable `{name}` has conflicting sorts {:?} and {:?}",
                    existing.sort, sort
                ));
            }
            return Ok(());
        }
        self.variables
            .insert(name.to_string(), TrustSpecVariable { name: name.to_string(), sort, origin });
        Ok(())
    }

    fn equality_operand_sort(&self, lhs: &SpecExpr, rhs: &SpecExpr) -> Option<TrustSpecSort> {
        self.expression_sort_hint(lhs).or_else(|| self.expression_sort_hint(rhs))
    }

    fn expression_sort_hint(&self, expr: &SpecExpr) -> Option<TrustSpecSort> {
        match expr {
            SpecExpr::BoolLit(_) => Some(TrustSpecSort::Bool),
            SpecExpr::IntLit(_) | SpecExpr::UIntLit(_) => Some(TrustSpecSort::Int),
            // Spec float literals are always binary64 (see `lower_expr`).
            SpecExpr::FloatLit(_) => Some(TrustSpecSort::Float { eb: 11, sb: 53 }),
            SpecExpr::Var(name) => self
                .quantified
                .get(name)
                .copied()
                .or_else(|| self.locals.get(name).map(|(sort, _)| *sort)),
            SpecExpr::Result => self.return_sort,
            SpecExpr::UnaryOp { op: SpecUnaryOp::Not, .. }
            | SpecExpr::Implies { .. }
            | SpecExpr::Forall { .. }
            | SpecExpr::Exists { .. } => Some(TrustSpecSort::Bool),
            SpecExpr::UnaryOp { op: SpecUnaryOp::Neg, .. } => Some(TrustSpecSort::Int),
            SpecExpr::BinOp { op, .. } => spec_binary_op(*op).map(TrustSpecBinaryOp::result_sort),
            SpecExpr::Old(inner) => self.expression_sort_hint(inner),
            SpecExpr::Field { .. }
            | SpecExpr::MethodCall { .. }
            | SpecExpr::Index { .. }
            | SpecExpr::FnCall { .. } => None,
            _ => None,
        }
    }
}

fn ensure_expected_sort(
    expr: &TrustSpecExpr,
    expected: Option<TrustSpecSort>,
) -> Result<(), String> {
    if let Some(expected) = expected {
        if expr.sort != expected {
            return Err(format!("expected {expected:?}, got {:?}", expr.sort));
        }
    }
    Ok(())
}

fn spec_binary_op(op: SpecBinOp) -> Option<TrustSpecBinaryOp> {
    match op {
        SpecBinOp::Add => Some(TrustSpecBinaryOp::Add),
        SpecBinOp::Sub => Some(TrustSpecBinaryOp::Sub),
        SpecBinOp::Mul => Some(TrustSpecBinaryOp::Mul),
        SpecBinOp::Div => Some(TrustSpecBinaryOp::Div),
        SpecBinOp::Mod => Some(TrustSpecBinaryOp::Mod),
        SpecBinOp::Eq => Some(TrustSpecBinaryOp::Eq),
        SpecBinOp::Ne => Some(TrustSpecBinaryOp::Ne),
        SpecBinOp::Lt => Some(TrustSpecBinaryOp::Lt),
        SpecBinOp::Le => Some(TrustSpecBinaryOp::Le),
        SpecBinOp::Gt => Some(TrustSpecBinaryOp::Gt),
        SpecBinOp::Ge => Some(TrustSpecBinaryOp::Ge),
        SpecBinOp::And => Some(TrustSpecBinaryOp::And),
        SpecBinOp::Or => Some(TrustSpecBinaryOp::Or),
        _ => None,
    }
}

fn ty_to_spec_sort(ty: &Ty) -> Option<TrustSpecSort> {
    match ty {
        Ty::Bool => Some(TrustSpecSort::Bool),
        Ty::Int { .. } => Some(TrustSpecSort::Int),
        // The two Rust machine float shapes, in the trust-types `Sort::Float
        // { eb, sb }` representation. Any other width fails closed (`None`):
        // losing a proof is sound; guessing a format is not.
        Ty::Float { width: 32 } => Some(TrustSpecSort::Float { eb: 8, sb: 24 }),
        Ty::Float { width: 64 } => Some(TrustSpecSort::Float { eb: 11, sb: 53 }),
        _ => None,
    }
}

#[derive(Clone, Copy)]
enum SpecQuantifierDomain {
    NonNegative,
    Inclusive { min: i128, max: i128 },
    UnsignedInclusive { max: u128 },
}

impl SpecQuantifierDomain {
    fn guard(self, variable: TrustSpecExpr) -> TrustSpecExpr {
        let lower = match self {
            Self::NonNegative | Self::UnsignedInclusive { .. } => "0".to_string(),
            Self::Inclusive { min, .. } => min.to_string(),
        };
        let lower = TrustSpecExpr::binary(
            TrustSpecBinaryOp::Ge,
            variable.clone(),
            TrustSpecExpr::int_literal(lower),
        );
        match self {
            Self::NonNegative => lower,
            Self::Inclusive { max, .. } => TrustSpecExpr::binary(
                TrustSpecBinaryOp::And,
                lower,
                TrustSpecExpr::binary(
                    TrustSpecBinaryOp::Le,
                    variable,
                    TrustSpecExpr::int_literal(max.to_string()),
                ),
            ),
            Self::UnsignedInclusive { max } => TrustSpecExpr::binary(
                TrustSpecBinaryOp::And,
                lower,
                TrustSpecExpr::binary(
                    TrustSpecBinaryOp::Le,
                    variable,
                    TrustSpecExpr::int_literal(max.to_string()),
                ),
            ),
        }
    }
}

fn spec_quantifier_sort_domain(
    ty: &str,
    target_pointer_width_bits: Option<u32>,
) -> Option<(TrustSpecSort, Option<SpecQuantifierDomain>)> {
    let int = |domain| Some((TrustSpecSort::Int, domain));
    match ty {
        "bool" | "Bool" => Some((TrustSpecSort::Bool, None)),
        "int" | "Int" => int(None),
        "nat" | "Nat" => int(Some(SpecQuantifierDomain::NonNegative)),
        "i8" => {
            int(Some(SpecQuantifierDomain::Inclusive { min: i8::MIN.into(), max: i8::MAX.into() }))
        }
        "i16" => int(Some(SpecQuantifierDomain::Inclusive {
            min: i16::MIN.into(),
            max: i16::MAX.into(),
        })),
        "i32" => int(Some(SpecQuantifierDomain::Inclusive {
            min: i32::MIN.into(),
            max: i32::MAX.into(),
        })),
        "i64" => int(Some(SpecQuantifierDomain::Inclusive {
            min: i64::MIN.into(),
            max: i64::MAX.into(),
        })),
        "i128" => int(Some(SpecQuantifierDomain::Inclusive { min: i128::MIN, max: i128::MAX })),
        "u8" => int(Some(SpecQuantifierDomain::UnsignedInclusive { max: u8::MAX.into() })),
        "u16" => int(Some(SpecQuantifierDomain::UnsignedInclusive { max: u16::MAX.into() })),
        "u32" => int(Some(SpecQuantifierDomain::UnsignedInclusive { max: u32::MAX.into() })),
        "u64" => int(Some(SpecQuantifierDomain::UnsignedInclusive { max: u64::MAX.into() })),
        "u128" => int(Some(SpecQuantifierDomain::UnsignedInclusive { max: u128::MAX })),
        // Pointer-sized binders take their exact domain from the compilation
        // target's pointer width, supplied by the compiler caller from
        // `tcx.data_layout.pointer_size()` — never the host, never a guess.
        // Without a supported width (16/32/64), keep rejecting both universal
        // and existential pointer-sized binders rather than publishing a
        // different proposition over a guessed or unbounded domain.
        "usize" => match target_pointer_width_bits {
            Some(16) => int(Some(SpecQuantifierDomain::UnsignedInclusive { max: u16::MAX.into() })),
            Some(32) => int(Some(SpecQuantifierDomain::UnsignedInclusive { max: u32::MAX.into() })),
            Some(64) => int(Some(SpecQuantifierDomain::UnsignedInclusive { max: u64::MAX.into() })),
            _ => None,
        },
        "isize" => match target_pointer_width_bits {
            Some(16) => int(Some(SpecQuantifierDomain::Inclusive {
                min: i16::MIN.into(),
                max: i16::MAX.into(),
            })),
            Some(32) => int(Some(SpecQuantifierDomain::Inclusive {
                min: i32::MIN.into(),
                max: i32::MAX.into(),
            })),
            Some(64) => int(Some(SpecQuantifierDomain::Inclusive {
                min: i64::MIN.into(),
                max: i64::MAX.into(),
            })),
            _ => None,
        },
        _ => None,
    }
}

fn predicate_schema(predicate: &ContractPredicate) -> Option<String> {
    match predicate {
        ContractPredicate::TrustIr { schema, .. }
        | ContractPredicate::MathIr { schema, .. }
        | ContractPredicate::MemoryIr { schema, .. }
        | ContractPredicate::CanonicalJson { schema, .. } => Some(schema.clone()),
        ContractPredicate::TrustExpr { .. }
        | ContractPredicate::TemporalModelRef { .. }
        | ContractPredicate::Unsupported { .. } => None,
        _ => None,
    }
}

struct VcFormulaPayload {
    schema: String,
    sort: String,
    smtlib: String,
    /// Byte length of a typed payload that lowered but was dropped at the transport
    /// ceiling. `None` when nothing was dropped (including when nothing lowered).
    typed_payload_dropped_bytes: Option<usize>,
    /// Byte length of an SMT-LIB rendering that exceeded the transport ceiling and
    /// was replaced, in `smtlib`, by the bounded omission marker. `None` when
    /// `smtlib` is the rendering itself.
    smtlib_omitted_bytes: Option<usize>,
    typed_payload: Option<String>,
    /// Exact formula from which `typed_payload` was serialized.
    ///
    /// This can differ from the fresh VC's source formula after the sound
    /// unsigned-BV widening or violation-pruning steps above.  TrustVC's direct
    /// MIR-memory proof unit must be derived from this exact selected formula,
    /// never by independently lowering the pre-selection source formula.
    selected_formula: Option<Formula>,
    verified_seal: Option<(usize, usize, u64)>,
    /// The `typed_payload` was produced by VIOLATION-PRUNING (un-lowerable hypothesis
    /// conjuncts dropped). The pruned residue `P` is a sub-conjunction of the original
    /// violation, so `P UNSAT ⟹ original UNSAT` — a PROVED verdict is sound. But a
    /// counterexample to `P` (fewer hypotheses) is NOT a valid counterexample to the
    /// original (the dropped hypotheses might exclude it), so the result processor must
    /// downgrade a pruned-obligation FAILED to UNKNOWN. Surfaced as the
    /// `trust.vc.formula.pruned` metadata flag.
    pruned: bool,
}

/// Metadata key marking an obligation whose typed payload was violation-pruned (see
/// [`VcFormulaPayload::pruned`]). The full-verifier downgrades a FAILED on such an
/// obligation to UNKNOWN.
pub(crate) const TRUST_VC_FORMULA_PRUNED_METADATA_KEY: &str = "trust.vc.formula.pruned";

impl VcFormulaPayload {
    fn exact_selected_typed_formula(&self) -> Result<&Formula, String> {
        let selected = self.selected_formula.as_ref().ok_or_else(|| {
            "trust-vc MIR memory proof unit omitted because the exact public typed formula was unavailable"
                .to_string()
        })?;
        if let (Some(typed_payload), Some(seal)) =
            (self.typed_payload.as_deref(), self.verified_seal)
        {
            if function_scan::fx_hash_selected_formula(&self.schema, typed_payload, selected)
                == seal
            {
                return Ok(selected);
            }
        }
        let predicate = trust_spec_predicate_from_formula(selected).ok_or_else(|| {
            "trust-vc MIR memory proof unit omitted because the selected public formula no longer lowers to a typed predicate"
                .to_string()
        })?;
        let ContractPredicate::TrustIr { schema, value } = predicate
            .into_contract_predicate()
            .map_err(|error| {
                format!(
                    "trust-vc MIR memory proof unit omitted because the selected public typed predicate could not be serialized: {error}"
                )
            })?
        else {
            return Err(
                "trust-vc MIR memory proof unit omitted because the selected public formula did not serialize as the typed TrustIr predicate schema"
                    .to_string(),
            );
        };
        let serialized = trust_types::json_depth::into_string_owned_on_deep_stack(value)
            .map_err(|error| {
                format!(
                    "trust-vc MIR memory proof unit omitted because the selected public typed predicate could not be serialized: {error}"
                )
            })?;
        if schema != self.schema || self.typed_payload.as_deref() != Some(serialized.as_str()) {
            return Err(
                "trust-vc MIR memory proof unit omitted because the selected formula and public typed payload drifted before proof-unit construction"
                    .to_string(),
            );
        }
        Ok(selected)
    }

    fn into_metadata(self) -> Vec<MetadataEntry> {
        let mut metadata = vec![
            MetadataEntry { key: "trust.vc.formula.schema".to_string(), value: self.schema },
            MetadataEntry { key: "trust.vc.formula.sort".to_string(), value: self.sort },
            MetadataEntry { key: "trust.vc.formula.smtlib2".to_string(), value: self.smtlib },
        ];
        if let Some(payload) = self.typed_payload {
            metadata.push(MetadataEntry {
                key: TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY.to_string(),
                value: payload,
            });
        }
        if self.pruned {
            metadata.push(MetadataEntry {
                key: TRUST_VC_FORMULA_PRUNED_METADATA_KEY.to_string(),
                value: "true".to_string(),
            });
        }
        if let Some(bytes) = self.typed_payload_dropped_bytes {
            // RECORD THE DROP. Without this the row is BYTE-IDENTICAL to one whose VC
            // never lowered to a typed predicate, and nobody — user or maintainer — can
            // tell "this does not lower" from "this lowered and we discarded a 1 MiB
            // proof carrier for transport reasons". That is exactly the laundering this
            // whole fix exists to remove, reintroduced one layer down, and it would have
            // shipped behind nothing but an eprintln gated on TRUST_FORMULA_DEBUG.
            //
            // The discipline is already this file's own, in three places: the temporal
            // model emits `.serialize_error` rather than silently dropping
            // ("Serialization failure is recorded loudly"), the MIR-memory unit emits
            // TRUST_VC_MIR_MEMORY_PROOF_UNIT_UNSUPPORTED_METADATA_KEY with its reason, and
            // contract_bundle_to_verifier_api records its exclusion in bundle metadata
            // "never silent". A dropped carrier gets the same treatment.
            metadata.push(MetadataEntry {
                key: TRUST_VC_FORMULA_PAYLOAD_DROPPED_METADATA_KEY.to_string(),
                value: bytes.to_string(),
            });
        }
        if let Some(bytes) = self.smtlib_omitted_bytes {
            metadata.push(MetadataEntry {
                key: TRUST_VC_FORMULA_SMTLIB_OMITTED_METADATA_KEY.to_string(),
                value: bytes.to_string(),
            });
        }
        metadata
    }
}

/// True for a non-negative `i128` representable in `width` unsigned bits.
fn bv_fits_unsigned(value: i128, width: u32) -> bool {
    value >= 0 && (width >= 127 || value < (1i128 << width))
}

/// A non-negative integer constant's value, or `None`.
fn formula_const_u128(f: &Formula) -> Option<u128> {
    match f {
        Formula::Int(n) if *n >= 0 => Some(*n as u128),
        Formula::UInt(n) => Some(*n),
        _ => None,
    }
}

/// Collect the variable names appearing in an arithmetic operand subterm.
fn collect_overflow_operand_names<'a>(
    f: &'a Formula,
    out: &mut trust_types::fx::FxHashSet<&'a str>,
) {
    match f {
        Formula::Var(name, _) => {
            out.insert(name.as_str());
        }
        Formula::SymVar(sym, _) => {
            out.insert(sym.as_str());
        }
        Formula::Add(a, b) | Formula::Sub(a, b) | Formula::Mul(a, b) => {
            collect_overflow_operand_names(a, out);
            collect_overflow_operand_names(b, out);
        }
        Formula::Neg(a) => collect_overflow_operand_names(a, out),
        _ => {}
    }
}

/// Translate a guard `Var`/`SymVar` into the `width`-bit unsigned BV theory. Bool
/// temporaries stay boolean; an integer var is only sound to reinterpret as
/// `width`-bit unsigned when it IS an overflow operand (a known unsigned value in
/// `[0, 2^width)`). Any other integer var has unknown sign/width, so bail.
fn bv_translate_guard_var(
    name: &str,
    sort: &Sort,
    width: u32,
    operand_names: &trust_types::fx::FxHashSet<&str>,
) -> Option<Formula> {
    match sort {
        Sort::Bool => Some(Formula::Var(name.to_string(), Sort::Bool)),
        Sort::Int | Sort::BitVec(_) => operand_names
            .contains(name)
            .then(|| Formula::Var(name.to_string(), Sort::BitVec(width))),
        _ => None,
    }
}

/// Recognize the Int overflow-check disjunction `Or([Lt(a OP b, 0), Gt(a OP b,
/// type_max)])` and return the EXACT unsigned `width`-bit wrap idiom (add:
/// `bvult(bvadd(a,b), a)`; sub: `bvult(a, b)`). `None` if the shape/bounds don't
/// match or an operand isn't soundly translatable. Term-wise translation is
/// unsound here: BV add/sub wrap mod 2^width, making `> type_max` vacuous.
fn bv_unsigned_overflow_idiom(
    disjuncts: &[Formula],
    width: u32,
    operand_names: &trust_types::fx::FxHashSet<&str>,
) -> Option<Formula> {
    let [Formula::Lt(result, lo), Formula::Gt(_, hi)] = disjuncts else {
        return None;
    };
    if formula_const_u128(lo)? != 0 {
        return None;
    }
    let type_max: u128 = if width >= 128 { u128::MAX } else { (1u128 << width) - 1 };
    if formula_const_u128(hi)? != type_max {
        return None;
    }
    match result.as_ref() {
        Formula::Add(a, b) => {
            let a_bv = bv_translate_guard(a, width, operand_names)?;
            let b_bv = bv_translate_guard(b, width, operand_names)?;
            Some(Formula::BvULt(
                Box::new(Formula::BvAdd(Box::new(a_bv.clone()), Box::new(b_bv), width)),
                Box::new(a_bv),
                width,
            ))
        }
        Formula::Sub(a, b) => {
            let a_bv = bv_translate_guard(a, width, operand_names)?;
            let b_bv = bv_translate_guard(b, width, operand_names)?;
            Some(Formula::BvULt(Box::new(a_bv), Box::new(b_bv), width))
        }
        _ => None,
    }
}

/// Recognize the BARE unsigned-subtraction underflow disjunct `Lt(Sub(a, b), 0)`
/// and translate it to the exact borrow idiom `bvult(a, b)`. Trust-vcgen emits
/// UNSIGNED subtraction overflow as just this single `result < 0` disjunct (the
/// `> type_max` half is dropped as tautologically false for a subtraction, see
/// `v2_build_overflow_vc_for_operands`), so it never appears inside the
/// two-disjunct [`bv_unsigned_overflow_idiom`]. Term-wise translation is UNSOUND
/// here: `bvsub(a, b)` wraps mod 2^width and an UNSIGNED value is never `<u 0`, so
/// `bvult(bvsub(a, b), 0)` is VACUOUSLY FALSE — the confirmed false-accept that
/// verified `fn sub(a: usize, b: usize) -> usize { a - b }` clean. The borrow
/// idiom `a <u b` is the exact, wrap-free encoding of unsigned underflow. `None`
/// unless it is exactly `Lt(Sub(operand, operand), 0)` on soundly-translatable
/// operands, so the caller keeps the sound Int formula and never a false PROVE.
fn bv_bare_unsigned_sub_underflow_idiom(
    result: &Formula,
    lo: &Formula,
    width: u32,
    operand_names: &trust_types::fx::FxHashSet<&str>,
) -> Option<Formula> {
    if formula_const_u128(lo)? != 0 {
        return None;
    }
    let Formula::Sub(a, b) = result else {
        return None;
    };
    let a_bv = bv_translate_guard(a, width, operand_names)?;
    let b_bv = bv_translate_guard(b, width, operand_names)?;
    Some(Formula::BvULt(Box::new(a_bv), Box::new(b_bv), width))
}

/// Translate an assembled overflow VC formula into the `width`-bit unsigned BV
/// theory, or `None` on any construct outside the sound relational+overflow
/// fragment. Soundness: the only integer terms admitted are overflow operand vars
/// (unsigned values in `[0, 2^width)`) and non-negative literals `< 2^width`, on
/// which unsigned-BV comparison agrees EXACTLY with integer comparison; the
/// overflow disjunction becomes the exact wrap idiom. Anything else bails — so the
/// caller keeps the sound Int formula and a false PROVE can never be introduced.
fn bv_translate_guard(
    f: &Formula,
    width: u32,
    operand_names: &trust_types::fx::FxHashSet<&str>,
) -> Option<Formula> {
    match f {
        Formula::Bool(b) => Some(Formula::Bool(*b)),
        Formula::Var(name, sort) => bv_translate_guard_var(name, sort, width, operand_names),
        Formula::SymVar(sym, sort) => {
            bv_translate_guard_var(sym.as_str(), sort, width, operand_names)
        }
        Formula::Int(n) if bv_fits_unsigned(*n, width) => {
            Some(Formula::BitVec { value: *n, width })
        }
        Formula::UInt(n) if bv_fits_unsigned(*n as i128, width) => {
            Some(Formula::BitVec { value: *n as i128, width })
        }
        Formula::Not(a) => {
            Some(Formula::Not(Box::new(bv_translate_guard(a, width, operand_names)?)))
        }
        Formula::And(xs) => Some(Formula::And(
            xs.iter()
                .map(|x| bv_translate_guard(x, width, operand_names))
                .collect::<Option<Vec<_>>>()?,
        )),
        Formula::Or(xs) => {
            if let Some(idiom) = bv_unsigned_overflow_idiom(xs, width, operand_names) {
                return Some(idiom);
            }
            Some(Formula::Or(
                xs.iter()
                    .map(|x| bv_translate_guard(x, width, operand_names))
                    .collect::<Option<Vec<_>>>()?,
            ))
        }
        Formula::Implies(a, b) => Some(Formula::Implies(
            Box::new(bv_translate_guard(a, width, operand_names)?),
            Box::new(bv_translate_guard(b, width, operand_names)?),
        )),
        Formula::Eq(a, b) => Some(Formula::Eq(
            Box::new(bv_translate_guard(a, width, operand_names)?),
            Box::new(bv_translate_guard(b, width, operand_names)?),
        )),
        // BARE unsigned-sub underflow `Lt(Sub(a,b), 0)` -> borrow `bvult(a,b)`
        // (the term-wise `bvult(bvsub(a,b), 0)` is vacuously false — the
        // unsigned-sub false-accept). Falls through to the generic relational
        // translation for every other `<` (range bounds etc.).
        Formula::Lt(a, b) => bv_bare_unsigned_sub_underflow_idiom(a, b, width, operand_names)
            .or_else(|| {
                Some(Formula::BvULt(
                    Box::new(bv_translate_guard(a, width, operand_names)?),
                    Box::new(bv_translate_guard(b, width, operand_names)?),
                    width,
                ))
            }),
        Formula::Le(a, b) => Some(Formula::BvULe(
            Box::new(bv_translate_guard(a, width, operand_names)?),
            Box::new(bv_translate_guard(b, width, operand_names)?),
            width,
        )),
        // `a > b` ⟺ `b < a`; `a >= b` ⟺ `b <= a`.
        Formula::Gt(a, b) => Some(Formula::BvULt(
            Box::new(bv_translate_guard(b, width, operand_names)?),
            Box::new(bv_translate_guard(a, width, operand_names)?),
            width,
        )),
        Formula::Ge(a, b) => Some(Formula::BvULe(
            Box::new(bv_translate_guard(b, width, operand_names)?),
            Box::new(bv_translate_guard(a, width, operand_names)?),
            width,
        )),
        _ => None,
    }
}

/// Find the unsigned overflow-check disjunction in an assembled VC formula and
/// return `(width, operand_var_names)` — but ONLY for width 64 (`u64`/`usize`),
/// whose `type_max` (`u64::MAX`) is the literal that exceeds the native solver's
/// i64 Int boundary. Narrower types already verify on the Int path.
fn find_unsigned_overflow_pattern(f: &Formula) -> Option<(u32, trust_types::fx::FxHashSet<&str>)> {
    match f {
        Formula::Or(xs) => {
            if let [Formula::Lt(result, lo), Formula::Gt(_, hi)] = xs.as_slice() {
                if formula_const_u128(lo) == Some(0)
                    && formula_const_u128(hi) == Some(u64::MAX as u128)
                    && matches!(result.as_ref(), Formula::Add(_, _) | Formula::Sub(_, _))
                {
                    let mut names = trust_types::fx::FxHashSet::default();
                    collect_overflow_operand_names(result, &mut names);
                    return Some((64, names));
                }
            }
            xs.iter().find_map(find_unsigned_overflow_pattern)
        }
        Formula::And(xs) => xs.iter().find_map(find_unsigned_overflow_pattern),
        Formula::Not(a) | Formula::Neg(a) => find_unsigned_overflow_pattern(a),
        // BARE unsigned-sub underflow `Lt(Sub(a,b), 0)` — trust-vcgen drops the
        // `> u64::MAX` half for a subtraction, so the overflow check is this lone
        // `< 0` disjunct. Recognizing it here routes the VC through the borrow
        // idiom instead of the relational widener (whose bvsub-never-underflows
        // premise is circular for the underflow check itself). See
        // `bv_bare_unsigned_sub_underflow_idiom`.
        Formula::Lt(result, lo)
            if formula_const_u128(lo) == Some(0)
                && matches!(result.as_ref(), Formula::Sub(_, _)) =>
        {
            let mut names = trust_types::fx::FxHashSet::default();
            collect_overflow_operand_names(result, &mut names);
            Some((64, names))
        }
        Formula::Implies(a, b)
        | Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b) => {
            find_unsigned_overflow_pattern(a).or_else(|| find_unsigned_overflow_pattern(b))
        }
        _ => None,
    }
}

/// Whether the formula already carries bitvector-theory structure. A VC that
/// arrives BV-typed was authored at its DECLARED machine width by trust-vcgen's
/// Machine{w} contract lane (ratified L1 rule 4): its arithmetic deliberately
/// WRAPS. The widening re-encoders below choose a strictly-larger width so
/// arithmetic can NEVER wrap — sound for the execution-domain (panic-guarded)
/// Int VCs they were built for, but the exact false-proof vector for a
/// spec-domain clause (`result + 1 > result` re-proved as unbounded). They must
/// therefore never touch a formula that already speaks bitvector. Their
/// translators already bail on every `Bv*` node; this predicate makes the
/// exclusion explicit at the entry so no future fragment extension can reopen
/// the vector.
fn formula_mentions_bitvector_theory(formula: &Formula) -> bool {
    trust_types::formula_mentions_bitvector_theory(formula)
}

/// Number of bits needed to hold the unsigned value `v` (>= 1; `u64::MAX` -> 64).
fn unsigned_value_bits(v: u128) -> u32 {
    if v == 0 { 1 } else { 128 - v.leading_zeros() }
}

/// Check every integer literal in `f` for the unsigned/signed gate without
/// allocating a `Vec<i128>`: returns `false` immediately if any negative literal
/// appears, and sets `*has_large = true` if any literal exceeds `i64::MAX`.
fn check_unsigned_int_literals(f: &Formula, has_large: &mut bool) -> bool {
    match f {
        Formula::Int(n) => {
            if *n < 0 {
                return false;
            }
            if *n > i64::MAX as i128 {
                *has_large = true;
            }
            true
        }
        Formula::UInt(n) => {
            if *n > i64::MAX as u128 {
                *has_large = true;
            }
            true
        }
        Formula::Not(a) | Formula::Neg(a) => check_unsigned_int_literals(a, has_large),
        Formula::And(xs) | Formula::Or(xs) => {
            xs.iter().all(|x| check_unsigned_int_literals(x, has_large))
        }
        Formula::Implies(a, b)
        | Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b)
        | Formula::Add(a, b)
        | Formula::Sub(a, b)
        | Formula::Mul(a, b)
        | Formula::Div(a, b)
        | Formula::Rem(a, b) => {
            check_unsigned_int_literals(a, has_large) && check_unsigned_int_literals(b, has_large)
        }
        _ => true,
    }
}

/// The width needed so that NO integer arithmetic in `f` can overflow: source
/// integer vars/consts are <= 64-bit unsigned; `add`/`sub` grow the result by 1
/// bit, `mul` by the sum of operand widths, `div`/`rem` never grow. `None` if a
/// non-arithmetic/non-relational node is hit or the width exceeds `cap`. Because
/// the chosen BV width is >= this bound, `bvadd`/`bvsub`/`bvmul` in that width are
/// EXACT (never wrap) — the crux of the soundness argument below.
fn unsigned_arith_max_width(f: &Formula, cap: u32) -> Option<u32> {
    let w = match f {
        Formula::Bool(_) => 1,
        Formula::Var(..) | Formula::SymVar(..) => 64,
        Formula::Int(n) => unsigned_value_bits(u128::try_from(*n).ok()?),
        Formula::UInt(n) => unsigned_value_bits(*n),
        Formula::Not(a) => unsigned_arith_max_width(a, cap)?,
        Formula::And(xs) | Formula::Or(xs) => {
            let mut m = 1;
            for x in xs {
                m = m.max(unsigned_arith_max_width(x, cap)?);
            }
            m
        }
        Formula::Implies(a, b)
        | Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b) => {
            unsigned_arith_max_width(a, cap)?.max(unsigned_arith_max_width(b, cap)?)
        }
        Formula::Add(a, b) | Formula::Sub(a, b) => {
            let w = unsigned_arith_max_width(a, cap)?
                .max(unsigned_arith_max_width(b, cap)?)
                .saturating_add(1);
            if w > cap {
                return None;
            }
            w
        }
        Formula::Mul(a, b) => {
            let w =
                unsigned_arith_max_width(a, cap)?.saturating_add(unsigned_arith_max_width(b, cap)?);
            if w > cap {
                return None;
            }
            w
        }
        Formula::Div(a, b) | Formula::Rem(a, b) => {
            unsigned_arith_max_width(b, cap)?;
            unsigned_arith_max_width(a, cap)?
        }
        _ => return None,
    };
    Some(w)
}

/// Translate an all-UNSIGNED integer VC into `width`-bit BV, term-wise: integer
/// vars/consts become `width`-bit BV; `+`/`-`/`*`/`/`/`%` become the BV ops; and
/// `<`/`<=`/`>`/`>=` become UNSIGNED BV comparisons. Bool structure is preserved.
/// `None` on any node outside this fragment (bitwise/float/quantifier), so the
/// caller keeps the sound Int formula.
fn bv_widen_translate(f: &Formula, width: u32) -> Option<Formula> {
    let bin = |a: &Formula, b: &Formula| -> Option<(Box<Formula>, Box<Formula>)> {
        Some((Box::new(bv_widen_translate(a, width)?), Box::new(bv_widen_translate(b, width)?)))
    };
    Some(match f {
        Formula::Bool(b) => Formula::Bool(*b),
        Formula::Var(name, sort) => match sort {
            Sort::Bool => Formula::Var(name.clone(), Sort::Bool),
            Sort::Int | Sort::BitVec(_) => Formula::Var(name.clone(), Sort::BitVec(width)),
            _ => return None,
        },
        Formula::SymVar(sym, sort) => match sort {
            Sort::Bool => Formula::Var(sym.as_str().to_string(), Sort::Bool),
            Sort::Int | Sort::BitVec(_) => {
                Formula::Var(sym.as_str().to_string(), Sort::BitVec(width))
            }
            _ => return None,
        },
        Formula::Int(n) if *n >= 0 && bv_fits_unsigned(*n, width) => {
            Formula::BitVec { value: *n, width }
        }
        Formula::UInt(n) => {
            let v = i128::try_from(*n).ok()?;
            if !bv_fits_unsigned(v, width) {
                return None;
            }
            Formula::BitVec { value: v, width }
        }
        Formula::Not(a) => Formula::Not(Box::new(bv_widen_translate(a, width)?)),
        Formula::And(xs) => Formula::And(
            xs.iter().map(|x| bv_widen_translate(x, width)).collect::<Option<Vec<_>>>()?,
        ),
        Formula::Or(xs) => Formula::Or(
            xs.iter().map(|x| bv_widen_translate(x, width)).collect::<Option<Vec<_>>>()?,
        ),
        Formula::Implies(a, b) => {
            let (a, b) = bin(a, b)?;
            Formula::Implies(a, b)
        }
        Formula::Eq(a, b) => {
            let (a, b) = bin(a, b)?;
            Formula::Eq(a, b)
        }
        // A subtraction compared `< 0` is an UNDERFLOW check. `bvsub` is
        // two's-complement EXACT at this non-wrapping width (the width bounds
        // arithmetic growth), so the difference is the genuine, possibly-NEGATIVE
        // integer — but an UNSIGNED `<u 0` is vacuously false, which vacuously
        // "proves" the underflow safe (the confirmed `fn sub(a,b)->a-b`
        // false-accept). SIGNED `<s 0` is the exact underflow test (a < b) and
        // agrees with the integer relation because the value is
        // signed-representable at this width. Every other `<` is between
        // non-negative operands, where unsigned is exact.
        Formula::Lt(a, b)
            if matches!(a.as_ref(), Formula::Sub(_, _)) && formula_const_u128(b) == Some(0) =>
        {
            let (a, b) = bin(a, b)?;
            Formula::BvSLt(a, b, width)
        }
        Formula::Lt(a, b) => {
            let (a, b) = bin(a, b)?;
            Formula::BvULt(a, b, width)
        }
        Formula::Le(a, b) => {
            let (a, b) = bin(a, b)?;
            Formula::BvULe(a, b, width)
        }
        // `a > b` ⟺ `b < a`; `a >= b` ⟺ `b <= a`.
        Formula::Gt(a, b) => {
            let (a, b) = bin(a, b)?;
            Formula::BvULt(b, a, width)
        }
        Formula::Ge(a, b) => {
            let (a, b) = bin(a, b)?;
            Formula::BvULe(b, a, width)
        }
        Formula::Add(a, b) => {
            let (a, b) = bin(a, b)?;
            Formula::BvAdd(a, b, width)
        }
        Formula::Sub(a, b) => {
            let (a, b) = bin(a, b)?;
            Formula::BvSub(a, b, width)
        }
        Formula::Mul(a, b) => {
            let (a, b) = bin(a, b)?;
            Formula::BvMul(a, b, width)
        }
        Formula::Div(a, b) => {
            let (a, b) = bin(a, b)?;
            Formula::BvUDiv(a, b, width)
        }
        Formula::Rem(a, b) => {
            let (a, b) = bin(a, b)?;
            Formula::BvURem(a, b, width)
        }
        _ => return None,
    })
}

/// Re-encode a wide UNSIGNED (u64/usize) VC — a postcondition or any relational
/// goal — into the BV theory, generalizing `try_widen_unsigned_overflow_vc_to_bv`
/// beyond the add/sub OVERFLOW idiom to arbitrary comparison + arithmetic goals.
/// The Int lowering carries the type-range literal `u64::MAX`, which exceeds ay's
/// i64 `ChcExpr::Int` boundary (gap-log #19) → `unknown`; in BV the width is
/// implicit so the literal is a legal constant and the goal is decided.
///
/// SOUNDNESS (no false PROVE of a false postcondition):
///  - Gated to ALL-UNSIGNED goals: triggered only when an out-of-i64 literal (the
///    `u64::MAX`-style type bound) is present, and REJECTED if any negative literal
///    appears (a negative marks a signed `i64`/`i32` var or bound — `i64::MIN` in
///    its arg-range — whose unsigned-BV comparison would mismodel it). Under the
///    gate every integer term is a non-negative value < 2^64.
///  - `bvule`/`bvult` agree EXACTLY with integer `<=`/`<` for non-negative operands.
///  - `bvadd`/`bvmul` are EXACT: the width (`unsigned_arith_max_width`) is chosen
///    strictly wider than any add/mul result can be, so they provably never wrap.
///  - `bvsub`/`bvudiv` are exact on the domain of REAL (panic-free) executions —
///    the only executions a postcondition can be violated by. A real usize `a - b`
///    never underflows (`a >= b`, else it panics / fails the L0 safety gate) and a
///    real `a / b` never divides by zero, and on that domain `bvsub`/`bvudiv` equal
///    the integer op. So any real violating state is preserved exactly in BV and
///    stays SAT ⇒ a FALSE postcondition is REFUTED. The only states BV mis-models
///    are the unreachable underflow/div-zero ones, which cannot correspond to a
///    real violation — hence no false PROVE. (A benign side effect: a spurious BV
///    model over an unreachable state can only add SAT ⇒ at worst a false REFUTE,
///    which is fail-closed, never a false PROVE.)
///  - Bails (keeps the Int formula) on any node outside the relational+arithmetic
///    fragment (bitwise/float/quantifier) or when the no-overflow width exceeds the
///    cap — never a false PROVE.
#[cfg(test)]
fn try_widen_unsigned_relational_vc_to_bv(formula: &Formula) -> Option<Formula> {
    // Declared-width Machine{w} VCs must keep their wrapping reading — see
    // `formula_mentions_bitvector_theory`.
    if formula_mentions_bitvector_theory(formula) {
        return None;
    }
    try_widen_unsigned_relational_vc_to_bv_unchecked(formula)
}

fn try_widen_unsigned_relational_vc_to_bv_unchecked(formula: &Formula) -> Option<Formula> {
    const CAP: u32 = 256;
    let mut has_large = false;
    // Soundness gate: no negative literal (⇒ no signed var/bound in the goal),
    // and trigger only when an out-of-i64 literal is present (the u64/usize type
    // bound that defeats the Int lane).
    if !check_unsigned_int_literals(formula, &mut has_large) || !has_large {
        return None;
    }
    let need = unsigned_arith_max_width(formula, CAP)?;
    // ARITHMETIC ENABLED (2026-07-08, wishlist rank 5): the former activation
    // gate that bailed on any add/sub/mul/div is LIFTED. ay rewrites
    // bvudiv/bvurem-by-2^k to shift/mask at term construction and simplification
    // (exact SMT-LIB equivalences), keys division/UF havoc bits by structural
    // identity, and fail-closes under-assigned models in BOTH the internal
    // DPLL(T) loop and the executor fallback — so the arithmetic fragment no
    // longer spuriously refutes. Validated with the full probe battery: true
    // usize comparison + arithmetic postconditions PROVE, their false variants
    // REFUTE, i64 regressions unchanged, a3d gate green.
    // Round up to a solver-friendly width strictly covering the no-overflow bound.
    let width = need.max(64).next_power_of_two().min(CAP);
    if need > width {
        return None;
    }
    bv_widen_translate(formula, width)
}

fn formula_contains_select(formula: &Formula) -> bool {
    trust_types::any_formula_node(formula, &mut |node| matches!(node, Formula::Select(..)))
}

/// Normalize the decidable fragment of SMT array read-over-write before the
/// public typed-predicate boundary.
///
/// The public predicate IR deliberately carries scalar `Select` but not an
/// arbitrary array-valued `Store`.  Native E4/E5 collection VCs nevertheless
/// produce `Select(Store(a, i, v), j)` after an exact exclusive write.  The two
/// cases below are exact SMT array identities:
///
/// - `i` and `j` are structurally identical: the read is `v`;
/// - `i` and `j` are provably distinct integer literals: the read is
///   `Select(a, j)`.
///
/// A symbolic or otherwise undecidable index relation is left untouched.  In
/// particular, this pass never guesses aliasing and never manufactures the
/// conditional (`ite`) required by the general read-over-write axiom.  Such a
/// formula therefore continues to fail closed at typed lowering.
fn normalize_decidable_array_read_over_write(formula: &Formula) -> Formula {
    if !formula_contains_select(formula) {
        return formula.clone();
    }
    // Rewriting an ill-sorted `Select(Store(..))` could erase the very node
    // that demonstrates the sort error. Validate the original tree first so
    // malformed producer input remains malformed and cannot splice into the
    // scalar typed lane.
    if check_formula_sort(formula).is_err() {
        return formula.clone();
    }
    formula.clone().map(&mut |node| {
        let Formula::Select(array, read_index) = node else {
            return node;
        };
        // `select(const(v), i) = v` for EVERY `i`: the read of a constant
        // array is its value (the ArraysEx `as const` law), exact and
        // index-independent. Same scalar-lane admission as the Store case.
        if let Formula::ConstArray { index_sort, elem_sort, value } = array.as_ref() {
            if *index_sort == Sort::Int && formula_sort_to_spec_scalar_sort(elem_sort).is_some() {
                return value.as_ref().clone();
            }
        }
        let Formula::Store(previous, stored_index, value) = *array else {
            return Formula::Select(array, read_index);
        };
        let supported_array = matches!(
            check_formula_sort(&previous),
            Ok(Sort::Array(index, element))
                if index.as_ref() == &Sort::Int
                    && formula_sort_to_spec_scalar_sort(element.as_ref()).is_some()
        );
        if !supported_array {
            return Formula::Select(
                Box::new(Formula::Store(previous, stored_index, value)),
                read_index,
            );
        }
        if stored_index == read_index || provably_equal_integer_literals(&stored_index, &read_index)
        {
            return *value;
        }
        if provably_distinct_integer_literals(&stored_index, &read_index) {
            // A constant array beneath the distinct write is read exactly
            // (its sort is the supported scalar lane established above).
            if let Formula::ConstArray { value, .. } = previous.as_ref() {
                return value.as_ref().clone();
            }
            return Formula::Select(previous, read_index);
        }
        Formula::Select(Box::new(Formula::Store(previous, stored_index, value)), read_index)
    })
}

fn provably_equal_integer_literals(lhs: &Formula, rhs: &Formula) -> bool {
    match (lhs, rhs) {
        (Formula::Int(lhs), Formula::Int(rhs)) => lhs == rhs,
        (Formula::UInt(lhs), Formula::UInt(rhs)) => lhs == rhs,
        (Formula::Int(lhs), Formula::UInt(rhs)) => {
            u128::try_from(*lhs).is_ok_and(|lhs| lhs == *rhs)
        }
        (Formula::UInt(lhs), Formula::Int(rhs)) => {
            u128::try_from(*rhs).is_ok_and(|rhs| *lhs == rhs)
        }
        _ => false,
    }
}

/// Whether two mathematical-integer literals are certainly unequal.
///
/// `UInt` is an alternate non-negative literal spelling in `Formula`, not a
/// distinct SMT sort, so cross-spelling comparisons are safe here as well.
fn provably_distinct_integer_literals(lhs: &Formula, rhs: &Formula) -> bool {
    match (lhs, rhs) {
        (Formula::Int(lhs), Formula::Int(rhs)) => lhs != rhs,
        (Formula::UInt(lhs), Formula::UInt(rhs)) => lhs != rhs,
        (Formula::Int(lhs), Formula::UInt(rhs)) => {
            *lhs < 0 || u128::try_from(*lhs).is_ok_and(|lhs| lhs != *rhs)
        }
        (Formula::UInt(lhs), Formula::Int(rhs)) => {
            *rhs < 0 || u128::try_from(*rhs).is_ok_and(|rhs| *lhs != rhs)
        }
        _ => false,
    }
}

/// Trust (2026-10-01, review rounds 34 and 35): whether EVERY free variable of
/// `formula` is a local of `function` of UNSIGNED integer type at most 64 bits wide
/// (by its rendered name, version suffix `#…` stripped), or such a local's slice
/// length (`{name}__slice_len`, a `usize`), or is `Bool`-sorted. The two unsigned
/// BV wideners below assume exactly that (`unsigned_arith_max_width` counts a variable as 64 bits and
/// `bv_widen_translate` compares unsigned), and anything else broke them: a `u128`
/// local (`if x > u64::MAX` encoded at bv64, never true: a CERTIFIED division by
/// zero, round 34), a `const N: u128` generic (vcgen's `__trust_constparam_…`
/// symbol, not a local: the same proof again, round 35), and a negative
/// `const N: i128` read as unsigned (`N < 0` never true, round 35). An allow-list,
/// because vcgen mints many synthetic symbols of no stated width
/// (`__trust_opaque_scalar_…`, `__trust_float_cast_…`, …). The widening is an
/// optimization only (the Int lane encodes large constants faithfully since
/// gap-log #19), so declining it costs decidability, never soundness.
#[cfg(test)]
fn formula_vars_are_narrow_unsigned_locals(
    function: &VerifiableFunction,
    formula: &Formula,
) -> bool {
    function_scan::NarrowUnsignedLocalIndex::new(function).admits_formula(formula)
}

#[cfg(test)]
fn vc_formula_payload(kind: &VcKind, formula: &Formula) -> VcFormulaPayload {
    vc_formula_payload_with(kind, formula, &mut || true)
}

/// [`vc_formula_payload_with`] for a VC of `function`: the unsigned BV wideners run only
/// when every variable is a narrow unsigned local
/// ([`formula_vars_are_narrow_unsigned_locals`]); otherwise the exact Int formula
/// is kept.
fn vc_formula_payload_for(
    function: &VerifiableFunction,
    kind: &VcKind,
    formula: &Formula,
) -> VcFormulaPayload {
    let narrow_index = std::cell::OnceCell::new();
    vc_formula_payload_for_cached(function, kind, formula, &narrow_index)
}

fn vc_formula_payload_for_cached<'a>(
    function: &'a VerifiableFunction,
    kind: &VcKind,
    formula: &Formula,
    narrow_index: &std::cell::OnceCell<function_scan::NarrowUnsignedLocalIndex<'a>>,
) -> VcFormulaPayload {
    let mut cached_admits: Option<bool> = None;
    vc_formula_payload_with(kind, formula, &mut || {
        *cached_admits.get_or_insert_with(|| {
            narrow_index
                .get_or_init(|| function_scan::NarrowUnsignedLocalIndex::new(function))
                .admits_formula(formula)
        })
    })
}

/// Finalize a VC's public proof carriers before either construction or fresh
/// identity reconstruction hashes them. A large MIR-memory unit must decline
/// only its own transport, rather than invalidate every row in its bundle.
fn vc_transport_for(
    function: &VerifiableFunction,
    vc: &VerificationCondition,
    index: usize,
    obligation_kind: &ObligationKind,
) -> (VcFormulaPayload, Vec<MetadataEntry>) {
    let def_path_id = trust_types::canonical_artifact_id_component(&function.def_path);
    let narrow_index = std::cell::OnceCell::new();
    let memory_scan = std::cell::OnceCell::new();
    vc_transport_for_cached(
        function,
        vc,
        index,
        obligation_kind,
        &def_path_id,
        &narrow_index,
        &memory_scan,
    )
}

fn vc_transport_for_cached<'a>(
    function: &'a VerifiableFunction,
    vc: &VerificationCondition,
    index: usize,
    obligation_kind: &ObligationKind,
    def_path_id: &str,
    narrow_index: &std::cell::OnceCell<function_scan::NarrowUnsignedLocalIndex<'a>>,
    memory_scan: &std::cell::OnceCell<function_scan::TrustVcMemoryFunctionScan>,
) -> (VcFormulaPayload, Vec<MetadataEntry>) {
    let formula = vc_formula_payload_for_cached(function, &vc.kind, &vc.formula, narrow_index);
    let memory = trust_vc_mir_memory_metadata_cached(
        function,
        vc,
        index,
        obligation_kind,
        &formula,
        def_path_id,
        memory_scan,
    );
    // This is the exact compiler-produced family, not arbitrary public
    // metadata. Structural errors and every other metadata value still pass
    // unchanged to the normal bundle validator.
    let Some(unit) =
        memory.iter().find(|entry| entry.key == TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY)
    else {
        return (formula, memory);
    };
    if !trust_types::audit_ledger::cap_hit_if(
        unit.value.len() > MAX_TRANSPORT_METADATA_VALUE_BYTES,
        "crates/trust-mir-extract/src/verifier_api.rs:MAX_TRANSPORT_METADATA_VALUE_BYTES",
    ) {
        return (formula, memory);
    }
    let reason = format!(
        "MIR-memory proof unit omitted: {} bytes exceed the {MAX_TRANSPORT_METADATA_VALUE_BYTES}-byte transport ceiling; sha256={}",
        unit.value.len(),
        stable_sha256_hex(unit.value.as_bytes()),
    );
    // Neither this marker nor the retained unsupported reason is executable
    // SMT. Remove the typed/selected formula and the entire memory proof-unit
    // family together. Independently checked fresh-VC proofs are unaffected.
    let formula = untyped_vc_formula_payload(
        formula.sort,
        format!("trust-omitted-mir-memory-proof-unit: {reason}"),
    );
    (
        formula,
        vec![MetadataEntry {
            key: TRUST_VC_MIR_MEMORY_PROOF_UNIT_UNSUPPORTED_METADATA_KEY.to_string(),
            value: reason,
        }],
    )
}

fn vc_formula_payload_with(
    kind: &VcKind,
    formula: &Formula,
    allow_unsigned_bv_widening: &mut dyn FnMut() -> bool,
) -> VcFormulaPayload {
    let payload = vc_formula_payload_unfactored(kind, formula, allow_unsigned_bv_widening);
    // Trust (G3, 2026-10-27): a VC behind a multi-way join carries its path condition
    // as one disjunct per incoming path, and every disjunct repeats the facts the paths
    // share. agy-alab's `days_from_civil` (a 12-arm `match` feeding a leap-year `&&`
    // chain) reached the lowering as a 48-way `Or` whose disjuncts were 809 nodes each,
    // 797 of them common: a 1.6-2.2 MB typed payload, over the 1 MiB transport
    // ceiling, so every overflow row of the function lost its typed carrier and every
    // native lane declined it ("partial formula schema/payload pair").
    //
    // Only for a row that lost a carrier to the ceiling, retry on the formula with the
    // shared conjuncts factored out of each disjunction (`factor_shared_disjunct_conjuncts`).
    // SOUND: `(C ∧ R1) ∨ … ∨ (C ∧ Rn) ≡ C ∧ (R1 ∨ … ∨ Rn)` is distributivity over
    // structurally identical conjuncts, an EQUIVALENCE: the factored violation is
    // satisfiable by exactly the assignments that satisfy the original, so a proof of
    // its unsatisfiability is a proof of the original's and a model of it is a model of
    // the original (unlike pruning, no `pruned` flag is needed). It is the
    // `selected_formula` precedent of the unsigned-BV widening above: the payload, its
    // SMT-LIB rendering and the direct proof unit all derive from the one selected
    // formula. A row that already carries both its typed payload and its rendering is
    // returned byte-identical; the retry is kept only when it restores the typed payload.
    if payload.typed_payload_dropped_bytes.is_none() && payload.smtlib_omitted_bytes.is_none() {
        return payload;
    }
    let factored = factor_shared_disjunct_conjuncts(formula);
    if factored == *formula {
        return payload;
    }
    let retried = vc_formula_payload_unfactored(kind, &factored, allow_unsigned_bv_widening);
    if retried.typed_payload.is_some() { retried } else { payload }
}

/// Rewrite every disjunction (bottom-up, through `And`/`Or`/`Not`) whose disjuncts
/// share structurally identical conjuncts into `And([shared…, Or([residues…])])`.
///
/// `Or_i (C ∧ R_i) ≡ C ∧ Or_i R_i`; a disjunct whose conjuncts are all shared has the
/// residue `true`, which makes the residual disjunction `true`, so only the shared
/// conjuncts remain. Shared conjuncts keep the first disjunct's order; each residue
/// keeps its own. A disjunction with fewer than two disjuncts, or none shared, is
/// rebuilt unchanged.
fn factor_shared_disjunct_conjuncts(formula: &Formula) -> Formula {
    fn conjuncts(formula: &Formula) -> &[Formula] {
        match formula {
            Formula::And(conjuncts) => conjuncts,
            other => std::slice::from_ref(other),
        }
    }
    match formula {
        Formula::And(conjuncts) => {
            Formula::And(conjuncts.iter().map(factor_shared_disjunct_conjuncts).collect())
        }
        Formula::Not(inner) => Formula::Not(Box::new(factor_shared_disjunct_conjuncts(inner))),
        Formula::Or(disjuncts) => {
            let disjuncts =
                disjuncts.iter().map(factor_shared_disjunct_conjuncts).collect::<Vec<_>>();
            let Some((first, rest)) = disjuncts.split_first() else {
                return Formula::Or(disjuncts);
            };
            if rest.is_empty() {
                return Formula::Or(disjuncts);
            }
            if conjuncts(first).len() > 16 {
                return function_scan::factor_shared_disjuncts_fast(disjuncts, conjuncts);
            }
            // A conjunct is shared when every other disjunct contains an identical one.
            // Repeats inside the first disjunct are taken once (`And` is idempotent).
            let mut shared: Vec<&Formula> = Vec::new();
            for candidate in conjuncts(first) {
                if !shared.contains(&candidate)
                    && rest.iter().all(|disjunct| conjuncts(disjunct).contains(candidate))
                {
                    shared.push(candidate);
                }
            }
            if shared.is_empty() {
                return Formula::Or(disjuncts);
            }
            let mut residues = Vec::with_capacity(disjuncts.len());
            for disjunct in &disjuncts {
                let residue = conjuncts(disjunct)
                    .iter()
                    .filter(|conjunct| !shared.contains(conjunct))
                    .cloned()
                    .collect::<Vec<_>>();
                match residue.len() {
                    // `C ∧ true` is one disjunct: the whole disjunction is `C`.
                    0 => return Formula::And(shared.into_iter().cloned().collect()),
                    1 => residues.extend(residue),
                    _ => residues.push(Formula::And(residue)),
                }
            }
            let mut factored = shared.into_iter().cloned().collect::<Vec<_>>();
            factored.push(Formula::Or(residues));
            Formula::And(factored)
        }
        other => other.clone(),
    }
}

fn formula_debug_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("TRUST_FORMULA_DEBUG").is_some())
}

fn vc_formula_payload_unfactored(
    kind: &VcKind,
    formula: &Formula,
    allow_unsigned_bv_widening: &mut dyn FnMut() -> bool,
) -> VcFormulaPayload {
    // Exact native collection writes reach this boundary as array
    // read-over-write terms.  Normalize only the two decidable identities
    // above; unresolved index aliasing remains an unsupported Store and thus
    // has no typed payload.
    let normalized = if formula_contains_select(formula) {
        std::borrow::Cow::Owned(normalize_decidable_array_read_over_write(formula))
    } else {
        std::borrow::Cow::Borrowed(formula)
    };
    let formula: &Formula = &normalized;
    let widened = if matches!(kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck)
        || formula_mentions_bitvector_theory(formula)
    {
        None
    } else if let Some((width, operand_names)) = find_unsigned_overflow_pattern(formula) {
        if allow_unsigned_bv_widening() {
            bv_translate_guard(formula, width, &operand_names)
                .or_else(|| try_widen_unsigned_relational_vc_to_bv_unchecked(formula))
        } else {
            None
        }
    } else {
        let mut has_large = false;
        if check_unsigned_int_literals(formula, &mut has_large)
            && has_large
            && allow_unsigned_bv_widening()
        {
            const CAP: u32 = 256;
            unsigned_arith_max_width(formula, CAP).and_then(|need| {
                let width = need.max(64).next_power_of_two().min(CAP);
                (need <= width).then(|| bv_widen_translate(formula, width)).flatten()
            })
        } else {
            None
        }
    };
    // gap-log #19 CLOSED AT THE LOWERING (2026-07-08): out-of-i64 integer
    // constants (the `u64::MAX` type-range bound) no longer need a refuse-to-emit
    // guard here — trust-mc's typed lowering Horner-encodes them in base 10^9
    // with only i64 literals (`lower_int_constant`, the exact shape ay's own
    // parser emits and its BigInt LIA stack decides), so the Int lane is
    // FAITHFUL: no wrap, no ex-falso. Constants beyond i128 still fail closed in
    // the lowering itself. Validated by the false-variant battery: the historic
    // ex-falso repro (false usize postcondition) REFUTES, never vacuously proves.
    let formula = widened.as_ref().unwrap_or(formula);
    let sort = infer_sort(formula).to_smtlib();
    let smtlib = formula.to_smtlib();
    // Temporary localization probe for the u64/usize typed-CHC gate (env-gated):
    // shows the real VC formula and whether it lowers to a typed predicate.
    if formula_debug_enabled() {
        let lowered = trust_spec_predicate_from_formula(formula).is_some();
        eprintln!(
            "TRUST_FORMULA_DEBUG: widened={} sort={sort} typed_lowered={lowered} smtlib={smtlib}",
            widened.is_some()
        );
    }
    // Trust (T4, 2026-10-10): the residual cliff the typed-payload guard below
    // named. `TrustContractBundle::validate` rejects ANY obligation metadata value
    // over the ceiling, and that one rejection discards the native TrustIr bundle
    // for the whole function: the exact fresh-VC rekey snapshot cannot bind, every
    // obligation of the function comes back `unknown` through
    // `fresh-vc-rekey-integrity`, and the Level-0 safety rows among them (the
    // `FullVerification::ArithmeticSafety`/`BoundsCheck` round trip) publish
    // `failed` — although each is an ordinary, modelable obligation. Measured on
    // trust-ir-conformance `refuse_template_fixtures::artifacts` (preview3, stage1
    // ed578e1a5): one VC's SMT-LIB rendering is 1,131,451 bytes, and 16 overflow /
    // slice rows failed that the kernel lane proves on the fresh VCs.
    //
    // The oversized rendering is replaced by a bounded marker that no SMT-LIB
    // parser accepts, and the typed payload is withheld as well, so the row reaches
    // no transport engine with any formula: it can only decline (`unknown`). The VC
    // digest still binds the complete source formula, and the identity
    // re-derivation calls this same function, so the rekey binds exactly. SOUND:
    // this removes a carrier, never adds a claim; it cannot turn an unproved row
    // into a proved one. Compiler-side lanes that read the fresh VC itself are
    // unaffected.
    //
    // T3 L4 (C06a): the omission is a hit of the same CAP site as the typed-payload
    // drop below (`trust_types::audit_ledger`).
    if trust_types::audit_ledger::cap_hit_if(
        smtlib.len() > MAX_TRANSPORT_METADATA_VALUE_BYTES,
        "crates/trust-mir-extract/src/verifier_api.rs:MAX_TRANSPORT_METADATA_VALUE_BYTES",
    ) {
        return smtlib_omitted_vc_formula_payload(sort, &smtlib);
    }
    if let Some(predicate) = trust_spec_predicate_from_formula(formula) {
        if let Ok(ContractPredicate::TrustIr { schema, value }) =
            predicate.into_contract_predicate()
        {
            // The preferred predicate encoder owns the canonical representation,
            // including when this value becomes embedded public-context text.
            if let Ok(payload) = trust_types::json_depth::into_string_owned_on_deep_stack(value) {
                return typed_vc_formula_payload_within_transport_limit(
                    schema,
                    sort,
                    smtlib,
                    payload,
                    widened.unwrap_or_else(|| normalized.into_owned()),
                    false,
                );
            }
        }
    }
    // VIOLATION-PRUNING fallback. When the VC does not fully lower to a typed predicate
    // because un-lowerable HYPOTHESIS conjuncts (BitVector/array/string atoms from
    // inlined `vec!`/box machinery — the `& 7` align, the sep heap `select`, kernel
    // `Name` strings) are conjoined with a lowerable error condition, drop the
    // un-lowerable conjuncts and lower the residue `P`. SOUNDNESS: `P` is a
    // sub-conjunction, so `formula ⟹ P`, hence `P UNSAT ⟹ formula UNSAT` — a PROVED
    // verdict establishes the original (never a false PROVE; adversarially validated).
    // The `pruned` flag makes the full-verifier downgrade a FAILED on `P` to UNKNOWN: a
    // counterexample to the fewer-hypotheses `P` is NOT a valid CE for the original.
    // This is what lets a box-allocator-DISCHARGED sep VC (`And([ptr!=0, ptr==0])`)
    // lower past the box-machinery context and PROVE, while a non-discharged residue
    // stays honestly UNKNOWN instead of surfacing a spurious CE.
    if let Some(pruned) = prune_to_lowerable_violation(formula) {
        if let Some(predicate) = trust_spec_predicate_from_formula(&pruned) {
            if let Ok(ContractPredicate::TrustIr { schema, value }) =
                predicate.into_contract_predicate()
            {
                if let Ok(payload) = trust_types::json_depth::into_string_owned_on_deep_stack(value)
                {
                    return typed_vc_formula_payload_within_transport_limit(
                        schema, sort, smtlib, payload, pruned, true,
                    );
                }
            }
        }
    }
    untyped_vc_formula_payload(sort, smtlib)
}

/// The verifier-API transport ceiling for a SINGLE obligation metadata value.
///
/// Aliased from the owning vocabulary crate rather than re-spelled: a local
/// copy could drift from the value `TrustContractBundle::validate` actually
/// enforces, and the whole point of this guard is that the two agree.
const MAX_TRANSPORT_METADATA_VALUE_BYTES: usize = trust_verifier_api::MAX_METADATA_VALUE_BYTES;

/// Build the no-typed-payload shape: schema/sort/smtlib only.
fn untyped_vc_formula_payload_dropped(
    sort: String,
    smtlib: String,
    dropped_bytes: Option<usize>,
) -> VcFormulaPayload {
    let mut p = untyped_vc_formula_payload(sort, smtlib);
    p.typed_payload_dropped_bytes = dropped_bytes;
    p
}

/// The no-formula shape for a VC whose SMT-LIB rendering exceeds the transport
/// ceiling: a bounded marker naming the rendering's length and SHA-256 stands in
/// for it, and no typed payload is offered (see the T4 note in
/// [`vc_formula_payload`]).
fn smtlib_omitted_vc_formula_payload(sort: String, smtlib: &str) -> VcFormulaPayload {
    let marker = format!(
        "{TRUST_VC_FORMULA_SMTLIB_OMITTED_PREFIX} {} bytes exceed the {MAX_TRANSPORT_METADATA_VALUE_BYTES}-byte transport ceiling; sha256={}",
        smtlib.len(),
        stable_sha256_hex(smtlib.as_bytes())
    );
    let mut p = untyped_vc_formula_payload(sort, marker);
    p.smtlib_omitted_bytes = Some(smtlib.len());
    p
}

fn untyped_vc_formula_payload(sort: String, smtlib: String) -> VcFormulaPayload {
    VcFormulaPayload {
        schema: TRUST_SYMBOLIC_FORMULA_SCHEMA.to_string(),
        sort,
        smtlib,
        typed_payload_dropped_bytes: None,
        smtlib_omitted_bytes: None,
        typed_payload: None,
        selected_formula: None,
        verified_seal: None,
        pruned: false,
    }
}

/// Emit the typed payload only when it FITS the verifier-API transport ceiling;
/// otherwise fall back to the ordinary no-typed-payload shape.
///
/// WHY THIS GUARD EXISTS. `TrustContractBundle::validate` rejects any obligation
/// metadata value larger than [`MAX_TRANSPORT_METADATA_VALUE_BYTES`] (1 MiB), and
/// the compiler validates the bundle exactly once — inside
/// `finalize_trust_mc_public_semantic_contracts`. A rejection there does NOT fail
/// just the oversized row: it discards the native TrustIr bundle for the WHOLE
/// function, which makes the exact fresh-VC rekey snapshot unbindable, which
/// drives EVERY obligation of that function to `unknown` through
/// `fresh-vc-rekey-integrity` — and the ones whose public `ObligationKind` has no
/// native `VcKind` reconstruction (`BoundsCheck`, `Assertion`) come back as
/// `unsupported_mir`, i.e. reported as a coverage gap rather than as the
/// transport-limit failure they are.
///
/// MEASURED (trustc 52e0a7031, 2026-08-22). The whole-function `Unreachable` VC
/// of a straight-line `?`-chain grows ~79 KB of typed payload per fallible call:
///
/// ```text
///   fallible calls   typed payload   smtlib    bundle
///        20            838,151       59,681    ok
///        21            913,854       65,293    ok
///        22            992,747       71,154    ok      (55,829 under the cap)
///        23             >1 MiB          —      REJECTED: "verifier obligation
///                                                metadata value exceeds the byte limit"
/// ```
///
/// a3d's `orient3d_i128` (23 calls) and `incircle_i128` sit past that cliff. Between
/// them they produced all 34 `unknown` rows of `./scripts/verify.sh` — including 18
/// bounds checks the Clean kernel had ALREADY discharged (`proof_evidence.status ==
/// "proved"`, `KernelRechecked`) yet which were reported `unsupported_mir` — plus 64
/// duplicated legacy rows (358 obligations reported where 294 exist).
///
/// SOUND: the typed payload is a proof CARRIER, not a claim. `typed_payload` is
/// already `Option`, and every consumer treats its absence as "no typed authority
/// here" and declines — `exact_selected_typed_formula` returns the recorded
/// `trust-vc MIR memory proof unit omitted …` reason, the identity re-derivation
/// (`verifier_vc_content_identity*`) calls THIS function, so both sides agree and
/// the rekey still binds. Dropping it can only make the verifier weaker on that
/// one row; it can never turn an Unknown into a Proved.
///
/// RESIDUAL (closed 2026-10-10, T4): `smtlib` is not droppable the same way — the
/// exact fresh-VC identity requires it present with an exact value — so a formula
/// whose SMT-LIB rendering alone exceeded 1 MiB still failed the bundle. It is now
/// replaced by a bounded omission marker that both the bundle and the identity
/// re-derivation compute (`smtlib_omitted_vc_formula_payload`), with the typed
/// payload withheld, before this guard is reached.
fn typed_vc_formula_payload_within_transport_limit(
    schema: String,
    sort: String,
    smtlib: String,
    typed_payload: String,
    selected_formula: Formula,
    pruned: bool,
) -> VcFormulaPayload {
    // T3 L4 (C06a): the typed-payload drop is a CAP site (`trust_types::audit_ledger`).
    if trust_types::audit_ledger::cap_hit_if(
        typed_payload.len() > MAX_TRANSPORT_METADATA_VALUE_BYTES,
        "crates/trust-mir-extract/src/verifier_api.rs:MAX_TRANSPORT_METADATA_VALUE_BYTES",
    ) {
        if formula_debug_enabled() {
            eprintln!(
                "TRUST_FORMULA_DEBUG: dropping typed payload of {} bytes (transport ceiling {MAX_TRANSPORT_METADATA_VALUE_BYTES}); row keeps schema/sort/smtlib and declines the typed lanes",
                typed_payload.len()
            );
        }
        return untyped_vc_formula_payload_dropped(sort, smtlib, Some(typed_payload.len()));
    }
    let verified_seal =
        Some(function_scan::fx_hash_selected_formula(&schema, &typed_payload, &selected_formula));
    VcFormulaPayload {
        schema,
        sort,
        smtlib,
        typed_payload_dropped_bytes: None,
        smtlib_omitted_bytes: None,
        typed_payload: Some(typed_payload),
        selected_formula: Some(selected_formula),
        verified_seal,
        pruned,
    }
}

/// Prune a VIOLATION formula to its largest sub-conjunction that lowers to a typed
/// `TrustSpecPredicate`, dropping conjuncts containing atoms the lowerer cannot model.
/// Returns `None` if nothing lowerable remains. Soundness: a sub-conjunction `P` of a
/// violation satisfies `P UNSAT ⇒ original UNSAT` (the `pruned` flag handles the SAT
/// case — a CE to `P` ⇒ UNKNOWN, not a false counterexample).
fn prune_to_lowerable_violation(formula: &Formula) -> Option<Formula> {
    let pruned = prune_unlowerable_conjuncts(formula)?;
    trust_spec_predicate_from_formula(&pruned).map(|_| pruned)
}

/// Recursively keep only the conjuncts (through nested `And`s) that lower to a typed
/// predicate; drop the rest. A non-`And` node is kept iff it lowers on its own.
fn prune_unlowerable_conjuncts(formula: &Formula) -> Option<Formula> {
    match formula {
        Formula::And(conjuncts) => {
            let kept: Vec<Formula> =
                conjuncts.iter().filter_map(prune_unlowerable_conjuncts).collect();
            match kept.len() {
                0 => None,
                1 => kept.into_iter().next(),
                _ => Some(Formula::And(kept)),
            }
        }
        other => trust_spec_predicate_from_formula(other).is_some().then(|| other.clone()),
    }
}

/// Canonical digest of the complete compiler-owned function source carrier.
///
/// Bundle conversion writes this value to every generated row. Callers that
/// validate multiple rows should compute it once and reuse it with
/// [`verifier_vc_content_identity_with_source_digest_and_crate_name`] inside an
/// independently authenticated `*_with_compiler_identity` bundle envelope.
#[must_use]
pub fn verifier_source_digest(function: &VerifiableFunction) -> String {
    let bytes = serde_json::to_vec(function).expect(
        "VerifiableFunction is the canonical serializable Trust model; refusing \
         to replace full source identity with a def-path-only digest",
    );
    stable_sha256_hex(&bytes)
}

// Digest material canonicalization. `trust_types::canonical_digest_json_value`
// is `serde_json::to_value` with a wide-integer fallback: `serde_json::Value`
// cannot represent integers outside the i64/u64 range, so a bare `to_value`
// here ICE'd the compiler on any VC formula carrying i128/u128 type-range
// literals (every i128 overflow VC carries `i128::MIN`/`i128::MAX` bounds).
// The verifier must never crash on material the Formula model can express;
// digest identity needs only determinism and injectivity, so out-of-range
// integers digest as tagged decimal strings (see `trust_types::json_digest`
// for the identity/injectivity argument). Every previously-digestible value
// keeps byte-identical digests (the fast path is unchanged); only formulas
// that previously had NO digest at all — they panicked — gain one. The expect
// stays the fail-closed backstop for genuinely unserializable material.
macro_rules! json_digest_value {
    ($value:expr) => {{
        let value = $value;
        trust_types::canonical_digest_json_value(value).expect(
            "canonical Trust verifier-api digest material must serialize; refusing \
             a debug-shaped fallback identity",
        )
    }};
}

fn contract_predicate_digest(
    function: &VerifiableFunction,
    index: usize,
    contract: &Contract,
    predicate: &ContractPredicate,
) -> String {
    let mut material = serde_json::Map::new();
    material.insert(
        "schema".to_string(),
        JsonValue::String("trust-mir-extract.contract-predicate-digest.v1".to_string()),
    );
    material.insert("function".to_string(), JsonValue::String(function.def_path.clone()));
    material.insert("contract_index".to_string(), JsonValue::String(index.to_string()));
    material.insert(
        "contract_kind".to_string(),
        JsonValue::String(contract.kind.attr_name().to_string()),
    );
    material.insert("contract_span".to_string(), json_digest_value!(&contract.span));
    material.insert("predicate".to_string(), json_digest_value!(predicate));
    stable_json_digest(&JsonValue::Object(material))
}

/// The schema of [`vc_content_digest`]'s material (T3 L4, C09w).
const VC_CONTENT_DIGEST_SCHEMA: &str = "trust-mir-extract.vc-digest.v2";

/// A VC's content digest, `trust.vc.digest.sha256` on its obligation.
///
/// Trust (T3 L4, C09w; design §8): v2 binds the function, the VC's index and kind, its
/// location, its formula's schema and sort, as v1 did, and the formula by its Merkle digest
/// (`trust_types::formula_merkle`) in place of its canonical JSON. The SMT-LIB text and the
/// typed payload, two more encodings of the same formula that v1 also bound, leave it: both
/// are derived from the formula and the function, which every consumer that checks the
/// digest re-derives them from. A formula with no Merkle digest (none is known: the DAG is
/// fresh and every payload serializes) panics, as material that does not serialize always
/// has here: there is no alternate text identity to fall back to.
fn vc_content_digest(
    function: &VerifiableFunction,
    index: usize,
    vc: &VerificationCondition,
    payload: &VcFormulaPayload,
) -> String {
    let formula = trust_types::formula_merkle::formula_digest(&vc.formula)
        .expect("a VC formula must have a Merkle digest; refusing an alternate text identity");
    let mut material = serde_json::Map::new();
    material.insert("schema".to_string(), JsonValue::String(VC_CONTENT_DIGEST_SCHEMA.to_string()));
    material.insert("function".to_string(), JsonValue::String(function.def_path.clone()));
    material.insert("vc_index".to_string(), JsonValue::String(index.to_string()));
    material.insert("vc_kind".to_string(), json_digest_value!(&vc.kind));
    material.insert("location".to_string(), json_digest_value!(&vc.location));
    material.insert("formula_schema".to_string(), JsonValue::String(payload.schema.clone()));
    material.insert("formula_sort".to_string(), JsonValue::String(payload.sort.clone()));
    material.insert("formula_merkle".to_string(), JsonValue::String(formula.to_hex()));
    stable_json_digest(&JsonValue::Object(material))
}

fn stable_json_digest(value: &JsonValue) -> String {
    trust_types::canonical_json_sha256(value).expect(
        "canonical JSON digest material must serialize; refusing an alternate \
         text identity",
    )
}

fn trust_spec_predicate_from_formula(formula: &Formula) -> Option<TrustSpecPredicate> {
    let mut lowerer = FormulaLowerer::default();
    let root = lowerer.lower_formula(formula, Some(TrustSpecSort::Bool))?;
    if root.sort != TrustSpecSort::Bool {
        return None;
    }
    let predicate = TrustSpecPredicate::new(root, lowerer.variables());
    predicate.validate().ok().map(|()| predicate)
}

#[derive(Default)]
struct FormulaLowerer {
    variables: BTreeMap<String, TrustSpecVariable>,
    quantified: BTreeMap<String, TrustSpecSort>,
}

impl FormulaLowerer {
    fn variables(self) -> Vec<TrustSpecVariable> {
        self.variables.into_values().collect()
    }

    fn lower_formula(
        &mut self,
        formula: &Formula,
        expected: Option<TrustSpecSort>,
    ) -> Option<TrustSpecExpr> {
        let lowered = match formula {
            Formula::Bool(value) => TrustSpecExpr::bool_literal(*value),
            Formula::Int(value) => TrustSpecExpr::int_literal(value.to_string()),
            Formula::UInt(value) => TrustSpecExpr::int_literal(value.to_string()),
            Formula::Var(name, sort) => self.lower_variable(name, sort, expected)?,
            Formula::SymVar(symbol, sort) => {
                self.lower_variable(symbol.as_str(), sort, expected)?
            }
            Formula::Not(inner) => {
                let inner = self.lower_formula(inner, Some(TrustSpecSort::Bool))?;
                TrustSpecExpr::unary(TrustSpecUnaryOp::Not, inner)
            }
            Formula::And(terms) => self.lower_bool_terms(TrustSpecBinaryOp::And, terms)?,
            Formula::Or(terms) => self.lower_bool_terms(TrustSpecBinaryOp::Or, terms)?,
            Formula::Implies(lhs, rhs) => {
                let lhs = self.lower_formula(lhs, Some(TrustSpecSort::Bool))?;
                let rhs = self.lower_formula(rhs, Some(TrustSpecSort::Bool))?;
                TrustSpecExpr::binary(TrustSpecBinaryOp::Implies, lhs, rhs)
            }
            // The IEEE literal, carried by bits exactly as the public IR stores
            // it. Float ARITHMETIC has no public spelling and stays refused by
            // validation, which is why only the literal is lowered here and the
            // `Fp*` arithmetic nodes are deliberately absent.
            Formula::FpConst { bits, eb, sb } => {
                TrustSpecExpr::float_literal(u64::try_from(*bits).ok()?, *eb, *sb)
            }
            // `Formula::Eq` is STRUCTURAL `=`; the public IR's `eq` over a Float
            // sort is IEEE equality (`trust_verifier_api` validation: NaN != NaN,
            // +0.0 == -0.0). Over floats the two disagree on exactly the values
            // that matter, so a structural float equation has no public spelling
            // and fails closed here rather than being relabelled IEEE
            // (SPEC-FLOAT-EQ-STRUCTURAL-1).
            Formula::Eq(lhs, rhs) => {
                let lowered = self.lower_binary_formula(lhs, TrustSpecBinaryOp::Eq, rhs)?;
                if binary_compares_float(&lowered) {
                    return None;
                }
                lowered
            }
            // IEEE equality IS the public `eq` over one Float sort — the spelling
            // a float contract `==` (Rust `PartialEq`) takes once its operand sorts
            // are known. Anything else under `FpEq` (a bit-vector operand left by a
            // callsite substitution, mixed formats) has no public spelling.
            Formula::FpEq(lhs, rhs) => {
                let lowered = self.lower_binary_formula(lhs, TrustSpecBinaryOp::Eq, rhs)?;
                let same_float = matches!(
                    &lowered.kind,
                    trust_verifier_api::TrustSpecExprKind::Binary { lhs, rhs, .. }
                        if matches!(lhs.sort, TrustSpecSort::Float { .. }) && lhs.sort == rhs.sort
                );
                if !same_float {
                    return None;
                }
                lowered
            }
            Formula::Lt(lhs, rhs) => self.lower_binary_formula(lhs, TrustSpecBinaryOp::Lt, rhs)?,
            Formula::Le(lhs, rhs) => self.lower_binary_formula(lhs, TrustSpecBinaryOp::Le, rhs)?,
            Formula::Gt(lhs, rhs) => self.lower_binary_formula(lhs, TrustSpecBinaryOp::Gt, rhs)?,
            Formula::Ge(lhs, rhs) => self.lower_binary_formula(lhs, TrustSpecBinaryOp::Ge, rhs)?,
            Formula::Add(lhs, rhs) => {
                self.lower_binary_formula(lhs, TrustSpecBinaryOp::Add, rhs)?
            }
            Formula::Sub(lhs, rhs) => {
                self.lower_binary_formula(lhs, TrustSpecBinaryOp::Sub, rhs)?
            }
            Formula::Mul(lhs, rhs) => {
                self.lower_binary_formula(lhs, TrustSpecBinaryOp::Mul, rhs)?
            }
            Formula::Div(lhs, rhs) => {
                self.lower_binary_formula(lhs, TrustSpecBinaryOp::Div, rhs)?
            }
            Formula::Rem(lhs, rhs) => {
                self.lower_binary_formula(lhs, TrustSpecBinaryOp::Mod, rhs)?
            }
            Formula::Neg(inner) => {
                let inner = self.lower_formula(inner, Some(TrustSpecSort::Int))?;
                TrustSpecExpr::unary(TrustSpecUnaryOp::Neg, inner)
            }
            Formula::Forall(bindings, body) => {
                self.lower_formula_quantifier(TrustSpecQuantifier::Forall, bindings, body)?
            }
            Formula::Exists(bindings, body) => {
                self.lower_formula_quantifier(TrustSpecQuantifier::Exists, bindings, body)?
            }
            Formula::Select(array, index) => {
                let array_sort = formula_sort_hint(array)?;
                let TrustSpecSort::Array { element } = array_sort else {
                    return None;
                };
                let array = self.lower_formula(array, Some(array_sort))?;
                let index = self.lower_formula(index, Some(TrustSpecSort::Int))?;
                TrustSpecExpr::index(array, index, element.expression_sort())
            }
            Formula::BitVec { value, width } => {
                TrustSpecExpr::bitvec_literal(value.to_string(), *width)
            }
            Formula::BvAdd(lhs, rhs, w) => {
                self.lower_bv_binary(lhs, TrustSpecBvBinaryOp::Add, rhs, *w)?
            }
            Formula::BvSub(lhs, rhs, w) => {
                self.lower_bv_binary(lhs, TrustSpecBvBinaryOp::Sub, rhs, *w)?
            }
            Formula::BvMul(lhs, rhs, w) => {
                self.lower_bv_binary(lhs, TrustSpecBvBinaryOp::Mul, rhs, *w)?
            }
            Formula::BvUDiv(lhs, rhs, w) => {
                self.lower_bv_binary(lhs, TrustSpecBvBinaryOp::Udiv, rhs, *w)?
            }
            Formula::BvURem(lhs, rhs, w) => {
                self.lower_bv_binary(lhs, TrustSpecBvBinaryOp::Urem, rhs, *w)?
            }
            Formula::BvSRem(lhs, rhs, w) => {
                self.lower_bv_binary(lhs, TrustSpecBvBinaryOp::Srem, rhs, *w)?
            }
            Formula::BvAnd(lhs, rhs, w) => {
                self.lower_bv_binary(lhs, TrustSpecBvBinaryOp::And, rhs, *w)?
            }
            Formula::BvOr(lhs, rhs, w) => {
                self.lower_bv_binary(lhs, TrustSpecBvBinaryOp::Or, rhs, *w)?
            }
            Formula::BvXor(lhs, rhs, w) => {
                self.lower_bv_binary(lhs, TrustSpecBvBinaryOp::Xor, rhs, *w)?
            }
            Formula::BvShl(lhs, rhs, w) => {
                self.lower_bv_binary(lhs, TrustSpecBvBinaryOp::Shl, rhs, *w)?
            }
            Formula::BvLShr(lhs, rhs, w) => {
                self.lower_bv_binary(lhs, TrustSpecBvBinaryOp::Lshr, rhs, *w)?
            }
            Formula::BvAShr(lhs, rhs, w) => {
                self.lower_bv_binary(lhs, TrustSpecBvBinaryOp::Ashr, rhs, *w)?
            }
            Formula::BvULt(lhs, rhs, w) => {
                self.lower_bv_binary(lhs, TrustSpecBvBinaryOp::Ult, rhs, *w)?
            }
            Formula::BvULe(lhs, rhs, w) => {
                self.lower_bv_binary(lhs, TrustSpecBvBinaryOp::Ule, rhs, *w)?
            }
            Formula::BvSLt(lhs, rhs, w) => {
                self.lower_bv_binary(lhs, TrustSpecBvBinaryOp::Slt, rhs, *w)?
            }
            Formula::BvSLe(lhs, rhs, w) => {
                self.lower_bv_binary(lhs, TrustSpecBvBinaryOp::Sle, rhs, *w)?
            }
            // Width-changing unary ops: the result width is derived from the
            // LOWERED operand's own sort (these nodes carry no operand width),
            // so the operand is lowered without an expected sort first.
            Formula::BvSignExt(inner, extend_by) => {
                if *extend_by == 0 {
                    return None;
                }
                let inner = self.lower_formula(inner, None)?;
                let TrustSpecSort::BitVec { width: inner_width } = inner.sort else {
                    return None;
                };
                let result_width = inner_width.checked_add(*extend_by)?;
                TrustSpecExpr::bv_unary(
                    TrustSpecBvUnaryOp::SignExt { extend_by: *extend_by },
                    inner,
                    result_width,
                )
            }
            Formula::BvExtract { inner, high, low } => {
                let inner = self.lower_formula(inner, None)?;
                let TrustSpecSort::BitVec { width: inner_width } = inner.sort else {
                    return None;
                };
                if *high < *low || *high >= inner_width {
                    return None;
                }
                TrustSpecExpr::bv_unary(
                    TrustSpecBvUnaryOp::Extract { high: *high, low: *low },
                    inner,
                    *high - *low + 1,
                )
            }
            Formula::BvNot(inner, w) => {
                let inner = self.lower_formula(inner, Some(TrustSpecSort::BitVec { width: *w }))?;
                TrustSpecExpr::bv_unary(TrustSpecBvUnaryOp::Not, inner, *w)
            }
            // Int→BV / BV→Int conversions (`int2bv` / `bv2nat`). These are what
            // let byte/nibble arithmetic (`x & 0x0F`, `hi << 4`) — modeled as an
            // Int local converted to BV for the bitwise op and back — lower to a
            // typed CHC predicate instead of falling to the un-lowerable
            // fallback. Faithful to `Formula::IntToBv`/`BvToInt`
            // (`trust-types` `ay_bridge::formula_to_expr`).
            Formula::IntToBv(inner, w) => {
                let inner = self.lower_formula(inner, Some(TrustSpecSort::Int))?;
                TrustSpecExpr::bv_from_int(inner, *w)
            }
            Formula::BvToInt(inner, w, signed) => {
                let inner = self.lower_formula(inner, Some(TrustSpecSort::BitVec { width: *w }))?;
                TrustSpecExpr::int_from_bv(inner, *signed, *w)
            }
            // Conditional (`if c { a } else { b }`) — the branch-merge a
            // u128-wrapping clamp/select body produces (`Formula::Ite`,
            // trust-ir-contract `formula.rs`). Faithful and sort-preserving: the
            // condition lowers as Bool and BOTH arms lower under one shared result
            // sort (the else-arm is forced to the then-arm's sort), so this carries
            // a genuine conditional value and never manufactures one. A
            // sort-mismatched or unlowerable-arm `Ite` returns `None` here, so the
            // VC keeps falling to the symbolic schema fail-closed — never a
            // partial/lossy typed payload.
            Formula::Ite(cond, then_branch, else_branch) => {
                let cond = self.lower_formula(cond, Some(TrustSpecSort::Bool))?;
                let then_expr = self.lower_formula(then_branch, None)?;
                let else_expr = self.lower_formula(else_branch, Some(then_expr.sort))?;
                TrustSpecExpr::ite(cond, then_expr, else_expr)
            }
            _ => return None,
        };
        (expected.map_or(true, |expected| lowered.sort == expected)).then_some(lowered)
    }

    fn lower_variable(
        &mut self,
        name: &str,
        sort: &Sort,
        expected: Option<TrustSpecSort>,
    ) -> Option<TrustSpecExpr> {
        let sort =
            self.quantified.get(name).copied().or_else(|| formula_sort_to_spec_sort(sort))?;
        if let Some(expected) = expected {
            if sort != expected {
                return None;
            }
        }
        let origin = if self.quantified.contains_key(name) {
            TrustSpecVariableOrigin::Quantified
        } else {
            TrustSpecVariableOrigin::Inferred
        };
        self.record_variable(name, sort, origin)?;
        Some(TrustSpecExpr::variable(name.to_string(), sort))
    }

    fn lower_bool_terms(
        &mut self,
        op: TrustSpecBinaryOp,
        terms: &[Formula],
    ) -> Option<TrustSpecExpr> {
        let mut terms =
            terms.iter().map(|term| self.lower_formula(term, Some(TrustSpecSort::Bool)));
        let first = terms.next().unwrap_or_else(|| {
            Some(TrustSpecExpr::bool_literal(matches!(op, TrustSpecBinaryOp::And)))
        })?;
        terms.try_fold(first, |lhs, rhs| rhs.map(|rhs| TrustSpecExpr::binary(op, lhs, rhs)))
    }

    fn lower_binary_formula(
        &mut self,
        lhs: &Formula,
        op: TrustSpecBinaryOp,
        rhs: &Formula,
    ) -> Option<TrustSpecExpr> {
        let operand_sort = match op {
            TrustSpecBinaryOp::And | TrustSpecBinaryOp::Or | TrustSpecBinaryOp::Implies => {
                Some(TrustSpecSort::Bool)
            }
            TrustSpecBinaryOp::Add
            | TrustSpecBinaryOp::Sub
            | TrustSpecBinaryOp::Mul
            | TrustSpecBinaryOp::Div
            | TrustSpecBinaryOp::Mod
            | TrustSpecBinaryOp::Lt
            | TrustSpecBinaryOp::Le
            | TrustSpecBinaryOp::Gt
            | TrustSpecBinaryOp::Ge => {
                // Ordering is Int by default, and takes its sort from the
                // operands ONLY when they are FLOAT. The public fragment admits
                // float comparisons, so forcing Int here refused an authored
                // magnitude bound the subset actually contains.
                //
                // Only Float, deliberately. A bit-vector comparison has its own
                // lowering (`lower_bv_binary`) with its own signedness, and
                // routing one through the integer spelling would silently change
                // what it means.
                match formula_sort_hint(lhs).or_else(|| formula_sort_hint(rhs)) {
                    Some(float @ TrustSpecSort::Float { .. }) => Some(float),
                    _ => Some(TrustSpecSort::Int),
                }
            }
            TrustSpecBinaryOp::Eq | TrustSpecBinaryOp::Ne => {
                formula_sort_hint(lhs).or_else(|| formula_sort_hint(rhs))
            }
            _ => return None,
        };
        let lhs = self.lower_formula(lhs, operand_sort)?;
        let rhs = self.lower_formula(rhs, operand_sort)?;
        Some(TrustSpecExpr::binary(op, lhs, rhs))
    }

    fn lower_bv_binary(
        &mut self,
        lhs: &Formula,
        op: TrustSpecBvBinaryOp,
        rhs: &Formula,
        width: u32,
    ) -> Option<TrustSpecExpr> {
        let operand = Some(TrustSpecSort::BitVec { width });
        let lhs = self.lower_formula(lhs, operand)?;
        let rhs = self.lower_formula(rhs, operand)?;
        Some(TrustSpecExpr::bv_binary(op, lhs, rhs, width))
    }

    fn lower_formula_quantifier(
        &mut self,
        quantifier: TrustSpecQuantifier,
        bindings: &[(trust_types::Symbol, Sort)],
        body: &Formula,
    ) -> Option<TrustSpecExpr> {
        let [(symbol, sort)] = bindings else {
            return None;
        };
        let sort = formula_sort_to_spec_sort(sort)?;
        let name = symbol.as_str();
        let previous = self.quantified.insert(name.to_string(), sort);
        self.record_variable(name, sort, TrustSpecVariableOrigin::Quantified)?;
        let body = self.lower_formula(body, Some(TrustSpecSort::Bool));
        if let Some(previous) = previous {
            self.quantified.insert(name.to_string(), previous);
        } else {
            self.quantified.remove(name);
        }
        Some(TrustSpecExpr::quantifier(quantifier, name.to_string(), sort, body?))
    }

    fn record_variable(
        &mut self,
        name: &str,
        sort: TrustSpecSort,
        origin: TrustSpecVariableOrigin,
    ) -> Option<()> {
        if let Some(existing) = self.variables.get(name) {
            return (existing.sort == sort).then_some(());
        }
        self.variables
            .insert(name.to_string(), TrustSpecVariable { name: name.to_string(), sort, origin });
        Some(())
    }
}

fn formula_sort_hint(formula: &Formula) -> Option<TrustSpecSort> {
    formula_sort_to_spec_sort(&infer_sort(formula))
}

/// Whether a lowered public comparison has a Float-sorted operand.
fn binary_compares_float(expr: &TrustSpecExpr) -> bool {
    matches!(
        &expr.kind,
        trust_verifier_api::TrustSpecExprKind::Binary { lhs, rhs, .. }
            if matches!(lhs.sort, TrustSpecSort::Float { .. })
                || matches!(rhs.sort, TrustSpecSort::Float { .. })
    )
}

fn formula_sort_to_spec_sort(sort: &Sort) -> Option<TrustSpecSort> {
    match sort {
        Sort::Bool => Some(TrustSpecSort::Bool),
        Sort::Int => Some(TrustSpecSort::Int),
        Sort::BitVec(width) => Some(TrustSpecSort::BitVec { width: *width }),
        // The public IR already carries an IEEE sort, and its fragment is
        // deliberately literals, variables and COMPARISONS — which is exactly
        // what a float magnitude bound is. Without this arm a float-sorted
        // contract variable had no public spelling, so the clause was refused as
        // outside the subset even though the subset contains it.
        Sort::Float { eb, sb } => Some(TrustSpecSort::Float { eb: *eb, sb: *sb }),
        Sort::Array(index, element) if index.as_ref() == &Sort::Int => {
            Some(TrustSpecSort::Array { element: formula_sort_to_spec_scalar_sort(element)? })
        }
        Sort::Array(_, _) => None,
        #[allow(unreachable_patterns)]
        _ => None,
    }
}

fn formula_sort_to_spec_scalar_sort(sort: &Sort) -> Option<TrustSpecScalarSort> {
    match sort {
        Sort::Bool => Some(TrustSpecScalarSort::Bool),
        Sort::Int => Some(TrustSpecScalarSort::Int),
        Sort::BitVec(width) => Some(TrustSpecScalarSort::BitVec { width: *width }),
        Sort::Array(_, _) => None,
        #[allow(unreachable_patterns)]
        _ => None,
    }
}

fn vc_engine_formula_metadata(
    kind: &ObligationKind,
    vc_kind: &VcKind,
    formula_schema: &str,
) -> Vec<MetadataEntry> {
    let mut metadata = Vec::with_capacity(3);
    if trust_mc_formula_obligation(kind, vc_kind) {
        metadata.push(MetadataEntry {
            key: "trust.vc.engine.trust-mc.formula_schema".to_string(),
            value: formula_schema.to_string(),
        });
    }
    if trust_wp_formula_obligation(kind) {
        metadata.push(MetadataEntry {
            key: "trust.vc.engine.trust-wp.formula_schema".to_string(),
            value: formula_schema.to_string(),
        });
    }
    if trust_vc_formula_obligation(kind) {
        metadata.push(MetadataEntry {
            key: "trust.vc.engine.trust-vc.formula_schema".to_string(),
            value: formula_schema.to_string(),
        });
    }
    metadata
}

/// Trust: temporal-model transport for the native ty engine.
///
/// A temporal VC's checkable content is its `VcKind` payload (CTL/LTL property
/// plus optional inline `StateMachineMetadata`), not its formula — the formula
/// is a deliberate placeholder Bool so no constant-folder steals the VC. The
/// public `TrustObligation` has no kind-payload field, so serialize the whole
/// temporal `VcKind` into obligation metadata; `NativeTyEngine` rebuilds the
/// machine from this entry and model-checks it. Serialization failure is
/// recorded loudly (the engine then reports the missing model, fail-closed)
/// rather than silently dropping the model.
fn ty_temporal_model_metadata(kind: &VcKind) -> Vec<MetadataEntry> {
    let Some(payload) = trust_types::TyTemporalModelPayload::from_vc_kind(kind) else {
        return Vec::new();
    };
    match payload.to_metadata_value() {
        Ok(value) => {
            vec![MetadataEntry {
                key: trust_types::TY_TEMPORAL_MODEL_METADATA_KEY.to_string(),
                value,
            }]
        }
        Err(error) => vec![MetadataEntry {
            key: format!("{}.serialize_error", trust_types::TY_TEMPORAL_MODEL_METADATA_KEY),
            value: error.to_string(),
        }],
    }
}

fn hardened_vc_metadata(kind: &VcKind) -> Vec<MetadataEntry> {
    let Some(category) = kind.hardened_category() else {
        return Vec::new();
    };
    let family =
        kind.hardened_family_tag().unwrap_or_else(|| format!("hardened_{}", category.as_tag()));
    let mut metadata = vec![
        MetadataEntry {
            key: TRUST_VC_HARDENED_CATEGORY_METADATA_KEY.to_string(),
            value: category.as_tag().to_string(),
        },
        MetadataEntry { key: TRUST_VC_HARDENED_FAMILY_METADATA_KEY.to_string(), value: family },
    ];

    let boundary = match kind {
        VcKind::HardenedBoundary { callee, detail, .. } => Some((callee.as_str(), detail.as_str())),
        VcKind::Assertion { message } if message.starts_with("[unsafe:ffi]") => {
            Some(("unsafe_ffi_assertion", message.as_str()))
        }
        VcKind::Assertion { message } if message.starts_with("[unsafe") => {
            Some(("unsafe_assertion", message.as_str()))
        }
        VcKind::UnsafeOperation { desc } => Some(("unsafe_operation", desc.as_str())),
        VcKind::FfiBoundaryViolation { callee, desc } => Some((callee.as_str(), desc.as_str())),
        _ => None,
    };

    if let Some((callee, detail)) = boundary {
        metadata.extend([
            MetadataEntry {
                key: TRUST_VC_HARDENED_CALLEE_METADATA_KEY.to_string(),
                value: callee.to_string(),
            },
            MetadataEntry {
                key: TRUST_VC_HARDENED_DETAIL_METADATA_KEY.to_string(),
                value: detail.to_string(),
            },
        ]);
    }

    metadata
}

fn trust_mc_formula_obligation(kind: &ObligationKind, vc_kind: &VcKind) -> bool {
    match (kind, vc_kind) {
        (ObligationKind::ArithmeticSafety, _)
        | (ObligationKind::Assertion, _)
        | (ObligationKind::Precondition, _)
        | (ObligationKind::Postcondition, _)
        | (ObligationKind::LoopInvariant, _) => true,
        (ObligationKind::Custom { namespace, .. }, _) => namespace == TRUST_VC_HARDENED_NAMESPACE,
        _ => false,
    }
}

fn trust_wp_formula_obligation(kind: &ObligationKind) -> bool {
    matches!(
        kind,
        ObligationKind::Precondition
            | ObligationKind::Postcondition
            | ObligationKind::LoopInvariant
            | ObligationKind::Refinement
            | ObligationKind::Termination
            | ObligationKind::Assertion
    )
}

fn trust_vc_formula_obligation(kind: &ObligationKind) -> bool {
    // BoundsCheck rides the same trust-vc MIR-memory proof-unit transport as
    // MemorySafety/Ownership: the unit's predicate is the negated (guard-
    // conjoined) VC formula, discharged by TrustVcTrustEngine with a
    // replayable certificate. Without this arm, bounds obligations reached
    // the native bundle as Pending with NO certificate and
    // validate_trust_vc_request failed the WHOLE bundle
    // (MissingTrustVcEvidenceForObligation) — one bounds obligation poisoned
    // every other obligation in the function.
    //
    // `trust.vc.unbounded_allocation` (#nia-oom) joins the SAME transport: the
    // unit's predicate is the negated `count >= CEILING` capacity VC (guards
    // conjoined) — the exact formula alloc_vcs.rs emits and the front line
    // already kernel-certifies. This is the ONLY route the namespace may take:
    // it stays out of the trust-mc formula set below and out of the native
    // whole-function CHC (the recorded P0; see `vc_obligation_kind`).
    matches!(
        kind,
        ObligationKind::MemorySafety | ObligationKind::Ownership | ObligationKind::BoundsCheck
    ) || matches!(
        kind,
        ObligationKind::Custom { namespace, .. }
            if namespace == TRUST_VC_UNBOUNDED_ALLOCATION_NAMESPACE
    )
}

fn trust_vc_mir_memory_required_strength(kind: &ObligationKind) -> Option<ProofStrength> {
    trust_vc_formula_obligation(kind)
        .then(|| ProofStrength::certified(ReasoningKind::OwnershipAnalysis))
}

#[cfg(test)]
fn trust_vc_mir_memory_metadata(
    function: &VerifiableFunction,
    vc: &VerificationCondition,
    vc_index: usize,
    obligation_kind: &ObligationKind,
    formula_payload: &VcFormulaPayload,
) -> Vec<MetadataEntry> {
    let def_path_id = trust_types::canonical_artifact_id_component(&function.def_path);
    let memory_scan = std::cell::OnceCell::new();
    trust_vc_mir_memory_metadata_cached(
        function,
        vc,
        vc_index,
        obligation_kind,
        formula_payload,
        &def_path_id,
        &memory_scan,
    )
}

fn trust_vc_mir_memory_metadata_cached(
    function: &VerifiableFunction,
    vc: &VerificationCondition,
    vc_index: usize,
    obligation_kind: &ObligationKind,
    formula_payload: &VcFormulaPayload,
    def_path_id: &str,
    memory_scan: &std::cell::OnceCell<function_scan::TrustVcMemoryFunctionScan>,
) -> Vec<MetadataEntry> {
    if !trust_vc_formula_obligation(obligation_kind) {
        return Vec::new();
    }

    let obligation_id =
        format!("vc:{}:{}:{}", def_path_id, obligation_kind_label(obligation_kind), vc_index);

    let selected_formula = match formula_payload.exact_selected_typed_formula() {
        Ok(formula) => formula,
        Err(reason) => {
            return vec![MetadataEntry {
                key: TRUST_VC_MIR_MEMORY_PROOF_UNIT_UNSUPPORTED_METADATA_KEY.to_string(),
                value: reason,
            }];
        }
    };

    match trust_vc_mir_memory_proof_unit_payload(
        function,
        vc,
        &obligation_id,
        selected_formula,
        def_path_id,
        memory_scan,
    ) {
        Ok(payload) => {
            // The direct bridge validates byte-for-byte canonical JSON after
            // deserializing into the typed TrustVC proof-unit schema.  Sort
            // object keys recursively so the producer format is independent
            // of serde struct declaration order and map implementation.
            let payload = trust_types::canonical_json_value(&payload);
            let Ok(payload) = serde_json::to_string(&payload) else {
                return vec![MetadataEntry {
                    key: TRUST_VC_MIR_MEMORY_PROOF_UNIT_UNSUPPORTED_METADATA_KEY.to_string(),
                    value: "failed to serialize trust_vc MIR memory proof unit".to_string(),
                }];
            };
            vec![
                MetadataEntry {
                    key: TRUST_VC_CONDITION_ORIGIN_METADATA_KEY.to_string(),
                    value: TRUST_VC_CONDITION_ORIGIN_METADATA_VALUE.to_string(),
                },
                MetadataEntry {
                    key: TRUST_VC_PROOF_OBLIGATION_METADATA_KEY.to_string(),
                    value: TRUST_VC_PROOF_OBLIGATION_METADATA_VALUE.to_string(),
                },
                MetadataEntry {
                    key: TRUST_VC_OWNERSHIP_CONTEXT_METADATA_KEY.to_string(),
                    value: TRUST_VC_OWNERSHIP_CONTEXT_METADATA_VALUE.to_string(),
                },
                MetadataEntry {
                    key: TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_METADATA_KEY.to_string(),
                    value: TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_VERSION.to_string(),
                },
                MetadataEntry {
                    key: TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY.to_string(),
                    value: payload,
                },
            ]
        }
        Err(reason) => {
            if std::env::var("TRUST_NATIVE_DEBUG").is_ok() {
                eprintln!("[TRUST_VC_UNIT] {} unsupported: {reason}", function.def_path);
            }
            vec![MetadataEntry {
                key: TRUST_VC_MIR_MEMORY_PROOF_UNIT_UNSUPPORTED_METADATA_KEY.to_string(),
                value: reason,
            }]
        }
    }
}

fn trust_vc_mir_memory_proof_unit_payload(
    function: &VerifiableFunction,
    vc: &VerificationCondition,
    obligation_id: &str,
    selected_formula: &Formula,
    def_path_id: &str,
    memory_scan: &std::cell::OnceCell<function_scan::TrustVcMemoryFunctionScan>,
) -> Result<JsonValue, String> {
    reject_unsupported_trust_vc_memory_vc(&vc.kind)?;
    reject_unsupported_trust_vc_memory_formula(&vc.formula)?;
    reject_unsupported_trust_vc_memory_formula(selected_formula)?;

    // Lower the formula FIRST: its variable sorts are authoritative for the
    // signature. vcgen's Int-lane VC formulas model integer locals as
    // mathematical integers with explicit range constraints (the exact
    // semantics the ay lane proves); declaring the same locals as bit-vectors
    // in the signature made the sort-consistency check below reject every
    // bounds proof unit.
    let mut lowerer = TrustVcFormulaLowering::default();
    let predicate = lowerer.negated_vc_formula(selected_formula)?;

    let scan = memory_scan.get_or_init(|| function_scan::TrustVcMemoryFunctionScan::new(function));
    let return_sort = scan.validate_and_return_sort(&lowerer.variables)?;

    let mut params = Vec::new();
    let mut declared_variables = BTreeMap::new();
    for local in
        scan.locals.iter().filter(|local| local.index > 0 && local.index <= function.body.arg_count)
    {
        let sort = if let Some(sort) = lowerer.variables.get(&local.name) {
            // Formula-referenced param: take the formula's sort.
            sort.clone()
        } else {
            match &local.sort {
                Ok(sort) => sort.clone(),
                // A param the predicate never references and whose type has
                // no trust_vc sort (e.g. a slice fat pointer) is OMITTED from
                // the signature instead of refusing the whole unit. Sound:
                // the predicate is closed over the declared variables; an
                // unreferenced param adds no constraint.
                Err(_) => continue,
            }
        };
        declared_variables.insert(local.name.clone(), sort.clone());
        params.push(json!({
            "name": local.name,
            "sort": sort,
        }));
    }

    let mut verifier_variables = Vec::new();
    for (name, sort) in &lowerer.variables {
        match declared_variables.get(name) {
            Some(existing) if existing == sort => {}
            Some(existing) => {
                return Err(format!(
                    "trust-vc MIR memory formula variable `{name}` has sort {:?}, but the function signature declares {:?}",
                    sort, existing
                ));
            }
            None => {
                verifier_variables.push(json!({
                    "name": name,
                    "sort": sort,
                }));
            }
        }
    }

    let ownership = scan.ownership_state(&lowerer.variables)?;
    let mut obligation = json!({
        "id": obligation_id,
        "predicate": predicate,
    });
    if let Some(location) = trust_vc_source_location(&vc.location) {
        obligation
            .as_object_mut()
            .expect("obligation JSON is an object")
            .insert("location".to_string(), JsonValue::String(location));
    }

    let mut proof_unit = serde_json::Map::new();
    proof_unit.insert(
        "source_id".to_string(),
        JsonValue::String(format!("trust-mir-extract:{def_path_id}")),
    );
    proof_unit.insert("unit_id".to_string(), JsonValue::String(function.def_path.clone()));
    proof_unit.insert("display_name".to_string(), JsonValue::String(function.name.clone()));
    proof_unit.insert(
        "native_context".to_string(),
        json!({
            "function_signature": {
                "name": function.def_path.clone(),
                "params": params,
                "return_sort": return_sort,
            },
            "ownership": ownership,
        }),
    );
    // `TrustMirMemoryProofUnit::verifier_variables` uses serde's
    // `skip_serializing_if = "Vec::is_empty"`.  Mirror that typed producer
    // encoding exactly: the direct bridge deliberately rejects alternate JSON
    // spellings before it binds the public formula to the proof-unit predicate.
    if !verifier_variables.is_empty() {
        proof_unit.insert("verifier_variables".to_string(), JsonValue::Array(verifier_variables));
    }
    proof_unit.insert("obligations".to_string(), JsonValue::Array(vec![obligation]));
    proof_unit.insert(
        "metadata".to_string(),
        json!({
            "producer": "trust-mir-extract",
            "vc_kind": vc_kind_label(&vc.kind),
        }),
    );
    Ok(JsonValue::Object(proof_unit))
}

#[derive(Default)]
struct TrustVcFormulaLowering {
    variables: BTreeMap<String, JsonValue>,
}

impl TrustVcFormulaLowering {
    fn negated_vc_formula(&mut self, formula: &Formula) -> Result<JsonValue, String> {
        match formula {
            Formula::Bool(true) => Err(
                "trust-vc MIR memory proof unit omitted because the VC bad-state formula is definitely satisfiable"
                    .to_string(),
            ),
            Formula::Bool(false) => Ok(json!({
                "kind": "bool_literal",
                "value": true,
            })),
            Formula::Not(inner) => self.formula(inner),
            formula => Ok(json!({
                "kind": "not",
                "expr": self.formula(formula)?,
            })),
        }
    }

    fn formula(&mut self, formula: &Formula) -> Result<JsonValue, String> {
        match formula {
            Formula::Bool(value) => Ok(json!({
                "kind": "bool_literal",
                "value": value,
            })),
            Formula::Int(value) => Ok(json!({
                "kind": "int_literal",
                "value": value.to_string(),
                "sort": trust_vc_math_int_sort(),
            })),
            Formula::UInt(value) => {
                let value = i128::try_from(*value).map_err(|_| {
                    "trust-vc MIR memory formula unsigned literal exceeds i128".to_string()
                })?;
                Ok(json!({
                    "kind": "int_literal",
                    "value": value.to_string(),
                    // The selected public TrustSpec formula represents both
                    // `Int` and `UInt` literals with `TrustSpecSort::Int`.
                    // Preserve that exact public sort here: independently
                    // strengthening the direct unit literal to `Nat` makes the
                    // bridge's byte-for-semantics predicate correlation reject
                    // an otherwise identical selected formula.
                    "sort": trust_vc_math_int_sort(),
                }))
            }
            Formula::BitVec { value, width } => {
                if *value < 0 {
                    return Err(
                        "trust-vc MIR memory formula negative bit-vector literals are unsupported"
                            .to_string(),
                    );
                }
                Ok(json!({
                    "kind": "int_literal",
                    "value": value.to_string(),
                    "sort": trust_vc_bit_vector_sort(*width, false)?,
                }))
            }
            Formula::Var(name, sort) => self.variable(name, sort),
            Formula::SymVar(name, sort) => self.variable(name.as_str(), sort),
            Formula::Not(expr) => Ok(json!({
                "kind": "not",
                "expr": self.formula(expr)?,
            })),
            Formula::And(terms) => self.logic_chain("and", terms, true),
            Formula::Or(terms) => self.logic_chain("or", terms, false),
            Formula::Implies(premise, conclusion) => Ok(json!({
                "kind": "implies",
                "premise": self.formula(premise)?,
                "conclusion": self.formula(conclusion)?,
            })),
            Formula::Eq(left, right) => self.compare("eq", left, right),
            Formula::Lt(left, right) => self.compare("lt", left, right),
            Formula::Le(left, right) => self.compare("le", left, right),
            Formula::Gt(left, right) => self.compare("gt", left, right),
            Formula::Ge(left, right) => self.compare("ge", left, right),
            Formula::Add(left, right) => self.arith("add", left, right, trust_vc_math_int_sort()),
            Formula::Sub(left, right) => self.arith("sub", left, right, trust_vc_math_int_sort()),
            Formula::Mul(left, right) => self.arith("mul", left, right, trust_vc_math_int_sort()),
            Formula::Div(left, right) => self.arith("div", left, right, trust_vc_math_int_sort()),
            Formula::Rem(left, right) => self.arith("rem", left, right, trust_vc_math_int_sort()),
            Formula::BvAdd(left, right, width) => {
                self.arith("add", left, right, trust_vc_bit_vector_sort(*width, false)?)
            }
            Formula::BvSub(left, right, width) => {
                self.arith("sub", left, right, trust_vc_bit_vector_sort(*width, false)?)
            }
            Formula::BvMul(left, right, width) => {
                self.arith("mul", left, right, trust_vc_bit_vector_sort(*width, false)?)
            }
            Formula::BvUDiv(left, right, width) => {
                self.arith("div", left, right, trust_vc_bit_vector_sort(*width, false)?)
            }
            Formula::BvURem(left, right, width) => {
                self.arith("rem", left, right, trust_vc_bit_vector_sort(*width, false)?)
            }
            Formula::BvULt(left, right, _) => self.compare("lt", left, right),
            Formula::BvULe(left, right, _) => self.compare("le", left, right),
            _ => Err(format!(
                "trust-vc MIR memory proof unit omitted because formula node `{}` is outside the direct typed TrustExpr subset",
                formula_node_name(formula)
            )),
        }
    }

    fn variable(&mut self, name: &str, sort: &Sort) -> Result<JsonValue, String> {
        if trust_vc_unsupported_memory_marker(name) {
            return Err(format!(
                "trust-vc MIR memory proof unit omitted because formula variable `{name}` references unsupported heap/raw pointer/provenance detail"
            ));
        }
        let sort = trust_vc_sort_for_formula_sort(sort)?;
        match self.variables.get(name) {
            Some(existing) if existing == &sort => {}
            Some(existing) => {
                return Err(format!(
                    "trust-vc MIR memory formula variable `{name}` has conflicting sorts {:?} and {:?}",
                    existing, sort
                ));
            }
            None => {
                self.variables.insert(name.to_string(), sort.clone());
            }
        }
        Ok(json!({
            "kind": "variable",
            "name": name,
            "sort": sort,
        }))
    }

    fn logic_chain(
        &mut self,
        op: &str,
        terms: &[Formula],
        empty_value: bool,
    ) -> Result<JsonValue, String> {
        let mut terms = terms.iter();
        let Some(first) = terms.next() else {
            return Ok(json!({
                "kind": "bool_literal",
                "value": empty_value,
            }));
        };
        let mut expr = self.formula(first)?;
        for term in terms {
            expr = json!({
                "kind": "logic",
                "op": op,
                "left": expr,
                "right": self.formula(term)?,
            });
        }
        Ok(expr)
    }

    fn compare(&mut self, op: &str, left: &Formula, right: &Formula) -> Result<JsonValue, String> {
        Ok(json!({
            "kind": "compare",
            "op": op,
            "left": self.formula(left)?,
            "right": self.formula(right)?,
        }))
    }

    fn arith(
        &mut self,
        op: &str,
        left: &Formula,
        right: &Formula,
        sort: JsonValue,
    ) -> Result<JsonValue, String> {
        Ok(json!({
            "kind": "arith",
            "op": op,
            "left": self.formula(left)?,
            "right": self.formula(right)?,
            "sort": sort,
        }))
    }
}

fn reject_unsupported_trust_vc_memory_vc(kind: &VcKind) -> Result<(), String> {
    match kind {
        VcKind::UseAfterFree | VcKind::DoubleFree => Err(
            "trust-vc MIR memory proof unit omitted because heap allocation lifetime obligations are not supported by the direct MIR memory payload"
                .to_string(),
        ),
        VcKind::UnsafeOperation { desc } if trust_vc_unsupported_memory_marker(desc) => Err(
            "trust-vc MIR memory proof unit omitted because the unsafe operation requires raw pointer/dereference/provenance modeling"
                .to_string(),
        ),
        VcKind::FfiBoundaryViolation { .. }
        | VcKind::SavedReturnAddressOverwrite { .. }
        | VcKind::FormatStringViolation { .. }
        | VcKind::TaintedIndirectBranch { .. } => Err(format!(
            "trust-vc MIR memory proof unit omitted because `{}` is outside the direct Rust MIR ownership payload",
            vc_kind_label(kind)
        )),
        _ => Ok(()),
    }
}

pub(crate) fn reject_unsupported_trust_vc_memory_ty(ty: &Ty) -> Result<(), String> {
    match ty {
        Ty::RawPtr { .. } => Err(
            "trust-vc MIR memory proof unit omitted because raw pointer types require provenance modeling"
                .to_string(),
        ),
        Ty::Ref { inner, .. } => reject_unsupported_trust_vc_memory_ty(inner),
        Ty::Array { elem, .. } => reject_unsupported_trust_vc_memory_ty(elem),
        Ty::Slice { elem } => reject_unsupported_trust_vc_memory_ty(elem),
        Ty::Adt { name, .. } if trust_vc_unsupported_memory_marker(name) => Err(format!(
            "trust-vc MIR memory proof unit omitted because ADT `{name}` appears heap/raw pointer/provenance-backed"
        )),
        Ty::Adt { name, .. } => Err(format!(
            "trust-vc MIR memory proof unit omitted because ADT `{name}` layout is not represented in the direct MIR memory payload"
        )),
        Ty::Tuple(_)
        | Ty::Closure { .. }
        | Ty::FnDef { .. }
        | Ty::FnPtr { .. }
        | Ty::Dynamic { .. }
        | Ty::Coroutine { .. }
        | Ty::Unsupported { .. } => Err(format!(
            "trust-vc MIR memory proof unit omitted because type `{ty:?}` is outside the direct MIR memory subset"
        )),
        Ty::Bool | Ty::Int { .. } | Ty::Float { .. } | Ty::Bv(_) | Ty::Unit | Ty::Never => Ok(()),
        _ => Err(format!(
            "trust-vc MIR memory proof unit omitted because type `{ty:?}` is outside the direct MIR memory subset"
        )),
    }
}

fn reject_unsupported_trust_vc_memory_formula(formula: &Formula) -> Result<(), String> {
    let mut unsupported: Option<&str> = None;
    let _ = trust_types::all_formula_nodes(formula, &mut |node| match node {
        Formula::Var(name, _) if trust_vc_unsupported_memory_marker(name) => {
            unsupported = Some(name.as_str());
            false
        }
        Formula::SymVar(name, _) if trust_vc_unsupported_memory_marker(name.as_str()) => {
            unsupported = Some(name.as_str());
            false
        }
        _ => true,
    });
    if let Some(name) = unsupported {
        Err(format!(
            "trust-vc MIR memory proof unit omitted because formula variable `{name}` references unsupported heap/raw pointer/provenance detail"
        ))
    } else {
        Ok(())
    }
}

pub(crate) fn reject_unsupported_trust_vc_memory_statement(
    stmt: &Statement,
    locals: &[trust_types::LocalDecl],
) -> Result<(), String> {
    match stmt {
        Statement::Assign { place, rvalue, .. } => {
            if place_has_unsupported_deref(place, locals)
                || rvalue_has_unsupported_deref(rvalue, locals)
            {
                return Err(
                    "trust-vc MIR memory proof unit omitted because dereference projections are unsupported"
                        .to_string(),
                );
            }
            if matches!(rvalue, Rvalue::AddressOf(..)) {
                return Err(
                    "trust-vc MIR memory proof unit omitted because raw address-of requires provenance modeling"
                        .to_string(),
                );
            }
            Ok(())
        }
        Statement::SetDiscriminant { place, .. }
        | Statement::Deinit { place }
        | Statement::Retag { place }
        | Statement::PlaceMention(place) => {
            if place_has_unsupported_deref(place, locals) {
                Err(
                    "trust-vc MIR memory proof unit omitted because dereference projections are unsupported"
                        .to_string(),
                )
            } else {
                Ok(())
            }
        }
        Statement::Intrinsic { args, .. } => {
            if args.iter().any(|operand| operand_has_unsupported_deref(operand, locals)) {
                Err(
                    "trust-vc MIR memory proof unit omitted because intrinsic operands contain dereference projections"
                        .to_string(),
                )
            } else {
                Ok(())
            }
        }
        Statement::Unsupported { kind, detail, .. }
            if trust_vc_unsupported_memory_marker(kind)
                || trust_vc_unsupported_memory_marker(detail) =>
        {
            Err(
                "trust-vc MIR memory proof unit omitted because unsupported MIR statement mentions heap/raw pointer/provenance detail"
                    .to_string(),
            )
        }
        _ => Ok(()),
    }
}

pub(crate) fn reject_unsupported_trust_vc_memory_terminator(
    terminator: &Terminator,
    locals: &[trust_types::LocalDecl],
) -> Result<(), String> {
    match terminator {
        Terminator::SwitchInt { discr, .. } | Terminator::Assert { cond: discr, .. } => {
            if operand_has_unsupported_deref(discr, locals) {
                Err(
                    "trust-vc MIR memory proof unit omitted because terminator operands contain dereference projections"
                        .to_string(),
                )
            } else {
                Ok(())
            }
        }
        Terminator::Call { args, dest, atomic, .. } => {
            if args.iter().any(|operand| operand_has_unsupported_deref(operand, locals))
                || place_has_unsupported_deref(dest, locals)
                || atomic.as_ref().is_some_and(|atomic| {
                    place_has_unsupported_deref(&atomic.place, locals)
                        || atomic
                            .dest
                            .as_ref()
                            .is_some_and(|place| place_has_unsupported_deref(place, locals))
                })
            {
                Err(
                    "trust-vc MIR memory proof unit omitted because call operands contain dereference projections"
                        .to_string(),
                )
            } else {
                Ok(())
            }
        }
        Terminator::TailCall { args, atomic, .. } => {
            if args.iter().any(|operand| operand_has_unsupported_deref(operand, locals))
                || atomic.as_ref().is_some_and(|atomic| {
                    place_has_unsupported_deref(&atomic.place, locals)
                        || atomic
                            .dest
                            .as_ref()
                            .is_some_and(|place| place_has_unsupported_deref(place, locals))
                })
            {
                Err(
                    "trust-vc MIR memory proof unit omitted because tail-call operands contain dereference projections"
                        .to_string(),
                )
            } else {
                Ok(())
            }
        }
        Terminator::Drop { place, .. } => {
            if place_has_unsupported_deref(place, locals) {
                Err(
                    "trust-vc MIR memory proof unit omitted because drop target contains a dereference projection"
                        .to_string(),
                )
            } else {
                Ok(())
            }
        }
        Terminator::Opaque { kind, .. } if trust_vc_unsupported_memory_marker(kind) => Err(
            "trust-vc MIR memory proof unit omitted because opaque terminator mentions heap/raw pointer/provenance detail"
                .to_string(),
        ),
        _ => Ok(()),
    }
}

fn local_decl_ty<'a>(local_idx: usize, locals: &'a [trust_types::LocalDecl]) -> Option<&'a Ty> {
    locals
        .get(local_idx)
        .filter(|local| local.index == local_idx)
        .or_else(|| locals.iter().find(|local| local.index == local_idx))
        .map(|local| &local.ty)
}

/// Whether a place contains a dereference projection the trust-vc MIR-memory
/// proof unit cannot model. A SINGLE leading `Deref` of a SAFE REFERENCE base
/// local (`&T`/`&mut T`) IS supported: the access is borrow-checker-valid, so the
/// bounds predicate (`idx < len`) is the sole safety obligation and trust-vc
/// discharges it soundly (e.g. `data[0]` on `data: &[u32; 1]`). Raw-pointer
/// derefs and nested/non-leading derefs stay unsupported — their validity and
/// provenance are not modeled here, so the bounds predicate alone is not enough.
fn place_has_unsupported_deref(place: &Place, locals: &[trust_types::LocalDecl]) -> bool {
    let deref_count = place
        .projections
        .iter()
        .filter(|projection| matches!(projection, Projection::Deref))
        .take(2)
        .count();
    if deref_count == 0 {
        return false;
    }
    let safe_reference_deref = deref_count == 1
        && matches!(place.projections.first(), Some(Projection::Deref))
        && matches!(local_decl_ty(place.local, locals), Some(Ty::Ref { .. }));
    !safe_reference_deref
}

fn operand_has_unsupported_deref(operand: &Operand, locals: &[trust_types::LocalDecl]) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place_has_unsupported_deref(place, locals),
        Operand::Constant(_) | Operand::Symbolic(_) | Operand::Unsupported { .. } => false,
        _ => false,
    }
}

fn rvalue_has_unsupported_deref(rvalue: &Rvalue, locals: &[trust_types::LocalDecl]) -> bool {
    match rvalue {
        Rvalue::Use(operand) | Rvalue::UnaryOp(_, operand) | Rvalue::Cast(operand, _) => {
            operand_has_unsupported_deref(operand, locals)
        }
        Rvalue::BinaryOp(_, left, right) | Rvalue::CheckedBinaryOp(_, left, right) => {
            operand_has_unsupported_deref(left, locals)
                || operand_has_unsupported_deref(right, locals)
        }
        Rvalue::Ref { place, .. }
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::CopyForDeref(place) => place_has_unsupported_deref(place, locals),
        Rvalue::Aggregate(_, operands) | Rvalue::Unsupported { operands, .. } => {
            operands.iter().any(|operand| operand_has_unsupported_deref(operand, locals))
        }
        Rvalue::Repeat(operand, _) => operand_has_unsupported_deref(operand, locals),
        Rvalue::AddressOf(_, place) => place_has_unsupported_deref(place, locals),
        _ => false,
    }
}

pub(crate) fn local_name(local: &trust_types::LocalDecl) -> String {
    local
        .name
        .as_deref()
        .filter(|name| !name.trim().is_empty())
        .map(str::to_string)
        .unwrap_or_else(|| format!("_{}", local.index))
}

pub(crate) fn trust_vc_sort_for_ty(ty: &Ty) -> Result<JsonValue, String> {
    match ty {
        Ty::Bool => Ok(json!({ "kind": "bool" })),
        Ty::Int { width, signed } => trust_vc_bit_vector_sort(*width, *signed),
        Ty::Float { width } if matches!(*width, 32 | 64) => {
            Ok(json!({ "kind": "float", "width": width }))
        }
        Ty::Float { width } => Err(format!(
            "trust-vc MIR memory proof unit omitted because float width {width} is unsupported"
        )),
        Ty::Ref { inner, .. } => trust_vc_sort_for_ty(inner),
        Ty::Array { elem, .. } => Ok(json!({
            "kind": "seq",
            "elem": trust_vc_sort_for_ty(elem)?,
        })),
        Ty::Bv(width) => trust_vc_bit_vector_sort(*width, false),
        Ty::Unit => Ok(json!({ "kind": "opaque", "name": "unit" })),
        Ty::Never => Ok(json!({ "kind": "opaque", "name": "never" })),
        other => Err(format!(
            "trust-vc MIR memory proof unit omitted because type `{other:?}` has no direct trust_vc sort"
        )),
    }
}

fn trust_vc_sort_for_formula_sort(sort: &Sort) -> Result<JsonValue, String> {
    match sort {
        Sort::Bool => Ok(json!({ "kind": "bool" })),
        Sort::Int => Ok(trust_vc_math_int_sort()),
        Sort::BitVec(width) => trust_vc_bit_vector_sort(*width, false),
        Sort::Array(_, _) => Err(
            "trust-vc MIR memory proof unit omitted because array formulas are outside the direct typed TrustExpr subset"
                .to_string(),
        ),
        _ => Err(
            "trust-vc MIR memory proof unit omitted because the formula sort is outside the direct typed TrustExpr subset"
                .to_string(),
        ),
    }
}

fn trust_vc_bit_vector_sort(width: u32, signed: bool) -> Result<JsonValue, String> {
    if !matches!(width, 8 | 16 | 32 | 64 | 128) {
        return Err(format!(
            "trust-vc MIR memory proof unit omitted because bit-vector width {width} is unsupported"
        ));
    }
    Ok(json!({
        "kind": "bit_vector",
        "width": width,
        "signed": signed,
    }))
}

fn trust_vc_math_int_sort() -> JsonValue {
    json!({ "kind": "math_int" })
}

fn trust_vc_source_location(span: &SourceSpan) -> Option<String> {
    (!span.file.is_empty()).then(|| {
        format!(
            "{}:{}:{}-{}:{}",
            span.file, span.line_start, span.col_start, span.line_end, span.col_end
        )
    })
}

fn trust_vc_unsupported_memory_marker(text: &str) -> bool {
    if text.len() < 4 {
        return false;
    }
    const MARKERS: [&str; 7] =
        ["heap", "rawptr", "rawpointer", "pointer", "provenance", "alloc", "deref"];
    if text.bytes().all(|b| b.is_ascii_lowercase() || b.is_ascii_digit()) {
        return MARKERS.iter().any(|marker| text.contains(marker));
    }
    let mut normalized = String::with_capacity(text.len());
    for byte in text.bytes() {
        if byte.is_ascii_alphanumeric() {
            normalized.push(byte.to_ascii_lowercase() as char);
        }
    }
    if normalized.len() < 4 {
        return false;
    }
    MARKERS.iter().any(|marker| normalized.contains(marker))
}

fn formula_node_name(formula: &Formula) -> &'static str {
    match formula {
        Formula::Bool(_) => "Bool",
        Formula::Int(_) => "Int",
        Formula::UInt(_) => "UInt",
        Formula::BitVec { .. } => "BitVec",
        Formula::Var(..) => "Var",
        Formula::SymVar(..) => "SymVar",
        Formula::Not(_) => "Not",
        Formula::And(_) => "And",
        Formula::Or(_) => "Or",
        Formula::Implies(..) => "Implies",
        Formula::Eq(..) => "Eq",
        Formula::Lt(..) => "Lt",
        Formula::Le(..) => "Le",
        Formula::Gt(..) => "Gt",
        Formula::Ge(..) => "Ge",
        Formula::Add(..) => "Add",
        Formula::Sub(..) => "Sub",
        Formula::Mul(..) => "Mul",
        Formula::Div(..) => "Div",
        Formula::Rem(..) => "Rem",
        Formula::Neg(_) => "Neg",
        Formula::BvAdd(..) => "BvAdd",
        Formula::BvSub(..) => "BvSub",
        Formula::BvMul(..) => "BvMul",
        Formula::BvUDiv(..) => "BvUDiv",
        Formula::BvSDiv(..) => "BvSDiv",
        Formula::BvURem(..) => "BvURem",
        Formula::BvSRem(..) => "BvSRem",
        Formula::BvAnd(..) => "BvAnd",
        Formula::BvOr(..) => "BvOr",
        Formula::BvXor(..) => "BvXor",
        Formula::BvNot(..) => "BvNot",
        Formula::BvShl(..) => "BvShl",
        Formula::BvLShr(..) => "BvLShr",
        Formula::BvAShr(..) => "BvAShr",
        Formula::BvULt(..) => "BvULt",
        Formula::BvULe(..) => "BvULe",
        Formula::BvSLt(..) => "BvSLt",
        Formula::BvSLe(..) => "BvSLe",
        Formula::BvToInt(..) => "BvToInt",
        Formula::IntToBv(..) => "IntToBv",
        Formula::BvExtract { .. } => "BvExtract",
        Formula::BvConcat(..) => "BvConcat",
        Formula::BvZeroExt(..) => "BvZeroExt",
        Formula::BvSignExt(..) => "BvSignExt",
        Formula::Ite(..) => "Ite",
        Formula::Forall(..) => "Forall",
        Formula::Exists(..) => "Exists",
        Formula::Select(..) => "Select",
        Formula::Store(..) => "Store",
        Formula::ConstArray { .. } => "ConstArray",
        _ => "Unknown",
    }
}

fn contract_kind(kind: TrustTypesContractKind) -> Option<(ContractKind, ObligationKind)> {
    match kind {
        TrustTypesContractKind::Requires => {
            Some((ContractKind::Requires, ObligationKind::Precondition))
        }
        TrustTypesContractKind::Ensures => {
            Some((ContractKind::Ensures, ObligationKind::Postcondition))
        }
        TrustTypesContractKind::Invariant => {
            Some((ContractKind::Invariant, ObligationKind::Invariant))
        }
        TrustTypesContractKind::LoopInvariant => {
            Some((ContractKind::LoopInvariant, ObligationKind::LoopInvariant))
        }
        TrustTypesContractKind::TypeRefinement => {
            Some((ContractKind::Refinement, ObligationKind::Refinement))
        }
        TrustTypesContractKind::Decreases => {
            Some((ContractKind::Asserts, ObligationKind::Termination))
        }
        TrustTypesContractKind::Modifies => None,
        _ => None,
    }
}

fn unsupported_contract_obligation(
    function: &VerifiableFunction,
    function_context: &FunctionContext,
    index: usize,
    contract: &Contract,
    source: SourceLocation,
    contract_id: Option<String>,
    predicate_digest: Option<String>,
    typed_proposition_digest: Option<String>,
    reason: String,
) -> TrustObligation {
    let mut metadata = vec![
        MetadataEntry {
            key: "trust.contract.kind".to_string(),
            value: contract.kind.attr_name().to_string(),
        },
        obligation_context_metadata(
            function_context,
            ObligationOrigin::UnsupportedContract {
                contract_index: index,
                compiler_contract_kind: contract.kind.attr_name().to_string(),
                reason: reason.clone(),
            },
        ),
    ];
    if let Some(predicate_digest) = predicate_digest {
        metadata.push(MetadataEntry {
            key: TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY.to_string(),
            value: predicate_digest,
        });
    }
    if let Some(typed_proposition_digest) = typed_proposition_digest {
        metadata.push(MetadataEntry {
            key: TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY.to_string(),
            value: typed_proposition_digest,
        });
    }
    TrustObligation {
        obligation_id: format!(
            "unsupported:{}:{}",
            trust_types::canonical_artifact_id_component(&function.def_path),
            index
        ),
        kind: ObligationKind::Custom {
            namespace: "trust.contract".to_string(),
            name: "unsupported".to_string(),
        },
        contract_id,
        proof_item_id: None,
        source,
        description: reason.clone(),
        required_strength: Some(ProofStrength::deductive()),
        summary_facts: Vec::new(),
        metadata,
    }
}

fn proof_item_obligation(
    function: &VerifiableFunction,
    function_context: &FunctionContext,
    index: usize,
    proof_item: &TrustProofItem,
) -> TrustObligation {
    let proof_item_id = format!(
        "proof-item:{}:{}:{}",
        trust_types::canonical_artifact_id_component(&function.def_path),
        index,
        trust_types::canonical_artifact_id_component(&proof_item.name)
    );
    let mut metadata = vec![
        MetadataEntry { key: "trust.proof_item.name".to_string(), value: proof_item.name.clone() },
        MetadataEntry {
            key: "trust.proof_item.source".to_string(),
            value: proof_item_source_label(proof_item.source).to_string(),
        },
        MetadataEntry {
            key: "trust.proof_item.kind".to_string(),
            value: proof_item_kind_label(proof_item.kind).to_string(),
        },
        MetadataEntry {
            key: "trust.proof_item.engine".to_string(),
            value: proof_engine_label(proof_item.engine).to_string(),
        },
        MetadataEntry {
            key: "trust.proof_item.mode".to_string(),
            value: proof_execution_mode_label(&proof_item.mode).to_string(),
        },
        MetadataEntry {
            key: "trust.proof_item.must_execute_full_verify".to_string(),
            value: proof_item.must_execute_in_full_verify().to_string(),
        },
    ];
    if let Some(depth) = proof_execution_bounded_depth(&proof_item.mode) {
        metadata.push(MetadataEntry {
            key: "trust.proof_item.bounded_depth".to_string(),
            value: depth.to_string(),
        });
    }
    if matches!(proof_item.mode, TrustProofExecutionMode::BoundedRegression { depth: None }) {
        metadata.push(MetadataEntry {
            key: "trust.proof_item.bounded_depth".to_string(),
            value: "unspecified".to_string(),
        });
    }
    if let Some(target) = &proof_item.target {
        metadata.push(MetadataEntry {
            key: "trust.proof_item.target".to_string(),
            value: target.clone(),
        });
    }
    if let Some(body_hash) = &proof_item.body_hash {
        metadata.push(MetadataEntry {
            key: "trust.proof_item.body_hash".to_string(),
            value: body_hash.clone(),
        });
    }
    if let Some(blocker) = proof_item.proof_grade_blocker() {
        metadata.push(MetadataEntry {
            key: "trust.proof_item.proof_grade_blocker".to_string(),
            value: blocker.to_string(),
        });
    }
    for diagnostic in &proof_item.diagnostics {
        metadata.push(MetadataEntry {
            key: "trust.proof_item.diagnostic".to_string(),
            value: diagnostic.clone(),
        });
    }
    metadata.push(obligation_context_metadata(
        function_context,
        ObligationOrigin::ProofItem {
            proof_item_id: proof_item_id.clone(),
            proof_item_kind: proof_item_kind_label(proof_item.kind).to_string(),
            engine: proof_engine_label(proof_item.engine).to_string(),
        },
    ));

    TrustObligation {
        obligation_id: proof_item_id.clone(),
        kind: proof_item_obligation_kind(proof_item),
        contract_id: None,
        proof_item_id: Some(proof_item_id),
        source: source_location(&proof_item.span),
        description: proof_item_obligation_description(proof_item),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata,
    }
}

fn proof_item_obligation_kind(proof_item: &TrustProofItem) -> ObligationKind {
    match (proof_item.engine, proof_item.kind) {
        (TrustProofEngineHint::TrustMc, TrustProofItemKind::Harness)
        | (TrustProofEngineHint::TrustMc, TrustProofItemKind::ContractHarness) => {
            ObligationKind::Assertion
        }
        _ => ObligationKind::Custom {
            namespace: "trust.proof_item".to_string(),
            name: proof_item_kind_label(proof_item.kind).to_string(),
        },
    }
}

fn proof_item_obligation_description(proof_item: &TrustProofItem) -> String {
    let source = proof_item_source_label(proof_item.source);
    let kind = proof_item_kind_label(proof_item.kind);
    let engine = proof_engine_label(proof_item.engine);
    let mut description = format!(
        "execute {source} {kind} `{}` through {engine} for full verification",
        proof_item.name
    );
    if let Some(target) = &proof_item.target {
        description.push_str(&format!(" targeting `{target}`"));
    }
    if let Some(blocker) = proof_item.proof_grade_blocker() {
        description.push_str(&format!("; {blocker}"));
    }
    description
}

fn proof_item_source_label(source: TrustProofItemSource) -> &'static str {
    match source {
        TrustProofItemSource::NativeProofFn => "native_proof_fn",
        TrustProofItemSource::NativeProofBlock => "native_proof_block",
        TrustProofItemSource::NativeHarness => "native_harness",
        TrustProofItemSource::TrustVcProofAttribute => "trust_vc_proof_attribute",
        TrustProofItemSource::TrustVcProofMacro => "trust_vc_proof_macro",
        TrustProofItemSource::TrustWpLawAttribute => "trust_wp_law_attribute",
        TrustProofItemSource::TrustWpLogicAttribute => "trust_wp_logic_attribute",
        TrustProofItemSource::LeanExternalProof => "lean_external_proof",
        _ => "unknown",
    }
}

fn proof_item_kind_label(kind: TrustProofItemKind) -> &'static str {
    match kind {
        TrustProofItemKind::Harness => "harness",
        TrustProofItemKind::ContractHarness => "contract_harness",
        TrustProofItemKind::Lemma => "lemma",
        TrustProofItemKind::SpecificationFunction => "specification_function",
        TrustProofItemKind::ProofBlock => "proof_block",
        TrustProofItemKind::LogicLaw => "logic_law",
        TrustProofItemKind::ExternalTheorem => "external_theorem",
        _ => "unknown",
    }
}

fn proof_engine_label(engine: TrustProofEngineHint) -> &'static str {
    match engine {
        TrustProofEngineHint::Auto => "auto",
        TrustProofEngineHint::TrustMc => "trust-mc",
        TrustProofEngineHint::TrustWp => "trust-wp",
        TrustProofEngineHint::TrustVc => "trust-vc",
        TrustProofEngineHint::Clean => "clean",
        TrustProofEngineHint::AY => "ay",
        TrustProofEngineHint::Ty => "ty",
        _ => "unknown",
    }
}

fn proof_execution_mode_label(mode: &TrustProofExecutionMode) -> &'static str {
    match mode {
        TrustProofExecutionMode::RequiredFullVerify => "required_full_verify",
        TrustProofExecutionMode::BoundedRegression { .. } => "bounded_regression",
        TrustProofExecutionMode::DiagnosticOnly => "diagnostic_only",
        _ => "unknown",
    }
}

fn proof_execution_bounded_depth(mode: &TrustProofExecutionMode) -> Option<u64> {
    match mode {
        TrustProofExecutionMode::BoundedRegression { depth } => *depth,
        _ => None,
    }
}

fn vc_obligation_kind(kind: &VcKind) -> ObligationKind {
    if let Some(category) = kind.hardened_category() {
        return ObligationKind::Custom {
            namespace: TRUST_VC_HARDENED_NAMESPACE.to_string(),
            name: category.as_tag().to_string(),
        };
    }

    match kind {
        VcKind::ArithmeticOverflow { .. }
        | VcKind::ShiftOverflow { .. }
        | VcKind::DivisionByZero
        | VcKind::RemainderByZero
        | VcKind::CastOverflow { .. }
        | VcKind::NegationOverflow { .. }
        | VcKind::FloatDivisionByZero
        | VcKind::FloatOverflowToInfinity { .. }
        | VcKind::AggregateArrayLengthMismatch { .. }
        | VcKind::InvalidDiscriminant { .. } => ObligationKind::ArithmeticSafety,
        // Trust (P0 false-proof fix): an `UnboundedAllocation` (#nia-oom) capacity
        // obligation is NOT an arithmetic-overflow / panic-freedom property — its
        // failure condition is `count >= ceiling` (the availability/capacity budget),
        // which the native trust-mc typed-CHC/PDR encoding does NOT model. The prior
        // code mapped it to `ArithmeticSafety`, which the native route claims via a
        // whole-function "safe" CHC proof (arithmetic overflow / panic reachability
        // only) — so a genuinely-unbounded `vec![0u8; n]` sitting alongside ANY other
        // routable ArithmeticSafety obligation (e.g. `a as u32 + 1` in the same
        // tuple) inherited the whole-function `Proved` transport and FALSE-PROVED
        // (the fuzzer's `sr_vec_from_elem_*` families). By keeping it OUT of the
        // trust-mc/CHC routable set, the alloc obligation never enters the CHC
        // bundle, so no whole-function proof can claim it. Its ONLY native route
        // is the trust-vc MIR-memory proof-unit lane (the BoundsCheck precedent,
        // `trust_vc_formula_obligation`): the unit's predicate is the negated
        // `count >= ceiling` VC itself, discharged with a replayable certificate
        // at import time, so the proof that reaches the native lane ENCODES the
        // capacity budget — the property whose absence was the P0. The per-VC
        // ay/interval bridge (`bridge_v1_ay_proofs_into_native_results`) still
        // discharges the REAL `count >= ceiling` formula on the front line —
        // proving a dominating-guard-bounded count and refuting an unguarded one
        // with a concrete `count = ceiling` witness, exactly as the alloc-only
        // (no-sibling) case already does. The failure-escalation path keys on
        // the `VcKind` (`is_refutable_l0_safety_vc_kind`), not this
        // ObligationKind, so a refuted allocation still hard-errors under strict.
        VcKind::UnboundedAllocation { .. } => ObligationKind::Custom {
            namespace: TRUST_VC_UNBOUNDED_ALLOCATION_NAMESPACE.to_string(),
            name: "unbounded_allocation".to_string(),
        },
        VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => ObligationKind::BoundsCheck,
        VcKind::UnsafeOperation { .. }
        | VcKind::SavedReturnAddressOverwrite { .. }
        | VcKind::FormatStringViolation { .. }
        | VcKind::TaintedIndirectBranch { .. }
        | VcKind::FfiBoundaryViolation { .. }
        | VcKind::UseAfterFree
        | VcKind::DoubleFree
        | VcKind::LifetimeViolation => ObligationKind::MemorySafety,
        VcKind::AliasingViolation { .. } | VcKind::SendViolation | VcKind::SyncViolation => {
            ObligationKind::Ownership
        }
        VcKind::Assertion { .. } | VcKind::Unreachable => ObligationKind::Assertion,
        VcKind::Precondition { .. } => ObligationKind::Precondition,
        VcKind::Postcondition => ObligationKind::Postcondition,
        VcKind::DeadState { .. }
        | VcKind::Deadlock
        | VcKind::Temporal { .. }
        | VcKind::Fairness { .. } => ObligationKind::TemporalSafety,
        VcKind::Liveness { .. } => ObligationKind::Liveness,
        VcKind::ProtocolViolation { .. } => ObligationKind::Protocol,
        VcKind::RefinementViolation { .. }
        | VcKind::FunctionalCorrectness { .. }
        | VcKind::TypeRefinementViolation { .. }
        | VcKind::FrameConditionViolation { .. } => ObligationKind::Refinement,
        VcKind::NonTermination { .. } => ObligationKind::Termination,
        VcKind::LoopInvariantInitiation { .. }
        | VcKind::LoopInvariantConsecution { .. }
        | VcKind::LoopInvariantSufficiency { .. } => ObligationKind::LoopInvariant,
        VcKind::TaintViolation { .. }
        | VcKind::ResilienceViolation { .. }
        | VcKind::DataRace { .. }
        | VcKind::InsufficientOrdering { .. }
        | VcKind::TranslationValidation { .. }
        | VcKind::BinaryAbiContradiction { .. }
        | VcKind::UnsupportedMir { .. }
        | VcKind::DeclinedContractBody(_)
        // TINV: NEVER `ObligationKind::Invariant`, which routes to trust-mc whole-function
        // reachability and to trust_ir TranslationValidation; neither encodes I(σ), so a
        // sibling-claimed whole-function `safe` could false-prove the row (the
        // UnboundedAllocation P0 shape above). A `trust.vc` Custom kind has no route.
        | VcKind::TypeInvariant { .. } => {
            ObligationKind::Custom { namespace: "trust.vc".to_string(), name: vc_kind_label(kind) }
        }
        _ => ObligationKind::Custom {
            namespace: "trust.vc".to_string(),
            name: "unknown".to_string(),
        },
    }
}

fn vc_kind_label(kind: &VcKind) -> String {
    if let Some(tag) = kind.hardened_family_tag() {
        return tag;
    }

    match kind {
        VcKind::ArithmeticOverflow { .. } => "arithmetic_overflow",
        VcKind::ShiftOverflow { .. } => "shift_overflow",
        VcKind::DivisionByZero => "division_by_zero",
        VcKind::RemainderByZero => "remainder_by_zero",
        VcKind::IndexOutOfBounds => "index_out_of_bounds",
        VcKind::SliceBoundsCheck => "slice_bounds_check",
        VcKind::Assertion { .. } => "assertion",
        VcKind::Precondition { .. } => "precondition",
        VcKind::Postcondition => "postcondition",
        VcKind::CastOverflow { .. } => "cast_overflow",
        VcKind::NegationOverflow { .. } => "negation_overflow",
        VcKind::Unreachable => "unreachable",
        VcKind::UnsupportedMir { .. } => "unsupported_mir",
        VcKind::DeclinedContractBody(_) => "declined_contract_body",
        VcKind::DeadState { .. } => "dead_state",
        VcKind::Deadlock => "deadlock",
        VcKind::Temporal { .. } => "temporal",
        VcKind::Liveness { .. } => "liveness",
        VcKind::Fairness { .. } => "fairness",
        VcKind::TaintViolation { .. } => "taint_violation",
        VcKind::RefinementViolation { .. } => "refinement_violation",
        VcKind::ResilienceViolation { .. } => "resilience_violation",
        VcKind::ProtocolViolation { .. } => "protocol_violation",
        VcKind::NonTermination { .. } => "non_termination",
        VcKind::DataRace { .. } => "data_race",
        VcKind::InsufficientOrdering { .. } => "insufficient_ordering",
        VcKind::TranslationValidation { .. } => "translation_validation",
        VcKind::FloatDivisionByZero => "float_division_by_zero",
        VcKind::FloatOverflowToInfinity { .. } => "float_overflow_to_infinity",
        VcKind::InvalidDiscriminant { .. } => "invalid_discriminant",
        VcKind::AggregateArrayLengthMismatch { .. } => "aggregate_array_length_mismatch",
        VcKind::UnsafeOperation { .. } => "unsafe_operation",
        VcKind::SavedReturnAddressOverwrite { .. } => "saved_return_address_overwrite",
        VcKind::FormatStringViolation { .. } => "format_string_violation",
        VcKind::TaintedIndirectBranch { .. } => "tainted_indirect_branch",
        VcKind::BinaryAbiContradiction { .. } => "binary_abi_contradiction",
        VcKind::FfiBoundaryViolation { .. } => "ffi_boundary_violation",
        VcKind::UseAfterFree => "use_after_free",
        VcKind::DoubleFree => "double_free",
        VcKind::AliasingViolation { .. } => "aliasing_violation",
        VcKind::LifetimeViolation => "lifetime_violation",
        VcKind::SendViolation => "send_violation",
        VcKind::SyncViolation => "sync_violation",
        VcKind::FunctionalCorrectness { .. } => "functional_correctness",
        VcKind::LoopInvariantInitiation { .. } => "loop_invariant_initiation",
        VcKind::LoopInvariantConsecution { .. } => "loop_invariant_consecution",
        VcKind::LoopInvariantSufficiency { .. } => "loop_invariant_sufficiency",
        VcKind::TypeRefinementViolation { .. } => "type_refinement_violation",
        VcKind::FrameConditionViolation { .. } => "frame_condition_violation",
        VcKind::TypeInvariant { .. } => "type_invariant",
        _ => "unknown",
    }
    .to_string()
}

fn contract_id(function: &VerifiableFunction, index: usize, contract: &Contract) -> String {
    contract.stable_source_id(&function.def_path, index)
}

fn obligation_id(function: &VerifiableFunction, index: usize, kind: &ObligationKind) -> String {
    format!(
        "obligation:{}:{}:{}",
        trust_types::canonical_artifact_id_component(&function.def_path),
        obligation_kind_label(&kind),
        index
    )
}

fn obligation_context_metadata(
    function: &FunctionContext,
    origin: ObligationOrigin,
) -> MetadataEntry {
    ObligationContext::new(ObligationProducer::CompilerMirExtract, origin)
        .with_function(function.clone())
        .to_metadata_entry()
        .expect("obligation context metadata serializes")
}

fn function_context_with_crate_name(
    function: &VerifiableFunction,
    crate_name: &str,
) -> FunctionContext {
    FunctionContext { crate_name: crate_name.to_string(), path: function.def_path.clone() }
}

fn obligation_kind_label(kind: &ObligationKind) -> &str {
    match kind {
        ObligationKind::Precondition => "precondition",
        ObligationKind::Postcondition => "postcondition",
        ObligationKind::Assertion => "assertion",
        ObligationKind::Invariant => "invariant",
        ObligationKind::LoopInvariant => "loop_invariant",
        ObligationKind::ArithmeticSafety => "arithmetic_safety",
        ObligationKind::MemorySafety => "memory_safety",
        ObligationKind::Ownership => "ownership",
        // Without this arm BoundsCheck fell to "unknown", and the proof-unit
        // payload's obligation id (`vc:<fn>:unknown:<idx>`) failed the
        // trust-vc bridge's artifact<->obligation matching — blocking native
        // discharge even though the whole pipeline was wired.
        ObligationKind::BoundsCheck => "bounds_check",
        ObligationKind::Refinement => "refinement",
        ObligationKind::Termination => "termination",
        ObligationKind::TemporalSafety => "temporal_safety",
        ObligationKind::Liveness => "liveness",
        ObligationKind::Protocol => "protocol",
        ObligationKind::Custom { namespace, name } if namespace == TRUST_VC_HARDENED_NAMESPACE => {
            name.as_str()
        }
        ObligationKind::Custom { .. } => "custom",
        _ => "unknown",
    }
}

fn source_location(span: &SourceSpan) -> SourceLocation {
    SourceLocation {
        file: (!span.file.is_empty()).then(|| span.file.clone()),
        line: (span.line_start != 0).then_some(span.line_start),
        column: (span.col_start != 0).then_some(span.col_start),
        end_line: (span.line_end != 0).then_some(span.line_end),
        end_column: (span.col_end != 0).then_some(span.col_end),
    }
}

fn compiler_identity_bundle_id(function: &VerifiableFunction, stable_crate_id: u64) -> String {
    format!(
        "trust-contracts:{}:rustc-crate:{stable_crate_id:016x}",
        trust_types::canonical_artifact_id_component(&function.def_path),
    )
}

fn bind_compiler_crate_identity(
    bundle: &mut TrustContractBundle,
    function: &VerifiableFunction,
    stable_crate_id: u64,
) {
    bundle.bundle_id = compiler_identity_bundle_id(function, stable_crate_id);
    bundle.metadata.push(MetadataEntry {
        key: TRUST_COMPILER_STABLE_CRATE_ID_METADATA_KEY.to_string(),
        value: format!("{stable_crate_id:016x}"),
    });
}

fn crate_name_from_def_path(def_path: &str) -> String {
    let Some(first) = def_path.split("::").next() else {
        return UNRESOLVED_COMPATIBILITY_CRATE_NAME.to_string();
    };
    if first.is_empty() || first.starts_with('<') {
        UNRESOLVED_COMPATIBILITY_CRATE_NAME.to_string()
    } else {
        first.to_string()
    }
}

#[cfg(test)]
#[allow(deprecated)]
mod tests {
    use trust_types::{BasicBlock, BlockId, LocalDecl, Terminator, Ty, UnwindEdge, VerifiableBody};
    use trust_verifier_api::{
        OBLIGATION_CONTEXT_METADATA_KEY, ObligationContext, TRUST_SPEC_PREDICATE_SCHEMA_VERSION,
        TrustSpecExprKind,
    };

    use super::*;

    fn test_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "f".to_string(),
            def_path: "demo::f".to_string(),
            span: SourceSpan {
                file: "src/lib.rs".to_string(),
                line_start: 10,
                col_start: 4,
                line_end: 12,
                col_end: 1,
            },
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: Vec::new(),
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Unit,
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    fn feedback_loop_function() -> VerifiableFunction {
        let clause_span = SourceSpan {
            file: "feedback.rs".to_string(),
            line_start: 8,
            col_start: 4,
            line_end: 8,
            col_end: 40,
        };
        VerifiableFunction {
            name: "feedback_loop".to_string(),
            def_path: "test::feedback_loop".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("i".into()) },
                    LocalDecl { index: 3, ty: Ty::Bool, name: Some("cond".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(1),
                                rvalue: Rvalue::Use(Operand::Constant(
                                    trust_types::ConstValue::Int(10),
                                )),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(2),
                                rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                trust_types::BinOp::Gt,
                                Operand::Copy(Place::local(2)),
                                // Trust: WIDTH-TAGGED, because this is a BINARY-OP
                                // OPERAND. The audit requires a `BinaryOp`'s operand
                                // and destination types to match the audited Rust
                                // operation; an untyped `Int(0)` against a `u32`
                                // local does not, so `generate_vcs` emitted
                                // `UnsupportedMir { kind: "MalformedTrustIr" }`
                                // instead of the E4 rows these tests look for.
                                //
                                // `Int(0)` stays correct in `Rvalue::Use`
                                // assignments — being an OPERAND is the distinction.
                                Operand::Constant(trust_types::ConstValue::Uint(0, 32)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(3)),
                            targets: vec![(1, BlockId(2))],
                            otherwise: BlockId(3),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: Ty::Unit,
                datatype_defs: Default::default(),
            },
            contracts: vec![
                Contract {
                    kind: TrustTypesContractKind::LoopInvariant,
                    span: clause_span.clone(),
                    body: "bb1: n <= 10 && i <= 10".to_string(),
                },
                Contract {
                    kind: TrustTypesContractKind::Decreases,
                    span: clause_span,
                    body: "bb1: i".to_string(),
                },
            ],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    fn feedback_loop_contracts(function: &VerifiableFunction) -> CompilerContractBundle {
        let invariant = &function.contracts[0];
        let decreases = &function.contracts[1];
        CompilerContractBundle::default().with_loop_contracts(vec![
            trust_types::LoopContractSpec {
                kind: trust_types::LoopContractKind::Invariant,
                source_loop_id: 0,
                source_hir_local_id: Some(1),
                mir_header: Some(1),
                loop_head: SourceSpan::default(),
                header_span: SourceSpan::default(),
                span: invariant.span.clone(),
                body: "n <= 10 && i <= 10".to_string(),
            },
            trust_types::LoopContractSpec {
                kind: trust_types::LoopContractKind::Decreases,
                source_loop_id: 0,
                source_hir_local_id: Some(1),
                mir_header: Some(1),
                loop_head: SourceSpan::default(),
                header_span: SourceSpan::default(),
                span: decreases.span.clone(),
                body: "i".to_string(),
            },
        ])
    }

    fn recursion_span(line: u32) -> SourceSpan {
        SourceSpan {
            file: "recursion.rs".to_string(),
            line_start: line,
            col_start: 5,
            line_end: line,
            col_end: 20,
        }
    }

    fn two_call_recursion_function() -> VerifiableFunction {
        let contract_span = recursion_span(2);
        let recursive_call = |id, line, target| BasicBlock {
            id: BlockId(id),
            stmts: Vec::new(),
            terminator: Terminator::Call {
                func: "test::two_call_recursion".to_string(),
                args: vec![Operand::Copy(Place::local(1))],
                dest: Place::local(0),
                target: Some(BlockId(target)),
                unwind: UnwindEdge::Unreachable,
                span: recursion_span(line),
                is_unsafe_sig: false,
                callee_identity: None,
                callee_key: None,
                is_foreign: false,
                atomic: None,
            },
        };
        VerifiableFunction {
            name: "two_call_recursion".to_string(),
            def_path: "test::two_call_recursion".to_string(),
            span: contract_span.clone(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("bbq".to_string()) },
                ],
                blocks: vec![
                    recursive_call(0, 10, 1),
                    recursive_call(1, 20, 2),
                    BasicBlock {
                        id: BlockId(2),
                        stmts: Vec::new(),
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::Unit,
                datatype_defs: Default::default(),
            },
            contracts: vec![Contract {
                kind: TrustTypesContractKind::Decreases,
                span: contract_span,
                // A normal function measure may begin with `bb`; only the
                // exact `bb<usize>:` grammar denotes a loop-local clause.
                body: "bbq".to_string(),
            }],
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    fn source_contract_marker_indices(bundle: &TrustContractBundle) -> Vec<usize> {
        bundle
            .obligations
            .iter()
            .filter_map(|obligation| match obligation_context(obligation).origin {
                ObligationOrigin::Contract { contract_index, .. }
                | ObligationOrigin::UnsupportedContract { contract_index, .. } => {
                    Some(contract_index)
                }
                _ => None,
            })
            .collect()
    }

    fn loop_contract_marker_indices(bundle: &TrustContractBundle) -> Vec<usize> {
        bundle
            .obligations
            .iter()
            .filter_map(|obligation| {
                let ObligationOrigin::UnsupportedContract { contract_index, .. } =
                    obligation_context(obligation).origin
                else {
                    return None;
                };
                Some(contract_index)
            })
            .collect()
    }

    fn loop_role(vc: &VerificationCondition) -> Option<&'static str> {
        match &vc.kind {
            VcKind::LoopInvariantInitiation { .. } => Some("initiation"),
            VcKind::LoopInvariantConsecution { .. } => Some("consecution"),
            VcKind::NonTermination { context, .. } if context == "loop-decreases" => {
                Some("decreases")
            }
            _ => None,
        }
    }

    fn trust_vc_memory_test_function(arg_ty: Ty) -> VerifiableFunction {
        let mut function = test_function();
        function.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".to_string()) },
            LocalDecl { index: 1, ty: arg_ty, name: Some("x".to_string()) },
        ];
        function.body.arg_count = 1;
        function
    }

    fn assert_trust_ir_bool_literal(predicate: &ContractPredicate, expected: bool) {
        let predicate = typed_spec_predicate(predicate);
        assert_eq!(predicate.root_sort, TrustSpecSort::Bool);
        assert!(predicate.variables.is_empty());
        assert!(matches!(
            predicate.root.kind,
            TrustSpecExprKind::BoolLiteral { value } if value == expected
        ));
    }

    fn assert_trust_ir_simple_expr(predicate: &ContractPredicate) {
        let predicate = typed_spec_predicate(predicate);
        assert_eq!(predicate.root_sort, TrustSpecSort::Bool);
        match predicate.root.kind {
            TrustSpecExprKind::Binary { op: TrustSpecBinaryOp::Gt, lhs, rhs } => {
                assert_eq!(lhs.sort, TrustSpecSort::Int);
                assert_eq!(rhs.sort, TrustSpecSort::Int);
                assert!(
                    matches!(lhs.kind, TrustSpecExprKind::Variable { ref name } if name == "x")
                );
                assert!(
                    matches!(rhs.kind, TrustSpecExprKind::IntLiteral { ref value } if value == "0")
                );
            }
            other => panic!("unexpected lowered expression root: {other:?}"),
        }
    }

    fn typed_spec_predicate(predicate: &ContractPredicate) -> TrustSpecPredicate {
        match predicate {
            ContractPredicate::TrustIr { schema, value } => {
                assert_eq!(schema, TRUST_SPEC_PREDICATE_SCHEMA_VERSION);
                assert_eq!(value["schema_version"], TRUST_SPEC_PREDICATE_SCHEMA_VERSION);
                assert!(value.get("source_text").is_none());
                TrustSpecPredicate::from_contract_predicate(predicate)
                    .expect("typed predicate should decode")
                    .expect("typed predicate schema")
            }
            other => panic!("unexpected contract predicate: {other:?}"),
        }
    }

    fn obligation_context(obligation: &TrustObligation) -> ObligationContext {
        let entry = obligation
            .metadata
            .iter()
            .find(|entry| entry.key == OBLIGATION_CONTEXT_METADATA_KEY)
            .expect("obligation context metadata");
        ObligationContext::from_metadata_entry(entry)
            .expect("context metadata should decode")
            .expect("context metadata key")
    }

    fn metadata_value<'a>(metadata: &'a [MetadataEntry], key: &str) -> Option<&'a str> {
        metadata.iter().find(|entry| entry.key == key).map(|entry| entry.value.as_str())
    }

    fn source_clause_return_function(value: u128) -> (VerifiableFunction, CompilerContractBundle) {
        let mut function = test_function();
        function.body.return_ty = Ty::u64();
        function.body.locals[0] =
            LocalDecl { index: 0, ty: Ty::u64(), name: Some("_0".to_string()) };
        function.body.blocks[0].stmts.push(Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Constant(trust_types::ConstValue::Uint(value, 64))),
            span: function.span.clone(),
        });
        function.contracts.push(Contract {
            kind: TrustTypesContractKind::Ensures,
            span: function.span.clone(),
            body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}result > 0"),
        });
        function.spec.ensures.push("result > 0".to_string());
        function.postconditions.push(trust_types::parse_spec_expr("result > 0").unwrap());
        let contracts = CompilerContractBundle::new(function.contracts.clone());
        (function, contracts)
    }

    #[test]
    fn source_monitor_metadata_accepts_actual_constructor_output() {
        for (function, contracts) in [source_clause_return_function(7), function_with_requires()] {
            let bundle = contract_bundle_to_verifier_api_with_compiler_identity(
                &function,
                &contracts,
                "demo",
                0x1234,
                Some(64),
            );
            let mut checked = 0;
            for obligation in &bundle.obligations {
                let Some(contract) = obligation.contract_id.as_ref().and_then(|id| {
                    bundle.contracts.iter().find(|contract| &contract.contract_id == id)
                }) else {
                    continue;
                };
                assert!(
                    obligation.metadata.iter().any(|entry| entry.key == "trust.contract.lowering")
                );
                assert!(
                    source_monitor_metadata_matches_contract(contract, obligation),
                    "authentic constructor obligation must reach the kernel-record matcher: {obligation:#?}"
                );
                checked += 1;
            }
            assert!(checked > 0, "the regression must exercise an actual source obligation");
        }
    }

    #[test]
    fn source_monitor_metadata_refuses_changed_constructor_lowering_and_claim() {
        let (function, contracts) = source_clause_return_function(7);
        let bundle = contract_bundle_to_verifier_api_with_compiler_identity(
            &function,
            &contracts,
            "demo",
            0x1234,
            Some(64),
        );
        let contract = &bundle.contracts[0];
        let obligation = &bundle.obligations[0];
        assert!(source_monitor_metadata_matches_contract(contract, obligation));
        for mutation in ["missing", "duplicate", "foreign", "extra", "predicate", "source", "id"] {
            let mut changed = obligation.clone();
            match mutation {
                "missing" => {
                    changed.metadata.retain(|entry| entry.key != "trust.contract.lowering")
                }
                "duplicate" => changed.metadata.push(
                    changed
                        .metadata
                        .iter()
                        .find(|entry| entry.key == "trust.contract.lowering")
                        .unwrap()
                        .clone(),
                ),
                "foreign" => {
                    changed
                        .metadata
                        .iter_mut()
                        .find(|entry| entry.key == "trust.contract.lowering")
                        .unwrap()
                        .value = "foreign-lowering".into()
                }
                "extra" => changed.metadata.push(MetadataEntry {
                    key: "foreign.metadata".into(),
                    value: "unbound".into(),
                }),
                "predicate" => {
                    changed
                        .metadata
                        .iter_mut()
                        .find(|entry| entry.key == TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY)
                        .unwrap()
                        .value = "f".repeat(64)
                }
                "source" => {
                    changed
                        .metadata
                        .iter_mut()
                        .find(|entry| entry.key == TRUST_SOURCE_DIGEST_METADATA_KEY)
                        .unwrap()
                        .value = "f".repeat(64)
                }
                "id" => changed.contract_id = Some("foreign-contract".into()),
                _ => unreachable!(),
            }
            assert!(!source_monitor_metadata_matches_contract(contract, &changed), "{mutation}");
        }
        for duplicate in [false, true] {
            let mut changed = contract.clone();
            if duplicate {
                changed.metadata.push(
                    changed
                        .metadata
                        .iter()
                        .find(|entry| entry.key == "trust.contract.lowering")
                        .unwrap()
                        .clone(),
                );
            } else {
                changed.metadata.retain(|entry| entry.key != "trust.contract.lowering");
            }
            assert!(!source_monitor_metadata_matches_contract(&changed, obligation));
        }
    }

    #[test]
    fn source_monitor_metadata_refuses_optional_typed_proposition_ambiguity() {
        let (function, contracts) = source_clause_return_function(7);
        let contract = &contracts.contracts[0];
        let proposition = trust_types::CompilerContractProposition {
            source_contract_index: 0,
            kind: contract.kind,
            body: contract.body.clone(),
            formula: function.postconditions[0].clone(),
            variable_domains: vec![trust_types::CompilerContractVariableDomain {
                name: "_0".into(),
                domain: trust_types::CompilerContractValueDomain::MachineInt {
                    width: 64,
                    signed: false,
                },
            }],
        };
        let contracts = contracts.with_typed_propositions(vec![proposition]);
        assert!(contracts.typed_proposition(0, &contracts.contracts[0]).is_some());
        let bundle = contract_bundle_to_verifier_api_with_compiler_identity(
            &function,
            &contracts,
            "demo",
            0x1234,
            Some(64),
        );
        let contract = &bundle.contracts[0];
        let obligation = &bundle.obligations[0];
        assert!(source_monitor_metadata_matches_contract(contract, obligation));
        let typed = contract
            .metadata
            .iter()
            .find(|entry| entry.key == TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY)
            .expect("actual typed constructor digest")
            .clone();
        let mut ambiguous = contract.clone();
        ambiguous.metadata.push(typed.clone());
        let mut missing = obligation.clone();
        missing
            .metadata
            .retain(|entry| entry.key != TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY);
        assert!(
            !source_monitor_metadata_matches_contract(&ambiguous, &missing),
            "duplicate optional source metadata must not collapse to the missing value"
        );
        for value in ["sha256:invalid".to_owned(), format!("sha256:{}", "f".repeat(64))] {
            let mut changed = obligation.clone();
            changed
                .metadata
                .iter_mut()
                .find(|entry| entry.key == TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY)
                .unwrap()
                .value = value;
            assert!(!source_monitor_metadata_matches_contract(contract, &changed));
        }
        let mut duplicate = obligation.clone();
        duplicate.metadata.push(typed);
        assert!(!source_monitor_metadata_matches_contract(contract, &duplicate));
        let mut malformed_contract = contract.clone();
        let mut malformed_obligation = obligation.clone();
        for entries in [&mut malformed_contract.metadata, &mut malformed_obligation.metadata] {
            entries
                .iter_mut()
                .find(|entry| entry.key == TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY)
                .unwrap()
                .value = "sha256:invalid".into();
        }
        assert!(!source_monitor_metadata_matches_contract(
            &malformed_contract,
            &malformed_obligation
        ));
    }

    #[test]
    fn source_clause_native_formula_is_the_exact_body_violation_not_the_positive_predicate() {
        for value in [0, 1] {
            let (function, contracts) = source_clause_return_function(value);
            let (raw, augmented) =
                trust_vcgen::regenerate_postcondition_production_variants(&function).unwrap();
            assert_eq!(raw.len(), 1);
            for rows in [&raw, &augmented] {
                let formulas = verifier_api_source_clause_body_formula_metadata(
                    &function,
                    &contracts,
                    rows,
                    "demo",
                    Some(64),
                );
                let metadata = formulas.get(&0).expect("fresh body-bound ensures formula");
                let expected =
                    vc_formula_payload_for(&function, &VcKind::Postcondition, &rows[0].formula)
                        .into_metadata();
                assert_eq!(&metadata[..expected.len()], expected);
                let provenance: JsonValue = serde_json::from_str(
                    metadata_value(metadata, "trust.contract.body_vcs.formula.v1").unwrap(),
                )
                .unwrap();
                assert_eq!(provenance["source_contract_index"], 0);
                assert_eq!(provenance["body_vcs"].as_array().unwrap().len(), 1);
                let authored =
                    contract_bundle_to_verifier_api_with_crate_name(&function, &contracts, "demo");
                let positive = typed_spec_predicate(&authored.contracts[0].predicate);
                let violation: TrustSpecPredicate = serde_json::from_str(
                    metadata_value(metadata, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY).unwrap(),
                )
                .unwrap();
                assert_ne!(violation, positive, "body/return facts and violation polarity survive");
            }
        }
    }

    #[test]
    fn source_clause_native_formula_carries_the_whole_claim_digest_before_native_mint() {
        let mut digests = BTreeSet::new();
        for value in [0, 1] {
            let (function, contracts) = source_clause_return_function(value);
            let (raw, augmented) =
                trust_vcgen::regenerate_postcondition_production_variants(&function).unwrap();
            for crate_name in ["demo", "other_demo"] {
                for rows in [&raw, &augmented] {
                    let formulas = verifier_api_source_clause_body_formula_metadata(
                        &function,
                        &contracts,
                        rows,
                        crate_name,
                        Some(64),
                    );
                    let metadata = formulas.get(&0).expect("complete fresh source-clause claim");
                    let digest_entries = metadata
                        .iter()
                        .filter(|entry| entry.key == TRUST_VC_DIGEST_METADATA_KEY)
                        .collect::<Vec<_>>();
                    assert_eq!(
                        digest_entries.len(),
                        1,
                        "native typed CHC binding requires exactly one public VC digest"
                    );
                    let digest = &digest_entries[0].value;
                    assert_eq!(digest.len(), 64);
                    assert!(
                        digest
                            .bytes()
                            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
                    );
                    for (index, row) in rows.iter().enumerate() {
                        assert_ne!(
                            digest,
                            &verifier_vc_content_identity_with_crate_name(
                                &function, index, row, crate_name,
                            )
                            .digest,
                            "one body row is not the whole source-clause claim"
                        );
                    }
                    digests.insert((value, crate_name, digest.clone()));
                }
            }
        }
        let unique = digests.iter().map(|(_, _, digest)| digest).collect::<BTreeSet<_>>();
        assert_eq!(unique.len(), digests.len(), "body and crate identities must not collide");
    }

    #[test]
    fn source_clause_native_formula_refuses_missing_duplicate_stale_and_repointed_rows() {
        let (function, contracts) = source_clause_return_function(0);
        let (raw, _) =
            trust_vcgen::regenerate_postcondition_production_variants(&function).unwrap();
        let mut duplicate = raw.clone();
        duplicate.extend(raw.clone());
        let mut stale = raw.clone();
        stale[0].formula = Formula::Bool(false);
        let mut repointed = raw.clone();
        repointed[0].contract_metadata.as_mut().unwrap().source_contract_index = Some(1);
        let mut wrong_function = raw.clone();
        wrong_function[0].function = "foreign::f".into();
        let mut moved_source = raw.clone();
        moved_source[0].location.line_start += 1;
        for rows in [Vec::new(), duplicate, stale, repointed, wrong_function, moved_source] {
            assert!(
                verifier_api_source_clause_body_formula_metadata(
                    &function,
                    &contracts,
                    &rows,
                    "demo",
                    Some(64),
                )
                .is_empty(),
                "invalid carrier acquired a body formula: {rows:#?}"
            );
        }
        let mut wrong_contracts = contracts.clone();
        wrong_contracts.contracts[0].body.push_str(" && true");
        assert!(
            verifier_api_source_clause_body_formula_metadata(
                &function,
                &wrong_contracts,
                &raw,
                "demo",
                Some(64),
            )
            .is_empty()
        );
        let (changed, _) = source_clause_return_function(1);
        assert!(
            verifier_api_source_clause_body_formula_metadata(
                &changed,
                &contracts,
                &raw,
                "demo",
                Some(64),
            )
            .is_empty(),
            "a different return body must invalidate the old violation"
        );
    }

    #[test]
    fn source_clause_native_formula_requires_and_encodes_every_return() {
        let (mut function, contracts) = source_clause_return_function(0);
        function.body.locals.push(LocalDecl {
            index: 1,
            ty: Ty::Bool,
            name: Some("take_first".to_string()),
        });
        // A real Int-sorted argument retains an interval in the function-wide
        // environment; a Bool-only function has no augmentable Int fact.
        function.body.locals.push(LocalDecl {
            index: 2,
            ty: Ty::i32(),
            name: Some("bounded_input".to_string()),
        });
        function.body.arg_count = 2;
        let mut first = function.body.blocks[0].clone();
        first.id = BlockId(1);
        let mut second = first.clone();
        second.id = BlockId(2);
        second.stmts[0] = Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Constant(trust_types::ConstValue::Uint(1, 64))),
            span: function.span.clone(),
        };
        function.body.blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: Vec::new(),
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(1)),
                    targets: vec![(0, BlockId(1))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: function.span.clone(),
                },
            },
            first,
            second,
        ];
        let (rows, augmented) =
            trust_vcgen::regenerate_postcondition_production_variants(&function).unwrap();
        assert_eq!(rows.len(), 2, "both concrete return paths need their own claim");
        assert_ne!(
            rows[1].formula, augmented[1].formula,
            "mixed control must use a genuinely augmented row"
        );
        let mixed = vec![rows[0].clone(), augmented[1].clone()];
        for supplied in [&rows, &augmented, &mixed] {
            for missing in [0, 1] {
                assert!(
                    verifier_api_source_clause_body_formula_metadata(
                        &function,
                        &contracts,
                        &supplied[missing..missing + 1],
                        "demo",
                        Some(64),
                    )
                    .is_empty(),
                    "one return may not stand for the whole ensures clause"
                );
            }
            let formulas = verifier_api_source_clause_body_formula_metadata(
                &function,
                &contracts,
                supplied,
                "demo",
                Some(64),
            );
            let metadata = formulas.get(&0).expect("complete return violation disjunction");
            let expected = vc_formula_payload_for(
                &function,
                &VcKind::Postcondition,
                &Formula::Or(supplied.iter().map(|vc| vc.formula.clone()).collect()),
            )
            .into_metadata();
            assert_eq!(&metadata[..expected.len()], expected);
            let provenance: JsonValue = serde_json::from_str(
                metadata_value(metadata, "trust.contract.body_vcs.formula.v1").unwrap(),
            )
            .unwrap();
            assert_eq!(provenance["body_vcs"].as_array().unwrap().len(), 2);
        }
    }

    #[test]
    fn source_clause_native_formula_retains_the_pruned_counterexample_barrier() {
        let (mut function, contracts) = source_clause_return_function(0);
        function.preconditions.push(Formula::Eq(
            Box::new(Formula::Select(
                Box::new(Formula::Var(
                    "memory_map".to_string(),
                    Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
                )),
                Box::new(Formula::BitVec { value: 0, width: 64 }),
            )),
            Box::new(Formula::BitVec { value: 0, width: 8 }),
        ));
        let (raw, _) =
            trust_vcgen::regenerate_postcondition_production_variants(&function).unwrap();
        let formulas = verifier_api_source_clause_body_formula_metadata(
            &function,
            &contracts,
            &raw,
            "demo",
            Some(64),
        );
        let metadata =
            formulas.get(&0).expect("lowerable residue remains available for proof only");
        assert_eq!(metadata_value(metadata, TRUST_VC_FORMULA_PRUNED_METADATA_KEY), Some("true"));
        assert!(metadata_value(metadata, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY).is_some());
    }

    #[test]
    fn source_clause_native_formula_covers_both_positive_share_surface_spellings() {
        for clause in ["total_ms > 0 ==> result > 0", "total_ms == 0 || result >= 1"] {
            let (mut function, _) = source_clause_return_function(0);
            function.body.locals.extend([
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("total_ms".to_string()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("parts".to_string()) },
            ]);
            function.body.arg_count = 2;
            let clauses = ["result <= total_ms", clause];
            function.contracts = clauses
                .iter()
                .map(|body| Contract {
                    kind: TrustTypesContractKind::Ensures,
                    span: function.span.clone(),
                    body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}{body}"),
                })
                .collect();
            function.spec.ensures = clauses.iter().map(|body| (*body).to_string()).collect();
            function.postconditions = clauses
                .iter()
                .map(|body| {
                    trust_types::parse_spec_expr(body).expect("actual positive-share clause parses")
                })
                .collect();
            let contracts = CompilerContractBundle::new(function.contracts.clone());
            let (rows, _) =
                trust_vcgen::regenerate_postcondition_production_variants(&function).unwrap();
            assert_eq!(rows.len(), 2);
            let formulas = verifier_api_source_clause_body_formula_metadata(
                &function,
                &contracts,
                &rows,
                "demo",
                Some(64),
            );
            assert_eq!(formulas.len(), 2, "both authored clauses retain their own body claim");
            let metadata =
                formulas.get(&1).expect("original missing conditional/disjunctive claim");
            assert!(metadata_value(metadata, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY).is_some());
            let provenance: JsonValue = serde_json::from_str(
                metadata_value(metadata, "trust.contract.body_vcs.formula.v1").unwrap(),
            )
            .unwrap();
            assert_eq!(provenance["source_contract_index"], 1);
            assert!(provenance["body_vcs"][0]["obligation_id"].as_str().unwrap().ends_with(":1"));
        }
    }

    fn trust_vc_payload(obligation: &TrustObligation) -> JsonValue {
        let value =
            metadata_value(&obligation.metadata, TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY)
                .expect("trust-vc MIR memory proof-unit metadata");
        serde_json::from_str(value).expect("trust-vc MIR memory proof-unit metadata is JSON")
    }

    #[test]
    fn converts_lowered_bool_requires_and_ensures_to_public_obligations() {
        let function = test_function();
        let compiler_contracts = CompilerContractBundle::new(vec![
            Contract {
                kind: TrustTypesContractKind::Requires,
                span: function.span.clone(),
                body: "true".to_string(),
            },
            Contract {
                kind: TrustTypesContractKind::Ensures,
                span: function.span.clone(),
                body: "false".to_string(),
            },
        ]);

        let bundle = contract_bundle_to_verifier_api(&function, &compiler_contracts);

        assert_eq!(bundle.contracts.len(), 2);
        assert_eq!(bundle.obligations.len(), 2);
        assert_eq!(bundle.contracts[0].kind, ContractKind::Requires);
        assert_eq!(bundle.obligations[0].kind, ObligationKind::Precondition);
        assert_eq!(bundle.contracts[1].kind, ContractKind::Ensures);
        assert_eq!(bundle.obligations[1].kind, ObligationKind::Postcondition);
        assert_eq!(bundle.obligations[0].required_strength, Some(ProofStrength::deductive()));
        assert_eq!(
            metadata_value(&bundle.contracts[0].metadata, "trust.contract.predicate.schema"),
            Some(TRUST_SPEC_PREDICATE_SCHEMA_VERSION)
        );
        assert_trust_ir_bool_literal(&bundle.contracts[0].predicate, true);
        assert_trust_ir_bool_literal(&bundle.contracts[1].predicate, false);
        let context = obligation_context(&bundle.obligations[0]);
        assert!(matches!(
            context.origin,
            ObligationOrigin::Contract { contract_index: 0, predicate_schema: Some(_), .. }
        ));
    }

    #[test]
    fn impl_method_contract_bundle_uses_canonical_exact_identities() {
        let mut function = test_function();
        function.name = "rank".to_string();
        function.def_path =
            "<sealed_dyn_probe::Button as sealed_dyn_probe::sealed::Widget>::rank".to_string();
        let compiler_contracts = CompilerContractBundle::new(vec![Contract {
            kind: TrustTypesContractKind::Requires,
            span: function.span.clone(),
            body: "true".to_string(),
        }]);

        let bundle = contract_bundle_to_verifier_api(&function, &compiler_contracts);
        bundle.validate().expect("impl-method bundle must satisfy the public identity schema");
        bundle
            .validate_requested_obligations(&bundle.obligations)
            .expect("impl-method request must be an exact canonical bundle subset");

        assert_eq!(bundle.contracts.len(), 1);
        assert_eq!(bundle.obligations.len(), 1);
        let contract_id = &bundle.contracts[0].contract_id;
        assert!(contract_id.contains("%20as%20"));
        assert!(contract_id.bytes().all(|byte| byte.is_ascii_graphic()));
        assert_eq!(bundle.obligations[0].contract_id.as_ref(), Some(contract_id));
        assert_eq!(trust_types::canonical_contract_source_index(contract_id), Some(0));
        assert!(bundle.obligations[0].obligation_id.contains("h0__x3csealed"));
    }

    #[test]
    fn exact_crate_name_variant_owns_impl_path_subject_context_and_vc_identity() {
        let mut function = test_function();
        function.name = "rank".to_string();
        function.def_path =
            "<sealed_dyn_probe::Button as sealed_dyn_probe::sealed::Widget>::rank".to_string();
        let compiler_contracts = CompilerContractBundle::new(vec![Contract {
            kind: TrustTypesContractKind::Ensures,
            span: function.span.clone(),
            body: "true".to_string(),
        }]);
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: trust_types::Symbol::intern("rank"),
            location: function.span.clone(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };

        let bundle = function_to_verifier_api_bundle_with_crate_name(
            &function,
            &compiler_contracts,
            std::slice::from_ref(&vc),
            "sealed_dyn_probe",
        );

        assert_eq!(
            bundle.subject,
            BundleSubject::Function {
                crate_name: "sealed_dyn_probe".to_string(),
                path: function.def_path.clone(),
            }
        );
        assert!(bundle.obligations.iter().all(|obligation| {
            obligation_context(obligation).function
                == Some(FunctionContext {
                    crate_name: "sealed_dyn_probe".to_string(),
                    path: function.def_path.clone(),
                })
        }));

        let identity =
            verifier_vc_content_identity_with_crate_name(&function, 0, &vc, "sealed_dyn_probe");
        assert_eq!(
            identity.function,
            FunctionContext { crate_name: "sealed_dyn_probe".to_string(), path: function.def_path }
        );
    }

    #[test]
    fn compatibility_wrappers_preserve_simple_function_crate_identity() {
        let function = test_function();
        let compiler_contracts = CompilerContractBundle::new(vec![Contract {
            kind: TrustTypesContractKind::Ensures,
            span: function.span.clone(),
            body: "true".to_string(),
        }]);
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: trust_types::Symbol::intern("demo::f"),
            location: function.span.clone(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };

        let bundle = function_to_verifier_api_bundle(
            &function,
            &compiler_contracts,
            std::slice::from_ref(&vc),
        );

        assert_eq!(
            bundle.subject,
            BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() }
        );
        assert!(bundle.obligations.iter().all(|obligation| {
            obligation_context(obligation).function
                == Some(FunctionContext {
                    crate_name: "demo".to_string(),
                    path: "demo::f".to_string(),
                })
        }));
        assert_eq!(verifier_vc_content_identity(&function, 0, &vc).function.crate_name, "demo");
    }

    #[test]
    fn compatibility_wrapper_refuses_to_invent_impl_crate_identity() {
        let mut function = test_function();
        function.def_path = "<demo::Ty as demo::Trait>::method".to_string();
        let compiler_contracts = CompilerContractBundle::default();

        let compatibility = contract_bundle_to_verifier_api(&function, &compiler_contracts);
        assert_eq!(
            compatibility.subject,
            BundleSubject::Function {
                crate_name: UNRESOLVED_COMPATIBILITY_CRATE_NAME.to_string(),
                path: function.def_path.clone(),
            },
        );

        let exact =
            contract_bundle_to_verifier_api_with_crate_name(&function, &compiler_contracts, "demo");
        assert_eq!(
            exact.subject,
            BundleSubject::Function { crate_name: "demo".to_string(), path: function.def_path },
        );
    }

    #[test]
    fn compiler_identity_binds_same_name_crates_into_bundle_and_semantic_digest() {
        let function = test_function();
        let compiler_contracts = CompilerContractBundle::new(vec![Contract {
            kind: TrustTypesContractKind::Ensures,
            span: function.span.clone(),
            body: "true".to_string(),
        }]);
        let first = contract_bundle_to_verifier_api_with_compiler_identity(
            &function,
            &compiler_contracts,
            "demo",
            0x11,
            None,
        );
        let second = contract_bundle_to_verifier_api_with_compiler_identity(
            &function,
            &compiler_contracts,
            "demo",
            0x22,
            None,
        );

        assert_eq!(first.subject, second.subject);
        assert_eq!(first.obligations, second.obligations);
        assert_ne!(first.bundle_id, second.bundle_id);
        assert!(first.bundle_id.ends_with(":rustc-crate:0000000000000011"));
        assert!(second.bundle_id.ends_with(":rustc-crate:0000000000000022"));
        assert_eq!(
            metadata_value(&first.metadata, TRUST_COMPILER_STABLE_CRATE_ID_METADATA_KEY),
            Some("0000000000000011"),
        );
        assert_eq!(
            metadata_value(&second.metadata, TRUST_COMPILER_STABLE_CRATE_ID_METADATA_KEY),
            Some("0000000000000022"),
        );
        assert_ne!(
            first
                .canonical_obligation_semantic_digest_sha256(&first.obligations[0])
                .expect("first compiler identity digest"),
            second
                .canonical_obligation_semantic_digest_sha256(&second.obligations[0])
                .expect("second compiler identity digest"),
        );

        for (stable_crate_id, expected) in [(0, "0000000000000000"), (u64::MAX, "ffffffffffffffff")]
        {
            let bundle = contract_bundle_to_verifier_api_with_compiler_identity(
                &function,
                &compiler_contracts,
                "demo",
                stable_crate_id,
                None,
            );
            assert_eq!(
                metadata_value(&bundle.metadata, TRUST_COMPILER_STABLE_CRATE_ID_METADATA_KEY,),
                Some(expected),
            );
        }
    }

    #[test]
    fn unlowered_requires_surfaces_contract_bound_unsupported_marker() {
        // Authored spec elaboration is all-or-nothing. Even though a Requires
        // predicate is a caller burden after successful elaboration, a clause
        // that never became a typed proposition must remain an explicit,
        // contract-bound gap.
        let function = test_function();
        let compiler_contracts = CompilerContractBundle::new(vec![Contract {
            kind: TrustTypesContractKind::Requires,
            span: function.span.clone(),
            body: "x > 0".to_string(),
        }]);

        let bundle = contract_bundle_to_verifier_api(&function, &compiler_contracts);

        assert_eq!(bundle.contracts.len(), 1);
        assert!(matches!(&bundle.contracts[0].predicate, ContractPredicate::Unsupported { .. }));
        assert_eq!(bundle.obligations.len(), 1);
        assert!(matches!(
            &bundle.obligations[0].kind,
            ObligationKind::Custom { namespace, name }
                if namespace == "trust.contract" && name == "unsupported"
        ));
        assert_eq!(
            bundle.obligations[0].contract_id.as_deref(),
            Some(bundle.contracts[0].contract_id.as_str()),
        );
    }

    #[test]
    fn unlowered_ensures_still_surfaces_as_unsupported_obligation() {
        // Ensures is the callee's burden — an unsupported marker MUST keep
        // surfacing as a gap so the function fail-closes under the strict default.
        let function = test_function();
        let compiler_contracts = CompilerContractBundle::new(vec![Contract {
            kind: TrustTypesContractKind::Ensures,
            span: function.span.clone(),
            body: "result > 0".to_string(),
        }]);

        let bundle = contract_bundle_to_verifier_api(&function, &compiler_contracts);

        assert_eq!(bundle.contracts.len(), 1);
        assert_eq!(bundle.obligations.len(), 1);
        assert!(matches!(&bundle.contracts[0].predicate, ContractPredicate::Unsupported { .. }));
        assert!(matches!(
            &bundle.obligations[0].kind,
            ObligationKind::Custom { namespace, name }
                if namespace == "trust.contract" && name == "unsupported"
        ));
        assert_eq!(
            bundle.obligations[0].contract_id.as_deref(),
            Some(bundle.contracts[0].contract_id.as_str())
        );
        assert_eq!(bundle.obligations[0].required_strength, Some(ProofStrength::deductive()));
        assert!(
            bundle.obligations[0]
                .description
                .contains("was not lowered into a typed verifier formula")
        );
        assert!(
            bundle.obligations[0].metadata.iter().all(|entry| entry.key != "trust.contract.body")
        );
        assert_eq!(
            metadata_value(
                &bundle.metadata,
                "trust.contract.definition_site_requires_markers_excluded"
            ),
            None,
        );
    }

    #[test]
    fn compiler_lowered_simple_expr_becomes_typed_verifier_api_predicate() {
        let function = test_function();
        let compiler_contracts = CompilerContractBundle::new(vec![Contract {
            kind: TrustTypesContractKind::Requires,
            span: function.span.clone(),
            body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}(x) > (0)"),
        }]);

        let bundle = contract_bundle_to_verifier_api(&function, &compiler_contracts);

        assert_eq!(bundle.contracts.len(), 1);
        assert_eq!(bundle.obligations.len(), 1);
        assert_trust_ir_simple_expr(&bundle.contracts[0].predicate);
        assert_eq!(bundle.obligations[0].kind, ObligationKind::Precondition);
        assert_eq!(bundle.contracts[0].metadata[1].value, "spec_expr");
        let predicate = typed_spec_predicate(&bundle.contracts[0].predicate);
        assert_eq!(predicate.variables.len(), 1);
        assert_eq!(predicate.variables[0].name, "x");
        assert_eq!(predicate.variables[0].sort, TrustSpecSort::Int);
    }

    #[test]
    fn compiler_lowered_method_call_does_not_alias_to_field_projection() {
        let mut function = test_function();
        function.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".to_string()) },
            LocalDecl {
                index: 1,
                ty: Ty::Ref {
                    mutable: false,
                    inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }),
                },
                name: Some("xs".to_string()),
            },
        ];
        function.body.arg_count = 1;
        let compiler_contracts = CompilerContractBundle::new(vec![Contract {
            kind: TrustTypesContractKind::Requires,
            span: function.span.clone(),
            body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}xs.len() > 0"),
        }]);

        let bundle = contract_bundle_to_verifier_api(&function, &compiler_contracts);

        assert_eq!(bundle.contracts.len(), 1);
        let ContractPredicate::Unsupported { reason } = &bundle.contracts[0].predicate else {
            panic!("a method call must stay unsupported until the public schema represents calls")
        };
        assert!(reason.contains("method call `.len()` has no distinct typed verifier payload"));
        assert_eq!(
            metadata_value(&bundle.contracts[0].metadata, "trust.contract.lowering"),
            Some("unsupported")
        );
        assert!(matches!(
            &bundle.obligations[0].kind,
            ObligationKind::Custom { namespace, name }
                if namespace == "trust.contract" && name == "unsupported"
        ));
    }

    #[test]
    fn typed_collection_len_proposition_uses_structural_verifier_formula() {
        let mut function = test_function();
        function.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".to_string()) },
            LocalDecl {
                index: 1,
                ty: Ty::Ref {
                    mutable: false,
                    inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }),
                },
                name: Some("xs".to_string()),
            },
        ];
        function.body.arg_count = 1;
        let contract = Contract {
            kind: TrustTypesContractKind::Requires,
            span: function.span.clone(),
            body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}xs.len() > 0"),
        };
        let formula = Formula::Gt(
            Box::new(Formula::Var("xs__len".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let compiler_contracts = CompilerContractBundle::new(vec![contract.clone()])
            .with_typed_propositions(vec![trust_types::CompilerContractProposition {
                source_contract_index: 0,
                kind: contract.kind,
                body: contract.body.clone(),
                formula,
                variable_domains: vec![trust_types::CompilerContractVariableDomain {
                    // Trust: DOUBLE underscore. `map_method_call`
                    // (trust-types/src/spec_parse.rs) lowers `.len()` to
                    // `{base}__len`, and `typed_proposition`'s round-trip
                    // provenance gate REPARSES the retained body
                    // `"xs.len() > 0"` and requires the domain sidecar to
                    // cover exactly the leaves that reparse produces. A
                    // single-underscore `xs_len` is not covered, the
                    // proposition is dropped as unprovenanced, and lowering
                    // silently falls through to the UNTYPED source lane —
                    // which is why this test saw `Unsupported { ".len() has
                    // no distinct typed verifier payload yet" }` and never
                    // reached the typed lane it is named for.
                    name: "xs__len".to_string(),
                    domain: trust_types::CompilerContractValueDomain::PointerSizedInt {
                        width: 64,
                        signed: false,
                    },
                }],
            }]);

        let bundle = contract_bundle_to_verifier_api(&function, &compiler_contracts);

        assert_eq!(bundle.contracts.len(), 1);
        assert_eq!(bundle.obligations.len(), 1);
        // Trust: report the predicate we DID get. `assert!(matches!(..))`
        // discards it, which is how a whole cluster of E4 failures spent six
        // hypotheses arguing about a reason the value already carried.
        assert!(
            matches!(bundle.contracts[0].predicate, ContractPredicate::TrustIr { .. }),
            "expected a TrustIr predicate, got {:?}",
            bundle.contracts[0].predicate
        );
        assert_eq!(bundle.obligations[0].kind, ObligationKind::Precondition);
        assert_eq!(
            metadata_value(&bundle.contracts[0].metadata, "trust.contract.lowering"),
            Some("typed_proposition"),
        );
        assert!(
            metadata_value(
                &bundle.contracts[0].metadata,
                TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY,
            )
            .is_some()
        );
    }

    #[test]
    fn compiler_lowered_machine_arithmetic_remains_fail_closed() {
        // The verifier-api carrier currently has only an undifferentiated Int
        // sort. A u8 expression cannot cross this bridge as mathematical Int:
        // `x + 1 > x` is false at 255 but would otherwise look tautological.
        let mut function = test_function();
        function.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u8(), name: Some("_0".to_string()) },
            LocalDecl { index: 1, ty: Ty::u8(), name: Some("x".to_string()) },
        ];
        function.body.arg_count = 1;
        function.body.return_ty = Ty::u8();
        let compiler_contracts = CompilerContractBundle::new(vec![
            Contract {
                kind: TrustTypesContractKind::Requires,
                span: function.span.clone(),
                body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}(x + 1) > x"),
            },
            Contract {
                kind: TrustTypesContractKind::Ensures,
                span: function.span.clone(),
                body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}(result + 1) > result"),
            },
        ]);

        let bundle = contract_bundle_to_verifier_api(&function, &compiler_contracts);

        assert_eq!(bundle.contracts.len(), 2);
        assert_eq!(bundle.obligations.len(), 2);
        for (contract, obligation) in bundle.contracts.iter().zip(&bundle.obligations) {
            assert!(matches!(&contract.predicate, ContractPredicate::Unsupported { .. }));
            assert_eq!(
                metadata_value(&contract.metadata, "trust.contract.lowering"),
                Some(UNMODELED_CONTRACT_ARITHMETIC_LOWERING),
            );
            assert!(matches!(
                &obligation.kind,
                ObligationKind::Custom { namespace, name }
                    if namespace == "trust.contract" && name == "unsupported"
            ));
            assert_eq!(obligation.contract_id.as_deref(), Some(contract.contract_id.as_str()));
        }
    }

    #[test]
    fn typed_unsigned_literal_remainder_preserves_width_and_digest() {
        let mut digests = std::collections::BTreeSet::new();
        // Exact Int lifts can compare different source widths without a
        // wrapping operation. Keep the final mixed-width row as a positive
        // control alongside every supported numerator width.
        for (width, result_width) in [(8, 8), (16, 16), (32, 32), (64, 64), (128, 128), (32, 64)] {
            let mut function = test_function();
            let arg_ty = Ty::Int { width, signed: false };
            let result_ty = Ty::Int { width: result_width, signed: false };
            function.body.locals = vec![
                LocalDecl { index: 0, ty: result_ty.clone(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: arg_ty, name: Some("x".into()) },
            ];
            function.body.arg_count = 1;
            function.body.return_ty = result_ty;
            let contract = Contract {
                kind: TrustTypesContractKind::Ensures,
                span: function.span.clone(),
                body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}result == x % 2"),
            };
            let formula = Formula::Eq(
                Box::new(Formula::Var("_0".into(), Sort::Int)),
                Box::new(Formula::Rem(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(2)),
                )),
            );
            let variable_domains = [("_0", result_width), ("x", width)]
                .into_iter()
                .map(|(name, width)| trust_types::CompilerContractVariableDomain {
                    name: name.into(),
                    domain: trust_types::CompilerContractValueDomain::MachineInt {
                        width,
                        signed: false,
                    },
                })
                .collect::<Vec<_>>();
            let digest =
                trust_types::typed_contract_proposition_digest(&formula, &variable_domains);
            assert!(digests.insert(digest.clone()), "source domains must have distinct digests");
            // Preserve the original formula; the sidecar and digest retain
            // both declared widths, including the mixed-width control.
            let expected =
                trust_spec_predicate_from_formula(&formula).expect("exact Int remainder");
            let compiler_contracts = CompilerContractBundle::new(vec![contract.clone()])
                .with_typed_propositions(vec![trust_types::CompilerContractProposition {
                    source_contract_index: 0,
                    kind: contract.kind,
                    body: contract.body.clone(),
                    formula,
                    variable_domains,
                }]);
            assert!(compiler_contracts.typed_proposition(0, &contract).is_some());
            let bundle = contract_bundle_to_verifier_api(&function, &compiler_contracts);
            let predicate = typed_spec_predicate(&bundle.contracts[0].predicate);
            assert_eq!(predicate.validate(), Ok(()));
            assert_eq!(predicate, expected);
            assert!(matches!(bundle.obligations[0].kind, ObligationKind::Postcondition));
            for metadata in [&bundle.contracts[0].metadata, &bundle.obligations[0].metadata] {
                assert_eq!(
                    metadata_value(metadata, "trust.contract.lowering"),
                    Some("typed_proposition")
                );
                assert_eq!(
                    metadata_value(metadata, TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY),
                    Some(digest.as_str())
                );
            }
        }
    }

    #[test]
    fn typed_remainder_preserves_definedness_and_declared_domains() {
        for (width, signed, result_width, expression) in [
            (8, false, 8, "result == x % 0"),
            (8, false, 8, "result == x % result"),
            (8, false, 8, "result == x % 256"),
            (8, false, 8, "result == (x + 1) % 2"),
            (8, false, 8, "result == x / 2"),
            (8, true, 8, "result == x % 2"),
            (8, true, 8, "result == x % -1"),
        ] {
            let mut function = test_function();
            function.body.locals = vec![
                LocalDecl {
                    index: 0,
                    ty: Ty::Int { width: result_width, signed },
                    name: Some("_0".into()),
                },
                LocalDecl { index: 1, ty: Ty::Int { width, signed }, name: Some("x".into()) },
            ];
            function.body.arg_count = 1;
            function.body.return_ty = Ty::Int { width: result_width, signed };
            let contract = Contract {
                kind: TrustTypesContractKind::Ensures,
                span: function.span.clone(),
                body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}{expression}"),
            };
            let variable_domains = [("_0", result_width), ("x", width)]
                .into_iter()
                .map(|(name, width)| trust_types::CompilerContractVariableDomain {
                    name: name.into(),
                    domain: trust_types::CompilerContractValueDomain::MachineInt { width, signed },
                })
                .collect();
            let compiler_contracts = CompilerContractBundle::new(vec![contract.clone()])
                .with_typed_propositions(vec![trust_types::CompilerContractProposition {
                    source_contract_index: 0,
                    kind: contract.kind,
                    body: contract.body.clone(),
                    formula: trust_types::parse_spec_expr(expression).expect("source clause"),
                    variable_domains,
                }]);
            assert!(
                compiler_contracts.typed_proposition(0, &contract).is_some(),
                "typed input: {expression}"
            );
            let bundle = contract_bundle_to_verifier_api(&function, &compiler_contracts);
            // Public main added the total declared-width remainder lane:
            // wrapping arithmetic and a positive signed literal now transport
            // at their original BV width. Undefined divisors remain refused.
            if expression == "result == (x + 1) % 2" || (signed && expression == "result == x % 2")
            {
                assert!(
                    matches!(&bundle.contracts[0].predicate, ContractPredicate::TrustIr { .. }),
                    "{expression}"
                );
                assert_eq!(
                    metadata_value(&bundle.contracts[0].metadata, "trust.contract.lowering"),
                    Some("typed_proposition_machine_width")
                );
                assert_eq!(typed_spec_predicate(&bundle.contracts[0].predicate).validate(), Ok(()));
            } else {
                assert!(
                    matches!(&bundle.contracts[0].predicate, ContractPredicate::Unsupported { .. }),
                    "{expression}: {:?}",
                    bundle.contracts[0].predicate
                );
                assert_eq!(
                    metadata_value(&bundle.contracts[0].metadata, "trust.contract.lowering"),
                    Some(UNMODELED_CONTRACT_ARITHMETIC_LOWERING)
                );
            }
        }
    }

    #[test]
    fn typed_literal_remainder_preserves_machine_domain_and_definedness() {
        use trust_types::{
            CompilerContractProposition, CompilerContractValueDomain as Domain,
            CompilerContractVariableDomain,
        };
        for signed in [false, true] {
            let rem = |divisor| {
                Formula::Eq(
                    Box::new(Formula::Rem(
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                        Box::new(divisor),
                    )),
                    Box::new(Formula::Int(0)),
                )
            };
            let proposition = |formula| CompilerContractProposition {
                source_contract_index: 0,
                kind: TrustTypesContractKind::Ensures,
                body: "x % 2 == 0".into(),
                formula,
                variable_domains: vec![CompilerContractVariableDomain {
                    name: "x".into(),
                    domain: Domain::MachineInt { width: 32, signed },
                }],
            };
            let dividend = Box::new(Formula::Var("x".into(), Sort::BitVec(32)));
            let divisor = Box::new(Formula::BitVec { value: 2, width: 32 });
            let expected = if signed {
                Formula::BvSRem(dividend, divisor, 32)
            } else {
                Formula::BvURem(dividend, divisor, 32)
            };
            let expected =
                Formula::Eq(Box::new(expected), Box::new(Formula::BitVec { value: 0, width: 32 }));
            assert_eq!(
                machine_width_proposition_formula(&proposition(rem(Formula::Int(2)))),
                Some(expected.clone()),
            );
            // The pure machine elaboration is not enough: the public transport
            // must retain the same signedness and width as a validated payload.
            let predicate = trust_spec_predicate_from_formula(&expected)
                .expect("literal remainder must cross the complete typed encoder");
            let wire = predicate.clone().into_contract_predicate().unwrap();
            assert_eq!(
                TrustSpecPredicate::from_contract_predicate(&wire).unwrap(),
                Some(predicate)
            );
            let ContractPredicate::TrustIr { value, .. } = wire else { unreachable!() };
            assert_eq!(
                value["root"]["kind"]["lhs"]["kind"]["op"],
                if signed { "srem" } else { "urem" }
            );
            for divisor in [
                Formula::Int(0),
                Formula::Int(-1),
                Formula::UInt(1_u128 << 32),
                Formula::Var("x".into(), Sort::Int),
                Formula::Add(Box::new(Formula::Int(1)), Box::new(Formula::Int(1))),
            ] {
                assert!(machine_width_proposition_formula(&proposition(rem(divisor))).is_none());
            }
            let division = Formula::Eq(
                Box::new(Formula::Div(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(2)),
                )),
                Box::new(Formula::Int(0)),
            );
            assert!(machine_width_proposition_formula(&proposition(division)).is_none());
        }
    }

    #[test]
    fn typed_digest_survives_machine_arithmetic_lowering() {
        let mut function = test_function();
        function.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u8(), name: Some("_0".to_string()) },
            LocalDecl { index: 1, ty: Ty::u8(), name: Some("x".to_string()) },
        ];
        function.body.arg_count = 1;
        function.body.return_ty = Ty::u8();
        let contract = Contract {
            kind: TrustTypesContractKind::Ensures,
            span: function.span.clone(),
            body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}result == x + x"),
        };
        let formula = Formula::Eq(
            Box::new(Formula::Var("_0".to_string(), Sort::Int)),
            Box::new(Formula::Add(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
            )),
        );
        let variable_domains = vec![
            trust_types::CompilerContractVariableDomain {
                name: "_0".to_string(),
                domain: trust_types::CompilerContractValueDomain::MachineInt {
                    width: 8,
                    signed: false,
                },
            },
            trust_types::CompilerContractVariableDomain {
                name: "x".to_string(),
                domain: trust_types::CompilerContractValueDomain::MachineInt {
                    width: 8,
                    signed: false,
                },
            },
        ];
        let expected_digest =
            trust_types::typed_contract_proposition_digest(&formula, &variable_domains);
        let compiler_contracts = CompilerContractBundle::new(vec![contract.clone()])
            .with_typed_propositions(vec![trust_types::CompilerContractProposition {
                source_contract_index: 0,
                kind: contract.kind,
                body: contract.body.clone(),
                formula,
                variable_domains,
            }]);

        let bundle = contract_bundle_to_verifier_api(&function, &compiler_contracts);

        // Trust: machine-width arithmetic in a contract USED to be unmodeled,
        // and this test pinned that the typed-proposition digest was stamped
        // anyway, on the way out through the `Unsupported` marker. Production
        // now MODELS it: `result == x + x` over `u8` locals lowers to a real
        // width-8 bit-vector proposition and the ensures clause carries a
        // genuine `Postcondition`, not a `trust.contract / unsupported` row.
        //
        // The digest assertions below are what this test was always about and
        // are unchanged -- they now witness the digest surviving a SUPPORTED
        // lowering, which is the stronger statement. Coverage of the digest on
        // the unsupported path is not lost: the shapes that remain unmodeled
        // still assert the `Unsupported` marker in the tests above.
        assert!(
            matches!(&bundle.contracts[0].predicate, ContractPredicate::TrustIr { .. }),
            "machine-width arithmetic must lower to a typed predicate, got {:?}",
            bundle.contracts[0].predicate,
        );
        assert_eq!(
            metadata_value(&bundle.contracts[0].metadata, "trust.contract.lowering"),
            Some("typed_proposition_machine_width"),
            "the width-aware lowering is what makes this contract supported; a fall back to              the unmodeled marker is a capability regression, not a cosmetic change",
        );
        assert!(
            matches!(&bundle.obligations[0].kind, ObligationKind::Postcondition),
            "an ensures clause that lowers must carry a real postcondition obligation, got {:?}",
            bundle.obligations[0].kind,
        );
        assert_eq!(
            metadata_value(
                &bundle.contracts[0].metadata,
                TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY,
            ),
            Some(expected_digest.as_str()),
        );
        assert_eq!(
            metadata_value(
                &bundle.obligations[0].metadata,
                TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY,
            ),
            Some(expected_digest.as_str()),
        );
    }

    #[test]
    fn arithmetic_nested_under_quantifier_is_rejected_recursively() {
        let function = test_function();
        let compiler_contracts = CompilerContractBundle::new(vec![Contract {
            kind: TrustTypesContractKind::Ensures,
            span: function.span.clone(),
            body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}forall(i, 0..1, i + 1 > i)"),
        }]);

        let bundle = contract_bundle_to_verifier_api(&function, &compiler_contracts);

        assert_eq!(bundle.obligations.len(), 1);
        assert!(matches!(&bundle.contracts[0].predicate, ContractPredicate::Unsupported { .. }));
        assert_eq!(
            metadata_value(&bundle.contracts[0].metadata, "trust.contract.lowering"),
            Some(UNMODELED_CONTRACT_ARITHMETIC_LOWERING),
        );
    }

    #[test]
    fn compiler_lowered_bounded_quantifier_becomes_typed_public_obligation() {
        let mut function = test_function();
        function.body.arg_count = 1;
        function.body.locals.push(LocalDecl {
            index: 1,
            ty: Ty::i32(),
            name: Some("x".to_string()),
        });
        let compiler_contracts = CompilerContractBundle::new(vec![Contract {
            kind: TrustTypesContractKind::Ensures,
            span: function.span.clone(),
            body: format!(
                "{LOWERED_COMPILER_CONTRACT_PREFIX}forall(i, 0..1, old(x) == old(x) && i == i => result == x)"
            ),
        }]);

        let bundle = contract_bundle_to_verifier_api(&function, &compiler_contracts);

        assert_eq!(bundle.contracts.len(), 1);
        assert_eq!(bundle.obligations.len(), 1);
        assert_eq!(bundle.obligations[0].kind, ObligationKind::Postcondition);
        assert_eq!(
            metadata_value(&bundle.contracts[0].metadata, "trust.contract.lowering"),
            Some("spec_expr"),
        );
        let predicate = typed_spec_predicate(&bundle.contracts[0].predicate);
        assert!(matches!(
            predicate.root.kind,
            TrustSpecExprKind::Quantifier {
                quantifier: TrustSpecQuantifier::Forall,
                ref variable,
                variable_sort: TrustSpecSort::Int,
                ..
            } if variable == "i"
        ));
        assert!(predicate.variables.iter().any(|variable| {
            variable.name == "i"
                && variable.origin == TrustSpecVariableOrigin::Quantified
                && variable.sort == TrustSpecSort::Int
        }));
        assert!(predicate.variables.iter().any(|variable| {
            variable.name == "x"
                && variable.origin == TrustSpecVariableOrigin::Local { index: 1 }
                && variable.sort == TrustSpecSort::Int
        }));
    }

    #[test]
    fn machine_typed_existential_gets_an_exact_domain_guard() {
        // Without the u8 guard, `exists i: u8, i < 0` changes from false over
        // Rust values to true over unbounded Int.
        let function = test_function();
        let compiler_contracts = CompilerContractBundle::new(vec![Contract {
            kind: TrustTypesContractKind::Ensures,
            span: function.span.clone(),
            body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}exists(i: u8, i < 0)"),
        }]);

        let bundle = contract_bundle_to_verifier_api(&function, &compiler_contracts);

        assert_eq!(bundle.obligations.len(), 1);
        let predicate = typed_spec_predicate(&bundle.contracts[0].predicate);
        let TrustSpecExprKind::Quantifier {
            quantifier: TrustSpecQuantifier::Exists,
            variable_sort: TrustSpecSort::Int,
            body,
            ..
        } = predicate.root.kind
        else {
            panic!("expected typed u8 existential")
        };
        let TrustSpecExprKind::Binary { op: TrustSpecBinaryOp::And, lhs: guard, rhs: original } =
            body.kind
        else {
            panic!("existential domain must be conjoined with its body")
        };
        let TrustSpecExprKind::Binary { op: TrustSpecBinaryOp::And, lhs: lower, rhs: upper } =
            guard.kind
        else {
            panic!("u8 domain must carry lower and upper bounds")
        };
        assert!(matches!(lower.kind, TrustSpecExprKind::Binary { op: TrustSpecBinaryOp::Ge, .. }));
        let TrustSpecExprKind::Binary { op: TrustSpecBinaryOp::Le, rhs: upper_bound, .. } =
            upper.kind
        else {
            panic!("u8 upper bound must use <=")
        };
        assert!(matches!(
            upper_bound.kind,
            TrustSpecExprKind::IntLiteral { ref value } if value == "255"
        ));
        assert!(matches!(
            original.kind,
            TrustSpecExprKind::Binary { op: TrustSpecBinaryOp::Lt, .. }
        ));
    }

    #[test]
    fn pointer_sized_quantifiers_fail_closed_without_a_target_width() {
        let function = test_function();
        let compiler_contracts = CompilerContractBundle::new(vec![
            Contract {
                kind: TrustTypesContractKind::Ensures,
                span: function.span.clone(),
                body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}exists(i: usize, i == i)"),
            },
            Contract {
                kind: TrustTypesContractKind::Ensures,
                span: function.span.clone(),
                body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}exists(i: isize, i == i)"),
            },
        ]);

        // The compatibility surface cannot name a target, and the production
        // constructor must stay closed for an absent or unsupported width —
        // never fall back to a guessed domain.
        let unsupported_sentinels = |bundle: &TrustContractBundle| {
            assert_eq!(bundle.obligations.len(), 2);
            assert!(bundle.contracts.iter().all(|contract| matches!(
                &contract.predicate,
                ContractPredicate::Unsupported { .. }
            )));
            assert!(bundle.obligations.iter().all(|obligation| matches!(
                &obligation.kind,
                ObligationKind::Custom { namespace, name }
                    if namespace == "trust.contract" && name == "unsupported"
            )));
        };

        unsupported_sentinels(&contract_bundle_to_verifier_api(&function, &compiler_contracts));
        for width in [None, Some(0), Some(8), Some(24), Some(128)] {
            unsupported_sentinels(&contract_bundle_to_verifier_api_with_compiler_identity(
                &function,
                &compiler_contracts,
                "demo",
                0x11,
                width,
            ));
        }
    }

    #[test]
    fn pointer_sized_quantifier_domain_follows_the_supplied_target_width() {
        // The domain is computed from the SUPPLIED target width — never the
        // host, never a hardcoded 64 — and every unknown width stays closed.
        for (bits, expected_max) in
            [(16u32, u128::from(u16::MAX)), (32, u128::from(u32::MAX)), (64, u128::from(u64::MAX))]
        {
            let Some((TrustSpecSort::Int, Some(SpecQuantifierDomain::UnsignedInclusive { max }))) =
                spec_quantifier_sort_domain("usize", Some(bits))
            else {
                panic!("usize must lower at supplied width {bits}");
            };
            assert_eq!(max, expected_max);
        }
        for (bits, expected_min, expected_max) in [
            (16u32, i128::from(i16::MIN), i128::from(i16::MAX)),
            (32, i128::from(i32::MIN), i128::from(i32::MAX)),
            (64, i128::from(i64::MIN), i128::from(i64::MAX)),
        ] {
            let Some((TrustSpecSort::Int, Some(SpecQuantifierDomain::Inclusive { min, max }))) =
                spec_quantifier_sort_domain("isize", Some(bits))
            else {
                panic!("isize must lower at supplied width {bits}");
            };
            assert_eq!((min, max), (expected_min, expected_max));
        }
        for unsupported in [None, Some(0), Some(24), Some(48), Some(128)] {
            assert!(spec_quantifier_sort_domain("usize", unsupported).is_none());
            assert!(spec_quantifier_sort_domain("isize", unsupported).is_none());
        }
        // The width input must never leak into fixed-width binders.
        assert!(matches!(
            spec_quantifier_sort_domain("u8", Some(16)),
            Some((TrustSpecSort::Int, Some(SpecQuantifierDomain::UnsignedInclusive { max: 255 })))
        ));
        assert!(spec_quantifier_sort_domain("u8", None).is_some());
    }

    #[test]
    fn pointer_sized_forall_lowers_typed_with_the_target_domain_guard() {
        // Production path: the SAME compiler-identity constructor the
        // compiler's build_full_verification_input calls, now carrying the
        // target pointer width. On a 32-bit target the guard must bind i to
        // [0, u32::MAX]; a 64-bit host must not leak in.
        let function = test_function();
        let compiler_contracts = CompilerContractBundle::new(vec![Contract {
            kind: TrustTypesContractKind::Ensures,
            span: function.span.clone(),
            body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}forall(i: usize, i == i)"),
        }]);

        let bundle = contract_bundle_to_verifier_api_with_compiler_identity(
            &function,
            &compiler_contracts,
            "demo",
            0x11,
            Some(32),
        );

        assert_eq!(bundle.obligations.len(), 1);
        assert_eq!(
            metadata_value(&bundle.contracts[0].metadata, "trust.contract.lowering"),
            Some("spec_expr"),
        );
        let predicate = typed_spec_predicate(&bundle.contracts[0].predicate);
        let TrustSpecExprKind::Quantifier {
            quantifier: TrustSpecQuantifier::Forall,
            variable_sort: TrustSpecSort::Int,
            body,
            ..
        } = predicate.root.kind
        else {
            panic!("expected typed usize universal")
        };
        let TrustSpecExprKind::Binary { op: TrustSpecBinaryOp::Implies, lhs: guard, rhs: original } =
            body.kind
        else {
            panic!("universal domain must imply its body")
        };
        let TrustSpecExprKind::Binary { op: TrustSpecBinaryOp::And, lhs: lower, rhs: upper } =
            guard.kind
        else {
            panic!("usize domain must carry lower and upper bounds")
        };
        assert!(matches!(lower.kind, TrustSpecExprKind::Binary { op: TrustSpecBinaryOp::Ge, .. }));
        let TrustSpecExprKind::Binary { op: TrustSpecBinaryOp::Le, rhs: upper_bound, .. } =
            upper.kind
        else {
            panic!("usize upper bound must use <=")
        };
        assert!(matches!(
            upper_bound.kind,
            TrustSpecExprKind::IntLiteral { ref value } if value == "4294967295"
        ));
        assert!(matches!(
            original.kind,
            TrustSpecExprKind::Binary { op: TrustSpecBinaryOp::Eq, .. }
        ));
    }

    #[test]
    fn pointer_sized_existential_gets_the_signed_target_domain_guard() {
        // isize existentials conjoin their exact signed target range: choosing
        // a witness outside the target's isize would change the proposition.
        let function = test_function();
        let compiler_contracts = CompilerContractBundle::new(vec![Contract {
            kind: TrustTypesContractKind::Ensures,
            span: function.span.clone(),
            body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}exists(i: isize, i < 0)"),
        }]);

        let bundle = contract_bundle_to_verifier_api_with_compiler_identity(
            &function,
            &compiler_contracts,
            "demo",
            0x11,
            Some(64),
        );

        let predicate = typed_spec_predicate(&bundle.contracts[0].predicate);
        let TrustSpecExprKind::Quantifier {
            quantifier: TrustSpecQuantifier::Exists,
            variable_sort: TrustSpecSort::Int,
            body,
            ..
        } = predicate.root.kind
        else {
            panic!("expected typed isize existential")
        };
        let TrustSpecExprKind::Binary { op: TrustSpecBinaryOp::And, lhs: guard, rhs: original } =
            body.kind
        else {
            panic!("existential domain must be conjoined with its body")
        };
        let TrustSpecExprKind::Binary { op: TrustSpecBinaryOp::And, lhs: lower, rhs: upper } =
            guard.kind
        else {
            panic!("isize domain must carry lower and upper bounds")
        };
        let TrustSpecExprKind::Binary { op: TrustSpecBinaryOp::Ge, rhs: lower_bound, .. } =
            lower.kind
        else {
            panic!("isize lower bound must use >=")
        };
        assert!(matches!(
            lower_bound.kind,
            TrustSpecExprKind::IntLiteral { ref value } if value == "-9223372036854775808"
        ));
        let TrustSpecExprKind::Binary { op: TrustSpecBinaryOp::Le, rhs: upper_bound, .. } =
            upper.kind
        else {
            panic!("isize upper bound must use <=")
        };
        assert!(matches!(
            upper_bound.kind,
            TrustSpecExprKind::IntLiteral { ref value } if value == "9223372036854775807"
        ));
        assert!(matches!(
            original.kind,
            TrustSpecExprKind::Binary { op: TrustSpecBinaryOp::Lt, .. }
        ));
    }

    #[test]
    fn full_bundle_constructor_threads_the_target_width_to_quantifier_binders() {
        // The contracts+VCs funnel must see the same width as the
        // contract-only reference constructor.
        let function = test_function();
        let compiler_contracts = CompilerContractBundle::new(vec![Contract {
            kind: TrustTypesContractKind::Ensures,
            span: function.span.clone(),
            body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}forall(i: usize, i == i)"),
        }]);

        let bundle =
            function_to_verifier_api_bundle_with_loop_feedback_candidates_and_compiler_identity(
                &function,
                &compiler_contracts,
                &[],
                &[],
                "demo",
                0x11,
                Some(32),
            );

        assert!(matches!(
            typed_spec_predicate(&bundle.contracts[0].predicate).root.kind,
            TrustSpecExprKind::Quantifier { quantifier: TrustSpecQuantifier::Forall, .. }
        ));
        assert!(bundle.obligations.iter().all(|obligation| !matches!(
            &obligation.kind,
            ObligationKind::Custom { namespace, name }
                if namespace == "trust.contract" && name == "unsupported"
        )));
    }

    #[test]
    fn malformed_bounded_quantifier_remains_unsupported_in_public_contract_row() {
        let function = test_function();
        for malformed in
            ["forall(i, 0, i == i)", "forall(i, 0..1 i == i)", "exists(i, 0..1, i == i"]
        {
            let compiler_contracts = CompilerContractBundle::new(vec![Contract {
                kind: TrustTypesContractKind::Ensures,
                span: function.span.clone(),
                body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}{malformed}"),
            }]);

            let bundle = contract_bundle_to_verifier_api(&function, &compiler_contracts);
            assert!(
                matches!(&bundle.contracts[0].predicate, ContractPredicate::Unsupported { .. }),
                "malformed predicate must fail closed: {malformed}",
            );
            assert_eq!(
                metadata_value(&bundle.contracts[0].metadata, "trust.contract.lowering"),
                Some("unsupported"),
            );
        }
    }

    #[test]
    fn compiler_lowered_spec_expr_uses_local_type_metadata_when_available() {
        let mut function = test_function();
        function.body.arg_count = 1;
        function.body.locals.push(LocalDecl {
            index: 1,
            ty: Ty::i32(),
            name: Some("x".to_string()),
        });
        let compiler_contracts = CompilerContractBundle::new(vec![Contract {
            kind: TrustTypesContractKind::Requires,
            span: function.span.clone(),
            body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}x > 0"),
        }]);

        let bundle = contract_bundle_to_verifier_api(&function, &compiler_contracts);
        let predicate = typed_spec_predicate(&bundle.contracts[0].predicate);

        assert_eq!(predicate.root_sort, TrustSpecSort::Bool);
        assert_eq!(predicate.variables.len(), 1);
        assert_eq!(predicate.variables[0].origin, TrustSpecVariableOrigin::Local { index: 1 });
    }

    #[test]
    fn compiler_lowered_float_range_contract_becomes_typed_predicate() {
        // The exact production shape that previously died as
        // "compiler-lowered contract predicate `((x) >= (-(1.0e30))) &&
        // ((x) <= (1.0e30))` is untyped: unsupported spec expression node"
        // (the parser-folded negative float literal had no typed carrier).
        let mut function = test_function();
        function.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::Bool, name: Some("_0".to_string()) },
            LocalDecl { index: 1, ty: Ty::f64_ty(), name: Some("x".to_string()) },
        ];
        function.body.arg_count = 1;
        let compiler_contracts = CompilerContractBundle::new(vec![Contract {
            kind: TrustTypesContractKind::Requires,
            span: function.span.clone(),
            body: format!(
                "{LOWERED_COMPILER_CONTRACT_PREFIX}((x) >= (-(1.0e30))) && ((x) <= (1.0e30))"
            ),
        }]);

        let bundle = contract_bundle_to_verifier_api(&function, &compiler_contracts);

        assert_eq!(bundle.contracts.len(), 1);
        assert_eq!(
            metadata_value(&bundle.contracts[0].metadata, "trust.contract.lowering"),
            Some("spec_expr"),
        );
        let predicate = typed_spec_predicate(&bundle.contracts[0].predicate);
        predicate.validate().expect("lowered float contract is canonical public IR");
        assert_eq!(predicate.root_sort, TrustSpecSort::Bool);
        assert_eq!(predicate.variables.len(), 1);
        assert_eq!(predicate.variables[0].name, "x");
        assert_eq!(predicate.variables[0].sort, TrustSpecSort::Float { eb: 11, sb: 53 });
        assert_eq!(predicate.variables[0].origin, TrustSpecVariableOrigin::Local { index: 1 });

        // The folded negative literal transfers as exact IEEE binary64 bits —
        // never a decimal round-trip.
        let TrustSpecExprKind::Binary { op: TrustSpecBinaryOp::And, lhs, rhs } =
            &predicate.root.kind
        else {
            panic!("expected And root, got {:?}", predicate.root.kind);
        };
        let TrustSpecExprKind::Binary { op: TrustSpecBinaryOp::Ge, lhs: ge_lhs, rhs: ge_rhs } =
            &lhs.kind
        else {
            panic!("expected Ge conjunct, got {:?}", lhs.kind);
        };
        assert_eq!(ge_lhs.sort, TrustSpecSort::Float { eb: 11, sb: 53 });
        assert!(matches!(&ge_lhs.kind, TrustSpecExprKind::Variable { name } if name == "x"));
        assert_eq!(
            ge_rhs.kind,
            TrustSpecExprKind::FloatLiteral { bits: (-1.0e30_f64).to_bits(), eb: 11, sb: 53 },
        );
        let TrustSpecExprKind::Binary { op: TrustSpecBinaryOp::Le, rhs: le_rhs, .. } = &rhs.kind
        else {
            panic!("expected Le conjunct, got {:?}", rhs.kind);
        };
        assert_eq!(
            le_rhs.kind,
            TrustSpecExprKind::FloatLiteral { bits: 1.0e30_f64.to_bits(), eb: 11, sb: 53 },
        );
    }

    #[test]
    fn compiler_lowered_float_arithmetic_remains_fail_closed() {
        // Float arithmetic needs rounding-mode semantics the verifier API
        // does not carry: `x + 1.0 > x` is FALSE at 1.0e30 (absorption) but
        // would be a tautology over the reals. It must stay rejected by the
        // recursive unmodeled-arithmetic gate.
        let mut function = test_function();
        function.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::Bool, name: Some("_0".to_string()) },
            LocalDecl { index: 1, ty: Ty::f64_ty(), name: Some("x".to_string()) },
        ];
        function.body.arg_count = 1;
        let compiler_contracts = CompilerContractBundle::new(vec![Contract {
            kind: TrustTypesContractKind::Requires,
            span: function.span.clone(),
            body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}(x + 1.0) > x"),
        }]);

        let bundle = contract_bundle_to_verifier_api(&function, &compiler_contracts);

        assert_eq!(bundle.contracts.len(), 1);
        assert!(matches!(&bundle.contracts[0].predicate, ContractPredicate::Unsupported { .. }));
        assert_eq!(
            metadata_value(&bundle.contracts[0].metadata, "trust.contract.lowering"),
            Some(UNMODELED_CONTRACT_ARITHMETIC_LOWERING),
        );
    }

    #[test]
    fn compiler_lowered_f32_contract_against_binary64_literal_stays_fail_closed() {
        // Spec float literals are always binary64. An f32 parameter must not
        // silently re-round the constant to binary32 — the sort mismatch
        // fails the contract closed instead.
        let mut function = test_function();
        function.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::Bool, name: Some("_0".to_string()) },
            LocalDecl { index: 1, ty: Ty::f32_ty(), name: Some("x".to_string()) },
        ];
        function.body.arg_count = 1;
        let compiler_contracts = CompilerContractBundle::new(vec![Contract {
            kind: TrustTypesContractKind::Requires,
            span: function.span.clone(),
            body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}(x) >= (0.5)"),
        }]);

        let bundle = contract_bundle_to_verifier_api(&function, &compiler_contracts);

        assert_eq!(bundle.contracts.len(), 1);
        let ContractPredicate::Unsupported { reason } = &bundle.contracts[0].predicate else {
            panic!("expected fail-closed predicate, got {:?}", bundle.contracts[0].predicate);
        };
        assert!(reason.contains("is untyped"), "{reason}");
    }

    #[test]
    fn compiler_lowered_spec_expr_preserves_bool_local_equality() {
        let mut function = test_function();
        function.body.arg_count = 2;
        function.body.locals.push(LocalDecl {
            index: 1,
            ty: Ty::Bool,
            name: Some("flag".to_string()),
        });
        function.body.locals.push(LocalDecl {
            index: 2,
            ty: Ty::Bool,
            name: Some("expected".to_string()),
        });
        let compiler_contracts = CompilerContractBundle::new(vec![Contract {
            kind: TrustTypesContractKind::Requires,
            span: function.span.clone(),
            body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}flag == expected"),
        }]);

        let bundle = contract_bundle_to_verifier_api(&function, &compiler_contracts);
        let predicate = typed_spec_predicate(&bundle.contracts[0].predicate);

        assert_eq!(predicate.root_sort, TrustSpecSort::Bool);
        assert_eq!(predicate.variables.len(), 2);
        assert!(predicate.variables.iter().all(|variable| variable.sort == TrustSpecSort::Bool));
        assert!(predicate.variables.iter().any(|variable| {
            variable.name == "flag"
                && variable.origin == TrustSpecVariableOrigin::Local { index: 1 }
        }));
        assert!(predicate.variables.iter().any(|variable| {
            variable.name == "expected"
                && variable.origin == TrustSpecVariableOrigin::Local { index: 2 }
        }));
    }

    #[test]
    fn compiler_marked_unsupported_predicates_become_contract_tied_obligations() {
        let function = test_function();
        let compiler_contracts = CompilerContractBundle::new(vec![Contract {
            kind: TrustTypesContractKind::Ensures,
            span: function.span.clone(),
            body: format!("{UNSUPPORTED_COMPILER_CONTRACT_PREFIX}nontrivial predicate"),
        }]);

        let bundle = contract_bundle_to_verifier_api(&function, &compiler_contracts);

        assert_eq!(bundle.contracts.len(), 1);
        assert_eq!(bundle.obligations.len(), 1);
        assert!(matches!(
            &bundle.contracts[0].predicate,
            ContractPredicate::Unsupported { reason }
                if reason.contains("nontrivial predicate")
        ));
        assert!(matches!(
            &bundle.obligations[0].kind,
            ObligationKind::Custom { namespace, name }
                if namespace == "trust.contract" && name == "unsupported"
        ));
        assert_eq!(
            bundle.obligations[0].contract_id.as_deref(),
            Some(bundle.contracts[0].contract_id.as_str())
        );
        assert!(bundle.obligations[0].description.contains("nontrivial predicate"));
    }

    #[test]
    fn exact_raw_and_interval_augmented_e4_e5_rows_replace_loop_clause_markers() {
        let function = feedback_loop_function();
        let compiler_contracts = feedback_loop_contracts(&function);
        let raw = trust_vcgen::generate_vcs(&function)
            .into_iter()
            .filter(|vc| loop_role(vc).is_some())
            .collect::<Vec<_>>();
        assert_eq!(raw.len(), 3);
        let raw_bundle = function_to_verifier_api_bundle(&function, &compiler_contracts, &raw);
        assert!(loop_contract_marker_indices(&raw_bundle).is_empty(), "{raw_bundle:#?}");
        assert_eq!(
            metadata_value(
                &raw_bundle.metadata,
                TRUST_EXACT_LOOP_CONTRACT_VC_REPLACEMENTS_METADATA_KEY,
            ),
            Some("0,1"),
        );

        let (solver, preclassified) = trust_vcgen::generate_vcs_with_discharge(&function);
        let mut production = solver;
        production.extend(preclassified.into_iter().map(|(vc, _)| vc));
        production.retain(|vc| loop_role(vc).is_some());
        assert_eq!(production.len(), 3);
        assert!(
            production.iter().any(|actual| {
                let role = loop_role(actual);
                raw.iter()
                    .find(|candidate| loop_role(candidate) == role)
                    .is_some_and(|expected| exact_vc_payload(actual) != exact_vc_payload(expected))
            }),
            "fixture must exercise production interval augmentation",
        );
        let production_bundle =
            function_to_verifier_api_bundle(&function, &compiler_contracts, &production);
        assert!(loop_contract_marker_indices(&production_bundle).is_empty());
    }

    #[test]
    fn loop_typed_proposition_digest_requires_exact_unique_bound_source() {
        let mut function = feedback_loop_function();
        let invariant_body = format!("{LOWERED_COMPILER_CONTRACT_PREFIX}n <= 10 && i <= 10");
        let decreases_body = format!("{LOWERED_COMPILER_CONTRACT_PREFIX}i");
        function.contracts[0].body = format!("bb1: {invariant_body}");
        function.contracts[1].body = format!("bb1: {decreases_body}");

        let mut compiler_contracts = feedback_loop_contracts(&function);
        compiler_contracts.loop_contracts[0].body = invariant_body.clone();
        compiler_contracts.loop_contracts[1].body = decreases_body.clone();
        let u32_domain = |name: &str| trust_types::CompilerContractVariableDomain {
            name: name.to_string(),
            domain: trust_types::CompilerContractValueDomain::MachineInt {
                width: 32,
                signed: false,
            },
        };
        let invariant_proposition = trust_types::CompilerContractProposition {
            source_contract_index: 0,
            kind: TrustTypesContractKind::LoopInvariant,
            body: invariant_body,
            formula: trust_types::parse_spec_expr("n <= 10 && i <= 10").expect("typed invariant"),
            variable_domains: vec![u32_domain("i"), u32_domain("n")],
        };
        let decreases_proposition = trust_types::CompilerContractProposition {
            source_contract_index: 1,
            kind: TrustTypesContractKind::Decreases,
            body: decreases_body,
            formula: trust_types::parse_spec_expr("i").expect("typed measure"),
            variable_domains: vec![u32_domain("i")],
        };
        compiler_contracts.typed_propositions =
            vec![invariant_proposition.clone(), decreases_proposition];

        let vcs = trust_vcgen::generate_vcs(&function);
        assert_eq!(
            vcs.iter()
                .filter(|vc| matches!(
                    vc.kind,
                    VcKind::LoopInvariantInitiation { .. }
                        | VcKind::LoopInvariantConsecution { .. }
                ))
                .count(),
            2,
            "the compiler canonical prefix must not make E4 unparseable",
        );
        let exact = function_to_verifier_api_bundle(&function, &compiler_contracts, &vcs);
        assert!(
            exact.contracts[0]
                .metadata
                .iter()
                .any(|entry| { entry.key == TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY }),
            "an exact bound loop proposition must carry its structural digest",
        );

        let mut tampered = compiler_contracts.clone();
        tampered.typed_propositions[0].body.push_str(" && true");
        let tampered_bundle = function_to_verifier_api_bundle(&function, &tampered, &vcs);
        assert!(matches!(
            &tampered_bundle.contracts[0].predicate,
            ContractPredicate::Unsupported { .. }
        ));
        assert!(
            !tampered_bundle.contracts[0]
                .metadata
                .iter()
                .any(|entry| { entry.key == TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY })
        );

        let mut duplicate = compiler_contracts;
        duplicate.typed_propositions.push(invariant_proposition);
        let duplicate_bundle = function_to_verifier_api_bundle(&function, &duplicate, &vcs);
        assert!(matches!(
            &duplicate_bundle.contracts[0].predicate,
            ContractPredicate::Unsupported { .. }
        ));
    }

    #[test]
    fn actual_discharge_partitioned_e4_hybrid_replaces_the_source_marker() {
        let function = feedback_loop_function();
        let compiler_contracts = feedback_loop_contracts(&function);
        let (raw, augmented) =
            trust_vcgen::regenerate_loop_contract_production_variants(&function, &[])
                .expect("production variants");

        let differing_roles = ["initiation", "consecution"]
            .into_iter()
            .filter(|role| {
                let raw_row =
                    raw.iter().find(|vc| loop_role(vc) == Some(*role)).expect("raw E4 role");
                let augmented_row = augmented
                    .iter()
                    .find(|vc| loop_role(vc) == Some(*role))
                    .expect("augmented E4 role");
                exact_vc_payload(raw_row) != exact_vc_payload(augmented_row)
            })
            .collect::<Vec<_>>();
        assert_eq!(
            differing_roles.len(),
            2,
            "fixture must make raw and augmented spellings distinct for both E4 roles",
        );

        let (solver, preclassified) = trust_vcgen::generate_vcs_with_discharge(&function);
        let mut production = solver;
        production.extend(preclassified.into_iter().map(|(vc, _)| vc));
        production.retain(|vc| loop_role(vc).is_some());

        let production_e4 = production
            .iter()
            .filter(|vc| matches!(loop_role(vc), Some("initiation" | "consecution")))
            .collect::<Vec<_>>();
        assert_eq!(production_e4.len(), 2);
        let raw_roles = production_e4
            .iter()
            .filter(|actual| {
                raw.iter()
                    .find(|candidate| loop_role(candidate) == loop_role(actual))
                    .is_some_and(|expected| exact_vc_payload(actual) == exact_vc_payload(expected))
            })
            .count();
        let augmented_roles = production_e4
            .iter()
            .filter(|actual| {
                augmented
                    .iter()
                    .find(|candidate| loop_role(candidate) == loop_role(actual))
                    .is_some_and(|expected| exact_vc_payload(actual) == exact_vc_payload(expected))
            })
            .count();
        assert_eq!(
            (raw_roles, augmented_roles),
            (1, 1),
            "the real discharge/solver partition must exercise one raw and one augmented E4 role",
        );

        let bundle = function_to_verifier_api_bundle(&function, &compiler_contracts, &production);
        assert!(
            loop_contract_marker_indices(&bundle).is_empty(),
            "the exact mixed production carrier must replace both loop markers: {bundle:#?}",
        );
        assert_eq!(
            metadata_value(
                &bundle.metadata,
                TRUST_EXACT_LOOP_CONTRACT_VC_REPLACEMENTS_METADATA_KEY,
            ),
            Some("0,1"),
        );
    }

    #[test]
    fn missing_duplicate_or_forged_loop_rows_leave_the_exact_source_marker_visible() {
        let function = feedback_loop_function();
        let compiler_contracts = feedback_loop_contracts(&function);
        let raw = trust_vcgen::generate_vcs(&function)
            .into_iter()
            .filter(|vc| loop_role(vc).is_some())
            .collect::<Vec<_>>();

        let missing_e5 =
            raw.iter().filter(|vc| loop_role(vc) != Some("decreases")).cloned().collect::<Vec<_>>();
        let missing_bundle =
            function_to_verifier_api_bundle(&function, &compiler_contracts, &missing_e5);
        assert_eq!(loop_contract_marker_indices(&missing_bundle), vec![1]);

        let missing_e4 = raw
            .iter()
            .filter(|vc| loop_role(vc) != Some("initiation"))
            .cloned()
            .collect::<Vec<_>>();
        let missing_e4_bundle =
            function_to_verifier_api_bundle(&function, &compiler_contracts, &missing_e4);
        assert_eq!(loop_contract_marker_indices(&missing_e4_bundle), vec![0]);

        let mut duplicate_e4 = raw.clone();
        duplicate_e4.push(
            raw.iter()
                .find(|vc| loop_role(vc) == Some("initiation"))
                .expect("initiation row")
                .clone(),
        );
        let duplicate_bundle =
            function_to_verifier_api_bundle(&function, &compiler_contracts, &duplicate_e4);
        assert_eq!(loop_contract_marker_indices(&duplicate_bundle), vec![0]);

        let mut forged_e4 = raw.clone();
        let forged = forged_e4
            .iter_mut()
            .find(|vc| loop_role(vc) == Some("consecution"))
            .expect("consecution row");
        forged.formula = Formula::And(vec![Formula::Bool(false), forged.formula.clone()]);
        let forged_bundle =
            function_to_verifier_api_bundle(&function, &compiler_contracts, &forged_e4);
        assert_eq!(loop_contract_marker_indices(&forged_bundle), vec![0]);
    }

    #[test]
    fn recursive_decreases_requires_an_exact_fresh_two_call_bijection() {
        let function = two_call_recursion_function();
        let compiler_contracts = CompilerContractBundle::new(function.contracts.clone());
        let (raw, augmented) =
            trust_vcgen::regenerate_recursion_decreases_production_variants(&function)
                .expect("fresh recursion production variants");
        assert_eq!(raw.len(), 2, "fixture must regenerate both recursive call sites");
        assert_eq!(augmented.len(), raw.len());

        let mixed_exact = vec![raw[0].clone(), augmented[1].clone()];
        let exact_bundle =
            function_to_verifier_api_bundle(&function, &compiler_contracts, &mixed_exact);
        assert!(
            source_contract_marker_indices(&exact_bundle).is_empty(),
            "each exact call-site row may independently use its raw or production-augmented shape: {exact_bundle:#?}",
        );
        assert_eq!(
            metadata_value(
                &exact_bundle.metadata,
                TRUST_EXACT_LOOP_CONTRACT_VC_REPLACEMENTS_METADATA_KEY,
            ),
            Some("0"),
        );

        let missing_bundle = function_to_verifier_api_bundle(
            &function,
            &compiler_contracts,
            std::slice::from_ref(&raw[0]),
        );
        assert_eq!(
            source_contract_marker_indices(&missing_bundle),
            vec![0],
            "one proved-looking recursion row cannot cover two fresh recursive call sites",
        );

        // Same cardinality as the fresh batch, but both supplied rows cover
        // the first call site. This is the exact duplicate/substitution shape
        // that the former nonempty-recursion gate accepted.
        let duplicate = vec![raw[0].clone(), raw[0].clone()];
        let duplicate_bundle =
            function_to_verifier_api_bundle(&function, &compiler_contracts, &duplicate);
        assert_eq!(
            source_contract_marker_indices(&duplicate_bundle),
            vec![0],
            "duplicating one call-site row must not stand in for the other call site",
        );

        // Raw and interval-augmented spellings are alternatives for one fresh
        // semantic row, not two independent call sites. Supplying both shapes
        // of call site 0 must therefore leave call site 1 uncovered.
        let mixed_same_callsite = vec![raw[0].clone(), augmented[0].clone()];
        let mixed_same_callsite_bundle =
            function_to_verifier_api_bundle(&function, &compiler_contracts, &mixed_same_callsite);
        assert_eq!(
            source_contract_marker_indices(&mixed_same_callsite_bundle),
            vec![0],
            "raw and augmented spellings of one call site must not cover a second call site",
        );

        let mut tampered = raw.clone();
        tampered[1].formula = Formula::And(vec![Formula::Bool(false), tampered[1].formula.clone()]);
        let tampered_bundle =
            function_to_verifier_api_bundle(&function, &compiler_contracts, &tampered);
        assert_eq!(
            source_contract_marker_indices(&tampered_bundle),
            vec![0],
            "a third-shape call-site formula must leave the source marker visible",
        );
    }

    #[test]
    fn strengthened_e5_marker_replacement_requires_the_exact_feedback_candidate() {
        let function = feedback_loop_function();
        let compiler_contracts = feedback_loop_contracts(&function);
        let (baseline_raw, _) =
            trust_vcgen::regenerate_loop_contract_production_variants(&function, &[])
                .expect("baseline production variants");
        let initiation =
            baseline_raw.iter().find(|vc| loop_role(vc) == Some("initiation")).expect("initiation");
        let consecution = baseline_raw
            .iter()
            .find(|vc| loop_role(vc) == Some("consecution"))
            .expect("consecution");
        let feedback =
            trust_vcgen::loop_invariant_feedback_candidate(&function, initiation, consecution)
                .expect("exact production E4 pair");
        let (strengthened, _) = trust_vcgen::regenerate_loop_contract_production_variants(
            &function,
            std::slice::from_ref(&feedback),
        )
        .expect("feedback production variants");
        let baseline_e5 =
            baseline_raw.iter().find(|vc| loop_role(vc) == Some("decreases")).expect("baseline E5");
        let strengthened_e5 = strengthened
            .iter()
            .find(|vc| loop_role(vc) == Some("decreases"))
            .expect("strengthened E5");
        assert_ne!(baseline_e5.formula, strengthened_e5.formula);

        let no_candidate =
            function_to_verifier_api_bundle(&function, &compiler_contracts, &strengthened);
        assert_eq!(loop_contract_marker_indices(&no_candidate), vec![1]);

        let structurally_recognized = function_to_verifier_api_bundle_with_loop_feedback_candidates(
            &function,
            &compiler_contracts,
            &strengthened,
            std::slice::from_ref(&feedback),
        );
        assert!(
            loop_contract_marker_indices(&structurally_recognized).is_empty(),
            "{structurally_recognized:#?}"
        );

        let mut forged = strengthened;
        let forged_e5 = forged
            .iter_mut()
            .find(|vc| loop_role(vc) == Some("decreases"))
            .expect("strengthened E5");
        forged_e5.formula = Formula::And(vec![Formula::Bool(false), forged_e5.formula.clone()]);
        let forged_bundle = function_to_verifier_api_bundle_with_loop_feedback_candidates(
            &function,
            &compiler_contracts,
            &forged,
            std::slice::from_ref(&feedback),
        );
        assert_eq!(loop_contract_marker_indices(&forged_bundle), vec![1]);
    }

    #[test]
    fn unsupported_contract_kinds_remain_explicit_obligations() {
        let function = test_function();
        let compiler_contracts = CompilerContractBundle::new(vec![Contract {
            kind: TrustTypesContractKind::Modifies,
            span: SourceSpan::default(),
            body: "x".to_string(),
        }]);

        let bundle = contract_bundle_to_verifier_api(&function, &compiler_contracts);

        assert!(bundle.contracts.is_empty());
        assert_eq!(bundle.obligations.len(), 1);
        assert!(matches!(&bundle.obligations[0].kind, ObligationKind::Custom { .. }));
        assert!(bundle.obligations[0].description.contains("unsupported compiler contract kind"));
    }

    #[test]
    fn native_harness_proof_items_become_trust_mc_full_verify_manifest_obligations() {
        let function = test_function();
        let proof = TrustProofItem {
            name: "reciprocal_contract_harness".to_string(),
            span: function.span.clone(),
            source: TrustProofItemSource::NativeHarness,
            kind: TrustProofItemKind::ContractHarness,
            engine: TrustProofEngineHint::TrustMc,
            mode: TrustProofExecutionMode::BoundedRegression { depth: None },
            target: Some("reciprocal".to_string()),
            body_hash: None,
            diagnostics: vec![],
        };

        let compiler_contracts = CompilerContractBundle::default().with_proof_items(vec![proof]);
        let bundle = contract_bundle_to_verifier_api(&function, &compiler_contracts);

        assert_eq!(bundle.contracts.len(), 0);
        assert_eq!(bundle.obligations.len(), 1);
        let obligation = &bundle.obligations[0];
        assert_eq!(obligation.kind, ObligationKind::Assertion);
        assert_eq!(obligation.required_strength, None);
        assert!(obligation.obligation_id.starts_with("proof-item:demo__f:0:"));
        assert_eq!(obligation.proof_item_id.as_deref(), Some(obligation.obligation_id.as_str()));
        assert!(obligation.summary_facts.is_empty());
        assert!(obligation.description.contains("native_harness contract_harness"));
        assert!(obligation.description.contains("targeting `reciprocal`"));
        assert!(obligation.metadata.iter().any(|entry| {
            entry.key == "trust.proof_item.mode" && entry.value == "bounded_regression"
        }));
        assert!(obligation.metadata.iter().any(|entry| {
            entry.key == "trust.proof_item.target" && entry.value == "reciprocal"
        }));
        assert!(obligation.metadata.iter().any(|entry| {
            entry.key == "trust.proof_item.proof_grade_blocker"
                && entry.value.contains("bounded proof item must execute")
        }));
    }

    fn function_with_requires() -> (VerifiableFunction, CompilerContractBundle) {
        let mut function = test_function();
        let contract = Contract {
            kind: TrustTypesContractKind::Requires,
            span: function.span.clone(),
            body: "true".to_string(),
        };
        function.contracts.push(contract.clone());
        (function, CompilerContractBundle::new(vec![contract]))
    }

    #[test]
    fn only_unique_fresh_source_owned_definition_precondition_is_excluded() {
        let (function, compiler_contracts) = function_with_requires();
        let vcs = trust_vcgen::generate_vcs(&function);
        assert_eq!(vcs.len(), 1, "one authored requires marker");

        let bundle = function_to_verifier_api_bundle(&function, &compiler_contracts, &vcs);

        assert_eq!(
            bundle.obligations.len(),
            1,
            "the source contract remains public while its freshly regenerated bookkeeping VC is excluded",
        );
        assert_eq!(
            metadata_value(
                &bundle.metadata,
                "trust.contract.definition_site_preconditions_excluded",
            ),
            Some("1"),
        );
    }

    #[test]
    fn mirrored_requires_production_shape_has_one_public_source_marker_and_no_generic_vc() {
        let mut function = trust_vc_memory_test_function(Ty::i32());
        let contract = Contract {
            kind: TrustTypesContractKind::Requires,
            span: function.span.clone(),
            body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}x > 0"),
        };
        function.contracts.push(contract.clone());
        function.spec.requires.push("x > 0".to_string());
        function
            .preconditions
            .push(trust_types::parse_spec_expr("x > 0").expect("mirrored precondition parses"));
        let compiler_contracts = CompilerContractBundle::new(vec![contract]);
        let vcs = trust_vcgen::generate_vcs(&function);

        let bundle = function_to_verifier_api_bundle(&function, &compiler_contracts, &vcs);

        assert_eq!(bundle.obligations.len(), 1, "{bundle:#?}");
        assert_eq!(bundle.obligations[0].kind, ObligationKind::Precondition);
        assert!(matches!(
            obligation_context(&bundle.obligations[0]).origin,
            ObligationOrigin::Contract { contract_index: 0, .. }
        ));
        assert_eq!(
            metadata_value(
                &bundle.metadata,
                "trust.contract.definition_site_preconditions_excluded",
            ),
            Some("1"),
        );
        assert!(!bundle.obligations.iter().any(|obligation| {
            obligation.kind == ObligationKind::Precondition
                && matches!(
                    obligation_context(obligation).origin,
                    ObligationOrigin::VerificationCondition { .. }
                )
        }));
    }

    #[test]
    fn self_false_precondition_without_exact_source_identity_remains_visible() {
        let (function, compiler_contracts) = function_with_requires();
        let forged_recursive_row = VerificationCondition {
            kind: VcKind::Precondition { callee: function.name.clone() },
            function: function.name.as_str().into(),
            location: function.span.clone(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };

        let bundle = function_to_verifier_api_bundle(
            &function,
            &compiler_contracts,
            &[forged_recursive_row],
        );

        assert_eq!(bundle.obligations.len(), 2);
        assert_eq!(bundle.obligations[1].kind, ObligationKind::Precondition);
        assert_eq!(
            metadata_value(
                &bundle.metadata,
                "trust.contract.definition_site_preconditions_excluded",
            ),
            None,
        );
    }

    #[test]
    fn duplicate_definition_precondition_rows_fail_closed() {
        let (function, compiler_contracts) = function_with_requires();
        let row = trust_vcgen::generate_vcs(&function)
            .into_iter()
            .next()
            .expect("definition-site marker");

        let bundle =
            function_to_verifier_api_bundle(&function, &compiler_contracts, &[row.clone(), row]);

        assert_eq!(
            bundle.obligations.len(),
            3,
            "ambiguous duplicate rows must both remain visible in addition to the source contract",
        );
        assert_eq!(
            metadata_value(
                &bundle.metadata,
                "trust.contract.definition_site_preconditions_excluded",
            ),
            None,
        );
    }

    // Feature unification may enable serde_json/preserve_order in the compiler
    // while the standalone consumer uses sorted maps. Embedded predicate text
    // is part of the exact public context, so both full and pruned production
    // paths must use the same canonical bytes under either feature graph.
    #[test]
    fn generated_vc_predicate_payloads_are_canonical_across_map_features() {
        let function = test_function();
        let unsupported = Formula::Eq(
            Box::new(Formula::Select(
                Box::new(Formula::Var(
                    "heap".into(),
                    Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
                )),
                Box::new(Formula::BitVec { value: 0, width: 64 }),
            )),
            Box::new(Formula::BitVec { value: 0, width: 8 }),
        );
        let formulas =
            [Formula::Bool(false), Formula::And(vec![unsupported, Formula::Bool(false)])];
        let mut noncanonical_paths = Vec::new();
        for (index, formula) in formulas.into_iter().enumerate() {
            let vc = VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: trust_types::Symbol::intern("demo::f"),
                location: function.span.clone(),
                formula,
                contract_metadata: None,
                obligation: None,
            };
            let bundle = function_to_verifier_api_bundle(
                &function,
                &CompilerContractBundle::default(),
                &[vc],
            );
            let metadata = &bundle.obligations[0].metadata;
            assert_eq!(
                metadata_value(metadata, TRUST_VC_FORMULA_PRUNED_METADATA_KEY),
                (index == 1).then_some("true"),
                "exercise the complete and pruned production paths"
            );
            let payload = metadata_value(metadata, "trust.vc.formula.payload")
                .expect("both production paths must retain a typed predicate");
            let predicate: TrustSpecPredicate = serde_json::from_str(payload).unwrap();
            predicate.validate().unwrap();
            let canonical = trust_types::canonical_json_bytes(&predicate).unwrap();
            if payload.as_bytes() != canonical {
                noncanonical_paths.push(index);
            }
        }
        assert!(
            noncanonical_paths.is_empty(),
            "noncanonical production paths: {noncanonical_paths:?}"
        );
    }

    #[test]
    fn generated_vcs_carry_contract_free_typed_spec_predicate_payloads() {
        let function = test_function();
        let compiler_contracts = CompilerContractBundle::default();
        let vcs = vec![VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: trust_types::Symbol::intern("demo::f"),
            location: function.span.clone(),
            formula: trust_types::Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        }];

        let bundle = function_to_verifier_api_bundle(&function, &compiler_contracts, &vcs);

        assert_eq!(bundle.contracts.len(), 0);
        assert_eq!(bundle.obligations.len(), 1);
        assert_eq!(bundle.obligations[0].kind, ObligationKind::ArithmeticSafety);
        assert_eq!(bundle.obligations[0].required_strength, None);
        assert_eq!(bundle.obligations[0].description, "division by zero");
        assert!(bundle.obligations[0].metadata.iter().all(|entry| {
            entry.key != "trust.vc.formula.debug" && !entry.key.contains("debug")
        }));
        assert_eq!(bundle.obligations[0].contract_id, None);
        assert_eq!(
            metadata_value(&bundle.obligations[0].metadata, "trust.vc.formula.schema"),
            Some(TRUST_SPEC_PREDICATE_SCHEMA_VERSION)
        );
        assert_eq!(
            metadata_value(&bundle.obligations[0].metadata, "trust.vc.formula.sort"),
            Some("Bool")
        );
        assert_eq!(
            metadata_value(&bundle.obligations[0].metadata, "trust.vc.formula.smtlib2"),
            Some("false")
        );
        let payload = metadata_value(&bundle.obligations[0].metadata, "trust.vc.formula.payload")
            .expect("typed spec-predicate payload");
        assert!(payload.contains("\"schema_version\":\"trust.spec-predicate.v1\""));
        assert!(payload.contains("\"root_sort\":\"bool\""));
        assert_eq!(
            metadata_value(
                &bundle.obligations[0].metadata,
                "trust.vc.engine.trust-mc.formula_schema"
            ),
            Some(TRUST_SPEC_PREDICATE_SCHEMA_VERSION)
        );
        assert_eq!(
            metadata_value(&bundle.obligations[0].metadata, TRUST_SOURCE_DIGEST_METADATA_KEY)
                .map(str::len),
            Some(64)
        );
        assert_eq!(
            metadata_value(&bundle.obligations[0].metadata, TRUST_VC_DIGEST_METADATA_KEY)
                .map(str::len),
            Some(64)
        );
        let context = obligation_context(&bundle.obligations[0]);
        assert_eq!(context.producer, ObligationProducer::CompilerMirExtract);
        assert_eq!(
            context.function,
            Some(FunctionContext { crate_name: "demo".to_string(), path: "demo::f".to_string() })
        );
        assert!(matches!(
            context.origin,
            ObligationOrigin::VerificationCondition {
                ref vc_kind,
                vc_index: 0,
                formula_schema: Some(ref schema)
            } if vc_kind == "division_by_zero"
                && schema == TRUST_SPEC_PREDICATE_SCHEMA_VERSION
        ));
    }

    /// Trust (P0 false-proof fix): an `UnboundedAllocation` capacity obligation must
    /// map to the dedicated `trust.vc.unbounded_allocation` Custom kind, NOT
    /// `ArithmeticSafety`. If it were `ArithmeticSafety` the native trust-mc whole-function
    /// CHC proof (which does not model the allocation budget) would false-prove it whenever
    /// a sibling routable arithmetic obligation exists (the `sr_vec_from_elem_*` fuzzer
    /// families). Its ONLY native route is the trust-vc MIR-memory proof-unit lane
    /// (whose predicate is the negated capacity VC itself); the per-VC ay lane still
    /// solves the real `count >= ceiling` obligation on the front line.
    #[test]
    fn unbounded_allocation_vc_is_not_arithmetic_safety() {
        let function = test_function();
        let compiler_contracts = CompilerContractBundle::default();
        let vcs = vec![VerificationCondition {
            kind: VcKind::UnboundedAllocation {
                callee: "vec::from_elem".to_string(),
                count: "n".to_string(),
                detail: "bulk allocation may reach the ceiling".to_string(),
            },
            function: trust_types::Symbol::intern("demo::f"),
            location: function.span.clone(),
            formula: trust_types::Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        }];

        let bundle = function_to_verifier_api_bundle(&function, &compiler_contracts, &vcs);

        assert_eq!(bundle.obligations.len(), 1);
        // Must be the dedicated, non-native-routable Custom namespace — never
        // ArithmeticSafety (which the native CHC route claims via a whole-function proof).
        assert_eq!(
            bundle.obligations[0].kind,
            ObligationKind::Custom {
                namespace: TRUST_VC_UNBOUNDED_ALLOCATION_NAMESPACE.to_string(),
                name: "unbounded_allocation".to_string(),
            }
        );
        assert_ne!(bundle.obligations[0].kind, ObligationKind::ArithmeticSafety);
    }

    /// Trust (#nia-oom, batch 6): the capacity obligation rides the trust-vc
    /// MIR-memory proof-unit transport (the BoundsCheck precedent) — the unit's
    /// predicate is the negated guard-conjoined `count >= ceiling` VC, so the
    /// certificate that discharges it ENCODES the allocation budget. This pins
    /// (a) the proof-unit metadata attach, (b) the stable `custom` obligation-id
    /// label, and (c) that the kind never joins the trust-mc formula set (the
    /// P0 direction).
    #[test]
    fn unbounded_allocation_vc_carries_the_trust_vc_proof_unit() {
        let function = trust_vc_memory_test_function(Ty::usize());
        let compiler_contracts = CompilerContractBundle::default();
        // The exact alloc_vcs.rs shape: violation `count >= CEILING` conjoined
        // with the dominating guard (`count <= 1024`), UNSAT under the guard.
        let formula = trust_types::Formula::And(vec![
            trust_types::Formula::Ge(
                Box::new(trust_types::Formula::var("x", trust_types::Sort::Int)),
                Box::new(trust_types::Formula::Int(1 << 28)),
            ),
            trust_types::Formula::Le(
                Box::new(trust_types::Formula::var("x", trust_types::Sort::Int)),
                Box::new(trust_types::Formula::Int(1024)),
            ),
        ]);
        let vcs = vec![VerificationCondition {
            kind: VcKind::UnboundedAllocation {
                callee: "Vec::with_capacity".to_string(),
                count: "x".to_string(),
                detail: "bulk allocation may reach the ceiling".to_string(),
            },
            function: trust_types::Symbol::intern("demo::f"),
            location: function.span.clone(),
            formula,
            contract_metadata: None,
            obligation: None,
        }];

        let bundle = function_to_verifier_api_bundle(&function, &compiler_contracts, &vcs);
        let obligation = &bundle.obligations[0];

        // (b) The obligation id keeps the pre-existing `custom` label — the
        // proof-unit payload binds by this exact id.
        assert_eq!(obligation.obligation_id, "vc:demo__f:custom:0");
        // (a) The full trust-vc MIR-memory proof-unit metadata set, exactly as
        // for BoundsCheck.
        assert_eq!(
            metadata_value(&obligation.metadata, TRUST_VC_CONDITION_ORIGIN_METADATA_KEY),
            Some(TRUST_VC_CONDITION_ORIGIN_METADATA_VALUE)
        );
        assert_eq!(
            metadata_value(&obligation.metadata, TRUST_VC_PROOF_OBLIGATION_METADATA_KEY),
            Some(TRUST_VC_PROOF_OBLIGATION_METADATA_VALUE)
        );
        assert_eq!(
            metadata_value(&obligation.metadata, TRUST_VC_OWNERSHIP_CONTEXT_METADATA_KEY),
            Some(TRUST_VC_OWNERSHIP_CONTEXT_METADATA_VALUE)
        );
        assert_eq!(
            metadata_value(
                &obligation.metadata,
                TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_METADATA_KEY
            ),
            Some(TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_VERSION)
        );
        let raw_payload =
            metadata_value(&obligation.metadata, TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY)
                .expect("the capacity obligation must carry the structured proof unit");
        let payload: serde_json::Value =
            serde_json::from_str(raw_payload).expect("proof unit parses");
        assert_eq!(payload["obligations"][0]["id"], "vc:demo__f:custom:0");
        // (c) NEVER a trust-mc formula obligation — the CHC proof does not
        // encode the capacity budget (the recorded P0).
        assert!(!trust_mc_formula_obligation(&obligation.kind, &vcs[0].kind));
        assert!(trust_vc_formula_obligation(&obligation.kind));
    }

    #[test]
    fn content_digests_are_emitted_and_track_predicate_and_vc_content() {
        let function = test_function();
        let requires_true = CompilerContractBundle::new(vec![Contract {
            kind: TrustTypesContractKind::Requires,
            span: function.span.clone(),
            body: "true".to_string(),
        }]);
        let requires_false = CompilerContractBundle::new(vec![Contract {
            kind: TrustTypesContractKind::Requires,
            span: function.span.clone(),
            body: "false".to_string(),
        }]);

        let true_bundle = contract_bundle_to_verifier_api(&function, &requires_true);
        let false_bundle = contract_bundle_to_verifier_api(&function, &requires_false);
        let true_digest = metadata_value(
            &true_bundle.contracts[0].metadata,
            TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY,
        )
        .expect("predicate digest");
        let false_digest = metadata_value(
            &false_bundle.contracts[0].metadata,
            TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY,
        )
        .expect("predicate digest");
        assert_eq!(true_digest.len(), 64);
        assert_eq!(false_digest.len(), 64);
        assert_ne!(true_digest, false_digest);

        let vc_true = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: trust_types::Symbol::intern("demo::f"),
            location: function.span.clone(),
            formula: trust_types::Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        };
        let vc_false =
            VerificationCondition { formula: trust_types::Formula::Bool(false), ..vc_true.clone() };
        let true_vc_bundle = function_to_verifier_api_bundle(
            &function,
            &CompilerContractBundle::default(),
            &[vc_true],
        );
        let false_vc_bundle = function_to_verifier_api_bundle(
            &function,
            &CompilerContractBundle::default(),
            &[vc_false],
        );
        let true_vc_digest =
            metadata_value(&true_vc_bundle.obligations[0].metadata, TRUST_VC_DIGEST_METADATA_KEY)
                .expect("VC digest");
        let false_vc_digest =
            metadata_value(&false_vc_bundle.obligations[0].metadata, TRUST_VC_DIGEST_METADATA_KEY)
                .expect("VC digest");
        assert_eq!(true_vc_digest.len(), 64);
        assert_eq!(false_vc_digest.len(), 64);
        assert_ne!(true_vc_digest, false_vc_digest);
    }

    #[test]
    fn generated_hardened_vcs_keep_first_class_kind_and_category_tag() {
        let function = test_function();
        let compiler_contracts = CompilerContractBundle::default();
        let vcs = vec![VerificationCondition {
            kind: VcKind::HardenedBoundary {
                category: trust_types::HardenedVcCategory::PanicBoundary,
                callee: "Option::unwrap".to_string(),
                detail: "success must be proven before unwrap".to_string(),
            },
            function: trust_types::Symbol::intern("demo::f"),
            location: function.span.clone(),
            formula: trust_types::Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        }];

        let bundle = function_to_verifier_api_bundle(&function, &compiler_contracts, &vcs);
        let obligation = &bundle.obligations[0];

        assert_eq!(
            obligation.kind,
            ObligationKind::Custom {
                namespace: TRUST_VC_HARDENED_NAMESPACE.to_string(),
                name: "panic_boundary".to_string(),
            }
        );
        assert!(obligation.obligation_id.contains(":panic_boundary:0"));
        assert_eq!(
            metadata_value(&obligation.metadata, "trust.vc.kind"),
            Some("hardened_panic_boundary")
        );
        assert_eq!(
            metadata_value(&obligation.metadata, TRUST_VC_HARDENED_CATEGORY_METADATA_KEY),
            Some("panic_boundary")
        );
        assert_eq!(
            metadata_value(&obligation.metadata, TRUST_VC_HARDENED_FAMILY_METADATA_KEY),
            Some("hardened_panic_boundary")
        );
        assert_eq!(
            metadata_value(&obligation.metadata, TRUST_VC_HARDENED_CALLEE_METADATA_KEY),
            Some("Option::unwrap")
        );
        assert_eq!(
            metadata_value(&obligation.metadata, TRUST_VC_HARDENED_DETAIL_METADATA_KEY),
            Some("success must be proven before unwrap")
        );
        let context = obligation_context(obligation);
        assert!(matches!(
            context.origin,
            ObligationOrigin::VerificationCondition {
                ref vc_kind,
                vc_index: 0,
                ..
            } if vc_kind == "hardened_panic_boundary"
        ));
    }

    #[test]
    fn generated_unknown_hardened_vcs_preserve_future_category_tag() {
        let function = test_function();
        let compiler_contracts = CompilerContractBundle::default();
        let vcs = vec![VerificationCondition {
            kind: VcKind::HardenedBoundary {
                category: trust_types::HardenedVcCategory::unknown_tag(
                    "future_kernel_object_identity",
                ),
                callee: "openat2".to_string(),
                detail: "future hardened category should stay fail-closed".to_string(),
            },
            function: trust_types::Symbol::intern("demo::f"),
            location: function.span.clone(),
            formula: trust_types::Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        }];

        let bundle = function_to_verifier_api_bundle(&function, &compiler_contracts, &vcs);
        let obligation = &bundle.obligations[0];

        assert_eq!(
            obligation.kind,
            ObligationKind::Custom {
                namespace: TRUST_VC_HARDENED_NAMESPACE.to_string(),
                name: "future_kernel_object_identity".to_string(),
            }
        );
        assert!(obligation.obligation_id.contains(":future_kernel_object_identity:0"));
        assert_eq!(
            metadata_value(&obligation.metadata, "trust.vc.kind"),
            Some("hardened_future_kernel_object_identity")
        );
        assert_eq!(
            metadata_value(&obligation.metadata, TRUST_VC_HARDENED_CATEGORY_METADATA_KEY),
            Some("future_kernel_object_identity")
        );
        assert_eq!(
            metadata_value(&obligation.metadata, TRUST_VC_HARDENED_FAMILY_METADATA_KEY),
            Some("hardened_future_kernel_object_identity")
        );
    }

    #[test]
    fn generated_native_unsafe_and_ffi_vcs_keep_hardened_category_tags() {
        let function = test_function();
        let compiler_contracts = CompilerContractBundle::default();
        let vcs = vec![
            VerificationCondition {
                kind: VcKind::UnsafeOperation { desc: "raw pointer deref".to_string() },
                function: trust_types::Symbol::intern("demo::f"),
                location: function.span.clone(),
                formula: trust_types::Formula::Bool(true),
                contract_metadata: None,
                obligation: None,
            },
            VerificationCondition {
                kind: VcKind::FfiBoundaryViolation {
                    callee: "strlen".to_string(),
                    desc: "trusted wrapper contract required".to_string(),
                },
                function: trust_types::Symbol::intern("demo::f"),
                location: function.span.clone(),
                formula: trust_types::Formula::Bool(true),
                contract_metadata: None,
                obligation: None,
            },
        ];

        let bundle = function_to_verifier_api_bundle(&function, &compiler_contracts, &vcs);
        let unsafe_obligation = &bundle.obligations[0];
        let ffi_obligation = &bundle.obligations[1];

        assert_eq!(
            unsafe_obligation.kind,
            ObligationKind::Custom {
                namespace: TRUST_VC_HARDENED_NAMESPACE.to_string(),
                name: "unsafe_operation".to_string(),
            }
        );
        assert_eq!(
            metadata_value(&unsafe_obligation.metadata, TRUST_VC_HARDENED_CALLEE_METADATA_KEY),
            Some("unsafe_operation")
        );
        assert_eq!(
            metadata_value(&unsafe_obligation.metadata, TRUST_VC_HARDENED_DETAIL_METADATA_KEY),
            Some("raw pointer deref")
        );
        assert_eq!(
            ffi_obligation.kind,
            ObligationKind::Custom {
                namespace: TRUST_VC_HARDENED_NAMESPACE.to_string(),
                name: "ffi_boundary".to_string(),
            }
        );
        assert_eq!(
            metadata_value(&ffi_obligation.metadata, TRUST_VC_HARDENED_CALLEE_METADATA_KEY),
            Some("strlen")
        );
        assert_eq!(
            metadata_value(&ffi_obligation.metadata, TRUST_VC_HARDENED_DETAIL_METADATA_KEY),
            Some("trusted wrapper contract required")
        );
        assert_eq!(
            metadata_value(&ffi_obligation.metadata, "trust.vc.engine.trust-mc.formula_schema"),
            Some(TRUST_SPEC_PREDICATE_SCHEMA_VERSION)
        );
    }

    #[test]
    fn generated_vcs_fall_back_to_symbolic_formula_schema_for_non_spec_payloads() {
        let function = test_function();
        let compiler_contracts = CompilerContractBundle::default();
        let vcs = vec![VerificationCondition {
            kind: VcKind::UseAfterFree,
            function: trust_types::Symbol::intern("demo::f"),
            location: function.span.clone(),
            formula: trust_types::Formula::Eq(
                Box::new(trust_types::Formula::Select(
                    Box::new(trust_types::Formula::Var(
                        "heap".to_string(),
                        trust_types::Sort::Array(
                            Box::new(trust_types::Sort::BitVec(64)),
                            Box::new(trust_types::Sort::BitVec(8)),
                        ),
                    )),
                    Box::new(trust_types::Formula::BitVec { value: 0, width: 64 }),
                )),
                Box::new(trust_types::Formula::BitVec { value: 0, width: 8 }),
            ),
            contract_metadata: None,
            obligation: None,
        }];

        let bundle = function_to_verifier_api_bundle(&function, &compiler_contracts, &vcs);
        let obligation = &bundle.obligations[0];

        assert_eq!(obligation.contract_id, None);
        assert_eq!(obligation.kind, ObligationKind::MemorySafety);
        assert_eq!(
            metadata_value(&obligation.metadata, "trust.vc.formula.schema"),
            Some(TRUST_SYMBOLIC_FORMULA_SCHEMA)
        );
        assert_eq!(metadata_value(&obligation.metadata, "trust.vc.formula.sort"), Some("Bool"));
        assert_eq!(
            metadata_value(&obligation.metadata, "trust.vc.formula.smtlib2"),
            Some("(= (select heap (_ bv0 64)) (_ bv0 8))")
        );
        assert_eq!(metadata_value(&obligation.metadata, "trust.vc.formula.payload"), None);
        assert_eq!(
            metadata_value(&obligation.metadata, "trust.vc.engine.trust-vc.formula_schema"),
            Some(TRUST_SYMBOLIC_FORMULA_SCHEMA)
        );
        let context = obligation_context(obligation);
        assert!(matches!(
            context.origin,
            ObligationOrigin::VerificationCondition {
                vc_index: 0,
                formula_schema: Some(ref schema),
                ..
            } if schema == TRUST_SYMBOLIC_FORMULA_SCHEMA
        ));
    }

    #[test]
    fn public_typed_predicate_preserves_int_indexed_array_select() {
        let array_sort = Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int));
        let formula = Formula::Eq(
            Box::new(Formula::Select(
                Box::new(Formula::Var("xs".to_string(), array_sort)),
                Box::new(Formula::Int(0)),
            )),
            Box::new(Formula::Var("first".to_string(), Sort::Int)),
        );
        let predicate = trust_spec_predicate_from_formula(&formula)
            .expect("Int-indexed scalar Select lowers to exact public schema");
        predicate.validate().expect("producer output passes the complete public validator");

        assert!(predicate.variables.iter().any(|variable| {
            variable.name == "xs"
                && variable.sort == TrustSpecSort::Array { element: TrustSpecScalarSort::Int }
        }));
        let TrustSpecExprKind::Binary { lhs, .. } = &predicate.root.kind else {
            panic!("array equality predicate must retain its binary root");
        };
        assert!(matches!(
            &lhs.kind,
            TrustSpecExprKind::Index { base, index }
                if matches!(&base.kind, TrustSpecExprKind::Variable { name } if name == "xs")
                    && matches!(&index.kind, TrustSpecExprKind::IntLiteral { value } if value == "0")
        ));
    }

    #[test]
    fn exact_array_read_after_write_gets_a_typed_loop_vc_payload() {
        let array_sort = Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int));
        let formula = Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::Select(
                Box::new(Formula::Store(
                    Box::new(Formula::Var("xs".to_string(), array_sort)),
                    Box::new(Formula::Int(0)),
                    Box::new(Formula::Int(7)),
                )),
                Box::new(Formula::Int(0)),
            )),
            Box::new(Formula::Int(7)),
        )));

        let payload = vc_formula_payload(
            &VcKind::LoopInvariantInitiation {
                invariant: "xs[0] == 7".to_string(),
                header_block: 1,
            },
            &formula,
        );

        let expected = Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::Int(7)),
            Box::new(Formula::Int(7)),
        )));
        assert_eq!(payload.selected_formula.as_ref(), Some(&expected));
        assert!(payload.typed_payload.is_some());
        assert!(!payload.pruned);
        assert!(!payload.smtlib.contains("store"));
    }

    /// Build a lowerable path-disjunction whose serialized typed payload is
    /// larger than the verifier-API transport ceiling while its SMT-LIB
    /// rendering stays well under it — the exact ratio a3d's whole-function
    /// `Unreachable` VC has (992,747 bytes of JSON payload against 71,154
    /// bytes of SMT-LIB). Balanced rather than left-deep so neither the
    /// lowering nor `serde_json` recurses 8k frames on a test thread.
    fn oversized_lowerable_violation() -> Formula {
        // Distinct literals keep the disjuncts distinct; the variable pool stays
        // small because `validate_trust_spec_predicate` caps declared variables
        // at `MAX_RECORD_METADATA_ENTRIES` and a predicate over that cap would
        // decline for the wrong reason.
        let mut level: Vec<Formula> = (0..16_384i128)
            .map(|index| {
                Formula::Eq(
                    Box::new(Formula::Var(format!("v{}", index % 64), Sort::Int)),
                    Box::new(Formula::Int(index)),
                )
            })
            .collect();
        while level.len() > 1 {
            level = level
                .chunks(2)
                .map(|pair| match pair {
                    [single] => single.clone(),
                    pair => Formula::Or(pair.to_vec()),
                })
                .collect();
        }
        level.pop().expect("non-empty disjunction")
    }

    #[test]
    fn oversized_typed_payload_is_dropped_instead_of_invalidating_the_bundle() {
        let formula = oversized_lowerable_violation();
        assert!(
            trust_spec_predicate_from_formula(&formula).is_some(),
            "the fixture must lower; otherwise the test would pass for the wrong reason"
        );

        let payload = vc_formula_payload(&VcKind::Unreachable, &formula);

        // The row survives with its schema/sort/smtlib carrier...
        assert_eq!(payload.schema, TRUST_SYMBOLIC_FORMULA_SCHEMA);
        assert_eq!(payload.sort, "Bool");
        assert!(!payload.smtlib.is_empty());
        // ...and drops only the oversized typed payload, so
        // `TrustContractBundle::validate` cannot reject the whole bundle (and
        // with it every other obligation of the function).
        assert_eq!(payload.typed_payload, None);
        assert_eq!(payload.selected_formula, None);
        assert!(!payload.pruned);
        for entry in payload.into_metadata() {
            assert!(
                entry.value.len() <= MAX_TRANSPORT_METADATA_VALUE_BYTES,
                "metadata value for `{}` still exceeds the transport ceiling",
                entry.key
            );
        }
    }

    /// G3 (2026-10-27): the shape agy-alab's `days_from_civil` reached the lowering
    /// in. One disjunct per path into a join, each repeating the facts every path
    /// shares, so the typed payload outgrew the transport ceiling only by
    /// repetition.
    fn join_disjunction_sharing_path_facts(paths: i128, shared_facts: i128) -> Formula {
        let shared = (0..shared_facts)
            .map(|index| {
                Formula::Le(
                    Box::new(Formula::Var(format!("c{}", index % 48), Sort::Int)),
                    Box::new(Formula::Int(index)),
                )
            })
            .collect::<Vec<_>>();
        Formula::Or(
            (0..paths)
                .map(|path| {
                    let mut conjuncts = shared.clone();
                    conjuncts.push(Formula::Eq(
                        Box::new(Formula::Var("m".to_string(), Sort::Int)),
                        Box::new(Formula::Int(path)),
                    ));
                    Formula::And(conjuncts)
                })
                .collect(),
        )
    }

    #[test]
    fn shared_join_facts_are_factored_to_keep_an_oversized_typed_payload() {
        let formula = join_disjunction_sharing_path_facts(8, 1_500);
        // Positive control: unfactored, this row loses its typed payload to the ceiling.
        let unfactored =
            vc_formula_payload_unfactored(&VcKind::Unreachable, &formula, &mut || true);
        assert_eq!(unfactored.typed_payload, None);
        assert!(
            unfactored
                .typed_payload_dropped_bytes
                .is_some_and(|bytes| bytes > MAX_TRANSPORT_METADATA_VALUE_BYTES),
            "the fixture must exceed the ceiling, or the test passes for the wrong reason"
        );

        let payload = vc_formula_payload(&VcKind::Unreachable, &formula);
        assert!(payload.typed_payload.is_some(), "factoring restores the typed carrier");
        assert_ne!(payload.schema, TRUST_SYMBOLIC_FORMULA_SCHEMA);
        assert!(!payload.pruned, "factoring is an equivalence, not a weakening");
        let Formula::Or(paths) = &formula else { unreachable!() };
        let Formula::And(first) = &paths[0] else { unreachable!() };
        let mut expected = first[..first.len() - 1].to_vec();
        expected.push(Formula::Or(
            paths
                .iter()
                .map(|path| match path {
                    Formula::And(conjuncts) => conjuncts.last().cloned().expect("residue"),
                    other => other.clone(),
                })
                .collect(),
        ));
        assert_eq!(payload.selected_formula, Some(Formula::And(expected)));
        assert_eq!(
            payload.exact_selected_typed_formula().expect("factored proof-unit binding"),
            payload.selected_formula.as_ref().unwrap(),
            "the restored carrier must bind the same selected formula before proof-unit construction"
        );
        for entry in payload.into_metadata() {
            assert!(entry.value.len() <= MAX_TRANSPORT_METADATA_VALUE_BYTES, "{}", entry.key);
        }
    }

    /// Negative control: a row that already fits keeps its payload byte-identical
    /// (no factoring), even when its disjuncts share conjuncts.
    #[test]
    fn a_row_within_the_ceiling_is_not_refactored() {
        let formula = join_disjunction_sharing_path_facts(3, 4);
        let payload = vc_formula_payload(&VcKind::Unreachable, &formula);
        assert_eq!(payload.selected_formula.as_ref(), Some(&formula));
        let unfactored =
            vc_formula_payload_unfactored(&VcKind::Unreachable, &formula, &mut || true);
        assert_eq!(payload.typed_payload, unfactored.typed_payload);
        assert_eq!(payload.smtlib, unfactored.smtlib);
    }

    fn eval_bool(formula: &Formula, env: u32) -> bool {
        match formula {
            Formula::Bool(value) => *value,
            Formula::Var(name, Sort::Bool) => {
                env & (1 << name.trim_start_matches('b').parse::<u32>().expect("bN")) != 0
            }
            Formula::Not(inner) => !eval_bool(inner, env),
            Formula::And(conjuncts) => conjuncts.iter().all(|c| eval_bool(c, env)),
            Formula::Or(disjuncts) => disjuncts.iter().any(|d| eval_bool(d, env)),
            other => panic!("unexpected node {other:?}"),
        }
    }

    /// Factoring is an equivalence: on every assignment of 5 boolean variables, the
    /// factored formula evaluates as the original, over a deterministic family of
    /// nested `And`/`Or`/`Not` formulas built to share conjuncts (including the
    /// `C ∨ (C ∧ R)` collapse, repeated conjuncts, and single-disjunct `Or`s).
    #[test]
    fn factoring_shared_disjunct_conjuncts_preserves_every_assignment() {
        let mut seed: u64 = 0x9e37_79b9_7f4a_7c15;
        let mut next = move |bound: u64| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed % bound
        };
        fn atom(index: u64) -> Formula {
            Formula::Var(format!("b{index}"), Sort::Bool)
        }
        let mut changed = 0;
        for _ in 0..2_000 {
            let pool = (0..3)
                .map(|_| match next(3) {
                    0 => atom(next(5)),
                    1 => Formula::Not(Box::new(atom(next(5)))),
                    _ => Formula::And(vec![atom(next(5)), atom(next(5))]),
                })
                .collect::<Vec<_>>();
            let disjuncts = (0..1 + next(4))
                .map(|_| {
                    let mut conjuncts = (0..next(4))
                        .map(|_| pool[usize::try_from(next(3)).expect("index")].clone())
                        .collect::<Vec<_>>();
                    if next(2) == 0 {
                        conjuncts.push(atom(next(5)));
                    }
                    match conjuncts.len() {
                        0 => pool[0].clone(),
                        1 => conjuncts.pop().expect("one"),
                        _ => Formula::And(conjuncts),
                    }
                })
                .collect::<Vec<_>>();
            let inner = Formula::Or(disjuncts);
            let formula = match next(3) {
                0 => inner,
                1 => Formula::Not(Box::new(inner)),
                _ => Formula::And(vec![atom(next(5)), inner]),
            };
            let factored = factor_shared_disjunct_conjuncts(&formula);
            if factored != formula {
                changed += 1;
            }
            for env in 0..32 {
                assert_eq!(
                    eval_bool(&factored, env),
                    eval_bool(&formula, env),
                    "{formula:?} vs {factored:?} at {env:#b}"
                );
            }
        }
        assert!(changed > 100, "the family must exercise the rewrite ({changed} changed)");
    }

    #[test]
    fn factoring_collapses_a_disjunct_that_is_only_the_shared_facts() {
        let c = Formula::Var("b0".to_string(), Sort::Bool);
        let r = Formula::Var("b1".to_string(), Sort::Bool);
        let formula = Formula::Or(vec![Formula::And(vec![c.clone(), r]), c.clone()]);
        assert_eq!(factor_shared_disjunct_conjuncts(&formula), Formula::And(vec![c]));
        let disjoint = Formula::Or(vec![
            Formula::Var("b2".to_string(), Sort::Bool),
            Formula::Var("b3".to_string(), Sort::Bool),
        ]);
        assert_eq!(factor_shared_disjunct_conjuncts(&disjoint), disjoint);
    }

    #[test]
    fn a_typed_payload_under_the_transport_ceiling_is_still_emitted() {
        let formula = Formula::Eq(
            Box::new(Formula::Var("v0".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let payload = vc_formula_payload(&VcKind::Unreachable, &formula);
        assert!(payload.typed_payload.is_some());
        assert_eq!(payload.selected_formula.as_ref(), Some(&formula));
    }

    /// A violation whose SMT-LIB rendering ALONE exceeds the transport ceiling
    /// (T4: trust-ir-conformance `refuse_template_fixtures::artifacts`, one VC
    /// rendering 1,131,451 bytes). Balanced, as above, so nothing recurses deeply.
    fn oversized_smtlib_violation() -> Formula {
        let mut level: Vec<Formula> = (0..131_072i128)
            .map(|index| {
                Formula::Eq(
                    Box::new(Formula::Var(format!("v{}", index % 64), Sort::Int)),
                    Box::new(Formula::Int(index)),
                )
            })
            .collect();
        while level.len() > 1 {
            level = level
                .chunks(2)
                .map(|pair| match pair {
                    [single] => single.clone(),
                    pair => Formula::Or(pair.to_vec()),
                })
                .collect();
        }
        let formula = level.pop().expect("non-empty disjunction");
        assert!(
            formula.to_smtlib().len() > MAX_TRANSPORT_METADATA_VALUE_BYTES,
            "the fixture must exceed the ceiling on its SMT-LIB rendering alone"
        );
        formula
    }

    #[test]
    fn oversized_smtlib_is_replaced_by_a_bounded_marker_and_no_formula_is_offered() {
        let formula = oversized_smtlib_violation();
        let smtlib = formula.to_smtlib();

        let payload = vc_formula_payload(&VcKind::Unreachable, &formula);

        // No transport engine can read a formula off this row: the rendering is
        // replaced by a marker no SMT-LIB parser accepts, and no typed payload
        // (which would be a proof carrier) is offered either.
        assert!(payload.smtlib.starts_with(TRUST_VC_FORMULA_SMTLIB_OMITTED_PREFIX));
        assert_ne!(payload.smtlib, "false", "never the default-admission row's reserved value");
        assert!(payload.smtlib.contains(&stable_sha256_hex(smtlib.as_bytes())));
        assert_eq!(payload.schema, TRUST_SYMBOLIC_FORMULA_SCHEMA);
        assert_eq!(payload.sort, "Bool");
        assert_eq!(payload.typed_payload, None);
        assert_eq!(payload.selected_formula, None);
        assert!(!payload.pruned);
        assert_eq!(payload.smtlib_omitted_bytes, Some(smtlib.len()));
        let metadata = payload.into_metadata();
        assert_eq!(
            metadata_value(&metadata, TRUST_VC_FORMULA_SMTLIB_OMITTED_METADATA_KEY),
            Some(smtlib.len().to_string().as_str()),
            "the omission is recorded, not silent"
        );
        assert_eq!(metadata_value(&metadata, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY), None);
        for entry in metadata {
            assert!(
                entry.value.len() <= MAX_TRANSPORT_METADATA_VALUE_BYTES,
                "metadata value for `{}` still exceeds the transport ceiling",
                entry.key
            );
        }
    }

    /// T4 regression: one oversized SMT-LIB rendering used to make
    /// `TrustContractBundle::validate` reject the WHOLE bundle, which discards the
    /// function's native bundle and drives every row, the ordinary overflow row
    /// beside it included, through `fresh-vc-rekey-integrity` to `unknown` (and
    /// the Level-0 safety rows on to `failed`). The bundle must now validate, the
    /// sibling row must keep its typed carrier, and the identity the compiler
    /// re-derives for the rekey must match the published row exactly.
    #[test]
    fn oversized_smtlib_row_leaves_the_bundle_valid_and_its_siblings_typed() {
        let function = test_function();
        let compiler_contracts = CompilerContractBundle::default();
        let huge = VerificationCondition {
            kind: VcKind::Unreachable,
            function: trust_types::Symbol::intern("demo::f"),
            location: function.span.clone(),
            formula: oversized_smtlib_violation(),
            contract_metadata: None,
            obligation: None,
        };
        let small = VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: trust_types::BinOp::Sub,
                operand_tys: (
                    Ty::Int { width: 32, signed: false },
                    Ty::Int { width: 32, signed: false },
                ),
            },
            function: trust_types::Symbol::intern("demo::f"),
            location: function.span.clone(),
            formula: Formula::Lt(
                Box::new(Formula::Var("a".to_string(), Sort::Int)),
                Box::new(Formula::Int(1)),
            ),
            contract_metadata: None,
            obligation: None,
        };
        let vcs = vec![huge.clone(), small.clone()];

        let bundle = function_to_verifier_api_bundle(&function, &compiler_contracts, &vcs);

        bundle.validate().expect("one oversized rendering must not invalidate the bundle");
        let huge_row = bundle
            .obligations
            .iter()
            .find(|obligation| {
                metadata_value(&obligation.metadata, TRUST_VC_FORMULA_SMTLIB_OMITTED_METADATA_KEY)
                    .is_some()
            })
            .expect("the oversized row is published, with its omission recorded");
        assert_eq!(metadata_value(&huge_row.metadata, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY), None);
        let huge_identity = verifier_vc_content_identity(&function, 0, &huge);
        assert_eq!(
            metadata_value(&huge_row.metadata, "trust.vc.formula.smtlib2"),
            Some(huge_identity.formula_smtlib.as_str()),
            "the rekey's identity re-derivation must agree with the published carrier"
        );
        assert_eq!(
            metadata_value(&huge_row.metadata, TRUST_VC_DIGEST_METADATA_KEY),
            Some(huge_identity.digest.as_str()),
        );
        assert!(
            bundle.obligations.iter().any(|obligation| {
                metadata_value(&obligation.metadata, "trust.vc.formula.smtlib2")
                    == Some(small.formula.to_smtlib().as_str())
                    && metadata_value(&obligation.metadata, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
                        .is_some()
            }),
            "the sibling overflow row keeps its exact rendering and typed carrier"
        );
    }

    fn memory_transport_case() -> (VerifiableFunction, VerificationCondition) {
        let function = trust_vc_memory_test_function(Ty::Int { width: 32, signed: true });
        let vc = VerificationCondition {
            kind: VcKind::AliasingViolation { mutable: true },
            function: trust_types::Symbol::intern("demo::f"),
            location: function.span.clone(),
            formula: Formula::Lt(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
            obligation: None,
        };
        (function, vc)
    }

    fn memory_unit_bytes(function: &VerifiableFunction, vc: &VerificationCondition) -> usize {
        let formula = vc_formula_payload_for(function, &vc.kind, &vc.formula);
        let memory =
            trust_vc_mir_memory_metadata(function, vc, 0, &ObligationKind::Ownership, &formula);
        metadata_value(&memory, TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY)
            .expect("fixture must produce the real typed proof unit")
            .len()
    }

    #[test]
    fn oversized_memory_unit_preserves_rows_sibling_carriers_and_exact_identity() {
        let (mut function, vc) = memory_transport_case();
        for index in 0..300 {
            function.body.locals.push(LocalDecl {
                index: index + 2,
                ty: Ty::Int { width: 32, signed: true },
                name: Some(format!("unused_{index}_{}", "a".repeat(4096))),
            });
        }
        let formula = vc_formula_payload_for(&function, &vc.kind, &vc.formula);
        assert!(formula.smtlib.len() < MAX_TRANSPORT_METADATA_VALUE_BYTES);
        assert!(formula.typed_payload.as_ref().unwrap().len() < MAX_TRANSPORT_METADATA_VALUE_BYTES);
        assert!(memory_unit_bytes(&function, &vc) > MAX_TRANSPORT_METADATA_VALUE_BYTES);
        let mut sibling = vc.clone();
        sibling.kind = VcKind::ArithmeticOverflow {
            op: trust_types::BinOp::Add,
            operand_tys: (Ty::Int { width: 32, signed: true }, Ty::Int { width: 32, signed: true }),
        };
        let bundle = function_to_verifier_api_bundle(
            &function,
            &CompilerContractBundle::default(),
            &[vc.clone(), sibling.clone()],
        );
        bundle.validate().expect("the oversized memory unit cannot poison its sibling");
        assert_eq!(bundle.obligations.len(), 2);
        let row = &bundle.obligations[0];
        assert_eq!(row.kind, ObligationKind::Ownership);
        assert_eq!(row.source, source_location(&vc.location));
        assert_eq!(row.required_strength, trust_vc_mir_memory_required_strength(&row.kind));
        assert_eq!(metadata_value(&row.metadata, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY), None);
        for key in [
            TRUST_VC_CONDITION_ORIGIN_METADATA_KEY,
            TRUST_VC_PROOF_OBLIGATION_METADATA_KEY,
            TRUST_VC_OWNERSHIP_CONTEXT_METADATA_KEY,
            TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_METADATA_KEY,
            TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY,
        ] {
            assert_eq!(metadata_value(&row.metadata, key), None, "retained {key}");
        }
        let identity = verifier_vc_content_identity(&function, 0, &vc);
        assert_eq!(row.obligation_id, identity.obligation_id);
        assert_eq!(
            metadata_value(&row.metadata, TRUST_VC_DIGEST_METADATA_KEY),
            Some(identity.digest.as_str())
        );
        assert_eq!(
            metadata_value(&row.metadata, TRUST_SOURCE_DIGEST_METADATA_KEY),
            Some(identity.source_digest.as_str())
        );
        assert!(identity.formula_smtlib.starts_with("trust-omitted-mir-memory-proof-unit:"));
        assert_eq!(
            metadata_value(&row.metadata, "trust.vc.formula.smtlib2"),
            Some(identity.formula_smtlib.as_str())
        );
        assert_eq!(identity.formula_payload, None);
        for entry in &identity.mir_memory_metadata {
            assert_eq!(metadata_value(&row.metadata, &entry.key), Some(entry.value.as_str()));
        }
        let expected_sibling = vc_formula_payload_for(&function, &sibling.kind, &sibling.formula);
        assert_eq!(
            metadata_value(&bundle.obligations[1].metadata, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY),
            expected_sibling.typed_payload.as_deref()
        );
        assert!(expected_sibling.typed_payload.is_some());

        let mut malformed = bundle.clone();
        malformed.obligations[0].metadata.push(MetadataEntry {
            key: "unknown.semantic.value".to_string(),
            value: "x".repeat(MAX_TRANSPORT_METADATA_VALUE_BYTES + 1),
        });
        assert!(malformed.validate().is_err(), "unrelated invalid metadata must still fail");
        malformed = bundle.clone();
        malformed.obligations.push(bundle.obligations[0].clone());
        assert!(malformed.validate().is_err(), "duplicate obligation IDs must still fail");
    }

    #[test]
    fn memory_transport_accepts_the_actual_byte_limit_and_omits_only_above_it() {
        for size in [MAX_TRANSPORT_METADATA_VALUE_BYTES, MAX_TRANSPORT_METADATA_VALUE_BYTES + 1] {
            let (mut function, vc) = memory_transport_case();
            function.body.locals.push(LocalDecl {
                index: 2,
                ty: Ty::Int { width: 32, signed: true },
                name: Some("padding".to_string()),
            });
            let initial = memory_unit_bytes(&function, &vc);
            function
                .body
                .locals
                .last_mut()
                .unwrap()
                .name
                .as_mut()
                .unwrap()
                .push_str(&"a".repeat(size - initial));
            assert_eq!(memory_unit_bytes(&function, &vc), size);
            let original = vc_formula_payload_for(&function, &vc.kind, &vc.formula);
            let original_memory = trust_vc_mir_memory_metadata(
                &function,
                &vc,
                0,
                &ObligationKind::Ownership,
                &original,
            );
            let (actual, actual_memory) =
                vc_transport_for(&function, &vc, 0, &ObligationKind::Ownership);
            if size == MAX_TRANSPORT_METADATA_VALUE_BYTES {
                assert_eq!(actual.into_metadata(), original.into_metadata());
                assert_eq!(actual_memory, original_memory);
            } else {
                assert!(actual.typed_payload.is_none());
                assert!(actual.selected_formula.is_none());
                assert_eq!(actual_memory.len(), 1);
                assert_eq!(
                    actual_memory[0].key,
                    TRUST_VC_MIR_MEMORY_PROOF_UNIT_UNSUPPORTED_METADATA_KEY
                );
                assert!(actual_memory[0].value.len() < MAX_TRANSPORT_METADATA_VALUE_BYTES);
            }
        }
    }

    #[test]
    fn array_read_over_distinct_literal_write_keeps_the_prior_array() {
        let array_sort = Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int));
        let prior_read = Formula::Select(
            Box::new(Formula::Var("xs".to_string(), array_sort.clone())),
            Box::new(Formula::Int(1)),
        );
        let formula = Formula::Eq(
            Box::new(Formula::Select(
                Box::new(Formula::Store(
                    Box::new(Formula::Var("xs".to_string(), array_sort)),
                    Box::new(Formula::Int(0)),
                    Box::new(Formula::Int(7)),
                )),
                Box::new(Formula::Int(1)),
            )),
            Box::new(prior_read.clone()),
        );

        let normalized = normalize_decidable_array_read_over_write(&formula);
        assert_eq!(normalized, Formula::Eq(Box::new(prior_read.clone()), Box::new(prior_read)));
        assert!(
            trust_spec_predicate_from_formula(&normalized).is_some(),
            "the exact distinct-index identity should lower through the scalar Select fragment"
        );
    }

    #[test]
    fn a_read_of_a_constant_array_is_its_value_at_every_index() {
        // `[v; N]` stated as `((as const (Array Int Int)) v)`: every lane is `v`,
        // so a read at ANY index — a symbolic one included, and one past a
        // distinct literal write — is exactly `v` (the ArraysEx `as const` law).
        let splat = || Formula::const_array(Sort::Int, Sort::Int, Formula::Int(7));
        let read_index = || Formula::Var("read_index".to_string(), Sort::Int);
        let direct = Formula::Eq(
            Box::new(Formula::Select(Box::new(splat()), Box::new(read_index()))),
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
        );
        assert_eq!(
            normalize_decidable_array_read_over_write(&direct),
            Formula::Eq(
                Box::new(Formula::Int(7)),
                Box::new(Formula::Var("x".to_string(), Sort::Int))
            )
        );
        let past_a_write = Formula::Eq(
            Box::new(Formula::Select(
                Box::new(Formula::Store(
                    Box::new(splat()),
                    Box::new(Formula::Int(0)),
                    Box::new(Formula::Int(9)),
                )),
                Box::new(Formula::Int(1)),
            )),
            Box::new(Formula::Int(7)),
        );
        assert_eq!(
            normalize_decidable_array_read_over_write(&past_a_write),
            Formula::Eq(Box::new(Formula::Int(7)), Box::new(Formula::Int(7)))
        );
        // A symbolic write index still leaves the aliasing question open.
        let symbolic_write = Formula::Eq(
            Box::new(Formula::Select(
                Box::new(Formula::Store(
                    Box::new(splat()),
                    Box::new(Formula::Var("write_index".to_string(), Sort::Int)),
                    Box::new(Formula::Int(9)),
                )),
                Box::new(read_index()),
            )),
            Box::new(Formula::Int(7)),
        );
        assert_eq!(normalize_decidable_array_read_over_write(&symbolic_write), symbolic_write);
    }

    #[test]
    fn symbolic_array_index_aliasing_remains_fail_closed() {
        let array_sort = Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int));
        let formula = Formula::Eq(
            Box::new(Formula::Select(
                Box::new(Formula::Store(
                    Box::new(Formula::Var("xs".to_string(), array_sort)),
                    Box::new(Formula::Var("write_index".to_string(), Sort::Int)),
                    Box::new(Formula::Int(7)),
                )),
                Box::new(Formula::Var("read_index".to_string(), Sort::Int)),
            )),
            Box::new(Formula::Int(7)),
        );

        assert_eq!(normalize_decidable_array_read_over_write(&formula), formula);
        let payload = vc_formula_payload(
            &VcKind::LoopInvariantConsecution {
                invariant: "xs[read_index] == 7".to_string(),
                header_block: 1,
            },
            &formula,
        );
        assert_eq!(payload.typed_payload, None);
        assert_eq!(payload.selected_formula, None);
        assert!(!payload.pruned);
    }

    #[test]
    fn malformed_or_non_int_array_store_cannot_splice_into_the_scalar_lane() {
        let malformed = Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::Select(
                Box::new(Formula::Store(
                    Box::new(Formula::Int(0)),
                    Box::new(Formula::Int(0)),
                    Box::new(Formula::Int(7)),
                )),
                Box::new(Formula::Int(0)),
            )),
            Box::new(Formula::Int(7)),
        )));
        assert!(check_formula_sort(&malformed).is_err());
        assert_eq!(normalize_decidable_array_read_over_write(&malformed), malformed);

        let memory_sort = Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8)));
        let address = Formula::BitVec { value: 0, width: 64 };
        let non_int_indexed = Formula::Eq(
            Box::new(Formula::Select(
                Box::new(Formula::Store(
                    Box::new(Formula::Var("memory".to_string(), memory_sort)),
                    Box::new(address.clone()),
                    Box::new(Formula::BitVec { value: 7, width: 8 }),
                )),
                Box::new(address),
            )),
            Box::new(Formula::BitVec { value: 7, width: 8 }),
        );
        assert_eq!(normalize_decidable_array_read_over_write(&non_int_indexed), non_int_indexed);

        for formula in [&malformed, &non_int_indexed] {
            let payload = vc_formula_payload(
                &VcKind::LoopInvariantInitiation {
                    invariant: "unsupported array store".to_string(),
                    header_block: 1,
                },
                formula,
            );
            assert_eq!(payload.typed_payload, None);
            assert_eq!(payload.selected_formula, None);
        }
    }

    #[test]
    fn false_array_read_after_write_is_transported_without_becoming_true() {
        let array_sort = Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int));
        let formula = Formula::Eq(
            Box::new(Formula::Select(
                Box::new(Formula::Store(
                    Box::new(Formula::Var("xs".to_string(), array_sort)),
                    Box::new(Formula::UInt(0)),
                    Box::new(Formula::Int(7)),
                )),
                Box::new(Formula::Int(0)),
            )),
            Box::new(Formula::Int(8)),
        );

        let payload = vc_formula_payload(
            &VcKind::LoopInvariantInitiation {
                invariant: "xs[0] == 8".to_string(),
                header_block: 1,
            },
            &formula,
        );
        let selected = payload.selected_formula.expect("the false scalar residue must transport");
        assert_eq!(selected, Formula::Eq(Box::new(Formula::Int(7)), Box::new(Formula::Int(8))));
        assert!(payload.typed_payload.is_some());
    }

    #[test]
    fn public_typed_predicate_rejects_arrays_outside_int_select_fragment() {
        let bv_indexed = Formula::Eq(
            Box::new(Formula::Select(
                Box::new(Formula::Var(
                    "heap".to_string(),
                    Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
                )),
                Box::new(Formula::BitVec { value: 0, width: 64 }),
            )),
            Box::new(Formula::BitVec { value: 0, width: 8 }),
        );
        assert!(trust_spec_predicate_from_formula(&bv_indexed).is_none());

        let nested = Formula::Eq(
            Box::new(Formula::Select(
                Box::new(Formula::Var(
                    "nested".to_string(),
                    Sort::Array(
                        Box::new(Sort::Int),
                        Box::new(Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int))),
                    ),
                )),
                Box::new(Formula::Int(0)),
            )),
            Box::new(Formula::Var(
                "row".to_string(),
                Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
            )),
        );
        assert!(trust_spec_predicate_from_formula(&nested).is_none());

        let array_sort = Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int));
        let equality = Formula::Eq(
            Box::new(Formula::Var("left".to_string(), array_sort.clone())),
            Box::new(Formula::Var("right".to_string(), array_sort)),
        );
        assert!(
            trust_spec_predicate_from_formula(&equality).is_none(),
            "the full validator must prevent producer emission of array equality"
        );
    }

    #[test]
    fn ownership_vc_gets_structured_trust_vc_mir_memory_proof_unit() {
        let function = trust_vc_memory_test_function(Ty::Int { width: 32, signed: true });
        let compiler_contracts = CompilerContractBundle::default();
        let vcs = vec![VerificationCondition {
            kind: VcKind::AliasingViolation { mutable: true },
            function: trust_types::Symbol::intern("demo::f"),
            location: function.span.clone(),
            formula: trust_types::Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        }];

        let bundle = function_to_verifier_api_bundle(&function, &compiler_contracts, &vcs);
        let obligation = &bundle.obligations[0];

        assert_eq!(obligation.kind, ObligationKind::Ownership);
        assert_eq!(
            obligation.required_strength,
            Some(ProofStrength::certified(ReasoningKind::OwnershipAnalysis))
        );
        assert_eq!(
            metadata_value(&obligation.metadata, TRUST_VC_CONDITION_ORIGIN_METADATA_KEY),
            Some(TRUST_VC_CONDITION_ORIGIN_METADATA_VALUE)
        );
        assert_eq!(
            metadata_value(&obligation.metadata, TRUST_VC_PROOF_OBLIGATION_METADATA_KEY),
            Some(TRUST_VC_PROOF_OBLIGATION_METADATA_VALUE)
        );
        assert_eq!(
            metadata_value(&obligation.metadata, TRUST_VC_OWNERSHIP_CONTEXT_METADATA_KEY),
            Some(TRUST_VC_OWNERSHIP_CONTEXT_METADATA_VALUE)
        );
        assert_eq!(
            metadata_value(
                &obligation.metadata,
                TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_METADATA_KEY
            ),
            Some(TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_VERSION)
        );
        assert_eq!(
            metadata_value(
                &obligation.metadata,
                TRUST_VC_MIR_MEMORY_PROOF_UNIT_UNSUPPORTED_METADATA_KEY
            ),
            None
        );

        let raw_payload =
            metadata_value(&obligation.metadata, TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY)
                .expect("structured direct proof-unit metadata");
        let typed_unit: trust_vc_trust_engine::TrustMirMemoryProofUnit =
            serde_json::from_str(raw_payload)
                .expect("producer payload parses as the consumer type");
        let typed_value =
            serde_json::to_value(&typed_unit).expect("consumer type serializes to JSON");
        let expected_typed_payload =
            serde_json::to_string(&trust_types::canonical_json_value(&typed_value))
                .expect("recursively sorted consumer payload serializes");
        assert_eq!(
            raw_payload, expected_typed_payload,
            "producer bytes must equal the recursively sorted typed consumer serialization"
        );

        let payload = trust_vc_payload(obligation);
        assert_eq!(payload["source_id"], "trust-mir-extract:demo__f");
        assert_eq!(payload["unit_id"], "demo::f");
        assert!(
            payload.get("verifier_variables").is_none(),
            "the typed proof-unit serializer omits an empty verifier-variable list"
        );
        assert_eq!(payload["native_context"]["function_signature"]["params"][0]["name"], "x");
        assert_eq!(
            payload["native_context"]["ownership"]["places"][1]["sort"],
            serde_json::json!({
                "kind": "bit_vector",
                "width": 32,
                "signed": true,
            })
        );
        assert_eq!(payload["obligations"][0]["id"], obligation.obligation_id);
        assert_eq!(
            payload["obligations"][0]["predicate"],
            serde_json::json!({
                "kind": "bool_literal",
                "value": true,
            })
        );
    }

    #[test]
    fn widened_public_formula_and_direct_proof_unit_share_exact_selected_formula() {
        let function = trust_vc_memory_test_function(Ty::Int { width: 64, signed: false });
        let compiler_contracts = CompilerContractBundle::default();
        let source_formula = Formula::Le(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::UInt(u64::MAX.into())),
        );
        let selected_formula = try_widen_unsigned_relational_vc_to_bv(&source_formula)
            .expect("wide unsigned relation selects the exact BV formula");
        assert_ne!(selected_formula, source_formula);
        let vcs = vec![VerificationCondition {
            kind: VcKind::AliasingViolation { mutable: true },
            function: trust_types::Symbol::intern("demo::f"),
            location: function.span.clone(),
            formula: source_formula.clone(),
            contract_metadata: None,
            obligation: None,
        }];

        let bundle = function_to_verifier_api_bundle(&function, &compiler_contracts, &vcs);
        let obligation = &bundle.obligations[0];
        let public_payload =
            metadata_value(&obligation.metadata, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
                .expect("widened public formula has a typed payload");
        let public_predicate: TrustSpecPredicate = serde_json::from_str(public_payload)
            .expect("widened public typed payload is canonical predicate JSON");
        let expected_public = trust_spec_predicate_from_formula(&selected_formula)
            .expect("selected BV formula lowers to the public predicate");
        assert_eq!(public_predicate, expected_public);

        let mut exact_lowerer = TrustVcFormulaLowering::default();
        let expected_unit_predicate = exact_lowerer
            .negated_vc_formula(&selected_formula)
            .expect("selected BV formula lowers to the direct TrustVC predicate");
        let mut stale_lowerer = TrustVcFormulaLowering::default();
        let stale_source_predicate = stale_lowerer
            .negated_vc_formula(&source_formula)
            .expect("pre-selection formula also lowers for the drift regression");
        assert_ne!(expected_unit_predicate, stale_source_predicate);
        assert_eq!(
            trust_vc_payload(obligation)["obligations"][0]["predicate"],
            expected_unit_predicate,
        );
    }

    #[test]
    fn wide_bounds_formula_stays_exact_int_in_public_and_direct_predicates() {
        let function = trust_vc_memory_test_function(Ty::Int { width: 64, signed: false });
        let compiler_contracts = CompilerContractBundle::default();
        let len = Formula::Var("len".to_string(), Sort::Int);
        let index = Formula::Var("index".to_string(), Sort::Int);
        let checked_len = Formula::Var("checked_len".to_string(), Sort::Int);
        let source_formula = Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(1)), Box::new(len.clone())),
            Formula::Le(Box::new(Formula::Int(0)), Box::new(len.clone())),
            Formula::Le(Box::new(len.clone()), Box::new(Formula::UInt(u64::MAX.into()))),
            Formula::Le(Box::new(Formula::Int(0)), Box::new(index.clone())),
            Formula::Le(Box::new(index.clone()), Box::new(Formula::UInt(u64::MAX.into()))),
            Formula::Eq(Box::new(index.clone()), Box::new(Formula::Int(0))),
            Formula::Eq(Box::new(checked_len.clone()), Box::new(len)),
            Formula::Le(Box::new(checked_len), Box::new(index)),
        ]);
        assert!(
            try_widen_unsigned_relational_vc_to_bv(&source_formula).is_some(),
            "the non-bounds lane must still recognize this as a wide unsigned relation",
        );
        let vc = VerificationCondition {
            kind: VcKind::SliceBoundsCheck,
            function: trust_types::Symbol::intern("demo::f"),
            location: function.span.clone(),
            formula: source_formula.clone(),
            contract_metadata: None,
            obligation: None,
        };

        let selection = vc_formula_payload(&vc.kind, &vc.formula);
        assert_eq!(selection.selected_formula.as_ref(), Some(&source_formula));
        assert!(!selection.pruned);
        assert_eq!(selection.sort, "Bool");
        assert_eq!(selection.smtlib, source_formula.to_smtlib());
        assert!(selection.smtlib.contains("18446744073709551615"));
        assert!(!selection.smtlib.contains("bvule"));
        let fixed_array_selection = vc_formula_payload(&VcKind::IndexOutOfBounds, &source_formula);
        assert_eq!(fixed_array_selection.selected_formula.as_ref(), Some(&source_formula));
        assert!(!fixed_array_selection.pruned);
        assert!(!fixed_array_selection.smtlib.contains("bvule"));

        let bundle = function_to_verifier_api_bundle(
            &function,
            &compiler_contracts,
            std::slice::from_ref(&vc),
        );
        let obligation = &bundle.obligations[0];
        assert_eq!(
            metadata_value(&obligation.metadata, TRUST_VC_FORMULA_PRUNED_METADATA_KEY),
            None,
        );
        let public_payload =
            metadata_value(&obligation.metadata, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
                .expect("wide bounds formula has a typed public payload");
        let public_predicate: TrustSpecPredicate = serde_json::from_str(public_payload)
            .expect("wide bounds payload is canonical predicate JSON");
        assert_eq!(
            public_predicate,
            trust_spec_predicate_from_formula(&source_formula)
                .expect("the exact source Int formula lowers publicly"),
        );

        let mut lowerer = TrustVcFormulaLowering::default();
        let expected_direct = lowerer
            .negated_vc_formula(&source_formula)
            .expect("the exact source Int formula lowers directly");
        assert_eq!(trust_vc_payload(obligation)["obligations"][0]["predicate"], expected_direct,);
        assert!(
            trust_vc_payload(obligation)["verifier_variables"]
                .as_array()
                .expect("wide bounds variables are explicit")
                .iter()
                .all(|variable| variable["sort"]["kind"] == "math_int"),
            "wide bounds variables must stay on the exact MathInt lane",
        );

        let identity = verifier_vc_content_identity(&function, 0, &vc);
        assert!(!identity.formula_pruned);
        assert_eq!(identity.formula_smtlib, source_formula.to_smtlib());
        assert_eq!(identity.formula_payload.as_deref(), Some(public_payload));
    }

    #[test]
    fn unsigned_literal_uses_same_integer_sort_in_public_and_direct_predicates() {
        let function = trust_vc_memory_test_function(Ty::Int { width: 32, signed: false });
        let compiler_contracts = CompilerContractBundle::default();
        let vcs = vec![VerificationCondition {
            kind: VcKind::AliasingViolation { mutable: true },
            function: trust_types::Symbol::intern("demo::f"),
            location: function.span.clone(),
            formula: Formula::Le(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::UInt(5)),
            ),
            contract_metadata: None,
            obligation: None,
        }];

        let bundle = function_to_verifier_api_bundle(&function, &compiler_contracts, &vcs);
        let obligation = &bundle.obligations[0];
        let public_payload =
            metadata_value(&obligation.metadata, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
                .expect("small unsigned formula has a typed public payload");
        let public_predicate: TrustSpecPredicate = serde_json::from_str(public_payload)
            .expect("typed public payload is canonical predicate JSON");
        let trust_verifier_api::TrustSpecExprKind::Binary { rhs, .. } = &public_predicate.root.kind
        else {
            panic!("public unsigned relation must remain a typed binary predicate");
        };
        assert_eq!(rhs.sort, TrustSpecSort::Int);

        let unit = trust_vc_payload(obligation);
        assert_eq!(
            unit["obligations"][0]["predicate"]["expr"]["right"]["sort"]["kind"],
            "math_int",
        );
    }

    #[test]
    fn pruned_public_formula_and_direct_proof_unit_share_exact_selected_residue() {
        let function = trust_vc_memory_test_function(Ty::Int { width: 32, signed: true });
        let compiler_contracts = CompilerContractBundle::default();
        let unlowerable = Formula::Eq(
            Box::new(Formula::Select(
                Box::new(Formula::Var(
                    "memory_map".to_string(),
                    Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
                )),
                Box::new(Formula::BitVec { value: 0, width: 64 }),
            )),
            Box::new(Formula::BitVec { value: 0, width: 8 }),
        );
        let source_formula = Formula::And(vec![unlowerable, Formula::Bool(false)]);
        let selected_formula = prune_to_lowerable_violation(&source_formula)
            .expect("violation pruning selects the lowerable residue");
        assert_eq!(selected_formula, Formula::Bool(false));
        let vcs = vec![VerificationCondition {
            kind: VcKind::AliasingViolation { mutable: true },
            function: trust_types::Symbol::intern("demo::f"),
            location: function.span.clone(),
            formula: source_formula,
            contract_metadata: None,
            obligation: None,
        }];

        let bundle = function_to_verifier_api_bundle(&function, &compiler_contracts, &vcs);
        let obligation = &bundle.obligations[0];
        assert_eq!(
            metadata_value(&obligation.metadata, TRUST_VC_FORMULA_PRUNED_METADATA_KEY),
            Some("true"),
        );
        let public_payload =
            metadata_value(&obligation.metadata, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
                .expect("pruned public formula has a typed payload");
        let public_predicate: TrustSpecPredicate = serde_json::from_str(public_payload)
            .expect("pruned public typed payload is canonical predicate JSON");
        assert_eq!(
            public_predicate,
            trust_spec_predicate_from_formula(&selected_formula)
                .expect("selected residue lowers to the public predicate"),
        );
        let mut lowerer = TrustVcFormulaLowering::default();
        assert_eq!(
            trust_vc_payload(obligation)["obligations"][0]["predicate"],
            lowerer
                .negated_vc_formula(&selected_formula)
                .expect("selected residue lowers to the direct predicate"),
        );
    }

    #[test]
    fn direct_proof_unit_rejects_selected_formula_or_public_payload_mutation() {
        let function = trust_vc_memory_test_function(Ty::Int { width: 32, signed: true });
        let vc = VerificationCondition {
            kind: VcKind::AliasingViolation { mutable: true },
            function: trust_types::Symbol::intern("demo::f"),
            location: function.span.clone(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };
        let obligation_kind = vc_obligation_kind(&vc.kind);

        let mut payload_mutated = vc_formula_payload(&vc.kind, &vc.formula);
        payload_mutated.typed_payload =
            vc_formula_payload(&vc.kind, &Formula::Bool(true)).typed_payload;
        let payload_metadata =
            trust_vc_mir_memory_metadata(&function, &vc, 0, &obligation_kind, &payload_mutated);
        assert_eq!(
            metadata_value(&payload_metadata, TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY,),
            None,
        );
        assert!(
            metadata_value(
                &payload_metadata,
                TRUST_VC_MIR_MEMORY_PROOF_UNIT_UNSUPPORTED_METADATA_KEY,
            )
            .is_some_and(
                |reason| reason.contains("selected formula and public typed payload drifted")
            ),
        );

        let mut selection_mutated = vc_formula_payload(&vc.kind, &vc.formula);
        selection_mutated.selected_formula = Some(Formula::Bool(true));
        let selection_metadata =
            trust_vc_mir_memory_metadata(&function, &vc, 0, &obligation_kind, &selection_mutated);
        assert_eq!(
            metadata_value(&selection_metadata, TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY,),
            None,
        );
        assert!(
            metadata_value(
                &selection_metadata,
                TRUST_VC_MIR_MEMORY_PROOF_UNIT_UNSUPPORTED_METADATA_KEY,
            )
            .is_some_and(
                |reason| reason.contains("selected formula and public typed payload drifted")
            ),
        );
    }

    #[test]
    fn memory_vc_with_heap_lifetime_kind_fails_closed_without_trust_vc_payload() {
        let function = trust_vc_memory_test_function(Ty::Int { width: 32, signed: true });
        let compiler_contracts = CompilerContractBundle::default();
        let vcs = vec![VerificationCondition {
            kind: VcKind::UseAfterFree,
            function: trust_types::Symbol::intern("demo::f"),
            location: function.span.clone(),
            formula: trust_types::Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        }];

        let bundle = function_to_verifier_api_bundle(&function, &compiler_contracts, &vcs);
        let obligation = &bundle.obligations[0];

        assert_eq!(obligation.kind, ObligationKind::MemorySafety);
        assert_eq!(
            metadata_value(&obligation.metadata, TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY),
            None
        );
        assert_eq!(
            metadata_value(&obligation.metadata, TRUST_VC_CONDITION_ORIGIN_METADATA_KEY),
            None
        );
        assert!(
            metadata_value(
                &obligation.metadata,
                TRUST_VC_MIR_MEMORY_PROOF_UNIT_UNSUPPORTED_METADATA_KEY
            )
            .is_some_and(|reason| reason.contains("heap allocation lifetime")),
            "expected heap lifetime fail-closed reason: {:?}",
            obligation.metadata
        );
    }

    #[test]
    fn ownership_vc_with_raw_pointer_local_fails_closed_without_trust_vc_payload() {
        let function = trust_vc_memory_test_function(Ty::RawPtr {
            mutable: false,
            pointee: Box::new(Ty::Int { width: 32, signed: true }),
        });
        let compiler_contracts = CompilerContractBundle::default();
        let vcs = vec![VerificationCondition {
            kind: VcKind::AliasingViolation { mutable: false },
            function: trust_types::Symbol::intern("demo::f"),
            location: function.span.clone(),
            formula: trust_types::Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        }];

        let bundle = function_to_verifier_api_bundle(&function, &compiler_contracts, &vcs);
        let obligation = &bundle.obligations[0];

        assert_eq!(obligation.kind, ObligationKind::Ownership);
        assert_eq!(
            metadata_value(&obligation.metadata, TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY),
            None
        );
        assert_eq!(
            metadata_value(&obligation.metadata, TRUST_VC_PROOF_OBLIGATION_METADATA_KEY),
            None
        );
        assert!(
            metadata_value(
                &obligation.metadata,
                TRUST_VC_MIR_MEMORY_PROOF_UNIT_UNSUPPORTED_METADATA_KEY
            )
            .is_some_and(|reason| reason.contains("raw pointer types")),
            "expected raw pointer fail-closed reason: {:?}",
            obligation.metadata
        );
    }

    /// The i128 overflow VC's type-range guard shape: `x >= LO && x <= i128::MAX`.
    /// `LO` is a parameter so the injectivity twin can digest a neighboring formula.
    fn i128_range_guard_formula(lower: i128) -> Formula {
        let x = || Box::new(Formula::Var("x".to_string(), Sort::Int));
        Formula::And(vec![
            Formula::Ge(x(), Box::new(Formula::Int(lower))),
            Formula::Le(x(), Box::new(Formula::Int(i128::MAX))),
        ])
    }

    fn i128_overflow_vc(function: &VerifiableFunction, lower: i128) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: trust_types::BinOp::Add,
                operand_tys: (
                    Ty::Int { width: 128, signed: true },
                    Ty::Int { width: 128, signed: true },
                ),
            },
            function: trust_types::Symbol::intern("demo::f"),
            location: function.span.clone(),
            formula: i128_range_guard_formula(lower),
            contract_metadata: None,
            obligation: None,
        }
    }

    #[test]
    fn vcs_with_i128_type_range_literals_digest_without_crashing() {
        // Falsification corpus, i128/u128 ICE class: `serde_json::to_value`
        // rejects integers outside the i64/u64 range, so the digest material
        // for an i128 overflow VC — whose formula carries the
        // `i128::MIN`/`i128::MAX` type-range bounds — panicked the compiler
        // inside `vc_content_digest` on all 8 i128/u128 gate fixtures. The
        // bundle must build, with a canonical 64-hex digest, deterministically.
        let function = test_function();
        let compiler_contracts = CompilerContractBundle::default();
        let vcs = vec![i128_overflow_vc(&function, i128::MIN)];

        let bundle = function_to_verifier_api_bundle(&function, &compiler_contracts, &vcs);
        assert_eq!(bundle.obligations.len(), 1);
        let digest = metadata_value(&bundle.obligations[0].metadata, TRUST_VC_DIGEST_METADATA_KEY)
            .expect("wide-literal VC must still carry a content digest");
        assert_eq!(digest.len(), 64);
        assert!(digest.chars().all(|ch| ch.is_ascii_hexdigit()));

        // Deterministic: the same material digests to the same identity.
        let again = function_to_verifier_api_bundle(&function, &compiler_contracts, &vcs);
        assert_eq!(
            metadata_value(&again.obligations[0].metadata, TRUST_VC_DIGEST_METADATA_KEY),
            Some(digest),
        );

        // Injectivity twin: a neighboring wide literal must NOT collapse onto
        // the same digest (a lossy wide-int encoding would be a forgeable
        // identity, worse than the crash it replaced).
        let neighbor = vec![i128_overflow_vc(&function, i128::MIN + 1)];
        let neighbor_bundle =
            function_to_verifier_api_bundle(&function, &compiler_contracts, &neighbor);
        assert_ne!(
            metadata_value(&neighbor_bundle.obligations[0].metadata, TRUST_VC_DIGEST_METADATA_KEY),
            Some(digest),
        );
    }

    /// T3 L4 (C09w; design §8): the VC content digest v2 binds the function, the index, the
    /// kind, the location, the formula's schema and sort, and the formula by its Merkle
    /// digest: v2's material is inlined as the differential oracle, each bound field moves
    /// the digest, the SMT-LIB text and the typed payload no longer do, a separately built
    /// formula of the same tree gives the same digest (I5), and v1's digest is not v2's.
    #[test]
    fn vc_content_digest_v2_binds_the_formula_by_its_merkle_digest() {
        let function = test_function();
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: trust_types::Symbol::intern("demo::f"),
            location: function.span.clone(),
            formula: Formula::Gt(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(7)),
            ),
            contract_metadata: None,
            obligation: None,
        };
        let payload_of = |schema: &str, sort: &str, smtlib: &str, typed: Option<&str>| {
            VcFormulaPayload {
                schema: schema.to_string(),
                sort: sort.to_string(),
                smtlib: smtlib.to_string(),
                // Nothing lowered here (`typed_payload: None`), so nothing can have been
                // dropped at the transport ceiling — which is exactly the case the field's
                // own doc names for `None`.
                typed_payload_dropped_bytes: None,
                smtlib_omitted_bytes: None,
                typed_payload: typed.map(str::to_string),
                selected_formula: None,
                verified_seal: None,
                pruned: false,
            }
        };
        let payload = payload_of(TRUST_SYMBOLIC_FORMULA_SCHEMA, "Bool", "(> x 7)", None);
        let digest = vc_content_digest(&function, 3, &vc, &payload);

        let merkle = trust_types::formula_merkle::formula_digest(&vc.formula).unwrap().to_hex();
        let mut material = serde_json::Map::new();
        material.insert(
            "schema".to_string(),
            JsonValue::String("trust-mir-extract.vc-digest.v2".to_string()),
        );
        material.insert("function".to_string(), JsonValue::String(function.def_path.clone()));
        material.insert("vc_index".to_string(), JsonValue::String("3".to_string()));
        material.insert("vc_kind".to_string(), serde_json::to_value(&vc.kind).unwrap());
        material.insert("location".to_string(), serde_json::to_value(&vc.location).unwrap());
        material.insert("formula_schema".to_string(), JsonValue::String(payload.schema.clone()));
        material.insert("formula_sort".to_string(), JsonValue::String(payload.sort.clone()));
        material.insert("formula_merkle".to_string(), JsonValue::String(merkle));
        assert_eq!(digest, stable_json_digest(&JsonValue::Object(material.clone())));

        // Each bound field moves the digest.
        let mut other_function = function.clone();
        other_function.def_path = "demo::g".to_string();
        let mut other_kind = vc.clone();
        other_kind.kind = VcKind::RemainderByZero;
        let mut other_location = vc.clone();
        other_location.location.line_start += 1;
        let mut other_formula = vc.clone();
        other_formula.formula = Formula::Bool(false);
        let other_schema = payload_of("other", "Bool", "(> x 7)", None);
        let other_sort = payload_of(TRUST_SYMBOLIC_FORMULA_SCHEMA, "Int", "(> x 7)", None);
        for (what, moved) in [
            ("function", vc_content_digest(&other_function, 3, &vc, &payload)),
            ("index", vc_content_digest(&function, 4, &vc, &payload)),
            ("kind", vc_content_digest(&function, 3, &other_kind, &payload)),
            ("location", vc_content_digest(&function, 3, &other_location, &payload)),
            ("formula", vc_content_digest(&function, 3, &other_formula, &payload)),
            ("schema", vc_content_digest(&function, 3, &vc, &other_schema)),
            ("sort", vc_content_digest(&function, 3, &vc, &other_sort)),
        ] {
            assert_ne!(moved, digest, "{what}");
        }

        // The formula's other encodings no longer reach it.
        let other_text = payload_of(TRUST_SYMBOLIC_FORMULA_SCHEMA, "Bool", "(> x 8)", Some("{}"));
        assert_eq!(vc_content_digest(&function, 3, &vc, &other_text), digest);

        // I5: the same tree, built separately.
        let rebuilt: VerificationCondition =
            serde_json::from_str(&serde_json::to_string(&vc).unwrap()).unwrap();
        assert_eq!(vc_content_digest(&function, 3, &rebuilt, &payload), digest);

        // v1's material is not v2's.
        material.insert(
            "schema".to_string(),
            JsonValue::String("trust-mir-extract.vc-digest.v1".to_string()),
        );
        material.remove("formula_merkle");
        material.insert("formula".to_string(), serde_json::to_value(&vc.formula).unwrap());
        material.insert("formula_smtlib2".to_string(), JsonValue::String(payload.smtlib.clone()));
        material.insert("formula_typed_payload".to_string(), JsonValue::Null);
        assert_ne!(stable_json_digest(&JsonValue::Object(material)), digest);
    }

    /// Review rounds 35 and 36: the unsigned BV wideners assume every variable is
    /// below `2^64`, so only a variable naming a narrow unsigned local (or a Bool)
    /// is admitted, and never a source name a wider local also carries.
    #[test]
    fn bv_widening_admits_only_unambiguous_narrow_unsigned_locals() {
        let mut function = test_function();
        function.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::Int { width: 64, signed: false }, name: None },
            LocalDecl {
                index: 1,
                ty: Ty::Int { width: 128, signed: false },
                name: Some("b".into()),
            },
            LocalDecl { index: 2, ty: Ty::Int { width: 8, signed: false }, name: Some("b".into()) },
            LocalDecl {
                index: 3,
                ty: Ty::Int { width: 64, signed: false },
                name: Some("d".into()),
            },
            LocalDecl { index: 4, ty: Ty::Bool, name: None },
            LocalDecl { index: 5, ty: Ty::Int { width: 64, signed: true }, name: Some("s".into()) },
        ];
        let admitted = |name: &str, sort: Sort| {
            formula_vars_are_narrow_unsigned_locals(
                &function,
                &Formula::Le(
                    Box::new(Formula::Var(name.to_string(), sort)),
                    Box::new(Formula::UInt(u64::MAX.into())),
                ),
            )
        };
        assert!(admitted("_0", Sort::Int));
        assert!(admitted("_2", Sort::Int));
        assert!(admitted("d", Sort::Int));
        assert!(admitted("d#s1_0", Sort::Int));
        assert!(admitted("_4", Sort::Bool));
        assert!(admitted("d__slice_len", Sort::Int));
        // The u128 parameter `b` shares its name with the u8 shadow `_2`.
        assert!(!admitted("b", Sort::Int));
        assert!(!admitted("_1", Sort::Int));
        assert!(!admitted("s", Sort::Int));
        assert!(!admitted("_5", Sort::Int));
        assert!(!admitted("__trust_constparam_0_N", Sort::Int));
        assert!(!admitted("e", Sort::Int));
    }

    #[test]
    fn wave498_bundle_conversion_cached_scans_and_selected_seal_parity() {
        let mut function = trust_vc_memory_test_function(Ty::Int { width: 64, signed: false });
        function.body.locals.push(LocalDecl {
            index: 2,
            ty: Ty::Slice { elem: Box::new(Ty::u8()) },
            name: Some("slice_param".to_string()),
        });
        function.body.arg_count = 2;

        let vcs = vec![
            VerificationCondition {
                kind: VcKind::SliceBoundsCheck,
                function: trust_types::Symbol::intern("demo::f"),
                location: function.span.clone(),
                formula: Formula::Lt(
                    Box::new(Formula::Var("x".to_string(), Sort::Int)),
                    Box::new(Formula::Var("slice_param__slice_len".to_string(), Sort::Int)),
                ),
                contract_metadata: None,
                obligation: None,
            },
            VerificationCondition {
                kind: VcKind::IndexOutOfBounds,
                function: trust_types::Symbol::intern("demo::f"),
                location: function.span.clone(),
                formula: Formula::Ge(
                    Box::new(Formula::Var("x".to_string(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
                contract_metadata: None,
                obligation: None,
            },
        ];
        let compiler_contracts = CompilerContractBundle::default();
        let bundle = function_to_verifier_api_bundle_with_compiler_identity(
            &function,
            &compiler_contracts,
            &vcs,
            "demo",
            0x498,
            Some(64),
        );
        assert_eq!(bundle.obligations.len(), 2);
        for (idx, vc) in vcs.iter().enumerate() {
            let id = verifier_vc_content_identity_with_crate_name(&function, idx, vc, "demo");
            assert_eq!(bundle.obligations[idx].obligation_id, id.obligation_id);
            assert_eq!(
                metadata_value(&bundle.obligations[idx].metadata, TRUST_VC_DIGEST_METADATA_KEY),
                Some(id.digest.as_str()),
            );
            assert!(
                metadata_value(
                    &bundle.obligations[idx].metadata,
                    TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY,
                )
                .is_some()
            );
        }

        // Wide (>16 conjuncts) disjunction factoring must match the <=16 reference.
        let shared: Vec<Formula> = (0..20)
            .map(|i| {
                Formula::Ge(
                    Box::new(Formula::Var(format!("v{i}"), Sort::Int)),
                    Box::new(Formula::Int(i)),
                )
            })
            .collect();
        let mut arm_a = shared.clone();
        arm_a.push(Formula::Eq(
            Box::new(Formula::Var("branch".into(), Sort::Int)),
            Box::new(Formula::Int(1)),
        ));
        let mut arm_b = shared.clone();
        arm_b.push(Formula::Eq(
            Box::new(Formula::Var("branch".into(), Sort::Int)),
            Box::new(Formula::Int(2)),
        ));
        let wide_or = Formula::Or(vec![Formula::And(arm_a), Formula::And(arm_b)]);
        let factored = factor_shared_disjunct_conjuncts(&wide_or);
        let Formula::And(conjuncts) = factored else {
            panic!("expected factored conjunction");
        };
        assert_eq!(conjuncts.len(), 21);
        assert_eq!(&conjuncts[..20], shared.as_slice());
    }
}

/// SPEC-FLOAT-EQ-STRUCTURAL-1: the public IR's `eq` over a Float sort is IEEE
/// equality, so only IEEE `FpEq` may lower to it; a structural float `Eq` has no
/// public spelling and fails closed.
#[cfg(test)]
mod float_eq_payload_tests {
    use trust_verifier_api::TrustSpecExprKind;

    use super::*;

    const F64: Sort = Sort::Float { eb: 11, sb: 53 };

    fn f64v(name: &str) -> Box<Formula> {
        Box::new(Formula::Var(name.to_string(), F64))
    }

    fn fp(value: f64) -> Box<Formula> {
        Box::new(Formula::FpConst { bits: u128::from(value.to_bits()), eb: 11, sb: 53 })
    }

    fn bits(value: f64) -> Box<Formula> {
        Box::new(Formula::BitVec { value: i128::from(value.to_bits()), width: 64 })
    }

    #[test]
    fn ieee_float_equality_lowers_to_the_public_float_eq() {
        let predicate = trust_spec_predicate_from_formula(&Formula::FpEq(f64v("x"), f64v("y")))
            .expect("IEEE equality of two f64 values is in the public subset");
        let TrustSpecExprKind::Binary { op, lhs, rhs } = &predicate.root.kind else {
            panic!("binary root expected: {:?}", predicate.root);
        };
        assert_eq!(*op, TrustSpecBinaryOp::Eq);
        assert_eq!(lhs.sort, TrustSpecSort::Float { eb: 11, sb: 53 });
        assert_eq!(rhs.sort, TrustSpecSort::Float { eb: 11, sb: 53 });
        assert!(
            trust_spec_predicate_from_formula(&Formula::Not(Box::new(Formula::FpEq(
                f64v("x"),
                fp(1.0)
            ))))
            .is_some()
        );
    }

    #[test]
    fn structural_float_equality_has_no_public_spelling() {
        assert!(trust_spec_predicate_from_formula(&Formula::Eq(f64v("x"), f64v("y"))).is_none());
        assert!(trust_spec_predicate_from_formula(&Formula::Eq(f64v("x"), fp(1.0))).is_none());
        // Integer and bit-vector equality keep their (structural, and correct)
        // public spelling.
        assert!(
            trust_spec_predicate_from_formula(&Formula::Eq(
                Box::new(Formula::Var("i".to_string(), Sort::Int)),
                Box::new(Formula::Int(3)),
            ))
            .is_some()
        );
        assert!(trust_spec_predicate_from_formula(&Formula::Eq(bits(1.0), bits(1.0))).is_some());
    }

    /// The callsite shape after the formals are replaced by the actuals' bit
    /// patterns (q4 `c_xy(f64::NAN, f64::NAN)`): IEEE equality over BIT VECTORS
    /// is ill-sorted and lowers to nothing, so no typed lane receives it. Its
    /// BEFORE spelling — structural `Eq` over the two bit patterns — lowered to
    /// the public bit-vector `eq` that the native trust_mc CHC/PDR lane proved.
    #[test]
    fn substituted_bit_pattern_equality_is_not_lowered() {
        let after = Formula::Not(Box::new(Formula::FpEq(bits(f64::NAN), bits(f64::NAN))));
        assert!(trust_spec_predicate_from_formula(&after).is_none());
        let before = Formula::Not(Box::new(Formula::Eq(bits(f64::NAN), bits(f64::NAN))));
        assert!(trust_spec_predicate_from_formula(&before).is_some());
    }
}

#[cfg(test)]
#[path = "unsigned_literal_remainder_tests.rs"]
mod unsigned_literal_remainder_tests;

#[cfg(test)]
mod correspondence_tests;

#[cfg(test)]
mod entry_domain_tests;

#[cfg(test)]
mod unsigned_call_tests;

#[cfg(test)]
mod typed_predicate_tests;
