//! Public Trust verifier API boundary.
//!
//! This crate defines the stable data boundary between Trust and verifier
//! engines. Engines consume `TrustContractBundle` values, report support for
//! each `TrustObligation`, and return structured `ObligationEvidence` with
//! enough publication metadata for dscan and dpub to audit releases.

use std::collections::{BTreeMap, BTreeSet};
use std::marker::PhantomData;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use rustc_hash::{FxHashMap, FxHashSet};
use serde::de::{self, IgnoredAny, SeqAccess, Visitor};
use serde::{Deserialize, Deserializer, Serialize};
use trust_types::digest::{canonicalize_json_in_place, is_stable_sha256_hex, stable_sha256_hex};

// The proof-assurance vocabulary is defined in trust-ir-contract (shared
// cross-repo vocabulary) and re-exported here so every dependent
// (trust-router, trust-wp, trust-vc-bridge, trust-mir-extract, trust-bmc, …)
// and `trust_verifier_api::{AssuranceLevel, ProofStrength, ReasoningKind,
// TrustSpecVariableOrigin}` path is unchanged. Derives/serde attrs are
// preserved verbatim there, so the wire format is byte-identical.
pub use trust_ir_contract::{
    AssuranceLevel, ProofStrength, ReasoningKind, TrustSpecVariableOrigin,
};

/// Schema version for serialized verifier API payloads.
pub const SCHEMA_VERSION: &str = "trust.verifier-api.v1";

/// Largest exact artifact payload that may be carried through compiler proof
/// transport. Producers may retain larger artifacts out of band, but they must
/// not claim inline materialization for them.
pub const MAX_EVIDENCE_ARTIFACT_MATERIALIZATION_BYTES: usize = 16 * 1024 * 1024;

/// Maximum artifact nodes accepted for one obligation evidence record.
/// Publication-grade routes use only a small fixed DAG; this ceiling leaves
/// ample room for supplemental diagnostics while bounding untrusted engine
/// response deserialization and policy work.
pub const MAX_EVIDENCE_ARTIFACTS_PER_OBLIGATION: usize = 256;

/// Maximum deduplicated artifact nodes accepted in a serialized run manifest.
/// A manifest aggregates many individually bounded obligation records, so its
/// ceiling is deliberately larger while still preventing an unbounded vector.
pub const MAX_EVIDENCE_ARTIFACTS_PER_RUN_MANIFEST: usize = 65_536;

/// Maximum typed obligations, evidence records, or skipped records accepted
/// in one serialized verifier run. The in-tree large-function regression uses
/// 100,000 obligations; this retains headroom while closing unbounded arrays.
pub const MAX_VERIFIER_RUN_RECORDS: usize = 131_072;

/// Maximum combined obligations, evidence decisions, and skipped records in a
/// run envelope. The individual vectors remain independently bounded; this
/// aggregate ceiling prevents a caller from filling every vector to its cap.
pub const MAX_VERIFIER_RUN_AGGREGATE_RECORDS: usize = 2 * MAX_VERIFIER_RUN_RECORDS;

/// Maximum top-level diagnostic messages in a run or release manifest.
pub const MAX_VERIFIER_RUN_DIAGNOSTICS: usize = 65_536;

/// Maximum engine diagnostic messages retained with one evidence decision.
pub const MAX_EVIDENCE_DIAGNOSTICS_PER_RECORD: usize = 256;

/// Maximum UTF-8 bytes in one diagnostic message accepted by actionable run
/// and manifest validation.
pub const MAX_VERIFIER_DIAGNOSTIC_BYTES: usize = 64 * 1024;

/// Maximum UTF-8 bytes in one requested-obligation description accepted by an
/// actionable run result.
pub const MAX_OBLIGATION_DESCRIPTION_BYTES: usize = 1024 * 1024;

/// Maximum serialized JSON bytes accepted by the checked run/manifest ingress
/// helpers. Generic `Deserialize` implementations cannot inspect the source
/// buffer length, so untrusted callers should use those helpers.
pub const MAX_VERIFIER_JSON_ENVELOPE_BYTES: usize = 64 * 1024 * 1024;

/// Structural work limits for a programmatically constructed counterexample
/// JSON value. `serde_json` also enforces its own parser recursion limit.
pub const MAX_COUNTEREXAMPLE_JSON_SCALAR_BYTES: usize = 16 * 1024 * 1024;
pub const MAX_COUNTEREXAMPLE_JSON_NODES: usize = 1_000_000;
pub const MAX_COUNTEREXAMPLE_JSON_DEPTH: usize = 128;

/// Bounded engine-manifest and bundle collection sizes used at serde and
/// programmatic validation boundaries.
pub const MAX_ENGINE_CAPABILITIES: usize = 256;
pub const MAX_ENGINE_PROOF_MODES: usize = 64;
pub const MAX_ENGINE_PROVENANCE_FIELD_BYTES: usize = 4096;
pub const MAX_BUNDLE_METADATA_ENTRIES: usize = 65_536;
pub const MAX_RECORD_METADATA_ENTRIES: usize = 4096;
pub const MAX_METADATA_VALUE_BYTES: usize = 1024 * 1024;
/// Maximum bytes accepted in a predicate text, schema, summary-fact endpoint,
/// or artifact URI at the typed verifier boundary.
pub const MAX_CONTRACT_PREDICATE_TEXT_BYTES: usize = 1024 * 1024;
pub const MAX_EVIDENCE_ARTIFACT_URI_BYTES: usize = 16 * 1024;
pub const MAX_SUMMARY_FACT_FIELD_BYTES: usize = 16 * 1024;
/// Structural limits for programmatically-created contract JSON/typed trees.
pub const MAX_CONTRACT_PREDICATE_JSON_NODES: usize = 262_144;
pub const MAX_CONTRACT_PREDICATE_JSON_DEPTH: usize = 128;
pub const MAX_CONTRACT_PREDICATE_JSON_SCALAR_BYTES: usize = 16 * 1024 * 1024;
pub const MAX_TRUST_SPEC_BITVECTOR_WIDTH: u32 = 1_048_576;

/// Canonical wrapper binding exact producer bytes to their public proof role
/// and owning obligation.
pub const EVIDENCE_ARTIFACT_BINDING_ENVELOPE_SCHEMA: &str =
    "trust.evidence-artifact-binding-envelope.v1";
const EVIDENCE_ARTIFACT_BINDING_ENVELOPE_MAGIC: &[u8] =
    b"trust.evidence-artifact-binding-envelope.v1\0";

/// Schema version for full-verification run manifests consumed by dscan/dpub.
pub const RUN_MANIFEST_SCHEMA_VERSION: &str = "trust.verifier-run-manifest.v1";

/// Schema version for cross-crate summary facts consumed by verifier engines.
pub const SUMMARY_FACT_SCHEMA_VERSION: &str = "trust.summary-fact.v1";

/// Schema version for compiler-lowered int/bool specification predicates.
pub const TRUST_SPEC_PREDICATE_SCHEMA_VERSION: &str = "trust.spec-predicate.v1";

/// Schema version for typed obligation origin/context metadata entries.
pub const OBLIGATION_CONTEXT_SCHEMA_VERSION: &str = "trust.obligation-context.v1";

/// Metadata key for serialized [`SummaryFact`] values carried through legacy
/// metadata vectors.
pub const SUMMARY_FACT_METADATA_KEY: &str = "trust.summary_fact.v1";

/// Metadata key for serialized [`ObligationContext`] values carried through
/// obligation metadata without adding required public struct fields.
pub const OBLIGATION_CONTEXT_METADATA_KEY: &str = "trust.obligation_context.v1";

/// Current crate version, used by engine manifests as the API compatibility
/// major/minor/patch value.
pub const API_VERSION: &str = env!("CARGO_PKG_VERSION");

/// Default run identifier used by compatibility callers that do not yet carry
/// an execution context.
pub const DEFAULT_VERIFICATION_RUN_ID: &str = "trust-verification-run";

/// Contract data for one function, item, crate, or external artifact.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct TrustContractBundle {
    /// Stable schema marker for serialized verifier API bundles.
    #[serde(default = "default_schema_version")]
    pub schema_version: String,
    /// Stable bundle identifier generated by Trust or dpub.
    pub bundle_id: String,
    /// Source subject covered by this bundle.
    pub subject: BundleSubject,
    /// Contract clauses preserved by the compiler boundary.
    #[serde(deserialize_with = "deserialize_bounded_run_records")]
    pub contracts: Vec<TrustContract>,
    /// Compiler-owned proof items, such as native `proof fn`, preserved as
    /// proof artifacts rather than proc macro output or runtime functions.
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        deserialize_with = "deserialize_bounded_run_records"
    )]
    pub proof_items: Vec<TrustProofItem>,
    /// Verification obligations derived from the contracts and program facts.
    #[serde(deserialize_with = "deserialize_bounded_run_records")]
    pub obligations: Vec<TrustObligation>,
    /// Source and release metadata required by publication gates.
    pub publication: PublicationMetadata,
    /// Producer-specific bundle metadata. Engines may interpret documented,
    /// versioned proof-bearing keys; any such input is part of the semantic
    /// claim and must be authenticated by the producer/consumer boundary.
    /// Unknown keys remain audit-only and must not affect a proof verdict.
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        deserialize_with = "deserialize_bounded_bundle_metadata"
    )]
    pub metadata: Vec<MetadataEntry>,
}

/// Duplicate-free lookup table of canonical public-obligation semantic
/// digests.
///
/// Construct this through
/// [`TrustContractBundle::canonical_obligation_semantic_digest_index_sha256`].
/// The constructor validates the bundle and the exact requested subset once,
/// then resolves contract/proof-item references through prebuilt maps.  A
/// consumer can therefore reconcile a native batch without repeating an
/// O(bundle size) validation or reference scan for every obligation.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CanonicalObligationSemanticDigestIndex {
    digests: BTreeMap<String, String>,
}

impl CanonicalObligationSemanticDigestIndex {
    /// Return the lowercase raw SHA-256 digest for one public obligation ID.
    #[must_use]
    pub fn get(&self, obligation_id: &str) -> Option<&str> {
        self.digests.get(obligation_id).map(String::as_str)
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.digests.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.digests.is_empty()
    }
}

impl TrustContractBundle {
    /// Create an empty bundle for the given subject.
    #[must_use]
    pub fn empty(bundle_id: impl Into<String>, subject: BundleSubject) -> Self {
        Self {
            schema_version: SCHEMA_VERSION.to_string(),
            bundle_id: bundle_id.into(),
            subject,
            contracts: Vec::new(),
            proof_items: Vec::new(),
            obligations: Vec::new(),
            publication: PublicationMetadata::default(),
            metadata: Vec::new(),
        }
    }

    /// Returns true when the bundle carries no contracts or obligations.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.contracts.is_empty() && self.proof_items.is_empty() && self.obligations.is_empty()
    }

    /// Validate schema, identity domains, duplicate-free inventories, and
    /// bounded nested metadata before this bundle is handed to an engine.
    pub fn validate(&self) -> Result<(), String> {
        validate_contract_bundle(self)
    }

    /// Validate that a requested batch is an exact, duplicate-free subset of
    /// this bundle's canonical obligation inventory.
    ///
    /// Matching only `obligation_id` is insufficient: a caller must not be
    /// able to retain an ID while changing the kind, predicate metadata,
    /// required strength, or source identity handed to an engine.
    pub fn validate_requested_obligations(
        &self,
        requested: &[TrustObligation],
    ) -> Result<(), String> {
        self.validate()?;
        if requested.len() > self.obligations.len() {
            return Err(format!(
                "verifier request contains more obligations ({}) than bundle inventory ({})",
                requested.len(),
                self.obligations.len()
            ));
        }

        let canonical_by_id: FxHashMap<&str, &TrustObligation> = self
            .obligations
            .iter()
            .map(|obligation| (obligation.obligation_id.as_str(), obligation))
            .collect();
        let mut requested_ids = FxHashSet::default();
        for obligation in requested {
            validate_obligation_record(obligation)?;
            if !requested_ids.insert(obligation.obligation_id.as_str()) {
                return Err(
                    "verifier request contains duplicate requested obligation IDs".to_string()
                );
            }
            let Some(canonical) = canonical_by_id.get(obligation.obligation_id.as_str()) else {
                return Err(format!(
                    "verifier request obligation {} is not present in bundle {}",
                    obligation.obligation_id, self.bundle_id
                ));
            };
            if *canonical != obligation {
                return Err(format!(
                    "verifier request obligation {} differs from its canonical bundle record",
                    obligation.obligation_id
                ));
            }
        }
        Ok(())
    }

    /// Digest one exact canonical obligation together with the bundle context
    /// that gives its references meaning.
    ///
    /// Native proof transports use this instead of hashing an obligation ID.
    /// The digest includes the canonical obligation semantics, bundle identity
    /// and subject, and the complete referenced contract/proof item records.
    /// A dangling reference fails closed rather than degenerating to an
    /// ID-only binding.
    pub fn canonical_obligation_semantic_digest_sha256(
        &self,
        obligation: &TrustObligation,
    ) -> Result<String, String> {
        let index = self
            .canonical_obligation_semantic_digest_index_sha256(std::slice::from_ref(obligation))?;
        index.get(&obligation.obligation_id).map(str::to_string).ok_or_else(|| {
            format!(
                "canonical semantic digest index omitted requested obligation {}",
                obligation.obligation_id
            )
        })
    }

    /// Validate and digest an exact requested obligation subset in one pass.
    ///
    /// This is the batch form used by compiler emission and native-adapter
    /// validation. It rejects duplicate/substituted requests and dangling
    /// references, builds all identity maps once, and produces a deterministic
    /// O(log N) lookup index. Only references of the selected obligations are
    /// required to resolve; unrelated compatibility obligations may continue
    /// to use `proof_item_id` as a source identity without manufacturing a
    /// [`TrustProofItem`].
    pub fn canonical_obligation_semantic_digest_index_sha256(
        &self,
        requested: &[TrustObligation],
    ) -> Result<CanonicalObligationSemanticDigestIndex, String> {
        self.validate()?;
        if requested.len() > self.obligations.len() {
            return Err(format!(
                "verifier semantic-digest request contains more obligations ({}) than bundle inventory ({})",
                requested.len(),
                self.obligations.len()
            ));
        }

        let canonical_by_id: FxHashMap<&str, &TrustObligation> = self
            .obligations
            .iter()
            .map(|obligation| (obligation.obligation_id.as_str(), obligation))
            .collect();
        let contracts_by_id: FxHashMap<&str, &TrustContract> = self
            .contracts
            .iter()
            .map(|contract| (contract.contract_id.as_str(), contract))
            .collect();
        let proof_items_by_id: FxHashMap<&str, &TrustProofItem> = self
            .proof_items
            .iter()
            .map(|proof_item| (proof_item.proof_item_id.as_str(), proof_item))
            .collect();
        let mut requested_ids = FxHashSet::default();
        let mut digests = BTreeMap::new();

        for requested_obligation in requested {
            if !requested_ids.insert(requested_obligation.obligation_id.as_str()) {
                return Err("verifier semantic-digest request contains duplicate obligation IDs"
                    .to_string());
            }
            let Some(obligation) =
                canonical_by_id.get(requested_obligation.obligation_id.as_str()).copied()
            else {
                return Err(format!(
                    "verifier semantic-digest request obligation {} is not present in bundle {}",
                    requested_obligation.obligation_id, self.bundle_id
                ));
            };
            if obligation != requested_obligation {
                return Err(format!(
                    "verifier semantic-digest request obligation {} differs from its canonical bundle record",
                    requested_obligation.obligation_id
                ));
            }

            let contract = match obligation.contract_id.as_deref() {
                Some(contract_id) => Some(*contracts_by_id.get(contract_id).ok_or_else(|| {
                    format!(
                        "public obligation {} references missing contract {contract_id}",
                        obligation.obligation_id
                    )
                })?),
                None => None,
            };
            let proof_item = match obligation.proof_item_id.as_deref() {
                Some(proof_item_id) => {
                    Some(*proof_items_by_id.get(proof_item_id).ok_or_else(|| {
                        format!(
                            "public obligation {} references missing proof item {proof_item_id}",
                            obligation.obligation_id
                        )
                    })?)
                }
                None => None,
            };

            digests.insert(
                obligation.obligation_id.clone(),
                self.canonical_obligation_context_digest_sha256(obligation, contract, proof_item)?,
            );
        }

        Ok(CanonicalObligationSemanticDigestIndex { digests })
    }

    fn canonical_obligation_context_digest_sha256(
        &self,
        obligation: &TrustObligation,
        contract: Option<&TrustContract>,
        proof_item: Option<&TrustProofItem>,
    ) -> Result<String, String> {
        #[derive(Serialize)]
        struct CanonicalObligationContext<'a> {
            schema: &'static str,
            verifier_schema: &'a str,
            bundle_id: &'a str,
            subject: &'a BundleSubject,
            obligation_digest: String,
            contract: Option<TrustContract>,
            proof_item: Option<TrustProofItem>,
        }

        let mut contract = contract.cloned();
        if let Some(contract) = &mut contract {
            canonicalize_contract_for_semantic_digest(contract);
        }
        let mut proof_item = proof_item.cloned();
        if let Some(proof_item) = &mut proof_item {
            proof_item.contracts.sort_by(|left, right| left.contract_id.cmp(&right.contract_id));
            for contract in &mut proof_item.contracts {
                canonicalize_contract_for_semantic_digest(contract);
            }
            sort_metadata_entries(&mut proof_item.metadata);
        }

        let canonical = CanonicalObligationContext {
            schema: PUBLIC_OBLIGATION_SEMANTIC_DIGEST_SCHEMA,
            verifier_schema: &self.schema_version,
            bundle_id: &self.bundle_id,
            subject: &self.subject,
            obligation_digest: obligation.canonical_semantic_digest_sha256_unchecked()?,
            contract,
            proof_item,
        };
        let mut canonical = serde_json::to_value(&canonical).map_err(|error| {
            format!("failed to serialize canonical public obligation context: {error}")
        })?;
        canonicalize_json_in_place(&mut canonical);
        let payload = serde_json::to_vec(&canonical).map_err(|error| {
            format!("failed to encode canonical public obligation context: {error}")
        })?;
        let mut material = PUBLIC_OBLIGATION_SEMANTIC_DIGEST_SCHEMA.as_bytes().to_vec();
        material.extend_from_slice(b".bundle-context\0");
        material.extend_from_slice(&payload);
        Ok(stable_sha256_hex(&material))
    }

    /// Parse an untrusted JSON bundle through the whole-envelope byte cap and
    /// the bundle's custom validated deserializer.
    pub fn from_json_slice(bytes: &[u8]) -> Result<Self, String> {
        validate_json_envelope_length(bytes.len(), "contract bundle")?;
        serde_json::from_slice(bytes).map_err(|error| error.to_string())
    }
}

impl<'de> Deserialize<'de> for TrustContractBundle {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        struct Helper {
            #[serde(default = "default_schema_version")]
            schema_version: String,
            bundle_id: String,
            subject: BundleSubject,
            #[serde(deserialize_with = "deserialize_bounded_run_records")]
            contracts: Vec<TrustContract>,
            #[serde(default, deserialize_with = "deserialize_bounded_run_records")]
            proof_items: Vec<TrustProofItem>,
            #[serde(deserialize_with = "deserialize_bounded_run_records")]
            obligations: Vec<TrustObligation>,
            publication: PublicationMetadata,
            #[serde(default, deserialize_with = "deserialize_bounded_bundle_metadata")]
            metadata: Vec<MetadataEntry>,
        }

        let helper = Helper::deserialize(deserializer)?;
        let bundle = Self {
            schema_version: helper.schema_version,
            bundle_id: helper.bundle_id,
            subject: helper.subject,
            contracts: helper.contracts,
            proof_items: helper.proof_items,
            obligations: helper.obligations,
            publication: helper.publication,
            metadata: helper.metadata,
        };
        bundle.validate().map_err(de::Error::custom)?;
        Ok(bundle)
    }
}

fn default_schema_version() -> String {
    SCHEMA_VERSION.to_string()
}

/// Source subject covered by a contract bundle.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BundleSubject {
    Crate { name: String },
    Function { crate_name: String, path: String },
    Artifact { name: String, kind: String },
}

/// R4 §1 typed-citation lane (seam map step 2; design note
/// 2026-07-22-r4-remaining-lanes-design.md §1a): a contract clause whose
/// predicate cites a Clean-island definition carries the citation on the
/// clause's `metadata` channel under these keys, alongside the (unchanged)
/// `ContractPredicate::Unsupported` payload. Metadata is INERT to verdicts
/// by standing doctrine (the refutation-witness lane's dual-run
/// discriminator pin established it): nothing may upgrade a verdict from
/// these entries until the discharge consumer validates the citation
/// against the island environment and unfolds it KERNEL-side
/// (`trust_certify::clean_island::unfold_island_application`) — never by
/// textual expansion into the machine snippet lane, which the
/// `e9_island_call_divergence_battery` pin forbids.
pub const ISLAND_CITATION_NAME_METADATA_KEY: &str = "trust.island_citation.name";
/// The cited definition's certificate digest at mint time; the discharge
/// consumer must recompute and match it against the session environment
/// before unfolding (the E6/E9 digest-binding pattern).
pub const ISLAND_CITATION_DIGEST_METADATA_KEY: &str = "trust.island_citation.digest";

/// One Trust contract clause in the public API form.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustContract {
    pub contract_id: String,
    pub kind: ContractKind,
    pub predicate: ContractPredicate,
    pub source: SourceLocation,
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        deserialize_with = "deserialize_bounded_record_metadata"
    )]
    pub metadata: Vec<MetadataEntry>,
}

/// Contract role.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ContractKind {
    Requires,
    Ensures,
    Invariant,
    LoopInvariant,
    Assumes,
    Asserts,
    Refinement,
    Temporal,
}

/// Predicate payload accepted at the public boundary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ContractPredicate {
    /// Stable textual Trust expression.
    TrustExpr { text: String },
    /// Canonical typed Trust expression IR. This is the preferred lossless
    /// compiler-owned representation for first-class contracts.
    TrustIr { schema: String, value: serde_json::Value },
    /// Canonical math formula IR for SMT/CHC-oriented engines.
    MathIr { schema: String, value: serde_json::Value },
    /// Canonical memory/provenance formula IR for ownership engines.
    MemoryIr { schema: String, value: serde_json::Value },
    /// Reference to an explicit temporal model artifact.
    TemporalModelRef { uri: String, hash: ArtifactHash },
    /// Canonical JSON IR for engines that already share a richer encoding.
    CanonicalJson { schema: String, value: serde_json::Value },
    /// Compiler found a contract but could not lower it without loss.
    Unsupported { reason: String },
}

/// Compiler-lowered int/bool specification predicate.
///
/// This is the stable TrustIr payload for `#[requires]`, `#[ensures]`, and
/// related contracts after the compiler has produced a typed `SpecExpr` tree.
/// Engines must use `root` and `variables` as proof input; source text and
/// debug strings are intentionally not part of this canonical schema.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustSpecPredicate {
    #[serde(default = "default_trust_spec_predicate_schema_version")]
    pub schema_version: String,
    pub root: TrustSpecExpr,
    pub root_sort: TrustSpecSort,
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        deserialize_with = "deserialize_bounded_record_items"
    )]
    pub variables: Vec<TrustSpecVariable>,
}

impl TrustSpecPredicate {
    /// Build a predicate rooted at a typed boolean expression.
    #[must_use]
    pub fn new(root: TrustSpecExpr, variables: Vec<TrustSpecVariable>) -> Self {
        Self {
            schema_version: TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
            root_sort: root.sort,
            root,
            variables,
        }
    }

    /// Returns true when this predicate uses the current stable schema marker.
    #[must_use]
    pub fn has_current_schema(&self) -> bool {
        self.schema_version == TRUST_SPEC_PREDICATE_SCHEMA_VERSION
    }

    /// Validate the complete canonical typed-predicate schema.
    ///
    /// This is the public accessor over the same checker used by bundle
    /// validation. Native adapters must call it after decoding predicates from
    /// metadata: merely deserializing and lowering an expression is not enough.
    /// Duplicate declarations, non-canonical literals, undeclared variables,
    /// and inconsistent node sorts must fail before solver invocation.
    pub fn validate(&self) -> Result<(), String> {
        validate_trust_spec_predicate(self)
    }

    /// Encode this predicate as the preferred public contract predicate form.
    pub fn into_contract_predicate(self) -> Result<ContractPredicate, serde_json::Error> {
        Ok(ContractPredicate::TrustIr {
            schema: TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
            value: serde_json::to_value(self)?,
        })
    }

    /// Decode a typed Trust spec predicate from a public contract predicate.
    ///
    /// Returns `Ok(None)` for unrelated predicate schemas.
    pub fn from_contract_predicate(
        predicate: &ContractPredicate,
    ) -> Result<Option<Self>, serde_json::Error> {
        match predicate {
            ContractPredicate::TrustIr { schema, value }
            | ContractPredicate::CanonicalJson { schema, value }
                if schema == TRUST_SPEC_PREDICATE_SCHEMA_VERSION =>
            {
                serde_json::from_value(value.clone()).map(Some)
            }
            _ => Ok(None),
        }
    }
}

fn default_trust_spec_predicate_schema_version() -> String {
    TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string()
}

/// Sorts supported by the stable compiler-lowered specification predicate IR.
///
/// The `Array` arm is an additive v1 capability with a deliberately closed
/// shape: indices are mathematical integers and elements are scalar. Existing
/// scalar v1 JSON is byte-for-byte unchanged; older readers reject the new
/// enum arm during deserialization, which is the required fail-closed behavior
/// rather than a semantic reinterpretation of an old payload.
///
/// The `Float` arm is likewise additive v1 (same precedent as `BitVec` and
/// `Array`: no schema-version bump; older readers fail closed on the unknown
/// enum arm during deserialization). Its fragment is deliberately minimal:
/// IEEE-754 literals, variables, and comparisons only. Float ARITHMETIC
/// (`Add`/`Sub`/`Mul`/`Div`/`Neg`, …) stays rejected by validation because it
/// would require rounding-mode semantics this IR does not carry.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", deny_unknown_fields)]
pub enum TrustSpecSort {
    Bool,
    Int,
    /// Fixed-width bitvector of `width` bits (machine-integer / overflow VCs).
    BitVec {
        width: u32,
    },
    /// Read-only SMT array with an implicit `Int` index sort and scalar values.
    Array {
        element: TrustSpecScalarSort,
    },
    /// IEEE-754 binary floating point with `eb` exponent bits and `sb`
    /// significand bits (including the hidden bit), matching the
    /// `trust-types` `Sort::Float { eb, sb }` representation. Only the two
    /// Rust machine shapes are valid: `f32` = `{ eb: 8, sb: 24 }` and
    /// `f64` = `{ eb: 11, sb: 53 }`; validation rejects every other shape
    /// fail-closed (mirroring the bounded `BitVec` width rule).
    Float {
        eb: u32,
        sb: u32,
    },
}

/// Scalar element sorts admitted by [`TrustSpecSort::Array`].
///
/// Keeping this separate from `TrustSpecSort` makes the public sort `Copy` and
/// makes nested arrays unrepresentable by construction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", deny_unknown_fields)]
pub enum TrustSpecScalarSort {
    Bool,
    Int,
    BitVec {
        width: u32,
    },
}

impl TrustSpecScalarSort {
    /// Return the corresponding scalar expression sort.
    #[must_use]
    pub const fn expression_sort(self) -> TrustSpecSort {
        match self {
            Self::Bool => TrustSpecSort::Bool,
            Self::Int => TrustSpecSort::Int,
            Self::BitVec { width } => TrustSpecSort::BitVec { width },
        }
    }
}

/// One typed expression node in a compiler-lowered specification predicate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustSpecExpr {
    pub sort: TrustSpecSort,
    pub kind: TrustSpecExprKind,
}

impl TrustSpecExpr {
    #[must_use]
    pub fn bool_literal(value: bool) -> Self {
        Self { sort: TrustSpecSort::Bool, kind: TrustSpecExprKind::BoolLiteral { value } }
    }

    #[must_use]
    pub fn int_literal(value: impl Into<String>) -> Self {
        Self {
            sort: TrustSpecSort::Int,
            kind: TrustSpecExprKind::IntLiteral { value: value.into() },
        }
    }

    #[must_use]
    pub fn variable(name: impl Into<String>, sort: TrustSpecSort) -> Self {
        Self { sort, kind: TrustSpecExprKind::Variable { name: name.into() } }
    }

    #[must_use]
    pub fn result(sort: TrustSpecSort) -> Self {
        Self { sort, kind: TrustSpecExprKind::Result }
    }

    #[must_use]
    pub fn unary(op: TrustSpecUnaryOp, expr: TrustSpecExpr) -> Self {
        let sort = match op {
            TrustSpecUnaryOp::Not => TrustSpecSort::Bool,
            TrustSpecUnaryOp::Neg => TrustSpecSort::Int,
        };
        Self { sort, kind: TrustSpecExprKind::Unary { op, expr: Box::new(expr) } }
    }

    #[must_use]
    pub fn binary(op: TrustSpecBinaryOp, lhs: TrustSpecExpr, rhs: TrustSpecExpr) -> Self {
        Self {
            sort: op.result_sort(),
            kind: TrustSpecExprKind::Binary { op, lhs: Box::new(lhs), rhs: Box::new(rhs) },
        }
    }

    #[must_use]
    pub fn old(expr: TrustSpecExpr) -> Self {
        Self { sort: expr.sort, kind: TrustSpecExprKind::Old { expr: Box::new(expr) } }
    }

    #[must_use]
    pub fn field(base: TrustSpecExpr, field: impl Into<String>, sort: TrustSpecSort) -> Self {
        Self { sort, kind: TrustSpecExprKind::Field { base: Box::new(base), field: field.into() } }
    }

    #[must_use]
    pub fn index(base: TrustSpecExpr, index: TrustSpecExpr, sort: TrustSpecSort) -> Self {
        Self {
            sort,
            kind: TrustSpecExprKind::Index { base: Box::new(base), index: Box::new(index) },
        }
    }

    #[must_use]
    pub fn bitvec_literal(value: impl Into<String>, width: u32) -> Self {
        Self {
            sort: TrustSpecSort::BitVec { width },
            kind: TrustSpecExprKind::BitVecLiteral { value: value.into(), width },
        }
    }

    /// IEEE-754 float constant carried as its raw interchange-format bits
    /// (`f64::to_bits`-style; for `f32` the low 32 bits) — never a decimal
    /// string round-trip, so every payload including NaNs and signed zeros is
    /// preserved exactly. `eb`/`sb` fix the format; only the `f32`/`f64`
    /// shapes validate.
    #[must_use]
    pub fn float_literal(bits: u64, eb: u32, sb: u32) -> Self {
        Self {
            sort: TrustSpecSort::Float { eb, sb },
            kind: TrustSpecExprKind::FloatLiteral { bits, eb, sb },
        }
    }

    #[must_use]
    pub fn bv_unary(op: TrustSpecBvUnaryOp, expr: TrustSpecExpr, width: u32) -> Self {
        Self {
            sort: TrustSpecSort::BitVec { width },
            kind: TrustSpecExprKind::BvUnary { op, expr: Box::new(expr), width },
        }
    }

    #[must_use]
    pub fn bv_binary(
        op: TrustSpecBvBinaryOp,
        lhs: TrustSpecExpr,
        rhs: TrustSpecExpr,
        width: u32,
    ) -> Self {
        Self {
            sort: op.result_sort(width),
            kind: TrustSpecExprKind::BvBinary { op, lhs: Box::new(lhs), rhs: Box::new(rhs), width },
        }
    }

    /// Integer→bitvector conversion (`int2bv`): result is a `width`-bit
    /// bitvector holding the low `width` bits of the integer's two's-complement
    /// representation. Faithful to SMT-LIB `int2bv` and to `Formula::IntToBv`
    /// (see `trust-types` `ay_bridge::formula_to_expr`, the reference lowering).
    #[must_use]
    pub fn bv_from_int(expr: TrustSpecExpr, width: u32) -> Self {
        Self {
            sort: TrustSpecSort::BitVec { width },
            kind: TrustSpecExprKind::BvFromInt { expr: Box::new(expr), width },
        }
    }

    /// Bitvector→integer conversion: `bv2nat` (unsigned magnitude) when
    /// `signed == false`, signed two's-complement value when `signed == true`.
    /// Result is `Int`; `width` is the operand bit width. Mirrors
    /// `Formula::BvToInt` (whose `signed` flag this preserves — a signed/unsigned
    /// mismatch here silently corrupts the value, so it is threaded through).
    #[must_use]
    pub fn int_from_bv(expr: TrustSpecExpr, signed: bool, width: u32) -> Self {
        Self {
            sort: TrustSpecSort::Int,
            kind: TrustSpecExprKind::IntFromBv { expr: Box::new(expr), signed, width },
        }
    }

    #[must_use]
    pub fn quantifier(
        quantifier: TrustSpecQuantifier,
        variable: impl Into<String>,
        variable_sort: TrustSpecSort,
        body: TrustSpecExpr,
    ) -> Self {
        Self {
            sort: TrustSpecSort::Bool,
            kind: TrustSpecExprKind::Quantifier {
                quantifier,
                variable: variable.into(),
                variable_sort,
                body: Box::new(body),
            },
        }
    }

    /// Enum discriminant test: `true` iff `scrutinee`'s active variant is
    /// `variant` (e.g. `is_ok(r)` ≙ `is_variant(r, "Ok")`). Models a
    /// `matches!`/pattern discriminant check; the engine encodes it as the SMT
    /// datatype discriminant tester. Bool-sorted. (#2/#4 closure-WP: lets the
    /// spec-AST represent the producers'/checker's `matches!`-on-`Result`
    /// postcondition. Encoding is added in trust-wp-core; until then external
    /// consumers fail-closed on it via the `#[non_exhaustive]` catch-all.)
    #[must_use]
    pub fn is_variant(scrutinee: TrustSpecExpr, variant: impl Into<String>) -> Self {
        Self {
            sort: TrustSpecSort::Bool,
            kind: TrustSpecExprKind::IsVariant {
                scrutinee: Box::new(scrutinee),
                variant: variant.into(),
            },
        }
    }

    /// Projection of variant `variant`'s field `field` from `scrutinee` (e.g. the
    /// `Ok` payload `c` ≙ `variant_field(r, "Ok", 0, Int)`). Sound only where the
    /// matching `is_variant` holds (the guard binds it); the engine encodes it as
    /// the SMT datatype field accessor.
    #[must_use]
    pub fn variant_field(
        scrutinee: TrustSpecExpr,
        variant: impl Into<String>,
        field: u32,
        sort: TrustSpecSort,
    ) -> Self {
        Self {
            sort,
            kind: TrustSpecExprKind::VariantField {
                scrutinee: Box::new(scrutinee),
                variant: variant.into(),
                field,
            },
        }
    }
}

/// Stable expression node kinds for [`TrustSpecExpr`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "node", rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustSpecExprKind {
    BoolLiteral {
        value: bool,
    },
    IntLiteral {
        value: String,
    },
    Variable {
        name: String,
    },
    Result,
    Unary {
        op: TrustSpecUnaryOp,
        expr: Box<TrustSpecExpr>,
    },
    Binary {
        op: TrustSpecBinaryOp,
        lhs: Box<TrustSpecExpr>,
        rhs: Box<TrustSpecExpr>,
    },
    Old {
        expr: Box<TrustSpecExpr>,
    },
    Field {
        base: Box<TrustSpecExpr>,
        field: String,
    },
    Index {
        base: Box<TrustSpecExpr>,
        index: Box<TrustSpecExpr>,
    },
    Quantifier {
        quantifier: TrustSpecQuantifier,
        variable: String,
        variable_sort: TrustSpecSort,
        body: Box<TrustSpecExpr>,
    },
    /// Fixed-width bitvector constant; `value` is the decimal magnitude.
    BitVecLiteral {
        value: String,
        width: u32,
    },
    /// IEEE-754 float constant carried as raw interchange-format bits (the
    /// `eb + sb`-bit encoding; high bits above that width must be zero).
    /// Bits are bits: NaN payloads and signed zeros are representational,
    /// never normalized. Built via [`TrustSpecExpr::float_literal`].
    FloatLiteral {
        bits: u64,
        eb: u32,
        sb: u32,
    },
    /// Bitvector unary op; `width` is the operand/result bit width.
    BvUnary {
        op: TrustSpecBvUnaryOp,
        expr: Box<TrustSpecExpr>,
        width: u32,
    },
    /// Bitvector binary op; `width` is the operand bit width. Result sort is a
    /// `width`-bit bitvector for arithmetic/bitwise/shift ops and `Bool` for
    /// the unsigned comparison ops.
    BvBinary {
        op: TrustSpecBvBinaryOp,
        lhs: Box<TrustSpecExpr>,
        rhs: Box<TrustSpecExpr>,
        width: u32,
    },
    /// Integer→bitvector conversion (`int2bv`); result is a `width`-bit
    /// bitvector. Built via [`TrustSpecExpr::bv_from_int`].
    BvFromInt {
        expr: Box<TrustSpecExpr>,
        width: u32,
    },
    /// Bitvector→integer conversion (`bv2nat` unsigned, or signed two's-complement
    /// when `signed`); result is `Int`. `width` is the operand bit width. Built
    /// via [`TrustSpecExpr::int_from_bv`].
    IntFromBv {
        expr: Box<TrustSpecExpr>,
        signed: bool,
        width: u32,
    },
    /// Enum discriminant test (`matches!`/pattern): true iff `scrutinee`'s active
    /// variant is `variant`. Bool-sorted. Built via [`TrustSpecExpr::is_variant`].
    /// Encoded as the SMT datatype discriminant tester (trust-wp-core).
    IsVariant {
        scrutinee: Box<TrustSpecExpr>,
        variant: String,
    },
    /// Projection of variant `variant`'s `field`-th payload from `scrutinee`
    /// (sound under the matching `IsVariant`). Built via
    /// [`TrustSpecExpr::variant_field`]. Encoded as the SMT datatype field accessor.
    VariantField {
        scrutinee: Box<TrustSpecExpr>,
        variant: String,
        field: u32,
    },
}

/// Unary operators supported by the compiler-lowered specification predicate IR.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustSpecUnaryOp {
    Not,
    Neg,
}

/// Binary operators supported by the compiler-lowered specification predicate IR.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustSpecBinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
    Implies,
}

impl TrustSpecBinaryOp {
    #[must_use]
    pub fn result_sort(self) -> TrustSpecSort {
        match self {
            Self::Add | Self::Sub | Self::Mul | Self::Div | Self::Mod => TrustSpecSort::Int,
            Self::Eq
            | Self::Ne
            | Self::Lt
            | Self::Le
            | Self::Gt
            | Self::Ge
            | Self::And
            | Self::Or
            | Self::Implies => TrustSpecSort::Bool,
        }
    }
}

/// Bitvector unary operators supported by the compiler-lowered specification IR.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustSpecBvUnaryOp {
    /// Bitwise complement (`bvnot`).
    Not,
    /// Sign extension by `extend_by` bits (`sign_extend`; result width =
    /// operand width + `extend_by`).
    SignExt { extend_by: u32 },
    /// Inclusive bit slice `[high:low]` (`extract`; result width =
    /// `high - low + 1`).
    Extract { high: u32, low: u32 },
}

/// Bitvector binary operators supported by the compiler-lowered specification IR.
///
/// All arithmetic/bitwise/shift operators have a bitvector result of the
/// operand width; the unsigned comparison operators have a `Bool` result.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustSpecBvBinaryOp {
    Add,
    Sub,
    Mul,
    Udiv,
    Urem,
    And,
    Or,
    Xor,
    Shl,
    Lshr,
    Ashr,
    Ult,
    Ule,
    Ugt,
    Uge,
    Slt,
    Sle,
}

impl TrustSpecBvBinaryOp {
    /// Result sort for this operator given the operand bit `width`.
    #[must_use]
    pub fn result_sort(self, width: u32) -> TrustSpecSort {
        match self {
            Self::Add
            | Self::Sub
            | Self::Mul
            | Self::Udiv
            | Self::Urem
            | Self::And
            | Self::Or
            | Self::Xor
            | Self::Shl
            | Self::Lshr
            | Self::Ashr => TrustSpecSort::BitVec { width },
            Self::Ult | Self::Ule | Self::Ugt | Self::Uge | Self::Slt | Self::Sle => {
                TrustSpecSort::Bool
            }
        }
    }
}

/// Quantifier kinds supported by the compiler-lowered specification predicate IR.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustSpecQuantifier {
    Forall,
    Exists,
}

/// Typed variable metadata used by [`TrustSpecPredicate`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustSpecVariable {
    pub name: String,
    pub sort: TrustSpecSort,
    pub origin: TrustSpecVariableOrigin,
}

// `TrustSpecVariableOrigin` is defined in trust-ir-contract and re-exported above.

/// One compiler-owned proof item exposed to verifier engines.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustProofItem {
    pub proof_item_id: String,
    pub name: String,
    pub kind: ProofItemKind,
    pub target: ProofItemTarget,
    pub signature: ProofItemSignature,
    pub body: ProofItemBody,
    pub source: SourceLocation,
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        deserialize_with = "deserialize_bounded_record_items"
    )]
    pub contracts: Vec<TrustContract>,
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        deserialize_with = "deserialize_bounded_record_metadata"
    )]
    pub metadata: Vec<MetadataEntry>,
}

impl TrustProofItem {
    /// Native proof items are verification-only and must not be emitted as code.
    #[must_use]
    pub fn is_runtime_erased(&self) -> bool {
        matches!(self.kind, ProofItemKind::ProofFn | ProofItemKind::Lemma)
    }
}

/// Proof item role.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ProofItemKind {
    ProofFn,
    Lemma,
}

/// Subject a proof item supports.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ProofItemTarget {
    LocalNamespace,
    Function { crate_name: String, path: String },
    Contract { contract_id: String },
    Crate { name: String },
}

/// Typed proof item signature in the public verifier API.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct ProofItemSignature {
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        deserialize_with = "deserialize_bounded_record_items"
    )]
    pub params: Vec<ProofItemParam>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub output: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofItemParam {
    pub name: Option<String>,
    pub ty: String,
}

/// Verification-only proof body representation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ProofItemBody {
    CompilerOwned { body_ref: String },
    NativeScript { engine: String, text: String },
    Unsupported { reason: String },
}

/// Metadata key marking the synthetic per-function trust-mc "default function"
/// admission obligation.
///
/// Trust: This obligation does NOT represent a real safety property. It carries
/// the goal `bool_literal(false)` and is injected solely to anchor native
/// trust-IR / typed-CHC bundle construction for functions that have no real
/// routable obligations. Its "proof" is vacuous by construction (the CHC error
/// query is UNSAT regardless of the function's behavior), so counting it as a
/// proved obligation manufactures false confidence. Every count, verdict, and
/// report MUST exclude obligations carrying this key. See
/// [`TrustObligation::is_default_admission`].
pub const TRUST_MC_DEFAULT_FUNCTION_OBLIGATION_METADATA_KEY: &str =
    "trust-trust-mc.default-function-obligation.v1";
/// Exact value for the compiler-authored synthetic admission marker. A mere
/// key match is never sufficient to erase an obligation from accounting.
pub const TRUST_MC_DEFAULT_FUNCTION_OBLIGATION_METADATA_VALUE: &str =
    "synthetic-trust-mc-default-function-admission-v1";

const TRUST_MC_DEFAULT_FUNCTION_OBLIGATION_ID_PREFIX: &str = "vc:";
const TRUST_MC_DEFAULT_FUNCTION_OBLIGATION_ID_SUFFIX: &str = ":trust_mc_default_function:0";
const TRUST_MC_DEFAULT_FUNCTION_DESCRIPTION: &str = "default trust-mc typed CHC function admission";
const TRUST_VC_KIND_METADATA_KEY: &str = "trust.vc.kind";
const TRUST_MC_DEFAULT_FUNCTION_VC_KIND: &str = "trust_mc_default_function";
const TRUST_SOURCE_DIGEST_METADATA_KEY: &str = "trust.mir-extract.source.digest.sha256";
const TRUST_VC_DIGEST_METADATA_KEY: &str = "trust.vc.digest.sha256";
const TRUST_VC_FORMULA_SCHEMA_METADATA_KEY: &str = "trust.vc.formula.schema";
const TRUST_VC_FORMULA_SORT_METADATA_KEY: &str = "trust.vc.formula.sort";
const TRUST_VC_FORMULA_SMTLIB_METADATA_KEY: &str = "trust.vc.formula.smtlib2";
const TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY: &str = "trust.vc.formula.payload";
const TRUST_MC_FORMULA_SCHEMA_METADATA_KEY: &str = "trust.vc.engine.trust-mc.formula_schema";

/// Domain used for the canonical semantics digest that binds a native proof
/// carrier to one exact public verifier obligation.
///
/// Native transport annotations are deliberately excluded from this digest:
/// the compiler can only derive their request, replay, and certificate digests
/// after it has built the native bundle whose proof formula carries this value.
/// Every semantic input that exists before that transport step remains covered,
/// including kind, source, required strength, summary facts, and typed
/// proof-unit/predicate metadata.
pub const PUBLIC_OBLIGATION_SEMANTIC_DIGEST_SCHEMA: &str =
    "trust.verifier-api.public-obligation-semantics.v1";

/// Metadata namespace added after a public obligation has been embedded in a
/// native Trust-IR bundle. Entries in this namespace are transport bindings,
/// not part of the pre-transport public claim.
pub const TRUST_IR_NATIVE_TRANSPORT_METADATA_PREFIX: &str = "trust.trust_ir.native.";

/// Compiler-owned post-lowering annotations excluded from the pre-transport
/// public-obligation semantic digest.
///
/// The allow-list is intentionally exact. An unknown key under the native
/// namespace remains covered by the digest, so extending the transport cannot
/// silently create a new unauthenticated field. Suite-specific legacy spellings
/// are listed individually below; there is no prefix exemption for them.
pub const TRUST_IR_NATIVE_TRANSPORT_METADATA_KEYS: &[&str] = &[
    "trust.trust_ir.native.proof_unit.v1",
    "trust.trust_ir.native.verifier_suite",
    "trust.trust_ir.native.request_id",
    "trust.trust_ir.native.proof_obligation_id",
    "trust.trust_ir.native.assertion_id",
    "trust.trust_ir.native.trust_ir_module_digest",
    "trust.trust_ir.native.request_digest",
    "trust.trust_ir.native.evidence_digest",
    "trust.trust_ir.native.certificate_digest",
    "trust.trust_ir.native.compiler_facts_digest",
    "trust.trust_ir.native.obligation_source_digest",
    "trust.trust_ir.native.replay_engine",
    "trust.trust_ir.native.replay_invocation",
    "trust.trust_ir.native.replay_transcript_digest",
    "trust.trust_ir.native.artifact_fingerprint",
    "trust.trust_ir.native.transport_status",
    "trust.trust_ir.native.unsupported_reason",
    // trust-wp replay context regenerated from the validated native bundle.
    "trust.trust-wp.native-origin.v1",
    "trust.trust-wp.claim-digest.v1",
    "trust.trust-wp.tmir-source-span.v1",
    "trust.trust-wp.native-verifier.v1",
    "trust.trust-wp.native-replay.v1",
    "trust.trust-wp.native-solver.v1",
    "trust.trust-wp.tmir-obligation-source.v1",
    "trust.trust-wp.proof-context.v1",
    "trust.trust-wp.summary-fact.v1",
    // Compiler-derived native solver inputs and their exact binding records.
    // These are deliberately not public source semantics: the native module's
    // typed obligation-source identity binds the pre-transport public claim,
    // while adapters validate these records against the supplied bundle.
    "trust-trust-wp.typed-formula.synthetic_contract.v1",
    "trust-trust-mc.typed-chc-obligation.synthetic_contract.v1",
    "trust-mc.typed-chc-obligation.binding.v1",
    "trust-mc.typed-chc-obligation.source_digest.sha256",
    "trust-mc.typed-chc-obligation.vc_digest.sha256",
    "trust-mc.typed-chc-obligation.synthetic_digest.sha256",
];

#[must_use]
pub fn is_trust_ir_native_transport_metadata_key(key: &str) -> bool {
    TRUST_IR_NATIVE_TRANSPORT_METADATA_KEYS.contains(&key)
}

/// One verification obligation derived from contracts or compiler checks.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustObligation {
    pub obligation_id: String,
    pub kind: ObligationKind,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub contract_id: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_item_id: Option<String>,
    pub source: SourceLocation,
    pub description: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub required_strength: Option<ProofStrength>,
    /// Hash-addressed summary facts available to native verifier replay.
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        deserialize_with = "deserialize_bounded_record_items"
    )]
    pub summary_facts: Vec<SummaryFact>,
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        deserialize_with = "deserialize_bounded_record_metadata"
    )]
    pub metadata: Vec<MetadataEntry>,
}

impl TrustObligation {
    /// True if this is the synthetic trust-mc per-function admission, which is
    /// not a real safety obligation and must be excluded from every count,
    /// verdict, and report. See
    /// [`TRUST_MC_DEFAULT_FUNCTION_OBLIGATION_METADATA_KEY`].
    #[must_use]
    pub fn is_default_admission(&self) -> bool {
        default_admission_identity_is_exact(self)
    }

    /// Return the deterministic SHA-256 digest of this obligation's canonical
    /// public semantics before native transport annotations are attached.
    ///
    /// This is the cross-boundary binding used by compiler-emitted Trust-IR
    /// proof formulas and native verifier adapters. Metadata and summary facts
    /// are sorted by their canonical identities so producer insertion order
    /// cannot change the digest. Validation rejects duplicate metadata keys
    /// before hashing so no ambiguous key/value interpretation can cross the
    /// public-to-native boundary.
    pub fn canonical_semantic_digest_sha256(&self) -> Result<String, String> {
        validate_obligation_record(self)?;
        self.canonical_semantic_digest_sha256_unchecked()
    }

    fn canonical_semantic_digest_sha256_unchecked(&self) -> Result<String, String> {
        let mut summary_facts: Vec<&SummaryFact> = self.summary_facts.iter().collect();
        summary_facts.sort_by(|left, right| left.id.cmp(&right.id));
        let mut metadata: Vec<&MetadataEntry> = self
            .metadata
            .iter()
            .filter(|entry| !is_trust_ir_native_transport_metadata_key(&entry.key))
            .collect();
        metadata.sort_by(|left, right| {
            (left.key.as_str(), left.value.as_str())
                .cmp(&(right.key.as_str(), right.value.as_str()))
        });

        #[derive(Serialize)]
        struct CanonicalPublicObligation<'a> {
            schema: &'static str,
            obligation_id: &'a str,
            kind: &'a ObligationKind,
            contract_id: &'a Option<String>,
            proof_item_id: &'a Option<String>,
            source: &'a SourceLocation,
            description: &'a str,
            required_strength: &'a Option<ProofStrength>,
            summary_facts: Vec<&'a SummaryFact>,
            metadata: Vec<&'a MetadataEntry>,
        }

        let canonical = CanonicalPublicObligation {
            schema: PUBLIC_OBLIGATION_SEMANTIC_DIGEST_SCHEMA,
            obligation_id: &self.obligation_id,
            kind: &self.kind,
            contract_id: &self.contract_id,
            proof_item_id: &self.proof_item_id,
            source: &self.source,
            description: &self.description,
            required_strength: &self.required_strength,
            summary_facts,
            metadata,
        };
        let mut canonical = serde_json::to_value(&canonical).map_err(|error| {
            format!("failed to serialize canonical public obligation semantics: {error}")
        })?;
        canonicalize_json_in_place(&mut canonical);
        let payload = serde_json::to_vec(&canonical).map_err(|error| {
            format!("failed to encode canonical public obligation semantics: {error}")
        })?;
        let mut material = PUBLIC_OBLIGATION_SEMANTIC_DIGEST_SCHEMA.as_bytes().to_vec();
        material.push(0);
        material.extend_from_slice(&payload);
        Ok(stable_sha256_hex(&material))
    }
}

fn sort_metadata_entries(metadata: &mut [MetadataEntry]) {
    metadata.sort_by(|left, right| {
        (left.key.as_str(), left.value.as_str()).cmp(&(right.key.as_str(), right.value.as_str()))
    });
}

fn canonicalize_contract_for_semantic_digest(contract: &mut TrustContract) {
    sort_metadata_entries(&mut contract.metadata);
}

fn default_admission_identity_is_exact(obligation: &TrustObligation) -> bool {
    let Some(function_fragment) = obligation
        .obligation_id
        .strip_prefix(TRUST_MC_DEFAULT_FUNCTION_OBLIGATION_ID_PREFIX)
        .and_then(|id| id.strip_suffix(TRUST_MC_DEFAULT_FUNCTION_OBLIGATION_ID_SUFFIX))
    else {
        return false;
    };
    if function_fragment.is_empty()
        || !function_fragment.bytes().all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        || obligation.kind != ObligationKind::ArithmeticSafety
        || obligation.contract_id.is_some()
        || obligation.proof_item_id.is_some()
        || obligation.required_strength.is_some()
        || !obligation.summary_facts.is_empty()
        || obligation.description != TRUST_MC_DEFAULT_FUNCTION_DESCRIPTION
    {
        return false;
    }

    let required = [
        (
            TRUST_MC_DEFAULT_FUNCTION_OBLIGATION_METADATA_KEY,
            TRUST_MC_DEFAULT_FUNCTION_OBLIGATION_METADATA_VALUE,
        ),
        (TRUST_VC_KIND_METADATA_KEY, TRUST_MC_DEFAULT_FUNCTION_VC_KIND),
        (TRUST_VC_FORMULA_SCHEMA_METADATA_KEY, TRUST_SPEC_PREDICATE_SCHEMA_VERSION),
        (TRUST_VC_FORMULA_SORT_METADATA_KEY, "Bool"),
        (TRUST_VC_FORMULA_SMTLIB_METADATA_KEY, "false"),
        (TRUST_MC_FORMULA_SCHEMA_METADATA_KEY, TRUST_SPEC_PREDICATE_SCHEMA_VERSION),
    ];
    if required
        .iter()
        .any(|(key, expected)| unique_metadata_value(obligation, key) != Some(*expected))
    {
        return false;
    }
    if !unique_metadata_value(obligation, TRUST_SOURCE_DIGEST_METADATA_KEY)
        .is_some_and(is_stable_sha256_hex)
        || !unique_metadata_value(obligation, TRUST_VC_DIGEST_METADATA_KEY)
            .is_some_and(is_stable_sha256_hex)
    {
        return false;
    }

    let Some(payload) = unique_metadata_value(obligation, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
    else {
        return false;
    };
    let Ok(predicate) = serde_json::from_str::<TrustSpecPredicate>(payload) else {
        return false;
    };
    predicate.has_current_schema()
        && predicate.root_sort == TrustSpecSort::Bool
        && predicate.variables.is_empty()
        && predicate.root.sort == TrustSpecSort::Bool
        && matches!(&predicate.root.kind, TrustSpecExprKind::BoolLiteral { value: false })
        && validate_trust_spec_predicate(&predicate).is_ok()
        && serde_json::to_string(&predicate).ok().as_deref() == Some(payload)
}

fn unique_metadata_value<'a>(obligation: &'a TrustObligation, key: &str) -> Option<&'a str> {
    let mut matching = obligation.metadata.iter().filter(|entry| entry.key == key);
    let value = matching.next()?.value.as_str();
    matching.next().is_none().then_some(value)
}

fn canonical_default_admission_metadata() -> Vec<MetadataEntry> {
    let predicate = TrustSpecPredicate::new(TrustSpecExpr::bool_literal(false), Vec::new());
    let payload = serde_json::to_string(&predicate)
        .expect("serializing the fixed default-admission predicate cannot fail");
    vec![
        MetadataEntry {
            key: TRUST_MC_DEFAULT_FUNCTION_OBLIGATION_METADATA_KEY.to_string(),
            value: TRUST_MC_DEFAULT_FUNCTION_OBLIGATION_METADATA_VALUE.to_string(),
        },
        MetadataEntry {
            key: TRUST_VC_KIND_METADATA_KEY.to_string(),
            value: TRUST_MC_DEFAULT_FUNCTION_VC_KIND.to_string(),
        },
        MetadataEntry { key: TRUST_SOURCE_DIGEST_METADATA_KEY.to_string(), value: "0".repeat(64) },
        MetadataEntry { key: TRUST_VC_DIGEST_METADATA_KEY.to_string(), value: "0".repeat(64) },
        MetadataEntry {
            key: TRUST_VC_FORMULA_SCHEMA_METADATA_KEY.to_string(),
            value: TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
        },
        MetadataEntry {
            key: TRUST_VC_FORMULA_SORT_METADATA_KEY.to_string(),
            value: "Bool".to_string(),
        },
        MetadataEntry {
            key: TRUST_VC_FORMULA_SMTLIB_METADATA_KEY.to_string(),
            value: "false".to_string(),
        },
        MetadataEntry { key: TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY.to_string(), value: payload },
        MetadataEntry {
            key: TRUST_MC_FORMULA_SCHEMA_METADATA_KEY.to_string(),
            value: TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
        },
    ]
}

/// Compiler-derived boundary-hardening lane (OS/path, byte/text, error, panic,
/// compatibility, process semantics, unsafe/FFI, trust domain).
///
/// This is the ONE privileged `ObligationKind::Custom` namespace. Consumers
/// treat it as a capability, not a label: carrying it grants a full-verifier
/// route (`trust-router` `obligation_route_for_kind`), trust-mc ownership plus a
/// `MirObligationKind::Assertion` lowering (`trust-bmc`), trust-mc
/// formula-obligation status (`trust-mir-extract`), and native TrustIr
/// routability (`rustc_mir_transform::trust_verify`). Every other `Custom`
/// namespace is deliberately un-routable, and that exclusion is load-bearing:
/// see [`TRUST_VC_UNBOUNDED_ALLOCATION_OBLIGATION_NAMESPACE`].
pub const TRUST_VC_HARDENED_OBLIGATION_NAMESPACE: &str = "trust.vc.hardened";

/// Compiler verification conditions with no nominal [`ObligationKind`].
pub const TRUST_VC_OBLIGATION_NAMESPACE: &str = "trust.vc";

/// Allocation-capacity obligations (`count >= ceiling`).
///
/// This namespace exists so the obligation is NOT natively routable. A
/// `VcKind::UnboundedAllocation` is not a panic-freedom / arithmetic-overflow
/// property, and the native whole-function CHC proof does not model it; mapping
/// it into a routable kind false-proved unbounded allocations. Widening the
/// privileged-namespace test to cover this namespace reopens that P0.
pub const TRUST_VC_UNBOUNDED_ALLOCATION_OBLIGATION_NAMESPACE: &str =
    "trust.vc.unbounded_allocation";

/// Source-level contract clauses the compiler could not lower (`name` is
/// `"unsupported"`), used to bind a public marker row to its clause monitor.
pub const TRUST_CONTRACT_OBLIGATION_NAMESPACE: &str = "trust.contract";

/// Proof items (lemmas, specification functions, proof blocks, logic laws).
pub const TRUST_PROOF_ITEM_OBLIGATION_NAMESPACE: &str = "trust.proof_item";

/// trust-vc's TrustIr adapter request lane.
pub const TRUST_VC_TRUST_IR_OBLIGATION_NAMESPACE: &str = "trust_vc.trust_ir";

/// The closed set of namespaces an [`ObligationKind::Custom`] may carry.
///
/// `namespace` is authority-bearing (see
/// [`TRUST_VC_HARDENED_OBLIGATION_NAMESPACE`]), so it is admitted from this
/// pinned list rather than accepted as free text: an obligation cannot mint a
/// producer identity that no Trust component defines, and a new privileged lane
/// cannot appear without an edit here, in the crate that owns the vocabulary.
/// Enforced by `validate_obligation_kind`, which runs on every obligation in a
/// bundle, a request batch, a run result, a skipped row, and on the canonical
/// semantic digest — and at the serde boundary itself: every `ObligationKind`
/// deserialization funnels through `ObligationKindWire`'s `TryFrom`, which runs
/// the same admission. The boundary check is load-bearing, not belt-and-braces:
/// obligation kinds are deserialized in production (`targo-trust`'s three-suite
/// artifact gate parses `verification-run-manifest.json` from disk), and bare
/// [`TrustObligation`]/[`SkippedObligation`]/[`EngineManifest`] values have no
/// validating `Deserialize` impls of their own.
///
/// `name` is deliberately NOT sealed: within an admitted namespace it is a
/// label, never an authority test — the hardened lane forwards unrecognized
/// names as `HardenedVcCategory::Unknown`, and the two name-sensitive consumers
/// (`trust.contract`/`"unsupported"`, `trust.vc`/`"translation_validation"`)
/// use exact equality to NARROW, so an unknown name fails closed.
pub const ADMITTED_OBLIGATION_NAMESPACES: &[&str] = &[
    TRUST_CONTRACT_OBLIGATION_NAMESPACE,
    TRUST_PROOF_ITEM_OBLIGATION_NAMESPACE,
    TRUST_VC_OBLIGATION_NAMESPACE,
    TRUST_VC_HARDENED_OBLIGATION_NAMESPACE,
    TRUST_VC_UNBOUNDED_ALLOCATION_OBLIGATION_NAMESPACE,
    TRUST_VC_TRUST_IR_OBLIGATION_NAMESPACE,
];

/// True when `namespace` is a Trust-defined [`ObligationKind::Custom`]
/// namespace. Exact match against [`ADMITTED_OBLIGATION_NAMESPACES`]: never a
/// prefix or `starts_with` test, which would let `trust.vc.hardened.evil` — or
/// the unbounded-allocation lane under a `trust.vc` prefix — inherit authority.
#[must_use]
pub fn is_admitted_obligation_namespace(namespace: &str) -> bool {
    ADMITTED_OBLIGATION_NAMESPACES.contains(&namespace)
}

/// Obligation role.
///
/// `Custom` is an open-ended shape but not an open-ended vocabulary: its
/// `namespace` must be one of [`ADMITTED_OBLIGATION_NAMESPACES`], and
/// deserialization enforces that admission itself (the `try_from` funnel
/// below), so an unpinned namespace cannot enter through any serde boundary.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(try_from = "ObligationKindWire")]
#[non_exhaustive]
pub enum ObligationKind {
    Precondition,
    Postcondition,
    Assertion,
    Invariant,
    LoopInvariant,
    ArithmeticSafety,
    MemorySafety,
    BoundsCheck,
    Ownership,
    Refinement,
    Termination,
    TemporalSafety,
    Liveness,
    Protocol,
    Custom { namespace: String, name: String },
}

/// Deserialization funnel for [`ObligationKind`]: identical wire shape (same
/// variant names, order, and `Custom` fields, so self-describing and
/// index-based encodings are both unchanged), with `TryFrom` running
/// `validate_obligation_kind` on the way in. A forged or unpinned `Custom`
/// namespace is refused AT the serde boundary itself, not only by the envelope
/// validators a deserializer happens to call. This matters because obligation
/// kinds ARE deserialized in production — `targo-trust`'s
/// `run_three_suite_artifact_gate` (pipeline_v2) parses an on-disk
/// `verification-run-manifest.json` outside `cfg(test)` — and a bare
/// [`TrustObligation`], [`SkippedObligation`], or [`EngineManifest`] has no
/// validating `Deserialize` impl of its own.
#[derive(Deserialize)]
enum ObligationKindWire {
    Precondition,
    Postcondition,
    Assertion,
    Invariant,
    LoopInvariant,
    ArithmeticSafety,
    MemorySafety,
    BoundsCheck,
    Ownership,
    Refinement,
    Termination,
    TemporalSafety,
    Liveness,
    Protocol,
    Custom { namespace: String, name: String },
}

impl TryFrom<ObligationKindWire> for ObligationKind {
    type Error = String;

    fn try_from(wire: ObligationKindWire) -> Result<Self, Self::Error> {
        let kind = match wire {
            ObligationKindWire::Precondition => Self::Precondition,
            ObligationKindWire::Postcondition => Self::Postcondition,
            ObligationKindWire::Assertion => Self::Assertion,
            ObligationKindWire::Invariant => Self::Invariant,
            ObligationKindWire::LoopInvariant => Self::LoopInvariant,
            ObligationKindWire::ArithmeticSafety => Self::ArithmeticSafety,
            ObligationKindWire::MemorySafety => Self::MemorySafety,
            ObligationKindWire::BoundsCheck => Self::BoundsCheck,
            ObligationKindWire::Ownership => Self::Ownership,
            ObligationKindWire::Refinement => Self::Refinement,
            ObligationKindWire::Termination => Self::Termination,
            ObligationKindWire::TemporalSafety => Self::TemporalSafety,
            ObligationKindWire::Liveness => Self::Liveness,
            ObligationKindWire::Protocol => Self::Protocol,
            ObligationKindWire::Custom { namespace, name } => Self::Custom { namespace, name },
        };
        validate_obligation_kind(&kind)?;
        Ok(kind)
    }
}

/// Typed origin and compiler context for one public obligation.
///
/// This payload intentionally travels through `TrustObligation::metadata`
/// instead of a required struct field so older adapter crates that construct
/// obligations directly remain source-compatible.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObligationContext {
    #[serde(default = "default_obligation_context_schema_version")]
    pub schema_version: String,
    pub producer: ObligationProducer,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub function: Option<FunctionContext>,
    pub origin: ObligationOrigin,
}

impl ObligationContext {
    #[must_use]
    pub fn new(producer: ObligationProducer, origin: ObligationOrigin) -> Self {
        Self {
            schema_version: OBLIGATION_CONTEXT_SCHEMA_VERSION.to_string(),
            producer,
            function: None,
            origin,
        }
    }

    #[must_use]
    pub fn with_function(mut self, function: FunctionContext) -> Self {
        self.function = Some(function);
        self
    }

    /// Returns true when this context uses the current stable schema marker.
    #[must_use]
    pub fn has_current_schema(&self) -> bool {
        self.schema_version == OBLIGATION_CONTEXT_SCHEMA_VERSION
    }

    /// Encode this context as a metadata entry.
    pub fn to_metadata_entry(&self) -> Result<MetadataEntry, serde_json::Error> {
        Ok(MetadataEntry {
            key: OBLIGATION_CONTEXT_METADATA_KEY.to_string(),
            value: serde_json::to_string(self)?,
        })
    }

    /// Decode an obligation context from a metadata entry.
    ///
    /// Returns `Ok(None)` for unrelated metadata keys.
    pub fn from_metadata_entry(
        metadata: &MetadataEntry,
    ) -> Result<Option<Self>, serde_json::Error> {
        if metadata.key == OBLIGATION_CONTEXT_METADATA_KEY {
            serde_json::from_str(&metadata.value).map(Some)
        } else {
            Ok(None)
        }
    }
}

fn default_obligation_context_schema_version() -> String {
    OBLIGATION_CONTEXT_SCHEMA_VERSION.to_string()
}

/// Producer that created the typed obligation context.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum ObligationProducer {
    CompilerMirExtract,
    VcGenerator,
    ProofItem,
    Compatibility,
}

/// Function-level context for an obligation.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FunctionContext {
    pub crate_name: String,
    pub path: String,
}

/// Stable machine-readable origin of an obligation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "origin", rename_all = "snake_case")]
#[non_exhaustive]
pub enum ObligationOrigin {
    Contract {
        contract_id: String,
        contract_kind: ContractKind,
        contract_index: usize,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        predicate_schema: Option<String>,
    },
    UnsupportedContract {
        contract_index: usize,
        compiler_contract_kind: String,
        reason: String,
    },
    VerificationCondition {
        vc_kind: String,
        vc_index: usize,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        formula_schema: Option<String>,
    },
    ProofItem {
        proof_item_id: String,
        proof_item_kind: String,
        engine: String,
    },
}

/// Structured evidence for a single obligation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObligationEvidence {
    pub evidence_id: String,
    pub obligation_id: String,
    pub engine: EngineManifest,
    pub status: EvidenceStatus,
    /// Why this obligation was declined, when the producing engine classified
    /// it. Set only by a producing engine, only on a decline, and only when the
    /// decline is a pure capability gap.
    ///
    /// `None` is TERMINAL and is the correct default: an absent class means
    /// nobody asserted that a retry is safe. Old wire payloads and engines that
    /// have not been taught the distinction both land here, fail-closed by
    /// construction.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub decline: Option<DeclineClass>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_strength: Option<ProofStrength>,
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        deserialize_with = "deserialize_obligation_evidence_artifacts"
    )]
    pub artifacts: Vec<EvidenceArtifact>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub counterexample: Option<Counterexample>,
    pub publication: EvidencePublicationMetadata,
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        deserialize_with = "deserialize_bounded_evidence_diagnostics"
    )]
    pub diagnostics: Vec<String>,
}

impl ObligationEvidence {
    /// Returns true only for proved evidence with publication-grade proof
    /// strength. Bounded, heuristic, unchecked, or missing proof strength must
    /// not be upgraded by aggregation.
    #[must_use]
    pub fn is_unbounded_proof(&self) -> bool {
        self.status == EvidenceStatus::Proved
            && self.proof_strength.as_ref().is_some_and(ProofStrength::is_publication_grade)
            && self.satisfies_proof_artifact_policy()
    }

    /// Returns true when this evidence can satisfy an obligation's required
    /// proof strength for publication-grade aggregation.
    #[must_use]
    pub fn satisfies_required_strength(&self, required: Option<&ProofStrength>) -> bool {
        self.satisfies_strength_requirement(required) && self.satisfies_proof_artifact_policy()
    }

    /// Returns true when the evidence status and proof strength are sufficient,
    /// before replay/check artifact requirements are applied.
    #[must_use]
    pub fn satisfies_strength_requirement(&self, required: Option<&ProofStrength>) -> bool {
        let Some(actual) = self.proof_strength.as_ref() else {
            return false;
        };
        self.status == EvidenceStatus::Proved
            && actual.is_publication_grade()
            && required.is_none_or(|required| actual.satisfies_requirement(required))
    }

    /// Returns true only when proof artifacts carry exact, same-artifact bytes
    /// and an unambiguous producer-authored relationship: one materialized
    /// certificate, or exactly one materialized transcript paired with exactly
    /// one materialized replay/check artifact in the same proof binding. A
    /// PDR proof may additionally carry exactly one materialized invariant
    /// model rooted in the transcript's exact structural inputs; every replay
    /// and check in that route must explicitly consume the model as well.
    #[must_use]
    pub fn satisfies_proof_artifact_policy(&self) -> bool {
        if self.artifacts.len() > MAX_EVIDENCE_ARTIFACTS_PER_OBLIGATION {
            return false;
        }
        let mut identities = BTreeSet::new();
        if self.artifacts.iter().any(|artifact| !identities.insert((artifact.kind, &artifact.hash)))
        {
            return false;
        }
        if !native_structural_domain_is_valid(&self.artifacts) {
            return false;
        }
        let certificates = self
            .artifacts
            .iter()
            .filter(|artifact| artifact.kind == EvidenceArtifactKind::ProofCertificate)
            .collect::<Vec<_>>();
        let transcripts = self
            .artifacts
            .iter()
            .filter(|artifact| artifact.kind.is_solver_transcript())
            .collect::<Vec<_>>();
        let replays = self
            .artifacts
            .iter()
            .filter(|artifact| {
                matches!(
                    artifact.kind,
                    EvidenceArtifactKind::ProofReplayTrace | EvidenceArtifactKind::ReplayLog
                )
            })
            .collect::<Vec<_>>();
        let checks = self
            .artifacts
            .iter()
            .filter(|artifact| artifact.kind == EvidenceArtifactKind::ProofCheckReport)
            .collect::<Vec<_>>();
        let models = self
            .artifacts
            .iter()
            .filter(|artifact| artifact.kind == EvidenceArtifactKind::Model)
            .collect::<Vec<_>>();

        let certificate_route = certificates.len() == 1
            && transcripts.is_empty()
            && replays.is_empty()
            && checks.is_empty()
            && models.is_empty()
            && artifact_has_valid_owned_materialization(certificates[0], &self.obligation_id)
            && certificates[0]
                .materialization
                .as_ref()
                .is_some_and(|materialization| materialization.referenced_artifacts().is_empty())
            && self.artifacts.iter().all(|artifact| {
                artifact.materialization.is_none()
                    || is_native_structural_artifact(artifact)
                    || (artifact.kind == certificates[0].kind
                        && artifact.hash == certificates[0].hash)
            });

        let dag_route = certificates.is_empty()
            && transcripts.len() == 1
            && replays.len() <= 1
            && checks.len() <= 1
            && models.len() <= 1
            && !(replays.is_empty() && checks.is_empty())
            && artifact_has_valid_owned_materialization(transcripts[0], &self.obligation_id)
            && transcript_structural_lineage_is_valid(
                transcripts[0],
                &self.artifacts,
                &self.obligation_id,
            )
            && models.first().is_none_or(|model| {
                artifact_has_valid_owned_materialization(model, &self.obligation_id)
                    && artifact_has_same_binding(model, transcripts[0])
                    && artifact_has_same_structural_lineage(model, transcripts[0])
            })
            && replays.first().is_none_or(|replay| {
                artifact_has_valid_owned_materialization(replay, &self.obligation_id)
                    && artifact_has_same_binding(replay, transcripts[0])
                    && models.first().map_or_else(
                        || artifact_references_exactly(replay, &[transcripts[0]]),
                        |model| {
                            artifact_references_exactly(replay, &[transcripts[0], model])
                        },
                    )
            })
            && checks.first().is_none_or(|check| {
                artifact_has_valid_owned_materialization(check, &self.obligation_id)
                    && artifact_has_same_binding(check, transcripts[0])
                    && match (models.first().copied(), replays.first().copied()) {
                        (None, None) => artifact_references_exactly(check, &[transcripts[0]]),
                        (None, Some(replay)) => {
                            artifact_references_exactly(check, &[replay])
                                || artifact_references_exactly(check, &[transcripts[0], replay])
                        }
                        (Some(model), None) => {
                            artifact_references_exactly(check, &[transcripts[0], model])
                        }
                        (Some(model), Some(replay)) => artifact_references_exactly(
                            check,
                            &[transcripts[0], replay, model],
                        ),
                    }
            })
            && dag_has_no_unreferenced_materialized_extras(
                &self.artifacts,
                transcripts[0],
                replays.first().copied(),
                checks.first().copied(),
                models.first().copied(),
            );

        certificate_route || dag_route
    }

    /// Returns true when the evidence references a proof replay/check artifact.
    #[must_use]
    pub fn has_replay_or_check_artifact_metadata(&self) -> bool {
        self.artifacts.iter().any(|artifact| artifact.kind.is_replay_or_check())
    }

    /// Returns true when solver-backed evidence references a solver transcript.
    #[must_use]
    pub fn has_solver_transcript_artifacts(&self) -> bool {
        self.artifacts.iter().any(|artifact| artifact.kind.is_solver_transcript())
    }
}

fn artifact_has_valid_owned_materialization(artifact: &EvidenceArtifact, owner: &str) -> bool {
    artifact.materialization.as_ref().is_some_and(|materialization| {
        materialization.matches_hash(&artifact.hash)
            && materialization.bound_payload_bytes(artifact.kind, owner).is_some()
            && artifact.uri.contains(&artifact.hash.value)
            && !materialization.referenced_artifacts().contains(&EvidenceArtifactReference {
                kind: artifact.kind,
                hash: artifact.hash.clone(),
            })
    })
}

fn artifact_has_same_binding(left: &EvidenceArtifact, right: &EvidenceArtifact) -> bool {
    left.materialization.as_ref().is_some_and(|left| {
        right
            .materialization
            .as_ref()
            .is_some_and(|right| left.proof_binding_id() == right.proof_binding_id())
    })
}

fn artifact_references_exactly(
    consumer: &EvidenceArtifact,
    consumed: &[&EvidenceArtifact],
) -> bool {
    let mut expected = consumed
        .iter()
        .map(|artifact| EvidenceArtifactReference {
            kind: artifact.kind,
            hash: artifact.hash.clone(),
        })
        .collect::<Vec<_>>();
    expected.sort();
    consumer
        .materialization
        .as_ref()
        .is_some_and(|materialization| materialization.referenced_artifacts() == expected)
}

fn artifact_has_same_structural_lineage(
    artifact: &EvidenceArtifact,
    transcript: &EvidenceArtifact,
) -> bool {
    artifact.materialization.as_ref().is_some_and(|artifact_materialization| {
        transcript.materialization.as_ref().is_some_and(|transcript_materialization| {
            artifact_materialization.referenced_artifacts()
                == transcript_materialization.referenced_artifacts()
        })
    })
}

fn transcript_structural_lineage_is_valid(
    transcript: &EvidenceArtifact,
    artifacts: &[EvidenceArtifact],
    owner: &str,
) -> bool {
    transcript.materialization.as_ref().is_some_and(|materialization| {
        let references = materialization.referenced_artifacts();
        !references.is_empty()
            && references.iter().all(|reference| {
                matches!(
                    reference.kind,
                    EvidenceArtifactKind::EngineInput | EvidenceArtifactKind::NormalizedObligation
                ) && {
                    let mut candidates = artifacts.iter().filter(|candidate| {
                        candidate.kind == reference.kind && candidate.hash == reference.hash
                    });
                    let Some(candidate) = candidates.next() else {
                        return false;
                    };
                    candidates.next().is_none() && {
                        artifact_has_valid_owned_materialization(candidate, owner)
                            && artifact_has_same_binding(candidate, transcript)
                            && candidate.materialization.as_ref().is_some_and(
                                |candidate_materialization| {
                                    candidate_materialization.referenced_artifacts().is_empty()
                                },
                            )
                    }
                }
            })
    })
}

fn dag_has_no_unreferenced_materialized_extras(
    artifacts: &[EvidenceArtifact],
    transcript: &EvidenceArtifact,
    replay: Option<&EvidenceArtifact>,
    check: Option<&EvidenceArtifact>,
    model: Option<&EvidenceArtifact>,
) -> bool {
    let mut allowed = vec![(transcript.kind, &transcript.hash)];
    if let Some(replay) = replay {
        allowed.push((replay.kind, &replay.hash));
    }
    if let Some(check) = check {
        allowed.push((check.kind, &check.hash));
    }
    if let Some(model) = model {
        allowed.push((model.kind, &model.hash));
    }
    if let Some(materialization) = &transcript.materialization {
        for reference in materialization.referenced_artifacts() {
            allowed.push((reference.kind, &reference.hash));
        }
    }
    artifacts.iter().all(|artifact| {
        artifact.materialization.is_none()
            || is_native_structural_artifact(artifact)
            || allowed.iter().any(|(kind, hash)| *kind == artifact.kind && **hash == artifact.hash)
    })
}

fn is_native_structural_artifact(artifact: &EvidenceArtifact) -> bool {
    matches!(
        artifact.kind,
        EvidenceArtifactKind::EngineInput | EvidenceArtifactKind::NormalizedObligation
    ) && artifact.uri.starts_with("trust_ir-native://verification-bundle/")
}

fn native_structural_domain_is_valid(artifacts: &[EvidenceArtifact]) -> bool {
    const PREFIX: &str = "trust_ir-native://verification-bundle/";
    let native =
        artifacts.iter().filter(|artifact| artifact.uri.starts_with(PREFIX)).collect::<Vec<_>>();
    if native.is_empty() {
        return true;
    }
    if native.len() != 3 || native.iter().any(|artifact| !is_native_structural_artifact(artifact)) {
        return false;
    }
    let Some(proof) = native
        .iter()
        .copied()
        .find(|artifact| artifact.kind == EvidenceArtifactKind::NormalizedObligation)
    else {
        return false;
    };
    let proof_segments =
        proof.uri.strip_prefix(PREFIX).map(|uri| uri.split('/').collect::<Vec<_>>());
    let Some([bundle_sha, suite, "request", request_id, request_sha, "proof", proof_id, proof_sha]) =
        proof_segments.as_deref()
    else {
        return false;
    };
    if !matches!(*suite, "trust-wp" | "trust-mc" | "trust-vc")
        || !is_stable_sha256_hex(bundle_sha)
        || !is_stable_sha256_hex(request_sha)
        || !is_stable_sha256_hex(proof_sha)
        || request_id.is_empty()
        || proof_id.is_empty()
        || proof.hash.value != *proof_sha
    {
        return false;
    }
    let bundle_uri = format!("{PREFIX}{bundle_sha}");
    let request_uri = format!("{bundle_uri}/{suite}/request/{request_id}/{request_sha}");
    let Some(bundle) = native.iter().copied().find(|artifact| {
        artifact.kind == EvidenceArtifactKind::EngineInput && artifact.uri == bundle_uri
    }) else {
        return false;
    };
    let Some(request) = native.iter().copied().find(|artifact| {
        artifact.kind == EvidenceArtifactKind::EngineInput && artifact.uri == request_uri
    }) else {
        return false;
    };
    if bundle.hash.value != *bundle_sha || request.hash.value != *request_sha {
        return false;
    }
    let binding = format!("trust_ir-native-{suite}-request-{request_id}-proof-{proof_id}");
    let Some(bundle_materialization) = bundle.materialization.as_ref() else {
        return false;
    };
    let Some(request_materialization) = request.materialization.as_ref() else {
        return false;
    };
    let Some(proof_materialization) = proof.materialization.as_ref() else {
        return false;
    };
    bundle_materialization.proof_binding_id() == binding
        && request_materialization.proof_binding_id() == binding
        && proof_materialization.proof_binding_id() == binding
        && bundle_materialization.matches_hash(&bundle.hash)
        && request_materialization.matches_hash(&request.hash)
        && proof_materialization.matches_hash(&proof.hash)
        && bundle_materialization.referenced_artifacts().is_empty()
        && request_materialization.referenced_artifacts()
            == [EvidenceArtifactReference {
                kind: EvidenceArtifactKind::EngineInput,
                hash: bundle.hash.clone(),
            }]
        && proof_materialization.referenced_artifacts()
            == [EvidenceArtifactReference {
                kind: EvidenceArtifactKind::EngineInput,
                hash: request.hash.clone(),
            }]
        && native_structural_envelope_matches(
            bundle_materialization.bytes(),
            "bundle",
            None,
            None,
            None,
        )
        && native_structural_envelope_matches(
            request_materialization.bytes(),
            "request",
            Some(suite),
            Some(request_id),
            None,
        )
        && native_structural_envelope_matches(
            proof_materialization.bytes(),
            "normalized_obligation",
            Some(suite),
            Some(request_id),
            Some(proof_id),
        )
}

fn native_structural_envelope_matches(
    bytes: &[u8],
    role: &str,
    suite: Option<&str>,
    request_id: Option<&str>,
    proof_id: Option<&str>,
) -> bool {
    let Ok(mut value) = serde_json::from_slice::<serde_json::Value>(bytes) else {
        return false;
    };
    let Some(object) = value.as_object() else {
        return false;
    };
    if object.len() != 6
        || object.get("schema").and_then(serde_json::Value::as_str)
            != Some("trust.native-trust-ir-materialization.v1")
        || object.get("role").and_then(serde_json::Value::as_str) != Some(role)
        || api_json_optional_string(object.get("suite")) != Some(suite)
        || api_json_optional_string(object.get("request_id")) != Some(request_id)
        || api_json_optional_string(object.get("proof_id")) != Some(proof_id)
        || object.get("payload").is_none_or(serde_json::Value::is_null)
    {
        return false;
    }
    canonicalize_json_in_place(&mut value);
    serde_json::to_vec(&value).is_ok_and(|canonical| canonical == bytes)
}

fn api_json_optional_string(value: Option<&serde_json::Value>) -> Option<Option<&str>> {
    match value? {
        serde_json::Value::Null => Some(None),
        serde_json::Value::String(value) => Some(Some(value)),
        _ => None,
    }
}

/// Verification outcome for one obligation, as an engine reports it.
///
/// This is the engine-boundary spelling of the shared outcome vocabulary. It is
/// deliberately narrower than [`trust_types::Outcome`]: an engine reports what
/// its own run concluded, so the outcomes that describe a decision made *around*
/// the engine — an admitted assumption, a runtime check accepted in place of a
/// proof — are not its to report. Everything it can report is one of the shared
/// meanings, which is what [`EvidenceStatus::outcome`] makes checkable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum EvidenceStatus {
    Proved,
    Failed,
    Unknown,
    Timeout,
    Canceled,
    Unsupported,
}

impl EvidenceStatus {
    /// This status as the shared outcome it denotes.
    ///
    /// Every consumer that needs to name an engine status — a report row, a
    /// diagnostic, a scorecard column — goes through here, so the name is the
    /// one the rest of Trust already uses for that meaning.
    ///
    /// Exhaustive on purpose: `EvidenceStatus` is `#[non_exhaustive]` only for
    /// its dependents, so a status added here has to be given a shared meaning
    /// at the same time rather than silently reporting as `Unknown`.
    #[must_use]
    pub const fn outcome(self) -> trust_types::Outcome {
        match self {
            Self::Proved => trust_types::Outcome::Proved,
            Self::Failed => trust_types::Outcome::Failed,
            Self::Unknown => trust_types::Outcome::Unknown,
            Self::Timeout => trust_types::Outcome::Timeout,
            Self::Canceled => trust_types::Outcome::Canceled,
            Self::Unsupported => trust_types::Outcome::Unsupported,
        }
    }
}

/// Why an engine declined a specific obligation INSTANCE.
///
/// This exists so a future multi-engine fallback can tell "I have no lowering
/// for this kind" apart from "I lowered this instance and refused it". Only the
/// first is ever eligible for a second engine's attempt; retrying the second
/// would launder a rejection into a green.
///
/// It is deliberately NOT derivable from [`SupportLevel`], which is a function
/// of [`ObligationKind`] alone — a per-kind constant cannot classify an
/// instance, so any discriminator built on it is a static whitelist wearing a
/// classifier's clothes.
///
/// **A single variant is deliberate.** `Soundness` is not a variant, because
/// "not `Capability`" is the safe default and naming the unsafe class invites
/// someone to populate it. The absence of a class is TERMINAL: engines that have
/// not been taught this distinction, older wire payloads, and every decline the
/// router itself mints all land on `None` and are never retried. If a second
/// retryable class is ever justified it is added here, on its own review;
/// `#[non_exhaustive]` keeps that additive.
///
/// Eligibility MUST be tested with a positive match —
/// `matches!(decline, Some(DeclineClass::Capability))` — never a negative one.
/// [`SupportLevel::is_supported`] is written negatively over a
/// `#[non_exhaustive]` enum, so every future variant there silently defaults to
/// *attemptable*. Do not copy that shape here, where the default must be
/// *terminal*.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum DeclineClass {
    /// The engine owns this obligation kind but has no lowering or encoding for
    /// it. Nothing about this instance was decided: no solver budget was spent,
    /// no admission policy ran, and no proof obligation was evaluated. Another
    /// engine may therefore attempt it without re-litigating anything.
    Capability,
}

impl DeclineClass {
    /// True only for a decline another engine may retry.
    ///
    /// Takes the `Option` so the terminal default is expressed once, here,
    /// rather than at each call site where a `None` could be mishandled.
    #[must_use]
    pub fn is_retryable(decline: Option<Self>) -> bool {
        matches!(decline, Some(Self::Capability))
    }
}

impl From<EvidenceStatus> for trust_types::Outcome {
    fn from(status: EvidenceStatus) -> Self {
        status.outcome()
    }
}

// `ProofStrength` (and its constructors / requirement-checking impl),
// `ReasoningKind`, and `AssuranceLevel` are defined in trust-ir-contract and
// re-exported above — preserved verbatim there with identical derives and serde
// representation, so the wire format and every dependent are unchanged.

/// Public manifest each verifier engine must expose.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EngineManifest {
    pub name: String,
    pub version: String,
    pub api_version: String,
    pub kind: EngineKind,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub repository: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub revision: Option<String>,
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        deserialize_with = "deserialize_bounded_engine_capabilities"
    )]
    pub capabilities: Vec<EngineCapability>,
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        deserialize_with = "deserialize_bounded_engine_proof_modes"
    )]
    pub proof_modes: Vec<ReasoningKind>,
}

impl EngineManifest {
    /// Build a manifest using the current verifier API version.
    #[must_use]
    pub fn new(name: impl Into<String>, version: impl Into<String>, kind: EngineKind) -> Self {
        Self {
            name: name.into(),
            version: version.into(),
            api_version: API_VERSION.to_string(),
            kind,
            repository: None,
            revision: None,
            capabilities: Vec::new(),
            proof_modes: Vec::new(),
        }
    }

    /// Validate the engine identity and capability inventory used as proof
    /// provenance at the verifier boundary.
    pub fn validate(&self) -> Result<(), String> {
        validate_engine_manifest(self)
    }
}

/// Engine ownership lane.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum EngineKind {
    Deductive,
    Reachability,
    ProofCalculus,
    Temporal,
    SolverKernel,
    Composite,
}

/// Capability advertised by an engine manifest.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct EngineCapability {
    pub obligation_kind: ObligationKind,
    pub support: SupportLevel,
}

/// How well an engine supports an obligation.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SupportLevel {
    Unsupported { reason: String },
    Experimental { reason: String },
    Supported,
    Preferred,
}

impl SupportLevel {
    /// Returns true when the engine may attempt this obligation.
    #[must_use]
    pub fn is_supported(&self) -> bool {
        !matches!(self, Self::Unsupported { .. })
    }
}

/// Native verifier invocation context.
///
/// This type is intended for in-process Trust execution. Use
/// [`VerifierExecutionSnapshot`] when a serializable record is needed for
/// release gates or audit logs.
#[derive(Debug, Clone)]
pub struct VerifierExecutionContext {
    pub run_id: String,
    pub invocation: VerifierInvocation,
    pub limits: VerifierResourceLimits,
    pub cancellation: CancellationToken,
    pub metadata: Vec<MetadataEntry>,
    /// Trust: Optional per-function wall-clock deadline. When set and
    /// reached, in-process full verification degrades the remaining obligations
    /// to `Timeout` (sound: never `Proved`) instead of solving unbounded. This
    /// is runtime-only state and is intentionally absent from the serializable
    /// [`VerifierExecutionSnapshot`].
    pub deadline: Option<Instant>,
}

impl VerifierExecutionContext {
    /// Create a native Trust verifier execution context with no resource
    /// limits and a fresh cancellation token.
    #[must_use]
    pub fn new(run_id: impl Into<String>) -> Self {
        Self {
            run_id: run_id.into(),
            invocation: VerifierInvocation::NativeTrustPipeline,
            limits: VerifierResourceLimits::default(),
            cancellation: CancellationToken::new(),
            metadata: Vec::new(),
            deadline: None,
        }
    }

    /// Compatibility context for callers that still use the original verifier
    /// trait entrypoint.
    #[must_use]
    pub fn compatibility() -> Self {
        Self::new(DEFAULT_VERIFICATION_RUN_ID)
    }

    /// Set resource limits for this execution context.
    #[must_use]
    pub fn with_limits(mut self, limits: VerifierResourceLimits) -> Self {
        self.limits = limits;
        self.with_wall_time_deadline_from_limits()
    }

    /// Trust: Derive the runtime wall-clock deadline from serialized limits.
    ///
    /// The absolute [`Instant`] remains runtime-only and is intentionally not
    /// serialized in [`VerifierExecutionSnapshot`]. If an earlier explicit
    /// deadline is already present, the earlier deadline wins.
    #[must_use]
    pub fn with_wall_time_deadline_from_limits(mut self) -> Self {
        let Some(wall_time_ms) = self.limits.wall_time_ms else {
            return self;
        };
        let wall_time_deadline = Instant::now()
            .checked_add(Duration::from_millis(wall_time_ms))
            .unwrap_or_else(Instant::now);
        self.deadline = Some(
            self.deadline.map_or(wall_time_deadline, |deadline| deadline.min(wall_time_deadline)),
        );
        self
    }

    /// Set the invocation lane for audit/reporting purposes.
    #[must_use]
    pub fn with_invocation(mut self, invocation: VerifierInvocation) -> Self {
        self.invocation = invocation;
        self
    }

    /// Trust: Set the per-function wall-clock deadline. Once reached,
    /// in-process full verification stops solving further obligations and
    /// degrades the remainder to `Timeout` (sound: never `Proved`).
    #[must_use]
    pub fn with_deadline(mut self, deadline: Instant) -> Self {
        self.deadline = Some(self.deadline.map_or(deadline, |existing| existing.min(deadline)));
        self
    }

    /// Trust: The configured per-function wall-clock deadline, if any.
    #[must_use]
    pub fn deadline(&self) -> Option<Instant> {
        self.deadline
    }

    /// Trust: True once the per-function wall-clock budget has elapsed.
    #[must_use]
    pub fn budget_exceeded(&self) -> bool {
        self.deadline.is_some_and(|deadline| Instant::now() >= deadline)
    }

    /// Returns true once cancellation has been requested.
    #[must_use]
    pub fn is_cancelled(&self) -> bool {
        self.cancellation.is_cancelled()
    }

    /// Build a serializable snapshot of this context.
    #[must_use]
    pub fn snapshot(&self) -> VerifierExecutionSnapshot {
        VerifierExecutionSnapshot {
            run_id: self.run_id.clone(),
            invocation: self.invocation.clone(),
            limits: self.limits.clone(),
            cancellation: self.cancellation.snapshot(),
            metadata: self.metadata.clone(),
        }
    }
}

impl Default for VerifierExecutionContext {
    fn default() -> Self {
        Self::compatibility()
    }
}

/// Serializable execution context captured in verifier result envelopes.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VerifierExecutionSnapshot {
    pub run_id: String,
    pub invocation: VerifierInvocation,
    pub limits: VerifierResourceLimits,
    pub cancellation: CancellationSnapshot,
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        deserialize_with = "deserialize_bounded_record_metadata"
    )]
    pub metadata: Vec<MetadataEntry>,
}

impl Default for VerifierExecutionSnapshot {
    fn default() -> Self {
        VerifierExecutionContext::compatibility().snapshot()
    }
}

/// Trust pipeline lane that requested verification.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum VerifierInvocation {
    NativeTrustPipeline,
    DscanPreflight,
    DpubReleaseGate,
    Ci,
    Custom { namespace: String, name: String },
}

/// Resource limits supplied by the Trust host before invoking native engines.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub struct VerifierResourceLimits {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub wall_time_ms: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cpu_time_ms: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub memory_bytes: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub solver_query_limit: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub obligation_limit: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub worker_threads: Option<u16>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub recursion_depth: Option<u32>,
}

impl VerifierResourceLimits {
    /// Resource-unbounded execution. Hosts should prefer explicit limits for
    /// release gates.
    #[must_use]
    pub fn unlimited() -> Self {
        Self::default()
    }

    /// Returns true when at least one limit is set.
    #[must_use]
    pub fn has_any_limit(&self) -> bool {
        self.wall_time_ms.is_some()
            || self.cpu_time_ms.is_some()
            || self.memory_bytes.is_some()
            || self.solver_query_limit.is_some()
            || self.obligation_limit.is_some()
            || self.worker_threads.is_some()
            || self.recursion_depth.is_some()
    }

    /// Set a wall-clock timeout in milliseconds.
    #[must_use]
    pub fn with_wall_time_ms(mut self, wall_time_ms: u64) -> Self {
        self.wall_time_ms = Some(wall_time_ms);
        self
    }

    /// Set a memory limit in bytes.
    #[must_use]
    pub fn with_memory_bytes(mut self, memory_bytes: u64) -> Self {
        self.memory_bytes = Some(memory_bytes);
        self
    }

    /// Set a solver-query budget.
    #[must_use]
    pub fn with_solver_query_limit(mut self, solver_query_limit: u64) -> Self {
        self.solver_query_limit = Some(solver_query_limit);
        self
    }

    /// Set a maximum number of obligations for one verifier run.
    #[must_use]
    pub fn with_obligation_limit(mut self, obligation_limit: u64) -> Self {
        self.obligation_limit = Some(obligation_limit);
        self
    }
}

/// Resource limit category used in cancellation and run status reporting.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ResourceLimitKind {
    WallTime,
    CpuTime,
    Memory,
    SolverQueries,
    Obligations,
    WorkerThreads,
    RecursionDepth,
}

/// Cloneable cancellation signal shared by the Trust host and native engines.
#[derive(Debug, Clone, Default)]
pub struct CancellationToken {
    inner: Arc<CancellationState>,
}

#[derive(Debug, Default)]
struct CancellationState {
    requested: AtomicBool,
    reason: Mutex<Option<CancellationReason>>,
}

impl CancellationToken {
    /// Create an unset cancellation token.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Request cancellation with a structured reason.
    pub fn cancel(&self, reason: CancellationReason) {
        let mut current_reason = self.reason_guard();
        if !self.inner.requested.load(Ordering::SeqCst) {
            *current_reason = Some(reason);
            self.inner.requested.store(true, Ordering::SeqCst);
        }
    }

    /// Returns true once cancellation has been requested.
    #[must_use]
    pub fn is_cancelled(&self) -> bool {
        self.inner.requested.load(Ordering::SeqCst)
    }

    /// Return the current cancellation reason, if any.
    #[must_use]
    pub fn reason(&self) -> Option<CancellationReason> {
        self.reason_guard().clone()
    }

    /// Build a serializable cancellation snapshot.
    #[must_use]
    pub fn snapshot(&self) -> CancellationSnapshot {
        let reason = self.reason_guard().clone();
        let requested = self.is_cancelled();
        CancellationSnapshot { requested, reason: if requested { reason } else { None } }
    }

    fn reason_guard(&self) -> std::sync::MutexGuard<'_, Option<CancellationReason>> {
        self.inner.reason.lock().unwrap_or_else(|poisoned| poisoned.into_inner())
    }
}

/// Serializable cancellation state captured in execution snapshots.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub struct CancellationSnapshot {
    pub requested: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reason: Option<CancellationReason>,
}

/// Reason a verification run was cancelled before all obligations completed.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum CancellationReason {
    UserRequested,
    DeadlineExceeded,
    ResourceLimitExceeded { limit: ResourceLimitKind },
    Superseded,
    HostShutdown,
    Custom { reason: String },
}

fn deserialize_bounded_sequence<'de, D, T>(
    deserializer: D,
    maximum: usize,
    description: &'static str,
) -> Result<Vec<T>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    struct BoundedSequenceVisitor<T> {
        maximum: usize,
        description: &'static str,
        marker: PhantomData<fn() -> T>,
    }

    impl<'de, T> Visitor<'de> for BoundedSequenceVisitor<T>
    where
        T: Deserialize<'de>,
    {
        type Value = Vec<T>;

        fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(formatter, "at most {} {}", self.maximum, self.description)
        }

        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            if sequence.size_hint().is_some_and(|hint| hint > self.maximum) {
                return Err(de::Error::custom(format!("too many {}", self.description)));
            }
            let mut records =
                Vec::with_capacity(sequence.size_hint().unwrap_or(0).min(self.maximum));
            while records.len() < self.maximum {
                let Some(record) = sequence.next_element::<T>()? else {
                    return Ok(records);
                };
                records.push(record);
            }
            if sequence.next_element::<IgnoredAny>()?.is_some() {
                return Err(de::Error::custom(format!("too many {}", self.description)));
            }
            Ok(records)
        }
    }

    deserializer.deserialize_seq(BoundedSequenceVisitor {
        maximum,
        description,
        marker: PhantomData,
    })
}

fn deserialize_bounded_run_records<'de, D, T>(deserializer: D) -> Result<Vec<T>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    deserialize_bounded_sequence(deserializer, MAX_VERIFIER_RUN_RECORDS, "verifier run records")
}

fn deserialize_bounded_run_diagnostics<'de, D>(deserializer: D) -> Result<Vec<String>, D::Error>
where
    D: Deserializer<'de>,
{
    deserialize_bounded_sequence(
        deserializer,
        MAX_VERIFIER_RUN_DIAGNOSTICS,
        "verifier run diagnostics",
    )
}

fn deserialize_bounded_evidence_diagnostics<'de, D>(
    deserializer: D,
) -> Result<Vec<String>, D::Error>
where
    D: Deserializer<'de>,
{
    deserialize_bounded_sequence(
        deserializer,
        MAX_EVIDENCE_DIAGNOSTICS_PER_RECORD,
        "evidence diagnostics",
    )
}

fn deserialize_bounded_engine_capabilities<'de, D>(
    deserializer: D,
) -> Result<Vec<EngineCapability>, D::Error>
where
    D: Deserializer<'de>,
{
    deserialize_bounded_sequence(deserializer, MAX_ENGINE_CAPABILITIES, "engine capabilities")
}

fn deserialize_bounded_engine_proof_modes<'de, D>(
    deserializer: D,
) -> Result<Vec<ReasoningKind>, D::Error>
where
    D: Deserializer<'de>,
{
    deserialize_bounded_sequence(deserializer, MAX_ENGINE_PROOF_MODES, "engine proof modes")
}

fn deserialize_bounded_bundle_metadata<'de, D>(
    deserializer: D,
) -> Result<Vec<MetadataEntry>, D::Error>
where
    D: Deserializer<'de>,
{
    deserialize_bounded_sequence(
        deserializer,
        MAX_BUNDLE_METADATA_ENTRIES,
        "bundle metadata entries",
    )
}

fn deserialize_bounded_record_metadata<'de, D>(
    deserializer: D,
) -> Result<Vec<MetadataEntry>, D::Error>
where
    D: Deserializer<'de>,
{
    deserialize_bounded_sequence(
        deserializer,
        MAX_RECORD_METADATA_ENTRIES,
        "record metadata entries",
    )
}

fn deserialize_bounded_record_items<'de, D, T>(deserializer: D) -> Result<Vec<T>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    deserialize_bounded_sequence(
        deserializer,
        MAX_RECORD_METADATA_ENTRIES,
        "nested verifier record items",
    )
}

/// Result envelope for one native verifier execution over one bundle.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct VerificationRunResult {
    pub schema_version: String,
    pub run_id: String,
    pub bundle_id: String,
    pub subject: BundleSubject,
    pub engine: EngineManifest,
    #[serde(default)]
    pub context: VerifierExecutionSnapshot,
    pub status: VerificationRunStatus,
    pub summary: VerificationRunSummary,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub requested_obligations: Vec<TrustObligation>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub evidence: Vec<ObligationEvidence>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub skipped: Vec<SkippedObligation>,
    pub publication: EvidencePublicationMetadata,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<String>,
}

impl VerificationRunResult {
    /// Build a result envelope from evidence returned by an engine.
    #[must_use]
    pub fn from_evidence(
        context: VerifierExecutionSnapshot,
        bundle: &TrustContractBundle,
        engine: EngineManifest,
        requested_obligations: &[TrustObligation],
        evidence: Vec<ObligationEvidence>,
    ) -> Self {
        let skipped = skipped_obligations(requested_obligations, &evidence, &context);
        let publication_result = run_publication_metadata(bundle, &evidence);
        let mut diagnostics = publication_result.conflicts;
        diagnostics.extend(run_engine_provenance_diagnostics(&engine, &evidence));
        diagnostics.extend(required_publication_metadata_diagnostics(
            &context.invocation,
            &publication_result.publication,
        ));
        let summary = VerificationRunSummary::from_parts(
            requested_obligations,
            &evidence,
            &skipped,
            diagnostics.len(),
        );
        let status = VerificationRunStatus::from_summary(&summary, &context);
        diagnostics.extend(release_blocking_skipped_proof_gap_diagnostics(&skipped));

        Self {
            schema_version: SCHEMA_VERSION.to_string(),
            run_id: context.run_id.clone(),
            bundle_id: bundle.bundle_id.clone(),
            subject: bundle.subject.clone(),
            engine,
            context,
            status,
            summary,
            requested_obligations: requested_obligations.to_vec(),
            evidence,
            skipped,
            publication: publication_result.publication,
            diagnostics,
        }
    }

    /// Returns true when every requested obligation was proved without
    /// cancellation, timeout, or skipped work.
    #[must_use]
    pub fn is_fully_proved(&self) -> bool {
        self.status == VerificationRunStatus::Proved && self.validate_derived_state().is_ok()
    }

    /// Validate every serialized field that is derived from the typed request
    /// and evidence payloads. A run status or summary is never independently
    /// authoritative: skips, publication aggregation, blocking diagnostics,
    /// counts, and the final status must all recompute exactly.
    pub fn validate_derived_state(&self) -> Result<(), String> {
        self.validate_input_state()?;
        let derived = derive_verification_run_state(self);
        if self.publication != derived.publication {
            return Err(
                "verifier result publication metadata does not match typed evidence aggregation"
                    .to_string(),
            );
        }
        if self.skipped != derived.skipped {
            return Err(
                "verifier result skipped obligations do not match requested/evidenced inventory"
                    .to_string(),
            );
        }
        if !diagnostics_contain_required(&self.diagnostics, &derived.required_diagnostics)
            || self
                .diagnostics
                .iter()
                .filter(|diagnostic| is_derived_verification_run_diagnostic(diagnostic))
                .count()
                != derived.required_diagnostics.len()
        {
            return Err(
                "verifier result derived provenance/publication/resource diagnostics are stale, duplicated, or incomplete"
                    .to_string(),
            );
        }
        if self.summary != derived.summary {
            return Err(
                "verifier result summary does not match typed obligations and evidence".to_string()
            );
        }
        if self.status != derived.status {
            return Err("verifier result status does not match recomputed summary".to_string());
        }
        Ok(())
    }

    fn validate_input_state(&self) -> Result<(), String> {
        if self.schema_version != SCHEMA_VERSION {
            return Err(format!(
                "unsupported verifier result schema `{}`; expected `{SCHEMA_VERSION}`",
                self.schema_version
            ));
        }
        validate_envelope_identifier("run_id", &self.run_id)?;
        validate_envelope_identifier("bundle_id", &self.bundle_id)?;
        validate_bundle_subject(&self.subject)?;
        validate_engine_manifest(&self.engine)?;
        if self.context.run_id != self.run_id {
            return Err("verifier result run_id does not match its execution context".to_string());
        }
        validate_cancellation_snapshot(&self.context.cancellation)?;
        validate_metadata_entries(
            "execution context",
            &self.context.metadata,
            MAX_RECORD_METADATA_ENTRIES,
        )?;
        validate_run_collection_limits(
            self.requested_obligations.len(),
            self.evidence.len(),
            self.skipped.len(),
            self.diagnostics.len(),
        )?;
        validate_diagnostics("verifier result", &self.diagnostics, MAX_VERIFIER_RUN_DIAGNOSTICS)?;

        let mut requested_ids = FxHashSet::default();
        for obligation in &self.requested_obligations {
            validate_obligation_record(obligation)?;
            if !requested_ids.insert(obligation.obligation_id.as_str()) {
                return Err(
                    "verifier result contains duplicate requested obligation IDs".to_string()
                );
            }
        }

        let mut evidence_ids = FxHashSet::default();
        let mut evidence_pairs = FxHashSet::default();
        for evidence in &self.evidence {
            if evidence.engine != self.engine {
                validate_engine_manifest(&evidence.engine)?;
            }
            validate_envelope_identifier("evidence_id", &evidence.evidence_id)?;
            validate_envelope_identifier("evidence obligation_id", &evidence.obligation_id)?;
            if !evidence_ids.insert(evidence.evidence_id.as_str()) {
                return Err("verifier result contains duplicate evidence IDs".to_string());
            }
            if !evidence_pairs
                .insert((evidence.evidence_id.as_str(), evidence.obligation_id.as_str()))
            {
                return Err(
                    "verifier result contains duplicate evidence identity pairs".to_string()
                );
            }
            if !requested_ids.contains(evidence.obligation_id.as_str()) {
                return Err(format!(
                    "verifier result evidence {} targets unrequested obligation {}",
                    evidence.evidence_id, evidence.obligation_id
                ));
            }
            validate_diagnostics(
                "obligation evidence",
                &evidence.diagnostics,
                MAX_EVIDENCE_DIAGNOSTICS_PER_RECORD,
            )?;
            if evidence.artifacts.len() > MAX_EVIDENCE_ARTIFACTS_PER_OBLIGATION {
                return Err(
                    "verifier result evidence exceeds the artifact safety limit".to_string()
                );
            }
            for artifact in &evidence.artifacts {
                validate_evidence_artifact(artifact)?;
            }
            validate_evidence_publication_metadata(&evidence.publication)?;
            if let Some(counterexample) = &evidence.counterexample {
                if evidence.status != EvidenceStatus::Failed {
                    return Err(format!(
                        "verifier result evidence {} carries a counterexample with non-failed status {:?}",
                        evidence.evidence_id, evidence.status
                    ));
                }
                validate_counterexample(counterexample)?;
            }
        }

        for skipped in &self.skipped {
            validate_envelope_identifier("skipped obligation_id", &skipped.obligation_id)?;
            // A skipped row's kind is copied verbatim into the release/audit
            // manifest (`manifest_obligations`) and into release-blocking
            // diagnostics, so it gets the same kind admission as a requested
            // obligation. Since the serde funnel (`deserialize_obligation_
            // namespace`) now rejects unpinned Custom namespaces at parse time,
            // `from_json_slice` can no longer deliver a forged kind here — this
            // check's remaining unique value is the IN-MEMORY lane: a row built
            // by pub-field construction never crosses serde, and this is the
            // only admission it meets.
            //
            // `validate_derived_state` would also catch a forged kind here, but
            // only indirectly, via the `self.skipped != derived.skipped`
            // recompute. Checking the field itself keeps "every public
            // ObligationKind is admitted" a local invariant of the record
            // rather than an emergent property of one comparison, and it holds
            // in `validate_input_state` alone, which `try_reconcile_derived_
            // state` runs before it rewrites derived fields.
            validate_obligation_kind(&skipped.kind)?;
        }
        Ok(())
    }

    /// Parse an untrusted JSON result through a whole-envelope byte cap before
    /// serde allocates nested strings, counterexamples, or materializations.
    pub fn from_json_slice(bytes: &[u8]) -> Result<Self, String> {
        validate_json_envelope_length(bytes.len(), "result")?;
        serde_json::from_slice(bytes).map_err(|error| error.to_string())
    }

    /// Build a release/audit manifest that accounts for every requested
    /// obligation and classifies every evidence item as accepted or rejected.
    #[must_use]
    pub fn to_manifest(&self) -> VerificationRunManifest {
        VerificationRunManifest::from_result(self)
    }

    /// Build a release manifest only if the caller's in-memory result already
    /// carries exact canonical derived state.
    pub fn try_to_manifest(&self) -> Result<VerificationRunManifest, String> {
        self.validate_derived_state()?;
        let manifest = VerificationRunManifest::from_validated_result(self);
        manifest.validate_derived_state()?;
        Ok(manifest)
    }

    /// Transactionally restore every public field derived from the current
    /// typed obligation/evidence carrier.
    ///
    /// This is intended for a trusted composite that atomically replaces one
    /// child evidence row (for example, after strict replay). It grants no new
    /// proof authority: status, counts, skips, publication metadata, and
    /// required diagnostics are recomputed solely from the public typed input.
    /// Structurally invalid input is rejected without changing `self`.
    pub fn try_reconcile_derived_state(&mut self) -> Result<(), String> {
        self.validate_input_state()?;
        let canonical = self.canonicalized_derived_state();
        canonical.validate_derived_state()?;
        *self = canonical;
        Ok(())
    }

    fn canonicalized_derived_state(&self) -> Self {
        let mut canonical = self.clone();
        let derived = derive_verification_run_state(&canonical);
        canonical.publication = derived.publication;
        canonical.skipped = derived.skipped;
        // These messages are serialized projections of typed run state, not
        // append-only engine history. Drop the reserved derived subset before
        // installing the current exact set so a repaired evidence carrier
        // cannot retain a stale release blocker or provenance conflict.
        canonical
            .diagnostics
            .retain(|diagnostic| !is_derived_verification_run_diagnostic(diagnostic));
        append_missing_diagnostics(&mut canonical.diagnostics, &derived.required_diagnostics);
        canonical.summary = derived.summary;
        canonical.status = derived.status;
        canonical
    }
}

fn validate_envelope_identifier(label: &str, value: &str) -> Result<(), String> {
    if canonical_artifact_owner_id(value) {
        Ok(())
    } else {
        Err(format!("verifier {label} is empty or non-canonical"))
    }
}

fn validate_canonical_text(label: &str, value: &str, maximum_bytes: usize) -> Result<(), String> {
    if value.is_empty()
        || value.trim() != value
        || value.len() > maximum_bytes
        || value.chars().any(char::is_control)
    {
        Err(format!("verifier {label} is empty, untrimmed, or exceeds its byte limit"))
    } else {
        Ok(())
    }
}

fn validate_optional_canonical_text(
    label: &str,
    value: &Option<String>,
    maximum_bytes: usize,
) -> Result<(), String> {
    if let Some(value) = value {
        validate_canonical_text(label, value, maximum_bytes)?;
    }
    Ok(())
}

fn validate_canonical_schema(label: &str, value: &str) -> Result<(), String> {
    validate_canonical_text(label, value, MAX_ENGINE_PROVENANCE_FIELD_BYTES)?;
    if !value.is_ascii()
        || !value.as_bytes().first().is_some_and(u8::is_ascii_alphanumeric)
        || value.bytes().any(|byte| {
            !(byte.is_ascii_alphanumeric()
                || matches!(byte, b'.' | b'_' | b'-' | b'/' | b':' | b'@'))
        })
    {
        return Err(format!("verifier {label} is not a canonical schema identifier"));
    }
    Ok(())
}

fn validate_canonical_uri(label: &str, uri: &str) -> Result<(), String> {
    validate_canonical_text(label, uri, MAX_EVIDENCE_ARTIFACT_URI_BYTES)?;
    if uri.bytes().any(|byte| byte.is_ascii_whitespace() || byte == b'\\') {
        return Err(format!("verifier {label} contains whitespace or a non-canonical separator"));
    }
    let Some((scheme, remainder)) = uri.split_once(':') else {
        return Err(format!("verifier {label} has no URI scheme"));
    };
    if remainder.is_empty()
        || !scheme.as_bytes().first().is_some_and(u8::is_ascii_alphabetic)
        || !scheme
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'+' | b'-' | b'.' | b'_'))
    {
        return Err(format!("verifier {label} has a non-canonical URI scheme"));
    }
    Ok(())
}

fn validate_bounded_json(label: &str, root: &serde_json::Value) -> Result<(), String> {
    let mut nodes = 0usize;
    let mut scalar_bytes = 0usize;
    let mut pending = vec![(root, 0usize)];
    while let Some((value, depth)) = pending.pop() {
        nodes = nodes
            .checked_add(1)
            .ok_or_else(|| format!("verifier {label} JSON node count overflowed"))?;
        if nodes > MAX_CONTRACT_PREDICATE_JSON_NODES {
            return Err(format!("verifier {label} exceeds the JSON node limit"));
        }
        if depth > MAX_CONTRACT_PREDICATE_JSON_DEPTH {
            return Err(format!("verifier {label} exceeds the JSON depth limit"));
        }
        match value {
            serde_json::Value::String(value) => {
                scalar_bytes = scalar_bytes
                    .checked_add(value.len())
                    .ok_or_else(|| format!("verifier {label} JSON scalar size overflowed"))?;
            }
            serde_json::Value::Number(value) => {
                scalar_bytes = scalar_bytes
                    .checked_add(value.to_string().len())
                    .ok_or_else(|| format!("verifier {label} JSON scalar size overflowed"))?;
            }
            serde_json::Value::Array(values) => {
                pending.extend(values.iter().map(|value| (value, depth.saturating_add(1))));
            }
            serde_json::Value::Object(object) => {
                for (key, value) in object {
                    scalar_bytes = scalar_bytes
                        .checked_add(key.len())
                        .ok_or_else(|| format!("verifier {label} JSON scalar size overflowed"))?;
                    pending.push((value, depth.saturating_add(1)));
                }
            }
            serde_json::Value::Null | serde_json::Value::Bool(_) => {}
        }
        if scalar_bytes > MAX_CONTRACT_PREDICATE_JSON_SCALAR_BYTES {
            return Err(format!("verifier {label} exceeds the JSON scalar byte limit"));
        }
    }
    Ok(())
}

fn validate_contract_predicate(predicate: &ContractPredicate) -> Result<(), String> {
    match predicate {
        ContractPredicate::TrustExpr { text } => {
            validate_canonical_text("TrustExpr predicate", text, MAX_CONTRACT_PREDICATE_TEXT_BYTES)
        }
        ContractPredicate::TrustIr { schema, value }
        | ContractPredicate::MathIr { schema, value }
        | ContractPredicate::MemoryIr { schema, value }
        | ContractPredicate::CanonicalJson { schema, value } => {
            validate_canonical_schema("contract predicate schema", schema)?;
            validate_bounded_json("contract predicate", value)?;
            if schema == TRUST_SPEC_PREDICATE_SCHEMA_VERSION {
                if !matches!(
                    predicate,
                    ContractPredicate::TrustIr { .. } | ContractPredicate::CanonicalJson { .. }
                ) {
                    return Err(
                        "typed TrustSpec schema is carried by an incompatible predicate variant"
                            .to_string(),
                    );
                }
                let typed: TrustSpecPredicate = serde_json::from_value(value.clone())
                    .map_err(|error| format!("invalid typed TrustSpec predicate: {error}"))?;
                validate_trust_spec_predicate(&typed)?;
                if serde_json::to_value(&typed).ok().as_ref() != Some(value) {
                    return Err(
                        "typed TrustSpec predicate is not the exact canonical schema shape"
                            .to_string(),
                    );
                }
            }
            Ok(())
        }
        ContractPredicate::TemporalModelRef { uri, hash } => {
            validate_canonical_uri("temporal model URI", uri)?;
            validate_artifact_hash("temporal model digest", hash)
        }
        ContractPredicate::Unsupported { reason } => validate_canonical_text(
            "unsupported contract reason",
            reason,
            MAX_VERIFIER_DIAGNOSTIC_BYTES,
        ),
    }
}

fn validate_artifact_hash(label: &str, hash: &ArtifactHash) -> Result<(), String> {
    if canonical_sha256_artifact_hash(hash) {
        Ok(())
    } else {
        Err(format!("verifier {label} is not canonical lowercase SHA-256"))
    }
}

fn validate_evidence_artifact(artifact: &EvidenceArtifact) -> Result<(), String> {
    if artifact.kind.canonical_wire_label().is_none() {
        return Err("verifier evidence artifact has an unknown kind".to_string());
    }
    validate_canonical_uri("evidence artifact URI", &artifact.uri)?;
    validate_artifact_hash("evidence artifact digest", &artifact.hash)?;
    if let Some(materialization) = &artifact.materialization {
        if !materialization.matches_hash(&artifact.hash) {
            return Err(
                "verifier evidence artifact materialization does not match its digest".to_string()
            );
        }
        if !canonical_proof_binding_id(materialization.proof_binding_id()) {
            return Err("verifier evidence artifact has a non-canonical proof binding".to_string());
        }
        for reference in materialization.referenced_artifacts() {
            if reference.kind.canonical_wire_label().is_none() {
                return Err("verifier evidence artifact references an unknown kind".to_string());
            }
            validate_artifact_hash("evidence artifact reference digest", &reference.hash)?;
        }
    }
    Ok(())
}

fn validate_trust_spec_sort(sort: TrustSpecSort) -> Result<(), String> {
    match sort {
        TrustSpecSort::Bool | TrustSpecSort::Int => Ok(()),
        TrustSpecSort::BitVec { width }
            if (1..=MAX_TRUST_SPEC_BITVECTOR_WIDTH).contains(&width) =>
        {
            Ok(())
        }
        TrustSpecSort::BitVec { width } => Err(format!(
            "typed TrustSpec bitvector width {width} is zero or exceeds {MAX_TRUST_SPEC_BITVECTOR_WIDTH}"
        )),
        TrustSpecSort::Array { element } => {
            validate_trust_spec_scalar_sort("array element", element)
        }
        // Only the two Rust machine float shapes are meaningful to producers
        // and consumers; every other (eb, sb) fails closed like an
        // out-of-bounds bitvector width.
        TrustSpecSort::Float { eb: 8, sb: 24 } | TrustSpecSort::Float { eb: 11, sb: 53 } => Ok(()),
        TrustSpecSort::Float { eb, sb } => Err(format!(
            "typed TrustSpec float shape eb={eb} sb={sb} is not IEEE-754 binary32 or binary64"
        )),
    }
}

fn validate_trust_spec_scalar_sort(
    role: &str,
    sort: TrustSpecScalarSort,
) -> Result<(), String> {
    match sort {
        TrustSpecScalarSort::Bool | TrustSpecScalarSort::Int => Ok(()),
        TrustSpecScalarSort::BitVec { width }
            if (1..=MAX_TRUST_SPEC_BITVECTOR_WIDTH).contains(&width) =>
        {
            Ok(())
        }
        TrustSpecScalarSort::BitVec { width } => Err(format!(
            "typed TrustSpec {role} bitvector width {width} is zero or exceeds {MAX_TRUST_SPEC_BITVECTOR_WIDTH}"
        )),
    }
}

fn validate_canonical_decimal(label: &str, value: &str, signed: bool) -> Result<(), String> {
    if value.is_empty() || value.len() > MAX_ENGINE_PROVENANCE_FIELD_BYTES {
        return Err(format!("typed TrustSpec {label} is empty or oversized"));
    }
    let digits = if signed { value.strip_prefix('-').unwrap_or(value) } else { value };
    if digits.is_empty()
        || !digits.bytes().all(|byte| byte.is_ascii_digit())
        || (digits.len() > 1 && digits.starts_with('0'))
        || value == "-0"
        || (!signed && value.starts_with('-'))
    {
        return Err(format!("typed TrustSpec {label} is not a canonical decimal"));
    }
    Ok(())
}

fn validate_trust_spec_predicate(predicate: &TrustSpecPredicate) -> Result<(), String> {
    if !predicate.has_current_schema() {
        return Err("typed TrustSpec predicate uses an unsupported schema".to_string());
    }
    validate_trust_spec_sort(predicate.root_sort)?;
    if predicate.root_sort != TrustSpecSort::Bool || predicate.root.sort != predicate.root_sort {
        return Err("typed TrustSpec predicate root must be consistently Bool-sorted".to_string());
    }
    if predicate.variables.len() > MAX_RECORD_METADATA_ENTRIES {
        return Err("typed TrustSpec predicate exceeds the variable limit".to_string());
    }
    let mut declared = BTreeMap::new();
    for variable in &predicate.variables {
        validate_canonical_text(
            "TrustSpec variable name",
            &variable.name,
            MAX_ENGINE_PROVENANCE_FIELD_BYTES,
        )?;
        validate_trust_spec_sort(variable.sort)?;
        if declared.insert(variable.name.clone(), variable.sort).is_some() {
            return Err("typed TrustSpec predicate has duplicate variables".to_string());
        }
    }
    let mut nodes = 0usize;
    validate_trust_spec_expr(&predicate.root, &declared, &mut Vec::new(), 0, &mut nodes)
}

fn validate_trust_spec_expr(
    expr: &TrustSpecExpr,
    declared: &BTreeMap<String, TrustSpecSort>,
    bound: &mut Vec<(String, TrustSpecSort)>,
    depth: usize,
    nodes: &mut usize,
) -> Result<(), String> {
    *nodes = nodes
        .checked_add(1)
        .ok_or_else(|| "typed TrustSpec expression node count overflowed".to_string())?;
    if *nodes > MAX_CONTRACT_PREDICATE_JSON_NODES {
        return Err("typed TrustSpec expression exceeds the node limit".to_string());
    }
    if depth > MAX_CONTRACT_PREDICATE_JSON_DEPTH {
        return Err("typed TrustSpec expression exceeds the depth limit".to_string());
    }
    validate_trust_spec_sort(expr.sort)?;
    let child_depth = depth.saturating_add(1);
    let require_sort = |actual: TrustSpecSort, expected: TrustSpecSort, role: &str| {
        if actual == expected {
            Ok(())
        } else {
            Err(format!("typed TrustSpec {role} has inconsistent sort"))
        }
    };
    match &expr.kind {
        TrustSpecExprKind::BoolLiteral { .. } => {
            require_sort(expr.sort, TrustSpecSort::Bool, "boolean literal")
        }
        TrustSpecExprKind::IntLiteral { value } => {
            require_sort(expr.sort, TrustSpecSort::Int, "integer literal")?;
            validate_canonical_decimal("integer literal", value, true)
        }
        TrustSpecExprKind::Variable { name } => {
            validate_canonical_text(
                "TrustSpec variable reference",
                name,
                MAX_ENGINE_PROVENANCE_FIELD_BYTES,
            )?;
            let expected = bound
                .iter()
                .rev()
                .find(|(candidate, _)| candidate == name)
                .map(|(_, sort)| *sort)
                .or_else(|| declared.get(name).copied())
                .ok_or_else(|| format!("typed TrustSpec variable `{name}` is undeclared"))?;
            require_sort(expr.sort, expected, "variable reference")
        }
        TrustSpecExprKind::Result => {
            if matches!(expr.sort, TrustSpecSort::Array { .. }) {
                Err("typed TrustSpec result values cannot have array sort".to_string())
            } else {
                Ok(())
            }
        }
        TrustSpecExprKind::Unary { op, expr: child } => {
            let expected = match op {
                TrustSpecUnaryOp::Not => TrustSpecSort::Bool,
                TrustSpecUnaryOp::Neg => TrustSpecSort::Int,
            };
            require_sort(child.sort, expected, "unary operand")?;
            require_sort(expr.sort, expected, "unary result")?;
            validate_trust_spec_expr(child, declared, bound, child_depth, nodes)
        }
        TrustSpecExprKind::Binary { op, lhs, rhs } => {
            let operand_sort = match op {
                // Arithmetic stays Int-only: float arithmetic would need
                // rounding-mode semantics this IR does not carry and is
                // rejected fail-closed here.
                TrustSpecBinaryOp::Add
                | TrustSpecBinaryOp::Sub
                | TrustSpecBinaryOp::Mul
                | TrustSpecBinaryOp::Div
                | TrustSpecBinaryOp::Mod => Some(TrustSpecSort::Int),
                // Ordered comparisons are Int by default; two operands of the
                // SAME Float sort are additionally admitted, denoting the
                // IEEE-754 predicates (`fp.lt`/`fp.leq`/`fp.gt`/`fp.geq` —
                // false on NaN operands), never bit-pattern order.
                TrustSpecBinaryOp::Lt
                | TrustSpecBinaryOp::Le
                | TrustSpecBinaryOp::Gt
                | TrustSpecBinaryOp::Ge => match (lhs.sort, rhs.sort) {
                    (TrustSpecSort::Float { .. }, TrustSpecSort::Float { .. })
                        if lhs.sort == rhs.sort =>
                    {
                        None
                    }
                    _ => Some(TrustSpecSort::Int),
                },
                TrustSpecBinaryOp::And | TrustSpecBinaryOp::Or | TrustSpecBinaryOp::Implies => {
                    Some(TrustSpecSort::Bool)
                }
                // On same-Float-sorted operands, Eq/Ne denote the IEEE-754
                // equality of the Rust source (`fp.eq` and its negation:
                // NaN != NaN, +0.0 == -0.0) — never the SMT bit/identity `=`.
                TrustSpecBinaryOp::Eq | TrustSpecBinaryOp::Ne => None,
            };
            if let Some(sort) = operand_sort {
                require_sort(lhs.sort, sort, "binary lhs")?;
                require_sort(rhs.sort, sort, "binary rhs")?;
            } else if lhs.sort != rhs.sort {
                return Err("typed TrustSpec equality operands have different sorts".to_string());
            } else if matches!(lhs.sort, TrustSpecSort::Array { .. }) {
                return Err(
                    "typed TrustSpec array equality is outside the read-only Select fragment"
                        .to_string(),
                );
            }
            require_sort(expr.sort, op.result_sort(), "binary result")?;
            validate_trust_spec_expr(lhs, declared, bound, child_depth, nodes)?;
            validate_trust_spec_expr(rhs, declared, bound, child_depth, nodes)
        }
        TrustSpecExprKind::Old { expr: child } => {
            if matches!(child.sort, TrustSpecSort::Array { .. }) {
                return Err(
                    "typed TrustSpec old(array) is outside the read-only Select fragment"
                        .to_string(),
                );
            }
            require_sort(expr.sort, child.sort, "old result")?;
            validate_trust_spec_expr(child, declared, bound, child_depth, nodes)
        }
        TrustSpecExprKind::Field { base, field } => {
            if matches!(base.sort, TrustSpecSort::Array { .. })
                || matches!(expr.sort, TrustSpecSort::Array { .. })
            {
                return Err(
                    "typed TrustSpec field projection cannot use or produce an array".to_string()
                );
            }
            validate_canonical_text(
                "TrustSpec field name",
                field,
                MAX_ENGINE_PROVENANCE_FIELD_BYTES,
            )?;
            validate_trust_spec_expr(base, declared, bound, child_depth, nodes)
        }
        TrustSpecExprKind::Index { base, index } => {
            let TrustSpecSort::Array { element } = base.sort else {
                return Err(
                    "typed TrustSpec index base is not an Int-indexed scalar array".to_string()
                );
            };
            if !matches!(&base.kind, TrustSpecExprKind::Variable { .. }) {
                return Err(
                    "typed TrustSpec index base must be a direct declared array variable"
                        .to_string(),
                );
            }
            require_sort(index.sort, TrustSpecSort::Int, "index operand")?;
            require_sort(expr.sort, element.expression_sort(), "index result")?;
            validate_trust_spec_expr(base, declared, bound, child_depth, nodes)?;
            validate_trust_spec_expr(index, declared, bound, child_depth, nodes)
        }
        TrustSpecExprKind::Quantifier { variable, variable_sort, body, .. } => {
            validate_canonical_text(
                "TrustSpec quantified variable",
                variable,
                MAX_ENGINE_PROVENANCE_FIELD_BYTES,
            )?;
            validate_trust_spec_sort(*variable_sort)?;
            if matches!(*variable_sort, TrustSpecSort::Array { .. }) {
                return Err(
                    "typed TrustSpec quantifiers cannot bind array variables".to_string()
                );
            }
            // The float fragment is comparisons + literals + free variables
            // only; quantified float domains are outside it (fail-closed like
            // array binders).
            if matches!(*variable_sort, TrustSpecSort::Float { .. }) {
                return Err(
                    "typed TrustSpec quantifiers cannot bind float variables".to_string()
                );
            }
            require_sort(expr.sort, TrustSpecSort::Bool, "quantifier result")?;
            require_sort(body.sort, TrustSpecSort::Bool, "quantifier body")?;
            bound.push((variable.clone(), *variable_sort));
            let result = validate_trust_spec_expr(body, declared, bound, child_depth, nodes);
            bound.pop();
            result
        }
        TrustSpecExprKind::BitVecLiteral { value, width } => {
            validate_trust_spec_sort(TrustSpecSort::BitVec { width: *width })?;
            require_sort(expr.sort, TrustSpecSort::BitVec { width: *width }, "bitvector literal")?;
            validate_canonical_decimal("bitvector literal", value, false)
        }
        TrustSpecExprKind::FloatLiteral { bits, eb, sb } => {
            validate_trust_spec_sort(TrustSpecSort::Float { eb: *eb, sb: *sb })?;
            require_sort(expr.sort, TrustSpecSort::Float { eb: *eb, sb: *sb }, "float literal")?;
            // The raw bits must fit the declared interchange format exactly
            // (for binary32 the high 32 bits of the carrier are zero). NaN
            // payloads and signed zeros are representational — bits are bits.
            let total_width = eb
                .checked_add(*sb)
                .ok_or_else(|| "typed TrustSpec float literal width overflowed".to_string())?;
            if total_width < 64 && (bits >> total_width) != 0 {
                return Err(format!(
                    "typed TrustSpec float literal bits exceed the {total_width}-bit format"
                ));
            }
            Ok(())
        }
        TrustSpecExprKind::BvUnary { op, expr: child, width } => {
            validate_trust_spec_sort(TrustSpecSort::BitVec { width: *width })?;
            let TrustSpecSort::BitVec { width: input_width } = child.sort else {
                return Err(
                    "typed TrustSpec bitvector unary operand is not a bitvector".to_string()
                );
            };
            let expected_width = match op {
                TrustSpecBvUnaryOp::Not => input_width,
                TrustSpecBvUnaryOp::SignExt { extend_by } => {
                    if *extend_by == 0 {
                        return Err("typed TrustSpec sign extension is zero-width".to_string());
                    }
                    input_width.checked_add(*extend_by).ok_or_else(|| {
                        "typed TrustSpec sign-extension width overflowed".to_string()
                    })?
                }
                TrustSpecBvUnaryOp::Extract { high, low } => {
                    if high < low || *high >= input_width {
                        return Err(
                            "typed TrustSpec bitvector extraction range is invalid".to_string()
                        );
                    }
                    high - low + 1
                }
            };
            if expected_width != *width {
                return Err(
                    "typed TrustSpec bitvector unary result width is inconsistent".to_string()
                );
            }
            require_sort(
                expr.sort,
                TrustSpecSort::BitVec { width: *width },
                "bitvector unary result",
            )?;
            validate_trust_spec_expr(child, declared, bound, child_depth, nodes)
        }
        TrustSpecExprKind::BvBinary { op, lhs, rhs, width } => {
            validate_trust_spec_sort(TrustSpecSort::BitVec { width: *width })?;
            require_sort(lhs.sort, TrustSpecSort::BitVec { width: *width }, "bitvector lhs")?;
            require_sort(rhs.sort, TrustSpecSort::BitVec { width: *width }, "bitvector rhs")?;
            require_sort(expr.sort, op.result_sort(*width), "bitvector binary result")?;
            validate_trust_spec_expr(lhs, declared, bound, child_depth, nodes)?;
            validate_trust_spec_expr(rhs, declared, bound, child_depth, nodes)
        }
        TrustSpecExprKind::BvFromInt { expr: child, width } => {
            validate_trust_spec_sort(TrustSpecSort::BitVec { width: *width })?;
            require_sort(child.sort, TrustSpecSort::Int, "int-to-bitvector operand")?;
            require_sort(
                expr.sort,
                TrustSpecSort::BitVec { width: *width },
                "int-to-bitvector result",
            )?;
            validate_trust_spec_expr(child, declared, bound, child_depth, nodes)
        }
        TrustSpecExprKind::IntFromBv { expr: child, width, .. } => {
            validate_trust_spec_sort(TrustSpecSort::BitVec { width: *width })?;
            require_sort(
                child.sort,
                TrustSpecSort::BitVec { width: *width },
                "bitvector-to-int operand",
            )?;
            require_sort(expr.sort, TrustSpecSort::Int, "bitvector-to-int result")?;
            validate_trust_spec_expr(child, declared, bound, child_depth, nodes)
        }
        TrustSpecExprKind::IsVariant { scrutinee, variant } => {
            if matches!(scrutinee.sort, TrustSpecSort::Array { .. }) {
                return Err(
                    "typed TrustSpec variant tests cannot inspect an array value".to_string()
                );
            }
            validate_canonical_text(
                "TrustSpec variant name",
                variant,
                MAX_ENGINE_PROVENANCE_FIELD_BYTES,
            )?;
            require_sort(expr.sort, TrustSpecSort::Bool, "variant test result")?;
            validate_trust_spec_expr(scrutinee, declared, bound, child_depth, nodes)
        }
        TrustSpecExprKind::VariantField { scrutinee, variant, .. } => {
            if matches!(scrutinee.sort, TrustSpecSort::Array { .. })
                || matches!(expr.sort, TrustSpecSort::Array { .. })
            {
                return Err(
                    "typed TrustSpec variant fields cannot use or produce an array".to_string()
                );
            }
            validate_canonical_text(
                "TrustSpec variant name",
                variant,
                MAX_ENGINE_PROVENANCE_FIELD_BYTES,
            )?;
            validate_trust_spec_expr(scrutinee, declared, bound, child_depth, nodes)
        }
    }
}

fn validate_bundle_subject(subject: &BundleSubject) -> Result<(), String> {
    match subject {
        BundleSubject::Crate { name } => {
            validate_canonical_text("subject crate name", name, MAX_ENGINE_PROVENANCE_FIELD_BYTES)
        }
        BundleSubject::Function { crate_name, path } => {
            validate_canonical_text(
                "subject function crate name",
                crate_name,
                MAX_ENGINE_PROVENANCE_FIELD_BYTES,
            )?;
            validate_canonical_text(
                "subject function path",
                path,
                MAX_ENGINE_PROVENANCE_FIELD_BYTES,
            )
        }
        BundleSubject::Artifact { name, kind } => {
            validate_canonical_text(
                "subject artifact name",
                name,
                MAX_ENGINE_PROVENANCE_FIELD_BYTES,
            )?;
            validate_canonical_text(
                "subject artifact kind",
                kind,
                MAX_ENGINE_PROVENANCE_FIELD_BYTES,
            )
        }
    }
}

fn validate_obligation_kind(kind: &ObligationKind) -> Result<(), String> {
    if let ObligationKind::Custom { namespace, name } = kind {
        validate_canonical_text(
            "custom obligation namespace",
            namespace,
            MAX_ENGINE_PROVENANCE_FIELD_BYTES,
        )?;
        validate_canonical_text("custom obligation name", name, MAX_ENGINE_PROVENANCE_FIELD_BYTES)?;
        // The namespace is authority-bearing, so it is admitted from the pinned
        // vocabulary this crate owns rather than accepted as producer free text.
        if !is_admitted_obligation_namespace(namespace) {
            return Err(format!(
                "verifier custom obligation namespace `{namespace}` is not an admitted Trust \
                 obligation namespace"
            ));
        }
    }
    Ok(())
}

fn validate_engine_manifest(engine: &EngineManifest) -> Result<(), String> {
    validate_canonical_text("engine name", &engine.name, MAX_ENGINE_PROVENANCE_FIELD_BYTES)?;
    validate_canonical_text("engine version", &engine.version, MAX_ENGINE_PROVENANCE_FIELD_BYTES)?;
    if engine.api_version != API_VERSION {
        return Err(format!(
            "verifier engine {} uses incompatible API version {}; expected {API_VERSION}",
            engine.name, engine.api_version
        ));
    }
    validate_optional_canonical_text(
        "engine repository",
        &engine.repository,
        MAX_ENGINE_PROVENANCE_FIELD_BYTES,
    )?;
    validate_optional_canonical_text(
        "engine revision",
        &engine.revision,
        MAX_ENGINE_PROVENANCE_FIELD_BYTES,
    )?;
    if engine.capabilities.len() > MAX_ENGINE_CAPABILITIES
        || engine.proof_modes.len() > MAX_ENGINE_PROOF_MODES
    {
        return Err("verifier engine manifest exceeds a collection safety limit".to_string());
    }
    let mut capability_kinds = FxHashSet::default();
    for capability in &engine.capabilities {
        validate_obligation_kind(&capability.obligation_kind)?;
        if !capability_kinds.insert(&capability.obligation_kind) {
            return Err("verifier engine manifest contains duplicate capability kinds".to_string());
        }
        match &capability.support {
            SupportLevel::Unsupported { reason } | SupportLevel::Experimental { reason } => {
                validate_canonical_text(
                    "engine capability reason",
                    reason,
                    MAX_VERIFIER_DIAGNOSTIC_BYTES,
                )?;
            }
            SupportLevel::Supported | SupportLevel::Preferred => {}
        }
    }
    let mut proof_modes = FxHashSet::default();
    if engine.proof_modes.iter().any(|mode| !proof_modes.insert(mode)) {
        return Err("verifier engine manifest contains duplicate proof modes".to_string());
    }
    Ok(())
}

fn validate_metadata_entries(
    label: &str,
    metadata: &[MetadataEntry],
    maximum: usize,
) -> Result<(), String> {
    if metadata.len() > maximum {
        return Err(format!("verifier {label} exceeds the metadata entry limit"));
    }
    let mut keys = FxHashSet::default();
    for entry in metadata {
        validate_canonical_text(
            &format!("{label} metadata key"),
            &entry.key,
            MAX_ENGINE_PROVENANCE_FIELD_BYTES,
        )?;
        if entry.value.len() > MAX_METADATA_VALUE_BYTES {
            return Err(format!("verifier {label} metadata value exceeds the byte limit"));
        }
        if !keys.insert(entry.key.as_str()) {
            return Err(format!(
                "verifier {label} contains duplicate metadata key `{}`",
                entry.key
            ));
        }
    }
    Ok(())
}

fn validate_source_location(source: &SourceLocation) -> Result<(), String> {
    validate_optional_canonical_text("source file", &source.file, MAX_ENGINE_PROVENANCE_FIELD_BYTES)
}

fn validate_contract_record(contract: &TrustContract) -> Result<(), String> {
    validate_envelope_identifier("contract_id", &contract.contract_id)?;
    validate_contract_predicate(&contract.predicate)?;
    validate_source_location(&contract.source)?;
    validate_metadata_entries("contract", &contract.metadata, MAX_RECORD_METADATA_ENTRIES)
}

fn validate_proof_item_record(proof_item: &TrustProofItem) -> Result<(), String> {
    validate_envelope_identifier("proof_item_id", &proof_item.proof_item_id)?;
    validate_canonical_text(
        "proof item name",
        &proof_item.name,
        MAX_ENGINE_PROVENANCE_FIELD_BYTES,
    )?;
    validate_source_location(&proof_item.source)?;
    if proof_item.signature.params.len() > MAX_RECORD_METADATA_ENTRIES
        || proof_item.contracts.len() > MAX_RECORD_METADATA_ENTRIES
    {
        return Err("verifier proof item exceeds a nested collection safety limit".to_string());
    }
    for parameter in &proof_item.signature.params {
        validate_optional_canonical_text(
            "proof item parameter name",
            &parameter.name,
            MAX_ENGINE_PROVENANCE_FIELD_BYTES,
        )?;
        validate_canonical_text(
            "proof item parameter type",
            &parameter.ty,
            MAX_ENGINE_PROVENANCE_FIELD_BYTES,
        )?;
    }
    validate_optional_canonical_text(
        "proof item output type",
        &proof_item.signature.output,
        MAX_ENGINE_PROVENANCE_FIELD_BYTES,
    )?;
    match &proof_item.target {
        ProofItemTarget::LocalNamespace => {}
        ProofItemTarget::Function { crate_name, path } => {
            validate_canonical_text(
                "proof target crate name",
                crate_name,
                MAX_ENGINE_PROVENANCE_FIELD_BYTES,
            )?;
            validate_canonical_text(
                "proof target function path",
                path,
                MAX_ENGINE_PROVENANCE_FIELD_BYTES,
            )?;
        }
        ProofItemTarget::Contract { contract_id } => {
            validate_envelope_identifier("proof target contract_id", contract_id)?;
        }
        ProofItemTarget::Crate { name } => {
            validate_canonical_text(
                "proof target crate name",
                name,
                MAX_ENGINE_PROVENANCE_FIELD_BYTES,
            )?;
        }
    }
    match &proof_item.body {
        ProofItemBody::CompilerOwned { body_ref } => validate_canonical_text(
            "compiler proof body reference",
            body_ref,
            MAX_METADATA_VALUE_BYTES,
        )?,
        ProofItemBody::NativeScript { engine, text } => {
            validate_canonical_text(
                "native proof script engine",
                engine,
                MAX_ENGINE_PROVENANCE_FIELD_BYTES,
            )?;
            if text.trim().is_empty() || text.len() > MAX_METADATA_VALUE_BYTES {
                return Err(
                    "verifier native proof script is empty or exceeds the byte limit".to_string()
                );
            }
        }
        ProofItemBody::Unsupported { reason } => validate_canonical_text(
            "unsupported proof item reason",
            reason,
            MAX_VERIFIER_DIAGNOSTIC_BYTES,
        )?,
    }
    let mut contract_ids = FxHashSet::default();
    for contract in &proof_item.contracts {
        validate_contract_record(contract)?;
        if !contract_ids.insert(contract.contract_id.as_str()) {
            return Err("verifier proof item contains duplicate contract IDs".to_string());
        }
    }
    validate_metadata_entries("proof item", &proof_item.metadata, MAX_RECORD_METADATA_ENTRIES)
}

fn validate_obligation_record(obligation: &TrustObligation) -> Result<(), String> {
    validate_envelope_identifier("obligation_id", &obligation.obligation_id)?;
    validate_obligation_kind(&obligation.kind)?;
    if let Some(contract_id) = &obligation.contract_id {
        validate_envelope_identifier("obligation contract_id", contract_id)?;
    }
    if let Some(proof_item_id) = &obligation.proof_item_id {
        validate_envelope_identifier("obligation proof_item_id", proof_item_id)?;
    }
    validate_source_location(&obligation.source)?;
    if obligation.description.len() > MAX_OBLIGATION_DESCRIPTION_BYTES {
        return Err("verifier obligation description exceeds the byte limit".to_string());
    }
    if obligation.summary_facts.len() > MAX_RECORD_METADATA_ENTRIES {
        return Err("verifier obligation exceeds the summary-fact count limit".to_string());
    }
    if obligation
        .metadata
        .iter()
        .any(|entry| entry.key == TRUST_MC_DEFAULT_FUNCTION_OBLIGATION_METADATA_KEY)
        && !obligation.is_default_admission()
    {
        return Err(
            "verifier obligation carries a malformed or duplicate synthetic-admission identity"
                .to_string(),
        );
    }
    let mut summary_fact_ids = BTreeSet::new();
    for fact in &obligation.summary_facts {
        validate_summary_fact(fact)?;
        if !summary_fact_ids.insert(fact.id.as_str()) {
            return Err("verifier obligation contains duplicate summary-fact IDs".to_string());
        }
    }
    validate_metadata_entries("obligation", &obligation.metadata, MAX_RECORD_METADATA_ENTRIES)
}

fn validate_publication_metadata(publication: &PublicationMetadata) -> Result<(), String> {
    for (label, value) in [
        ("publication candidate_id", &publication.candidate_id),
        ("publication source_repo", &publication.source_repo),
        ("publication source_commit", &publication.source_commit),
        ("publication crate_name", &publication.crate_name),
        ("publication crate_version", &publication.crate_version),
        ("publication trust_engines_lock_hash", &publication.trust_engines_lock_hash),
        ("publication dpub_plan_hash", &publication.dpub_plan_hash),
        ("publication conformance_report_hash", &publication.conformance_report_hash),
        ("publication release_gate_report_hash", &publication.release_gate_report_hash),
    ] {
        validate_optional_canonical_text(label, value, MAX_ENGINE_PROVENANCE_FIELD_BYTES)?;
    }
    Ok(())
}

fn validate_evidence_publication_metadata(
    publication: &EvidencePublicationMetadata,
) -> Result<(), String> {
    for (label, value) in [
        ("evidence dscan_attestation_hash", &publication.dscan_attestation_hash),
        ("evidence dpub_release_id", &publication.dpub_release_id),
        ("evidence publication_plan_hash", &publication.publication_plan_hash),
        ("evidence trust_engines_lock_hash", &publication.trust_engines_lock_hash),
        ("evidence bundle hash", &publication.evidence_bundle_hash),
    ] {
        validate_optional_canonical_text(label, value, MAX_ENGINE_PROVENANCE_FIELD_BYTES)?;
    }
    Ok(())
}

fn validate_contract_bundle(bundle: &TrustContractBundle) -> Result<(), String> {
    if bundle.schema_version != SCHEMA_VERSION {
        return Err(format!(
            "unsupported verifier bundle schema `{}`; expected `{SCHEMA_VERSION}`",
            bundle.schema_version
        ));
    }
    validate_envelope_identifier("bundle_id", &bundle.bundle_id)?;
    validate_bundle_subject(&bundle.subject)?;
    if bundle.contracts.len() > MAX_VERIFIER_RUN_RECORDS
        || bundle.proof_items.len() > MAX_VERIFIER_RUN_RECORDS
        || bundle.obligations.len() > MAX_VERIFIER_RUN_RECORDS
    {
        return Err("verifier bundle exceeds an individual collection safety limit".to_string());
    }
    let aggregate = bundle
        .contracts
        .len()
        .checked_add(bundle.proof_items.len())
        .and_then(|count| count.checked_add(bundle.obligations.len()))
        .ok_or_else(|| "verifier bundle record count overflowed".to_string())?;
    if aggregate > MAX_VERIFIER_RUN_AGGREGATE_RECORDS {
        return Err("verifier bundle exceeds the aggregate record safety limit".to_string());
    }

    let mut contract_ids = FxHashSet::default();
    for contract in &bundle.contracts {
        validate_contract_record(contract)?;
        if !contract_ids.insert(contract.contract_id.as_str()) {
            return Err("verifier bundle contains duplicate contract IDs".to_string());
        }
    }
    let mut proof_item_ids = FxHashSet::default();
    for proof_item in &bundle.proof_items {
        validate_proof_item_record(proof_item)?;
        if !proof_item_ids.insert(proof_item.proof_item_id.as_str()) {
            return Err("verifier bundle contains duplicate proof-item IDs".to_string());
        }
    }
    let mut obligation_ids = FxHashSet::default();
    for obligation in &bundle.obligations {
        validate_obligation_record(obligation)?;
        if !obligation_ids.insert(obligation.obligation_id.as_str()) {
            return Err("verifier bundle contains duplicate obligation IDs".to_string());
        }
    }
    validate_publication_metadata(&bundle.publication)?;
    validate_metadata_entries("bundle", &bundle.metadata, MAX_BUNDLE_METADATA_ENTRIES)
}

fn validate_cancellation_snapshot(cancellation: &CancellationSnapshot) -> Result<(), String> {
    if !cancellation.requested && cancellation.reason.is_some() {
        return Err(
            "verifier cancellation snapshot carries a reason without a cancellation request"
                .to_string(),
        );
    }
    if let Some(CancellationReason::Custom { reason }) = &cancellation.reason
        && (reason.trim().is_empty() || reason.len() > MAX_VERIFIER_DIAGNOSTIC_BYTES)
    {
        return Err("verifier cancellation reason is empty or exceeds the byte limit".to_string());
    }
    Ok(())
}

fn validate_run_collection_limits(
    obligations: usize,
    evidence: usize,
    skipped: usize,
    diagnostics: usize,
) -> Result<(), String> {
    if obligations > MAX_VERIFIER_RUN_RECORDS
        || evidence > MAX_VERIFIER_RUN_RECORDS
        || skipped > MAX_VERIFIER_RUN_RECORDS
        || diagnostics > MAX_VERIFIER_RUN_DIAGNOSTICS
    {
        return Err("verifier run exceeds an individual collection safety limit".to_string());
    }
    let aggregate = obligations
        .checked_add(evidence)
        .and_then(|count| count.checked_add(skipped))
        .ok_or_else(|| "verifier run record count overflowed".to_string())?;
    if aggregate > MAX_VERIFIER_RUN_AGGREGATE_RECORDS {
        return Err("verifier run exceeds the aggregate record safety limit".to_string());
    }
    Ok(())
}

fn validate_diagnostics(label: &str, diagnostics: &[String], maximum: usize) -> Result<(), String> {
    if diagnostics.len() > maximum {
        return Err(format!("{label} exceeds the diagnostic count limit"));
    }
    if diagnostics.iter().any(|diagnostic| diagnostic.len() > MAX_VERIFIER_DIAGNOSTIC_BYTES) {
        return Err(format!("{label} contains a diagnostic exceeding the byte limit"));
    }
    Ok(())
}

fn validate_json_envelope_length(length: usize, label: &str) -> Result<(), String> {
    if length > MAX_VERIFIER_JSON_ENVELOPE_BYTES {
        Err(format!(
            "verifier {label} JSON exceeds the {}-byte ingress limit",
            MAX_VERIFIER_JSON_ENVELOPE_BYTES
        ))
    } else {
        Ok(())
    }
}

fn validate_counterexample(counterexample: &Counterexample) -> Result<(), String> {
    if counterexample.format.trim().is_empty()
        || counterexample.format.len() > MAX_OBLIGATION_DESCRIPTION_BYTES
    {
        return Err("verifier counterexample format is empty or exceeds the byte limit".to_string());
    }

    let mut nodes = 0usize;
    let mut scalar_bytes = counterexample.format.len();
    let mut pending = vec![(&counterexample.data, 0usize)];
    while let Some((value, depth)) = pending.pop() {
        nodes = nodes
            .checked_add(1)
            .ok_or_else(|| "verifier counterexample node count overflowed".to_string())?;
        if nodes > MAX_COUNTEREXAMPLE_JSON_NODES {
            return Err("verifier counterexample exceeds the JSON node limit".to_string());
        }
        if depth > MAX_COUNTEREXAMPLE_JSON_DEPTH {
            return Err("verifier counterexample exceeds the JSON depth limit".to_string());
        }
        match value {
            serde_json::Value::String(value) => {
                scalar_bytes = scalar_bytes.checked_add(value.len()).ok_or_else(|| {
                    "verifier counterexample scalar byte count overflowed".to_string()
                })?;
            }
            serde_json::Value::Array(values) => {
                pending.extend(values.iter().map(|value| (value, depth.saturating_add(1))));
            }
            serde_json::Value::Object(object) => {
                for (key, value) in object {
                    scalar_bytes = scalar_bytes.checked_add(key.len()).ok_or_else(|| {
                        "verifier counterexample scalar byte count overflowed".to_string()
                    })?;
                    pending.push((value, depth.saturating_add(1)));
                }
            }
            serde_json::Value::Null | serde_json::Value::Bool(_) | serde_json::Value::Number(_) => {
            }
        }
        if scalar_bytes > MAX_COUNTEREXAMPLE_JSON_SCALAR_BYTES {
            return Err("verifier counterexample exceeds the JSON scalar byte limit".to_string());
        }
    }
    Ok(())
}

struct DerivedVerificationRunState {
    publication: EvidencePublicationMetadata,
    skipped: Vec<SkippedObligation>,
    required_diagnostics: Vec<String>,
    summary: VerificationRunSummary,
    status: VerificationRunStatus,
}

fn derive_verification_run_state(result: &VerificationRunResult) -> DerivedVerificationRunState {
    let skipped =
        skipped_obligations(&result.requested_obligations, &result.evidence, &result.context);
    let publication_result = serialized_run_publication_metadata(result);
    let mut blocking_diagnostics = publication_result.conflicts;
    blocking_diagnostics
        .extend(run_engine_provenance_diagnostics(&result.engine, &result.evidence));
    blocking_diagnostics.extend(required_publication_metadata_diagnostics(
        &result.context.invocation,
        &publication_result.publication,
    ));
    let summary = VerificationRunSummary::from_parts(
        &result.requested_obligations,
        &result.evidence,
        &skipped,
        blocking_diagnostics.len(),
    );
    let status = VerificationRunStatus::from_summary(&summary, &result.context);
    let mut required_diagnostics = blocking_diagnostics;
    required_diagnostics.extend(release_blocking_skipped_proof_gap_diagnostics(&skipped));
    DerivedVerificationRunState {
        publication: publication_result.publication,
        skipped,
        required_diagnostics,
        summary,
        status,
    }
}

fn diagnostics_contain_required(actual: &[String], required: &[String]) -> bool {
    let mut counts = BTreeMap::<&str, usize>::new();
    for diagnostic in actual {
        *counts.entry(diagnostic.as_str()).or_default() += 1;
    }
    for diagnostic in required {
        let Some(count) = counts.get_mut(diagnostic.as_str()) else {
            return false;
        };
        if *count == 0 {
            return false;
        }
        *count -= 1;
    }
    true
}

/// The reserved diagnostic vocabulary derived mechanically from typed run
/// state. Engine-authored diagnostics outside this vocabulary are history and
/// survive reconciliation; these rows must instead match the current carrier
/// exactly.
fn is_derived_verification_run_diagnostic(diagnostic: &str) -> bool {
    if diagnostic.starts_with("release-blocking proof gap: obligation ")
        || diagnostic.starts_with("engine provenance mismatch for evidence ")
    {
        return true;
    }

    const PUBLICATION_FIELDS: &[&str] = &[
        "publication_plan_hash",
        "trust_engines_lock_hash",
        "dscan_attestation_hash",
        "dpub_release_id",
        "evidence_bundle_hash",
    ];
    let Some((field, detail)) = diagnostic.split_once(' ') else { return false };
    PUBLICATION_FIELDS.contains(&field)
        && (detail == "is required for this verifier invocation"
            || detail.starts_with("conflict for evidence "))
}

fn append_missing_diagnostics(actual: &mut Vec<String>, required: &[String]) {
    let mut counts = BTreeMap::<String, usize>::new();
    for diagnostic in actual.iter() {
        *counts.entry(diagnostic.clone()).or_default() += 1;
    }
    for diagnostic in required {
        let count = counts.entry(diagnostic.clone()).or_default();
        if *count == 0 {
            actual.push(diagnostic.clone());
        } else {
            *count -= 1;
        }
    }
}

impl<'de> Deserialize<'de> for VerificationRunResult {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        struct Helper {
            schema_version: String,
            run_id: String,
            bundle_id: String,
            subject: BundleSubject,
            engine: EngineManifest,
            #[serde(default)]
            context: Option<VerifierExecutionSnapshot>,
            status: VerificationRunStatus,
            summary: VerificationRunSummary,
            #[serde(default, deserialize_with = "deserialize_bounded_run_records")]
            requested_obligations: Vec<TrustObligation>,
            #[serde(default, deserialize_with = "deserialize_bounded_run_records")]
            evidence: Vec<ObligationEvidence>,
            #[serde(default, deserialize_with = "deserialize_bounded_run_records")]
            skipped: Vec<SkippedObligation>,
            publication: EvidencePublicationMetadata,
            #[serde(default, deserialize_with = "deserialize_bounded_run_diagnostics")]
            diagnostics: Vec<String>,
        }

        let helper = Helper::deserialize(deserializer)?;
        let context = helper.context.unwrap_or_else(|| {
            let mut snapshot = VerifierExecutionContext::compatibility().snapshot();
            snapshot.run_id = helper.run_id.clone();
            snapshot
        });
        let result = Self {
            schema_version: helper.schema_version,
            run_id: helper.run_id,
            bundle_id: helper.bundle_id,
            subject: helper.subject,
            engine: helper.engine,
            context,
            status: helper.status,
            summary: helper.summary,
            requested_obligations: helper.requested_obligations,
            evidence: helper.evidence,
            skipped: helper.skipped,
            publication: helper.publication,
            diagnostics: helper.diagnostics,
        };
        result.validate_derived_state().map_err(de::Error::custom)?;
        Ok(result)
    }
}

/// Coarse status for a verifier execution.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum VerificationRunStatus {
    Empty,
    Proved,
    Failed,
    Inconclusive,
    TimedOut,
    Canceled,
}

impl VerificationRunStatus {
    #[must_use]
    fn from_summary(summary: &VerificationRunSummary, context: &VerifierExecutionSnapshot) -> Self {
        if summary.cancelled > 0
            || (context.cancellation.requested && !resource_limit_cancellation(context))
        {
            return Self::Canceled;
        }
        if summary.requested_obligations == 0 {
            return Self::Empty;
        }
        if summary.timed_out > 0 {
            return Self::TimedOut;
        }
        if summary.failed > 0 {
            return Self::Failed;
        }
        // SOUNDNESS: this list must name every counter that can absorb an
        // obligation WITHOUT contributing to `proved`. It is enumerated
        // negatively, so a counter added later and forgotten here silently
        // becomes non-blocking — which is exactly how `bounded_proved` came to be
        // missing. Its own field doc says "bounded proofs ... do not make the run
        // proved", and the gate did not enforce that: a bounded row incremented
        // only `bounded_proved`, touching nothing here, so an obligation could be
        // absorbed with no proof and no blocker. Paired with a `proved` count that
        // did not deduplicate by obligation, two proved rows on one obligation
        // could pay for a bounded-only row on another and still satisfy the
        // equality below.
        //
        // If you add a counter to `VerificationRunSummary`, add it here unless it
        // is provably non-absorbing.
        if summary.unknown > 0
            || summary.unsupported > 0
            || summary.skipped > 0
            || summary.bounded_proved > 0
            || summary.insufficient_strength > 0
            || summary.missing_proof_artifacts > 0
            || summary.publication_conflicts > 0
        {
            return Self::Inconclusive;
        }
        // `proved` counts DISTINCT obligations (see `VerificationRunSummary::new`),
        // so this equality means "every requested obligation has a
        // publication-grade proof", not "we accumulated enough rows".
        if summary.proved == summary.requested_obligations {
            return Self::Proved;
        }
        Self::Inconclusive
    }
}

/// Counts used by dscan/dpub gates and CI summaries.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub struct VerificationRunSummary {
    pub requested_obligations: usize,
    pub evidence_count: usize,
    /// Publication-grade unbounded proofs.
    pub proved: usize,
    /// Bounded proofs are useful evidence but do not make the run proved.
    #[serde(default, skip_serializing_if = "is_zero")]
    pub bounded_proved: usize,
    /// Proved evidence whose assurance does not satisfy the requested
    /// publication-grade proof strength.
    #[serde(default, skip_serializing_if = "is_zero")]
    pub insufficient_strength: usize,
    /// Proved evidence with sufficient strength but missing replay/check or
    /// solver transcript artifacts.
    #[serde(default, skip_serializing_if = "is_zero")]
    pub missing_proof_artifacts: usize,
    pub failed: usize,
    pub unknown: usize,
    pub timed_out: usize,
    pub cancelled: usize,
    pub unsupported: usize,
    pub skipped: usize,
    #[serde(default, skip_serializing_if = "is_zero")]
    pub publication_conflicts: usize,
    /// Synthetic admission obligations that were excluded from every real
    /// count above (e.g. the trust-mc per-function "default function"
    /// admission). Trust: tracked purely for auditability — these never
    /// contribute to `proved`, `requested_obligations`, or any verdict,
    /// because their "proof" is vacuous by construction.
    #[serde(default, skip_serializing_if = "is_zero")]
    pub admitted: usize,
}

impl VerificationRunSummary {
    /// Summarize evidence and skipped obligations for a run.
    #[must_use]
    pub fn from_parts(
        requested_obligations: &[TrustObligation],
        evidence: &[ObligationEvidence],
        skipped: &[SkippedObligation],
        publication_conflicts: usize,
    ) -> Self {
        // Index obligations by id once; the prior per-evidence find() was O(n*m).
        let obligation_by_id: FxHashMap<&str, &TrustObligation> = {
            let mut map = FxHashMap::default();
            for obligation in requested_obligations {
                map.entry(obligation.obligation_id.as_str()).or_insert(obligation);
            }
            map
        };

        // Trust: The synthetic trust-mc per-function admission is not a real
        // obligation — its goal is `bool_literal(false)` and its "proof" is
        // vacuous by construction. Exclude it from every real count so it can
        // never inflate `proved` or flip a verdict to Proved; record how many
        // were excluded in `admitted` for auditability.
        let is_admission = |obligation_id: &str| -> bool {
            obligation_by_id
                .get(obligation_id)
                .is_some_and(|obligation| obligation.is_default_admission())
        };
        let admitted = requested_obligations.iter().filter(|o| o.is_default_admission()).count();

        let mut summary = Self {
            requested_obligations: requested_obligations.len().saturating_sub(admitted),
            evidence_count: evidence
                .iter()
                .filter(|item| !is_admission(&item.obligation_id))
                .count(),
            skipped: skipped.iter().filter(|item| !is_admission(&item.obligation_id)).count(),
            admitted,
            publication_conflicts,
            ..Self::default()
        };

        // SOUNDNESS: `proved` must count DISTINCT obligations, never evidence
        // rows. `from_summary` accepts a run when `proved == requested_obligations`,
        // so if one obligation contributed two publication-grade rows it could pay
        // for a second obligation that was never proved at all. Nothing emits two
        // rows per obligation today — a multi-engine fallback would be the first
        // mechanism that does — so this is a guard placed before the mechanism
        // that needs it, not a fix to an observed miscount.
        let mut counted_proved: std::collections::BTreeSet<&str> = std::collections::BTreeSet::new();
        for item in evidence {
            if is_admission(&item.obligation_id) {
                continue;
            }
            match item.status {
                EvidenceStatus::Proved => {
                    let required_strength = obligation_by_id
                        .get(item.obligation_id.as_str())
                        .and_then(|obligation| obligation.required_strength.as_ref());
                    if item.proof_strength.as_ref().is_some_and(ProofStrength::is_bounded) {
                        summary.bounded_proved += 1;
                    } else if !item.satisfies_strength_requirement(required_strength) {
                        summary.insufficient_strength += 1;
                    } else if !item.satisfies_proof_artifact_policy() {
                        summary.missing_proof_artifacts += 1;
                    } else if counted_proved.insert(item.obligation_id.as_str()) {
                        summary.proved += 1;
                    }
                }
                EvidenceStatus::Failed => summary.failed += 1,
                EvidenceStatus::Unknown => summary.unknown += 1,
                EvidenceStatus::Timeout => summary.timed_out += 1,
                EvidenceStatus::Canceled => summary.cancelled += 1,
                EvidenceStatus::Unsupported => summary.unsupported += 1,
            }
        }

        for item in skipped {
            if is_admission(&item.obligation_id) {
                continue;
            }
            match &item.reason {
                SkipReason::Canceled { .. } => summary.cancelled += 1,
                SkipReason::Unsupported { .. } => summary.unsupported += 1,
                SkipReason::ResourceLimit { .. } | SkipReason::NotAttempted { .. } => {}
            }
        }

        summary
    }
}

/// Obligation that did not produce evidence during a run.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SkippedObligation {
    pub obligation_id: String,
    pub kind: ObligationKind,
    pub reason: SkipReason,
}

/// Reason an obligation did not produce evidence.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SkipReason {
    Canceled {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        reason: Option<CancellationReason>,
    },
    ResourceLimit {
        limit: ResourceLimitKind,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        detail: Option<String>,
    },
    Unsupported {
        support: SupportLevel,
    },
    NotAttempted {
        reason: String,
    },
}

/// A verifier request whose obligations have been checked against the exact
/// canonical inventory in its contract bundle.
///
/// The fields and constructor are intentionally private.  Verification engines
/// can inspect a value passed to their implementation hook, but callers cannot
/// manufacture one and thereby bypass [`TrustContractBundle::validate_requested_obligations`].
///
/// ```compile_fail
/// use trust_verifier_api::{
///     TrustContractBundle, TrustObligation, ValidatedVerificationRequest,
/// };
///
/// fn forge<'a>(
///     bundle: &'a TrustContractBundle,
///     obligations: &'a [TrustObligation],
/// ) -> ValidatedVerificationRequest<'a> {
///     ValidatedVerificationRequest { bundle, obligations }
/// }
/// ```
#[derive(Debug, Clone, Copy)]
pub struct ValidatedVerificationRequest<'a> {
    bundle: &'a TrustContractBundle,
    obligations: &'a [TrustObligation],
}

impl<'a> ValidatedVerificationRequest<'a> {
    fn new(bundle: &'a TrustContractBundle, obligations: &'a [TrustObligation]) -> Self {
        Self { bundle, obligations }
    }

    /// Return the canonical contract bundle for this request.
    #[must_use]
    pub fn bundle(self) -> &'a TrustContractBundle {
        self.bundle
    }

    /// Return the validated, duplicate-free obligation subset.
    #[must_use]
    pub fn obligations(self) -> &'a [TrustObligation] {
        self.obligations
    }

    /// Split the request into its canonical bundle and validated obligations.
    #[must_use]
    pub fn into_parts(self) -> (&'a TrustContractBundle, &'a [TrustObligation]) {
        (self.bundle, self.obligations)
    }
}

/// Public verifier engine trait.
pub trait VerificationEngine {
    /// Engine manifest used in all evidence produced by this engine.
    fn manifest(&self) -> &EngineManifest;

    /// Report whether this engine can attempt the obligation.
    fn supports(&self, obligation: &TrustObligation) -> SupportLevel;

    /// Verify a batch of obligations from one contract bundle.
    ///
    /// This public wrapper always enforces that `obligations` is an exact
    /// subset of `bundle.obligations`. Invalid or ID-preserving substituted
    /// requests return no evidence and never reach engine code.
    fn verify(
        &self,
        bundle: &TrustContractBundle,
        obligations: &[TrustObligation],
    ) -> Vec<ObligationEvidence> {
        if bundle.validate_requested_obligations(obligations).is_err() {
            return Vec::new();
        }
        self.verify_validated(ValidatedVerificationRequest::new(bundle, obligations))
    }

    /// Engine implementation for a batch already proven to be an exact subset
    /// of its canonical bundle inventory. Implementors must not call this as a
    /// replacement for the public [`VerificationEngine::verify`] boundary.
    #[doc(hidden)]
    fn verify_validated(
        &self,
        request: ValidatedVerificationRequest<'_>,
    ) -> Vec<ObligationEvidence>;

    /// Verify with execution context, resource limits, cancellation, and a
    /// serializable result envelope.
    ///
    /// The wrapper enforces the same canonical bundle/request binding as
    /// [`VerificationEngine::verify`] before calling the engine hook.
    fn verify_with_context(
        &self,
        bundle: &TrustContractBundle,
        obligations: &[TrustObligation],
        context: &VerifierExecutionContext,
    ) -> VerificationRunResult {
        if let Err(error) = bundle.validate_requested_obligations(obligations) {
            let mut result = VerificationRunResult::from_evidence(
                context.snapshot(),
                bundle,
                self.manifest().clone(),
                obligations,
                Vec::new(),
            );
            result
                .diagnostics
                .push(format!("verifier rejected non-canonical obligation request: {error}"));
            return result;
        }
        self.verify_with_context_validated(
            ValidatedVerificationRequest::new(bundle, obligations),
            context,
        )
    }

    /// Context-aware engine hook for an already validated canonical request.
    /// Native engines override this hook to enforce additional runtime limits
    /// or poll cancellation during execution.
    #[doc(hidden)]
    fn verify_with_context_validated(
        &self,
        request: ValidatedVerificationRequest<'_>,
        context: &VerifierExecutionContext,
    ) -> VerificationRunResult {
        let (bundle, obligations) = request.into_parts();
        let evidence = if context.is_cancelled() {
            Vec::new()
        } else {
            self.verify_validated(ValidatedVerificationRequest::new(bundle, obligations))
        };
        VerificationRunResult::from_evidence(
            context.snapshot(),
            bundle,
            self.manifest().clone(),
            obligations,
            evidence,
        )
    }
}

fn skipped_obligations(
    requested_obligations: &[TrustObligation],
    evidence: &[ObligationEvidence],
    context: &VerifierExecutionSnapshot,
) -> Vec<SkippedObligation> {
    // Index evidence once (O(n+m)); the prior per-obligation rescan was O(n*m) and hung self-verification of large crates for hours.
    let evidenced: FxHashSet<&str> =
        evidence.iter().map(|item| item.obligation_id.as_str()).collect();
    requested_obligations
        .iter()
        .filter(|obligation| !evidenced.contains(obligation.obligation_id.as_str()))
        .map(|obligation| SkippedObligation {
            obligation_id: obligation.obligation_id.clone(),
            kind: obligation.kind.clone(),
            reason: skip_reason_for_missing_evidence(context),
        })
        .collect()
}

fn skip_reason_for_missing_evidence(context: &VerifierExecutionSnapshot) -> SkipReason {
    if let Some(CancellationReason::ResourceLimitExceeded { limit }) =
        context.cancellation.reason.as_ref()
    {
        return SkipReason::ResourceLimit {
            limit: *limit,
            detail: Some(resource_limit_skip_detail(*limit)),
        };
    }
    if context.cancellation.requested {
        return SkipReason::Canceled { reason: context.cancellation.reason.clone() };
    }
    SkipReason::NotAttempted {
        reason: "engine returned no evidence for requested obligation".to_string(),
    }
}

fn resource_limit_cancellation(context: &VerifierExecutionSnapshot) -> bool {
    matches!(
        context.cancellation.reason.as_ref(),
        Some(CancellationReason::ResourceLimitExceeded { .. })
    )
}

fn resource_limit_skip_detail(limit: ResourceLimitKind) -> String {
    match limit {
        ResourceLimitKind::Memory => {
            "memory guard skipped solver dispatch before proof evidence was produced".to_string()
        }
        _ => {
            format!(
                "resource limit {limit:?} skipped solver dispatch before proof evidence was produced"
            )
        }
    }
}

fn release_blocking_skipped_proof_gap_diagnostics(skipped: &[SkippedObligation]) -> Vec<String> {
    skipped
        .iter()
        .filter_map(|item| {
            let SkipReason::ResourceLimit { limit, detail } = &item.reason else {
                return None;
            };
            let detail = detail.as_deref().unwrap_or("resource limit reached");
            Some(format!(
                "release-blocking proof gap: obligation {} ({:?}) skipped by {:?}; {}",
                item.obligation_id, item.kind, limit, detail
            ))
        })
        .collect()
}

fn run_engine_provenance_diagnostics(
    engine: &EngineManifest,
    evidence: &[ObligationEvidence],
) -> Vec<String> {
    evidence
        .iter()
        .filter(|item| item.engine != *engine)
        .map(|item| {
            format!(
                "engine provenance mismatch for evidence {}: run engine {}@{}, evidence engine {}@{}",
                item.evidence_id,
                engine.name,
                engine.version,
                item.engine.name,
                item.engine.version
            )
        })
        .collect()
}

fn required_publication_metadata_diagnostics(
    invocation: &VerifierInvocation,
    publication: &EvidencePublicationMetadata,
) -> Vec<String> {
    let mut diagnostics = Vec::new();
    match invocation {
        VerifierInvocation::DscanPreflight | VerifierInvocation::DpubReleaseGate => {
            require_publication_field(
                "publication_plan_hash",
                &publication.publication_plan_hash,
                &mut diagnostics,
            );
            require_publication_field(
                "trust_engines_lock_hash",
                &publication.trust_engines_lock_hash,
                &mut diagnostics,
            );
        }
        _ => {}
    }
    if matches!(invocation, VerifierInvocation::DpubReleaseGate) {
        require_publication_field(
            "dscan_attestation_hash",
            &publication.dscan_attestation_hash,
            &mut diagnostics,
        );
        require_publication_field(
            "dpub_release_id",
            &publication.dpub_release_id,
            &mut diagnostics,
        );
    }
    diagnostics
}

fn require_publication_field(field: &str, value: &Option<String>, diagnostics: &mut Vec<String>) {
    if value.as_ref().is_none_or(|value| value.trim().is_empty()) {
        diagnostics.push(format!("{field} is required for this verifier invocation"));
    }
}

fn is_zero(value: &usize) -> bool {
    *value == 0
}

fn evidence_publication_is_empty(publication: &EvidencePublicationMetadata) -> bool {
    publication == &EvidencePublicationMetadata::default()
}

struct PublicationAggregationResult {
    publication: EvidencePublicationMetadata,
    conflicts: Vec<String>,
}

fn run_publication_metadata(
    bundle: &TrustContractBundle,
    evidence: &[ObligationEvidence],
) -> PublicationAggregationResult {
    aggregate_publication_metadata(
        EvidencePublicationMetadata {
            publication_plan_hash: bundle.publication.dpub_plan_hash.clone(),
            trust_engines_lock_hash: bundle.publication.trust_engines_lock_hash.clone(),
            ..EvidencePublicationMetadata::default()
        },
        evidence,
    )
}

fn serialized_run_publication_metadata(
    result: &VerificationRunResult,
) -> PublicationAggregationResult {
    // The bundle-level plan/lock inputs are not duplicated in the run-result
    // wire schema, so they are the only permitted aggregate base values. Every
    // other publication field must be re-derived solely from typed evidence.
    aggregate_publication_metadata(
        EvidencePublicationMetadata {
            publication_plan_hash: result.publication.publication_plan_hash.clone(),
            trust_engines_lock_hash: result.publication.trust_engines_lock_hash.clone(),
            ..EvidencePublicationMetadata::default()
        },
        &result.evidence,
    )
}

fn aggregate_publication_metadata(
    mut publication: EvidencePublicationMetadata,
    evidence: &[ObligationEvidence],
) -> PublicationAggregationResult {
    let mut conflicts = Vec::new();

    for item in evidence {
        merge_publication_field(
            "dscan_attestation_hash",
            &mut publication.dscan_attestation_hash,
            &item.publication.dscan_attestation_hash,
            &item.evidence_id,
            &mut conflicts,
        );
        merge_publication_field(
            "dpub_release_id",
            &mut publication.dpub_release_id,
            &item.publication.dpub_release_id,
            &item.evidence_id,
            &mut conflicts,
        );
        merge_publication_field(
            "evidence_bundle_hash",
            &mut publication.evidence_bundle_hash,
            &item.publication.evidence_bundle_hash,
            &item.evidence_id,
            &mut conflicts,
        );
        merge_publication_field(
            "publication_plan_hash",
            &mut publication.publication_plan_hash,
            &item.publication.publication_plan_hash,
            &item.evidence_id,
            &mut conflicts,
        );
        merge_publication_field(
            "trust_engines_lock_hash",
            &mut publication.trust_engines_lock_hash,
            &item.publication.trust_engines_lock_hash,
            &item.evidence_id,
            &mut conflicts,
        );
    }

    PublicationAggregationResult { publication, conflicts }
}

fn merge_publication_field(
    field: &str,
    current: &mut Option<String>,
    next: &Option<String>,
    evidence_id: &str,
    conflicts: &mut Vec<String>,
) {
    let Some(next_value) = next.as_ref() else {
        return;
    };
    match current.as_ref() {
        None => *current = Some(next_value.clone()),
        Some(current_value) if current_value == next_value => {}
        Some(current_value) => conflicts.push(format!(
            "{field} conflict for evidence {evidence_id}: aggregate {current_value}, evidence {next_value}"
        )),
    }
}

/// Source location for contracts, obligations, and diagnostics.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub struct SourceLocation {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub file: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub line: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub column: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub end_line: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub end_column: Option<u32>,
}

/// Source and release metadata carried through dscan and dpub.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct PublicationMetadata {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub candidate_id: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source_repo: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source_commit: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub crate_name: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub crate_version: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub trust_engines_lock_hash: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub dpub_plan_hash: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub conformance_report_hash: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub release_gate_report_hash: Option<String>,
}

/// Evidence publication metadata emitted after an engine runs.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct EvidencePublicationMetadata {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub dscan_attestation_hash: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub dpub_release_id: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub publication_plan_hash: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub trust_engines_lock_hash: Option<String>,
    /// Identity of the complete evidence publication bundle for this run.
    /// Every non-empty row in one [`VerificationRunResult`] must agree on this
    /// value; per-obligation proof digests belong in [`EvidenceArtifact`]s.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub evidence_bundle_hash: Option<String>,
}

/// Artifact referenced by obligation evidence.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct EvidenceArtifact {
    pub kind: EvidenceArtifactKind,
    pub uri: String,
    pub hash: ArtifactHash,
    /// Exact bytes for this artifact plus producer-authored proof-set binding.
    /// Metadata and the logical artifact URI are never substitutes for these
    /// bytes. A replay/check artifact names the digest(s) it actually checked.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub materialization: Option<EvidenceArtifactMaterialization>,
}

fn deserialize_obligation_evidence_artifacts<'de, D>(
    deserializer: D,
) -> Result<Vec<EvidenceArtifact>, D::Error>
where
    D: Deserializer<'de>,
{
    deserialize_bounded_evidence_artifacts::<D, MAX_EVIDENCE_ARTIFACTS_PER_OBLIGATION>(deserializer)
}

fn deserialize_run_manifest_evidence_artifacts<'de, D>(
    deserializer: D,
) -> Result<Vec<EvidenceArtifact>, D::Error>
where
    D: Deserializer<'de>,
{
    deserialize_bounded_evidence_artifacts::<D, MAX_EVIDENCE_ARTIFACTS_PER_RUN_MANIFEST>(
        deserializer,
    )
}

fn deserialize_bounded_evidence_artifacts<'de, D, const LIMIT: usize>(
    deserializer: D,
) -> Result<Vec<EvidenceArtifact>, D::Error>
where
    D: Deserializer<'de>,
{
    struct BoundedArtifactsVisitor<const LIMIT: usize>;

    impl<'de, const LIMIT: usize> Visitor<'de> for BoundedArtifactsVisitor<LIMIT> {
        type Value = Vec<EvidenceArtifact>;

        fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(formatter, "at most {LIMIT} evidence artifacts")
        }

        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            if sequence.size_hint().is_some_and(|hint| hint > LIMIT) {
                return Err(de::Error::custom("too many evidence artifacts"));
            }
            let mut artifacts = Vec::with_capacity(sequence.size_hint().unwrap_or(0).min(LIMIT));
            while artifacts.len() < LIMIT {
                let Some(artifact) = sequence.next_element::<EvidenceArtifact>()? else {
                    return Ok(artifacts);
                };
                artifacts.push(artifact);
            }
            if sequence.next_element::<IgnoredAny>()?.is_some() {
                return Err(de::Error::custom("too many evidence artifacts"));
            }
            Ok(artifacts)
        }
    }

    deserializer.deserialize_seq(BoundedArtifactsVisitor::<LIMIT>)
}

/// Exact, producer-authored artifact materialization carried to downstream
/// proof consumers.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EvidenceArtifactMaterialization {
    /// Exact artifact bytes. Empty and oversized payloads are rejected by the
    /// compiler transport boundary and downstream consumers.
    bytes: Arc<[u8]>,
    /// Stable identity of the proof set that produced this artifact.
    proof_binding_id: String,
    /// Digests of other materialized artifacts this artifact explicitly checks
    /// or incorporates. This prevents independently selected A/B artifact
    /// mixtures from being treated as a replayed proof.
    referenced_artifacts: Vec<EvidenceArtifactReference>,
}

/// Typed edge from one materialized proof artifact to another.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct EvidenceArtifactReference {
    pub kind: EvidenceArtifactKind,
    pub hash: ArtifactHash,
}

const MAX_EVIDENCE_ARTIFACT_REFERENCES: usize = 32;

impl EvidenceArtifactMaterialization {
    /// Construct a bounded, non-empty exact payload with canonical,
    /// duplicate-free SHA-256 references.
    #[must_use]
    pub fn new(
        bytes: Vec<u8>,
        proof_binding_id: impl Into<String>,
        referenced_artifacts: Vec<EvidenceArtifactReference>,
    ) -> Option<Self> {
        let proof_binding_id = proof_binding_id.into();
        if bytes.is_empty()
            || bytes.len() > MAX_EVIDENCE_ARTIFACT_MATERIALIZATION_BYTES
            || !canonical_proof_binding_id(&proof_binding_id)
            || referenced_artifacts.len() > MAX_EVIDENCE_ARTIFACT_REFERENCES
            || referenced_artifacts
                .iter()
                .any(|reference| !canonical_sha256_artifact_hash(&reference.hash))
            || referenced_artifacts.windows(2).any(|pair| pair[0] >= pair[1])
        {
            return None;
        }
        Some(Self { bytes: bytes.into(), proof_binding_id, referenced_artifacts })
    }

    /// Wrap exact producer bytes in a canonical, hash-addressed owner/role
    /// envelope. The returned hash is over the complete envelope, so changing
    /// the obligation, binding, role, references, or payload changes the public
    /// artifact identity.
    #[must_use]
    pub fn new_bound(
        kind: EvidenceArtifactKind,
        payload: &[u8],
        proof_binding_id: impl Into<String>,
        obligation_id: &str,
        referenced_artifacts: Vec<EvidenceArtifactReference>,
    ) -> Option<(Self, ArtifactHash)> {
        let proof_binding_id = proof_binding_id.into();
        if payload.is_empty()
            || payload.len() > MAX_EVIDENCE_ARTIFACT_MATERIALIZATION_BYTES
            || !canonical_proof_binding_id(&proof_binding_id)
            || !canonical_artifact_owner_id(obligation_id)
            || referenced_artifacts.len() > MAX_EVIDENCE_ARTIFACT_REFERENCES
            || referenced_artifacts.iter().any(|reference| {
                reference.kind.canonical_wire_label().is_none()
                    || !canonical_sha256_artifact_hash(&reference.hash)
            })
            || referenced_artifacts.windows(2).any(|pair| pair[0] >= pair[1])
        {
            return None;
        }
        let mut bytes = Vec::with_capacity(payload.len().saturating_add(1024));
        bytes.extend_from_slice(EVIDENCE_ARTIFACT_BINDING_ENVELOPE_MAGIC);
        push_binding_field(&mut bytes, kind.canonical_wire_label()?.as_bytes())?;
        push_binding_field(&mut bytes, obligation_id.as_bytes())?;
        push_binding_field(&mut bytes, proof_binding_id.as_bytes())?;
        bytes.extend_from_slice(&u32::try_from(referenced_artifacts.len()).ok()?.to_be_bytes());
        for reference in &referenced_artifacts {
            push_binding_field(&mut bytes, reference.kind.canonical_wire_label()?.as_bytes())?;
            push_binding_field(&mut bytes, reference.hash.algorithm.as_bytes())?;
            push_binding_field(&mut bytes, reference.hash.value.as_bytes())?;
        }
        bytes.extend_from_slice(&u64::try_from(payload.len()).ok()?.to_be_bytes());
        bytes.extend_from_slice(payload);
        if bytes.len() > MAX_EVIDENCE_ARTIFACT_MATERIALIZATION_BYTES {
            return None;
        }
        let materialization = Self::new(bytes, proof_binding_id, referenced_artifacts)?;
        let hash = ArtifactHash {
            algorithm: "sha256".to_string(),
            value: stable_sha256_hex(materialization.bytes()),
        };
        Some((materialization, hash))
    }

    /// Exact bytes retained by the producer.
    #[must_use]
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Producer-authored proof-set identity.
    #[must_use]
    pub fn proof_binding_id(&self) -> &str {
        &self.proof_binding_id
    }

    /// Canonical SHA-256 digests explicitly incorporated or checked by this
    /// artifact.
    #[must_use]
    pub fn referenced_artifacts(&self) -> &[EvidenceArtifactReference] {
        &self.referenced_artifacts
    }

    /// Whether these exact bytes match the artifact's canonical SHA-256 hash.
    #[must_use]
    pub fn matches_hash(&self, hash: &ArtifactHash) -> bool {
        if !canonical_sha256_artifact_hash(hash) {
            return false;
        }
        stable_sha256_hex(&self.bytes) == hash.value
    }

    /// Validate and return the exact producer payload from a canonical binding
    /// envelope owned by `obligation_id`.
    pub fn bound_payload_bytes<'a>(
        &'a self,
        kind: EvidenceArtifactKind,
        obligation_id: &str,
    ) -> Option<&'a [u8]> {
        parse_bound_payload(
            &self.bytes,
            kind,
            obligation_id,
            &self.proof_binding_id,
            &self.referenced_artifacts,
        )
    }

    /// Rebind a reusable structural artifact to the concrete proof identity at
    /// the producer's obligation-routing boundary.
    #[must_use]
    pub fn with_proof_binding_id(mut self, proof_binding_id: impl Into<String>) -> Option<Self> {
        let proof_binding_id = proof_binding_id.into();
        if !canonical_proof_binding_id(&proof_binding_id) {
            return None;
        }
        if self.bytes.starts_with(EVIDENCE_ARTIFACT_BINDING_ENVELOPE_MAGIC) {
            return (self.proof_binding_id == proof_binding_id).then_some(self);
        }
        self.proof_binding_id = proof_binding_id;
        Some(self)
    }
}

impl Serialize for EvidenceArtifactMaterialization {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        #[derive(Serialize)]
        struct Wire<'a> {
            bytes: &'a [u8],
            proof_binding_id: &'a str,
            referenced_artifacts: &'a [EvidenceArtifactReference],
        }
        Wire {
            bytes: &self.bytes,
            proof_binding_id: &self.proof_binding_id,
            referenced_artifacts: &self.referenced_artifacts,
        }
        .serialize(serializer)
    }
}

fn canonical_sha256_artifact_hash(digest: &ArtifactHash) -> bool {
    digest.algorithm == "sha256"
        && digest.value.len() == 64
        && digest.value.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn canonical_proof_binding_id(value: &str) -> bool {
    const MAX_BINDING_ID_BYTES: usize = 256;
    !value.is_empty()
        && value.len() <= MAX_BINDING_ID_BYTES
        && value.as_bytes().first().is_some_and(u8::is_ascii_alphanumeric)
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'_' | b':' | b'-'))
}

fn canonical_artifact_owner_id(value: &str) -> bool {
    // Rust def-paths for trait-impl methods embed an interior ASCII space
    // (e.g. `<Button as sealed::Widget>::rank`), so a legitimate,
    // compiler-minted `contract_id`/`obligation_id` can carry one. Permit an
    // interior space alongside the graphic-ASCII set, but keep rejecting
    // leading/trailing whitespace, control bytes, non-ASCII, and the
    // URL-significant `?`/`#`. This only enlarges the accepted set and never
    // trims or normalizes the value, so distinct ids stay distinct (no
    // collision) and every downstream evidence/hash binding (all length
    // framed) is unaffected.
    !value.is_empty()
        && value.len() <= 1024
        && !value.starts_with(' ')
        && !value.ends_with(' ')
        && value
            .bytes()
            .all(|byte| (byte.is_ascii_graphic() || byte == b' ') && !matches!(byte, b'?' | b'#'))
}

fn push_binding_field(bytes: &mut Vec<u8>, value: &[u8]) -> Option<()> {
    bytes.extend_from_slice(&u32::try_from(value.len()).ok()?.to_be_bytes());
    bytes.extend_from_slice(value);
    Some(())
}

fn parse_bound_payload<'a>(
    bytes: &'a [u8],
    kind: EvidenceArtifactKind,
    obligation_id: &str,
    proof_binding_id: &str,
    references: &[EvidenceArtifactReference],
) -> Option<&'a [u8]> {
    let mut cursor = EVIDENCE_ARTIFACT_BINDING_ENVELOPE_MAGIC.len();
    bytes.starts_with(EVIDENCE_ARTIFACT_BINDING_ENVELOPE_MAGIC).then_some(())?;
    (read_binding_field(bytes, &mut cursor)? == kind.canonical_wire_label()?.as_bytes())
        .then_some(())?;
    (read_binding_field(bytes, &mut cursor)? == obligation_id.as_bytes()).then_some(())?;
    (read_binding_field(bytes, &mut cursor)? == proof_binding_id.as_bytes()).then_some(())?;
    let reference_count = read_binding_u32(bytes, &mut cursor)? as usize;
    (reference_count == references.len()).then_some(())?;
    for reference in references {
        (read_binding_field(bytes, &mut cursor)?
            == reference.kind.canonical_wire_label()?.as_bytes())
        .then_some(())?;
        (read_binding_field(bytes, &mut cursor)? == reference.hash.algorithm.as_bytes())
            .then_some(())?;
        (read_binding_field(bytes, &mut cursor)? == reference.hash.value.as_bytes())
            .then_some(())?;
    }
    let payload_len = usize::try_from(read_binding_u64(bytes, &mut cursor)?).ok()?;
    if payload_len == 0 || payload_len > MAX_EVIDENCE_ARTIFACT_MATERIALIZATION_BYTES {
        return None;
    }
    let end = cursor.checked_add(payload_len)?;
    (end == bytes.len()).then_some(&bytes[cursor..end])
}

fn read_binding_field<'a>(bytes: &'a [u8], cursor: &mut usize) -> Option<&'a [u8]> {
    let len = read_binding_u32(bytes, cursor)? as usize;
    let end = (*cursor).checked_add(len)?;
    let value = bytes.get(*cursor..end)?;
    *cursor = end;
    Some(value)
}

fn read_binding_u32(bytes: &[u8], cursor: &mut usize) -> Option<u32> {
    let end = (*cursor).checked_add(4)?;
    let value = u32::from_be_bytes(bytes.get(*cursor..end)?.try_into().ok()?);
    *cursor = end;
    Some(value)
}

fn read_binding_u64(bytes: &[u8], cursor: &mut usize) -> Option<u64> {
    let end = (*cursor).checked_add(8)?;
    let value = u64::from_be_bytes(bytes.get(*cursor..end)?.try_into().ok()?);
    *cursor = end;
    Some(value)
}

#[derive(Deserialize)]
struct EvidenceArtifactMaterializationWire {
    #[serde(deserialize_with = "deserialize_bounded_artifact_bytes")]
    bytes: Vec<u8>,
    proof_binding_id: String,
    #[serde(default, deserialize_with = "deserialize_bounded_artifact_references")]
    referenced_artifacts: Vec<EvidenceArtifactReference>,
}

impl<'de> Deserialize<'de> for EvidenceArtifactMaterialization {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = EvidenceArtifactMaterializationWire::deserialize(deserializer)?;
        Self::new(wire.bytes, wire.proof_binding_id, wire.referenced_artifacts).ok_or_else(|| {
            de::Error::custom(
                "artifact materialization must be non-empty, bounded, proof-bound, and carry only canonical duplicate-free SHA-256 references",
            )
        })
    }
}

fn deserialize_bounded_artifact_bytes<'de, D>(deserializer: D) -> Result<Vec<u8>, D::Error>
where
    D: Deserializer<'de>,
{
    struct BoundedBytesVisitor;

    impl<'de> Visitor<'de> for BoundedBytesVisitor {
        type Value = Vec<u8>;

        fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(
                formatter,
                "between 1 and {MAX_EVIDENCE_ARTIFACT_MATERIALIZATION_BYTES} artifact bytes"
            )
        }

        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let initial =
                sequence.size_hint().unwrap_or(0).min(MAX_EVIDENCE_ARTIFACT_MATERIALIZATION_BYTES);
            let mut bytes = Vec::with_capacity(initial);
            while let Some(byte) = sequence.next_element::<u8>()? {
                if bytes.len() == MAX_EVIDENCE_ARTIFACT_MATERIALIZATION_BYTES {
                    return Err(de::Error::custom("artifact materialization exceeds byte limit"));
                }
                bytes.push(byte);
            }
            if bytes.is_empty() {
                return Err(de::Error::custom("artifact materialization is empty"));
            }
            Ok(bytes)
        }
    }

    deserializer.deserialize_seq(BoundedBytesVisitor)
}

fn deserialize_bounded_artifact_references<'de, D>(
    deserializer: D,
) -> Result<Vec<EvidenceArtifactReference>, D::Error>
where
    D: Deserializer<'de>,
{
    struct BoundedReferencesVisitor;

    impl<'de> Visitor<'de> for BoundedReferencesVisitor {
        type Value = Vec<EvidenceArtifactReference>;

        fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(formatter, "at most {MAX_EVIDENCE_ARTIFACT_REFERENCES} artifact digests")
        }

        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let mut references = Vec::with_capacity(
                sequence.size_hint().unwrap_or(0).min(MAX_EVIDENCE_ARTIFACT_REFERENCES),
            );
            while let Some(reference) = sequence.next_element::<EvidenceArtifactReference>()? {
                if references.len() == MAX_EVIDENCE_ARTIFACT_REFERENCES {
                    return Err(de::Error::custom("too many artifact digest references"));
                }
                references.push(reference);
            }
            Ok(references)
        }
    }

    deserializer.deserialize_seq(BoundedReferencesVisitor)
}

/// Artifact category.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum EvidenceArtifactKind {
    NormalizedObligation,
    EngineInput,
    SolverQuery,
    SolverProof,
    SolverTranscript,
    ProofCertificate,
    ProofReplayTrace,
    ProofCheckReport,
    ReplayLog,
    Model,
    Counterexample,
    Log,
    Report,
    DscanAttestation,
    DpubManifest,
    BuildManifest,
    SummaryEvidence,
}

impl EvidenceArtifactKind {
    /// Explicit schema-stable transport label. New variants fail closed until
    /// assigned a reviewed label here.
    #[must_use]
    pub const fn canonical_wire_label(self) -> Option<&'static str> {
        Some(match self {
            Self::NormalizedObligation => "NormalizedObligation",
            Self::EngineInput => "EngineInput",
            Self::SolverQuery => "SolverQuery",
            Self::SolverProof => "SolverProof",
            Self::SolverTranscript => "SolverTranscript",
            Self::ProofCertificate => "ProofCertificate",
            Self::ProofReplayTrace => "ProofReplayTrace",
            Self::ProofCheckReport => "ProofCheckReport",
            Self::ReplayLog => "ReplayLog",
            Self::Model => "Model",
            Self::Counterexample => "Counterexample",
            Self::Log => "Log",
            Self::Report => "Report",
            Self::DscanAttestation => "DscanAttestation",
            Self::DpubManifest => "DpubManifest",
            Self::BuildManifest => "BuildManifest",
            Self::SummaryEvidence => "SummaryEvidence",
        })
    }

    /// Artifact categories that make proof replay/check metadata explicit.
    #[must_use]
    pub fn is_replay_or_check(self) -> bool {
        matches!(
            self,
            Self::ProofCertificate
                | Self::ProofReplayTrace
                | Self::ProofCheckReport
                | Self::ReplayLog
        )
    }

    /// Artifact categories that make solver-backed proof transcripts explicit.
    #[must_use]
    pub fn is_solver_transcript(self) -> bool {
        matches!(self, Self::SolverTranscript)
    }
}

/// Named artifact digest.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ArtifactHash {
    pub algorithm: String,
    pub value: String,
}

impl ArtifactHash {
    /// Returns true when both digest fields are populated.
    #[must_use]
    pub fn is_hash_addressed(&self) -> bool {
        !self.algorithm.trim().is_empty() && !self.value.trim().is_empty()
    }
}

/// Hash-addressed cross-crate summary fact supplied by Trust or another
/// verifier producer.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SummaryFact {
    pub schema_version: String,
    pub id: String,
    pub producer: String,
    pub source_crate: String,
    pub source_item: String,
    pub kind: SummaryFactKind,
    pub digest: ArtifactHash,
}

impl SummaryFact {
    /// Create a summary fact with explicit source provenance.
    #[must_use]
    pub fn new(
        id: impl Into<String>,
        producer: impl Into<String>,
        source_crate: impl Into<String>,
        source_item: impl Into<String>,
        kind: SummaryFactKind,
        digest: ArtifactHash,
    ) -> Self {
        Self {
            schema_version: SUMMARY_FACT_SCHEMA_VERSION.to_string(),
            id: id.into(),
            producer: producer.into(),
            source_crate: source_crate.into(),
            source_item: source_item.into(),
            kind,
            digest,
        }
    }

    /// Returns true when the fact has the provenance and digest fields trust_wp
    /// requires before committing it into replay evidence.
    #[must_use]
    pub fn is_replay_addressable(&self) -> bool {
        validate_summary_fact(self).is_ok()
    }

    /// Encode this fact as a metadata entry for callers that have not yet
    /// promoted summary facts to the first-class field.
    pub fn to_metadata_entry(&self) -> Result<MetadataEntry, serde_json::Error> {
        Ok(MetadataEntry {
            key: SUMMARY_FACT_METADATA_KEY.to_string(),
            value: serde_json::to_string(self)?,
        })
    }

    /// Decode a summary fact from a metadata entry.
    ///
    /// Returns `Ok(None)` for unrelated metadata keys.
    pub fn from_metadata_entry(
        metadata: &MetadataEntry,
    ) -> Result<Option<Self>, serde_json::Error> {
        if metadata.key == SUMMARY_FACT_METADATA_KEY {
            serde_json::from_str(&metadata.value).map(Some)
        } else {
            Ok(None)
        }
    }
}

/// Native summary fact kinds aligned with trust_wp verify-bundle summary evidence.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
#[non_exhaustive]
pub enum SummaryFactKind {
    /// Thin pointer equality backed by alias/provenance analysis.
    PointerProvenanceEq { left: String, right: String },
    /// Fat pointer equality backed by data-address and metadata equality.
    FatPointerMetadataEq { left: String, right: String },
    /// Future fact kind carried for correlation but ignored by v1 replay.
    Other { schema: String },
}

impl SummaryFactKind {
    /// Stable machine-readable kind label used in trust_wp evidence material.
    #[must_use]
    pub fn as_str(&self) -> &str {
        match self {
            Self::PointerProvenanceEq { .. } => "pointer-provenance-eq",
            Self::FatPointerMetadataEq { .. } => "fat-pointer-metadata-eq",
            Self::Other { schema } => schema.as_str(),
        }
    }

    /// Endpoints for equality summary facts.
    #[must_use]
    pub fn endpoints(&self) -> Option<(&str, &str)> {
        match self {
            Self::PointerProvenanceEq { left, right }
            | Self::FatPointerMetadataEq { left, right } => Some((left, right)),
            Self::Other { .. } => None,
        }
    }
}

fn validate_summary_fact(fact: &SummaryFact) -> Result<(), String> {
    if fact.schema_version != SUMMARY_FACT_SCHEMA_VERSION {
        return Err("verifier summary fact uses an unsupported schema".to_string());
    }
    validate_envelope_identifier("summary fact id", &fact.id)?;
    validate_canonical_text("summary fact producer", &fact.producer, MAX_SUMMARY_FACT_FIELD_BYTES)?;
    validate_canonical_text(
        "summary fact source crate",
        &fact.source_crate,
        MAX_SUMMARY_FACT_FIELD_BYTES,
    )?;
    validate_canonical_text(
        "summary fact source item",
        &fact.source_item,
        MAX_SUMMARY_FACT_FIELD_BYTES,
    )?;
    validate_artifact_hash("summary fact digest", &fact.digest)?;
    validate_summary_fact_kind(&fact.kind)
}

fn validate_summary_fact_kind(kind: &SummaryFactKind) -> Result<(), String> {
    match kind {
        SummaryFactKind::PointerProvenanceEq { left, right }
        | SummaryFactKind::FatPointerMetadataEq { left, right } => {
            validate_canonical_text(
                "summary fact left endpoint",
                left,
                MAX_SUMMARY_FACT_FIELD_BYTES,
            )?;
            validate_canonical_text(
                "summary fact right endpoint",
                right,
                MAX_SUMMARY_FACT_FIELD_BYTES,
            )
        }
        SummaryFactKind::Other { schema } => {
            validate_canonical_schema("summary fact kind schema", schema)
        }
    }
}

/// Counterexample payload for failed obligations.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Counterexample {
    pub format: String,
    pub data: serde_json::Value,
}

/// Metadata key/value carried without engine-specific interpretation.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct MetadataEntry {
    pub key: String,
    pub value: String,
}

/// Release-grade manifest for one verifier run.
///
/// Unlike [`VerificationRunResult`], this is shaped for dscan/dpub admission:
/// it lists the requested obligations, accepted proof evidence, rejected or
/// diagnostic evidence, skipped obligations, and artifact hashes in one
/// deterministic envelope.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct VerificationRunManifest {
    pub schema_version: String,
    pub run_id: String,
    pub bundle_id: String,
    pub subject: BundleSubject,
    pub engine: EngineManifest,
    pub context: VerifierExecutionSnapshot,
    pub status: VerificationRunStatus,
    pub summary: VerificationRunSummary,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub obligations: Vec<ManifestObligation>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub accepted_evidence: Vec<ManifestEvidenceDecision>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub rejected_evidence: Vec<ManifestEvidenceDecision>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub skipped: Vec<SkippedObligation>,
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        deserialize_with = "deserialize_run_manifest_evidence_artifacts"
    )]
    pub artifacts: Vec<EvidenceArtifact>,
    pub publication: EvidencePublicationMetadata,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<String>,
}

impl VerificationRunManifest {
    /// Build a run manifest from a verifier result envelope.
    ///
    /// Publicly mutable result fields are treated as input only: this method
    /// first recomputes fail-closed derived state so a forged in-memory status
    /// or summary cannot become an actionable release manifest.
    #[must_use]
    pub fn from_result(result: &VerificationRunResult) -> Self {
        if result.validate_derived_state().is_ok() {
            return Self::from_validated_result(result);
        }
        let input_error = result.validate_input_state().err();
        let canonical = result.canonicalized_derived_state();
        let mut manifest = Self::from_validated_result(&canonical);
        if let Some(error) = input_error {
            // This infallible compatibility constructor remains useful for
            // diagnostics, but structurally invalid source identity/inventory
            // must never be laundered into an actionable manifest. Callers
            // requiring a validated manifest use `try_to_manifest`.
            manifest.status = VerificationRunStatus::Inconclusive;
            manifest
                .diagnostics
                .push(format!("source verifier result failed structural validation: {error}"));
        }
        manifest
    }

    fn from_validated_result(result: &VerificationRunResult) -> Self {
        let obligations = manifest_obligations(result);
        let mut accepted_evidence = Vec::new();
        let mut rejected_evidence = Vec::new();
        let mut artifacts = Vec::new();
        let mut diagnostics = result.diagnostics.clone();

        // Index obligations by id once; a per-evidence find() over the
        // requested set is O(n*m) — the same reintroduced-quadratic family the
        // skipped_obligations/from_parts/manifest_obligations fixes closed.
        let obligation_by_id: FxHashMap<&str, &TrustObligation> = {
            let mut map = FxHashMap::default();
            for obligation in &result.requested_obligations {
                map.entry(obligation.obligation_id.as_str()).or_insert(obligation);
            }
            map
        };

        for evidence in &result.evidence {
            artifacts.extend(evidence.artifacts.clone());
            let decision = ManifestEvidenceDecision::classify(result, evidence, &obligation_by_id);
            if decision.disposition == EvidenceDisposition::AcceptedProof {
                accepted_evidence.push(decision);
            } else {
                rejected_evidence.push(decision);
            }
        }

        artifacts.sort_by(|left, right| {
            (&left.kind, &left.uri, &left.hash.algorithm, &left.hash.value).cmp(&(
                &right.kind,
                &right.uri,
                &right.hash.algorithm,
                &right.hash.value,
            ))
        });
        artifacts.dedup();

        // Set-based dedup: `Vec::contains` per diagnostic is O(d^2) once every
        // skipped obligation carries a release-blocking proof-gap line.
        let mut seen_diagnostics: FxHashSet<String> = diagnostics.iter().cloned().collect();
        for diagnostic in release_blocking_skipped_proof_gap_diagnostics(&result.skipped) {
            if seen_diagnostics.insert(diagnostic.clone()) {
                diagnostics.push(diagnostic);
            }
        }

        Self {
            schema_version: RUN_MANIFEST_SCHEMA_VERSION.to_string(),
            run_id: result.run_id.clone(),
            bundle_id: result.bundle_id.clone(),
            subject: result.subject.clone(),
            engine: result.engine.clone(),
            context: result.context.clone(),
            status: result.status,
            summary: result.summary.clone(),
            obligations,
            accepted_evidence,
            rejected_evidence,
            skipped: result.skipped.clone(),
            artifacts,
            publication: result.publication.clone(),
            diagnostics,
        }
    }

    /// Validate a deserialized release manifest by reconstructing its typed
    /// run inputs and reclassifying every evidence decision and artifact.
    pub fn validate_derived_state(&self) -> Result<(), String> {
        if self.schema_version != RUN_MANIFEST_SCHEMA_VERSION {
            return Err(format!(
                "unsupported verifier manifest schema `{}`; expected `{RUN_MANIFEST_SCHEMA_VERSION}`",
                self.schema_version
            ));
        }
        validate_envelope_identifier("manifest run_id", &self.run_id)?;
        validate_envelope_identifier("manifest bundle_id", &self.bundle_id)?;
        if self.context.run_id != self.run_id {
            return Err("verifier manifest run_id does not match its execution context".to_string());
        }
        validate_cancellation_snapshot(&self.context.cancellation)?;
        let evidence_count = self
            .accepted_evidence
            .len()
            .checked_add(self.rejected_evidence.len())
            .ok_or_else(|| "verifier manifest evidence count overflowed".to_string())?;
        validate_run_collection_limits(
            self.obligations.len(),
            evidence_count,
            self.skipped.len(),
            self.diagnostics.len(),
        )?;
        validate_diagnostics("verifier manifest", &self.diagnostics, MAX_VERIFIER_RUN_DIAGNOSTICS)?;
        if self.artifacts.len() > MAX_EVIDENCE_ARTIFACTS_PER_RUN_MANIFEST
            || self
                .accepted_evidence
                .iter()
                .chain(&self.rejected_evidence)
                .any(|decision| decision.artifacts.len() > MAX_EVIDENCE_ARTIFACTS_PER_OBLIGATION)
        {
            return Err("verifier manifest evidence exceeds an artifact safety limit".to_string());
        }
        for artifact in &self.artifacts {
            validate_evidence_artifact(artifact)?;
        }
        for decision in self.accepted_evidence.iter().chain(&self.rejected_evidence) {
            for artifact in &decision.artifacts {
                validate_evidence_artifact(artifact)?;
            }
        }

        let mut requested_obligations = Vec::new();
        let mut seen_obligations = FxHashSet::default();
        for obligation in &self.obligations {
            validate_envelope_identifier("manifest obligation_id", &obligation.obligation_id)?;
            if !seen_obligations.insert(obligation.obligation_id.as_str()) {
                return Err("verifier manifest contains duplicate obligation IDs".to_string());
            }
            if let Some(source) = &obligation.source {
                let kind = obligation.kind.clone().ok_or_else(|| {
                    "requested manifest obligation omitted its typed kind".to_string()
                })?;
                if obligation.admitted
                    && (kind != ObligationKind::ArithmeticSafety
                        || obligation.required_strength.is_some())
                {
                    return Err(
                        "manifest synthetic admission has an incompatible kind or proof strength"
                            .to_string(),
                    );
                }
                let metadata = if obligation.admitted {
                    canonical_default_admission_metadata()
                } else {
                    Vec::new()
                };
                requested_obligations.push(TrustObligation {
                    obligation_id: obligation.obligation_id.clone(),
                    kind,
                    contract_id: None,
                    proof_item_id: None,
                    source: source.clone(),
                    description: if obligation.admitted {
                        TRUST_MC_DEFAULT_FUNCTION_DESCRIPTION.to_string()
                    } else {
                        String::new()
                    },
                    required_strength: (!obligation.admitted)
                        .then(|| obligation.required_strength.clone())
                        .flatten(),
                    summary_facts: Vec::new(),
                    metadata,
                });
            } else if obligation.admitted {
                return Err("non-requested manifest obligation cannot claim synthetic admission"
                    .to_string());
            }
        }

        let mut evidence = Vec::new();
        let mut seen_evidence_ids = FxHashSet::default();
        let mut seen_evidence_pairs = FxHashSet::default();
        for decision in self.accepted_evidence.iter().chain(&self.rejected_evidence) {
            validate_envelope_identifier("manifest evidence_id", &decision.evidence_id)?;
            validate_envelope_identifier(
                "manifest evidence obligation_id",
                &decision.obligation_id,
            )?;
            if !seen_evidence_ids.insert(decision.evidence_id.as_str()) {
                return Err("verifier manifest contains duplicate evidence IDs".to_string());
            }
            if !seen_evidence_pairs
                .insert((decision.evidence_id.as_str(), decision.obligation_id.as_str()))
            {
                return Err("verifier manifest contains duplicate evidence decisions".to_string());
            }
            validate_diagnostics(
                "manifest evidence decision",
                &decision.diagnostics,
                MAX_EVIDENCE_DIAGNOSTICS_PER_RECORD,
            )?;
            if let Some(counterexample) = &decision.counterexample {
                validate_counterexample(counterexample)?;
            }
            evidence.push(ObligationEvidence {
                evidence_id: decision.evidence_id.clone(),
                obligation_id: decision.obligation_id.clone(),
                engine: decision.engine.clone(),
                status: decision.status,
                decline: None,
                proof_strength: decision.proof_strength.clone(),
                artifacts: decision.artifacts.clone(),
                counterexample: decision.counterexample.clone(),
                publication: decision.publication.clone(),
                diagnostics: decision.diagnostics.clone(),
            });
        }

        let reconstructed = VerificationRunResult {
            schema_version: SCHEMA_VERSION.to_string(),
            run_id: self.run_id.clone(),
            bundle_id: self.bundle_id.clone(),
            subject: self.subject.clone(),
            engine: self.engine.clone(),
            context: self.context.clone(),
            status: self.status,
            summary: self.summary.clone(),
            requested_obligations,
            evidence,
            skipped: self.skipped.clone(),
            publication: self.publication.clone(),
            diagnostics: self.diagnostics.clone(),
        };
        reconstructed.validate_derived_state()?;
        let expected = Self::from_validated_result(&reconstructed);
        if &expected != self {
            return Err(
                "verifier manifest derived obligations/evidence/artifacts do not match typed inputs"
                    .to_string(),
            );
        }
        Ok(())
    }

    /// Whether this manifest may drive a release decision.
    #[must_use]
    pub fn is_release_actionable(&self) -> bool {
        matches!(self.context.invocation, VerifierInvocation::DpubReleaseGate)
            && required_publication_metadata_diagnostics(
                &self.context.invocation,
                &self.publication,
            )
            .is_empty()
            && self.status == VerificationRunStatus::Proved
            && self.validate_derived_state().is_ok()
    }

    /// Parse an untrusted JSON release manifest through a whole-envelope byte
    /// cap before serde allocates nested strings and counterexamples.
    pub fn from_json_slice(bytes: &[u8]) -> Result<Self, String> {
        validate_json_envelope_length(bytes.len(), "manifest")?;
        serde_json::from_slice(bytes).map_err(|error| error.to_string())
    }
}

impl<'de> Deserialize<'de> for VerificationRunManifest {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        struct Helper {
            schema_version: String,
            run_id: String,
            bundle_id: String,
            subject: BundleSubject,
            engine: EngineManifest,
            context: VerifierExecutionSnapshot,
            status: VerificationRunStatus,
            summary: VerificationRunSummary,
            #[serde(default, deserialize_with = "deserialize_bounded_run_records")]
            obligations: Vec<ManifestObligation>,
            #[serde(default, deserialize_with = "deserialize_bounded_run_records")]
            accepted_evidence: Vec<ManifestEvidenceDecision>,
            #[serde(default, deserialize_with = "deserialize_bounded_run_records")]
            rejected_evidence: Vec<ManifestEvidenceDecision>,
            #[serde(default, deserialize_with = "deserialize_bounded_run_records")]
            skipped: Vec<SkippedObligation>,
            #[serde(default, deserialize_with = "deserialize_run_manifest_evidence_artifacts")]
            artifacts: Vec<EvidenceArtifact>,
            publication: EvidencePublicationMetadata,
            #[serde(default, deserialize_with = "deserialize_bounded_run_diagnostics")]
            diagnostics: Vec<String>,
        }

        let helper = Helper::deserialize(deserializer)?;
        let manifest = Self {
            schema_version: helper.schema_version,
            run_id: helper.run_id,
            bundle_id: helper.bundle_id,
            subject: helper.subject,
            engine: helper.engine,
            context: helper.context,
            status: helper.status,
            summary: helper.summary,
            obligations: helper.obligations,
            accepted_evidence: helper.accepted_evidence,
            rejected_evidence: helper.rejected_evidence,
            skipped: helper.skipped,
            artifacts: helper.artifacts,
            publication: helper.publication,
            diagnostics: helper.diagnostics,
        };
        manifest.validate_derived_state().map_err(de::Error::custom)?;
        Ok(manifest)
    }
}

fn manifest_obligations(result: &VerificationRunResult) -> Vec<ManifestObligation> {
    // Index evidence/skipped once; the prior per-obligation rescans were O(n*m).
    let mut evidence_count_by_id: FxHashMap<&str, usize> = FxHashMap::default();
    for item in &result.evidence {
        *evidence_count_by_id.entry(item.obligation_id.as_str()).or_insert(0) += 1;
    }
    let skipped_ids: FxHashSet<&str> =
        result.skipped.iter().map(|item| item.obligation_id.as_str()).collect();

    let mut seen_ids: FxHashSet<&str> = FxHashSet::default();
    let mut obligations: Vec<ManifestObligation> =
        Vec::with_capacity(result.requested_obligations.len());

    for obligation in &result.requested_obligations {
        seen_ids.insert(obligation.obligation_id.as_str());
        obligations.push(ManifestObligation {
            obligation_id: obligation.obligation_id.clone(),
            kind: Some(obligation.kind.clone()),
            required_strength: obligation.required_strength.clone(),
            source: Some(obligation.source.clone()),
            admitted: obligation.is_default_admission(),
            evidence_count: evidence_count_by_id
                .get(obligation.obligation_id.as_str())
                .copied()
                .unwrap_or(0),
            skipped: skipped_ids.contains(obligation.obligation_id.as_str()),
        });
    }

    for evidence in &result.evidence {
        if !seen_ids.insert(evidence.obligation_id.as_str()) {
            continue;
        }
        obligations.push(ManifestObligation {
            obligation_id: evidence.obligation_id.clone(),
            kind: None,
            required_strength: None,
            source: None,
            admitted: false,
            evidence_count: evidence_count_by_id
                .get(evidence.obligation_id.as_str())
                .copied()
                .unwrap_or(0),
            skipped: skipped_ids.contains(evidence.obligation_id.as_str()),
        });
    }

    for skipped in &result.skipped {
        if !seen_ids.insert(skipped.obligation_id.as_str()) {
            continue;
        }
        obligations.push(ManifestObligation {
            obligation_id: skipped.obligation_id.clone(),
            kind: Some(skipped.kind.clone()),
            required_strength: None,
            source: None,
            admitted: false,
            evidence_count: 0,
            skipped: true,
        });
    }

    obligations.sort_by(|left, right| left.obligation_id.cmp(&right.obligation_id));
    obligations
}

/// One obligation entry in a run manifest.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ManifestObligation {
    pub obligation_id: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub kind: Option<ObligationKind>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub required_strength: Option<ProofStrength>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source: Option<SourceLocation>,
    /// Whether this requested entry is the synthetic non-obligation admission.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub admitted: bool,
    pub evidence_count: usize,
    pub skipped: bool,
}

/// Classification of one evidence item inside a run manifest.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ManifestEvidenceDecision {
    pub evidence_id: String,
    pub obligation_id: String,
    pub engine: EngineManifest,
    pub status: EvidenceStatus,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub proof_strength: Option<ProofStrength>,
    pub disposition: EvidenceDisposition,
    pub reason: String,
    /// Publication identity carried by the typed evidence. Retaining it lets a
    /// deserialized manifest recompute aggregate publication conflicts instead
    /// of trusting the top-level summary.
    #[serde(default, skip_serializing_if = "evidence_publication_is_empty")]
    pub publication: EvidencePublicationMetadata,
    /// Counterexample retained exactly for rejected/failed evidence audit.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub counterexample: Option<Counterexample>,
    /// Engine diagnostics retained exactly instead of being dropped while
    /// shaping the release manifest.
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        deserialize_with = "deserialize_bounded_evidence_diagnostics"
    )]
    pub diagnostics: Vec<String>,
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        deserialize_with = "deserialize_obligation_evidence_artifacts"
    )]
    pub artifacts: Vec<EvidenceArtifact>,
}

impl ManifestEvidenceDecision {
    fn classify(
        result: &VerificationRunResult,
        evidence: &ObligationEvidence,
        obligation_by_id: &FxHashMap<&str, &TrustObligation>,
    ) -> Self {
        let disposition = evidence_disposition(result, evidence, obligation_by_id);
        let reason = evidence_disposition_reason(&disposition, evidence);

        Self {
            evidence_id: evidence.evidence_id.clone(),
            obligation_id: evidence.obligation_id.clone(),
            engine: evidence.engine.clone(),
            status: evidence.status,
            proof_strength: evidence.proof_strength.clone(),
            disposition,
            reason,
            publication: evidence.publication.clone(),
            counterexample: evidence.counterexample.clone(),
            diagnostics: evidence.diagnostics.clone(),
            artifacts: evidence.artifacts.clone(),
        }
    }
}

fn evidence_disposition(
    result: &VerificationRunResult,
    evidence: &ObligationEvidence,
    obligation_by_id: &FxHashMap<&str, &TrustObligation>,
) -> EvidenceDisposition {
    if evidence.engine != result.engine {
        return EvidenceDisposition::RejectedEngineProvenance;
    }
    if evidence.status != EvidenceStatus::Proved {
        return EvidenceDisposition::RejectedStatus;
    }
    if evidence.proof_strength.as_ref().is_some_and(ProofStrength::is_bounded) {
        return EvidenceDisposition::RejectedBounded;
    }
    // Indexed lookup: a per-evidence find() over requested_obligations was the
    // O(n*m) scan that pushed 100k-obligation result assembly past 20 seconds.
    let required_strength = obligation_by_id
        .get(evidence.obligation_id.as_str())
        .and_then(|obligation| obligation.required_strength.as_ref());
    if !evidence.satisfies_strength_requirement(required_strength) {
        return EvidenceDisposition::RejectedInsufficientStrength;
    }
    if !evidence.satisfies_proof_artifact_policy() {
        return EvidenceDisposition::RejectedMissingProofArtifacts;
    }
    EvidenceDisposition::AcceptedProof
}

fn evidence_disposition_reason(
    disposition: &EvidenceDisposition,
    evidence: &ObligationEvidence,
) -> String {
    match disposition {
        EvidenceDisposition::AcceptedProof => {
            "publication-grade proof evidence accepted".to_string()
        }
        EvidenceDisposition::RejectedBounded => {
            "bounded evidence is diagnostic-only in full verification".to_string()
        }
        EvidenceDisposition::RejectedInsufficientStrength => {
            "evidence proof strength is not publication-grade".to_string()
        }
        EvidenceDisposition::RejectedMissingProofArtifacts => {
            "proof evidence is missing replay/check or solver transcript artifacts".to_string()
        }
        EvidenceDisposition::RejectedStatus => {
            format!("evidence status {:?} is not a proof", evidence.status)
        }
        EvidenceDisposition::RejectedEngineProvenance => {
            "evidence engine does not match run engine".to_string()
        }
    }
}

/// Manifest-level evidence disposition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum EvidenceDisposition {
    AcceptedProof,
    RejectedBounded,
    RejectedInsufficientStrength,
    RejectedMissingProofArtifacts,
    RejectedStatus,
    RejectedEngineProvenance,
}

#[cfg(test)]
mod tests {
    use super::*;

    /// R4 §1 step-2 pin: the island-citation metadata contract. The keys are
    /// stable wire strings; a clause carrying them round-trips losslessly
    /// with its predicate UNCHANGED (`Unsupported` stays `Unsupported` — the
    /// metadata channel is inert to verdicts by standing doctrine, and the
    /// discharge consumer is the only party that may ever read these keys
    /// into a proof path, after digest validation).
    #[test]
    fn island_citation_metadata_round_trips_inert() {
        assert_eq!(ISLAND_CITATION_NAME_METADATA_KEY, "trust.island_citation.name");
        assert_eq!(ISLAND_CITATION_DIGEST_METADATA_KEY, "trust.island_citation.digest");
        let contract = TrustContract {
            contract_id: "c0".to_string(),
            kind: ContractKind::Ensures,
            predicate: ContractPredicate::Unsupported {
                reason: "island citation `sqr` awaits typed-citation discharge".to_string(),
            },
            source: SourceLocation::default(),
            metadata: vec![
                MetadataEntry {
                    key: ISLAND_CITATION_NAME_METADATA_KEY.to_string(),
                    value: "sqr".to_string(),
                },
                MetadataEntry {
                    key: ISLAND_CITATION_DIGEST_METADATA_KEY.to_string(),
                    value: "deadbeef".to_string(),
                },
            ],
        };
        let json = serde_json::to_string(&contract).expect("serialize");
        let back: TrustContract = serde_json::from_str(&json).expect("round-trip");
        assert_eq!(back, contract, "citation metadata must ride losslessly");
        assert!(
            matches!(back.predicate, ContractPredicate::Unsupported { .. }),
            "the predicate stays refused until the discharge consumer exists"
        );
    }

    struct AlwaysProves {
        manifest: EngineManifest,
    }

    struct CancelsDuringVerify {
        manifest: EngineManifest,
        cancellation: CancellationToken,
    }

    impl AlwaysProves {
        fn new() -> Self {
            let mut manifest = EngineManifest::new("unit-engine", "0.1.0", EngineKind::Deductive);
            manifest.proof_modes.push(ReasoningKind::Deductive);
            Self { manifest }
        }
    }

    impl CancelsDuringVerify {
        fn new(cancellation: CancellationToken) -> Self {
            let mut manifest = EngineManifest::new("cancel-engine", "0.1.0", EngineKind::Deductive);
            manifest.proof_modes.push(ReasoningKind::Deductive);
            Self { manifest, cancellation }
        }
    }

    impl VerificationEngine for AlwaysProves {
        fn manifest(&self) -> &EngineManifest {
            &self.manifest
        }

        fn supports(&self, obligation: &TrustObligation) -> SupportLevel {
            match obligation.kind {
                ObligationKind::Postcondition => SupportLevel::Preferred,
                _ => SupportLevel::Unsupported { reason: "only postconditions".to_string() },
            }
        }

        fn verify_validated(
            &self,
            request: ValidatedVerificationRequest<'_>,
        ) -> Vec<ObligationEvidence> {
            let (bundle, obligations) = request.into_parts();
            obligations
                .iter()
                .filter(|obligation| self.supports(obligation).is_supported())
                .map(|obligation| ObligationEvidence {
                    evidence_id: format!("{}:{}", bundle.bundle_id, obligation.obligation_id),
                    obligation_id: obligation.obligation_id.clone(),
                    engine: self.manifest.clone(),
                    status: EvidenceStatus::Proved,
                    decline: None,
                    proof_strength: Some(ProofStrength::deductive()),
                    artifacts: vec![certificate_artifact(
                        &obligation.obligation_id,
                        "unit-engine-proof",
                    )],
                    counterexample: None,
                    publication: EvidencePublicationMetadata {
                        publication_plan_hash: bundle.publication.dpub_plan_hash.clone(),
                        trust_engines_lock_hash: bundle.publication.trust_engines_lock_hash.clone(),
                        ..EvidencePublicationMetadata::default()
                    },
                    diagnostics: Vec::new(),
                })
                .collect()
        }
    }

    impl VerificationEngine for CancelsDuringVerify {
        fn manifest(&self) -> &EngineManifest {
            &self.manifest
        }

        fn supports(&self, _obligation: &TrustObligation) -> SupportLevel {
            SupportLevel::Preferred
        }

        fn verify_validated(
            &self,
            _request: ValidatedVerificationRequest<'_>,
        ) -> Vec<ObligationEvidence> {
            self.cancellation.cancel(CancellationReason::DeadlineExceeded);
            Vec::new()
        }
    }

    fn obligation(kind: ObligationKind) -> TrustObligation {
        TrustObligation {
            obligation_id: "obl-1".to_string(),
            kind,
            contract_id: Some("contract-1".to_string()),
            proof_item_id: None,
            source: SourceLocation {
                file: Some("src/lib.rs".to_string()),
                line: Some(10),
                column: Some(5),
                end_line: Some(10),
                end_column: Some(20),
            },
            description: "return value satisfies postcondition".to_string(),
            required_strength: None,
            summary_facts: Vec::new(),
            metadata: Vec::new(),
        }
    }

    fn obligation_with_id(obligation_id: &str, kind: ObligationKind) -> TrustObligation {
        let mut obligation = obligation(kind);
        obligation.obligation_id = obligation_id.to_string();
        obligation
    }

    fn semantic_digest_bundle() -> TrustContractBundle {
        let mut bundle = TrustContractBundle::empty(
            "bundle-semantic-digest",
            BundleSubject::Function {
                crate_name: "demo".to_string(),
                path: "demo::semantic_digest".to_string(),
            },
        );
        bundle.contracts.push(TrustContract {
            contract_id: "contract-1".to_string(),
            kind: ContractKind::Ensures,
            predicate: ContractPredicate::MemoryIr {
                schema: "trust.test.memory-predicate.v1".to_string(),
                value: serde_json::json!({"predicate": "owned(ptr)", "width": 64}),
            },
            source: SourceLocation::default(),
            metadata: vec![
                MetadataEntry { key: "contract.owner".to_string(), value: "compiler".to_string() },
                MetadataEntry { key: "contract.mode".to_string(), value: "strict".to_string() },
            ],
        });
        bundle.proof_items.push(TrustProofItem {
            proof_item_id: "proof-1".to_string(),
            name: "semantic_digest_proof".to_string(),
            kind: ProofItemKind::ProofFn,
            target: ProofItemTarget::Contract { contract_id: "contract-1".to_string() },
            signature: ProofItemSignature::default(),
            body: ProofItemBody::NativeScript {
                engine: "trust-vc".to_string(),
                text: "prove owned(ptr)".to_string(),
            },
            source: SourceLocation::default(),
            contracts: Vec::new(),
            metadata: vec![
                MetadataEntry { key: "proof.owner".to_string(), value: "compiler".to_string() },
                MetadataEntry { key: "proof.mode".to_string(), value: "strict".to_string() },
            ],
        });
        let mut obligation = obligation(ObligationKind::MemorySafety);
        obligation.proof_item_id = Some("proof-1".to_string());
        obligation.required_strength =
            Some(ProofStrength::certified(ReasoningKind::OwnershipAnalysis));
        obligation.metadata = vec![
            MetadataEntry {
                key: "trust_vc.mir_memory.proof_unit".to_string(),
                value: "{\"predicate\":\"owned(ptr)\"}".to_string(),
            },
            MetadataEntry {
                key: "trust.vc.formula.payload".to_string(),
                value: "owned(ptr)".to_string(),
            },
        ];
        bundle.obligations.push(obligation);
        bundle
    }

    fn artifact(kind: EvidenceArtifactKind, uri: &str, hash_value: &str) -> EvidenceArtifact {
        let hash_value = if is_stable_sha256_hex(hash_value) {
            hash_value.to_string()
        } else {
            stable_sha256_hex(hash_value.as_bytes())
        };
        EvidenceArtifact {
            kind,
            uri: uri.to_string(),
            hash: ArtifactHash { algorithm: "sha256".to_string(), value: hash_value },
            materialization: None,
        }
    }

    fn bound_artifact(
        kind: EvidenceArtifactKind,
        owner: &str,
        proof_binding_id: &str,
        payload: &[u8],
        referenced_artifacts: Vec<EvidenceArtifactReference>,
    ) -> EvidenceArtifact {
        let (materialization, hash) = EvidenceArtifactMaterialization::new_bound(
            kind,
            payload,
            proof_binding_id,
            owner,
            referenced_artifacts,
        )
        .expect("test artifact envelope is canonical");
        EvidenceArtifact {
            kind,
            uri: format!("artifact://unit-test/proof-artifacts/{}", hash.value),
            hash,
            materialization: Some(materialization),
        }
    }

    fn certificate_artifact(owner: &str, proof_binding_id: &str) -> EvidenceArtifact {
        bound_artifact(
            EvidenceArtifactKind::ProofCertificate,
            owner,
            proof_binding_id,
            format!("checked certificate for {owner}").as_bytes(),
            Vec::new(),
        )
    }

    fn proof_dag_artifacts(owner: &str, proof_binding_id: &str) -> Vec<EvidenceArtifact> {
        let input = bound_artifact(
            EvidenceArtifactKind::NormalizedObligation,
            owner,
            proof_binding_id,
            format!("normalized obligation for {owner}").as_bytes(),
            Vec::new(),
        );
        let transcript = bound_artifact(
            EvidenceArtifactKind::SolverTranscript,
            owner,
            proof_binding_id,
            b"exact solver transcript",
            vec![EvidenceArtifactReference { kind: input.kind, hash: input.hash.clone() }],
        );
        let check = bound_artifact(
            EvidenceArtifactKind::ProofCheckReport,
            owner,
            proof_binding_id,
            b"exact proof check report",
            vec![EvidenceArtifactReference {
                kind: transcript.kind,
                hash: transcript.hash.clone(),
            }],
        );
        vec![input, transcript, check]
    }

    fn pdr_proof_dag_artifacts(owner: &str, proof_binding_id: &str) -> Vec<EvidenceArtifact> {
        let input = bound_artifact(
            EvidenceArtifactKind::NormalizedObligation,
            owner,
            proof_binding_id,
            format!("normalized PDR obligation for {owner}").as_bytes(),
            Vec::new(),
        );
        let input_reference = EvidenceArtifactReference {
            kind: input.kind,
            hash: input.hash.clone(),
        };
        let transcript = bound_artifact(
            EvidenceArtifactKind::SolverTranscript,
            owner,
            proof_binding_id,
            b"exact PDR solver transcript",
            vec![input_reference.clone()],
        );
        let model = bound_artifact(
            EvidenceArtifactKind::Model,
            owner,
            proof_binding_id,
            b"exact PDR invariant model",
            vec![input_reference],
        );
        let replay = bound_artifact(
            EvidenceArtifactKind::ReplayLog,
            owner,
            proof_binding_id,
            b"exact PDR replay log",
            vec![
                EvidenceArtifactReference {
                    kind: transcript.kind,
                    hash: transcript.hash.clone(),
                },
                EvidenceArtifactReference { kind: model.kind, hash: model.hash.clone() },
            ],
        );
        let check = bound_artifact(
            EvidenceArtifactKind::ProofCheckReport,
            owner,
            proof_binding_id,
            b"exact PDR proof check report",
            vec![
                EvidenceArtifactReference {
                    kind: transcript.kind,
                    hash: transcript.hash.clone(),
                },
                EvidenceArtifactReference { kind: replay.kind, hash: replay.hash.clone() },
                EvidenceArtifactReference { kind: model.kind, hash: model.hash.clone() },
            ],
        );
        vec![input, transcript, model, replay, check]
    }

    fn evidence(
        engine: &EngineManifest,
        evidence_id: &str,
        obligation_id: &str,
        status: EvidenceStatus,
        proof_strength: Option<ProofStrength>,
        artifacts: Vec<EvidenceArtifact>,
    ) -> ObligationEvidence {
        ObligationEvidence {
            evidence_id: evidence_id.to_string(),
            obligation_id: obligation_id.to_string(),
            engine: engine.clone(),
            status,
            decline: None,
            proof_strength,
            artifacts,
            counterexample: None,
            publication: EvidencePublicationMetadata::default(),
            diagnostics: Vec::new(),
        }
    }

    fn fully_proved_result(invocation: VerifierInvocation) -> VerificationRunResult {
        let engine = EngineManifest::new("unit-engine", "0.1.0", EngineKind::Deductive);
        let mut bundle = TrustContractBundle::empty(
            "bundle-fully-proved",
            BundleSubject::Function {
                crate_name: "demo".to_string(),
                path: "demo::fully_proved".to_string(),
            },
        );
        bundle.publication.dpub_plan_hash = Some("sha256:plan".to_string());
        bundle.publication.trust_engines_lock_hash = Some("sha256:lock".to_string());
        let obligation = obligation_with_id("obl-fully-proved", ObligationKind::Postcondition);
        bundle.obligations.push(obligation.clone());
        let mut proof = evidence(
            &engine,
            "ev-fully-proved",
            &obligation.obligation_id,
            EvidenceStatus::Proved,
            Some(ProofStrength::deductive()),
            vec![certificate_artifact(&obligation.obligation_id, "fully-proved-proof")],
        );
        proof.publication = EvidencePublicationMetadata {
            dscan_attestation_hash: Some("sha256:dscan".to_string()),
            dpub_release_id: Some("release-1".to_string()),
            publication_plan_hash: bundle.publication.dpub_plan_hash.clone(),
            trust_engines_lock_hash: bundle.publication.trust_engines_lock_hash.clone(),
            evidence_bundle_hash: Some("sha256:evidence-bundle".to_string()),
        };
        VerificationRunResult::from_evidence(
            VerifierExecutionContext::new("run-fully-proved")
                .with_invocation(invocation)
                .snapshot(),
            &bundle,
            engine,
            &bundle.obligations,
            vec![proof],
        )
    }

    #[test]
    fn synthetic_trust_mc_admission_is_excluded_from_counts_and_verdict() {
        // Trust: the synthetic trust-mc per-function admission carries a
        // `bool_literal(false)` goal and is "proved" vacuously by construction.
        // It must never count as a real proof, never satisfy a real obligation,
        // and never let a function read as Proved. This is the regression guard
        // for the false-confidence bug where ~245 admissions were reported as
        // proved obligations.
        let engine = EngineManifest::new("unit-engine", "0.1.0", EngineKind::Deductive);

        let mut admission = obligation_with_id(
            "vc:demo__f:trust_mc_default_function:0",
            ObligationKind::ArithmeticSafety,
        );
        admission.contract_id = None;
        admission.description = TRUST_MC_DEFAULT_FUNCTION_DESCRIPTION.to_string();
        admission.metadata = canonical_default_admission_metadata();
        assert!(admission.is_default_admission(), "fixture must be recognized as the admission");

        let admission_evidence = evidence(
            &engine,
            "ev-admission",
            &admission.obligation_id,
            EvidenceStatus::Proved,
            Some(ProofStrength::smt_unsat()),
            Vec::new(),
        );

        // Admission-only bundle: zero real obligations, zero proved, one admitted.
        let summary = VerificationRunSummary::from_parts(
            std::slice::from_ref(&admission),
            std::slice::from_ref(&admission_evidence),
            &[],
            0,
        );
        assert_eq!(summary.proved, 0, "the admission must not be counted as proved");
        assert_eq!(summary.requested_obligations, 0, "the admission is not a real obligation");
        assert_eq!(summary.admitted, 1, "the admission is tracked separately for audit");

        let snapshot = VerifierExecutionContext::new("run-admission").snapshot();
        assert_eq!(
            VerificationRunStatus::from_summary(&summary, &snapshot),
            VerificationRunStatus::Empty,
            "a function whose only obligation is the vacuous admission must not be Proved",
        );

        // With a real, still-unknown obligation alongside the admission: the
        // real obligation is counted, the admission is still excluded, and the
        // run stays Inconclusive (fail-closed) — never Proved on the back of the
        // admission.
        let real = obligation_with_id("vc:demo__f:overflow:0", ObligationKind::ArithmeticSafety);
        let real_unknown = evidence(
            &engine,
            "ev-real",
            &real.obligation_id,
            EvidenceStatus::Unknown,
            None,
            Vec::new(),
        );
        let summary2 = VerificationRunSummary::from_parts(
            &[admission.clone(), real.clone()],
            &[admission_evidence.clone(), real_unknown],
            &[],
            0,
        );
        assert_eq!(summary2.requested_obligations, 1, "only the real obligation is requested");
        assert_eq!(summary2.admitted, 1, "the admission is still excluded");
        assert_eq!(summary2.proved, 0, "the vacuous admission cannot satisfy the real obligation");
        assert_eq!(summary2.unknown, 1, "the real obligation is unknown");
        assert_eq!(
            VerificationRunStatus::from_summary(&summary2, &snapshot),
            VerificationRunStatus::Inconclusive,
            "an unknown real obligation keeps the run Inconclusive even with the admission proved",
        );
    }

    #[test]
    fn large_obligation_set_result_assembly_is_not_quadratic() {
        // Regression guard for the O(n*m) result-assembly scans (skipped_obligations,
        // from_parts, manifest_obligations) that hung self-verification of large rustc
        // crates for hours. Under the fixed O(n+m) assembly this finishes in well under a
        // second; a reintroduced quadratic blows far past the generous wall-clock bound.
        use std::time::Instant;

        const REQUESTED: usize = 100_000;

        let engine = EngineManifest::new("perf-engine", "0.1.0", EngineKind::Deductive);
        let bundle = TrustContractBundle::empty(
            "bundle-perf",
            BundleSubject::Function {
                crate_name: "demo".to_string(),
                path: "demo::big".to_string(),
            },
        );

        let requested: Vec<TrustObligation> = (0..REQUESTED)
            .map(|i| obligation_with_id(&format!("obl-{i:08}"), ObligationKind::Postcondition))
            .collect();

        // Only even-indexed obligations get (Proved) evidence; odd ones must end up skipped.
        // Proved status is required to exercise the per-evidence obligation lookup in from_parts.
        let evidence: Vec<ObligationEvidence> = (0..REQUESTED)
            .filter(|i| i % 2 == 0)
            .map(|i| {
                evidence(
                    &engine,
                    &format!("ev-{i:08}"),
                    &format!("obl-{i:08}"),
                    EvidenceStatus::Proved,
                    Some(ProofStrength::deductive()),
                    Vec::new(),
                )
            })
            .collect();

        let context = VerifierExecutionContext::compatibility().snapshot();

        let started = Instant::now();
        let result =
            VerificationRunResult::from_evidence(context, &bundle, engine, &requested, evidence);
        let manifest = result.to_manifest();
        let elapsed = started.elapsed();

        assert_eq!(result.summary.requested_obligations, REQUESTED);
        assert_eq!(result.skipped.len(), REQUESTED / 2);
        assert_eq!(manifest.obligations.len(), REQUESTED);
        assert!(
            elapsed.as_secs() < 20,
            "result assembly took {elapsed:?} for {REQUESTED} obligations — likely a reintroduced O(n*m) scan",
        );
    }

    #[test]
    fn empty_bundle_has_no_contracts_or_obligations() {
        let bundle = TrustContractBundle::empty(
            "bundle-1",
            BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
        );

        assert!(bundle.is_empty());
        assert_eq!(bundle.schema_version, SCHEMA_VERSION);
        assert_eq!(bundle.publication, PublicationMetadata::default());
        bundle.validate().expect("empty bundle has canonical identity");
        let encoded = serde_json::to_vec(&bundle).expect("serialize empty bundle");
        let decoded = TrustContractBundle::from_json_slice(&encoded)
            .expect("checked bundle ingress accepts canonical bundle");
        assert_eq!(decoded, bundle);
    }

    #[test]
    fn public_obligation_semantic_digest_is_order_invariant_and_transport_aware() {
        let bundle = semantic_digest_bundle();
        let expected = bundle
            .canonical_obligation_semantic_digest_sha256(&bundle.obligations[0])
            .expect("canonical semantic digest");
        assert_eq!(expected.len(), 64);
        assert!(
            expected.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        );

        let mut reordered = bundle.clone();
        reordered.obligations[0].metadata.reverse();
        reordered.contracts[0].metadata.reverse();
        reordered.proof_items[0].metadata.reverse();
        assert_eq!(
            reordered
                .canonical_obligation_semantic_digest_sha256(&reordered.obligations[0])
                .expect("metadata order is not semantic"),
            expected
        );

        let mut transported = bundle.clone();
        transported.obligations[0].metadata.push(MetadataEntry {
            key: "trust.trust_ir.native.request_digest".to_string(),
            value: "a".repeat(64),
        });
        assert_eq!(
            transported
                .canonical_obligation_semantic_digest_sha256(&transported.obligations[0])
                .expect("known post-lowering transport field is excluded"),
            expected
        );

        for key in [
            "trust.trust-wp.claim-digest.v1",
            "trust.trust-wp.proof-context.v1",
            "trust-trust-wp.typed-formula.synthetic_contract.v1",
            "trust-trust-mc.typed-chc-obligation.synthetic_contract.v1",
            "trust-mc.typed-chc-obligation.binding.v1",
            "trust-mc.typed-chc-obligation.synthetic_digest.sha256",
        ] {
            let mut suite_transport = bundle.clone();
            suite_transport.obligations[0].metadata.push(MetadataEntry {
                key: key.to_string(),
                value: "controlled native transport".to_string(),
            });
            assert_eq!(
                suite_transport
                    .canonical_obligation_semantic_digest_sha256(
                        &suite_transport.obligations[0],
                    )
                    .unwrap_or_else(|error| panic!("known transport key {key} rejected: {error}")),
                expected,
                "known native transport key {key} must not rewrite the public claim"
            );
        }

        let mut unknown_native_key = bundle.clone();
        unknown_native_key.obligations[0].metadata.push(MetadataEntry {
            key: "trust.trust_ir.native.future_semantic_claim".to_string(),
            value: "must remain authenticated".to_string(),
        });
        assert_ne!(
            unknown_native_key
                .canonical_obligation_semantic_digest_sha256(&unknown_native_key.obligations[0],)
                .expect("unknown native namespace key remains semantic"),
            expected
        );
    }

    #[test]
    fn public_obligation_semantic_digest_covers_full_claim_and_references() {
        let bundle = semantic_digest_bundle();
        let expected = bundle
            .canonical_obligation_semantic_digest_sha256(&bundle.obligations[0])
            .expect("canonical semantic digest");

        let assert_changed = |mutated: &TrustContractBundle, label: &str| {
            let actual = mutated
                .canonical_obligation_semantic_digest_sha256(&mutated.obligations[0])
                .unwrap_or_else(|error| panic!("{label} mutation must remain digestible: {error}"));
            assert_ne!(actual, expected, "{label} must be authenticated");
        };

        let mut kind = bundle.clone();
        kind.obligations[0].kind = ObligationKind::Ownership;
        assert_changed(&kind, "obligation kind");

        let mut description = bundle.clone();
        description.obligations[0].description.push_str(" (altered)");
        assert_changed(&description, "obligation description");

        let mut source = bundle.clone();
        source.obligations[0].source.line = Some(11);
        assert_changed(&source, "obligation source");

        let mut predicate_metadata = bundle.clone();
        predicate_metadata.obligations[0].metadata[0].value =
            "{\"predicate\":\"borrowed(ptr)\"}".to_string();
        assert_changed(&predicate_metadata, "typed proof-unit predicate");

        let mut contract = bundle.clone();
        contract.contracts[0].predicate =
            ContractPredicate::TrustExpr { text: "false".to_string() };
        assert_changed(&contract, "referenced contract predicate");

        let mut contract_metadata = bundle.clone();
        contract_metadata.contracts[0].metadata[0].value = "attacker".to_string();
        assert_changed(&contract_metadata, "referenced contract metadata");

        let mut proof_body = bundle.clone();
        proof_body.proof_items[0].body = ProofItemBody::NativeScript {
            engine: "trust-vc".to_string(),
            text: "admit owned(ptr)".to_string(),
        };
        assert_changed(&proof_body, "referenced proof-item body");

        let mut subject = bundle.clone();
        subject.subject = BundleSubject::Function {
            crate_name: "demo".to_string(),
            path: "demo::other_function".to_string(),
        };
        assert_changed(&subject, "bundle subject");
    }

    #[test]
    fn public_obligation_semantic_digest_batch_indexes_once_and_fails_closed() {
        let mut bundle = semantic_digest_bundle();
        let mut second = bundle.obligations[0].clone();
        second.obligation_id = "obl-2".to_string();
        second.description = "second exact public obligation".to_string();
        bundle.obligations.push(second);

        let index = bundle
            .canonical_obligation_semantic_digest_index_sha256(&bundle.obligations)
            .expect("multi-obligation digest index");
        assert_eq!(index.len(), 2);
        assert!(index.get("obl-1").is_some());
        assert!(index.get("obl-2").is_some());
        assert_ne!(index.get("obl-1"), index.get("obl-2"));

        let duplicate = vec![bundle.obligations[0].clone(), bundle.obligations[0].clone()];
        let error = bundle
            .canonical_obligation_semantic_digest_index_sha256(&duplicate)
            .expect_err("duplicate requested IDs must fail closed");
        assert!(error.contains("duplicate obligation IDs"), "{error}");

        let mut substituted = vec![bundle.obligations[0].clone()];
        substituted[0].description = "same ID, substituted claim".to_string();
        let error = bundle
            .canonical_obligation_semantic_digest_index_sha256(&substituted)
            .expect_err("same-ID substitution must fail closed");
        assert!(error.contains("differs from its canonical bundle record"), "{error}");

        let mut dangling_selected = bundle.clone();
        dangling_selected.obligations[0].proof_item_id = Some("missing-proof".to_string());
        let error = dangling_selected
            .canonical_obligation_semantic_digest_sha256(&dangling_selected.obligations[0])
            .expect_err("selected dangling proof item must fail closed");
        assert!(error.contains("references missing proof item"), "{error}");

        let mut unrelated_dangling = bundle.clone();
        unrelated_dangling.obligations[1].proof_item_id = Some("source-identity-only".to_string());
        unrelated_dangling
            .canonical_obligation_semantic_digest_sha256(&unrelated_dangling.obligations[0])
            .expect("unselected source-identity compatibility row does not block digesting");
    }

    #[test]
    fn contract_bundle_rejects_duplicate_metadata_keys_at_every_semantic_level() {
        let duplicate = |entry: &MetadataEntry| vec![entry.clone(), entry.clone()];

        let mut obligation = semantic_digest_bundle();
        obligation.obligations[0].metadata = duplicate(&obligation.obligations[0].metadata[0]);
        assert!(
            obligation
                .validate()
                .expect_err("duplicate obligation metadata")
                .contains("duplicate metadata key")
        );

        let mut contract = semantic_digest_bundle();
        contract.contracts[0].metadata = duplicate(&contract.contracts[0].metadata[0]);
        assert!(
            contract
                .validate()
                .expect_err("duplicate contract metadata")
                .contains("duplicate metadata key")
        );

        let mut proof_item = semantic_digest_bundle();
        proof_item.proof_items[0].metadata = duplicate(&proof_item.proof_items[0].metadata[0]);
        assert!(
            proof_item
                .validate()
                .expect_err("duplicate proof-item metadata")
                .contains("duplicate metadata key")
        );

        let mut bundle = semantic_digest_bundle();
        bundle.metadata = duplicate(&MetadataEntry {
            key: "bundle.owner".to_string(),
            value: "compiler".to_string(),
        });
        assert!(
            bundle
                .validate()
                .expect_err("duplicate bundle metadata")
                .contains("duplicate metadata key")
        );
    }

    #[test]
    fn contract_bundle_serde_rejects_blank_duplicate_and_oversized_inventories() {
        let mut duplicate_obligations = TrustContractBundle::empty(
            "bundle-duplicates",
            BundleSubject::Crate { name: "demo".to_string() },
        );
        let obligation = obligation_with_id("obl-duplicate", ObligationKind::Postcondition);
        duplicate_obligations.obligations = vec![obligation.clone(), obligation];
        assert!(duplicate_obligations.validate().is_err());
        let encoded = serde_json::to_vec(&duplicate_obligations)
            .expect("serialize duplicate obligation bundle");
        let error = TrustContractBundle::from_json_slice(&encoded)
            .expect_err("custom bundle deserializer must reject duplicate obligation IDs");
        assert!(error.contains("duplicate obligation IDs"), "{error}");

        let mut duplicate_contracts = TrustContractBundle::empty(
            "bundle-contract-duplicates",
            BundleSubject::Crate { name: "demo".to_string() },
        );
        let contract = TrustContract {
            contract_id: "contract-duplicate".to_string(),
            kind: ContractKind::Ensures,
            predicate: ContractPredicate::TrustExpr { text: "true".to_string() },
            source: SourceLocation::default(),
            metadata: Vec::new(),
        };
        duplicate_contracts.contracts = vec![contract.clone(), contract];
        assert!(duplicate_contracts.validate().is_err());

        let mut duplicate_proof_items = TrustContractBundle::empty(
            "bundle-proof-duplicates",
            BundleSubject::Crate { name: "demo".to_string() },
        );
        let proof_item = TrustProofItem {
            proof_item_id: "proof-duplicate".to_string(),
            name: "proof_duplicate".to_string(),
            kind: ProofItemKind::ProofFn,
            target: ProofItemTarget::LocalNamespace,
            signature: ProofItemSignature::default(),
            body: ProofItemBody::CompilerOwned { body_ref: "mir:proof_duplicate".to_string() },
            source: SourceLocation::default(),
            contracts: Vec::new(),
            metadata: Vec::new(),
        };
        duplicate_proof_items.proof_items = vec![proof_item.clone(), proof_item];
        assert!(duplicate_proof_items.validate().is_err());

        let mut blank =
            TrustContractBundle::empty(" ", BundleSubject::Crate { name: "".to_string() });
        blank.schema_version = "future.schema".to_string();
        let encoded = serde_json::to_vec(&blank).expect("serialize invalid identity bundle");
        assert!(TrustContractBundle::from_json_slice(&encoded).is_err());

        let valid = TrustContractBundle::empty(
            "bundle-oversized",
            BundleSubject::Crate { name: "demo".to_string() },
        );
        let mut value = serde_json::to_value(valid).expect("serialize bundle value");
        value.as_object_mut().expect("bundle object").insert(
            "obligations".to_string(),
            serde_json::Value::Array(vec![serde_json::Value::Null; MAX_VERIFIER_RUN_RECORDS + 1]),
        );
        let error = serde_json::from_value::<TrustContractBundle>(value)
            .expect_err("oversized bundle inventory must fail before element parsing");
        assert!(error.to_string().contains("too many verifier run records"), "{error}");
    }

    #[test]
    fn contract_predicate_payloads_are_bounded_and_typed_at_both_ingress_paths() {
        let make_bundle = |predicate: ContractPredicate| {
            let mut bundle = TrustContractBundle::empty(
                "bundle-predicate-boundary",
                BundleSubject::Function {
                    crate_name: "demo".to_string(),
                    path: "demo::predicate_boundary".to_string(),
                },
            );
            bundle.contracts.push(TrustContract {
                contract_id: "contract-predicate-boundary".to_string(),
                kind: ContractKind::Ensures,
                predicate,
                source: SourceLocation::default(),
                metadata: Vec::new(),
            });
            bundle
        };

        let invalid_width = TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::Eq,
                TrustSpecExpr::bitvec_literal("1", 0),
                TrustSpecExpr::bitvec_literal("1", 0),
            ),
            Vec::new(),
        )
        .into_contract_predicate()
        .expect("invalid typed fixture still serializes");
        let invalid_width_bundle = make_bundle(invalid_width);
        let error = invalid_width_bundle
            .validate()
            .expect_err("zero-width typed predicate must fail programmatic validation");
        assert!(error.contains("bitvector width"), "{error}");
        let encoded = serde_json::to_vec(&invalid_width_bundle).expect("serialize invalid bundle");
        let error = TrustContractBundle::from_json_slice(&encoded)
            .expect_err("zero-width typed predicate must fail deserialization");
        assert!(error.contains("bitvector width"), "{error}");

        let undeclared = TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::Eq,
                TrustSpecExpr::variable("missing", TrustSpecSort::Int),
                TrustSpecExpr::int_literal("0"),
            ),
            Vec::new(),
        )
        .into_contract_predicate()
        .expect("undeclared-variable fixture serializes");
        assert!(make_bundle(undeclared).validate().is_err());

        let mut deep = serde_json::Value::Null;
        for _ in 0..=MAX_CONTRACT_PREDICATE_JSON_DEPTH {
            deep = serde_json::Value::Array(vec![deep]);
        }
        let deep_bundle = make_bundle(ContractPredicate::CanonicalJson {
            schema: "trust.test.deep.v1".to_string(),
            value: deep,
        });
        let error = deep_bundle
            .validate()
            .expect_err("deep programmatic predicate must hit the traversal limit");
        assert!(error.contains("JSON depth limit"), "{error}");

        let invalid_temporal = make_bundle(ContractPredicate::TemporalModelRef {
            uri: "relative model path".to_string(),
            hash: ArtifactHash { algorithm: "SHA256".to_string(), value: "A".repeat(64) },
        });
        assert!(invalid_temporal.validate().is_err());
    }

    #[test]
    fn exact_default_admission_identity_cannot_be_spoofed_by_metadata_presence() {
        let mut exact = obligation_with_id(
            "vc:demo__f:trust_mc_default_function:0",
            ObligationKind::ArithmeticSafety,
        );
        exact.contract_id = None;
        exact.description = TRUST_MC_DEFAULT_FUNCTION_DESCRIPTION.to_string();
        exact.metadata = canonical_default_admission_metadata();
        assert!(exact.is_default_admission());

        let mut bundle = TrustContractBundle::empty(
            "bundle-exact-admission",
            BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
        );
        bundle.obligations.push(exact.clone());
        bundle.validate().expect("exact compiler-shaped admission validates");

        let mut wrong_value = exact.clone();
        wrong_value
            .metadata
            .iter_mut()
            .find(|entry| entry.key == TRUST_MC_DEFAULT_FUNCTION_OBLIGATION_METADATA_KEY)
            .expect("marker exists")
            .value = "enabled".to_string();
        assert!(!wrong_value.is_default_admission());
        let summary =
            VerificationRunSummary::from_parts(std::slice::from_ref(&wrong_value), &[], &[], 0);
        assert_eq!(summary.requested_obligations, 1, "lookalike must not be erased");
        assert_eq!(summary.admitted, 0);
        bundle.obligations = vec![wrong_value];
        assert!(bundle.validate().is_err(), "marker lookalike must fail bundle ingress");

        let mut duplicate = exact.clone();
        duplicate.metadata.push(MetadataEntry {
            key: TRUST_MC_DEFAULT_FUNCTION_OBLIGATION_METADATA_KEY.to_string(),
            value: TRUST_MC_DEFAULT_FUNCTION_OBLIGATION_METADATA_VALUE.to_string(),
        });
        assert!(!duplicate.is_default_admission());
        bundle.obligations = vec![duplicate];
        assert!(bundle.validate().is_err(), "duplicate marker identity must fail ingress");

        let mut real =
            obligation_with_id("vc:demo__f:overflow:0", ObligationKind::ArithmeticSafety);
        real.metadata.push(MetadataEntry {
            key: TRUST_MC_DEFAULT_FUNCTION_OBLIGATION_METADATA_KEY.to_string(),
            value: TRUST_MC_DEFAULT_FUNCTION_OBLIGATION_METADATA_VALUE.to_string(),
        });
        assert!(!real.is_default_admission());
        let real_summary = VerificationRunSummary::from_parts(&[real], &[], &[], 0);
        assert_eq!(real_summary.requested_obligations, 1);
        assert_eq!(real_summary.admitted, 0);
    }

    #[test]
    fn typed_spec_predicate_round_trips_through_contract_predicate() {
        let root = TrustSpecExpr::binary(
            TrustSpecBinaryOp::Eq,
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::Add,
                TrustSpecExpr::int_literal("1"),
                TrustSpecExpr::int_literal("1"),
            ),
            TrustSpecExpr::int_literal("2"),
        );
        let predicate = TrustSpecPredicate::new(root, Vec::new())
            .into_contract_predicate()
            .expect("predicate serializes");

        let ContractPredicate::TrustIr { schema, value } = &predicate else {
            panic!("expected TrustIr predicate");
        };
        assert_eq!(schema, TRUST_SPEC_PREDICATE_SCHEMA_VERSION);
        assert_eq!(
            value,
            &serde_json::json!({
                "schema_version": TRUST_SPEC_PREDICATE_SCHEMA_VERSION,
                "root": {
                    "sort": "bool",
                    "kind": {
                        "node": "binary",
                        "op": "eq",
                        "lhs": {
                            "sort": "int",
                            "kind": {
                                "node": "binary",
                                "op": "add",
                                "lhs": {
                                    "sort": "int",
                                    "kind": {
                                        "node": "int_literal",
                                        "value": "1"
                                    }
                                },
                                "rhs": {
                                    "sort": "int",
                                    "kind": {
                                        "node": "int_literal",
                                        "value": "1"
                                    }
                                }
                            }
                        },
                        "rhs": {
                            "sort": "int",
                            "kind": {
                                "node": "int_literal",
                                "value": "2"
                            }
                        }
                    }
                },
                "root_sort": "bool"
            })
        );

        let decoded = TrustSpecPredicate::from_contract_predicate(&predicate)
            .expect("predicate decodes")
            .expect("typed predicate schema");
        assert!(decoded.has_current_schema());
        assert_eq!(decoded.root_sort, TrustSpecSort::Bool);
    }

    #[test]
    fn typed_spec_predicate_public_validator_rejects_noncanonical_declarations() {
        let variable = TrustSpecVariable {
            name: "x".to_string(),
            sort: TrustSpecSort::Int,
            origin: TrustSpecVariableOrigin::Local { index: 0 },
        };
        let valid = TrustSpecPredicate::new(TrustSpecExpr::bool_literal(true), vec![variable.clone()]);
        valid.validate().expect("canonical typed predicate");

        let duplicate = TrustSpecPredicate::new(
            TrustSpecExpr::bool_literal(true),
            vec![variable.clone(), variable],
        );
        let error = duplicate.validate().expect_err("duplicate declarations must fail closed");
        assert!(error.contains("duplicate variables"), "{error}");
    }

    #[test]
    fn typed_spec_array_select_is_exact_and_bounded() {
        let array_sort = TrustSpecSort::Array { element: TrustSpecScalarSort::Int };
        let array = TrustSpecVariable {
            name: "xs".to_string(),
            sort: array_sort,
            origin: TrustSpecVariableOrigin::Local { index: 0 },
        };
        let selected = TrustSpecExpr::index(
            TrustSpecExpr::variable("xs", array_sort),
            TrustSpecExpr::int_literal("0"),
            TrustSpecSort::Int,
        );
        let predicate = TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::Eq,
                selected,
                TrustSpecExpr::int_literal("42"),
            ),
            vec![array],
        );
        predicate.validate().expect("direct Int-array Select is canonical");

        assert_eq!(
            serde_json::to_value(array_sort).expect("array sort serializes"),
            serde_json::json!({ "array": { "element": "int" } })
        );
        assert_eq!(
            serde_json::to_value(TrustSpecSort::Bool).expect("scalar sort serializes"),
            serde_json::json!("bool"),
            "adding Array must not change existing scalar v1 JSON"
        );
        assert_eq!(
            serde_json::to_value(TrustSpecSort::BitVec { width: 8 })
                .expect("bit-vector sort serializes"),
            serde_json::json!({ "bit_vec": { "width": 8 } }),
            "adding Array must not change existing bit-vector v1 JSON"
        );
    }

    #[test]
    fn typed_spec_array_select_rejects_forged_shapes() {
        let array_sort = TrustSpecSort::Array { element: TrustSpecScalarSort::Int };
        let array = TrustSpecVariable {
            name: "xs".to_string(),
            sort: array_sort,
            origin: TrustSpecVariableOrigin::Local { index: 0 },
        };
        let array_ref = || TrustSpecExpr::variable("xs", array_sort);
        let equality = |selected: TrustSpecExpr| {
            TrustSpecPredicate::new(
                TrustSpecExpr::binary(
                    TrustSpecBinaryOp::Eq,
                    selected,
                    TrustSpecExpr::int_literal("0"),
                ),
                vec![array.clone()],
            )
        };

        let scalar_base = equality(TrustSpecExpr::index(
            TrustSpecExpr::int_literal("1"),
            TrustSpecExpr::int_literal("0"),
            TrustSpecSort::Int,
        ));
        assert!(
            scalar_base.validate().expect_err("scalar base must fail").contains("index base")
        );

        let bool_index = equality(TrustSpecExpr::index(
            array_ref(),
            TrustSpecExpr::bool_literal(false),
            TrustSpecSort::Int,
        ));
        assert!(
            bool_index.validate().expect_err("Bool index must fail").contains("index operand")
        );

        let wrong_result = TrustSpecExpr {
            sort: TrustSpecSort::Bool,
            kind: TrustSpecExprKind::Index {
                base: Box::new(array_ref()),
                index: Box::new(TrustSpecExpr::int_literal("0")),
            },
        };
        let wrong_result = TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::Eq,
                wrong_result,
                TrustSpecExpr::bool_literal(true),
            ),
            vec![array.clone()],
        );
        assert!(
            wrong_result.validate().expect_err("wrong result sort must fail").contains("index result")
        );

        let forged_field_base = TrustSpecExpr::field(
            TrustSpecExpr::int_literal("0"),
            "forged_array",
            array_sort,
        );
        let forged_field = equality(TrustSpecExpr::index(
            forged_field_base,
            TrustSpecExpr::int_literal("0"),
            TrustSpecSort::Int,
        ));
        assert!(
            forged_field
                .validate()
                .expect_err("non-variable array base must fail")
                .contains("direct declared array variable")
        );

        let array_equality = TrustSpecPredicate::new(
            TrustSpecExpr::binary(TrustSpecBinaryOp::Eq, array_ref(), array_ref()),
            vec![array.clone()],
        );
        assert!(
            array_equality.validate().expect_err("array equality must fail").contains("array equality")
        );

        let array_quantifier = TrustSpecPredicate::new(
            TrustSpecExpr::quantifier(
                TrustSpecQuantifier::Forall,
                "a",
                array_sort,
                TrustSpecExpr::bool_literal(true),
            ),
            Vec::new(),
        );
        assert!(
            array_quantifier.validate().expect_err("array binder must fail").contains("bind array")
        );

        let zero_width_array = TrustSpecPredicate::new(
            TrustSpecExpr::bool_literal(true),
            vec![TrustSpecVariable {
                name: "bytes".to_string(),
                sort: TrustSpecSort::Array {
                    element: TrustSpecScalarSort::BitVec { width: 0 },
                },
                origin: TrustSpecVariableOrigin::Local { index: 1 },
            }],
        );
        assert!(
            zero_width_array
                .validate()
                .expect_err("zero-width array element must fail")
                .contains("array element bitvector width")
        );
    }

    #[test]
    fn typed_spec_float_comparisons_validate_and_round_trip() {
        let f64_sort = TrustSpecSort::Float { eb: 11, sb: 53 };
        let f32_sort = TrustSpecSort::Float { eb: 8, sb: 24 };
        let x_var = |sort| TrustSpecExpr::variable("x", sort);
        let x_decl = |sort| TrustSpecVariable {
            name: "x".to_string(),
            sort,
            origin: TrustSpecVariableOrigin::Local { index: 1 },
        };

        // The production contract shape: `x >= -1.0e30 && x <= 1.0e30` on f64.
        let range = TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::And,
                TrustSpecExpr::binary(
                    TrustSpecBinaryOp::Ge,
                    x_var(f64_sort),
                    TrustSpecExpr::float_literal((-1.0e30_f64).to_bits(), 11, 53),
                ),
                TrustSpecExpr::binary(
                    TrustSpecBinaryOp::Le,
                    x_var(f64_sort),
                    TrustSpecExpr::float_literal(1.0e30_f64.to_bits(), 11, 53),
                ),
            ),
            vec![x_decl(f64_sort)],
        );
        range.validate().expect("f64 range comparison contract is canonical");

        // f32 comparisons against f32 literals type as well.
        let f32_compare = TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::Lt,
                x_var(f32_sort),
                TrustSpecExpr::float_literal(u64::from(2.5_f32.to_bits()), 8, 24),
            ),
            vec![x_decl(f32_sort)],
        );
        f32_compare.validate().expect("f32 comparison contract is canonical");

        // Equality on one float sort is the IEEE `fp.eq` denotation; a NaN
        // literal (arbitrary payload) is representational — bits are bits —
        // and must survive the wire round-trip exactly, never through a
        // decimal re-parse.
        let nan_bits = f64::NAN.to_bits() | 0xdead;
        let nan_equality = TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::Eq,
                x_var(f64_sort),
                TrustSpecExpr::float_literal(nan_bits, 11, 53),
            ),
            vec![x_decl(f64_sort)],
        );
        nan_equality.validate().expect("NaN payloads are representational");
        let wire = nan_equality
            .clone()
            .into_contract_predicate()
            .expect("float predicate serializes");
        let decoded = TrustSpecPredicate::from_contract_predicate(&wire)
            .expect("float predicate decodes")
            .expect("typed predicate schema");
        assert_eq!(decoded, nan_equality, "exact bits round-trip");
        assert!(
            decoded.has_current_schema(),
            "the float fragment is additive v1 — no schema bump (BitVec/Array precedent)"
        );

        // Additive JSON: existing scalar v1 encodings are byte-identical and
        // the float sort serializes as a new externally-tagged arm.
        assert_eq!(
            serde_json::to_value(TrustSpecSort::Bool).expect("scalar sort serializes"),
            serde_json::json!("bool"),
            "adding Float must not change existing scalar v1 JSON"
        );
        assert_eq!(
            serde_json::to_value(f64_sort).expect("float sort serializes"),
            serde_json::json!({ "float": { "eb": 11, "sb": 53 } })
        );

        // `from_contract_predicate` tolerance: unrelated schemas decode None.
        let foreign = ContractPredicate::CanonicalJson {
            schema: "trust.spec-predicate.v2-float-experimental".to_string(),
            value: serde_json::json!({ "anything": true }),
        };
        assert_eq!(
            TrustSpecPredicate::from_contract_predicate(&foreign).expect("tolerant decode"),
            None
        );
    }

    #[test]
    fn typed_spec_float_fragment_rejects_forged_shapes() {
        let f64_sort = TrustSpecSort::Float { eb: 11, sb: 53 };
        let f32_sort = TrustSpecSort::Float { eb: 8, sb: 24 };
        let x_decl = TrustSpecVariable {
            name: "x".to_string(),
            sort: f64_sort,
            origin: TrustSpecVariableOrigin::Local { index: 1 },
        };
        let x_var = || TrustSpecExpr::variable("x", f64_sort);
        let f64_lit = || TrustSpecExpr::float_literal(1.0_f64.to_bits(), 11, 53);

        // Mixed-format comparison: f64 variable against an f32 literal.
        let mixed = TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::Ge,
                x_var(),
                TrustSpecExpr::float_literal(u64::from(1.0_f32.to_bits()), 8, 24),
            ),
            vec![x_decl.clone()],
        );
        assert!(
            mixed.validate().expect_err("mixed float formats must fail").contains("binary lhs"),
        );

        // Mixed-format equality.
        let mixed_eq = TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::Eq,
                x_var(),
                TrustSpecExpr::float_literal(u64::from(1.0_f32.to_bits()), 8, 24),
            ),
            vec![x_decl.clone()],
        );
        assert!(
            mixed_eq
                .validate()
                .expect_err("mixed float equality must fail")
                .contains("different sorts"),
        );

        // Float arithmetic: rounding-mode semantics are not carried, so
        // `Add` (and every other arithmetic operator) stays Int-only.
        let float_add = TrustSpecExpr {
            sort: f64_sort,
            kind: TrustSpecExprKind::Binary {
                op: TrustSpecBinaryOp::Add,
                lhs: Box::new(x_var()),
                rhs: Box::new(f64_lit()),
            },
        };
        let arithmetic = TrustSpecPredicate::new(
            TrustSpecExpr::binary(TrustSpecBinaryOp::Eq, float_add, f64_lit()),
            vec![x_decl.clone()],
        );
        assert!(
            arithmetic
                .validate()
                .expect_err("float arithmetic must fail closed")
                .contains("binary"),
        );

        // Float negation is arithmetic too (`Neg` is Int-only).
        let negated = TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::Eq,
                TrustSpecExpr::unary(TrustSpecUnaryOp::Neg, x_var()),
                TrustSpecExpr::int_literal("0"),
            ),
            vec![x_decl.clone()],
        );
        assert!(
            negated
                .validate()
                .expect_err("float negation must fail closed")
                .contains("unary operand"),
        );

        // Only the two Rust machine shapes are valid float sorts.
        let bad_shape = TrustSpecPredicate::new(
            TrustSpecExpr::bool_literal(true),
            vec![TrustSpecVariable {
                name: "q".to_string(),
                sort: TrustSpecSort::Float { eb: 15, sb: 113 },
                origin: TrustSpecVariableOrigin::Local { index: 1 },
            }],
        );
        assert!(
            bad_shape
                .validate()
                .expect_err("binary128 shape must fail")
                .contains("not IEEE-754 binary32 or binary64"),
        );

        // Literal bits must fit the declared format exactly.
        let oversized_f32 = TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::Eq,
                TrustSpecExpr::variable("y", f32_sort),
                TrustSpecExpr::float_literal(1_u64 << 40, 8, 24),
            ),
            vec![TrustSpecVariable {
                name: "y".to_string(),
                sort: f32_sort,
                origin: TrustSpecVariableOrigin::Local { index: 1 },
            }],
        );
        assert!(
            oversized_f32
                .validate()
                .expect_err("bits beyond binary32 must fail")
                .contains("exceed the 32-bit format"),
        );

        // Quantified float domains are outside the fragment.
        let float_binder = TrustSpecPredicate::new(
            TrustSpecExpr::quantifier(
                TrustSpecQuantifier::Forall,
                "a",
                f64_sort,
                TrustSpecExpr::bool_literal(true),
            ),
            Vec::new(),
        );
        assert!(
            float_binder
                .validate()
                .expect_err("float binder must fail")
                .contains("bind float"),
        );
    }

    #[test]
    fn typed_spec_array_sort_json_rejects_malformed_v1_shapes() {
        for malformed in [
            serde_json::json!({ "array": {} }),
            serde_json::json!({ "array": { "element": "int", "index": "int" } }),
            serde_json::json!({
                "array": { "element": { "array": { "element": "int" } } }
            }),
            serde_json::json!({ "array": { "element": { "bit_vec": { "width": 8, "signed": false } } } }),
        ] {
            assert!(
                serde_json::from_value::<TrustSpecSort>(malformed).is_err(),
                "malformed/expanded v1 Array shape must fail closed"
            );
        }
    }

    #[test]
    fn obligation_context_round_trips_through_metadata_entry() {
        let context = ObligationContext::new(
            ObligationProducer::CompilerMirExtract,
            ObligationOrigin::Contract {
                contract_id: "contract:demo:f:requires:0".to_string(),
                contract_kind: ContractKind::Requires,
                contract_index: 0,
                predicate_schema: Some(TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string()),
            },
        )
        .with_function(FunctionContext {
            crate_name: "demo".to_string(),
            path: "demo::f".to_string(),
        });

        let metadata = context.to_metadata_entry().expect("context serializes");

        assert_eq!(metadata.key, OBLIGATION_CONTEXT_METADATA_KEY);
        let decoded = ObligationContext::from_metadata_entry(&metadata)
            .expect("context decodes")
            .expect("context metadata key");
        assert!(decoded.has_current_schema());
        assert_eq!(decoded, context);
    }

    #[test]
    fn proof_items_make_bundle_non_empty_without_proc_macro_shape() {
        let mut bundle = TrustContractBundle::empty(
            "bundle-proof",
            BundleSubject::Function {
                crate_name: "demo".to_string(),
                path: "demo::sorted_insert_preserves_sorted".to_string(),
            },
        );
        bundle.proof_items.push(TrustProofItem {
            proof_item_id: "proof:demo::sorted_insert_preserves_sorted".to_string(),
            name: "sorted_insert_preserves_sorted".to_string(),
            kind: ProofItemKind::ProofFn,
            target: ProofItemTarget::Function {
                crate_name: "demo".to_string(),
                path: "demo::SortedVec::insert".to_string(),
            },
            signature: ProofItemSignature {
                params: vec![ProofItemParam {
                    name: Some("pos".to_string()),
                    ty: "usize".to_string(),
                }],
                output: None,
            },
            body: ProofItemBody::CompilerOwned {
                body_ref: "hir-body:demo::sorted_insert_preserves_sorted".to_string(),
            },
            source: SourceLocation::default(),
            contracts: Vec::new(),
            metadata: vec![MetadataEntry {
                key: "trust.proof_item.syntax".to_string(),
                value: "proof fn".to_string(),
            }],
        });
        bundle.obligations.push(TrustObligation {
            obligation_id: "proof-obligation-1".to_string(),
            kind: ObligationKind::Custom {
                namespace: "trust.proof_item".to_string(),
                name: "lemma_validity".to_string(),
            },
            contract_id: None,
            proof_item_id: Some("proof:demo::sorted_insert_preserves_sorted".to_string()),
            source: SourceLocation::default(),
            description: "verify native proof fn body".to_string(),
            required_strength: Some(ProofStrength::certified(ReasoningKind::ProofCalculus)),
            summary_facts: Vec::new(),
            metadata: Vec::new(),
        });

        assert!(!bundle.is_empty());
        assert!(bundle.proof_items[0].is_runtime_erased());

        let json = serde_json::to_string(&bundle).expect("serialize proof bundle");
        assert!(json.contains("proof_items"));
        assert!(!json.contains("proc_macro"));
        let decoded: TrustContractBundle =
            serde_json::from_str(&json).expect("deserialize proof bundle");
        assert_eq!(decoded, bundle);
    }

    #[test]
    fn support_level_distinguishes_attemptable_obligations() {
        assert!(
            SupportLevel::Experimental { reason: "partial lowering".to_string() }.is_supported()
        );
        assert!(SupportLevel::Preferred.is_supported());
        assert!(!SupportLevel::Unsupported { reason: "temporal".to_string() }.is_supported());
    }

    #[test]
    fn bounded_strength_stays_bounded() {
        let bounded = ProofStrength::bounded(32);
        assert!(bounded.is_bounded());
        assert_ne!(bounded.assurance, AssuranceLevel::Certified);

        let certified = ProofStrength::certified(ReasoningKind::Constructive);
        assert!(!certified.is_bounded());
        assert_eq!(certified.assurance, AssuranceLevel::Certified);
    }

    #[test]
    fn proof_artifact_policy_requires_exact_certificate_or_bound_dag() {
        let engine = EngineManifest::new("unit-engine", "0.1.0", EngineKind::Deductive);
        let mut checked = evidence(
            &engine,
            "ev-checked",
            "obl-1",
            EvidenceStatus::Proved,
            Some(ProofStrength::deductive()),
            proof_dag_artifacts("obl-1", "dag-proof"),
        );
        assert!(checked.satisfies_required_strength(None));

        let pdr = evidence(
            &engine,
            "ev-pdr",
            "obl-1",
            EvidenceStatus::Proved,
            Some(ProofStrength::deductive()),
            pdr_proof_dag_artifacts("obl-1", "pdr-proof"),
        );
        assert!(
            pdr.satisfies_required_strength(None),
            "an exact PDR DAG must retain its proof-critical invariant model"
        );

        let mut missing_model_replay_edge = pdr.clone();
        let transcript = missing_model_replay_edge
            .artifacts
            .iter()
            .find(|artifact| artifact.kind == EvidenceArtifactKind::SolverTranscript)
            .expect("PDR transcript")
            .clone();
        let model = missing_model_replay_edge
            .artifacts
            .iter()
            .find(|artifact| artifact.kind == EvidenceArtifactKind::Model)
            .expect("PDR invariant model")
            .clone();
        let replay_index = missing_model_replay_edge
            .artifacts
            .iter()
            .position(|artifact| artifact.kind == EvidenceArtifactKind::ReplayLog)
            .expect("PDR replay");
        let replay = bound_artifact(
            EvidenceArtifactKind::ReplayLog,
            "obl-1",
            "pdr-proof",
            b"replay that omits the PDR invariant model",
            vec![EvidenceArtifactReference {
                kind: transcript.kind,
                hash: transcript.hash.clone(),
            }],
        );
        missing_model_replay_edge.artifacts[replay_index] = replay.clone();
        let check_index = missing_model_replay_edge
            .artifacts
            .iter()
            .position(|artifact| artifact.kind == EvidenceArtifactKind::ProofCheckReport)
            .expect("PDR check");
        missing_model_replay_edge.artifacts[check_index] = bound_artifact(
            EvidenceArtifactKind::ProofCheckReport,
            "obl-1",
            "pdr-proof",
            b"check over the mutated PDR replay",
            vec![
                EvidenceArtifactReference {
                    kind: transcript.kind,
                    hash: transcript.hash.clone(),
                },
                EvidenceArtifactReference { kind: replay.kind, hash: replay.hash.clone() },
                EvidenceArtifactReference { kind: model.kind, hash: model.hash.clone() },
            ],
        );
        assert!(
            !missing_model_replay_edge.satisfies_required_strength(None),
            "a PDR replay that omits its proof-critical model must fail closed"
        );

        checked.artifacts.clear();
        assert!(checked.satisfies_strength_requirement(None));
        assert!(!checked.satisfies_required_strength(None));

        let digest_only = evidence(
            &engine,
            "ev-digest-only",
            "obl-1",
            EvidenceStatus::Proved,
            Some(ProofStrength::smt_unsat()),
            vec![artifact(
                EvidenceArtifactKind::SolverTranscript,
                "artifact://solver-transcript.json",
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
            )],
        );
        assert!(!digest_only.satisfies_required_strength(None));

        let certificate = evidence(
            &engine,
            "ev-certificate",
            "obl-1",
            EvidenceStatus::Proved,
            Some(ProofStrength::deductive()),
            vec![certificate_artifact("obl-1", "certificate-proof")],
        );
        assert!(certificate.satisfies_required_strength(None));

        let mut owner_transplant = certificate.clone();
        owner_transplant.obligation_id = "obl-2".to_string();
        assert!(!owner_transplant.satisfies_required_strength(None));

        let mut duplicate = certificate.clone();
        duplicate.artifacts.push(duplicate.artifacts[0].clone());
        assert!(!duplicate.satisfies_required_strength(None));

        let mut mixed = certificate.clone();
        mixed.artifacts.extend(proof_dag_artifacts("obl-1", "certificate-proof"));
        assert!(!mixed.satisfies_required_strength(None));

        let mut role_relabel = evidence(
            &engine,
            "ev-role-relabel",
            "obl-1",
            EvidenceStatus::Proved,
            Some(ProofStrength::deductive()),
            proof_dag_artifacts("obl-1", "role-proof"),
        );
        role_relabel.artifacts[1].kind = EvidenceArtifactKind::ReplayLog;
        assert!(!role_relabel.satisfies_required_strength(None));

        let mut dangling_reference = evidence(
            &engine,
            "ev-dangling-reference",
            "obl-1",
            EvidenceStatus::Proved,
            Some(ProofStrength::deductive()),
            proof_dag_artifacts("obl-1", "dangling-proof"),
        );
        dangling_reference.artifacts[1] = bound_artifact(
            EvidenceArtifactKind::SolverTranscript,
            "obl-1",
            "dangling-proof",
            b"exact solver transcript",
            vec![EvidenceArtifactReference {
                kind: EvidenceArtifactKind::NormalizedObligation,
                hash: ArtifactHash { algorithm: "sha256".to_string(), value: "0".repeat(64) },
            }],
        );
        assert!(!dangling_reference.satisfies_required_strength(None));

        let transcript_without_input = bound_artifact(
            EvidenceArtifactKind::SolverTranscript,
            "obl-1",
            "inputless-proof",
            b"inputless solver transcript",
            Vec::new(),
        );
        let inputless_check = bound_artifact(
            EvidenceArtifactKind::ProofCheckReport,
            "obl-1",
            "inputless-proof",
            b"inputless proof check",
            vec![EvidenceArtifactReference {
                kind: transcript_without_input.kind,
                hash: transcript_without_input.hash.clone(),
            }],
        );
        let inputless_dag = evidence(
            &engine,
            "ev-inputless-dag",
            "obl-1",
            EvidenceStatus::Proved,
            Some(ProofStrength::deductive()),
            vec![transcript_without_input, inputless_check],
        );
        assert!(
            !inputless_dag.satisfies_required_strength(None),
            "a transcript/check pair without an exact structural input must fail closed"
        );

        let mut unreferenced_extra = evidence(
            &engine,
            "ev-extra",
            "obl-1",
            EvidenceStatus::Proved,
            Some(ProofStrength::deductive()),
            proof_dag_artifacts("obl-1", "extra-proof"),
        );
        unreferenced_extra.artifacts.push(bound_artifact(
            EvidenceArtifactKind::Report,
            "obl-1",
            "extra-proof",
            b"unreferenced materialized extra",
            Vec::new(),
        ));
        assert!(!unreferenced_extra.satisfies_required_strength(None));
    }

    #[test]
    fn obligation_evidence_artifact_count_is_bounded_at_serde_and_policy_boundaries() {
        let engine = EngineManifest::new("unit-engine", "0.1.0", EngineKind::Deductive);
        let mut at_limit = evidence(
            &engine,
            "ev-artifact-limit",
            "obl-1",
            EvidenceStatus::Proved,
            Some(ProofStrength::deductive()),
            vec![certificate_artifact("obl-1", "certificate-proof")],
        );
        for index in 0..(MAX_EVIDENCE_ARTIFACTS_PER_OBLIGATION - 1) {
            at_limit.artifacts.push(artifact(
                EvidenceArtifactKind::Report,
                &format!("artifact://supplemental/{index}"),
                &format!("{index:064x}"),
            ));
        }
        assert_eq!(at_limit.artifacts.len(), MAX_EVIDENCE_ARTIFACTS_PER_OBLIGATION);
        assert!(
            at_limit.satisfies_proof_artifact_policy(),
            "the exact collection limit must preserve an otherwise valid certificate route"
        );
        let exact_json = serde_json::to_string(&at_limit).expect("serialize exact-limit evidence");
        let exact_round_trip: ObligationEvidence =
            serde_json::from_str(&exact_json).expect("deserialize exact-limit evidence");
        assert_eq!(exact_round_trip.artifacts.len(), MAX_EVIDENCE_ARTIFACTS_PER_OBLIGATION);

        let mut over_limit = at_limit;
        over_limit.artifacts.push(artifact(
            EvidenceArtifactKind::Report,
            "artifact://supplemental/overflow",
            &"f".repeat(64),
        ));
        assert!(
            !over_limit.satisfies_proof_artifact_policy(),
            "programmatically constructed evidence must obey the same work limit"
        );
        let over_json = serde_json::to_string(&over_limit).expect("serialize over-limit evidence");
        let error = serde_json::from_str::<ObligationEvidence>(&over_json)
            .expect_err("over-limit external evidence must fail during deserialization");
        assert!(error.to_string().contains("too many evidence artifacts"), "{error}");
    }

    #[test]
    fn engine_trait_returns_per_obligation_evidence_with_publication_hashes() {
        let engine = AlwaysProves::new();
        let mut bundle = TrustContractBundle::empty(
            "bundle-1",
            BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
        );
        bundle.publication.dpub_plan_hash = Some("sha256:plan".to_string());
        bundle.publication.trust_engines_lock_hash = Some("sha256:lock".to_string());
        bundle.obligations.push(obligation(ObligationKind::Postcondition));

        let evidence = engine.verify(&bundle, &bundle.obligations);

        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].engine.name, "unit-engine");
        assert_eq!(evidence[0].publication.publication_plan_hash.as_deref(), Some("sha256:plan"));
        assert_eq!(evidence[0].publication.trust_engines_lock_hash.as_deref(), Some("sha256:lock"));
        assert!(evidence[0].is_unbounded_proof());
    }

    #[test]
    fn wall_time_limit_installs_runtime_deadline_without_snapshot_deadline() {
        let context = VerifierExecutionContext::new("run-wall-time")
            .with_limits(VerifierResourceLimits::unlimited().with_wall_time_ms(0));

        assert_eq!(context.limits.wall_time_ms, Some(0));
        assert!(context.deadline().is_some());
        assert!(context.budget_exceeded());

        let cloned = context.clone();
        assert_eq!(cloned.deadline(), context.deadline());
        assert!(cloned.budget_exceeded());

        let snapshot = context.snapshot();
        assert_eq!(snapshot.limits.wall_time_ms, Some(0));

        let json = serde_json::to_value(&snapshot).expect("snapshot serializes");
        assert!(json.get("deadline").is_none());
        assert_eq!(json["limits"]["wall_time_ms"].as_u64(), Some(0));
    }

    #[test]
    fn wall_time_limit_does_not_extend_existing_runtime_deadline() {
        let elapsed_deadline =
            Instant::now().checked_sub(Duration::from_millis(1)).unwrap_or_else(Instant::now);
        let context = VerifierExecutionContext::new("run-existing-deadline")
            .with_deadline(elapsed_deadline)
            .with_limits(VerifierResourceLimits::unlimited().with_wall_time_ms(60_000));

        assert_eq!(context.deadline(), Some(elapsed_deadline));
        assert!(context.budget_exceeded());
        assert_eq!(context.snapshot().limits.wall_time_ms, Some(60_000));
    }

    #[test]
    fn resource_limits_and_cancellation_snapshot_are_first_class() {
        let limits = VerifierResourceLimits::unlimited()
            .with_wall_time_ms(5_000)
            .with_memory_bytes(256 * 1024 * 1024)
            .with_solver_query_limit(10_000)
            .with_obligation_limit(128);
        assert!(limits.has_any_limit());

        let context = VerifierExecutionContext::new("run-1")
            .with_invocation(VerifierInvocation::DscanPreflight)
            .with_limits(limits.clone());
        context.cancellation.cancel(CancellationReason::ResourceLimitExceeded {
            limit: ResourceLimitKind::WallTime,
        });

        let snapshot = context.snapshot();

        assert_eq!(snapshot.run_id, "run-1");
        assert_eq!(snapshot.invocation, VerifierInvocation::DscanPreflight);
        assert_eq!(snapshot.limits, limits);
        assert_eq!(snapshot.limits.obligation_limit, Some(128));
        assert!(snapshot.cancellation.requested);
        assert_eq!(
            snapshot.cancellation.reason,
            Some(CancellationReason::ResourceLimitExceeded { limit: ResourceLimitKind::WallTime })
        );
    }

    #[test]
    fn context_aware_default_trait_method_wraps_results() {
        let engine = AlwaysProves::new();
        let mut bundle = TrustContractBundle::empty(
            "bundle-1",
            BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
        );
        bundle.publication.dpub_plan_hash = Some("sha256:plan".to_string());
        bundle.publication.trust_engines_lock_hash = Some("sha256:lock".to_string());
        bundle.obligations.push(obligation(ObligationKind::Postcondition));
        let context = VerifierExecutionContext::new("run-2")
            .with_invocation(VerifierInvocation::NativeTrustPipeline);

        let result = engine.verify_with_context(&bundle, &bundle.obligations, &context);

        assert_eq!(result.status, VerificationRunStatus::Proved);
        assert!(result.is_fully_proved());
        assert_eq!(result.run_id, "run-2");
        assert_eq!(result.summary.requested_obligations, 1);
        assert_eq!(result.summary.proved, 1);
        assert_eq!(result.publication.publication_plan_hash.as_deref(), Some("sha256:plan"));
        assert_eq!(result.publication.trust_engines_lock_hash.as_deref(), Some("sha256:lock"));
        assert!(result.skipped.is_empty());
    }

    #[test]
    fn context_aware_trait_rejects_obligations_outside_the_canonical_bundle() {
        let engine = AlwaysProves::new();
        let mut bundle = TrustContractBundle::empty(
            "bundle-request-binding",
            BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
        );
        bundle
            .obligations
            .push(obligation_with_id("canonical-obligation", ObligationKind::Postcondition));
        let mut substituted = bundle.obligations.clone();
        substituted[0].kind = ObligationKind::Precondition;

        let error = bundle
            .validate_requested_obligations(&substituted)
            .expect_err("ID-preserving record substitution must fail");
        assert!(error.contains("differs from its canonical bundle record"), "{error}");
        assert!(
            engine.verify(&bundle, &substituted).is_empty(),
            "the context-free trait wrapper must reject the substituted record before dispatch"
        );

        let result = engine.verify_with_context(
            &bundle,
            &substituted,
            &VerifierExecutionContext::new("run-request-binding"),
        );
        assert_ne!(result.status, VerificationRunStatus::Proved);
        assert!(result.evidence.is_empty());
        assert!(result.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("rejected non-canonical obligation request")
                && diagnostic.contains("differs from its canonical bundle record")
        }));
    }

    #[test]
    fn cancelled_context_skips_without_calling_legacy_verify() {
        let engine = AlwaysProves::new();
        let mut bundle = TrustContractBundle::empty(
            "bundle-1",
            BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
        );
        bundle.obligations.push(obligation(ObligationKind::Postcondition));
        let context = VerifierExecutionContext::new("run-cancelled");
        context.cancellation.cancel(CancellationReason::UserRequested);

        let result = engine.verify_with_context(&bundle, &bundle.obligations, &context);

        assert_eq!(result.status, VerificationRunStatus::Canceled);
        assert!(result.evidence.is_empty());
        assert_eq!(result.skipped.len(), 1);
        assert_eq!(result.summary.cancelled, 1);
        assert_eq!(
            result.skipped[0].reason,
            SkipReason::Canceled { reason: Some(CancellationReason::UserRequested) }
        );
    }

    #[test]
    fn memory_guard_resource_skip_is_release_blocking_proof_gap_in_manifest() {
        let engine = AlwaysProves::new();
        let mut bundle = TrustContractBundle::empty(
            "bundle-1",
            BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
        );
        bundle.obligations.push(obligation(ObligationKind::MemorySafety));
        let context = VerifierExecutionContext::new("run-memory-guard");
        context
            .cancellation
            .cancel(CancellationReason::ResourceLimitExceeded { limit: ResourceLimitKind::Memory });

        let result = engine.verify_with_context(&bundle, &bundle.obligations, &context);
        let manifest = result.to_manifest();

        assert_eq!(result.status, VerificationRunStatus::Inconclusive);
        assert_eq!(result.summary.skipped, 1);
        assert_eq!(result.summary.cancelled, 0);
        assert!(matches!(
            &result.skipped[0].reason,
            SkipReason::ResourceLimit { limit: ResourceLimitKind::Memory, detail: Some(detail) }
                if detail.contains("memory guard skipped solver dispatch")
        ));
        assert!(result.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("release-blocking proof gap")
                && diagnostic.contains("memory guard skipped solver dispatch")
        }));
        assert!(manifest.obligations[0].skipped);
        assert!(matches!(
            &manifest.skipped[0].reason,
            SkipReason::ResourceLimit { limit: ResourceLimitKind::Memory, detail: Some(detail) }
                if detail.contains("memory guard skipped solver dispatch")
        ));
        assert!(manifest.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("release-blocking proof gap")
                && diagnostic.contains("memory guard skipped solver dispatch")
        }));
    }

    #[test]
    fn cancellation_during_legacy_verify_is_reflected_in_result() {
        let context = VerifierExecutionContext::new("run-cancel-race");
        let engine = CancelsDuringVerify::new(context.cancellation.clone());
        let mut bundle = TrustContractBundle::empty(
            "bundle-1",
            BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
        );
        bundle.obligations.push(obligation(ObligationKind::Postcondition));

        let result = engine.verify_with_context(&bundle, &bundle.obligations, &context);

        assert_eq!(result.status, VerificationRunStatus::Canceled);
        assert!(result.context.cancellation.requested);
        assert_eq!(result.summary.cancelled, 1);
        assert_eq!(
            result.skipped[0].reason,
            SkipReason::Canceled { reason: Some(CancellationReason::DeadlineExceeded) }
        );
    }

    #[test]
    fn bounded_proof_does_not_make_run_fully_proved() {
        let mut bundle = TrustContractBundle::empty(
            "bundle-1",
            BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
        );
        bundle.obligations.push(obligation(ObligationKind::Postcondition));
        let context = VerifierExecutionContext::new("run-bounded").snapshot();
        let evidence = vec![ObligationEvidence {
            evidence_id: "ev-bounded".to_string(),
            obligation_id: "obl-1".to_string(),
            engine: EngineManifest::new("trust-mc", "0.1.0", EngineKind::Reachability),
            status: EvidenceStatus::Proved,
            decline: None,
            proof_strength: Some(ProofStrength::bounded(16)),
            artifacts: Vec::new(),
            counterexample: None,
            publication: EvidencePublicationMetadata::default(),
            diagnostics: Vec::new(),
        }];

        let result = VerificationRunResult::from_evidence(
            context,
            &bundle,
            EngineManifest::new("trust-mc", "0.1.0", EngineKind::Reachability),
            &bundle.obligations,
            evidence,
        );

        assert_eq!(result.summary.proved, 0);
        assert_eq!(result.summary.bounded_proved, 1);
        assert_eq!(result.status, VerificationRunStatus::Inconclusive);
        assert!(!result.is_fully_proved());
    }

    /// SOUNDNESS: the decline taxonomy's default must be TERMINAL.
    ///
    /// `DeclineClass` exists so a future fallback can retry a pure capability
    /// gap without re-litigating a decline that was actually a refusal. The
    /// whole design rests on the default being non-retryable: every engine that
    /// has not been taught the distinction, every older wire payload, and every
    /// decline the router itself mints arrive as `None`.
    ///
    /// Written as a positive match on purpose. `SupportLevel::is_supported` is
    /// `!matches!(self, Self::Unsupported { .. })` over a `#[non_exhaustive]`
    /// enum, so a variant added there silently becomes *attemptable*. Here a
    /// variant added without updating `is_retryable` stays *terminal*, which is
    /// the safe direction.
    #[test]
    fn decline_class_default_is_terminal_and_only_capability_retries() {
        assert!(!DeclineClass::is_retryable(None), "an unclassified decline must never be retried");
        assert!(DeclineClass::is_retryable(Some(DeclineClass::Capability)));
    }

    /// An older payload with no `decline` field must deserialize to the terminal
    /// default, and a row carrying no class must serialize without the key so
    /// today's bytes are unchanged.
    #[test]
    fn decline_is_wire_additive_and_absent_means_terminal() {
        let legacy = serde_json::json!({
            "evidence_id": "ev-legacy",
            "obligation_id": "obl-1",
            "engine": {
                "name": "unit-engine",
                "version": "0.1.0",
                "kind": "Deductive",
                "api_version": API_VERSION,
            },
            "status": "Unsupported",
            "publication": {},
        });
        let restored: ObligationEvidence =
            serde_json::from_value(legacy).expect("legacy payload without `decline` deserializes");
        assert_eq!(restored.decline, None, "absent means terminal");
        assert!(!DeclineClass::is_retryable(restored.decline));

        let json = serde_json::to_value(&restored).expect("serialize");
        assert!(
            json.get("decline").is_none(),
            "a row with no decline class must not emit the key, so existing bytes are unchanged"
        );
    }

    /// SOUNDNESS WITNESS: duplicate proved rows on one obligation must not pay
    /// for another obligation that was never proved.
    ///
    /// `from_summary` accepts a run when `proved == requested_obligations`. If
    /// `proved` counted evidence ROWS, two publication-grade rows for the same
    /// obligation would satisfy that equality for a two-obligation bundle while
    /// the second obligation held only a bounded row — and a bounded row
    /// increments neither `proved` nor, formerly, any blocking counter. The run
    /// would report `Proved` with the second obligation proved by nobody.
    ///
    /// Two independent guards must both hold: `proved` deduplicates by
    /// obligation, and `bounded_proved` blocks. Nothing emits two rows per
    /// obligation today; a multi-engine fallback would be the first mechanism
    /// that does, which is why this guard precedes it.
    #[test]
    fn duplicate_proved_rows_cannot_pay_for_an_unproved_obligation() {
        let base = fully_proved_result(VerifierInvocation::NativeTrustPipeline);
        assert_eq!(base.status, VerificationRunStatus::Proved, "baseline is a real proof");

        let mut forged = base.clone();
        // A SECOND, distinct obligation that only ever gets a bounded row.
        let second = obligation_with_id("obl-bounded", ObligationKind::Postcondition);
        forged.requested_obligations.push(second.clone());
        let mut bounded = forged.evidence[0].clone();
        bounded.evidence_id = "ev-bounded".to_string();
        bounded.obligation_id = second.obligation_id.clone();
        bounded.proof_strength = Some(ProofStrength::bounded(16));
        forged.evidence.push(bounded);
        // A duplicate publication-grade row for the FIRST obligation, which under
        // row-counting would supply the missing `proved`.
        let mut duplicate = forged.evidence[0].clone();
        duplicate.evidence_id = "ev-duplicate".to_string();
        forged.evidence.push(duplicate);

        let forged = forged.canonicalized_derived_state();

        assert_eq!(
            forged.summary.requested_obligations, 2,
            "two distinct obligations were requested"
        );
        assert_eq!(
            forged.summary.proved, 1,
            "proved must count distinct obligations, not evidence rows"
        );
        assert_eq!(forged.summary.bounded_proved, 1);
        assert_eq!(
            forged.status,
            VerificationRunStatus::Inconclusive,
            "an obligation with only a bounded row must never be absorbed into a Proved run"
        );
        assert!(!forged.is_fully_proved());
    }

    #[test]
    fn weak_assurance_does_not_make_run_fully_proved() {
        let mut bundle = TrustContractBundle::empty(
            "bundle-1",
            BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
        );
        bundle.obligations.push(obligation(ObligationKind::Postcondition));
        let context = VerifierExecutionContext::new("run-weak").snapshot();
        let evidence = vec![ObligationEvidence {
            evidence_id: "ev-weak".to_string(),
            obligation_id: "obl-1".to_string(),
            engine: EngineManifest::new("heuristic", "0.1.0", EngineKind::Composite),
            status: EvidenceStatus::Proved,
            decline: None,
            proof_strength: Some(ProofStrength {
                reasoning: ReasoningKind::AbstractInterpretation,
                assurance: AssuranceLevel::Heuristic,
            }),
            artifacts: Vec::new(),
            counterexample: None,
            publication: EvidencePublicationMetadata::default(),
            diagnostics: Vec::new(),
        }];

        let result = VerificationRunResult::from_evidence(
            context,
            &bundle,
            EngineManifest::new("heuristic", "0.1.0", EngineKind::Composite),
            &bundle.obligations,
            evidence,
        );

        assert_eq!(result.summary.proved, 0);
        assert_eq!(result.summary.insufficient_strength, 1);
        assert_eq!(result.status, VerificationRunStatus::Inconclusive);
    }

    #[test]
    fn required_certified_strength_rejects_weaker_sound_proof() {
        let mut required = obligation(ObligationKind::Postcondition);
        required.required_strength = Some(ProofStrength::certified(ReasoningKind::ProofCalculus));
        let mut bundle = TrustContractBundle::empty(
            "bundle-1",
            BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
        );
        bundle.obligations.push(required);
        let context = VerifierExecutionContext::new("run-required").snapshot();
        let evidence = vec![ObligationEvidence {
            evidence_id: "ev-sound".to_string(),
            obligation_id: "obl-1".to_string(),
            engine: EngineManifest::new("trust-wp", "0.1.0", EngineKind::Deductive),
            status: EvidenceStatus::Proved,
            decline: None,
            proof_strength: Some(ProofStrength::deductive()),
            artifacts: Vec::new(),
            counterexample: None,
            publication: EvidencePublicationMetadata::default(),
            diagnostics: Vec::new(),
        }];

        let result = VerificationRunResult::from_evidence(
            context,
            &bundle,
            EngineManifest::new("trust-wp", "0.1.0", EngineKind::Deductive),
            &bundle.obligations,
            evidence,
        );

        assert_eq!(result.summary.proved, 0);
        assert_eq!(result.summary.insufficient_strength, 1);
        assert_eq!(result.status, VerificationRunStatus::Inconclusive);
    }

    #[test]
    fn required_reasoning_kind_must_match() {
        let mut required = obligation(ObligationKind::Postcondition);
        required.required_strength = Some(ProofStrength::certified(ReasoningKind::ProofCalculus));
        let mut bundle = TrustContractBundle::empty(
            "bundle-1",
            BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
        );
        bundle.obligations.push(required);
        let context = VerifierExecutionContext::new("run-required-reasoning").snapshot();
        let evidence = vec![ObligationEvidence {
            evidence_id: "ev-certified-smt".to_string(),
            obligation_id: "obl-1".to_string(),
            engine: EngineManifest::new("ay", "0.1.0", EngineKind::SolverKernel),
            status: EvidenceStatus::Proved,
            decline: None,
            proof_strength: Some(ProofStrength::certified(ReasoningKind::Smt)),
            artifacts: Vec::new(),
            counterexample: None,
            publication: EvidencePublicationMetadata::default(),
            diagnostics: Vec::new(),
        }];

        let result = VerificationRunResult::from_evidence(
            context,
            &bundle,
            EngineManifest::new("ay", "0.1.0", EngineKind::SolverKernel),
            &bundle.obligations,
            evidence,
        );

        assert_eq!(result.summary.proved, 0);
        assert_eq!(result.summary.insufficient_strength, 1);
        assert_eq!(result.status, VerificationRunStatus::Inconclusive);
    }

    #[test]
    fn conflicting_publication_hashes_make_run_inconclusive() {
        let mut bundle = TrustContractBundle::empty(
            "bundle-1",
            BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
        );
        bundle.publication.dpub_plan_hash = Some("sha256:plan-a".to_string());
        bundle.obligations.push(obligation(ObligationKind::Postcondition));
        let context = VerifierExecutionContext::new("run-conflict").snapshot();
        let evidence = vec![ObligationEvidence {
            evidence_id: "ev-conflict".to_string(),
            obligation_id: "obl-1".to_string(),
            engine: EngineManifest::new("trust-wp", "0.1.0", EngineKind::Deductive),
            status: EvidenceStatus::Proved,
            decline: None,
            proof_strength: Some(ProofStrength::deductive()),
            artifacts: vec![certificate_artifact("obl-1", "conflict-proof")],
            counterexample: None,
            publication: EvidencePublicationMetadata {
                publication_plan_hash: Some("sha256:plan-b".to_string()),
                ..EvidencePublicationMetadata::default()
            },
            diagnostics: Vec::new(),
        }];

        let result = VerificationRunResult::from_evidence(
            context,
            &bundle,
            EngineManifest::new("trust-wp", "0.1.0", EngineKind::Deductive),
            &bundle.obligations,
            evidence,
        );

        assert_eq!(result.summary.proved, 1);
        assert_eq!(result.summary.publication_conflicts, 1);
        assert_eq!(result.status, VerificationRunStatus::Inconclusive);
        assert!(result.diagnostics[0].contains("publication_plan_hash conflict"));
    }

    #[test]
    fn per_obligation_hashes_cannot_masquerade_as_one_evidence_bundle() {
        let engine = EngineManifest::new("trust-wp", "0.1.0", EngineKind::Deductive);
        let mut bundle = TrustContractBundle::empty(
            "bundle-evidence-splice",
            BundleSubject::Function {
                crate_name: "demo".to_string(),
                path: "demo::two_clauses".to_string(),
            },
        );
        bundle.obligations = vec![
            obligation_with_id("obl-a", ObligationKind::Postcondition),
            obligation_with_id("obl-b", ObligationKind::Postcondition),
        ];
        let mut evidence_a = evidence(
            &engine,
            "ev-a",
            "obl-a",
            EvidenceStatus::Proved,
            Some(ProofStrength::deductive()),
            vec![certificate_artifact("obl-a", "proof-a")],
        );
        evidence_a.publication.evidence_bundle_hash = Some("sha256:bundle-a".to_string());
        let mut evidence_b = evidence(
            &engine,
            "ev-b",
            "obl-b",
            EvidenceStatus::Proved,
            Some(ProofStrength::deductive()),
            vec![certificate_artifact("obl-b", "proof-b")],
        );
        evidence_b.publication.evidence_bundle_hash = Some("sha256:bundle-b".to_string());

        let result = VerificationRunResult::from_evidence(
            VerifierExecutionContext::new("run-evidence-splice").snapshot(),
            &bundle,
            engine,
            &bundle.obligations,
            vec![evidence_a, evidence_b],
        );

        assert_eq!(result.summary.proved, 2);
        assert_eq!(result.summary.publication_conflicts, 1);
        assert_eq!(result.status, VerificationRunStatus::Inconclusive);
        assert!(result.diagnostics[0].contains("evidence_bundle_hash conflict"));
    }

    #[test]
    fn evidence_engine_mismatch_forces_inconclusive() {
        let mut bundle = TrustContractBundle::empty(
            "bundle-1",
            BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
        );
        bundle.obligations.push(obligation(ObligationKind::Postcondition));
        let context = VerifierExecutionContext::new("run-engine-mismatch").snapshot();
        let evidence = vec![ObligationEvidence {
            evidence_id: "ev-engine-b".to_string(),
            obligation_id: "obl-1".to_string(),
            engine: EngineManifest::new("engine-b", "0.1.0", EngineKind::Deductive),
            status: EvidenceStatus::Proved,
            decline: None,
            proof_strength: Some(ProofStrength::deductive()),
            artifacts: Vec::new(),
            counterexample: None,
            publication: EvidencePublicationMetadata::default(),
            diagnostics: Vec::new(),
        }];

        let result = VerificationRunResult::from_evidence(
            context,
            &bundle,
            EngineManifest::new("engine-a", "0.1.0", EngineKind::Deductive),
            &bundle.obligations,
            evidence,
        );

        assert_eq!(result.status, VerificationRunStatus::Inconclusive);
        assert!(result.diagnostics[0].contains("engine provenance mismatch"));
    }

    #[test]
    fn run_manifest_accounts_for_accepted_rejected_and_skipped_obligations() {
        let engine = EngineManifest::new("trust-mc", "0.1.0", EngineKind::Reachability);
        let mut bundle = TrustContractBundle::empty(
            "bundle-1",
            BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
        );
        let mut proved = obligation(ObligationKind::Postcondition);
        proved.obligation_id = "obl-proved".to_string();
        let mut bounded = obligation(ObligationKind::LoopInvariant);
        bounded.obligation_id = "obl-bounded".to_string();
        let mut skipped = obligation(ObligationKind::MemorySafety);
        skipped.obligation_id = "obl-skipped".to_string();
        bundle.obligations.extend([proved, bounded, skipped]);

        let artifact = certificate_artifact("obl-proved", "manifest-proof");
        let evidence = vec![
            ObligationEvidence {
                evidence_id: "ev-proved".to_string(),
                obligation_id: "obl-proved".to_string(),
                engine: engine.clone(),
                status: EvidenceStatus::Proved,
                decline: None,
                proof_strength: Some(ProofStrength {
                    reasoning: ReasoningKind::Chc,
                    assurance: AssuranceLevel::SmtBacked,
                }),
                artifacts: vec![artifact.clone()],
                counterexample: None,
                publication: EvidencePublicationMetadata::default(),
                diagnostics: Vec::new(),
            },
            ObligationEvidence {
                evidence_id: "ev-bounded".to_string(),
                obligation_id: "obl-bounded".to_string(),
                engine: engine.clone(),
                status: EvidenceStatus::Proved,
                decline: None,
                proof_strength: Some(ProofStrength::bounded(32)),
                artifacts: Vec::new(),
                counterexample: None,
                publication: EvidencePublicationMetadata::default(),
                diagnostics: Vec::new(),
            },
        ];

        let result = VerificationRunResult::from_evidence(
            VerifierExecutionContext::new("run-manifest").snapshot(),
            &bundle,
            engine,
            &bundle.obligations,
            evidence,
        );
        let manifest = result.to_manifest();

        assert_eq!(manifest.schema_version, RUN_MANIFEST_SCHEMA_VERSION);
        assert_eq!(manifest.obligations.len(), 3);
        assert_eq!(manifest.accepted_evidence.len(), 1);
        assert_eq!(manifest.accepted_evidence[0].disposition, EvidenceDisposition::AcceptedProof);
        assert_eq!(manifest.rejected_evidence.len(), 1);
        assert_eq!(manifest.rejected_evidence[0].disposition, EvidenceDisposition::RejectedBounded);
        assert_eq!(manifest.skipped.len(), 1);
        assert_eq!(manifest.skipped[0].obligation_id, "obl-skipped");
        assert_eq!(manifest.artifacts, vec![artifact]);
        assert_eq!(manifest.status, VerificationRunStatus::Inconclusive);
    }

    #[test]
    fn run_manifest_json_round_trip_preserves_audit_lists() {
        let engine = EngineManifest::new("trust-mc", "0.1.0", EngineKind::Reachability);
        let mut bundle = TrustContractBundle::empty(
            "bundle-1",
            BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
        );
        bundle.obligations.extend([
            obligation_with_id("obl-accepted", ObligationKind::Postcondition),
            obligation_with_id("obl-bounded", ObligationKind::LoopInvariant),
            obligation_with_id("obl-missing-strength", ObligationKind::MemorySafety),
            obligation_with_id("obl-skipped", ObligationKind::TemporalSafety),
            obligation_with_id("obl-unchecked", ObligationKind::Ownership),
        ]);

        let accepted_certificate = certificate_artifact("obl-accepted", "manifest-json-proof");
        let replay_log = artifact(
            EvidenceArtifactKind::ReplayLog,
            "artifact://bounded-replay.log",
            "bounded-replay",
        );
        let dpub_manifest = artifact(
            EvidenceArtifactKind::DpubManifest,
            "artifact://dpub-manifest.json",
            "unchecked-dpub",
        );
        let evidence = vec![
            evidence(
                &engine,
                "ev-accepted",
                "obl-accepted",
                EvidenceStatus::Proved,
                Some(ProofStrength::smt_unsat()),
                vec![accepted_certificate.clone()],
            ),
            evidence(
                &engine,
                "ev-missing-strength",
                "obl-missing-strength",
                EvidenceStatus::Proved,
                None,
                Vec::new(),
            ),
            evidence(
                &engine,
                "ev-unchecked",
                "obl-unchecked",
                EvidenceStatus::Proved,
                Some(ProofStrength {
                    reasoning: ReasoningKind::OwnershipAnalysis,
                    assurance: AssuranceLevel::Unchecked,
                }),
                vec![dpub_manifest.clone(), dpub_manifest.clone()],
            ),
            evidence(
                &engine,
                "ev-bounded",
                "obl-bounded",
                EvidenceStatus::Proved,
                Some(ProofStrength::bounded(32)),
                vec![replay_log.clone(), replay_log.clone()],
            ),
        ];

        let result = VerificationRunResult::from_evidence(
            VerifierExecutionContext::new("run-manifest-json").snapshot(),
            &bundle,
            engine,
            &bundle.obligations,
            evidence,
        );
        let manifest = result.to_manifest();
        let json = serde_json::to_string(&manifest).expect("serialize manifest");
        let decoded: VerificationRunManifest =
            serde_json::from_str(&json).expect("deserialize manifest");

        assert_eq!(decoded, manifest);
        assert_eq!(
            decoded
                .obligations
                .iter()
                .map(|obligation| (
                    obligation.obligation_id.as_str(),
                    obligation.evidence_count,
                    obligation.skipped
                ))
                .collect::<Vec<_>>(),
            vec![
                ("obl-accepted", 1, false),
                ("obl-bounded", 1, false),
                ("obl-missing-strength", 1, false),
                ("obl-skipped", 0, true),
                ("obl-unchecked", 1, false),
            ]
        );
        assert_eq!(
            decoded
                .accepted_evidence
                .iter()
                .map(|decision| decision.obligation_id.as_str())
                .collect::<Vec<_>>(),
            vec!["obl-accepted"]
        );
        assert_eq!(
            decoded
                .rejected_evidence
                .iter()
                .map(|decision| (decision.obligation_id.as_str(), decision.disposition))
                .collect::<Vec<_>>(),
            vec![
                ("obl-missing-strength", EvidenceDisposition::RejectedInsufficientStrength),
                ("obl-unchecked", EvidenceDisposition::RejectedInsufficientStrength),
                ("obl-bounded", EvidenceDisposition::RejectedBounded),
            ]
        );
        assert_eq!(decoded.skipped.len(), 1);
        assert_eq!(decoded.skipped[0].obligation_id, "obl-skipped");
        let mut expected_artifacts = vec![accepted_certificate, replay_log, dpub_manifest];
        expected_artifacts.sort_by(|left, right| {
            (&left.kind, &left.uri, &left.hash.algorithm, &left.hash.value).cmp(&(
                &right.kind,
                &right.uri,
                &right.hash.algorithm,
                &right.hash.value,
            ))
        });
        assert_eq!(decoded.artifacts, expected_artifacts);
        assert!(
            ["obl-missing-strength", "obl-unchecked", "obl-bounded", "obl-skipped"].iter().all(
                |obligation_id| decoded
                    .accepted_evidence
                    .iter()
                    .all(|decision| decision.obligation_id != *obligation_id)
            )
        );

        let mut forged = manifest.clone();
        let mut promoted = forged.rejected_evidence.remove(0);
        promoted.disposition = EvidenceDisposition::AcceptedProof;
        promoted.reason = "publication-grade proof evidence accepted".to_string();
        forged.accepted_evidence.push(promoted);
        forged.status = VerificationRunStatus::Proved;
        assert!(
            !forged.is_release_actionable(),
            "publicly mutable manifest fields must not become actionable without revalidation"
        );
        let forged_json = serde_json::to_string(&forged).expect("serialize forged manifest");
        let error = serde_json::from_str::<VerificationRunManifest>(&forged_json)
            .expect_err("forged AcceptedProof classification must fail deserialization");
        assert!(error.to_string().contains("verifier"), "{error}");
    }

    #[test]
    fn dpub_release_gate_requires_publication_metadata() {
        let mut bundle = TrustContractBundle::empty(
            "bundle-1",
            BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
        );
        bundle.obligations.push(obligation(ObligationKind::Postcondition));
        let context = VerifierExecutionContext::new("run-dpub")
            .with_invocation(VerifierInvocation::DpubReleaseGate)
            .snapshot();
        let evidence = vec![ObligationEvidence {
            evidence_id: "ev-dpub".to_string(),
            obligation_id: "obl-1".to_string(),
            engine: EngineManifest::new("trust-wp", "0.1.0", EngineKind::Deductive),
            status: EvidenceStatus::Proved,
            decline: None,
            proof_strength: Some(ProofStrength::deductive()),
            artifacts: Vec::new(),
            counterexample: None,
            publication: EvidencePublicationMetadata::default(),
            diagnostics: Vec::new(),
        }];

        let result = VerificationRunResult::from_evidence(
            context,
            &bundle,
            EngineManifest::new("trust-wp", "0.1.0", EngineKind::Deductive),
            &bundle.obligations,
            evidence,
        );

        assert_eq!(result.status, VerificationRunStatus::Inconclusive);
        assert!(result.diagnostics.iter().any(|item| item.contains("publication_plan_hash")));
        assert!(result.diagnostics.iter().any(|item| item.contains("trust_engines_lock_hash")));
    }

    #[test]
    fn evidence_round_trips_as_json() {
        let evidence = ObligationEvidence {
            evidence_id: "ev-1".to_string(),
            obligation_id: "obl-1".to_string(),
            engine: EngineManifest::new("trust-mc", "1.2.3", EngineKind::Reachability),
            status: EvidenceStatus::Proved,
            decline: None,
            proof_strength: Some(ProofStrength::bounded(8)),
            artifacts: vec![EvidenceArtifact {
                kind: EvidenceArtifactKind::SolverQuery,
                uri: "artifact://query.smt2".to_string(),
                hash: ArtifactHash { algorithm: "sha256".to_string(), value: "abc123".to_string() },
                materialization: None,
            }],
            counterexample: None,
            publication: EvidencePublicationMetadata {
                dscan_attestation_hash: Some("sha256:dscan".to_string()),
                dpub_release_id: Some("trust-0.1.0".to_string()),
                ..EvidencePublicationMetadata::default()
            },
            diagnostics: Vec::new(),
        };

        let json = serde_json::to_string(&evidence).expect("serialize evidence");
        let decoded: ObligationEvidence =
            serde_json::from_str(&json).expect("deserialize evidence");

        assert_eq!(decoded, evidence);
    }

    #[test]
    fn artifact_materialization_constructor_enforces_hard_byte_cap() {
        let at_limit = EvidenceArtifactMaterialization::new(
            vec![0x5a; MAX_EVIDENCE_ARTIFACT_MATERIALIZATION_BYTES],
            "size-cap-proof",
            Vec::new(),
        )
        .expect("the documented maximum is accepted");
        assert_eq!(at_limit.bytes().len(), MAX_EVIDENCE_ARTIFACT_MATERIALIZATION_BYTES);
        drop(at_limit);

        assert!(
            EvidenceArtifactMaterialization::new(
                vec![0x5a; MAX_EVIDENCE_ARTIFACT_MATERIALIZATION_BYTES + 1],
                "size-cap-proof",
                Vec::new(),
            )
            .is_none(),
            "one byte over the materialization limit must fail before publication"
        );
    }

    #[test]
    fn artifact_owner_ids_accept_only_interior_ascii_spaces() {
        let trait_impl = "<Button as sealed::Widget>::rank";
        assert!(canonical_artifact_owner_id(trait_impl));
        assert!(canonical_artifact_owner_id("crate::Type::method with suffix"));

        for rejected in [
            " <Button as sealed::Widget>::rank",
            "<Button as sealed::Widget>::rank ",
            "<Button\tas sealed::Widget>::rank",
            "<Button\nas sealed::Widget>::rank",
            "<Button as sealed::Widget>::rank?query",
            "<Button as sealed::Widget>::rank#fragment",
            "crate::Té::method",
        ] {
            assert!(
                !canonical_artifact_owner_id(rejected),
                "non-canonical owner id must remain rejected: {rejected:?}"
            );
        }

        assert_ne!(
            "<Button as sealed::Widget>::rank",
            "<Button  as sealed::Widget>::rank",
            "accepting spaces must not normalize or collapse distinct owner ids"
        );
        assert!(canonical_artifact_owner_id("<Button  as sealed::Widget>::rank"));
    }

    #[test]
    fn summary_fact_round_trips_through_metadata_entry() {
        let fact = SummaryFact::new(
            "summary-pointer-p-q",
            "TrustIr",
            "dep_crate",
            "dep_crate::callee",
            SummaryFactKind::PointerProvenanceEq { left: "p".to_string(), right: "q".to_string() },
            ArtifactHash { algorithm: "sha256".to_string(), value: "a".repeat(64) },
        );

        assert!(fact.is_replay_addressable());
        let metadata = fact.to_metadata_entry().expect("summary fact serializes");
        assert_eq!(metadata.key, SUMMARY_FACT_METADATA_KEY);
        let decoded = SummaryFact::from_metadata_entry(&metadata)
            .expect("summary fact metadata decodes")
            .expect("summary fact metadata key should decode");

        assert_eq!(decoded, fact);
        assert_eq!(decoded.kind.as_str(), "pointer-provenance-eq");
        assert_eq!(decoded.kind.endpoints(), Some(("p", "q")));
    }

    #[test]
    fn summary_fact_provenance_endpoints_and_digest_are_strict_at_bundle_ingress() {
        let valid = SummaryFact::new(
            "summary-pointer-p-q",
            "TrustIr",
            "dep_crate",
            "dep_crate::callee",
            SummaryFactKind::PointerProvenanceEq { left: "p".to_string(), right: "q".to_string() },
            ArtifactHash { algorithm: "sha256".to_string(), value: "b".repeat(64) },
        );
        assert!(valid.is_replay_addressable());

        let mut invalid = valid.clone();
        invalid.digest.algorithm = "SHA-256".to_string();
        invalid.digest.value = "B".repeat(64);
        invalid.source_item = format!("dep::{}", "x".repeat(MAX_SUMMARY_FACT_FIELD_BYTES));
        invalid.kind = SummaryFactKind::PointerProvenanceEq {
            left: " p".to_string(),
            right: "q\n".to_string(),
        };
        assert!(!invalid.is_replay_addressable());

        let mut bundle = TrustContractBundle::empty(
            "bundle-invalid-summary",
            BundleSubject::Crate { name: "demo".to_string() },
        );
        let mut obligation = obligation(ObligationKind::Postcondition);
        obligation.summary_facts.push(invalid);
        bundle.obligations.push(obligation);
        let error = bundle
            .validate()
            .expect_err("invalid summary provenance must fail programmatic validation");
        assert!(error.contains("summary fact"), "{error}");
        let encoded = serde_json::to_vec(&bundle).expect("invalid summary bundle serializes");
        let error = TrustContractBundle::from_json_slice(&encoded)
            .expect_err("invalid summary provenance must fail deserialization");
        assert!(error.contains("summary fact"), "{error}");
    }

    #[test]
    fn evidence_artifact_uri_digest_and_materialization_are_validated_on_runs() {
        let mut invalid_uri = fully_proved_result(VerifierInvocation::Ci);
        invalid_uri.evidence[0].artifacts[0].uri = "../relative proof".to_string();
        let error = invalid_uri
            .validate_derived_state()
            .expect_err("relative artifact URI must fail programmatic validation");
        assert!(error.contains("artifact URI"), "{error}");
        let encoded = serde_json::to_vec(&invalid_uri).expect("invalid URI run serializes");
        let error = serde_json::from_slice::<VerificationRunResult>(&encoded)
            .expect_err("relative artifact URI must fail deserialization");
        assert!(error.to_string().contains("artifact URI"), "{error}");

        let mut digest_mismatch = fully_proved_result(VerifierInvocation::Ci);
        digest_mismatch.evidence[0].artifacts[0].hash.value = "f".repeat(64);
        let error = digest_mismatch
            .validate_derived_state()
            .expect_err("canonical but incorrect digest must not authenticate exact bytes");
        assert!(error.contains("materialization does not match"), "{error}");

        let mut noncanonical_digest = fully_proved_result(VerifierInvocation::Ci);
        noncanonical_digest.evidence[0].artifacts[0].hash.algorithm = "SHA256".to_string();
        noncanonical_digest.evidence[0].artifacts[0].hash.value = "A".repeat(64);
        let error = noncanonical_digest
            .validate_derived_state()
            .expect_err("non-canonical artifact digest must fail the run boundary");
        assert!(error.contains("lowercase SHA-256"), "{error}");
    }

    #[test]
    fn verification_run_result_round_trips_as_json() {
        let engine = AlwaysProves::new();
        let mut bundle = TrustContractBundle::empty(
            "bundle-1",
            BundleSubject::Function { crate_name: "demo".to_string(), path: "demo::f".to_string() },
        );
        bundle.obligations.push(obligation(ObligationKind::Postcondition));
        let context = VerifierExecutionContext::new("run-json")
            .with_invocation(VerifierInvocation::DpubReleaseGate);

        let result = engine.verify_with_context(&bundle, &bundle.obligations, &context);
        let json = serde_json::to_string(&result).expect("serialize run result");
        let decoded: VerificationRunResult =
            serde_json::from_str(&json).expect("deserialize run result");

        assert_eq!(decoded, result);
        assert_eq!(decoded.context.invocation, VerifierInvocation::DpubReleaseGate);

        let mut forged = result;
        forged.status = VerificationRunStatus::Proved;
        forged.summary.publication_conflicts = 0;
        forged.diagnostics.clear();
        assert!(
            !forged.is_fully_proved(),
            "a publicly mutated status/summary cannot bypass derived-state validation"
        );
        let forged_json = serde_json::to_string(&forged).expect("serialize forged result");
        let error = serde_json::from_str::<VerificationRunResult>(&forged_json)
            .expect_err("forged Proved run must fail deserialization");
        assert!(error.to_string().contains("verifier result"), "{error}");
    }

    #[test]
    fn run_reconciliation_is_evidence_derived_and_transactional() {
        let mut result = fully_proved_result(VerifierInvocation::NativeTrustPipeline);
        result.evidence[0].status = EvidenceStatus::Unknown;
        result.evidence[0].proof_strength = None;
        result.evidence[0].artifacts.clear();
        assert!(
            result.validate_derived_state().is_err(),
            "changing typed evidence must stale the old public summary"
        );

        result.try_reconcile_derived_state().expect("valid typed evidence must reconcile");
        assert_eq!(result.status, VerificationRunStatus::Inconclusive);
        assert_eq!(result.summary.proved, 0);
        assert_eq!(result.summary.unknown, 1);
        result.validate_derived_state().expect("reconciled run is canonical");
        result.try_to_manifest().expect("reconciled run has a lossless manifest");

        let mut invalid = fully_proved_result(VerifierInvocation::NativeTrustPipeline);
        invalid.requested_obligations.push(invalid.requested_obligations[0].clone());
        let before = invalid.clone();
        let error = invalid
            .try_reconcile_derived_state()
            .expect_err("reconciliation must not launder duplicate public identity");
        assert!(error.contains("duplicate requested obligation"), "{error}");
        assert_eq!(invalid, before, "failed reconciliation must not partially mutate the run");
    }

    #[test]
    fn run_reconciliation_replaces_stale_derived_diagnostics_but_keeps_engine_history() {
        let mut result = fully_proved_result(VerifierInvocation::NativeTrustPipeline);
        let proved_evidence = result.evidence.clone();
        result.evidence.clear();
        result.context.cancellation = CancellationSnapshot {
            requested: true,
            reason: Some(CancellationReason::ResourceLimitExceeded {
                limit: ResourceLimitKind::Memory,
            }),
        };
        result
            .try_reconcile_derived_state()
            .expect("resource-limited typed carrier must reconcile");
        assert!(result
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.starts_with("release-blocking proof gap: obligation ")));

        result.context.cancellation = CancellationSnapshot::default();
        result.evidence = proved_evidence;
        result.diagnostics.push("engine-authored audit history".to_string());
        result
            .try_reconcile_derived_state()
            .expect("replacement proof must remove the obsolete resource diagnostic");
        assert_eq!(result.status, VerificationRunStatus::Proved);
        assert!(!result
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.starts_with("release-blocking proof gap: obligation ")));
        assert!(result.diagnostics.iter().any(|diagnostic| {
            diagnostic == "engine-authored audit history"
        }));

        let enclosing_engine = result.engine.clone();
        result.evidence[0].engine =
            EngineManifest::new("different-child", API_VERSION, EngineKind::Deductive);
        result
            .try_reconcile_derived_state()
            .expect("typed child-engine conflict must reconcile as Inconclusive");
        assert!(result.diagnostics.iter().any(|diagnostic| {
            diagnostic.starts_with("engine provenance mismatch for evidence ")
        }));

        result.evidence[0].engine = enclosing_engine;
        result
            .try_reconcile_derived_state()
            .expect("restored engine provenance must remove the obsolete conflict");
        assert_eq!(result.status, VerificationRunStatus::Proved);
        assert!(!result.diagnostics.iter().any(|diagnostic| {
            diagnostic.starts_with("engine provenance mismatch for evidence ")
        }));
        result.validate_derived_state().expect("reconciled diagnostics are exact");
        result.try_to_manifest().expect("reconciled diagnostics remain manifestable");
    }

    #[test]
    fn honest_fully_proved_manifest_is_release_actionable() {
        let result = fully_proved_result(VerifierInvocation::DpubReleaseGate);
        assert!(result.is_fully_proved());
        let manifest = result.try_to_manifest().expect("validated manifest");
        assert!(manifest.is_release_actionable());
        let json = serde_json::to_string(&manifest).expect("serialize actionable manifest");
        let restored: VerificationRunManifest =
            serde_json::from_str(&json).expect("validated manifest round trip");
        assert!(restored.is_release_actionable());
    }

    #[test]
    fn fully_proved_non_release_invocations_are_not_release_actionable() {
        for invocation in [
            VerifierInvocation::NativeTrustPipeline,
            VerifierInvocation::Ci,
            VerifierInvocation::Custom {
                namespace: "legacy".to_string(),
                name: "compatibility".to_string(),
            },
        ] {
            let result = fully_proved_result(invocation.clone());
            assert!(result.is_fully_proved(), "{invocation:?} remains a valid proof run");
            let manifest = result.try_to_manifest().expect("validated non-release manifest");
            assert!(
                !manifest.is_release_actionable(),
                "{invocation:?} must not acquire dpub release authority"
            );
        }
    }

    #[test]
    fn duplicate_and_unrequested_evidence_cannot_forge_a_fully_proved_run() {
        let base = fully_proved_result(VerifierInvocation::NativeTrustPipeline);

        let mut duplicated = base.clone();
        duplicated.requested_obligations.push(duplicated.requested_obligations[0].clone());
        duplicated.evidence.push(duplicated.evidence[0].clone());
        duplicated = duplicated.canonicalized_derived_state();
        // The forgery is now caught by TWO independent layers. It used to pass the
        // summary arithmetic (`status == Proved`, `proved == 2`) and be caught only
        // by `validate_derived_state` below. `proved` now counts DISTINCT
        // obligations, so a duplicated row no longer supplies a second proof and
        // the run is already Inconclusive before validation runs. Defence in depth:
        // both assertions below must hold.
        assert_eq!(duplicated.summary.requested_obligations, 2);
        assert_eq!(
            duplicated.summary.proved, 1,
            "a duplicated evidence row must not count as a second proof"
        );
        assert_eq!(
            duplicated.status,
            VerificationRunStatus::Inconclusive,
            "the summary layer must refuse a run whose obligations are not each proved"
        );
        let duplicate_error = duplicated
            .validate_derived_state()
            .expect_err("duplicate request/evidence identities must fail closed");
        assert!(duplicate_error.contains("duplicate requested obligation"), "{duplicate_error}");
        assert!(!duplicated.is_fully_proved());
        let duplicate_json = serde_json::to_vec(&duplicated).expect("serialize duplicate run");
        assert!(VerificationRunResult::from_json_slice(&duplicate_json).is_err());

        let mut duplicate_evidence_id = base.clone();
        let second_obligation =
            obligation_with_id("obl-second-proof", ObligationKind::Postcondition);
        let mut second_evidence = duplicate_evidence_id.evidence[0].clone();
        second_evidence.obligation_id = second_obligation.obligation_id.clone();
        second_evidence.artifacts =
            vec![certificate_artifact(&second_obligation.obligation_id, "second-proof")];
        duplicate_evidence_id.requested_obligations.push(second_obligation);
        duplicate_evidence_id.evidence.push(second_evidence);
        duplicate_evidence_id = duplicate_evidence_id.canonicalized_derived_state();
        assert_eq!(duplicate_evidence_id.status, VerificationRunStatus::Proved);
        let evidence_id_error = duplicate_evidence_id
            .validate_derived_state()
            .expect_err("one evidence ID cannot identify two records");
        assert!(evidence_id_error.contains("duplicate evidence IDs"), "{evidence_id_error}");

        let mut unrequested = base;
        unrequested.evidence[0].obligation_id = "obl-not-requested".to_string();
        unrequested.evidence[0].artifacts =
            vec![certificate_artifact("obl-not-requested", "unrequested-proof")];
        unrequested = unrequested.canonicalized_derived_state();
        let unrequested_error = unrequested
            .validate_derived_state()
            .expect_err("evidence must resolve to the requested inventory");
        assert!(
            unrequested_error.contains("targets unrequested obligation"),
            "{unrequested_error}"
        );
    }

    #[test]
    fn blank_identity_domains_and_inconsistent_cancellation_are_rejected() {
        let base = fully_proved_result(VerifierInvocation::NativeTrustPipeline);

        let mut blank_run = base.clone();
        blank_run.run_id.clear();
        blank_run.context.run_id.clear();
        assert!(blank_run.validate_derived_state().is_err());

        let mut blank_bundle = base.clone();
        blank_bundle.bundle_id = "   ".to_string();
        assert!(blank_bundle.validate_derived_state().is_err());

        let mut blank_evidence = base.clone();
        blank_evidence.evidence[0].evidence_id.clear();
        assert!(blank_evidence.validate_derived_state().is_err());

        let mut blank_obligation = base.clone();
        blank_obligation.requested_obligations[0].obligation_id.clear();
        assert!(blank_obligation.validate_derived_state().is_err());

        let mut inconsistent_cancellation = base;
        inconsistent_cancellation.context.cancellation = CancellationSnapshot {
            requested: false,
            reason: Some(CancellationReason::UserRequested),
        };
        let error = inconsistent_cancellation
            .validate_derived_state()
            .expect_err("a cancellation reason cannot exist without a request");
        assert!(error.contains("reason without a cancellation request"), "{error}");

        let mut mismatched_context = fully_proved_result(VerifierInvocation::DpubReleaseGate);
        mismatched_context.context.run_id = "different-run".to_string();
        let diagnostic_manifest = mismatched_context.to_manifest();
        assert_eq!(diagnostic_manifest.status, VerificationRunStatus::Inconclusive);
        assert!(
            !diagnostic_manifest.is_release_actionable(),
            "the infallible diagnostic constructor must not launder invalid source identity"
        );
    }

    #[test]
    fn blank_incompatible_or_ambiguous_engine_provenance_is_rejected() {
        let base = fully_proved_result(VerifierInvocation::DpubReleaseGate);

        let mut blank = base.clone();
        blank.engine.name = "   ".to_string();
        blank.evidence[0].engine = blank.engine.clone();
        blank = blank.canonicalized_derived_state();
        assert_eq!(blank.status, VerificationRunStatus::Proved);
        assert!(blank.validate_derived_state().is_err());
        assert!(!blank.to_manifest().is_release_actionable());

        let mut incompatible = base.clone();
        incompatible.engine.api_version = "999.0.0".to_string();
        incompatible.evidence[0].engine = incompatible.engine.clone();
        incompatible = incompatible.canonicalized_derived_state();
        let error = incompatible
            .validate_derived_state()
            .expect_err("incompatible engine API provenance must fail");
        assert!(error.contains("incompatible API version"), "{error}");
        let json = serde_json::to_vec(&incompatible).expect("serialize incompatible result");
        assert!(VerificationRunResult::from_json_slice(&json).is_err());

        let duplicate_capability = EngineCapability {
            obligation_kind: ObligationKind::Postcondition,
            support: SupportLevel::Preferred,
        };
        let mut ambiguous = base.clone();
        ambiguous.engine.capabilities = vec![duplicate_capability.clone(), duplicate_capability];
        ambiguous.engine.proof_modes = vec![ReasoningKind::Deductive, ReasoningKind::Deductive];
        ambiguous.evidence[0].engine = ambiguous.engine.clone();
        ambiguous = ambiguous.canonicalized_derived_state();
        assert!(ambiguous.validate_derived_state().is_err());

        let mut blank_optional_provenance = base.clone();
        blank_optional_provenance.engine.repository = Some("".to_string());
        blank_optional_provenance.evidence[0].engine = blank_optional_provenance.engine.clone();
        blank_optional_provenance = blank_optional_provenance.canonicalized_derived_state();
        assert!(blank_optional_provenance.validate_derived_state().is_err());

        let mut blank_subject = base;
        blank_subject.subject = BundleSubject::Crate { name: "\t".to_string() };
        assert!(blank_subject.validate_derived_state().is_err());

        let mut oversized_engine =
            EngineManifest::new("oversized-engine", "1.0.0", EngineKind::Deductive);
        oversized_engine.capabilities = vec![
            EngineCapability {
                obligation_kind: ObligationKind::Postcondition,
                support: SupportLevel::Supported,
            };
            MAX_ENGINE_CAPABILITIES + 1
        ];
        let encoded = serde_json::to_vec(&oversized_engine).expect("serialize oversized engine");
        let error = serde_json::from_slice::<EngineManifest>(&encoded)
            .expect_err("engine capability vector must be bounded during serde");
        assert!(error.to_string().contains("too many engine capabilities"), "{error}");
    }

    #[test]
    fn counterexamples_are_valid_only_for_failed_evidence() {
        let mut forged = fully_proved_result(VerifierInvocation::DpubReleaseGate);
        forged.evidence[0].counterexample = Some(Counterexample {
            format: "trust.counterexample.v1".to_string(),
            data: serde_json::json!({"impossible": true}),
        });
        let error = forged
            .validate_derived_state()
            .expect_err("proved evidence cannot simultaneously claim a counterexample");
        assert!(error.contains("non-failed status"), "{error}");
        assert!(!forged.to_manifest().is_release_actionable());
    }

    /// `ObligationKind::Custom.namespace` is authority-bearing, not decorative:
    /// `trust.vc.hardened` alone buys a full-verifier route, trust-mc ownership
    /// plus an `Assertion` MIR lowering, and native TrustIr routability, while
    /// every other namespace is deliberately unroutable (the
    /// `trust.vc.unbounded_allocation` P0). It is therefore admitted from a
    /// pinned list instead of accepted as producer free text.
    #[test]
    fn custom_obligation_namespace_is_sealed_to_the_pinned_vocabulary() {
        for namespace in ADMITTED_OBLIGATION_NAMESPACES {
            assert!(is_admitted_obligation_namespace(namespace), "{namespace}");
            validate_obligation_kind(&ObligationKind::Custom {
                namespace: (*namespace).to_string(),
                // Names stay free inside an admitted namespace: the hardened
                // lane forwards unrecognized names as `Unknown`.
                name: "a_name_no_consumer_knows".to_string(),
            })
            .unwrap_or_else(|error| panic!("`{namespace}` must stay admitted: {error}"));
        }

        // Admission is exact match. A prefix, suffix, case, or homoglyph
        // near-miss on the privileged namespace must not inherit its authority,
        // and no producer may mint an identity Trust does not define.
        for forged in [
            "trust.vc.hardened.evil",
            "trust.vc.hardened2",
            "trust.vc.hardene",
            "TRUST.VC.HARDENED",
            "trust.vc.hardened\u{200b}",
            "trust\u{2024}vc\u{2024}hardened",
            "trust.vc.unbounded_allocation.routable",
            "trust.vc.test",
            "attacker.ns",
        ] {
            assert!(!is_admitted_obligation_namespace(forged), "{forged}");
            let error = validate_obligation_kind(&ObligationKind::Custom {
                namespace: forged.to_string(),
                name: "raw_path_api".to_string(),
            })
            .expect_err("an unadmitted obligation namespace must be refused");
            assert!(error.contains("not an admitted Trust"), "{error}");
        }

        // Untrimmed / control-character spellings stay refused by the canonical
        // text gate that runs first.
        for malformed in ["trust.vc.hardened ", " trust.vc.hardened", "trust.vc.\thardened", ""] {
            assert!(
                validate_obligation_kind(&ObligationKind::Custom {
                    namespace: malformed.to_string(),
                    name: "raw_path_api".to_string(),
                })
                .is_err(),
                "{malformed:?}"
            );
        }
    }

    /// The exact wire spellings serialized artifacts, digests, and match arms
    /// compare against. In-tree consumers do not re-state them: `trust-router`,
    /// `trust-bmc`, and `trust-mir-extract` alias these constants by `use`, and
    /// `rustc_mir_transform::trust_verify` compares against them directly, so
    /// in-process agreement is structural, not tested. What this pin protects
    /// is the WIRE meaning: an edit to the owning spelling would silently
    /// re-key every already-serialized artifact and digest.
    #[test]
    fn admitted_obligation_namespace_wire_values_are_pinned() {
        assert_eq!(TRUST_VC_HARDENED_OBLIGATION_NAMESPACE, "trust.vc.hardened");
        assert_eq!(TRUST_VC_OBLIGATION_NAMESPACE, "trust.vc");
        assert_eq!(
            TRUST_VC_UNBOUNDED_ALLOCATION_OBLIGATION_NAMESPACE,
            "trust.vc.unbounded_allocation"
        );
        assert_eq!(TRUST_CONTRACT_OBLIGATION_NAMESPACE, "trust.contract");
        assert_eq!(TRUST_PROOF_ITEM_OBLIGATION_NAMESPACE, "trust.proof_item");
        assert_eq!(TRUST_VC_TRUST_IR_OBLIGATION_NAMESPACE, "trust_vc.trust_ir");

        // Exactly one privileged namespace.
        assert_ne!(
            TRUST_VC_UNBOUNDED_ALLOCATION_OBLIGATION_NAMESPACE,
            TRUST_VC_HARDENED_OBLIGATION_NAMESPACE
        );
        // The prefix hazard is REAL, in the direction a guard would test it: an
        // authority check of the form `candidate.starts_with(prefix)` cannot
        // separate these lanes, because the shared `trust.vc` spelling is a
        // proper prefix of BOTH the privileged lane and the deliberately
        // unroutable allocation lane, and the privileged spelling is itself a
        // proper prefix of forgeable extensions. (A previous revision asserted
        // the vacuous opposite direction — that the unbounded spelling does not
        // start with the hardened one — which no guard tests and which no edit
        // to non-nested spellings could ever make fail.) Exact-match admission
        // is therefore load-bearing: pin that it separates exactly the pairs
        // `starts_with` cannot.
        assert!(TRUST_VC_HARDENED_OBLIGATION_NAMESPACE.starts_with(TRUST_VC_OBLIGATION_NAMESPACE));
        assert!(
            TRUST_VC_UNBOUNDED_ALLOCATION_OBLIGATION_NAMESPACE
                .starts_with(TRUST_VC_OBLIGATION_NAMESPACE)
        );
        let forged_extension = format!("{TRUST_VC_HARDENED_OBLIGATION_NAMESPACE}.evil");
        assert!(forged_extension.starts_with(TRUST_VC_HARDENED_OBLIGATION_NAMESPACE));
        assert!(forged_extension.starts_with(TRUST_VC_OBLIGATION_NAMESPACE));
        assert!(!is_admitted_obligation_namespace(&forged_extension));

        let mut sorted = ADMITTED_OBLIGATION_NAMESPACES.to_vec();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(
            sorted.len(),
            ADMITTED_OBLIGATION_NAMESPACES.len(),
            "the admitted namespace list must not contain duplicates"
        );
    }

    #[test]
    fn an_unadmitted_custom_namespace_is_refused_at_every_obligation_entry_point() {
        let admitted = ObligationKind::Custom {
            namespace: TRUST_VC_HARDENED_OBLIGATION_NAMESPACE.to_string(),
            name: "raw_path_api".to_string(),
        };
        let forged = ObligationKind::Custom {
            namespace: "trust.vc.hardened.evil".to_string(),
            name: "raw_path_api".to_string(),
        };

        // 1. Bundle inventory.
        let mut bundle = TrustContractBundle::empty(
            "bundle-sealed-namespace",
            BundleSubject::Function {
                crate_name: "demo".to_string(),
                path: "demo::sealed_namespace".to_string(),
            },
        );
        bundle.obligations.push(obligation_with_id("obl-forged", forged.clone()));
        let error = bundle.validate().expect_err("a forged namespace cannot enter a bundle");
        assert!(error.contains("not an admitted Trust"), "{error}");

        // 2. The cross-boundary semantic digest refuses to bind it at all.
        let digest_error = bundle.obligations[0]
            .canonical_semantic_digest_sha256()
            .expect_err("a forged namespace has no canonical public semantics");
        assert!(digest_error.contains("not an admitted Trust"), "{digest_error}");

        // 3. Request batches (the ID-retention guard is not the only check).
        bundle.obligations[0].kind = admitted.clone();
        bundle.validate().expect("the admitted hardened namespace still validates");
        let mut requested = bundle.obligations.clone();
        requested[0].kind = forged.clone();
        assert!(bundle.validate_requested_obligations(&requested).is_err());

        // 4. Engine capability inventory: an engine cannot declare authority in
        //    a namespace Trust does not define.
        let mut engine = EngineManifest::new("forged-engine", "0.1.0", EngineKind::Reachability);
        engine.capabilities =
            vec![EngineCapability { obligation_kind: forged, support: SupportLevel::Preferred }];
        let engine_error =
            engine.validate().expect_err("a forged capability namespace must be refused");
        assert!(engine_error.contains("not an admitted Trust"), "{engine_error}");
        engine.capabilities[0].obligation_kind = admitted;
        engine.validate().expect("the admitted hardened capability still validates");
    }

    /// `from_json_slice` is documented as parsing an UNTRUSTED result, and a
    /// skipped row's kind is copied verbatim into the release/audit manifest and
    /// into release-blocking diagnostics. It gets the same admission as a
    /// requested obligation, so the rejection is attributable to the forged
    /// namespace rather than to a downstream derived-state recompute.
    #[test]
    fn skipped_obligation_kinds_are_admitted_across_the_untrusted_json_boundary() {
        let engine = EngineManifest::new("unit-engine", "0.1.0", EngineKind::Deductive);
        let mut bundle = TrustContractBundle::empty(
            "bundle-skipped-kind",
            BundleSubject::Function {
                crate_name: "demo".to_string(),
                path: "demo::skipped_kind".to_string(),
            },
        );
        let proved = obligation_with_id("obl-proved", ObligationKind::Postcondition);
        let unevidenced = obligation_with_id(
            "obl-skipped",
            ObligationKind::Custom {
                namespace: TRUST_VC_HARDENED_OBLIGATION_NAMESPACE.to_string(),
                name: "raw_path_api".to_string(),
            },
        );
        bundle.obligations.push(proved.clone());
        bundle.obligations.push(unevidenced);
        let proof = evidence(
            &engine,
            "ev-proved",
            &proved.obligation_id,
            EvidenceStatus::Proved,
            Some(ProofStrength::deductive()),
            vec![certificate_artifact(&proved.obligation_id, "skipped-kind-proof")],
        );
        let result = VerificationRunResult::from_evidence(
            VerifierExecutionContext::new("run-skipped-kind").snapshot(),
            &bundle,
            engine,
            &bundle.obligations,
            vec![proof],
        );
        assert_eq!(result.skipped.len(), 1, "fixture must carry exactly one skipped row");
        result.validate_derived_state().expect("an admitted skipped kind is canonical");

        // Forge ONLY the skipped row, leaving every requested obligation
        // admitted, so the rejection is attributable to the skipped lane.
        let mut forged = serde_json::to_value(&result).expect("serialize skipped-row result");
        forged["skipped"][0]["kind"]["Custom"]["namespace"] =
            serde_json::Value::String("trust.vc.hardened.evil".to_string());
        let bytes = serde_json::to_vec(&forged).expect("encode forged skipped row");
        let error = VerificationRunResult::from_json_slice(&bytes)
            .expect_err("an unadmitted skipped-row namespace must not cross the JSON boundary");
        assert!(error.contains("not an admitted Trust"), "{error}");
    }

    /// Serde `Deserialize` DOES have a production caller — `targo-trust`'s
    /// `run_three_suite_artifact_gate` (pipeline_v2, not under `cfg(test)`)
    /// parses a `VerificationRunManifest` from an on-disk
    /// `verification-run-manifest.json` — so admission cannot rely on every
    /// deserializer remembering to validate. It is enforced at the serde
    /// boundary of `ObligationKind` itself: a bare kind, and a bare
    /// `TrustObligation` (which has no validating `Deserialize` impl), both
    /// refuse an unpinned namespace before any envelope validator runs.
    #[test]
    fn an_unadmitted_namespace_is_refused_at_the_serde_boundary_itself() {
        let forged_kind_json =
            r#"{"Custom":{"namespace":"trust.vc.hardened.evil","name":"raw_path_api"}}"#;
        let error = serde_json::from_str::<ObligationKind>(forged_kind_json)
            .expect_err("a bare ObligationKind deserialization must enforce admission");
        assert!(error.to_string().contains("not an admitted Trust"), "{error}");

        // Positive controls: every admitted namespace (with a free name) and a
        // nominal variant still cross the same boundary.
        for namespace in ADMITTED_OBLIGATION_NAMESPACES {
            let admitted_json = format!(
                r#"{{"Custom":{{"namespace":"{namespace}","name":"a_name_no_consumer_knows"}}}}"#
            );
            let kind: ObligationKind = serde_json::from_str(&admitted_json)
                .unwrap_or_else(|error| panic!("`{namespace}` must deserialize: {error}"));
            assert_eq!(
                kind,
                ObligationKind::Custom {
                    namespace: (*namespace).to_string(),
                    name: "a_name_no_consumer_knows".to_string(),
                }
            );
        }
        assert_eq!(
            serde_json::from_str::<ObligationKind>("\"Assertion\"")
                .expect("nominal variants still deserialize"),
            ObligationKind::Assertion
        );

        // A bare TrustObligation rides the same funnel.
        let mut obligation = serde_json::to_value(obligation_with_id(
            "obl-bare-boundary",
            ObligationKind::Custom {
                namespace: TRUST_VC_HARDENED_OBLIGATION_NAMESPACE.to_string(),
                name: "raw_path_api".to_string(),
            },
        ))
        .expect("serialize bare obligation");
        serde_json::from_value::<TrustObligation>(obligation.clone())
            .expect("the admitted bare obligation deserializes");
        obligation["kind"]["Custom"]["namespace"] =
            serde_json::Value::String("attacker.ns".to_string());
        let error = serde_json::from_value::<TrustObligation>(obligation)
            .expect_err("a bare TrustObligation deserialization must enforce admission");
        assert!(error.to_string().contains("not an admitted Trust"), "{error}");
    }

    /// The exact production boundary of the release-manifest gate: a manifest
    /// whose privileged namespace is forged CONSISTENTLY — every occurrence
    /// rewritten, so every derived-state recompute still matches — must still
    /// be refused, attributably to namespace admission. When the namespace was
    /// producer free text, exactly this forgery deserialized and validated
    /// clean.
    #[test]
    fn a_consistently_forged_namespace_is_refused_at_the_release_manifest_boundary() {
        let engine = EngineManifest::new("unit-engine", "0.1.0", EngineKind::Deductive);
        let mut bundle = TrustContractBundle::empty(
            "bundle-manifest-boundary",
            BundleSubject::Function {
                crate_name: "demo".to_string(),
                path: "demo::manifest_boundary".to_string(),
            },
        );
        let proved = obligation_with_id("obl-proved", ObligationKind::Postcondition);
        let unevidenced = obligation_with_id(
            "obl-skipped",
            ObligationKind::Custom {
                namespace: TRUST_VC_HARDENED_OBLIGATION_NAMESPACE.to_string(),
                name: "raw_path_api".to_string(),
            },
        );
        bundle.obligations.push(proved.clone());
        bundle.obligations.push(unevidenced);
        let proof = evidence(
            &engine,
            "ev-proved",
            &proved.obligation_id,
            EvidenceStatus::Proved,
            Some(ProofStrength::deductive()),
            vec![certificate_artifact(&proved.obligation_id, "manifest-boundary-proof")],
        );
        let result = VerificationRunResult::from_evidence(
            VerifierExecutionContext::new("run-manifest-boundary").snapshot(),
            &bundle,
            engine,
            &bundle.obligations,
            vec![proof],
        );
        let manifest = result.try_to_manifest().expect("canonical manifest");
        let text = serde_json::to_string(&manifest).expect("serialize manifest");
        VerificationRunManifest::from_json_slice(text.as_bytes())
            .expect("the admitted manifest crosses the JSON boundary");

        // Rewrite EVERY occurrence (requested-obligation row AND skipped row at
        // minimum), so nothing but admission can tell the forgery apart.
        assert!(
            text.matches(TRUST_VC_HARDENED_OBLIGATION_NAMESPACE).count() >= 2,
            "fixture must exercise the namespace in more than one manifest field"
        );
        let forged_text = text.replace(TRUST_VC_HARDENED_OBLIGATION_NAMESPACE, "trust.vc.hardenex");
        assert_ne!(forged_text, text);
        let error = VerificationRunManifest::from_json_slice(forged_text.as_bytes())
            .expect_err("a forged manifest namespace must not cross the JSON boundary");
        assert!(error.contains("not an admitted Trust"), "{error}");
    }

    /// The defect report framed `Custom` as a collision surface. It is not:
    /// obligation identity is `obligation_id` plus the canonical semantic
    /// digest, and the externally-tagged encoding of `Custom` is injective.
    /// Pinned here so a future `#[serde(untagged)]`/`rename_all`/flatten change
    /// cannot quietly make two different claims hash alike.
    #[test]
    fn custom_obligation_kind_encoding_is_injective() {
        let encode = |kind: &ObligationKind| {
            serde_json::to_string(kind).expect("obligation kinds serialize")
        };

        // A nominal variant is a bare string; `Custom` is always a tagged
        // object, so no `Custom` can ever spell a nominal role.
        assert_eq!(encode(&ObligationKind::Assertion), "\"Assertion\"");
        assert_eq!(
            encode(&ObligationKind::Custom {
                namespace: TRUST_VC_OBLIGATION_NAMESPACE.to_string(),
                name: "Assertion".to_string(),
            }),
            "{\"Custom\":{\"namespace\":\"trust.vc\",\"name\":\"Assertion\"}}"
        );

        // The namespace/name split is not collapsible: no pair of distinct
        // (namespace, name) values shares an encoding, so the obligation digest
        // separates them.
        let pairs = [
            (TRUST_VC_OBLIGATION_NAMESPACE, "a.b"),
            (TRUST_VC_OBLIGATION_NAMESPACE, "a"),
            (TRUST_VC_HARDENED_OBLIGATION_NAMESPACE, "a"),
            (TRUST_VC_HARDENED_OBLIGATION_NAMESPACE, "a.b"),
            (TRUST_VC_UNBOUNDED_ALLOCATION_OBLIGATION_NAMESPACE, "a"),
        ];
        let mut encodings = FxHashSet::default();
        let mut digests = FxHashSet::default();
        for (namespace, name) in pairs {
            let kind =
                ObligationKind::Custom { namespace: namespace.to_string(), name: name.to_string() };
            assert!(encodings.insert(encode(&kind)), "{namespace}/{name} collided on the wire");
            let obligation = obligation_with_id("obl-digest", kind);
            let digest = obligation
                .canonical_semantic_digest_sha256()
                .expect("an admitted namespace digests");
            assert!(digests.insert(digest), "{namespace}/{name} collided in the semantic digest");
        }

        // Two claims that share a kind are still separated by the rest of the
        // canonical semantics, so the kind was never the identity.
        let shared = ObligationKind::Custom {
            namespace: TRUST_VC_HARDENED_OBLIGATION_NAMESPACE.to_string(),
            name: "raw_path_api".to_string(),
        };
        let left = obligation_with_id("obl-left", shared.clone());
        let mut right = obligation_with_id("obl-right", shared);
        right.description = "a different claim".to_string();
        assert_ne!(
            left.canonical_semantic_digest_sha256().expect("left digests"),
            right.canonical_semantic_digest_sha256().expect("right digests")
        );
    }

    #[test]
    fn verifier_run_and_manifest_collections_are_bounded_before_element_parsing() {
        #[derive(Debug, serde::Deserialize)]
        struct BoundedRunRecords {
            #[serde(deserialize_with = "deserialize_bounded_run_records")]
            records: Vec<()>,
        }
        #[derive(Debug, serde::Deserialize)]
        struct BoundedRunDiagnostics {
            #[serde(deserialize_with = "deserialize_bounded_run_diagnostics")]
            diagnostics: Vec<String>,
        }

        let exact_records: BoundedRunRecords = serde_json::from_value(serde_json::json!({
            "records": vec![serde_json::Value::Null; MAX_VERIFIER_RUN_RECORDS]
        }))
        .expect("the exact run-record limit is accepted");
        assert_eq!(exact_records.records.len(), MAX_VERIFIER_RUN_RECORDS);
        let record_error = serde_json::from_value::<BoundedRunRecords>(serde_json::json!({
            "records": vec![serde_json::Value::Null; MAX_VERIFIER_RUN_RECORDS + 1]
        }))
        .expect_err("one record above the run limit must fail");
        assert!(record_error.to_string().contains("too many verifier run records"));

        let exact_diagnostics: BoundedRunDiagnostics = serde_json::from_value(serde_json::json!({
            "diagnostics": vec!["diagnostic"; MAX_VERIFIER_RUN_DIAGNOSTICS]
        }))
        .expect("the exact diagnostic limit is accepted");
        assert_eq!(exact_diagnostics.diagnostics.len(), MAX_VERIFIER_RUN_DIAGNOSTICS);
        let diagnostic_error = serde_json::from_value::<BoundedRunDiagnostics>(serde_json::json!({
            "diagnostics": vec!["diagnostic"; MAX_VERIFIER_RUN_DIAGNOSTICS + 1]
        }))
        .expect_err("one diagnostic above the run limit must fail");
        assert!(diagnostic_error.to_string().contains("too many verifier run diagnostics"));

        let result = fully_proved_result(VerifierInvocation::DpubReleaseGate);
        let result_value = serde_json::to_value(&result).expect("serialize bounded result");
        for field in ["requested_obligations", "evidence", "skipped"] {
            let mut forged = result_value.clone();
            forged.as_object_mut().expect("result object").insert(
                field.to_string(),
                serde_json::Value::Array(vec![
                    serde_json::Value::Null;
                    MAX_VERIFIER_RUN_RECORDS + 1
                ]),
            );
            let error = serde_json::from_value::<VerificationRunResult>(forged)
                .expect_err("oversized result vector must fail before parsing elements");
            assert!(error.to_string().contains("too many verifier run records"), "{error}");
        }

        let manifest = result.try_to_manifest().expect("validated manifest");
        let manifest_value = serde_json::to_value(&manifest).expect("serialize bounded manifest");
        for field in ["obligations", "accepted_evidence", "rejected_evidence", "skipped"] {
            let mut forged = manifest_value.clone();
            forged.as_object_mut().expect("manifest object").insert(
                field.to_string(),
                serde_json::Value::Array(vec![
                    serde_json::Value::Null;
                    MAX_VERIFIER_RUN_RECORDS + 1
                ]),
            );
            let error = serde_json::from_value::<VerificationRunManifest>(forged)
                .expect_err("oversized manifest vector must fail before parsing elements");
            assert!(error.to_string().contains("too many verifier run records"), "{error}");
        }

        assert!(
            validate_run_collection_limits(
                MAX_VERIFIER_RUN_RECORDS,
                MAX_VERIFIER_RUN_RECORDS,
                0,
                MAX_VERIFIER_RUN_DIAGNOSTICS,
            )
            .is_ok()
        );
        assert!(
            validate_run_collection_limits(
                MAX_VERIFIER_RUN_RECORDS,
                MAX_VERIFIER_RUN_RECORDS,
                1,
                0,
            )
            .expect_err("aggregate count above its limit must fail")
            .contains("aggregate record")
        );
    }

    #[test]
    fn nested_audit_payloads_obey_count_byte_and_depth_limits() {
        let mut evidence =
            fully_proved_result(VerifierInvocation::NativeTrustPipeline).evidence[0].clone();
        evidence.diagnostics =
            vec!["engine diagnostic".to_string(); MAX_EVIDENCE_DIAGNOSTICS_PER_RECORD + 1];
        let json = serde_json::to_vec(&evidence).expect("serialize excessive diagnostics");
        let error = serde_json::from_slice::<ObligationEvidence>(&json)
            .expect_err("nested evidence diagnostics must be serde-bounded");
        assert!(error.to_string().contains("too many evidence diagnostics"), "{error}");

        let mut long_diagnostic = fully_proved_result(VerifierInvocation::NativeTrustPipeline);
        long_diagnostic.diagnostics = vec!["x".repeat(MAX_VERIFIER_DIAGNOSTIC_BYTES + 1)];
        assert!(long_diagnostic.validate_derived_state().is_err());

        let mut long_description = fully_proved_result(VerifierInvocation::NativeTrustPipeline);
        long_description.requested_obligations[0].description =
            "x".repeat(MAX_OBLIGATION_DESCRIPTION_BYTES + 1);
        assert!(long_description.validate_derived_state().is_err());

        let mut nested = serde_json::Value::Null;
        for _ in 0..=MAX_COUNTEREXAMPLE_JSON_DEPTH {
            nested = serde_json::Value::Array(vec![nested]);
        }
        let mut deep_counterexample = fully_proved_result(VerifierInvocation::NativeTrustPipeline);
        deep_counterexample.evidence[0].status = EvidenceStatus::Failed;
        deep_counterexample.evidence[0].proof_strength = None;
        deep_counterexample.evidence[0].counterexample =
            Some(Counterexample { format: "trust.counterexample.v1".to_string(), data: nested });
        let error = deep_counterexample
            .validate_derived_state()
            .expect_err("programmatic counterexample nesting must be bounded");
        assert!(error.contains("JSON depth limit"), "{error}");

        assert!(validate_json_envelope_length(MAX_VERIFIER_JSON_ENVELOPE_BYTES, "test").is_ok());
        assert!(
            validate_json_envelope_length(MAX_VERIFIER_JSON_ENVELOPE_BYTES + 1, "test")
                .expect_err("one byte above the checked-ingress cap must fail")
                .contains("ingress limit")
        );
    }

    #[test]
    fn manifest_decisions_retain_counterexamples_and_engine_diagnostics() {
        let mut result = fully_proved_result(VerifierInvocation::NativeTrustPipeline);
        result.evidence[0].status = EvidenceStatus::Failed;
        result.evidence[0].proof_strength = None;
        result.evidence[0].counterexample = Some(Counterexample {
            format: "trust.counterexample.v1".to_string(),
            data: serde_json::json!({"x": 7, "branch": "overflow"}),
        });
        result.evidence[0].diagnostics =
            vec!["solver produced a concrete failing model".to_string()];
        result = result.canonicalized_derived_state();
        result.validate_derived_state().expect("failed run remains internally valid");

        let manifest = result.try_to_manifest().expect("lossless manifest");
        assert_eq!(manifest.rejected_evidence.len(), 1);
        assert_eq!(manifest.rejected_evidence[0].counterexample, result.evidence[0].counterexample);
        assert_eq!(manifest.rejected_evidence[0].diagnostics, result.evidence[0].diagnostics);
        let encoded = serde_json::to_vec(&manifest).expect("serialize lossless manifest");
        let decoded = VerificationRunManifest::from_json_slice(&encoded)
            .expect("deserialize lossless manifest through checked ingress");
        assert_eq!(decoded, manifest);
    }

    #[test]
    fn duplicate_manifest_decisions_are_never_actionable() {
        let result = fully_proved_result(VerifierInvocation::DpubReleaseGate);
        let mut manifest = result.try_to_manifest().expect("validated manifest");
        manifest.accepted_evidence.push(manifest.accepted_evidence[0].clone());
        assert!(!manifest.is_release_actionable());
        let error =
            manifest.validate_derived_state().expect_err("duplicate evidence decision must fail");
        assert!(error.contains("duplicate evidence IDs"), "{error}");
        let encoded = serde_json::to_vec(&manifest).expect("serialize duplicate manifest");
        assert!(VerificationRunManifest::from_json_slice(&encoded).is_err());
    }

    #[test]
    fn legacy_v1_run_result_without_context_uses_compatibility_snapshot() {
        let json = r#"{
            "schema_version": "trust.verifier-api.v1",
            "run_id": "legacy-run",
            "bundle_id": "bundle-1",
            "subject": { "Function": { "crate_name": "demo", "path": "demo::f" } },
            "engine": {
                "name": "unit-engine",
                "version": "0.1.0",
                "api_version": "0.1.0",
                "kind": "Deductive"
            },
            "status": "Empty",
            "summary": {
                "requested_obligations": 0,
                "evidence_count": 0,
                "proved": 0,
                "failed": 0,
                "unknown": 0,
                "timed_out": 0,
                "cancelled": 0,
                "unsupported": 0,
                "skipped": 0
            },
            "publication": {}
        }"#;

        let decoded: VerificationRunResult =
            serde_json::from_str(json).expect("deserialize legacy run result");

        assert_eq!(decoded.context.run_id, "legacy-run");
        assert_eq!(decoded.context.invocation, VerifierInvocation::NativeTrustPipeline);
    }
}
