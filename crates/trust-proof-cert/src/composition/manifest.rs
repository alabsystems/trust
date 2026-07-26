// trust-proof-cert composition manifest
//
// Cross-crate proof composition metadata for export and import.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use super::checkers::strength_rank;
use super::dag::ProofComposition;
use super::types::CompositionNodeStatus;

/// Per-function specification metadata for cross-crate composition.
///
/// Records producer-reported strength and pre/postcondition descriptions for
/// diagnostics. These fields are public transport metadata, not replay-bound
/// proof authority.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionSpec {
    /// Pre-condition descriptions (human-readable or formula hashes).
    pub preconditions: Vec<String>,
    /// Post-condition descriptions.
    pub postconditions: Vec<String>,
    /// Producer-reported strength, retained as a planning hint only.
    #[serde(rename = "proof_strength")]
    reported_proof_strength: trust_types::ProofStrength,
}

impl FunctionSpec {
    /// Construct non-authoritative function metadata.
    #[must_use]
    pub fn new(
        preconditions: Vec<String>,
        postconditions: Vec<String>,
        reported_proof_strength: trust_types::ProofStrength,
    ) -> Self {
        Self { preconditions, postconditions, reported_proof_strength }
    }

    /// Return the producer-reported strength hint.
    #[must_use]
    pub fn reported_proof_strength(&self) -> &trust_types::ProofStrength {
        &self.reported_proof_strength
    }
}

/// Entry in a [`CompositionManifest`] for a single function.
///
/// Combines function metadata with structural integrity hints. No field in
/// this serde type grants proof-composition authority.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ManifestEntry {
    /// Function metadata (pre/post descriptions and reported strength).
    pub spec: FunctionSpec,
    /// SHA-256 hex hash of the function body/IR artifact, for staleness hints.
    pub signature_hash: String,
    /// Legacy producer claim from the serialized `composable` field.
    ///
    /// Kept private so a public data label cannot be confused with an
    /// authority capability. Generated entries always set it to `false`, and
    /// authority decisions never consult it.
    #[serde(default, rename = "composable", skip_deserializing)]
    reported_composable: bool,
    /// Whether the source record passed mutable/internal integrity checks.
    /// This is a structural hint only and can itself be forged in JSON.
    #[serde(default)]
    pub integrity_valid: bool,
    /// Functions this entry depends on (callees).
    pub dependencies: Vec<String>,
}

impl ManifestEntry {
    /// Construct a structural-only manifest entry.
    #[must_use]
    pub fn new(
        spec: FunctionSpec,
        signature_hash: String,
        dependencies: Vec<String>,
        integrity_valid: bool,
    ) -> Self {
        Self { spec, signature_hash, reported_composable: false, integrity_valid, dependencies }
    }
}

/// Errors specific to manifest operations.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum ManifestError {
    /// A referenced function is not present in the manifest.
    #[error("function `{function}` not found in manifest")]
    FunctionNotFound { function: String },

    /// Merging manifests found conflicting metadata for the same function.
    #[error("conflicting manifest metadata for function `{function}`")]
    MergeConflict { function: String },

    /// Serialization or deserialization failed.
    #[error("manifest serialization failed: {reason}")]
    SerializationFailed { reason: String },
}

/// A manifest exported by a crate for cross-crate proof composition.
///
/// Maps function identifiers to non-authoritative metadata (reported strength,
/// pre/post descriptions, signature hash, and graph hints). Downstream crates
/// must not compose proofs from this transport without independent exact replay.
///
/// Designed for JSON serialization and transport alongside proof artifacts.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompositionManifest {
    /// Crate identifier (name).
    pub crate_id: String,
    /// Crate version (semver).
    pub version: String,
    // Trust: BTreeMap for deterministic certificate output
    /// Function entries keyed by fully-qualified function name.
    pub entries: BTreeMap<String, ManifestEntry>,
    /// Internal call graph edges: (caller, callee) within this crate.
    pub internal_edges: Vec<(String, String)>,
    /// External dependencies: (local_function, dep_crate, dep_function).
    pub external_deps: Vec<(String, String, String)>,
    /// Caller-supplied spec-hash hints for invalidation (function -> hash).
    pub spec_hashes: BTreeMap<String, u64>,
    /// Legacy optional associated-bundle digest.
    ///
    /// This module neither computes nor verifies it; it is transport metadata
    /// only and must not be used as proof authority.
    pub bundle_hash: Vec<u8>,
}

impl CompositionManifest {
    /// Create a new empty manifest for a crate.
    #[must_use]
    pub fn new(crate_id: impl Into<String>, version: impl Into<String>) -> Self {
        CompositionManifest {
            crate_id: crate_id.into(),
            version: version.into(),
            entries: BTreeMap::new(),
            internal_edges: Vec::new(),
            external_deps: Vec::new(),
            spec_hashes: BTreeMap::new(),
            bundle_hash: Vec::new(),
        }
    }

    /// Register a structural metadata entry in the manifest.
    pub fn add_entry(&mut self, fn_id: impl Into<String>, mut entry: ManifestEntry) {
        let fn_id = fn_id.into();
        entry.reported_composable = false;
        self.entries.insert(fn_id, entry);
    }

    /// Look up a function's manifest entry.
    #[must_use]
    pub fn lookup(&self, fn_id: &str) -> Option<&ManifestEntry> {
        self.entries.get(fn_id)
    }

    /// Proof-authoritative composability gate.
    ///
    /// Manifest entries are public serde data and carry no signature trust-root
    /// configuration, obligation digest binding, or replay receipt. Therefore
    /// this gate always returns `false` after validating that both names exist.
    pub fn is_composable(&self, fn_a: &str, fn_b: &str) -> Result<bool, ManifestError> {
        self.entries
            .get(fn_a)
            .ok_or_else(|| ManifestError::FunctionNotFound { function: fn_a.into() })?;
        self.entries
            .get(fn_b)
            .ok_or_else(|| ManifestError::FunctionNotFound { function: fn_b.into() })?;
        Ok(false)
    }

    /// Return a non-authoritative structural compatibility hint.
    ///
    /// This checks internal-integrity labels and reported strengths only. Since
    /// every input is forgeable serde metadata, `true` must never be promoted
    /// to `Certified`, `sound`, or proof reuse.
    pub fn is_structurally_compatible(
        &self,
        fn_a: &str,
        fn_b: &str,
    ) -> Result<bool, ManifestError> {
        let entry_a = self
            .entries
            .get(fn_a)
            .ok_or_else(|| ManifestError::FunctionNotFound { function: fn_a.into() })?;
        let entry_b = self
            .entries
            .get(fn_b)
            .ok_or_else(|| ManifestError::FunctionNotFound { function: fn_b.into() })?;

        let rank_a = strength_rank(entry_a.spec.reported_proof_strength());
        let rank_b = strength_rank(entry_b.spec.reported_proof_strength());
        Ok(entry_a.integrity_valid && entry_b.integrity_valid && rank_a >= 1 && rank_b >= 1)
    }

    /// Merge another manifest into this one (for combining dependency manifests).
    ///
    /// If both manifests contain entries for the same function, every field
    /// must match after legacy authority claims are cleared. A body hash alone
    /// cannot justify silently replacing different spec/dependency metadata.
    pub fn merge(&mut self, other: &CompositionManifest) -> Result<(), ManifestError> {
        // Preflight every conflict before mutating `self`: a failed merge must
        // not leave a partially imported manifest.
        for (fn_id, entry) in &other.entries {
            let mut entry = entry.clone();
            entry.reported_composable = false;
            if let Some(existing) = self.entries.get(fn_id)
                && existing != &entry
            {
                return Err(ManifestError::MergeConflict { function: fn_id.clone() });
            }
        }
        for (k, v) in &other.spec_hashes {
            if self.spec_hashes.get(k).is_some_and(|existing| existing != v) {
                return Err(ManifestError::MergeConflict { function: k.clone() });
            }
        }

        for (fn_id, entry) in &other.entries {
            let mut entry = entry.clone();
            entry.reported_composable = false;
            self.entries.insert(fn_id.clone(), entry);
        }

        // Merge edges (deduplicate).
        let mut existing_edges: BTreeSet<(String, String)> =
            self.internal_edges.iter().cloned().collect();
        for edge in &other.internal_edges {
            if existing_edges.insert(edge.clone()) {
                self.internal_edges.push(edge.clone());
            }
        }

        let mut existing_ext: BTreeSet<(String, String, String)> =
            self.external_deps.iter().cloned().collect();
        for dep in &other.external_deps {
            if existing_ext.insert(dep.clone()) {
                self.external_deps.push(dep.clone());
            }
        }

        // Merge spec hashes without silently replacing contradictory metadata.
        for (k, v) in &other.spec_hashes {
            self.spec_hashes.insert(k.clone(), *v);
        }

        Ok(())
    }

    /// Number of function entries in the manifest.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the manifest has no entries.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// All function names in the manifest, sorted.
    #[must_use]
    pub fn function_names(&self) -> Vec<String> {
        self.entries.keys().cloned().collect()
    }

    /// Serialize the manifest to JSON.
    pub fn to_json(&self) -> Result<String, ManifestError> {
        serde_json::to_string_pretty(self)
            .map_err(|e| ManifestError::SerializationFailed { reason: e.to_string() })
    }

    /// Deserialize a manifest from JSON.
    pub fn from_json(json: &str) -> Result<Self, ManifestError> {
        let mut manifest: Self = serde_json::from_str(json)
            .map_err(|e| ManifestError::SerializationFailed { reason: e.to_string() })?;
        for entry in manifest.entries.values_mut() {
            entry.reported_composable = false;
        }
        Ok(manifest)
    }
}

/// Generate a [`CompositionManifest`] from a [`ProofComposition`] DAG.
///
/// Extracts reported function specs, call edges, and integrity hints from the
/// composition DAG for diagnostics/caching. Generated entries never claim
/// proof-authoritative composability.
pub fn generate_manifest(
    composition: &ProofComposition,
    crate_id: &str,
    version: &str,
) -> CompositionManifest {
    let mut manifest = CompositionManifest::new(crate_id, version);

    for func_name in composition.functions() {
        let node = match composition.get_node(&func_name) {
            Some(n) => n,
            None => continue,
        };

        let cert = composition.get_certificate(&func_name);

        let spec = FunctionSpec::new(
            Vec::new(), // Populated from contract metadata when available
            Vec::new(),
            cert.map(|c| c.solver.strength.clone())
                .unwrap_or_else(trust_types::ProofStrength::smt_unsat_unvalidated),
        );

        let signature_hash = cert.map(|c| c.function_hash.0.clone()).unwrap_or_default();

        let integrity_valid = node.status == CompositionNodeStatus::Valid;

        let entry =
            ManifestEntry::new(spec, signature_hash, node.dependencies.clone(), integrity_valid);

        manifest.add_entry(func_name.clone(), entry);

        // Record internal edges from this function to its callees.
        for dep in &node.dependencies {
            manifest.internal_edges.push((func_name.clone(), dep.clone()));
        }
    }

    manifest
}
