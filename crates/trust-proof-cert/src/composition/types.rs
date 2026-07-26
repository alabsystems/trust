// trust-proof-cert proof composition types
//
// Core types for proof composition: errors, results, and property tags.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::{CertError, CertificationStatus};

/// Errors specific to proof composition.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum CompositionError {
    /// The two certificates have incompatible assumptions
    /// (e.g., contradictory preconditions on shared variables).
    #[error("incompatible assumptions between {cert_a} and {cert_b}: {detail}")]
    IncompatibleAssumptions { cert_a: String, cert_b: String, detail: String },

    /// Composing these certificates would create a circular dependency.
    #[error("circular dependency detected: {cycle}")]
    CircularDependency { cycle: String },

    /// A required intermediate certificate is missing from the composition.
    #[error("missing link: certificate for `{function}` is required but not provided")]
    MissingLink { function: String },

    /// Cannot weaken to a property that is not implied by the original.
    #[error("weakening failed: `{target_property}` is not implied by the certificate")]
    WeakeningFailed { target_property: String },

    /// Cannot strengthen: the certificate does not prove the stronger property.
    #[error("strengthening check failed: `{target_property}` is not proved by {cert_id}")]
    StrengtheningFailed { cert_id: String, target_property: String },

    /// Generic composition failure.
    #[error("composition failed: {reason}")]
    CompositionFailed { reason: String },

    /// Formula deserialization failed during composition.
    ///
    /// Corrupted or incompatible `formula_json` in a proof certificate must
    /// not be silently ignored — composition cannot verify semantic
    /// consistency without the formula.
    #[error("formula deserialization failed for `{function}`: {reason}")]
    FormulaDeserializationFailed { function: String, reason: String },

    /// The requested operation would create proof authority from structural
    /// metadata, but no replay-bound/signed composition evidence was supplied.
    ///
    /// This is deliberately distinct from structural incompatibility: callers
    /// can still inspect structural diagnostics, but must not treat them as a
    /// proof.
    #[error(
        "proof authority unavailable for {operation}: composition requires exact replay-bound or sealed evidence"
    )]
    ProofAuthorityUnavailable { operation: &'static str },
}

/// Status of a composition node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum CompositionNodeStatus {
    /// Certificate metadata is internally self-consistent.
    ///
    /// Despite the legacy `Valid` spelling, this checks only mutable/public
    /// integrity metadata (the VC snapshot hash and the certificate's own hash
    /// chain). It does **not** mean that the proof was replayed, that a signature
    /// chains to a configured trust root, or that this node may authorize proof
    /// composition.
    Valid,
    /// Certificate metadata failed an internal integrity check.
    ChainBroken,
    /// Certificate is stale (function hash changed).
    Stale,
    /// Certificate is missing (required but not provided).
    Missing,
}

/// Whether a change was body-only or also changed the spec/signature.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ChangeKind {
    /// Only the function body changed; spec and signature are the same.
    /// Only the changed function itself needs re-verification.
    BodyOnly,
    /// The function's spec or signature changed.
    /// The changed function AND all transitive callers need re-verification.
    SpecChanged,
}

/// Per-function proof strength record.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionStrength {
    /// Fully-qualified function name.
    pub function: String,
    /// The certificate producer's reported proof strength.
    pub strength: trust_types::ProofStrength,
    /// The certificate producer's reported certification status.
    pub status: CertificationStatus,
}

impl From<CompositionError> for CertError {
    fn from(e: CompositionError) -> Self {
        CertError::VerificationFailed { reason: e.to_string() }
    }
}

/// Legacy transport shape for a composed-proof result.
///
/// The public composition entry points currently fail closed before producing
/// this type because no exact replay-bound composition authority is wired. Its
/// fields are metadata and must not be reconstructed from serde input and then
/// treated as proof authority.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ComposedProof {
    /// IDs of the constituent certificates.
    pub constituent_ids: Vec<String>,
    /// Functions covered by this composed proof.
    pub functions: Vec<String>,
    /// Producer-reported combined strength metadata.
    pub combined_strength: trust_types::ProofStrength,
    /// Legacy producer-reported status; no public composition gate emits this type.
    pub combined_status: CertificationStatus,
    /// Total solver time across all constituents (ms).
    pub total_time_ms: u64,
    /// Legacy producer-reported consistency label; not proof authority.
    pub is_consistent: bool,
    /// Edges in the call graph that this composition covers.
    /// Each entry is (caller_function, callee_function).
    pub call_edges: Vec<(String, String)>,
    /// Per-function proof strengths (empty for backward compat).
    pub function_strengths: Vec<FunctionStrength>,
}

/// Result of a composability check between two certificates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ComposabilityResult {
    /// Whether proof-authoritative composition is permitted.
    ///
    /// This is always `false` until a sealed/replayed authority input is added
    /// to the composition API. Public certificate fields cannot set it.
    pub composable: bool,
    /// Whether the public metadata passed the structural compatibility checks.
    /// This is useful for diagnostics and planning only.
    pub structurally_compatible: bool,
    /// Structural incompatibilities (empty if structurally compatible).
    pub issues: Vec<String>,
    /// Shared function dependencies between the two certificates.
    pub shared_deps: Vec<String>,
}

/// A property tag for weakening/strengthening operations.
/// Represented as a string label for now; in production this would
/// reference the formula AST.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Property(pub String);

impl Property {
    /// Create a property from a string label.
    pub fn new(label: impl Into<String>) -> Self {
        Property(label.into())
    }
}
