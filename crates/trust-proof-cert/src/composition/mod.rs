// trust-proof-cert proof composition
//
// Combines proof certificates for modular verification.
// Supports composability checks, transitive closure, weakening,
// strengthening checks, and cross-function composition.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

mod checkers;
mod dag;
mod manifest;
mod modular;
mod types;
// Portfolio certificate composition for multi-backend proof results.
pub(crate) mod portfolio;

#[cfg(test)]
mod tests;

// --- Re-exports: types ---
pub use types::{
    ChangeKind, ComposabilityResult, ComposedProof, CompositionError, CompositionNodeStatus,
    FunctionStrength, Property,
};

// --- Re-exports: checkers ---
pub use checkers::{
    check_composability, compose_proofs, strengthening_check, transitive_closure, weakening,
};
#[allow(unused_imports)]
pub(crate) use checkers::{check_composability_semantic, negate_formula_json, strength_rank};

// --- Re-exports: modular ---
pub use modular::{modular_composition, modular_composition_with_deps};

// --- Re-exports: dag ---
pub use dag::{
    CompositionNode, CompositionVerification, IncrementalComposition, ProofComposition,
    verify_composition,
};

// --- Re-exports: manifest ---
pub use manifest::{
    CompositionManifest, FunctionSpec, ManifestEntry, ManifestError, generate_manifest,
};

// --- Re-exports: portfolio ---
pub use portfolio::{
    CertificateComponent, ComposedCertificate, CompositionMethod, compose_certificates,
    make_component,
};
