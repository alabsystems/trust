// trust-types/formula/vc: Verification condition and related types
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use super::Formula;
use super::contracts::ContractMetadata;
use super::vc_kind::VcKind;
use crate::Symbol;
use crate::model::SourceSpan;

/// A verification condition — the thing we send to solvers.
///
/// # Examples
///
/// ```
/// use trust_types::{VerificationCondition, VcKind, Formula, Sort, SourceSpan, Symbol};
///
/// // Division-by-zero check: denominator != 0
/// let denom = Formula::Var("d".into(), Sort::Int);
/// let vc = VerificationCondition {
///     kind: VcKind::DivisionByZero,
///     function: Symbol::intern("my_crate::div"),
///     location: SourceSpan::default(),
///     formula: Formula::Eq(Box::new(denom), Box::new(Formula::Int(0))),
///     contract_metadata: None,
/// };
///
/// assert_eq!(vc.kind.proof_level(), trust_types::ProofLevel::L0Safety);
/// assert!(!vc.has_contracts());
/// ```
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerificationCondition {
    pub kind: VcKind,
    // Interned function name — reduces heap allocations for repeated
    // function names across verification conditions.
    pub function: Symbol,
    pub location: SourceSpan,
    /// The formula to check. Convention: we assert this formula and check SAT.
    /// If UNSAT, the property holds (no violation exists).
    /// If SAT, the model is a counterexample.
    pub formula: Formula,
    // Trust: Contract metadata for deductive verification routing.
    #[serde(default)]
    pub contract_metadata: Option<ContractMetadata>,
}

impl VerificationCondition {
    /// Returns true if this VC has any contract annotations.
    #[must_use]
    pub fn has_contracts(&self) -> bool {
        self.contract_metadata.as_ref().is_some_and(|m| m.has_any())
    }
}

// Serializable VC for serde boundaries (JSON proof certificates, caches).
//
// When `arena-formula` is enabled, `VerificationCondition` holds a `FormulaRef`.
// `SerializableVc` always holds an owned `Formula` and implements Serialize/Deserialize,
// used at persistence boundaries (proof certificates, JSON output).

/// A serializable verification condition — always holds an owned `Formula`.
///
/// Use this at persistence boundaries (proof certificates, JSON caches) where
/// the `FormulaArena` is not available. Convert using `from_vc()` / `into_vc()`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SerializableVc {
    pub kind: VcKind,
    // Interned function name for consistency with VerificationCondition.
    pub function: Symbol,
    pub location: SourceSpan,
    /// The formula to check (always an owned `Formula` for serialization).
    pub formula: Formula,
    #[serde(default)]
    pub contract_metadata: Option<ContractMetadata>,
}

impl SerializableVc {
    /// Create from a `VerificationCondition`.
    #[must_use]
    pub fn from_vc(vc: &VerificationCondition) -> Self {
        Self {
            kind: vc.kind.clone(),
            function: vc.function,
            location: vc.location.clone(),
            formula: vc.formula.clone(),
            contract_metadata: vc.contract_metadata,
        }
    }

    /// Convert back to a `VerificationCondition`.
    #[must_use]
    pub fn into_vc(self) -> VerificationCondition {
        VerificationCondition {
            kind: self.kind,
            function: self.function,
            location: self.location,
            formula: self.formula,
            contract_metadata: self.contract_metadata,
        }
    }
}

/// Trust: #178 Ownership metadata extracted from VCs for trust-vc-enriched encoding.
///
/// Carries region identifiers, borrow relationships, lifetime outlives relations,
/// and provenance tracking flags. Used by the trust_vc backend to generate
/// ownership axioms (region non-aliasing, Stacked Borrows permissions, borrow
/// validity constraints) instead of plain SMT-LIB2.
///
/// Not stored on VerificationCondition directly (that would break 477+ existing
/// construction sites). Instead, trust_vc extracts this from VcKind::Assertion
/// messages tagged with the `[memory:region]` prefix by region_encoding.rs.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OwnershipMetadata {
    /// Region identifiers involved in this VC (e.g., "region_0", "region_1").
    pub regions: Vec<String>,
    /// Active borrow relationships (e.g., "region_1 borrows region_0").
    pub borrows: Vec<String>,
    /// Lifetime outlives relations (e.g., "'a: 'b" encoded as "a outlives b").
    #[serde(default)]
    pub lifetime_constraints: Vec<String>,
    /// Whether provenance tracking is needed (raw pointer casts, addr_of).
    #[serde(default)]
    pub has_provenance: bool,
}

impl OwnershipMetadata {
    /// Trust: Returns true if this metadata has any ownership-related content.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.regions.is_empty() && self.borrows.is_empty() && self.lifetime_constraints.is_empty()
    }
}
