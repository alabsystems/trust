// trust-clean/certification/types.rs: Proof theory and generation types
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::logic_classification::SmtLogic;
use crate::reconstruction::LeanProofTerm;

// ---------------------------------------------------------------------------
// Trust: Proof theory and generation types
// ---------------------------------------------------------------------------

/// Trust: SMT theory that a proof term was generated for.
///
/// Used to tag proof certificates with the theory fragment that was certified,
/// enabling downstream consumers to know the scope of the proof.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProofTheory {
    /// Quantifier-free linear integer arithmetic.
    QfLia,
    /// Quantifier-free uninterpreted functions (equality logic).
    QfUf,
    /// Combined QF_LIA + QF_UF: formulas with both integer arithmetic and
    /// Boolean/equality reasoning.
    QfLiaUf,
}

impl ProofTheory {
    /// Human-readable name for the theory.
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            ProofTheory::QfLia => "QF_LIA",
            ProofTheory::QfUf => "QF_UF",
            ProofTheory::QfLiaUf => "QF_LIA+UF",
        }
    }
}

/// Trust: Result of clean proof term generation from a solver proof.
///
/// Captures both the generated proof term and the theory it was generated for,
/// or an error if generation failed.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum ProofGeneration {
    /// Proof term was successfully generated.
    Generated {
        /// The clean proof term (our intermediate representation).
        proof_term: LeanProofTerm,
        /// SMT theory the proof was generated for.
        theory: ProofTheory,
    },
    /// Proof term generation failed.
    Failed {
        /// Why generation failed.
        reason: String,
    },
    /// The formula's logic is not supported for proof generation.
    Unsupported {
        /// The classified logic fragment.
        logic: SmtLogic,
        /// Why this logic is not supported.
        reason: String,
    },
}

impl ProofGeneration {
    /// Returns `true` if proof generation succeeded.
    #[must_use]
    pub fn is_generated(&self) -> bool {
        matches!(self, ProofGeneration::Generated { .. })
    }

    /// Returns `true` if the formula's logic was unsupported.
    #[must_use]
    pub fn is_unsupported(&self) -> bool {
        matches!(self, ProofGeneration::Unsupported { .. })
    }

    /// Returns `true` if proof generation failed (error during reconstruction).
    #[must_use]
    pub fn is_failed(&self) -> bool {
        matches!(self, ProofGeneration::Failed { .. })
    }
}
