// trust_vcgen/quantifier_tiers/types.rs: Configuration, enums, errors
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for the quantifier elimination pipeline.
#[derive(Debug, Clone)]
pub struct QuantifierConfig {
    /// Maximum number of values to unroll in Tier 1 (default 64, max 1024).
    pub max_unroll: usize,
    /// Whether to attempt Tier 2 (Cooper's method) after Tier 1 fails.
    pub enable_tier2: bool,
}

impl Default for QuantifierConfig {
    fn default() -> Self {
        Self { max_unroll: 64, enable_tier2: true }
    }
}

// ---------------------------------------------------------------------------
// Tier classification
// ---------------------------------------------------------------------------

/// Which elimination tier applies to a quantified formula.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum QuantifierTier {
    /// Tier 0: quantifier-free (no quantifiers present).
    QuantifierFree,
    /// Tier 1: the quantifier ranges over a finite, statically-known domain.
    FiniteUnrolling,
    /// Tier 2: the body is in Presburger arithmetic (linear integer).
    DecidableArithmetic,
    /// No decidable tier applies — leave for the solver.
    Full,
}

/// Solver strategy recommended for a quantified formula.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum SolverStrategy {
    /// No quantifier handling needed — use QF_LIA / QF_BV / QF_ABV.
    QuantifierFree,
    /// Unroll the quantifier and solve the resulting QF formula.
    Unroll,
    /// Use a decidable theory solver (LIA with quantifiers, Cooper's method).
    DecidableTheory,
    /// Use full quantifier reasoning (MBQI, E-matching, or external prover).
    FullQuantifier,
}

/// Result of classifying a quantified formula.
#[derive(Debug, Clone)]
pub struct TierClassification {
    pub tier: QuantifierTier,
    /// For Tier 1: the concrete domain values (if detected).
    pub domain: Option<Vec<i128>>,
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors that can occur during quantifier elimination.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum QuantifierError {
    #[error("unrolling bound {bound} exceeds maximum {max}")]
    UnrollBoundExceeded { bound: usize, max: usize },

    #[error("formula is not in Presburger arithmetic: {reason}")]
    NotPresburger { reason: String },

    #[error("Cooper elimination failed: {reason}")]
    CooperFailed { reason: String },

    #[error("Skolemization is unsupported for this formula: {reason}")]
    UnsupportedSkolemization { reason: String },

    #[error("universal instantiation is unsupported for this formula: {reason}")]
    UnsupportedInstantiation { reason: String },
}

// ---------------------------------------------------------------------------
// Elimination statistics
// ---------------------------------------------------------------------------

/// Elimination statistics.
#[derive(Debug, Clone, Default)]
pub struct EliminationStats {
    pub tier1_eliminated: usize,
    pub tier2_eliminated: usize,
    pub left_intact: usize,
}

/// Statistics about quantifier structure in a formula.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct QuantifierStats {
    /// Number of universal (forall) quantifiers.
    pub num_forall: usize,
    /// Number of existential (exists) quantifiers.
    pub num_exists: usize,
    /// Maximum nesting depth of quantifiers.
    pub max_nesting_depth: usize,
    /// Whether the formula has quantifier alternation (forall-exists or exists-forall).
    pub has_alternation: bool,
}
