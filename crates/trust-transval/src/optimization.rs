// trust-transval: Optimization pass metadata
//
// Defines the known MIR optimization passes surfaced by trust-transval.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

/// Known MIR optimization passes.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[non_exhaustive]
pub enum OptimizationPass {
    /// Replaces expressions with compile-time constants.
    ConstantFolding,
    /// Removes assignments whose results are never used.
    DeadCodeElimination,
    /// Replaces function calls with the callee body.
    Inlining,
    /// Substitutes copies: `_2 = _1; use _2` -> `use _1`.
    CopyPropagation,
    /// Replaces expensive operations with cheaper equivalents (e.g., `x * 2` -> `x << 1`).
    StrengthReduction,
    /// An unrecognized or custom optimization.
    Other(String),
}

impl std::fmt::Display for OptimizationPass {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ConstantFolding => write!(f, "constant_folding"),
            Self::DeadCodeElimination => write!(f, "dead_code_elimination"),
            Self::Inlining => write!(f, "inlining"),
            Self::CopyPropagation => write!(f, "copy_propagation"),
            Self::StrengthReduction => write!(f, "strength_reduction"),
            Self::Other(name) => write!(f, "other({name})"),
        }
    }
}

/// Reserved entry point for pass-specific translation validation.
#[derive(Debug, Clone, Default)]
pub struct OptimizationPassValidator;
