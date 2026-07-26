// trust_vcgen/cross_check/mod.rs: Cross-checking for MIR->Formula VC generation
//
// Validates that generated VerificationConditions have structurally correct
// formulas: variables match function parameters, overflow VCs use correct
// type bounds, division-by-zero VCs test the divisor, and formulas are
// well-sorted (types match across operands).
//
// This is a defensive layer that catches translation bugs in the VC generator
// before formulas reach solvers. A solver silently accepts a mis-sorted
// formula and produces a meaningless result — these checks prevent that.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

mod comparison;
mod properties;
mod reference_vcgen;
mod structural;
mod warnings;

#[cfg(test)]
mod tests;

// Re-export public types
pub use comparison::{CrossCheckResult, CrossCheckVerdict, full_cross_check};
pub use properties::{
    formula_free_var_count, strengthen_by_dropping_assumption, weakening_preserves_safety,
};
use structural::{
    check_degenerate_connectives, check_divzero_structure, check_overflow_bounds,
    check_sort_consistency, check_trivial_formula, check_variable_scope,
};
use trust_types::{VerifiableFunction, VerificationCondition};
pub use warnings::{CrossCheckWarning, SortClass};

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Cross-check a single verification condition against its source function.
///
/// Returns all warnings found. An empty vec means the VC passed all checks.
#[must_use]
pub fn cross_check_vc(
    vc: &VerificationCondition,
    func: &VerifiableFunction,
) -> Vec<CrossCheckWarning> {
    let mut warnings = Vec::new();

    check_variable_scope(vc, func, &mut warnings);
    check_overflow_bounds(vc, &mut warnings);
    check_divzero_structure(vc, &mut warnings);
    check_sort_consistency(&vc.formula, &mut warnings);
    check_degenerate_connectives(&vc.formula, &mut warnings);
    check_trivial_formula(vc, &mut warnings);

    warnings
}

/// Cross-check all VCs produced for a function.
#[must_use]
pub fn cross_check_all_vcs(
    vcs: &[VerificationCondition],
    func: &VerifiableFunction,
) -> Vec<CrossCheckWarning> {
    vcs.iter().flat_map(|vc| cross_check_vc(vc, func)).collect()
}
