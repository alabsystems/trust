// trust_vcgen/cross_check/properties.rs: Formula property functions for property-based testing
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::Formula;

/// Count the free variables in a formula.
#[must_use]
pub fn formula_free_var_count(formula: &Formula) -> usize {
    formula.free_variables().len()
}

/// Property: weakening a VC (adding a disjunction) should not lose safety.
///
/// Given a VC formula `phi`, the weakened formula `phi OR extra` should still
/// be satisfiable whenever `phi` is satisfiable. This function checks that
/// the weakened formula structurally contains the original as a disjunct.
#[must_use]
pub fn weakening_preserves_safety(original: &Formula, weakened: &Formula) -> bool {
    // A weakened formula should be an Or containing the original.
    // If the weakened formula is Or(terms), check that original is among them.
    if let Formula::Or(terms) = weakened {
        terms.iter().any(|t| formula_structurally_eq(t, original))
    } else {
        // If not an Or, it should be identical to the original.
        formula_structurally_eq(original, weakened)
    }
}

/// Property: strengthening by dropping an assumption should not add spurious proofs.
///
/// Given a formula `And(a1, a2, ..., aN)`, dropping one conjunct produces a
/// strictly weaker formula. Returns None if the formula is not a conjunction
/// or has only one conjunct.
#[must_use]
pub fn strengthen_by_dropping_assumption(formula: &Formula) -> Option<Formula> {
    if let Formula::And(terms) = formula {
        if terms.len() <= 1 {
            return None;
        }
        // Drop the first conjunct.
        let remaining: Vec<Formula> = terms[1..].to_vec();
        if remaining.len() == 1 {
            remaining.into_iter().next()
        } else {
            Some(Formula::And(remaining))
        }
    } else {
        None
    }
}

/// Structural equality check for formulas (used in property tests).
/// This is a conservative check — it compares Debug representations.
fn formula_structurally_eq(a: &Formula, b: &Formula) -> bool {
    format!("{a:?}") == format!("{b:?}")
}
