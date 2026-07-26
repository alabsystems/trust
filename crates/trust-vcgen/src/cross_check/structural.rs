// trust_vcgen/cross_check/structural.rs: Individual structural checks on VCs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;
use trust_types::{Formula, Sort, VcKind, VerifiableFunction, VerificationCondition};

use super::warnings::{CrossCheckWarning, SortClass};
use crate::range::{signed_max, signed_min, unsigned_max};

// ---------------------------------------------------------------------------
// Individual checks
// ---------------------------------------------------------------------------

/// Check that all free variables in the formula correspond to function locals.
///
/// The VC generator converts MIR locals to formula variables using their
/// name or `_N` fallback. Every free variable in the formula should map
/// to a known local. Unknown variables indicate a translation bug.
pub(crate) fn check_variable_scope(
    vc: &VerificationCondition,
    func: &VerifiableFunction,
    warnings: &mut Vec<CrossCheckWarning>,
) {
    let free_vars = vc.formula.free_variables();
    let known_names: FxHashSet<String> = func
        .body
        .locals
        .iter()
        .map(|decl| decl.name.as_deref().unwrap_or(&format!("_{}", decl.index)).to_string())
        .collect();

    // Also accept `_N` fallback names and `__slice_len` suffixed names.
    let fallback_names: FxHashSet<String> =
        func.body.locals.iter().map(|decl| format!("_{}", decl.index)).collect();

    for var in &free_vars {
        // Accept known names, fallback _N names, and slice-len auxiliary vars
        if known_names.contains(var)
            || fallback_names.contains(var)
            || var.ends_with("__slice_len")
            || var.starts_with("float_")
        {
            continue;
        }

        // Also accept field-projected names like "_3.0" or "x.1"
        let base = var.split('.').next().unwrap_or(var);
        if known_names.contains(base) || fallback_names.contains(base) {
            continue;
        }

        // Also accept deref/index projected names like "*x" or "arr[_2]"
        let deref_stripped = var.strip_prefix('*').unwrap_or(var);
        let bracket_base = deref_stripped.split('[').next().unwrap_or(deref_stripped);
        if known_names.contains(bracket_base) || fallback_names.contains(bracket_base) {
            continue;
        }

        warnings.push(CrossCheckWarning::UnknownVariable {
            var_name: var.clone(),
            function: vc.function.as_str().to_string(),
        });
    }
}

/// Check that arithmetic overflow VCs use correct type bounds.
///
/// An overflow VC for `i32 + i32` should contain bounds [-2^31, 2^31-1].
/// An overflow VC for `u32 + u32` should contain bounds [0, 2^32-1].
/// If the bounds in the formula do not match, this flags a warning.
pub(crate) fn check_overflow_bounds(
    vc: &VerificationCondition,
    warnings: &mut Vec<CrossCheckWarning>,
) {
    let (op, (lhs_ty, rhs_ty)) = match &vc.kind {
        VcKind::ArithmeticOverflow { op, operand_tys } => (*op, operand_tys.clone()),
        _ => return,
    };

    // Determine expected bounds from the operand type (use LHS as canonical).
    let width = match lhs_ty.int_width() {
        Some(w) => w,
        None => return, // Non-integer overflow VC — skip.
    };
    let signed = lhs_ty.is_signed();

    let expected_min = if signed { signed_min(width) } else { 0 };
    let expected_max = if signed {
        signed_max(width)
    } else {
        // For unsigned, cap at i128::MAX for comparison purposes.
        // u128::MAX cannot be represented as i128.
        let umax = unsigned_max(width);
        if umax > i128::MAX as u128 { i128::MAX } else { umax as i128 }
    };

    // Scan the formula for Int/UInt literals that should be the bounds.
    let mut found_min = false;
    let mut found_max = false;

    vc.formula.visit(&mut |f| {
        match f {
            Formula::Int(n) => {
                if *n == expected_min {
                    found_min = true;
                }
                if *n == expected_max {
                    found_max = true;
                }
            }
            Formula::UInt(n) if !signed && *n == unsigned_max(width) => {
                // Handle u128::MAX case.
                found_max = true;
            }
            Formula::UInt(_) => {}
            _ => {}
        }
    });

    if !found_min || !found_max {
        let vc_desc = format!(
            "{:?} overflow for ({:?}, {:?}), width={width}, signed={signed}",
            op, lhs_ty, rhs_ty
        );
        warnings.push(CrossCheckWarning::OverflowBoundsMismatch {
            expected_min,
            expected_max_approx: expected_max,
            vc_description: vc_desc,
        });
    }
}

/// Check that division-by-zero VCs contain an `Eq(divisor, 0)` test.
///
/// The standard formula is `divisor == 0`. If we cannot find this pattern
/// in the VC formula, the VC is probably malformed.
pub(crate) fn check_divzero_structure(
    vc: &VerificationCondition,
    warnings: &mut Vec<CrossCheckWarning>,
) {
    match &vc.kind {
        VcKind::DivisionByZero | VcKind::RemainderByZero => {}
        _ => return,
    }

    let mut found_eq_zero = false;
    vc.formula.visit(&mut |f| {
        if found_eq_zero {
            return;
        }
        if let Formula::Eq(lhs, rhs) = f {
            // Check for `var == 0` or `0 == var`.
            let has_zero =
                matches!(lhs.as_ref(), Formula::Int(0)) || matches!(rhs.as_ref(), Formula::Int(0));
            let has_var = matches!(lhs.as_ref(), Formula::Var(..))
                || matches!(rhs.as_ref(), Formula::Var(..));
            if has_zero && has_var {
                found_eq_zero = true;
            }
        }
    });

    if !found_eq_zero {
        warnings.push(CrossCheckWarning::DivZeroMissingDivisorCheck {
            function: vc.function.as_str().to_string(),
        });
    }
}

/// Check that formulas are well-sorted: binary operations do not mix
/// incompatible sort domains.
///
/// We classify each sub-formula into a SortClass and check that binary
/// arithmetic and comparison operators have matching operand sorts.
pub(crate) fn check_sort_consistency(formula: &Formula, warnings: &mut Vec<CrossCheckWarning>) {
    formula.visit(&mut |f| {
        match f {
            // Integer arithmetic — both sides should be Int-domain.
            Formula::Add(a, b)
            | Formula::Sub(a, b)
            | Formula::Mul(a, b)
            | Formula::Div(a, b)
            | Formula::Rem(a, b) => {
                let lhs_sort = classify_sort(a);
                let rhs_sort = classify_sort(b);
                if !sorts_compatible(lhs_sort, rhs_sort) {
                    warnings.push(CrossCheckWarning::SortMismatch {
                        context: "integer arithmetic".to_string(),
                        lhs_sort,
                        rhs_sort,
                    });
                }
            }
            // Comparison operators.
            Formula::Lt(a, b) | Formula::Le(a, b) | Formula::Gt(a, b) | Formula::Ge(a, b) => {
                let lhs_sort = classify_sort(a);
                let rhs_sort = classify_sort(b);
                if !sorts_compatible(lhs_sort, rhs_sort) {
                    warnings.push(CrossCheckWarning::SortMismatch {
                        context: "comparison".to_string(),
                        lhs_sort,
                        rhs_sort,
                    });
                }
            }
            // BV operations — both sides should be BitVec with same width.
            Formula::BvAdd(a, b, w) | Formula::BvSub(a, b, w) | Formula::BvMul(a, b, w) => {
                let lhs_sort = classify_sort(a);
                let rhs_sort = classify_sort(b);
                let expected = SortClass::BitVec(*w);
                if lhs_sort != SortClass::Unknown && lhs_sort != expected {
                    warnings.push(CrossCheckWarning::SortMismatch {
                        context: format!("bitvector arithmetic (width {w})"),
                        lhs_sort,
                        rhs_sort: expected,
                    });
                }
                if rhs_sort != SortClass::Unknown && rhs_sort != expected {
                    warnings.push(CrossCheckWarning::SortMismatch {
                        context: format!("bitvector arithmetic (width {w})"),
                        lhs_sort: expected,
                        rhs_sort,
                    });
                }
            }
            _ => {}
        }
    });
}

/// Check for degenerate And/Or connectives with 0 or 1 children.
pub(crate) fn check_degenerate_connectives(
    formula: &Formula,
    warnings: &mut Vec<CrossCheckWarning>,
) {
    formula.visit(&mut |f| match f {
        Formula::And(terms) if terms.len() < 2 => {
            warnings.push(CrossCheckWarning::DegenerateConnective {
                connective: "And".to_string(),
                child_count: terms.len(),
            });
        }
        Formula::Or(terms) if terms.len() < 2 => {
            warnings.push(CrossCheckWarning::DegenerateConnective {
                connective: "Or".to_string(),
                child_count: terms.len(),
            });
        }
        _ => {}
    });
}

/// Check if the entire VC formula is trivially true or false.
pub(crate) fn check_trivial_formula(
    vc: &VerificationCondition,
    warnings: &mut Vec<CrossCheckWarning>,
) {
    if let Formula::Bool(val) = &vc.formula {
        warnings.push(CrossCheckWarning::TrivialFormula {
            function: vc.function.as_str().to_string(),
            value: *val,
        });
    }
}

// ---------------------------------------------------------------------------
// Sort classification helpers
// ---------------------------------------------------------------------------

/// Classify the top-level sort of a formula expression.
pub(crate) fn classify_sort(formula: &Formula) -> SortClass {
    match formula {
        Formula::Bool(_) => SortClass::Bool,
        Formula::Int(_) | Formula::UInt(_) => SortClass::Int,
        Formula::BitVec { width, .. } => SortClass::BitVec(*width),
        Formula::Var(_, sort) => match sort {
            Sort::Bool => SortClass::Bool,
            Sort::Int => SortClass::Int,
            Sort::BitVec(w) => SortClass::BitVec(*w),
            Sort::Array(..) => SortClass::Unknown,
            _ => SortClass::Unknown,
        },
        // Arithmetic results are Int-domain.
        Formula::Add(..)
        | Formula::Sub(..)
        | Formula::Mul(..)
        | Formula::Div(..)
        | Formula::Rem(..)
        | Formula::Neg(..) => SortClass::Int,
        // BV results carry width.
        Formula::BvAdd(_, _, w)
        | Formula::BvSub(_, _, w)
        | Formula::BvMul(_, _, w)
        | Formula::BvNot(_, w)
        | Formula::BvAnd(_, _, w)
        | Formula::BvOr(_, _, w)
        | Formula::BvXor(_, _, w)
        | Formula::BvShl(_, _, w)
        | Formula::BvLShr(_, _, w)
        | Formula::BvAShr(_, _, w) => SortClass::BitVec(*w),
        // Boolean results.
        Formula::Not(_)
        | Formula::And(_)
        | Formula::Or(_)
        | Formula::Implies(..)
        | Formula::Eq(..)
        | Formula::Lt(..)
        | Formula::Le(..)
        | Formula::Gt(..)
        | Formula::Ge(..)
        | Formula::BvULt(..)
        | Formula::BvULe(..)
        | Formula::BvSLt(..)
        | Formula::BvSLe(..) => SortClass::Bool,
        // Conversions.
        Formula::BvToInt(..) => SortClass::Int,
        Formula::IntToBv(_, w) => SortClass::BitVec(*w),
        // Other.
        _ => SortClass::Unknown,
    }
}

/// Check if two sort classes are compatible for binary operations.
///
/// Int and Int are compatible. BitVec(n) and BitVec(n) are compatible.
/// Unknown is compatible with anything (we cannot determine the sort).
/// All other combinations are mismatches.
pub(crate) fn sorts_compatible(a: SortClass, b: SortClass) -> bool {
    match (a, b) {
        (SortClass::Unknown, _) | (_, SortClass::Unknown) => true,
        (SortClass::Int, SortClass::Int) => true,
        (SortClass::Bool, SortClass::Bool) => true,
        (SortClass::BitVec(wa), SortClass::BitVec(wb)) => wa == wb,
        _ => false,
    }
}
