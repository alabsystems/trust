// trust_vcgen/quantifier_tiers/presburger.rs: Tier 2 Presburger detection + Cooper's method
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;
use trust_types::{Formula, Sort};

use super::finite_domain::{is_var, substitute};
use super::types::QuantifierError;

// ---------------------------------------------------------------------------
// Tier 2: Presburger arithmetic detection + Cooper's method
// ---------------------------------------------------------------------------

/// Check whether a formula body (under the given bindings) is in Presburger
/// arithmetic -- i.e., only uses linear integer operations and comparisons.
pub(super) fn is_presburger(bindings: &[(trust_types::Symbol, Sort)], body: &Formula) -> bool {
    // All bound variables must be Int.
    if !bindings.iter().all(|(_, s)| matches!(s, Sort::Int)) {
        return false;
    }
    let bound_vars: FxHashSet<&str> = bindings.iter().map(|(n, _)| n.as_str()).collect();
    is_presburger_formula(body, &bound_vars)
}

/// Recursively check if a formula is within Presburger arithmetic.
pub(super) fn is_presburger_formula(f: &Formula, bound: &FxHashSet<&str>) -> bool {
    match f {
        Formula::Bool(_) | Formula::Int(_) => true,
        Formula::Var(_, sort) => matches!(sort, Sort::Int | Sort::Bool),
        Formula::Not(inner) => is_presburger_formula(inner, bound),
        Formula::And(cs) | Formula::Or(cs) => cs.iter().all(|c| is_presburger_formula(c, bound)),
        Formula::Implies(a, b) => {
            is_presburger_formula(a, bound) && is_presburger_formula(b, bound)
        }
        Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b) => is_presburger_term(a, bound) && is_presburger_term(b, bound),
        Formula::Add(a, b) | Formula::Sub(a, b) => {
            is_presburger_term(a, bound) && is_presburger_term(b, bound)
        }
        Formula::Neg(inner) => is_presburger_term(inner, bound),
        // Mul is linear only if at least one operand is a constant.
        Formula::Mul(a, b) => {
            (is_const(a) && is_presburger_term(b, bound))
                || (is_presburger_term(a, bound) && is_const(b))
        }
        // Rem/Div by constant is OK in Presburger (divisibility constraints).
        Formula::Rem(a, b) => is_presburger_term(a, bound) && is_const(b),
        Formula::Div(a, b) => is_presburger_term(a, bound) && is_const(b),
        Formula::Forall(inner_bindings, body) | Formula::Exists(inner_bindings, body) => {
            let mut extended = bound.clone();
            for (n, _) in inner_bindings {
                extended.insert(n.as_str());
            }
            is_presburger_formula(body, &extended)
        }
        Formula::Ite(c, t, e) => {
            is_presburger_formula(c, bound)
                && is_presburger_formula(t, bound)
                && is_presburger_formula(e, bound)
        }
        // Select/Store, BitVec ops, etc. are NOT Presburger.
        _ => false,
    }
}

/// Check if a formula is a valid Presburger term (integer expression).
pub(super) fn is_presburger_term(f: &Formula, bound: &FxHashSet<&str>) -> bool {
    match f {
        Formula::Int(_) => true,
        Formula::Var(_, Sort::Int) => true,
        Formula::Add(a, b) | Formula::Sub(a, b) => {
            is_presburger_term(a, bound) && is_presburger_term(b, bound)
        }
        Formula::Neg(inner) => is_presburger_term(inner, bound),
        Formula::Mul(a, b) => {
            (is_const(a) && is_presburger_term(b, bound))
                || (is_presburger_term(a, bound) && is_const(b))
        }
        Formula::Rem(a, b) => is_presburger_term(a, bound) && is_const(b),
        Formula::Div(a, b) => is_presburger_term(a, bound) && is_const(b),
        // Ite with Presburger condition and Presburger branches is a valid term.
        Formula::Ite(c, t, e) => {
            is_presburger_formula(c, bound)
                && is_presburger_term(t, bound)
                && is_presburger_term(e, bound)
        }
        _ => false,
    }
}

/// Check if a formula is a ground constant.
fn is_const(f: &Formula) -> bool {
    matches!(f, Formula::Int(_))
}

/// Collect free variables in a formula.
pub(super) fn free_vars(f: &Formula) -> FxHashSet<String> {
    let mut result = FxHashSet::default();
    collect_free_vars(f, &FxHashSet::default(), &mut result);
    result
}

fn collect_free_vars(f: &Formula, bound: &FxHashSet<String>, out: &mut FxHashSet<String>) {
    match f {
        Formula::Var(name, _) if !bound.contains(name) => {
            out.insert(name.clone());
        }
        Formula::Var(_, _) => {}
        Formula::Bool(_) | Formula::Int(_) | Formula::BitVec { .. } => {}
        Formula::Not(inner) | Formula::Neg(inner) => collect_free_vars(inner, bound, out),
        Formula::And(cs) | Formula::Or(cs) => {
            for c in cs {
                collect_free_vars(c, bound, out);
            }
        }
        Formula::Implies(a, b)
        | Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b)
        | Formula::Add(a, b)
        | Formula::Sub(a, b)
        | Formula::Mul(a, b)
        | Formula::Div(a, b)
        | Formula::Rem(a, b) => {
            collect_free_vars(a, bound, out);
            collect_free_vars(b, bound, out);
        }
        Formula::Ite(c, t, e) | Formula::Store(c, t, e) => {
            collect_free_vars(c, bound, out);
            collect_free_vars(t, bound, out);
            collect_free_vars(e, bound, out);
        }
        Formula::Select(a, i) => {
            collect_free_vars(a, bound, out);
            collect_free_vars(i, bound, out);
        }
        Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
            let mut extended = bound.clone();
            for (n, _) in bindings {
                extended.insert(n.as_str().to_string());
            }
            collect_free_vars(body, &extended, out);
        }
        _ => {} // Bitvector ops -- no variables in width params
    }
}

/// Fragment classification for decidable theories.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ArithmeticFragment {
    /// Pure Presburger arithmetic (linear integer arithmetic).
    Presburger,
    /// Array theory with linear integer indices.
    ArrayLinear,
    /// Fixed-width bitvector arithmetic.
    Bitvector,
    /// Does not fit any decidable fragment.
    Other,
}

/// Classify a formula into a decidable arithmetic fragment.
#[must_use]
pub fn classify_fragment(formula: &Formula) -> ArithmeticFragment {
    let bound = FxHashSet::default();
    if has_bitvec_ops(formula) {
        return ArithmeticFragment::Bitvector;
    }
    if has_array_ops(formula) {
        if is_presburger_formula(formula, &bound) || array_indices_linear(formula) {
            return ArithmeticFragment::ArrayLinear;
        }
        return ArithmeticFragment::Other;
    }
    if is_presburger_formula(formula, &bound) {
        return ArithmeticFragment::Presburger;
    }
    ArithmeticFragment::Other
}

/// Check if formula uses any bitvector operations.
fn has_bitvec_ops(f: &Formula) -> bool {
    match f {
        Formula::BitVec { .. }
        | Formula::BvAdd(..)
        | Formula::BvSub(..)
        | Formula::BvMul(..)
        | Formula::BvUDiv(..)
        | Formula::BvSDiv(..)
        | Formula::BvURem(..)
        | Formula::BvSRem(..)
        | Formula::BvAnd(..)
        | Formula::BvOr(..)
        | Formula::BvXor(..)
        | Formula::BvNot(..)
        | Formula::BvShl(..)
        | Formula::BvLShr(..)
        | Formula::BvAShr(..)
        | Formula::BvULt(..)
        | Formula::BvULe(..)
        | Formula::BvSLt(..)
        | Formula::BvSLe(..)
        | Formula::BvToInt(..)
        | Formula::IntToBv(..)
        | Formula::BvExtract { .. }
        | Formula::BvConcat(..)
        | Formula::BvZeroExt(..)
        | Formula::BvSignExt(..) => true,
        Formula::Not(inner) | Formula::Neg(inner) => has_bitvec_ops(inner),
        Formula::And(cs) | Formula::Or(cs) => cs.iter().any(has_bitvec_ops),
        Formula::Implies(a, b)
        | Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b)
        | Formula::Add(a, b)
        | Formula::Sub(a, b)
        | Formula::Mul(a, b)
        | Formula::Div(a, b)
        | Formula::Rem(a, b) => has_bitvec_ops(a) || has_bitvec_ops(b),
        Formula::Ite(c, t, e) | Formula::Store(c, t, e) => {
            has_bitvec_ops(c) || has_bitvec_ops(t) || has_bitvec_ops(e)
        }
        Formula::Select(a, i) => has_bitvec_ops(a) || has_bitvec_ops(i),
        Formula::Forall(_, body) | Formula::Exists(_, body) => has_bitvec_ops(body),
        _ => false,
    }
}

/// Check if formula uses array operations (Select/Store).
fn has_array_ops(f: &Formula) -> bool {
    match f {
        Formula::Select(..) | Formula::Store(..) => true,
        Formula::Not(inner) | Formula::Neg(inner) => has_array_ops(inner),
        Formula::And(cs) | Formula::Or(cs) => cs.iter().any(has_array_ops),
        Formula::Implies(a, b)
        | Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b)
        | Formula::Add(a, b)
        | Formula::Sub(a, b)
        | Formula::Mul(a, b)
        | Formula::Div(a, b)
        | Formula::Rem(a, b) => has_array_ops(a) || has_array_ops(b),
        Formula::Ite(c, t, e) => has_array_ops(c) || has_array_ops(t) || has_array_ops(e),
        Formula::Forall(_, body) | Formula::Exists(_, body) => has_array_ops(body),
        _ => false,
    }
}

/// Check if array indices are linear integer expressions.
fn array_indices_linear(f: &Formula) -> bool {
    let bound = FxHashSet::default();
    match f {
        Formula::Select(_, idx) => is_presburger_term(idx, &bound),
        Formula::Store(_, idx, val) => is_presburger_term(idx, &bound) && array_indices_linear(val),
        Formula::And(cs) | Formula::Or(cs) => cs.iter().all(array_indices_linear),
        Formula::Implies(a, b) | Formula::Eq(a, b) => {
            array_indices_linear(a) && array_indices_linear(b)
        }
        Formula::Not(inner) => array_indices_linear(inner),
        Formula::Forall(_, body) | Formula::Exists(_, body) => array_indices_linear(body),
        _ => true,
    }
}

// ---------------------------------------------------------------------------
// Cooper's method -- simplified for common patterns
// ---------------------------------------------------------------------------

/// Try to eliminate a universal quantifier via Cooper's method.
pub(super) fn cooper_eliminate_forall(
    bindings: &[(trust_types::Symbol, Sort)],
    body: &Formula,
) -> Result<Formula, QuantifierError> {
    if bindings.len() != 1 {
        return Err(QuantifierError::CooperFailed {
            reason: "multi-variable Cooper not supported".to_string(),
        });
    }

    let var_name = &bindings[0].0;

    // Extract the structure: Implies(guard, inner) for forall
    if let Formula::Implies(guard, inner) = body
        && let Some(bounds) = extract_linear_bounds(guard, var_name.as_str())
    {
        return cooper_check_universal(var_name.as_str(), &bounds, inner);
    }

    // For simple formulas like `forall x. a*x + b > 0`, try direct analysis.
    if let Some(result) = try_simple_linear_forall(var_name.as_str(), body) {
        return Ok(result);
    }

    Err(QuantifierError::CooperFailed {
        reason: "formula structure not amenable to Cooper's method".to_string(),
    })
}

/// Try to eliminate an existential quantifier via Cooper's method.
pub(super) fn cooper_eliminate_exists(
    bindings: &[(trust_types::Symbol, Sort)],
    body: &Formula,
) -> Result<Formula, QuantifierError> {
    if bindings.len() != 1 {
        return Err(QuantifierError::CooperFailed {
            reason: "multi-variable Cooper not supported".to_string(),
        });
    }

    let var_name = bindings[0].0.as_str();

    // Collect all atomic constraints as a conjunction.
    let atoms = flatten_conjunction(body);

    // Extract lower bounds (B-set) for the variable.
    let mut b_set: Vec<Formula> = Vec::new();
    let mut _other_constraints: Vec<Formula> = Vec::new();

    for atom in &atoms {
        match extract_lower_bound(atom, var_name) {
            Some(bound_expr) => b_set.push(bound_expr),
            None => _other_constraints.push(atom.clone()),
        }
    }

    if b_set.is_empty() {
        return Err(QuantifierError::CooperFailed {
            reason: "no lower bounds found for Cooper elimination".to_string(),
        });
    }

    // For each b_i in B-set, substitute x = b_i in all constraints.
    let disjuncts: Vec<Formula> = b_set
        .iter()
        .map(|bound| {
            let substituted: Vec<Formula> =
                atoms.iter().map(|atom| substitute(atom, var_name, bound)).collect();
            if substituted.len() == 1 {
                substituted.into_iter().next().unwrap_or(Formula::Bool(true))
            } else {
                Formula::And(substituted)
            }
        })
        .collect();

    if disjuncts.len() == 1 {
        Ok(disjuncts.into_iter().next().unwrap_or(Formula::Bool(false)))
    } else {
        Ok(Formula::Or(disjuncts))
    }
}

/// Linear bounds for a variable: lower and upper.
struct LinearBounds {
    lo: Option<Formula>,
    hi: Option<Formula>,
}

/// Extract linear bounds on `var_name` from a guard formula.
fn extract_linear_bounds(guard: &Formula, var_name: &str) -> Option<LinearBounds> {
    let atoms = flatten_conjunction(guard);
    let mut lo = None;
    let mut hi = None;

    for atom in &atoms {
        match atom {
            Formula::Le(a, b) if is_var(b, var_name) => lo = Some(*a.clone()),
            Formula::Le(a, b) if is_var(a, var_name) => hi = Some(*b.clone()),
            Formula::Lt(a, b) if is_var(a, var_name) => hi = Some(*b.clone()),
            Formula::Lt(a, b) if is_var(b, var_name) => lo = Some(*a.clone()),
            Formula::Ge(a, b) if is_var(a, var_name) => lo = Some(*b.clone()),
            Formula::Ge(a, b) if is_var(b, var_name) => hi = Some(*a.clone()),
            Formula::Gt(a, b) if is_var(a, var_name) => {
                hi = Some(Formula::Add(b.clone(), Box::new(Formula::Int(1))));
            }
            _ => {}
        }
    }

    if lo.is_some() || hi.is_some() { Some(LinearBounds { lo, hi }) } else { None }
}

/// Cooper check for universal quantifier with known bounds.
fn cooper_check_universal(
    var_name: &str,
    bounds: &LinearBounds,
    body: &Formula,
) -> Result<Formula, QuantifierError> {
    let fv = free_vars(body);
    if !fv.contains(var_name) {
        return Ok(body.clone());
    }

    let mut guard_parts = Vec::new();
    if let Some(lo) = &bounds.lo {
        guard_parts.push(Formula::Le(
            Box::new(lo.clone()),
            Box::new(Formula::Var(var_name.into(), Sort::Int)),
        ));
    }
    if let Some(hi) = &bounds.hi {
        guard_parts.push(Formula::Lt(
            Box::new(Formula::Var(var_name.into(), Sort::Int)),
            Box::new(hi.clone()),
        ));
    }

    let guard = if guard_parts.len() == 1 {
        guard_parts.into_iter().next().unwrap_or(Formula::Bool(true))
    } else {
        Formula::And(guard_parts)
    };

    Ok(Formula::Implies(Box::new(guard), Box::new(body.clone())))
}

/// Try to analyze a simple linear formula and determine its truth universally.
fn try_simple_linear_forall(var_name: &str, body: &Formula) -> Option<Formula> {
    let fv = free_vars(body);
    if !fv.contains(var_name) {
        return Some(body.clone());
    }

    if let Formula::Eq(a, b) = body
        && a == b
    {
        return Some(Formula::Bool(true));
    }

    None
}

/// Flatten a formula into a list of conjuncts.
fn flatten_conjunction(f: &Formula) -> Vec<Formula> {
    match f {
        Formula::And(cs) => cs.iter().flat_map(flatten_conjunction).collect(),
        other => vec![other.clone()],
    }
}

/// Extract a lower bound expression for `var_name` from an atomic constraint.
fn extract_lower_bound(atom: &Formula, var_name: &str) -> Option<Formula> {
    match atom {
        Formula::Ge(a, b) if is_var(a, var_name) => Some(*b.clone()),
        Formula::Le(a, b) if is_var(b, var_name) => Some(*a.clone()),
        Formula::Gt(a, b) if is_var(a, var_name) => {
            Some(Formula::Add(b.clone(), Box::new(Formula::Int(1))))
        }
        Formula::Lt(a, b) if is_var(b, var_name) => {
            Some(Formula::Add(a.clone(), Box::new(Formula::Int(1))))
        }
        _ => None,
    }
}
