//! Formula substitution engine for caller propagation.
//!
//! Substitutes variables in SMT-level formulas (formal parameters -> actual arguments).
//! Handles nested substitutions safely to avoid variable capture, and simplifies
//! resulting formulas after substitution.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

use thiserror::Error;
use trust_types::{Formula, Sort, infer_sort};

/// Errors that can occur during formula substitution.
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub enum SubstitutionError {
    /// A required variable was not found in the substitution map.
    #[error("unbound variable `{name}` of sort {sort:?}")]
    UnboundVariable { name: String, sort: Sort },

    /// A substitution would cause variable capture in a quantifier.
    #[error("variable capture: `{captured}` would be captured by quantifier binding `{binder}`")]
    VariableCapture { captured: String, binder: String },

    /// Sort mismatch between formal parameter and actual argument.
    #[error("sort mismatch for `{name}`: expected {expected:?}, got {actual:?}")]
    SortMismatch { name: String, expected: Sort, actual: Sort },

    /// Formal-parameter and actual-argument counts differ.
    #[error("call arity mismatch: expected {expected} arguments, got {actual}")]
    ArityMismatch { expected: usize, actual: usize },

    /// Substitution depth exceeded (protection against infinite expansion).
    #[error("substitution depth limit {limit} exceeded")]
    DepthExceeded { limit: usize },

    /// A mapped free variable survived substitution, usually because a new
    /// Formula variant was not traversed by the structural implementation.
    #[error("incomplete substitution: mapped free variable `{name}` remains in the result")]
    IncompleteSubstitution { name: String },
}

/// A mapping from variable names to their replacement formulas.
#[derive(Debug, Clone, Default)]
pub struct SubstitutionMap {
    /// Variable name -> replacement formula.
    mappings: FxHashMap<String, Formula>,
    /// Variable name -> expected sort (for type checking).
    sorts: FxHashMap<String, Sort>,
}

impl SubstitutionMap {
    /// Create an empty substitution map.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a mapping from a variable name to a replacement formula.
    pub fn insert(&mut self, name: impl Into<String>, sort: Sort, replacement: Formula) {
        let name = name.into();
        self.sorts.insert(name.clone(), sort);
        self.mappings.insert(name, replacement);
    }

    /// Build a substitution map from parallel slices of formal parameter names/sorts
    /// and actual argument formulas.
    ///
    /// # Errors
    ///
    /// Returns `SubstitutionError::ArityMismatch` if lengths differ, or
    /// `SubstitutionError::SortMismatch` if a sort check fails.
    pub fn from_params_and_args(
        params: &[(String, Sort)],
        args: &[Formula],
    ) -> Result<Self, SubstitutionError> {
        if params.len() != args.len() {
            return Err(SubstitutionError::ArityMismatch {
                expected: params.len(),
                actual: args.len(),
            });
        }
        let mut map = Self::new();
        for (i, (name, sort)) in params.iter().enumerate() {
            let arg = &args[i];
            let arg_sort = infer_sort(arg);
            if &arg_sort != sort {
                return Err(SubstitutionError::SortMismatch {
                    name: name.clone(),
                    expected: sort.clone(),
                    actual: arg_sort,
                });
            }
            map.insert(name.clone(), sort.clone(), arg.clone());
        }
        Ok(map)
    }

    /// Number of mappings.
    #[must_use]
    pub fn len(&self) -> usize {
        self.mappings.len()
    }

    /// Whether the map is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.mappings.is_empty()
    }

    /// Get the replacement for a variable name.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&Formula> {
        self.mappings.get(name)
    }

    /// Get all variable names in this map.
    #[must_use]
    pub fn variables(&self) -> FxHashSet<&str> {
        self.mappings.keys().map(String::as_str).collect()
    }
}

/// Apply a substitution map to a formula, replacing variables with their
/// mapped formulas.
///
/// This is capture-avoiding: if a quantifier binds a variable that appears
/// free in a replacement, the substitution will return an error rather than
/// silently capturing the variable.
///
/// # Errors
///
/// Returns `SubstitutionError` on variable capture or depth overflow.
pub fn substitute(formula: &Formula, map: &SubstitutionMap) -> Result<Formula, SubstitutionError> {
    let result = substitute_inner(formula, map, 0, 100)?;
    validate_substitution_complete(formula, &result, map)?;
    Ok(result)
}

/// Apply substitution with configurable depth limit.
///
/// # Errors
///
/// Returns `SubstitutionError` on variable capture or depth overflow.
pub fn substitute_with_depth(
    formula: &Formula,
    map: &SubstitutionMap,
    max_depth: usize,
) -> Result<Formula, SubstitutionError> {
    let result = substitute_inner(formula, map, 0, max_depth)?;
    validate_substitution_complete(formula, &result, map)?;
    Ok(result)
}

fn validate_substitution_complete(
    original: &Formula,
    result: &Formula,
    map: &SubstitutionMap,
) -> Result<(), SubstitutionError> {
    let original_free = free_variables(original);
    let result_free = free_variables(result);
    for name in map.variables() {
        if original_free.contains(name) && result_free.contains(name) {
            return Err(SubstitutionError::IncompleteSubstitution { name: name.to_string() });
        }
    }
    Ok(())
}

fn substitute_inner(
    formula: &Formula,
    map: &SubstitutionMap,
    depth: usize,
    max_depth: usize,
) -> Result<Formula, SubstitutionError> {
    if depth > max_depth {
        return Err(SubstitutionError::DepthExceeded { limit: max_depth });
    }

    let recurse = |f: &Formula| -> Result<Formula, SubstitutionError> {
        substitute_inner(f, map, depth + 1, max_depth)
    };

    let recurse_box =
        |f: &Formula| -> Result<Box<Formula>, SubstitutionError> { Ok(Box::new(recurse(f)?)) };

    match formula {
        // Variable: substitute if in map, otherwise leave as-is.
        Formula::Var(name, _sort) => {
            if let Some(replacement) = map.get(name) {
                Ok(replacement.clone())
            } else {
                Ok(formula.clone())
            }
        }

        // Literals: no substitution needed.
        Formula::Bool(_) | Formula::Int(_) | Formula::UInt(_) | Formula::BitVec { .. } => {
            Ok(formula.clone())
        }

        // Boolean connectives
        Formula::Not(inner) => Ok(Formula::Not(recurse_box(inner)?)),
        Formula::And(conjuncts) => {
            let subs: Result<Vec<_>, _> = conjuncts.iter().map(&recurse).collect();
            Ok(Formula::And(subs?))
        }
        Formula::Or(disjuncts) => {
            let subs: Result<Vec<_>, _> = disjuncts.iter().map(&recurse).collect();
            Ok(Formula::Or(subs?))
        }
        Formula::Implies(lhs, rhs) => Ok(Formula::Implies(recurse_box(lhs)?, recurse_box(rhs)?)),

        // Comparisons
        Formula::Eq(l, r) => Ok(Formula::Eq(recurse_box(l)?, recurse_box(r)?)),
        Formula::Lt(l, r) => Ok(Formula::Lt(recurse_box(l)?, recurse_box(r)?)),
        Formula::Le(l, r) => Ok(Formula::Le(recurse_box(l)?, recurse_box(r)?)),
        Formula::Gt(l, r) => Ok(Formula::Gt(recurse_box(l)?, recurse_box(r)?)),
        Formula::Ge(l, r) => Ok(Formula::Ge(recurse_box(l)?, recurse_box(r)?)),

        // Integer arithmetic
        Formula::Add(l, r) => Ok(Formula::Add(recurse_box(l)?, recurse_box(r)?)),
        Formula::Sub(l, r) => Ok(Formula::Sub(recurse_box(l)?, recurse_box(r)?)),
        Formula::Mul(l, r) => Ok(Formula::Mul(recurse_box(l)?, recurse_box(r)?)),
        Formula::Div(l, r) => Ok(Formula::Div(recurse_box(l)?, recurse_box(r)?)),
        Formula::Rem(l, r) => Ok(Formula::Rem(recurse_box(l)?, recurse_box(r)?)),
        Formula::Neg(inner) => Ok(Formula::Neg(recurse_box(inner)?)),

        // Bitvector arithmetic
        Formula::BvAdd(l, r, w) => Ok(Formula::BvAdd(recurse_box(l)?, recurse_box(r)?, *w)),
        Formula::BvSub(l, r, w) => Ok(Formula::BvSub(recurse_box(l)?, recurse_box(r)?, *w)),
        Formula::BvMul(l, r, w) => Ok(Formula::BvMul(recurse_box(l)?, recurse_box(r)?, *w)),
        Formula::BvUDiv(l, r, w) => Ok(Formula::BvUDiv(recurse_box(l)?, recurse_box(r)?, *w)),
        Formula::BvSDiv(l, r, w) => Ok(Formula::BvSDiv(recurse_box(l)?, recurse_box(r)?, *w)),
        Formula::BvURem(l, r, w) => Ok(Formula::BvURem(recurse_box(l)?, recurse_box(r)?, *w)),
        Formula::BvSRem(l, r, w) => Ok(Formula::BvSRem(recurse_box(l)?, recurse_box(r)?, *w)),
        Formula::BvAnd(l, r, w) => Ok(Formula::BvAnd(recurse_box(l)?, recurse_box(r)?, *w)),
        Formula::BvOr(l, r, w) => Ok(Formula::BvOr(recurse_box(l)?, recurse_box(r)?, *w)),
        Formula::BvXor(l, r, w) => Ok(Formula::BvXor(recurse_box(l)?, recurse_box(r)?, *w)),
        Formula::BvNot(inner, w) => Ok(Formula::BvNot(recurse_box(inner)?, *w)),
        Formula::BvShl(l, r, w) => Ok(Formula::BvShl(recurse_box(l)?, recurse_box(r)?, *w)),
        Formula::BvLShr(l, r, w) => Ok(Formula::BvLShr(recurse_box(l)?, recurse_box(r)?, *w)),
        Formula::BvAShr(l, r, w) => Ok(Formula::BvAShr(recurse_box(l)?, recurse_box(r)?, *w)),

        // Bitvector comparisons
        Formula::BvULt(l, r, w) => Ok(Formula::BvULt(recurse_box(l)?, recurse_box(r)?, *w)),
        Formula::BvULe(l, r, w) => Ok(Formula::BvULe(recurse_box(l)?, recurse_box(r)?, *w)),
        Formula::BvSLt(l, r, w) => Ok(Formula::BvSLt(recurse_box(l)?, recurse_box(r)?, *w)),
        Formula::BvSLe(l, r, w) => Ok(Formula::BvSLe(recurse_box(l)?, recurse_box(r)?, *w)),

        // Bitvector conversions
        Formula::BvToInt(inner, w, signed) => {
            Ok(Formula::BvToInt(recurse_box(inner)?, *w, *signed))
        }
        Formula::IntToBv(inner, w) => Ok(Formula::IntToBv(recurse_box(inner)?, *w)),
        Formula::BvExtract { inner, high, low } => {
            Ok(Formula::BvExtract { inner: recurse_box(inner)?, high: *high, low: *low })
        }
        Formula::BvConcat(l, r) => Ok(Formula::BvConcat(recurse_box(l)?, recurse_box(r)?)),
        Formula::BvZeroExt(inner, w) => Ok(Formula::BvZeroExt(recurse_box(inner)?, *w)),
        Formula::BvSignExt(inner, w) => Ok(Formula::BvSignExt(recurse_box(inner)?, *w)),

        // Conditional
        Formula::Ite(cond, then, els) => {
            Ok(Formula::Ite(recurse_box(cond)?, recurse_box(then)?, recurse_box(els)?))
        }

        // Quantifiers: capture-avoiding substitution.
        Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
            let bound_names: FxHashSet<&str> = bindings.iter().map(|(n, _)| n.as_str()).collect();

            // Check for capture: if any replacement formula contains a free variable
            // that is bound by this quantifier, we have capture.
            for (var_name, replacement) in &map.mappings {
                if bound_names.contains(var_name.as_str()) {
                    // Variable is shadowed by the quantifier -- skip it.
                    continue;
                }
                let free_in_replacement = free_variables(replacement);
                for bound in &bound_names {
                    if free_in_replacement.contains(*bound) {
                        return Err(SubstitutionError::VariableCapture {
                            captured: bound.to_string(),
                            binder: bound.to_string(),
                        });
                    }
                }
            }

            // Build a restricted map that excludes bound variables.
            let mut restricted = SubstitutionMap::new();
            for (name, replacement) in &map.mappings {
                if !bound_names.contains(name.as_str()) {
                    let sort = map.sorts.get(name).cloned().unwrap_or(Sort::Int);
                    restricted.insert(name.clone(), sort, replacement.clone());
                }
            }

            let new_body = substitute_inner(body, &restricted, depth + 1, max_depth)?;
            match formula {
                Formula::Forall(..) => Ok(Formula::Forall(bindings.clone(), Box::new(new_body))),
                Formula::Exists(..) => Ok(Formula::Exists(bindings.clone(), Box::new(new_body))),
                _ => unreachable!(
                    "quantifier branch only matches Formula::Forall or Formula::Exists"
                ),
            }
        }

        // Arrays
        Formula::Select(arr, idx) => Ok(Formula::Select(recurse_box(arr)?, recurse_box(idx)?)),
        Formula::Store(arr, idx, val) => {
            Ok(Formula::Store(recurse_box(arr)?, recurse_box(idx)?, recurse_box(val)?))
        }
        _ => Ok(formula.clone()),
    }
}

/// Collect all free variables in a formula.
///
/// Delegates to `Formula::free_variables()` from trust-types.
#[must_use]
pub fn free_variables(formula: &Formula) -> FxHashSet<String> {
    formula.free_variables()
}

/// Simplify a formula by applying basic algebraic identities.
///
/// This is a shallow, single-pass simplifier that handles common patterns:
/// - `And([])` -> `Bool(true)`, `Or([])` -> `Bool(false)`
/// - `And([x])` -> `x`, `Or([x])` -> `x`
/// - `Not(Bool(b))` -> `Bool(!b)`
/// - `Not(Not(x))` -> `x`
/// - `And` / `Or` flattening and constant folding
/// - `Implies(Bool(true), x)` -> `x`
/// - `Eq(x, x)` -> `Bool(true)` for literals
#[must_use]
pub fn simplify(formula: &Formula) -> Formula {
    match formula {
        Formula::Not(inner) => {
            let inner_s = simplify(inner);
            match inner_s {
                Formula::Bool(b) => Formula::Bool(!b),
                Formula::Not(inner2) => *inner2,
                other => Formula::Not(Box::new(other)),
            }
        }

        Formula::And(conjuncts) => {
            let simplified: Vec<Formula> = conjuncts
                .iter()
                .map(simplify)
                .flat_map(|f| {
                    // Flatten nested And
                    if let Formula::And(inner) = f { inner } else { vec![f] }
                })
                .filter(|f| !matches!(f, Formula::Bool(true)))
                .collect();

            // If any conjunct is false, the whole thing is false.
            if simplified.iter().any(|f| matches!(f, Formula::Bool(false))) {
                return Formula::Bool(false);
            }
            match simplified.len() {
                0 => Formula::Bool(true),
                1 =>
                // SAFETY: match arm guarantees len == 1, so .next() returns Some.
                {
                    simplified
                        .into_iter()
                        .next()
                        .unwrap_or_else(|| unreachable!("empty iter despite len == 1"))
                }
                _ => Formula::And(simplified),
            }
        }

        Formula::Or(disjuncts) => {
            let simplified: Vec<Formula> = disjuncts
                .iter()
                .map(simplify)
                .flat_map(|f| if let Formula::Or(inner) = f { inner } else { vec![f] })
                .filter(|f| !matches!(f, Formula::Bool(false)))
                .collect();

            if simplified.iter().any(|f| matches!(f, Formula::Bool(true))) {
                return Formula::Bool(true);
            }
            match simplified.len() {
                0 => Formula::Bool(false),
                1 =>
                // SAFETY: match arm guarantees len == 1, so .next() returns Some.
                {
                    simplified
                        .into_iter()
                        .next()
                        .unwrap_or_else(|| unreachable!("empty iter despite len == 1"))
                }
                _ => Formula::Or(simplified),
            }
        }

        Formula::Implies(lhs, rhs) => {
            let lhs_s = simplify(lhs);
            let rhs_s = simplify(rhs);
            match (&lhs_s, &rhs_s) {
                (Formula::Bool(true), _) => rhs_s,
                (Formula::Bool(false), _) => Formula::Bool(true),
                (_, Formula::Bool(true)) => Formula::Bool(true),
                _ => Formula::Implies(Box::new(lhs_s), Box::new(rhs_s)),
            }
        }

        Formula::Eq(l, r) => {
            let l_s = simplify(l);
            let r_s = simplify(r);
            if l_s == r_s { Formula::Bool(true) } else { Formula::Eq(Box::new(l_s), Box::new(r_s)) }
        }

        // For all other formulas, just recurse and rebuild.
        _ => formula.clone(),
    }
}

/// Rename a free variable throughout a formula (alpha-conversion).
///
/// Replaces all free occurrences of `old_name` with `new_name`, preserving
/// the same sort.
///
/// # Errors
///
/// Returns `SubstitutionError::VariableCapture` when `new_name` is bound by an
/// enclosing quantifier, or any structural substitution error.
pub fn rename_variable(
    formula: &Formula,
    old_name: &str,
    new_name: &str,
) -> Result<Formula, SubstitutionError> {
    if old_name == new_name {
        return Ok(formula.clone());
    }
    let Some(sort) = infer_var_sort(formula, old_name) else { return Ok(formula.clone()) };
    let mut map = SubstitutionMap::new();
    map.insert(old_name, sort.clone(), Formula::Var(new_name.to_string(), sort));
    substitute(formula, &map)
}

/// Infer the sort of a variable by finding its first occurrence in a formula.
fn infer_var_sort(formula: &Formula, var_name: &str) -> Option<Sort> {
    match formula {
        Formula::Var(name, sort) if name == var_name => Some(sort.clone()),
        Formula::Not(inner)
        | Formula::Neg(inner)
        | Formula::BvNot(inner, _)
        | Formula::BvToInt(inner, _, _)
        | Formula::IntToBv(inner, _)
        | Formula::BvZeroExt(inner, _)
        | Formula::BvSignExt(inner, _) => infer_var_sort(inner, var_name),
        Formula::BvExtract { inner, .. } => infer_var_sort(inner, var_name),

        Formula::And(fs) | Formula::Or(fs) => fs.iter().find_map(|f| infer_var_sort(f, var_name)),

        Formula::Implies(l, r)
        | Formula::Eq(l, r)
        | Formula::Lt(l, r)
        | Formula::Le(l, r)
        | Formula::Gt(l, r)
        | Formula::Ge(l, r)
        | Formula::Add(l, r)
        | Formula::Sub(l, r)
        | Formula::Mul(l, r)
        | Formula::Div(l, r)
        | Formula::Rem(l, r)
        | Formula::BvConcat(l, r)
        | Formula::Select(l, r) => {
            infer_var_sort(l, var_name).or_else(|| infer_var_sort(r, var_name))
        }

        Formula::BvAdd(l, r, _)
        | Formula::BvSub(l, r, _)
        | Formula::BvMul(l, r, _)
        | Formula::BvUDiv(l, r, _)
        | Formula::BvSDiv(l, r, _)
        | Formula::BvURem(l, r, _)
        | Formula::BvSRem(l, r, _)
        | Formula::BvAnd(l, r, _)
        | Formula::BvOr(l, r, _)
        | Formula::BvXor(l, r, _)
        | Formula::BvShl(l, r, _)
        | Formula::BvLShr(l, r, _)
        | Formula::BvAShr(l, r, _)
        | Formula::BvULt(l, r, _)
        | Formula::BvULe(l, r, _)
        | Formula::BvSLt(l, r, _)
        | Formula::BvSLe(l, r, _) => {
            infer_var_sort(l, var_name).or_else(|| infer_var_sort(r, var_name))
        }

        Formula::Ite(c, t, e) | Formula::Store(c, t, e) => infer_var_sort(c, var_name)
            .or_else(|| infer_var_sort(t, var_name))
            .or_else(|| infer_var_sort(e, var_name)),

        Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
            // Check bindings first.
            for (name, sort) in bindings {
                if name == var_name {
                    return Some(sort.clone());
                }
            }
            infer_var_sort(body, var_name)
        }

        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(name: &str, sort: Sort) -> Formula {
        Formula::Var(name.to_string(), sort)
    }

    fn int_var(name: &str) -> Formula {
        var(name, Sort::Int)
    }

    fn bv64_var(name: &str) -> Formula {
        var(name, Sort::BitVec(64))
    }

    // --- SubstitutionMap tests ---

    #[test]
    fn test_substitution_map_new_is_empty() {
        let map = SubstitutionMap::new();
        assert!(map.is_empty());
        assert_eq!(map.len(), 0);
    }

    #[test]
    fn test_substitution_map_insert_and_get() {
        let mut map = SubstitutionMap::new();
        map.insert("x", Sort::Int, Formula::Int(42));
        assert_eq!(map.len(), 1);
        assert!(!map.is_empty());
        assert_eq!(map.get("x"), Some(&Formula::Int(42)));
        assert_eq!(map.get("y"), None);
    }

    #[test]
    fn test_substitution_map_from_params_and_args() {
        let params = vec![("a".to_string(), Sort::Int), ("b".to_string(), Sort::Int)];
        let args = vec![int_var("x"), int_var("y")];
        let map = SubstitutionMap::from_params_and_args(&params, &args).expect("should build map");
        assert_eq!(map.len(), 2);
        assert_eq!(map.get("a"), Some(&int_var("x")));
        assert_eq!(map.get("b"), Some(&int_var("y")));
    }

    #[test]
    fn test_substitution_map_from_params_and_args_sort_mismatch() {
        let params = vec![("a".to_string(), Sort::Bool)];
        let args = vec![int_var("x")];
        let result = SubstitutionMap::from_params_and_args(&params, &args);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            SubstitutionError::SortMismatch { name, .. } if name == "a"
        ));
    }

    #[test]
    fn test_substitution_map_rejects_literal_sort_mismatch() {
        let params = vec![("flag".to_string(), Sort::Bool)];
        let error = SubstitutionMap::from_params_and_args(&params, &[Formula::Int(1)]).unwrap_err();
        assert!(matches!(
            error,
            SubstitutionError::SortMismatch { expected: Sort::Bool, actual: Sort::Int, .. }
        ));
    }

    #[test]
    fn test_substitution_map_rejects_implicit_int_bitvec_coercions() {
        let int_param = vec![("x".to_string(), Sort::Int)];
        let bv_param = vec![("x".to_string(), Sort::BitVec(64))];

        assert!(matches!(
            SubstitutionMap::from_params_and_args(&int_param, &[bv64_var("arg")]),
            Err(SubstitutionError::SortMismatch { .. })
        ));
        assert!(matches!(
            SubstitutionMap::from_params_and_args(&bv_param, &[Formula::Int(1)]),
            Err(SubstitutionError::SortMismatch { .. })
        ));
    }

    #[test]
    fn test_substitution_map_rejects_fewer_args_than_params() {
        let params = vec![("a".to_string(), Sort::Int), ("b".to_string(), Sort::Int)];
        let args = vec![int_var("x")];
        let error = SubstitutionMap::from_params_and_args(&params, &args).unwrap_err();
        assert!(matches!(error, SubstitutionError::ArityMismatch { expected: 2, actual: 1 }));
    }

    #[test]
    fn test_substitution_map_variables() {
        let mut map = SubstitutionMap::new();
        map.insert("x", Sort::Int, Formula::Int(1));
        map.insert("y", Sort::Int, Formula::Int(2));
        let vars = map.variables();
        assert!(vars.contains("x"));
        assert!(vars.contains("y"));
        assert_eq!(vars.len(), 2);
    }

    // --- substitute tests ---

    #[test]
    fn test_substitute_literal_unchanged() {
        let map = SubstitutionMap::new();
        let f = Formula::Int(42);
        let result = substitute(&f, &map).expect("should succeed");
        assert_eq!(result, Formula::Int(42));
    }

    #[test]
    fn test_substitute_bool_unchanged() {
        let map = SubstitutionMap::new();
        let f = Formula::Bool(true);
        let result = substitute(&f, &map).expect("should succeed");
        assert_eq!(result, Formula::Bool(true));
    }

    #[test]
    fn test_substitute_variable_in_map() {
        let mut map = SubstitutionMap::new();
        map.insert("x", Sort::Int, Formula::Int(42));
        let f = int_var("x");
        let result = substitute(&f, &map).expect("should succeed");
        assert_eq!(result, Formula::Int(42));
    }

    #[test]
    fn test_substitute_variable_not_in_map() {
        let map = SubstitutionMap::new();
        let f = int_var("y");
        let result = substitute(&f, &map).expect("should succeed");
        assert_eq!(result, int_var("y"));
    }

    #[test]
    fn test_substitute_in_addition() {
        let mut map = SubstitutionMap::new();
        map.insert("a", Sort::Int, int_var("x"));
        map.insert("b", Sort::Int, int_var("y"));
        let f = Formula::Add(Box::new(int_var("a")), Box::new(int_var("b")));
        let result = substitute(&f, &map).expect("should succeed");
        assert_eq!(result, Formula::Add(Box::new(int_var("x")), Box::new(int_var("y"))));
    }

    #[test]
    fn test_substitute_in_comparison() {
        let mut map = SubstitutionMap::new();
        map.insert("n", Sort::Int, Formula::Int(10));
        // n > 0 => 10 > 0
        let f = Formula::Gt(Box::new(int_var("n")), Box::new(Formula::Int(0)));
        let result = substitute(&f, &map).expect("should succeed");
        assert_eq!(result, Formula::Gt(Box::new(Formula::Int(10)), Box::new(Formula::Int(0))));
    }

    #[test]
    fn test_substitute_in_not() {
        let mut map = SubstitutionMap::new();
        map.insert("p", Sort::Bool, Formula::Bool(true));
        let f = Formula::Not(Box::new(var("p", Sort::Bool)));
        let result = substitute(&f, &map).expect("should succeed");
        assert_eq!(result, Formula::Not(Box::new(Formula::Bool(true))));
    }

    #[test]
    fn test_substitute_in_and() {
        let mut map = SubstitutionMap::new();
        map.insert("x", Sort::Int, Formula::Int(5));
        let f = Formula::And(vec![
            Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(100))),
        ]);
        let result = substitute(&f, &map).expect("should succeed");
        assert_eq!(
            result,
            Formula::And(vec![
                Formula::Gt(Box::new(Formula::Int(5)), Box::new(Formula::Int(0))),
                Formula::Lt(Box::new(Formula::Int(5)), Box::new(Formula::Int(100))),
            ])
        );
    }

    #[test]
    fn test_substitute_in_implies() {
        let mut map = SubstitutionMap::new();
        map.insert("a", Sort::Int, int_var("caller_a"));
        let f = Formula::Implies(
            Box::new(Formula::Gt(Box::new(int_var("a")), Box::new(Formula::Int(0)))),
            Box::new(Formula::Bool(true)),
        );
        let result = substitute(&f, &map).expect("should succeed");
        assert_eq!(
            result,
            Formula::Implies(
                Box::new(Formula::Gt(Box::new(int_var("caller_a")), Box::new(Formula::Int(0)))),
                Box::new(Formula::Bool(true)),
            )
        );
    }

    #[test]
    fn test_substitute_in_ite() {
        let mut map = SubstitutionMap::new();
        map.insert("c", Sort::Bool, Formula::Bool(false));
        let f = Formula::Ite(
            Box::new(var("c", Sort::Bool)),
            Box::new(Formula::Int(1)),
            Box::new(Formula::Int(2)),
        );
        let result = substitute(&f, &map).expect("should succeed");
        assert_eq!(
            result,
            Formula::Ite(
                Box::new(Formula::Bool(false)),
                Box::new(Formula::Int(1)),
                Box::new(Formula::Int(2)),
            )
        );
    }

    #[test]
    fn test_substitute_respects_quantifier_binding() {
        // forall x. x > 0 -- substituting x -> 42 should NOT affect bound x
        let mut map = SubstitutionMap::new();
        map.insert("x", Sort::Int, Formula::Int(42));
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(0)))),
        );
        let result = substitute(&f, &map).expect("should succeed");
        // x is bound, so no substitution inside
        assert_eq!(result, f);
    }

    #[test]
    fn test_substitute_rejects_unhandled_composite_that_retains_mapped_variable() {
        let float_sort = Sort::Float { eb: 8, sb: 24 };
        let formula = Formula::FpNeg(Box::new(Formula::Var("x".into(), float_sort.clone())));
        let mut map = SubstitutionMap::new();
        map.insert("x", float_sort.clone(), Formula::Var("y".into(), float_sort));

        let error = substitute(&formula, &map).unwrap_err();

        assert!(matches!(
            error,
            SubstitutionError::IncompleteSubstitution { name } if name == "x"
        ));
    }

    #[test]
    fn test_substitute_capture_detection() {
        // forall y. (x + y > 0) with x -> y+1
        // This should detect capture: y in the replacement would be captured.
        let mut map = SubstitutionMap::new();
        map.insert("x", Sort::Int, Formula::Add(Box::new(int_var("y")), Box::new(Formula::Int(1))));
        let f = Formula::Forall(
            vec![("y".into(), Sort::Int)],
            Box::new(Formula::Gt(
                Box::new(Formula::Add(Box::new(int_var("x")), Box::new(int_var("y")))),
                Box::new(Formula::Int(0)),
            )),
        );
        let result = substitute(&f, &map);
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), SubstitutionError::VariableCapture { .. }));
    }

    #[test]
    fn test_substitute_depth_exceeded() {
        // Create a deeply nested formula to trigger depth limit.
        let mut map = SubstitutionMap::new();
        map.insert("x", Sort::Int, Formula::Int(1));
        let mut f = int_var("x");
        for _ in 0..5 {
            f = Formula::Not(Box::new(f));
        }
        let result = substitute_with_depth(&f, &map, 3);
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), SubstitutionError::DepthExceeded { limit: 3 }));
    }

    #[test]
    fn test_substitute_bitvector_ops() {
        let mut map = SubstitutionMap::new();
        map.insert("a", Sort::BitVec(64), bv64_var("x"));
        map.insert("b", Sort::BitVec(64), bv64_var("y"));
        let f = Formula::BvAdd(Box::new(bv64_var("a")), Box::new(bv64_var("b")), 64);
        let result = substitute(&f, &map).expect("should succeed");
        assert_eq!(result, Formula::BvAdd(Box::new(bv64_var("x")), Box::new(bv64_var("y")), 64));
    }

    #[test]
    fn test_substitute_in_select_store() {
        let mut map = SubstitutionMap::new();
        let arr_sort = Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int));
        map.insert(
            "arr",
            arr_sort,
            var("my_array", Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int))),
        );
        map.insert("idx", Sort::Int, Formula::Int(3));

        let f = Formula::Select(
            Box::new(var("arr", Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)))),
            Box::new(int_var("idx")),
        );
        let result = substitute(&f, &map).expect("should succeed");
        assert_eq!(
            result,
            Formula::Select(
                Box::new(var("my_array", Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)))),
                Box::new(Formula::Int(3)),
            )
        );
    }

    // --- free_variables tests ---

    #[test]
    fn test_free_variables_literal() {
        assert!(free_variables(&Formula::Int(42)).is_empty());
        assert!(free_variables(&Formula::Bool(true)).is_empty());
    }

    #[test]
    fn test_free_variables_var() {
        let vars = free_variables(&int_var("x"));
        assert_eq!(vars.len(), 1);
        assert!(vars.contains("x"));
    }

    #[test]
    fn test_free_variables_bound_not_free() {
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(0)))),
        );
        let vars = free_variables(&f);
        assert!(vars.is_empty());
    }

    #[test]
    fn test_free_variables_mixed_bound_and_free() {
        // forall x. (x + y > 0) -- y is free, x is bound
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Gt(
                Box::new(Formula::Add(Box::new(int_var("x")), Box::new(int_var("y")))),
                Box::new(Formula::Int(0)),
            )),
        );
        let vars = free_variables(&f);
        assert_eq!(vars.len(), 1);
        assert!(vars.contains("y"));
    }

    #[test]
    fn test_free_variables_nested_quantifiers() {
        // forall x. exists y. (x + y + z > 0) -- z is free
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Exists(
                vec![("y".into(), Sort::Int)],
                Box::new(Formula::Gt(
                    Box::new(Formula::Add(
                        Box::new(Formula::Add(Box::new(int_var("x")), Box::new(int_var("y")))),
                        Box::new(int_var("z")),
                    )),
                    Box::new(Formula::Int(0)),
                )),
            )),
        );
        let vars = free_variables(&f);
        assert_eq!(vars.len(), 1);
        assert!(vars.contains("z"));
    }

    // --- simplify tests ---

    #[test]
    fn test_simplify_and_empty() {
        assert_eq!(simplify(&Formula::And(vec![])), Formula::Bool(true));
    }

    #[test]
    fn test_simplify_or_empty() {
        assert_eq!(simplify(&Formula::Or(vec![])), Formula::Bool(false));
    }

    #[test]
    fn test_simplify_and_singleton() {
        let f = Formula::And(vec![int_var("x")]);
        assert_eq!(simplify(&f), int_var("x"));
    }

    #[test]
    fn test_simplify_or_singleton() {
        let f = Formula::Or(vec![int_var("x")]);
        assert_eq!(simplify(&f), int_var("x"));
    }

    #[test]
    fn test_simplify_not_bool() {
        assert_eq!(simplify(&Formula::Not(Box::new(Formula::Bool(true)))), Formula::Bool(false));
        assert_eq!(simplify(&Formula::Not(Box::new(Formula::Bool(false)))), Formula::Bool(true));
    }

    #[test]
    fn test_simplify_double_not() {
        let f = Formula::Not(Box::new(Formula::Not(Box::new(int_var("x")))));
        assert_eq!(simplify(&f), int_var("x"));
    }

    #[test]
    fn test_simplify_and_with_true() {
        let f = Formula::And(vec![Formula::Bool(true), int_var("x"), Formula::Bool(true)]);
        assert_eq!(simplify(&f), int_var("x"));
    }

    #[test]
    fn test_simplify_and_with_false() {
        let f = Formula::And(vec![int_var("x"), Formula::Bool(false)]);
        assert_eq!(simplify(&f), Formula::Bool(false));
    }

    #[test]
    fn test_simplify_or_with_true() {
        let f = Formula::Or(vec![int_var("x"), Formula::Bool(true)]);
        assert_eq!(simplify(&f), Formula::Bool(true));
    }

    #[test]
    fn test_simplify_or_with_false() {
        let f = Formula::Or(vec![Formula::Bool(false), int_var("x"), Formula::Bool(false)]);
        assert_eq!(simplify(&f), int_var("x"));
    }

    #[test]
    fn test_simplify_implies_true_lhs() {
        let f = Formula::Implies(Box::new(Formula::Bool(true)), Box::new(int_var("x")));
        assert_eq!(simplify(&f), int_var("x"));
    }

    #[test]
    fn test_simplify_implies_false_lhs() {
        let f = Formula::Implies(Box::new(Formula::Bool(false)), Box::new(int_var("x")));
        assert_eq!(simplify(&f), Formula::Bool(true));
    }

    #[test]
    fn test_simplify_implies_true_rhs() {
        let f = Formula::Implies(Box::new(int_var("x")), Box::new(Formula::Bool(true)));
        assert_eq!(simplify(&f), Formula::Bool(true));
    }

    #[test]
    fn test_simplify_eq_same_literal() {
        let f = Formula::Eq(Box::new(Formula::Int(5)), Box::new(Formula::Int(5)));
        assert_eq!(simplify(&f), Formula::Bool(true));
    }

    #[test]
    fn test_simplify_eq_same_var() {
        let f = Formula::Eq(Box::new(int_var("x")), Box::new(int_var("x")));
        assert_eq!(simplify(&f), Formula::Bool(true));
    }

    #[test]
    fn test_simplify_nested_and_flattening() {
        // And(And(a, b), c) -> And(a, b, c)
        let f = Formula::And(vec![Formula::And(vec![int_var("a"), int_var("b")]), int_var("c")]);
        let result = simplify(&f);
        assert_eq!(result, Formula::And(vec![int_var("a"), int_var("b"), int_var("c")]));
    }

    // --- rename_variable tests ---

    #[test]
    fn test_rename_variable_simple() {
        let f = int_var("x");
        let result = rename_variable(&f, "x", "y").unwrap();
        assert_eq!(result, int_var("y"));
    }

    #[test]
    fn test_rename_variable_not_present() {
        let f = int_var("x");
        let result = rename_variable(&f, "z", "w").unwrap();
        assert_eq!(result, int_var("x"));
    }

    #[test]
    fn test_rename_variable_in_addition() {
        let f = Formula::Add(Box::new(int_var("x")), Box::new(int_var("y")));
        let result = rename_variable(&f, "x", "a").unwrap();
        assert_eq!(result, Formula::Add(Box::new(int_var("a")), Box::new(int_var("y"))));
    }

    #[test]
    fn test_rename_respects_binding() {
        // forall x. x > 0 -- renaming x to y should not affect the bound x
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(0)))),
        );
        let result = rename_variable(&f, "x", "y").unwrap();
        assert_eq!(result, f); // unchanged
    }

    #[test]
    fn test_rename_rejects_capture_by_enclosing_quantifier() {
        let f = Formula::Forall(
            vec![("y".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(int_var("x")), Box::new(int_var("y")))),
        );

        let error = rename_variable(&f, "x", "y").unwrap_err();

        assert!(
            matches!(error, SubstitutionError::VariableCapture { captured, .. } if captured == "y")
        );
    }

    // --- infer_var_sort tests ---

    #[test]
    fn test_infer_var_sort_found() {
        let f = Formula::Add(Box::new(bv64_var("x")), Box::new(Formula::Int(1)));
        assert_eq!(infer_var_sort(&f, "x"), Some(Sort::BitVec(64)));
    }

    #[test]
    fn test_infer_var_sort_not_found() {
        let f = Formula::Int(42);
        assert_eq!(infer_var_sort(&f, "x"), None);
    }
}
