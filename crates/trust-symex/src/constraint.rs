// trust-symex constraint management
//
// Provides constraint set operations for path constraint solving:
// accumulation, simplification, feasibility checking, and independence
// splitting (inspired by KLEE's constraint independence optimization,
// refs/klee/lib/Solver/).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use trust_types::Formula;

use crate::path::{PathConstraint, symbolic_to_formula};
use crate::state::SymbolicValue;

/// Result of a feasibility check on a constraint set.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum FeasibilityResult {
    /// The constraints are satisfiable (a model exists).
    Feasible,
    /// The constraints are unsatisfiable (no model can satisfy them).
    Infeasible,
    /// Feasibility could not be determined (e.g., timeout or approximation).
    Unknown,
}

/// An accumulator of path constraints with efficient operations.
///
/// Wraps a `Vec<Formula>` and provides simplification, feasibility
/// checking, and independence-based splitting.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ConstraintSet {
    constraints: Vec<Formula>,
}

impl ConstraintSet {
    /// Create an empty constraint set.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Build a `ConstraintSet` from an existing `PathConstraint`.
    #[must_use]
    pub fn from_path(path: &PathConstraint) -> Self {
        // (P1-18): Include both decisions and auxiliary formulas.
        let mut constraints: Vec<Formula> = path
            .decisions()
            .iter()
            .map(|d| {
                let f = symbolic_to_formula(&d.condition);
                if d.taken { f } else { Formula::Not(Box::new(f)) }
            })
            .collect();
        // Auxiliary formulas encode additional path constraints (e.g., memory
        // invariants, type guards) that are not branch decisions but must be
        // included in the constraint set for soundness.
        constraints.extend(path.auxiliary().iter().cloned());
        Self { constraints }
    }

    /// Add a formula to the constraint set.
    pub fn add(&mut self, formula: Formula) {
        self.constraints.push(formula);
    }

    /// Add a symbolic value as a constraint (asserted true).
    pub fn add_symbolic(&mut self, value: &SymbolicValue, taken: bool) {
        let f = symbolic_to_formula(value);
        if taken {
            self.constraints.push(f);
        } else {
            self.constraints.push(Formula::Not(Box::new(f)));
        }
    }

    /// Returns the number of constraints.
    #[must_use]
    pub fn len(&self) -> usize {
        self.constraints.len()
    }

    /// Returns `true` if the set contains no constraints.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.constraints.is_empty()
    }

    /// Access the underlying formulas.
    #[must_use]
    pub fn formulas(&self) -> &[Formula] {
        &self.constraints
    }

    /// Convert the entire set to a single conjunction formula.
    #[must_use]
    pub fn to_conjunction(&self) -> Formula {
        match self.constraints.len() {
            0 => Formula::Bool(true),
            1 => self.constraints[0].clone(),
            _ => Formula::And(self.constraints.clone()),
        }
    }
}

/// Remove trivially redundant constraints from a formula slice.
///
/// Current simplifications:
/// - Remove `Bool(true)` (tautologies).
/// - Detect `Bool(false)` (contradiction) and return `[Bool(false)]`.
/// - Deduplicate identical formulas.
/// - Flatten nested `And` at the top level.
#[must_use]
pub fn simplify_constraints(constraints: &[Formula]) -> Vec<Formula> {
    let mut result: Vec<Formula> = Vec::new();
    let mut seen: BTreeSet<String> = BTreeSet::default();

    for c in constraints {
        // Flatten nested And.
        let flattened = flatten_and(c);
        for f in flattened {
            // Skip tautologies.
            if f == Formula::Bool(true) {
                continue;
            }
            // Contradiction: short-circuit.
            if f == Formula::Bool(false) {
                return vec![Formula::Bool(false)];
            }
            // Deduplicate via debug representation (structural equality).
            let key = format!("{f:?}");
            if seen.insert(key) {
                result.push(f);
            }
        }
    }

    if result.is_empty() { vec![Formula::Bool(true)] } else { result }
}

/// Flatten top-level `And` nodes into a flat list.
fn flatten_and(f: &Formula) -> Vec<Formula> {
    match f {
        Formula::And(children) => children.iter().flat_map(flatten_and).collect(),
        other => vec![other.clone()],
    }
}

/// Quick feasibility check using syntactic analysis.
///
/// This does NOT invoke an SMT solver; it detects trivially infeasible
/// or trivially feasible constraint sets. Returns `Unknown` when the
/// structure is non-trivial and a solver call is needed.
#[must_use]
pub fn check_feasibility(constraints: &ConstraintSet) -> FeasibilityResult {
    if constraints.is_empty() {
        return FeasibilityResult::Feasible;
    }

    let simplified = simplify_constraints(constraints.formulas());

    // A single Bool(false) means infeasible.
    if simplified.len() == 1 && simplified[0] == Formula::Bool(false) {
        return FeasibilityResult::Infeasible;
    }

    // All tautologies means feasible.
    if simplified.len() == 1 && simplified[0] == Formula::Bool(true) {
        return FeasibilityResult::Feasible;
    }

    // Check for direct contradictions: X and Not(X) both present.
    let mut pos: BTreeSet<String> = BTreeSet::default();
    let mut neg: BTreeSet<String> = BTreeSet::default();
    for f in &simplified {
        let key = format!("{f:?}");
        match f {
            Formula::Not(inner) => {
                let inner_key = format!("{inner:?}");
                neg.insert(inner_key.clone());
                if pos.contains(&inner_key) {
                    return FeasibilityResult::Infeasible;
                }
            }
            _ => {
                pos.insert(key);
                let neg_key = format!("{f:?}");
                if neg.contains(&neg_key) {
                    return FeasibilityResult::Infeasible;
                }
            }
        }
    }

    FeasibilityResult::Unknown
}

/// Split a constraint set into independent subsets based on shared variables.
///
/// Two constraints are in the same group if they share at least one free
/// variable. This is a union-find based partitioning inspired by KLEE's
/// constraint independence optimisation (refs/klee/lib/Solver/).
///
/// Splitting allows each independent group to be solved separately,
/// reducing solver complexity from O(2^n) to O(sum(2^k_i)) where k_i
/// are the group sizes.
#[must_use]
pub fn independence_splitting(constraints: &ConstraintSet) -> Vec<ConstraintSet> {
    if constraints.is_empty() {
        return vec![];
    }

    let formulas = constraints.formulas();
    let n = formulas.len();

    // Collect free variables for each constraint.
    let vars_per_constraint: Vec<BTreeSet<String>> = formulas.iter().map(collect_vars).collect();

    // Union-find: group constraints that share variables.
    let mut parent: Vec<usize> = (0..n).collect();

    for i in 0..n {
        for j in (i + 1)..n {
            if !vars_per_constraint[i].is_disjoint(&vars_per_constraint[j]) {
                union(&mut parent, i, j);
            }
        }
    }

    // Group constraints by their root.
    let mut groups: BTreeMap<usize, Vec<Formula>> = BTreeMap::default();
    for (i, f) in formulas.iter().enumerate() {
        let root = find(&mut parent, i);
        groups.entry(root).or_default().push(f.clone());
    }

    // Build output ConstraintSets in a deterministic order.
    let mut roots: Vec<usize> = groups.keys().copied().collect();
    roots.sort_unstable();

    roots
        .into_iter()
        .map(|root| {
            let mut cs = ConstraintSet::new();
            // SAFETY: root came from groups.keys(), so it must exist in the map.
            for f in groups.remove(&root).unwrap_or_else(|| unreachable!("root key not in groups"))
            {
                cs.add(f);
            }
            cs
        })
        .collect()
}

/// Collect all variable names occurring in a formula.
fn collect_vars(f: &Formula) -> BTreeSet<String> {
    let mut out = BTreeSet::default();
    collect_vars_inner(f, &mut out);
    out
}

fn collect_vars_inner(f: &Formula, out: &mut BTreeSet<String>) {
    match f {
        Formula::Var(name, _) => {
            out.insert(name.clone());
        }
        // Unary wrappers.
        Formula::Not(inner)
        | Formula::Neg(inner)
        | Formula::BvNot(inner, _)
        | Formula::BvToInt(inner, _, _)
        | Formula::IntToBv(inner, _)
        | Formula::BvZeroExt(inner, _)
        | Formula::BvSignExt(inner, _) => collect_vars_inner(inner, out),
        // Variadic.
        Formula::And(children) | Formula::Or(children) => {
            for child in children {
                collect_vars_inner(child, out);
            }
        }
        // Binary (no width).
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
        | Formula::Rem(a, b)
        | Formula::BvConcat(a, b)
        | Formula::Select(a, b) => {
            collect_vars_inner(a, out);
            collect_vars_inner(b, out);
        }
        // Ternary: Ite, Store.
        Formula::Ite(c, t, e) | Formula::Store(c, t, e) => {
            collect_vars_inner(c, out);
            collect_vars_inner(t, out);
            collect_vars_inner(e, out);
        }
        // Bitvector binary ops (with width).
        Formula::BvAdd(a, b, _)
        | Formula::BvSub(a, b, _)
        | Formula::BvMul(a, b, _)
        | Formula::BvUDiv(a, b, _)
        | Formula::BvSDiv(a, b, _)
        | Formula::BvURem(a, b, _)
        | Formula::BvSRem(a, b, _)
        | Formula::BvAnd(a, b, _)
        | Formula::BvOr(a, b, _)
        | Formula::BvXor(a, b, _)
        | Formula::BvShl(a, b, _)
        | Formula::BvLShr(a, b, _)
        | Formula::BvAShr(a, b, _)
        | Formula::BvULt(a, b, _)
        | Formula::BvULe(a, b, _)
        | Formula::BvSLt(a, b, _)
        | Formula::BvSLe(a, b, _) => {
            collect_vars_inner(a, out);
            collect_vars_inner(b, out);
        }
        // BvExtract: single inner.
        Formula::BvExtract { inner, .. } => collect_vars_inner(inner, out),
        // Quantifiers: recurse into body, bound vars are not free.
        Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
            let mut inner_vars = BTreeSet::default();
            collect_vars_inner(body, &mut inner_vars);
            // Remove bound variables.
            for (name, _) in bindings {
                inner_vars.remove(name.as_str());
            }
            out.extend(inner_vars);
        }
        // Leaves with no variables.
        Formula::Bool(_) | Formula::Int(_) | Formula::UInt(_) | Formula::BitVec { .. } => {}
        _ => {}
    }
}

// Union-find helpers.

fn find(parent: &mut [usize], mut x: usize) -> usize {
    while parent[x] != x {
        parent[x] = parent[parent[x]]; // path compression
        x = parent[x];
    }
    x
}

fn union(parent: &mut [usize], a: usize, b: usize) {
    let ra = find(parent, a);
    let rb = find(parent, b);
    if ra != rb {
        // Always merge higher into lower for determinism.
        if ra < rb {
            parent[rb] = ra;
        } else {
            parent[ra] = rb;
        }
    }
}

#[cfg(test)]
mod tests {
    use trust_types::Sort;

    use super::*;
    use crate::state::SymbolicValue;

    // --- ConstraintSet basics ---

    #[test]
    fn test_constraint_set_empty() {
        let cs = ConstraintSet::new();
        assert!(cs.is_empty());
        assert_eq!(cs.len(), 0);
        assert_eq!(cs.to_conjunction(), Formula::Bool(true));
    }

    #[test]
    fn test_constraint_set_add_and_conjunction() {
        let mut cs = ConstraintSet::new();
        cs.add(Formula::Var("x".into(), Sort::Int));
        cs.add(Formula::Var("y".into(), Sort::Int));
        assert_eq!(cs.len(), 2);
        match cs.to_conjunction() {
            Formula::And(parts) => assert_eq!(parts.len(), 2),
            other => panic!("expected And, got {other:?}"),
        }
    }

    #[test]
    fn test_constraint_set_single_to_conjunction() {
        let mut cs = ConstraintSet::new();
        cs.add(Formula::Bool(true));
        // Single constraint should not be wrapped in And.
        assert_eq!(cs.to_conjunction(), Formula::Bool(true));
    }

    #[test]
    fn test_constraint_set_from_path() {
        let mut path = PathConstraint::new();
        path.add_constraint(SymbolicValue::Symbol("a".into()), true);
        path.add_constraint(SymbolicValue::Symbol("b".into()), false);
        let cs = ConstraintSet::from_path(&path);
        assert_eq!(cs.len(), 2);
    }

    #[test]
    fn test_constraint_set_add_symbolic() {
        let mut cs = ConstraintSet::new();
        cs.add_symbolic(&SymbolicValue::Symbol("x".into()), true);
        cs.add_symbolic(&SymbolicValue::Symbol("y".into()), false);
        assert_eq!(cs.len(), 2);
        // First is Var, second is Not(Var).
        match &cs.formulas()[1] {
            Formula::Not(_) => {}
            other => panic!("expected Not, got {other:?}"),
        }
    }

    // --- simplify_constraints ---

    #[test]
    fn test_simplify_removes_tautologies() {
        let constraints =
            vec![Formula::Bool(true), Formula::Var("x".into(), Sort::Int), Formula::Bool(true)];
        let result = simplify_constraints(&constraints);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0], Formula::Var("x".into(), Sort::Int));
    }

    #[test]
    fn test_simplify_detects_contradiction() {
        let constraints = vec![Formula::Var("x".into(), Sort::Int), Formula::Bool(false)];
        let result = simplify_constraints(&constraints);
        assert_eq!(result, vec![Formula::Bool(false)]);
    }

    #[test]
    fn test_simplify_deduplicates() {
        let constraints = vec![
            Formula::Var("x".into(), Sort::Int),
            Formula::Var("x".into(), Sort::Int),
            Formula::Var("y".into(), Sort::Int),
        ];
        let result = simplify_constraints(&constraints);
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn test_simplify_empty_returns_true() {
        let result = simplify_constraints(&[]);
        assert_eq!(result, vec![Formula::Bool(true)]);
    }

    #[test]
    fn test_simplify_all_tautologies_returns_true() {
        let constraints = vec![Formula::Bool(true), Formula::Bool(true)];
        let result = simplify_constraints(&constraints);
        assert_eq!(result, vec![Formula::Bool(true)]);
    }

    #[test]
    fn test_simplify_flattens_nested_and() {
        let inner = Formula::And(vec![
            Formula::Var("a".into(), Sort::Int),
            Formula::Var("b".into(), Sort::Int),
        ]);
        let constraints = vec![inner, Formula::Var("c".into(), Sort::Int)];
        let result = simplify_constraints(&constraints);
        // Should have 3 constraints: a, b, c (flattened).
        assert_eq!(result.len(), 3);
    }

    // --- check_feasibility ---

    #[test]
    fn test_feasibility_empty_is_feasible() {
        let cs = ConstraintSet::new();
        assert_eq!(check_feasibility(&cs), FeasibilityResult::Feasible);
    }

    #[test]
    fn test_feasibility_contradiction_is_infeasible() {
        let mut cs = ConstraintSet::new();
        cs.add(Formula::Bool(false));
        assert_eq!(check_feasibility(&cs), FeasibilityResult::Infeasible);
    }

    #[test]
    fn test_feasibility_tautology_is_feasible() {
        let mut cs = ConstraintSet::new();
        cs.add(Formula::Bool(true));
        assert_eq!(check_feasibility(&cs), FeasibilityResult::Feasible);
    }

    #[test]
    fn test_feasibility_direct_contradiction() {
        let mut cs = ConstraintSet::new();
        let x = Formula::Var("x".into(), Sort::Int);
        cs.add(x.clone());
        cs.add(Formula::Not(Box::new(x)));
        assert_eq!(check_feasibility(&cs), FeasibilityResult::Infeasible);
    }

    #[test]
    fn test_feasibility_unknown_for_nontrivial() {
        let mut cs = ConstraintSet::new();
        cs.add(Formula::Lt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(10)),
        ));
        assert_eq!(check_feasibility(&cs), FeasibilityResult::Unknown);
    }

    // --- independence_splitting ---

    #[test]
    fn test_splitting_empty() {
        let cs = ConstraintSet::new();
        let groups = independence_splitting(&cs);
        assert!(groups.is_empty());
    }

    #[test]
    fn test_splitting_independent_constraints() {
        let mut cs = ConstraintSet::new();
        // x < 10
        cs.add(Formula::Lt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(10)),
        ));
        // y > 5
        cs.add(Formula::Gt(
            Box::new(Formula::Var("y".into(), Sort::Int)),
            Box::new(Formula::Int(5)),
        ));
        let groups = independence_splitting(&cs);
        assert_eq!(groups.len(), 2, "x and y are independent");
        assert_eq!(groups[0].len(), 1);
        assert_eq!(groups[1].len(), 1);
    }

    #[test]
    fn test_splitting_dependent_constraints() {
        let mut cs = ConstraintSet::new();
        // x < 10
        cs.add(Formula::Lt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(10)),
        ));
        // x > 0
        cs.add(Formula::Gt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ));
        let groups = independence_splitting(&cs);
        assert_eq!(groups.len(), 1, "both constraints reference x");
        assert_eq!(groups[0].len(), 2);
    }

    #[test]
    fn test_splitting_transitive_dependency() {
        let mut cs = ConstraintSet::new();
        // x < y
        cs.add(Formula::Lt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Var("y".into(), Sort::Int)),
        ));
        // y < z
        cs.add(Formula::Lt(
            Box::new(Formula::Var("y".into(), Sort::Int)),
            Box::new(Formula::Var("z".into(), Sort::Int)),
        ));
        // w > 0 (independent of x,y,z)
        cs.add(Formula::Gt(
            Box::new(Formula::Var("w".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ));
        let groups = independence_splitting(&cs);
        assert_eq!(groups.len(), 2);
        // One group has x,y,z constraints (2), the other has w (1).
        let sizes: Vec<usize> = groups.iter().map(|g| g.len()).collect();
        assert!(sizes.contains(&2));
        assert!(sizes.contains(&1));
    }

    #[test]
    fn test_splitting_no_variables_ground_constraints() {
        let mut cs = ConstraintSet::new();
        cs.add(Formula::Bool(true));
        cs.add(Formula::Int(42));
        // Ground constraints (no variables) each form their own group.
        let groups = independence_splitting(&cs);
        assert_eq!(groups.len(), 2);
    }

    #[test]
    fn test_splitting_single_constraint() {
        let mut cs = ConstraintSet::new();
        cs.add(Formula::Var("x".into(), Sort::Int));
        let groups = independence_splitting(&cs);
        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].len(), 1);
    }
}
