// trust-cache/independence.rs: Constraint independence splitting
//
// Splits formulas into independent conjuncts that share no free variables.
// Smaller independent sub-queries are faster for SMT solvers.
// Inspired by KLEE's IndependentSolver (refs/klee/lib/Solver/IndependentSolver.cpp).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

use trust_types::Formula;

/// KLEE-style constraint independence engine.
///
/// Partitions formula conjuncts by shared variables so that independent
/// sub-formulas can be checked separately. This avoids sending the full
/// constraint set to the solver when only a subset is relevant to the
/// query variables.
///
/// Inspired by KLEE's `IndependentSolver` and `IndependentElementSet`
/// (refs/klee/lib/Solver/IndependentSolver.cpp).
pub struct ConstraintIndependence {
    /// The original top-level conjuncts.
    conjuncts: Vec<Formula>,
    /// Free variables for each conjunct (parallel to `conjuncts`).
    var_sets: Vec<FxHashSet<String>>,
    /// Union-find parent array for grouping.
    parent: Vec<usize>,
}

impl ConstraintIndependence {
    /// Analyze a formula and compute its independence structure.
    ///
    /// Flattens nested `And` nodes and computes free variable sets per conjunct,
    /// then uses union-find to group conjuncts that share variables.
    #[must_use]
    pub fn new(formula: &Formula) -> Self {
        let conjuncts = flatten_and(formula);
        let var_sets: Vec<FxHashSet<String>> = conjuncts.iter().map(free_variables).collect();
        let n = conjuncts.len();
        let mut parent: Vec<usize> = (0..n).collect();

        // Map each variable to the conjuncts that mention it
        let mut var_to_conjuncts: FxHashMap<&str, Vec<usize>> = FxHashMap::default();
        for (i, vars) in var_sets.iter().enumerate() {
            for v in vars {
                var_to_conjuncts.entry(v.as_str()).or_default().push(i);
            }
        }

        // Union conjuncts that share a variable
        for indices in var_to_conjuncts.values() {
            if indices.len() > 1 {
                let first = indices[0];
                for &other in &indices[1..] {
                    union(&mut parent, first, other);
                }
            }
        }

        Self { conjuncts, var_sets, parent }
    }

    /// Return the number of independent partitions.
    #[must_use]
    pub fn partition_count(&self) -> usize {
        if self.conjuncts.is_empty() {
            return 0;
        }
        let mut roots: FxHashSet<usize> = FxHashSet::default();
        let mut parent = self.parent.clone();
        for i in 0..self.conjuncts.len() {
            roots.insert(find(&mut parent, i));
        }
        roots.len()
    }

    /// Return the independent partitions as separate formulas.
    ///
    /// Each partition is a conjunction of conjuncts that share variables
    /// transitively. Single-conjunct partitions are returned unwrapped.
    #[must_use]
    pub fn partitions(&self) -> Vec<Formula> {
        if self.conjuncts.is_empty() {
            return vec![];
        }

        let mut parent = self.parent.clone();
        let mut groups: FxHashMap<usize, Vec<Formula>> = FxHashMap::default();
        for (i, conjunct) in self.conjuncts.iter().enumerate() {
            let root = find(&mut parent, i);
            groups.entry(root).or_default().push(conjunct.clone());
        }

        let mut result: Vec<Formula> = groups
            .into_values()
            .map(|group| {
                if group.len() == 1 {
                    // SAFETY: len == 1 guarantees .next() returns Some.
                    group
                        .into_iter()
                        .next()
                        .unwrap_or_else(|| unreachable!("empty iter despite len == 1"))
                } else {
                    Formula::And(group)
                }
            })
            .collect();

        // Sort for deterministic output
        result.sort_by(|a, b| format!("{a:?}").cmp(&format!("{b:?}")));
        result
    }

    /// Return the free variables across all conjuncts.
    #[must_use]
    pub fn all_variables(&self) -> FxHashSet<String> {
        self.var_sets.iter().flat_map(|s| s.iter().cloned()).collect()
    }

    /// Return the free variables for a specific partition (by root index).
    #[must_use]
    pub fn partition_variables(&self) -> Vec<FxHashSet<String>> {
        if self.conjuncts.is_empty() {
            return vec![];
        }

        let mut parent = self.parent.clone();
        let mut group_vars: FxHashMap<usize, FxHashSet<String>> = FxHashMap::default();
        for (i, vars) in self.var_sets.iter().enumerate() {
            let root = find(&mut parent, i);
            group_vars.entry(root).or_default().extend(vars.iter().cloned());
        }

        let mut result: Vec<FxHashSet<String>> = group_vars.into_values().collect();
        // Sort for deterministic output
        result.sort_by(|a, b| {
            let a_sorted: Vec<&String> = {
                let mut v: Vec<&String> = a.iter().collect();
                v.sort();
                v
            };
            let b_sorted: Vec<&String> = {
                let mut v: Vec<&String> = b.iter().collect();
                v.sort();
                v
            };
            a_sorted.cmp(&b_sorted)
        });
        result
    }
}

/// Partition a formula's conjuncts into independent sub-formulas.
///
/// This is the primary entry point: given a formula, split it into the
/// smallest independent sub-formulas that can be checked separately.
///
/// Sound because `(A /\ B)` is satisfiable iff both `A` and `B` are
/// satisfiable independently (when they share no variables).
#[must_use]
pub fn partition_constraints(formula: &Formula) -> Vec<Formula> {
    let ci = ConstraintIndependence::new(formula);
    let partitions = ci.partitions();
    if partitions.is_empty() { vec![formula.clone()] } else { partitions }
}

/// Project away constraints that don't mention any of the relevant variables.
///
/// Given a formula and a set of "interesting" variables, return a simplified
/// formula containing only the conjuncts whose free variables overlap with
/// `relevant_vars`. Conjuncts that mention only irrelevant variables are
/// dropped.
///
/// This is useful when checking a specific query about particular variables:
/// constraints on unrelated variables are irrelevant and slow down the solver.
#[must_use]
pub fn simplify_query(formula: &Formula, relevant_vars: &FxHashSet<String>) -> Formula {
    let conjuncts = flatten_and(formula);
    if conjuncts.len() <= 1 {
        return formula.clone();
    }

    let relevant: Vec<Formula> = conjuncts
        .into_iter()
        .filter(|conjunct| {
            let fv = free_variables(conjunct);
            // Keep if: conjunct mentions a relevant variable, OR
            // conjunct is a literal (no variables — always relevant)
            fv.is_empty() || fv.iter().any(|v| relevant_vars.contains(v))
        })
        .collect();

    match relevant.len() {
        0 => Formula::Bool(true),
        // SAFETY: match arm guarantees len == 1, so .next() returns Some.
        1 => relevant
            .into_iter()
            .next()
            .unwrap_or_else(|| unreachable!("empty iter despite len == 1")),
        _ => Formula::And(relevant),
    }
}

/// Extract all free variable names from a formula.
///
/// Traverses the formula tree and collects Var names. Variables bound by
/// quantifiers (Forall, Exists) are excluded from the result set.
#[must_use]
pub fn free_variables(formula: &Formula) -> FxHashSet<String> {
    let mut vars = FxHashSet::default();
    let mut bound = FxHashSet::default();
    collect_free_vars(formula, &mut vars, &mut bound);
    vars
}

fn collect_free_vars(
    formula: &Formula,
    vars: &mut FxHashSet<String>,
    bound: &mut FxHashSet<String>,
) {
    match formula {
        // Literals — no variables
        Formula::Bool(_) | Formula::Int(_) | Formula::UInt(_) | Formula::BitVec { .. } => {}

        // Variable — add if not bound
        Formula::Var(name, _) if !bound.contains(name) => {
            vars.insert(name.clone());
        }
        Formula::Var(_, _) => {}

        // Unary operators
        Formula::Not(inner) | Formula::Neg(inner) => {
            collect_free_vars(inner, vars, bound);
        }
        Formula::BvNot(inner, _)
        | Formula::BvToInt(inner, _, _)
        | Formula::IntToBv(inner, _)
        | Formula::BvZeroExt(inner, _)
        | Formula::BvSignExt(inner, _) => {
            collect_free_vars(inner, vars, bound);
        }
        Formula::BvExtract { inner, .. } => {
            collect_free_vars(inner, vars, bound);
        }

        // N-ary: And, Or
        Formula::And(children) | Formula::Or(children) => {
            for child in children {
                collect_free_vars(child, vars, bound);
            }
        }

        // Binary operators
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
        | Formula::Select(a, b)
        | Formula::BvConcat(a, b) => {
            collect_free_vars(a, vars, bound);
            collect_free_vars(b, vars, bound);
        }

        // Binary bitvector ops (with width)
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
            collect_free_vars(a, vars, bound);
            collect_free_vars(b, vars, bound);
        }

        // Ternary
        Formula::Ite(cond, then_f, else_f) | Formula::Store(cond, then_f, else_f) => {
            collect_free_vars(cond, vars, bound);
            collect_free_vars(then_f, vars, bound);
            collect_free_vars(else_f, vars, bound);
        }

        // Quantifiers — bind variables in the body
        Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
            let mut new_bound = bound.clone();
            for (name, _) in bindings {
                new_bound.insert(name.to_string());
            }
            collect_free_vars(body, vars, &mut new_bound);
        }
        _ => {}
    }
}

/// Flatten a top-level And into its conjuncts. Non-And formulas return as-is.
fn flatten_and(formula: &Formula) -> Vec<Formula> {
    match formula {
        Formula::And(children) => {
            let mut result = Vec::new();
            for child in children {
                result.extend(flatten_and(child));
            }
            result
        }
        other => vec![other.clone()],
    }
}

// Simple union-find (used by ConstraintIndependence)
fn find(parent: &mut [usize], mut i: usize) -> usize {
    while parent[i] != i {
        parent[i] = parent[parent[i]]; // path compression
        i = parent[i];
    }
    i
}

fn union(parent: &mut [usize], a: usize, b: usize) {
    let ra = find(parent, a);
    let rb = find(parent, b);
    if ra != rb {
        parent[rb] = ra;
    }
}

#[cfg(test)]
mod tests {
    use trust_types::Sort;

    use super::*;

    // Trust: find_independent_sets and helpers moved here — only used in tests.

    // Simple union-find
    fn uf_find(parent: &mut [usize], mut i: usize) -> usize {
        while parent[i] != i {
            parent[i] = parent[parent[i]]; // path compression
            i = parent[i];
        }
        i
    }

    fn uf_union(parent: &mut [usize], a: usize, b: usize) {
        let ra = uf_find(parent, a);
        let rb = uf_find(parent, b);
        if ra != rb {
            parent[rb] = ra;
        }
    }

    /// Split a formula into independent conjuncts (test-only legacy API).
    fn find_independent_sets(formula: &Formula) -> Vec<Formula> {
        let conjuncts = super::flatten_and(formula);
        if conjuncts.len() <= 1 {
            return vec![formula.clone()];
        }

        let var_sets: Vec<FxHashSet<String>> = conjuncts.iter().map(free_variables).collect();
        let n = conjuncts.len();
        let mut parent: Vec<usize> = (0..n).collect();

        let mut var_to_conjuncts: FxHashMap<&str, Vec<usize>> = FxHashMap::default();
        for (i, vars) in var_sets.iter().enumerate() {
            for v in vars {
                var_to_conjuncts.entry(v.as_str()).or_default().push(i);
            }
        }

        for indices in var_to_conjuncts.values() {
            if indices.len() > 1 {
                let first = indices[0];
                for &other in &indices[1..] {
                    uf_union(&mut parent, first, other);
                }
            }
        }

        let mut groups: FxHashMap<usize, Vec<Formula>> = FxHashMap::default();
        for (i, conjunct) in conjuncts.into_iter().enumerate() {
            let root = uf_find(&mut parent, i);
            groups.entry(root).or_default().push(conjunct);
        }

        let mut result: Vec<Formula> = groups
            .into_values()
            .map(|group| {
                if group.len() == 1 {
                    group
                        .into_iter()
                        .next()
                        .unwrap_or_else(|| unreachable!("empty iter despite len == 1"))
                } else {
                    Formula::And(group)
                }
            })
            .collect();

        result.sort_by(|a, b| format!("{a:?}").cmp(&format!("{b:?}")));
        result
    }

    fn var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }

    // -----------------------------------------------------------------------
    // free_variables tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_free_variables_simple_var() {
        let f = var("x");
        let fv = free_variables(&f);
        assert_eq!(fv.len(), 1);
        assert!(fv.contains("x"));
    }

    #[test]
    fn test_free_variables_literal() {
        let f = Formula::Bool(true);
        assert!(free_variables(&f).is_empty());
    }

    #[test]
    fn test_free_variables_nested() {
        let f = Formula::And(vec![
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(1))),
            Formula::Lt(Box::new(var("y")), Box::new(var("z"))),
        ]);
        let fv = free_variables(&f);
        assert_eq!(fv.len(), 3);
        assert!(fv.contains("x"));
        assert!(fv.contains("y"));
        assert!(fv.contains("z"));
    }

    #[test]
    fn test_free_variables_excludes_bound() {
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(var("x")), Box::new(var("y")))),
        );
        let fv = free_variables(&f);
        assert_eq!(fv.len(), 1);
        assert!(fv.contains("y"));
        assert!(!fv.contains("x"));
    }

    #[test]
    fn test_free_variables_exists_binding() {
        let f = Formula::Exists(
            vec![("a".into(), Sort::Bool)],
            Box::new(Formula::And(vec![var("a"), var("b")])),
        );
        let fv = free_variables(&f);
        assert_eq!(fv.len(), 1);
        assert!(fv.contains("b"));
    }

    #[test]
    fn test_free_variables_ite() {
        let f = Formula::Ite(Box::new(var("c")), Box::new(var("t")), Box::new(var("e")));
        let fv = free_variables(&f);
        assert_eq!(fv.len(), 3);
    }

    #[test]
    fn test_free_variables_bitvec_ops() {
        let f = Formula::BvAdd(Box::new(var("a")), Box::new(var("b")), 32);
        let fv = free_variables(&f);
        assert_eq!(fv.len(), 2);
        assert!(fv.contains("a"));
        assert!(fv.contains("b"));
    }

    // -----------------------------------------------------------------------
    // find_independent_sets tests (legacy API)
    // -----------------------------------------------------------------------

    #[test]
    fn test_independence_single_conjunct() {
        let f = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let sets = find_independent_sets(&f);
        assert_eq!(sets.len(), 1);
    }

    #[test]
    fn test_independence_fully_independent() {
        // x == 0 AND y > 1 — no shared variables
        let f = Formula::And(vec![
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(1))),
        ]);
        let sets = find_independent_sets(&f);
        assert_eq!(sets.len(), 2, "two independent conjuncts");
    }

    #[test]
    fn test_independence_shared_variable() {
        // x == 0 AND x > 1 — shared variable x
        let f = Formula::And(vec![
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(1))),
        ]);
        let sets = find_independent_sets(&f);
        assert_eq!(sets.len(), 1, "shared variable means one group");
    }

    #[test]
    fn test_independence_transitive() {
        // x == y AND y == z AND w == 0
        // First three share variables transitively, w is independent
        let f = Formula::And(vec![
            Formula::Eq(Box::new(var("x")), Box::new(var("y"))),
            Formula::Eq(Box::new(var("y")), Box::new(var("z"))),
            Formula::Eq(Box::new(var("w")), Box::new(Formula::Int(0))),
        ]);
        let sets = find_independent_sets(&f);
        assert_eq!(sets.len(), 2, "transitive sharing yields two groups");
    }

    #[test]
    fn test_independence_nested_and_flattened() {
        // And(And(x==0, y==1), z==2) — all independent
        let f = Formula::And(vec![
            Formula::And(vec![
                Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
                Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(1))),
            ]),
            Formula::Eq(Box::new(var("z")), Box::new(Formula::Int(2))),
        ]);
        let sets = find_independent_sets(&f);
        assert_eq!(sets.len(), 3, "nested Ands should be flattened");
    }

    #[test]
    fn test_independence_non_conjunction() {
        let f = Formula::Or(vec![var("x"), var("y")]);
        let sets = find_independent_sets(&f);
        assert_eq!(sets.len(), 1, "Or is not split");
    }

    #[test]
    fn test_independence_all_share_one_var() {
        // x == 0 AND x == 1 AND x == 2
        let f = Formula::And(vec![
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(1))),
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(2))),
        ]);
        let sets = find_independent_sets(&f);
        assert_eq!(sets.len(), 1);
    }

    #[test]
    fn test_independence_literal_conjuncts() {
        // true AND false — literals have no variables, so they're "independent"
        let f = Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]);
        let sets = find_independent_sets(&f);
        // Each literal is its own group (no shared vars)
        assert_eq!(sets.len(), 2);
    }

    // -----------------------------------------------------------------------
    // ConstraintIndependence struct tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_constraint_independence_partition_count() {
        // x==0 AND y>1 AND z<2 — three independent conjuncts
        let f = Formula::And(vec![
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(1))),
            Formula::Lt(Box::new(var("z")), Box::new(Formula::Int(2))),
        ]);
        let ci = ConstraintIndependence::new(&f);
        assert_eq!(ci.partition_count(), 3);
    }

    #[test]
    fn test_constraint_independence_shared_reduces_partitions() {
        // x==0 AND x>1 AND y<2 — x conjuncts grouped, y separate
        let f = Formula::And(vec![
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(1))),
            Formula::Lt(Box::new(var("y")), Box::new(Formula::Int(2))),
        ]);
        let ci = ConstraintIndependence::new(&f);
        assert_eq!(ci.partition_count(), 2);
        assert_eq!(ci.partitions().len(), 2);
    }

    #[test]
    fn test_constraint_independence_all_variables() {
        let f = Formula::And(vec![
            Formula::Eq(Box::new(var("a")), Box::new(Formula::Int(0))),
            Formula::Gt(Box::new(var("b")), Box::new(var("c"))),
        ]);
        let ci = ConstraintIndependence::new(&f);
        let all = ci.all_variables();
        assert_eq!(all.len(), 3);
        assert!(all.contains("a"));
        assert!(all.contains("b"));
        assert!(all.contains("c"));
    }

    #[test]
    fn test_constraint_independence_partition_variables() {
        // Two independent groups: {a} and {b, c}
        let f = Formula::And(vec![
            Formula::Eq(Box::new(var("a")), Box::new(Formula::Int(0))),
            Formula::Gt(Box::new(var("b")), Box::new(var("c"))),
        ]);
        let ci = ConstraintIndependence::new(&f);
        let pv = ci.partition_variables();
        assert_eq!(pv.len(), 2);
        // One partition has {a}, the other has {b, c}
        let sizes: Vec<usize> = pv.iter().map(|s| s.len()).collect();
        assert!(sizes.contains(&1));
        assert!(sizes.contains(&2));
    }

    #[test]
    fn test_constraint_independence_empty_formula() {
        let f = Formula::Bool(true);
        let ci = ConstraintIndependence::new(&f);
        // Single non-And formula yields one "conjunct"
        assert_eq!(ci.partition_count(), 1);
        assert_eq!(ci.partitions().len(), 1);
    }

    // -----------------------------------------------------------------------
    // partition_constraints tests (new public API)
    // -----------------------------------------------------------------------

    #[test]
    fn test_partition_constraints_splits_independent() {
        let f = Formula::And(vec![
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(1))),
        ]);
        let parts = partition_constraints(&f);
        assert_eq!(parts.len(), 2);
    }

    #[test]
    fn test_partition_constraints_keeps_dependent() {
        let f = Formula::And(vec![
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(1))),
        ]);
        let parts = partition_constraints(&f);
        assert_eq!(parts.len(), 1);
    }

    #[test]
    fn test_partition_constraints_single_formula() {
        let f = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(42)));
        let parts = partition_constraints(&f);
        assert_eq!(parts.len(), 1);
        assert_eq!(parts[0], f);
    }

    #[test]
    fn test_partition_constraints_four_groups() {
        // a==0, b==1, c==2, d==3 — four independent groups
        let f = Formula::And(vec![
            Formula::Eq(Box::new(var("a")), Box::new(Formula::Int(0))),
            Formula::Eq(Box::new(var("b")), Box::new(Formula::Int(1))),
            Formula::Eq(Box::new(var("c")), Box::new(Formula::Int(2))),
            Formula::Eq(Box::new(var("d")), Box::new(Formula::Int(3))),
        ]);
        let parts = partition_constraints(&f);
        assert_eq!(parts.len(), 4);
    }

    // -----------------------------------------------------------------------
    // simplify_query tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_simplify_query_keeps_relevant() {
        // x==0 AND y>1 AND z<2, relevant={x}
        let f = Formula::And(vec![
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(1))),
            Formula::Lt(Box::new(var("z")), Box::new(Formula::Int(2))),
        ]);
        let relevant: FxHashSet<String> = ["x".to_string()].into_iter().collect();
        let simplified = simplify_query(&f, &relevant);
        // Should keep only x==0
        let fv = free_variables(&simplified);
        assert!(fv.contains("x"));
        assert!(!fv.contains("y"));
        assert!(!fv.contains("z"));
    }

    #[test]
    fn test_simplify_query_keeps_multiple_relevant() {
        // x==0 AND y>1 AND z<2, relevant={x, y}
        let f = Formula::And(vec![
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(1))),
            Formula::Lt(Box::new(var("z")), Box::new(Formula::Int(2))),
        ]);
        let relevant: FxHashSet<String> = ["x".to_string(), "y".to_string()].into_iter().collect();
        let simplified = simplify_query(&f, &relevant);
        let fv = free_variables(&simplified);
        assert!(fv.contains("x"));
        assert!(fv.contains("y"));
        assert!(!fv.contains("z"));
    }

    #[test]
    fn test_simplify_query_keeps_literals() {
        // true AND x==0 AND y>1, relevant={x}
        // Should keep true (literal) and x==0
        let f = Formula::And(vec![
            Formula::Bool(true),
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(1))),
        ]);
        let relevant: FxHashSet<String> = ["x".to_string()].into_iter().collect();
        let simplified = simplify_query(&f, &relevant);
        // Should be And(true, x==0) since true has no vars (literal)
        match &simplified {
            Formula::And(children) => assert_eq!(children.len(), 2),
            _ => panic!("expected And, got {simplified:?}"),
        }
    }

    #[test]
    fn test_simplify_query_no_relevant_returns_true() {
        // x==0 AND y>1, relevant={z} (nothing relevant)
        let f = Formula::And(vec![
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(1))),
        ]);
        let relevant: FxHashSet<String> = ["z".to_string()].into_iter().collect();
        let simplified = simplify_query(&f, &relevant);
        assert_eq!(simplified, Formula::Bool(true));
    }

    #[test]
    fn test_simplify_query_single_conjunct_passthrough() {
        let f = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let relevant: FxHashSet<String> = ["z".to_string()].into_iter().collect();
        // Single conjunct: returned as-is (no splitting possible)
        let simplified = simplify_query(&f, &relevant);
        assert_eq!(simplified, f);
    }

    #[test]
    fn test_simplify_query_all_relevant() {
        let f = Formula::And(vec![
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(1))),
        ]);
        let relevant: FxHashSet<String> = ["x".to_string(), "y".to_string()].into_iter().collect();
        let simplified = simplify_query(&f, &relevant);
        // All conjuncts are relevant: returned as full And
        let fv = free_variables(&simplified);
        assert!(fv.contains("x"));
        assert!(fv.contains("y"));
    }
}
