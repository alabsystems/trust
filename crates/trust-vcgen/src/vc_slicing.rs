// Proof obligation slicing to reduce solver work.
//
// Performs backward dependency analysis on VC formulas to remove
// conjuncts that are irrelevant to the property being checked.
// This reduces the formula size sent to solvers, improving performance.
//
// The core algorithm:
//   1. Collect free variables from the target (property) formula.
//   2. Compute a dependency cone: iteratively add context formulas
//      whose variables overlap with the current dependency set.
//   3. Remove conjuncts outside the cone from the VC.
//
// Inspired by program slicing (Weiser 1981) and KLEE's constraint
// independence optimization (refs/klee/lib/Solver/).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;
use trust_types::{Formula, VerificationCondition};

// Collect all free variable names from a formula.
//
// Delegates to `Formula::free_variables()` which already handles
// quantifier-bound variable exclusion.
#[must_use]
pub fn collect_vars(formula: &Formula) -> FxHashSet<String> {
    formula.free_variables()
}

// Compute the backward dependency cone from a target formula.
//
// Starting from the free variables of `target`, iteratively includes
// context formulas whose free variables overlap with the current
// dependency set. Reaches a fixpoint when no new context formulas
// are added (monotone, bounded by context length).
//
// Returns the subset of `context` that is transitively relevant to
// `target`, preserving original order.
#[must_use]
pub fn dependency_cone(target: &Formula, context: &[Formula]) -> Vec<Formula> {
    // Seed the dependency set with target's free variables.
    let mut dep_vars: FxHashSet<String> = collect_vars(target);

    // Track which context formulas are already included.
    let mut included = vec![false; context.len()];

    // Pre-compute free variables for each context formula
    // to avoid redundant traversals in the fixpoint loop.
    let context_vars: Vec<FxHashSet<String>> = context.iter().map(collect_vars).collect();

    // Fixpoint iteration — keep adding context formulas
    // whose variables overlap with the current dependency set until
    // no new formulas are added.
    let mut changed = true;
    while changed {
        changed = false;
        for (i, vars) in context_vars.iter().enumerate() {
            if included[i] {
                continue;
            }
            // A context formula is relevant if it shares
            // any variable with the current dependency set.
            if vars.iter().any(|v| dep_vars.contains(v)) {
                included[i] = true;
                dep_vars.extend(vars.iter().cloned());
                changed = true;
            }
        }
    }

    // Collect included formulas in original order.
    context
        .iter()
        .enumerate()
        .filter_map(|(i, f)| if included[i] { Some(f.clone()) } else { None })
        .collect()
}

// Slice a verification condition to remove irrelevant conjuncts.
//
// For a VC formula of the form `And([assumption1, ..., assumptionN, target])`,
// identifies the target (last conjunct) and runs dependency_cone on the
// remaining conjuncts (assumptions). Conjuncts outside the dependency cone
// are removed.
//
// For non-And formulas, or formulas with fewer than 2 conjuncts,
// the VC is returned unchanged (no slicing opportunity).
#[must_use]
pub fn slice_vc(vc: &VerificationCondition) -> VerificationCondition {
    let (assumptions, target) = match &vc.formula {
        // For And formulas, treat last conjunct as target.
        // This matches the convention in generate_vcs where guard
        // assumptions are prepended and the violation formula is last.
        Formula::And(conjuncts) if conjuncts.len() >= 2 => {
            let (assumptions, target_slice) = conjuncts.split_at(conjuncts.len() - 1);
            (assumptions, &target_slice[0])
        }
        // No slicing for non-conjunctive or trivial formulas.
        _ => return vc.clone(),
    };

    // Compute the dependency cone of assumptions relevant
    // to the target formula.
    let relevant = dependency_cone(target, assumptions);

    // Reconstruct the formula with only relevant assumptions.
    let mut sliced_conjuncts = relevant;
    sliced_conjuncts.push(target.clone());

    let sliced_formula = if sliced_conjuncts.len() == 1 {
        sliced_conjuncts.into_iter().next().expect("invariant: len == 1")
    } else {
        Formula::And(sliced_conjuncts)
    };

    VerificationCondition {
        kind: vc.kind.clone(),
        function: vc.function,
        location: vc.location.clone(),
        formula: sliced_formula,
        contract_metadata: vc.contract_metadata,
        // The formula is SLICED here, so a recorded obligation body would no longer
        // reconstruct it — drop it fail-closed (the consumer would DECLINE anyway).
        obligation: None,
    }
}

// Statistics about the slicing transformation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SlicingStats {
    /// Number of top-level conjuncts before slicing.
    pub original_size: usize,
    /// Number of top-level conjuncts after slicing.
    pub sliced_size: usize,
    /// Number of unique variables kept in the sliced formula.
    pub vars_kept: usize,
    /// Number of unique variables dropped by slicing.
    pub vars_dropped: usize,
}

// Compute slicing statistics for a VC.
//
// Compares the original formula with the sliced version to report
// how many conjuncts and variables were removed.
#[must_use]
pub fn compute_slicing_stats(vc: &VerificationCondition) -> SlicingStats {
    let original_conjuncts = match &vc.formula {
        Formula::And(conjuncts) => conjuncts.len(),
        _ => 1,
    };

    let original_vars = collect_vars(&vc.formula);
    let sliced = slice_vc(vc);
    let sliced_vars = collect_vars(&sliced.formula);

    let sliced_conjuncts = match &sliced.formula {
        Formula::And(conjuncts) => conjuncts.len(),
        _ => 1,
    };

    let vars_kept = sliced_vars.len();
    let vars_dropped = original_vars.difference(&sliced_vars).count();

    SlicingStats {
        original_size: original_conjuncts,
        sliced_size: sliced_conjuncts,
        vars_kept,
        vars_dropped,
    }
}

#[cfg(test)]
mod tests {
    use trust_types::{Formula, Sort, SourceSpan, VcKind, VerificationCondition};

    use super::*;

    // Helper to create a variable formula.
    fn var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    // Helper to create a simple test VC.
    fn make_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    #[test]
    fn test_collect_vars_empty_for_literal() {
        // Literals have no free variables.
        assert!(collect_vars(&Formula::Bool(true)).is_empty());
        assert!(collect_vars(&Formula::Int(42)).is_empty());
    }

    #[test]
    fn test_collect_vars_single_variable() {
        // A single variable formula yields exactly that variable.
        let vars = collect_vars(&var("x"));
        assert_eq!(vars.len(), 1);
        assert!(vars.contains("x"));
    }

    #[test]
    fn test_collect_vars_nested_formula() {
        // Variables collected from nested sub-formulas.
        let f = Formula::And(vec![
            Formula::Eq(Box::new(var("a")), Box::new(var("b"))),
            Formula::Lt(Box::new(var("c")), Box::new(Formula::Int(10))),
        ]);
        let vars = collect_vars(&f);
        assert_eq!(vars.len(), 3);
        assert!(vars.contains("a"));
        assert!(vars.contains("b"));
        assert!(vars.contains("c"));
    }

    #[test]
    fn test_collect_vars_excludes_quantifier_bound() {
        // Quantifier-bound variables are excluded.
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(var("x")), Box::new(var("y")))),
        );
        let vars = collect_vars(&f);
        assert_eq!(vars.len(), 1);
        assert!(vars.contains("y"));
        assert!(!vars.contains("x"));
    }

    #[test]
    fn test_dependency_cone_empty_context() {
        // Empty context yields empty cone.
        let target = var("x");
        let cone = dependency_cone(&target, &[]);
        assert!(cone.is_empty());
    }

    #[test]
    fn test_dependency_cone_all_relevant() {
        // All context formulas share variables with target.
        let target = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let context = vec![
            Formula::Lt(Box::new(var("x")), Box::new(Formula::Int(100))),
            Formula::Ge(Box::new(var("x")), Box::new(Formula::Int(0))),
        ];
        let cone = dependency_cone(&target, &context);
        assert_eq!(cone.len(), 2);
    }

    #[test]
    fn test_dependency_cone_none_relevant() {
        // No context formulas share variables with target.
        let target = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let context = vec![
            Formula::Lt(Box::new(var("a")), Box::new(var("b"))),
            Formula::Ge(Box::new(var("c")), Box::new(Formula::Int(0))),
        ];
        let cone = dependency_cone(&target, &context);
        assert!(cone.is_empty());
    }

    #[test]
    fn test_dependency_cone_transitive_dependency() {
        // Transitive variable dependency pulls in indirectly related formulas.
        // target uses "x", context[0] uses "x" and "y", context[1] uses "y" and "z".
        // context[1] should be included transitively via "y".
        let target = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let context = vec![
            Formula::Eq(Box::new(var("x")), Box::new(var("y"))),
            Formula::Lt(Box::new(var("y")), Box::new(var("z"))),
            Formula::Eq(Box::new(var("w")), Box::new(Formula::Int(99))), // irrelevant
        ];
        let cone = dependency_cone(&target, &context);
        assert_eq!(cone.len(), 2);
        // "w" formula should not be included.
        let cone_vars: FxHashSet<String> = cone.iter().flat_map(collect_vars).collect();
        assert!(cone_vars.contains("x"));
        assert!(cone_vars.contains("y"));
        assert!(cone_vars.contains("z"));
        assert!(!cone_vars.contains("w"));
    }

    #[test]
    fn test_dependency_cone_preserves_order() {
        // Relevant formulas are returned in original context order.
        let target = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let context = vec![
            Formula::Eq(Box::new(var("a")), Box::new(Formula::Int(1))), // irrelevant
            Formula::Lt(Box::new(var("x")), Box::new(Formula::Int(100))),
            Formula::Eq(Box::new(var("b")), Box::new(Formula::Int(2))), // irrelevant
            Formula::Ge(Box::new(var("x")), Box::new(Formula::Int(0))),
        ];
        let cone = dependency_cone(&target, &context);
        assert_eq!(cone.len(), 2);
        // Check the two relevant formulas are in original order.
        assert!(matches!(&cone[0], Formula::Lt(..)));
        assert!(matches!(&cone[1], Formula::Ge(..)));
    }

    #[test]
    fn test_slice_vc_removes_irrelevant_conjuncts() {
        // Slicing removes conjuncts not in the dependency cone.
        let formula = Formula::And(vec![
            Formula::Eq(Box::new(var("a")), Box::new(Formula::Int(1))), // irrelevant
            Formula::Lt(Box::new(var("x")), Box::new(Formula::Int(100))), // relevant
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))), // target
        ]);
        let vc = make_vc(formula);
        let sliced = slice_vc(&vc);

        match &sliced.formula {
            Formula::And(conjuncts) => {
                assert_eq!(conjuncts.len(), 2, "should keep 1 relevant + 1 target");
            }
            _ => panic!("expected And formula after slicing"),
        }
    }

    #[test]
    fn test_slice_vc_non_and_formula_unchanged() {
        // Non-And formulas pass through unchanged.
        let formula = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let vc = make_vc(formula.clone());
        let sliced = slice_vc(&vc);
        assert_eq!(sliced.formula, formula);
    }

    #[test]
    fn test_slice_vc_single_conjunct_unchanged() {
        // A single-element And has no assumptions to slice.
        let formula =
            Formula::And(vec![Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)))]);
        let vc = make_vc(formula.clone());
        let sliced = slice_vc(&vc);
        assert_eq!(sliced.formula, formula);
    }

    #[test]
    fn test_slice_vc_keeps_all_when_all_relevant() {
        // When all assumptions are relevant, nothing is sliced.
        let formula = Formula::And(vec![
            Formula::Lt(Box::new(var("x")), Box::new(Formula::Int(100))),
            Formula::Ge(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(50))), // target
        ]);
        let vc = make_vc(formula);
        let sliced = slice_vc(&vc);

        match &sliced.formula {
            Formula::And(conjuncts) => {
                assert_eq!(conjuncts.len(), 3, "all conjuncts should be kept");
            }
            _ => panic!("expected And formula"),
        }
    }

    #[test]
    fn test_slice_vc_preserves_metadata() {
        // Slicing preserves VC kind, function, location.
        let formula = Formula::And(vec![
            Formula::Eq(Box::new(var("a")), Box::new(Formula::Int(1))),
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
        ]);
        let vc = make_vc(formula);
        let sliced = slice_vc(&vc);
        assert_eq!(sliced.function, "test_fn");
        assert!(matches!(sliced.kind, VcKind::DivisionByZero));
    }

    #[test]
    fn test_slice_vc_target_only_when_all_irrelevant() {
        // When no assumptions are relevant, result is just the target.
        let formula = Formula::And(vec![
            Formula::Eq(Box::new(var("a")), Box::new(Formula::Int(1))), // irrelevant
            Formula::Eq(Box::new(var("b")), Box::new(var("c"))),        // irrelevant
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))), // target
        ]);
        let vc = make_vc(formula);
        let sliced = slice_vc(&vc);

        // When only the target remains, it is unwrapped from And.
        assert_eq!(sliced.formula, Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))));
    }

    #[test]
    fn test_slicing_stats_no_slicing() {
        // Stats when nothing is sliced (all relevant).
        let formula = Formula::And(vec![
            Formula::Lt(Box::new(var("x")), Box::new(Formula::Int(100))),
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
        ]);
        let vc = make_vc(formula);
        let stats = compute_slicing_stats(&vc);
        assert_eq!(stats.original_size, 2);
        assert_eq!(stats.sliced_size, 2);
        assert_eq!(stats.vars_dropped, 0);
    }

    #[test]
    fn test_slicing_stats_with_dropped_vars() {
        // Stats when variables are dropped by slicing.
        let formula = Formula::And(vec![
            Formula::Eq(Box::new(var("a")), Box::new(var("b"))), // irrelevant
            Formula::Lt(Box::new(var("x")), Box::new(Formula::Int(100))),
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
        ]);
        let vc = make_vc(formula);
        let stats = compute_slicing_stats(&vc);
        assert_eq!(stats.original_size, 3);
        assert_eq!(stats.sliced_size, 2);
        assert_eq!(stats.vars_dropped, 2); // "a" and "b" dropped
        assert_eq!(stats.vars_kept, 1); // "x" kept
    }

    #[test]
    fn test_slicing_stats_non_and_formula() {
        // Non-And formulas have size 1 and no slicing.
        let formula = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let vc = make_vc(formula);
        let stats = compute_slicing_stats(&vc);
        assert_eq!(stats.original_size, 1);
        assert_eq!(stats.sliced_size, 1);
        assert_eq!(stats.vars_dropped, 0);
    }

    #[test]
    fn test_dependency_cone_fixpoint_convergence() {
        // Three-step transitive chain: x->y->z->w.
        // Target uses "x", should pull in all three context formulas.
        let target = var("x");
        let context = vec![
            Formula::Eq(Box::new(var("x")), Box::new(var("y"))),
            Formula::Eq(Box::new(var("y")), Box::new(var("z"))),
            Formula::Eq(Box::new(var("z")), Box::new(var("w"))),
            Formula::Eq(Box::new(var("unrelated")), Box::new(Formula::Int(0))),
        ];
        let cone = dependency_cone(&target, &context);
        assert_eq!(cone.len(), 3, "three transitively related formulas");
        let cone_vars: FxHashSet<String> = cone.iter().flat_map(collect_vars).collect();
        assert!(cone_vars.contains("x"));
        assert!(cone_vars.contains("y"));
        assert!(cone_vars.contains("z"));
        assert!(cone_vars.contains("w"));
        assert!(!cone_vars.contains("unrelated"));
    }

    #[test]
    fn test_slice_vc_nested_and_in_assumption() {
        // Nested And within a top-level And conjunct is treated
        // as a single unit — its variables are all collected.
        let nested_assumption = Formula::And(vec![
            Formula::Eq(Box::new(var("x")), Box::new(var("y"))),
            Formula::Lt(Box::new(var("y")), Box::new(Formula::Int(10))),
        ]);
        let formula = Formula::And(vec![
            nested_assumption,                                          // relevant via "x"
            Formula::Eq(Box::new(var("a")), Box::new(Formula::Int(1))), // irrelevant
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))), // target
        ]);
        let vc = make_vc(formula);
        let sliced = slice_vc(&vc);

        match &sliced.formula {
            Formula::And(conjuncts) => {
                assert_eq!(conjuncts.len(), 2, "nested And + target");
            }
            _ => panic!("expected And formula"),
        }
    }
}
