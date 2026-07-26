// trust_vcgen/simplify.rs: Verification condition simplification passes
//
// Reduces formula size before sending to solvers. Each pass is a composable
// SimplificationPass; SimplificationPipeline chains them to a fixed point.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::Formula;
use trust_types::fx::FxHashSet;

// ---------------------------------------------------------------------------
// SimplificationPass trait + pipeline
// ---------------------------------------------------------------------------

/// A single simplification pass over a formula.
pub trait SimplificationPass {
    /// Human-readable name for diagnostics.
    fn name(&self) -> &str;

    /// Apply this pass to a formula, returning a (potentially) simplified one.
    fn apply(&self, formula: Formula) -> Formula;
}

/// Run a sequence of passes until fixed point (no size change) or `max_iters`.
pub struct SimplificationPipeline {
    passes: Vec<Box<dyn SimplificationPass>>,
    max_iters: usize,
}

impl SimplificationPipeline {
    /// Create a pipeline with the given passes and iteration limit.
    #[must_use]
    pub fn new(passes: Vec<Box<dyn SimplificationPass>>, max_iters: usize) -> Self {
        Self { passes, max_iters }
    }

    /// Create a default pipeline with all built-in passes.
    #[must_use]
    pub fn default_pipeline() -> Self {
        Self {
            passes: vec![Box::new(ConstantFoldPass), Box::new(BooleanSimplifyPass)],
            max_iters: 10,
        }
    }

    /// Run all passes until fixed point or max iterations reached.
    /// Returns the simplified formula and the number of iterations performed.
    #[must_use]
    pub fn run(&self, formula: Formula) -> (Formula, usize) {
        let mut current = formula;
        for iter in 0..self.max_iters {
            let before_size = measure_size(&current);
            for pass in &self.passes {
                current = pass.apply(current);
            }
            let after_size = measure_size(&current);
            if after_size >= before_size {
                return (current, iter + 1);
            }
        }
        (current, self.max_iters)
    }
}

// ---------------------------------------------------------------------------
// measure_size
// ---------------------------------------------------------------------------

/// Count the number of AST nodes in a formula.
#[must_use]
pub fn measure_size(formula: &Formula) -> usize {
    let mut count = 0;
    formula.visit(&mut |_| count += 1);
    count
}

// ---------------------------------------------------------------------------
// constant_fold
// ---------------------------------------------------------------------------

/// Evaluate constant sub-expressions bottom-up.
///
/// Folds: Not(Bool), And/Or of all-constant, Eq/Lt/Le/Gt/Ge on Int literals,
/// Add/Sub/Mul/Div/Rem/Neg on Int literals, Implies on Bool constants,
/// Eq(x, x) reflexive equality.
#[must_use]
pub fn constant_fold(formula: Formula) -> Formula {
    formula.map(&mut |f| match f {
        // Boolean not
        Formula::Not(inner) => match *inner {
            Formula::Bool(b) => Formula::Bool(!b),
            other => Formula::Not(Box::new(other)),
        },

        // And: all-true -> true, any-false -> false
        Formula::And(terms) => {
            if terms.iter().all(|t| matches!(t, Formula::Bool(true))) {
                Formula::Bool(true)
            } else if terms.iter().any(|t| matches!(t, Formula::Bool(false))) {
                Formula::Bool(false)
            } else {
                Formula::And(terms)
            }
        }

        // Or: all-false -> false, any-true -> true
        Formula::Or(terms) => {
            if terms.iter().all(|t| matches!(t, Formula::Bool(false))) {
                Formula::Bool(false)
            } else if terms.iter().any(|t| matches!(t, Formula::Bool(true))) {
                Formula::Bool(true)
            } else {
                Formula::Or(terms)
            }
        }

        // Implies
        Formula::Implies(a, b) => match (*a, *b) {
            (Formula::Bool(false), _) => Formula::Bool(true),
            (_, Formula::Bool(true)) => Formula::Bool(true),
            (Formula::Bool(true), rhs) => rhs,
            (lhs, rhs) => Formula::Implies(Box::new(lhs), Box::new(rhs)),
        },

        // Integer comparisons — also handles reflexive equality: Eq(x, x) -> true
        Formula::Eq(a, b) => match (*a, *b) {
            (Formula::Int(x), Formula::Int(y)) => Formula::Bool(x == y),
            (ref lhs, ref rhs) if lhs == rhs => Formula::Bool(true),
            (lhs, rhs) => Formula::Eq(Box::new(lhs), Box::new(rhs)),
        },
        Formula::Lt(a, b) => match (*a, *b) {
            (Formula::Int(x), Formula::Int(y)) => Formula::Bool(x < y),
            (lhs, rhs) => Formula::Lt(Box::new(lhs), Box::new(rhs)),
        },
        Formula::Le(a, b) => match (*a, *b) {
            (Formula::Int(x), Formula::Int(y)) => Formula::Bool(x <= y),
            (lhs, rhs) => Formula::Le(Box::new(lhs), Box::new(rhs)),
        },
        Formula::Gt(a, b) => match (*a, *b) {
            (Formula::Int(x), Formula::Int(y)) => Formula::Bool(x > y),
            (lhs, rhs) => Formula::Gt(Box::new(lhs), Box::new(rhs)),
        },
        Formula::Ge(a, b) => match (*a, *b) {
            (Formula::Int(x), Formula::Int(y)) => Formula::Bool(x >= y),
            (lhs, rhs) => Formula::Ge(Box::new(lhs), Box::new(rhs)),
        },

        // Integer arithmetic — use checked ops so i128 overflow leaves the
        // formula unsimplified instead of silently wrapping (SMT integers are
        // mathematical / unbounded).
        Formula::Add(a, b) => match (*a, *b) {
            (Formula::Int(x), Formula::Int(y)) => match x.checked_add(y) {
                Some(r) => Formula::Int(r),
                None => Formula::Add(Box::new(Formula::Int(x)), Box::new(Formula::Int(y))),
            },
            (lhs, rhs) => Formula::Add(Box::new(lhs), Box::new(rhs)),
        },
        Formula::Sub(a, b) => match (*a, *b) {
            (Formula::Int(x), Formula::Int(y)) => match x.checked_sub(y) {
                Some(r) => Formula::Int(r),
                None => Formula::Sub(Box::new(Formula::Int(x)), Box::new(Formula::Int(y))),
            },
            (lhs, rhs) => Formula::Sub(Box::new(lhs), Box::new(rhs)),
        },
        Formula::Mul(a, b) => match (*a, *b) {
            (Formula::Int(x), Formula::Int(y)) => match x.checked_mul(y) {
                Some(r) => Formula::Int(r),
                None => Formula::Mul(Box::new(Formula::Int(x)), Box::new(Formula::Int(y))),
            },
            (lhs, rhs) => Formula::Mul(Box::new(lhs), Box::new(rhs)),
        },
        Formula::Div(a, b) => match (*a, *b) {
            (Formula::Int(x), Formula::Int(y)) if y != 0 => match x.checked_div(y) {
                Some(r) => Formula::Int(r),
                None => Formula::Div(Box::new(Formula::Int(x)), Box::new(Formula::Int(y))),
            },
            (lhs, rhs) => Formula::Div(Box::new(lhs), Box::new(rhs)),
        },
        Formula::Rem(a, b) => match (*a, *b) {
            (Formula::Int(x), Formula::Int(y)) if y != 0 => match x.checked_rem(y) {
                Some(r) => Formula::Int(r),
                None => Formula::Rem(Box::new(Formula::Int(x)), Box::new(Formula::Int(y))),
            },
            (lhs, rhs) => Formula::Rem(Box::new(lhs), Box::new(rhs)),
        },
        Formula::Neg(inner) => match *inner {
            Formula::Int(x) => match x.checked_neg() {
                Some(r) => Formula::Int(r),
                None => Formula::Neg(Box::new(Formula::Int(x))),
            },
            other => Formula::Neg(Box::new(other)),
        },

        // Ite with constant condition
        Formula::Ite(cond, then_f, else_f) => match *cond {
            Formula::Bool(true) => *then_f,
            Formula::Bool(false) => *else_f,
            c => Formula::Ite(Box::new(c), then_f, else_f),
        },

        other => other,
    })
}

/// Pass wrapper for `constant_fold`.
pub struct ConstantFoldPass;

impl SimplificationPass for ConstantFoldPass {
    fn name(&self) -> &str {
        "constant_fold"
    }

    fn apply(&self, formula: Formula) -> Formula {
        constant_fold(formula)
    }
}

// ---------------------------------------------------------------------------
// boolean_simplify
// ---------------------------------------------------------------------------

/// Boolean algebraic simplification (identity/annihilation/double negation).
///
/// Rules applied bottom-up:
/// - And(true, x) -> x, And(false, _) -> false, flatten nested And
/// - Or(false, x) -> x, Or(true, _) -> true, flatten nested Or
/// - Not(Not(x)) -> x
/// - Implies(false, _) -> true, Implies(_, true) -> true
/// - And([]) -> true, Or([]) -> false
/// - Singleton And/Or unwrapped
/// - Contradiction: And([..., P, ..., Not(P), ...]) -> false
/// - Excluded middle: Or([..., P, ..., Not(P), ...]) -> true
#[must_use]
pub fn boolean_simplify(formula: Formula) -> Formula {
    formula.map(&mut |f| match f {
        // Double negation
        Formula::Not(inner) => match *inner {
            Formula::Not(x) => *x,
            other => Formula::Not(Box::new(other)),
        },

        // And: filter out true, short-circuit on false, flatten nested And,
        // detect contradiction (P and Not(P))
        Formula::And(terms) => {
            let mut flat = Vec::with_capacity(terms.len());
            for t in terms {
                match t {
                    Formula::Bool(true) => {}                            // identity: skip
                    Formula::Bool(false) => return Formula::Bool(false), // annihilation
                    Formula::And(inner) => flat.extend(inner),           // flatten
                    other => flat.push(other),
                }
            }
            // Contradiction detection: And([..., P, ..., Not(P), ...]) -> false
            if has_ast_contradiction(&flat) {
                return Formula::Bool(false);
            }
            match flat.len() {
                0 => Formula::Bool(true),
                // SAFETY: match arm guarantees len == 1, so .next() returns Some.
                1 => flat
                    .into_iter()
                    .next()
                    .unwrap_or_else(|| unreachable!("empty iter despite len == 1")),
                _ => Formula::And(flat),
            }
        }

        // Or: filter out false, short-circuit on true, flatten nested Or,
        // detect excluded middle (P or Not(P))
        Formula::Or(terms) => {
            let mut flat = Vec::with_capacity(terms.len());
            for t in terms {
                match t {
                    Formula::Bool(false) => {}                         // identity: skip
                    Formula::Bool(true) => return Formula::Bool(true), // annihilation
                    Formula::Or(inner) => flat.extend(inner),          // flatten
                    other => flat.push(other),
                }
            }
            // Excluded middle: Or([..., P, ..., Not(P), ...]) -> true
            if has_ast_contradiction(&flat) {
                return Formula::Bool(true);
            }
            match flat.len() {
                0 => Formula::Bool(false),
                // SAFETY: match arm guarantees len == 1, so .next() returns Some.
                1 => flat
                    .into_iter()
                    .next()
                    .unwrap_or_else(|| unreachable!("empty iter despite len == 1")),
                _ => Formula::Or(flat),
            }
        }

        // Implies simplifications
        Formula::Implies(a, b) => match (*a, *b) {
            (Formula::Bool(false), _) => Formula::Bool(true),
            (_, Formula::Bool(true)) => Formula::Bool(true),
            (Formula::Bool(true), rhs) => rhs,
            (lhs, Formula::Bool(false)) => Formula::Not(Box::new(lhs)),
            (lhs, rhs) => Formula::Implies(Box::new(lhs), Box::new(rhs)),
        },

        other => other,
    })
}

/// Check whether a list of formulas contains both P and Not(P) for some P.
///
/// Used for contradiction detection in And and excluded-middle detection in Or.
fn has_ast_contradiction(terms: &[Formula]) -> bool {
    // Collect all positive terms and all negated terms, then check for overlap.
    // We compare by structural equality which is already derived on Formula.
    let mut positives: FxHashSet<usize> = FxHashSet::default();
    let mut negative_indices: Vec<usize> = Vec::new();

    for (i, term) in terms.iter().enumerate() {
        if matches!(term, Formula::Not(_)) {
            negative_indices.push(i);
        } else {
            positives.insert(i);
        }
    }

    for neg_idx in &negative_indices {
        if let Formula::Not(inner) = &terms[*neg_idx] {
            // Check if the inner formula appears as a positive term
            for &pos_idx in &positives {
                if terms[pos_idx] == **inner {
                    return true;
                }
            }
        }
    }

    false
}

/// Pass wrapper for `boolean_simplify`.
pub struct BooleanSimplifyPass;

impl SimplificationPass for BooleanSimplifyPass {
    fn name(&self) -> &str {
        "boolean_simplify"
    }

    fn apply(&self, formula: Formula) -> Formula {
        boolean_simplify(formula)
    }
}

// ---------------------------------------------------------------------------
// dead_var_elimination
// ---------------------------------------------------------------------------

/// Remove Forall/Exists bindings for variables not referenced in the body.
/// Also simplify: if all bindings are eliminated, unwrap the quantifier.
///
/// `live_vars` is an additional set of variable names that should be considered
/// live even if they don't appear syntactically (e.g., for external references).
#[must_use]
pub fn dead_var_elimination(formula: Formula, live_vars: &FxHashSet<String>) -> Formula {
    formula.map(&mut |f| match f {
        Formula::Forall(bindings, body) => {
            let body_vars = body.free_variables();
            let kept: Vec<_> = bindings
                .into_iter()
                .filter(|(name, _)| {
                    body_vars.contains(name.as_str()) || live_vars.contains(name.as_str())
                })
                .collect();
            if kept.is_empty() { *body } else { Formula::Forall(kept, body) }
        }
        Formula::Exists(bindings, body) => {
            let body_vars = body.free_variables();
            let kept: Vec<_> = bindings
                .into_iter()
                .filter(|(name, _)| {
                    body_vars.contains(name.as_str()) || live_vars.contains(name.as_str())
                })
                .collect();
            if kept.is_empty() { *body } else { Formula::Exists(kept, body) }
        }
        other => other,
    })
}

/// Pass wrapper for `dead_var_elimination` with no external live vars.
pub struct DeadVarEliminationPass;

impl SimplificationPass for DeadVarEliminationPass {
    fn name(&self) -> &str {
        "dead_var_elimination"
    }

    fn apply(&self, formula: Formula) -> Formula {
        dead_var_elimination(formula, &FxHashSet::default())
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::Sort;

    use super::*;

    fn var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    // -----------------------------------------------------------------------
    // constant_fold tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_constant_fold_not_true() {
        let f = Formula::Not(Box::new(Formula::Bool(true)));
        assert_eq!(constant_fold(f), Formula::Bool(false));
    }

    #[test]
    fn test_constant_fold_not_false() {
        let f = Formula::Not(Box::new(Formula::Bool(false)));
        assert_eq!(constant_fold(f), Formula::Bool(true));
    }

    #[test]
    fn test_constant_fold_and_all_true() {
        let f = Formula::And(vec![Formula::Bool(true), Formula::Bool(true)]);
        assert_eq!(constant_fold(f), Formula::Bool(true));
    }

    #[test]
    fn test_constant_fold_and_one_false() {
        let f = Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]);
        assert_eq!(constant_fold(f), Formula::Bool(false));
    }

    #[test]
    fn test_constant_fold_or_all_false() {
        let f = Formula::Or(vec![Formula::Bool(false), Formula::Bool(false)]);
        assert_eq!(constant_fold(f), Formula::Bool(false));
    }

    #[test]
    fn test_constant_fold_or_one_true() {
        let f = Formula::Or(vec![Formula::Bool(false), Formula::Bool(true)]);
        assert_eq!(constant_fold(f), Formula::Bool(true));
    }

    #[test]
    fn test_constant_fold_int_arithmetic() {
        // (3 + 4) should fold to 7
        let f = Formula::Add(Box::new(Formula::Int(3)), Box::new(Formula::Int(4)));
        assert_eq!(constant_fold(f), Formula::Int(7));
    }

    #[test]
    fn test_constant_fold_int_sub() {
        let f = Formula::Sub(Box::new(Formula::Int(10)), Box::new(Formula::Int(3)));
        assert_eq!(constant_fold(f), Formula::Int(7));
    }

    #[test]
    fn test_constant_fold_int_mul() {
        let f = Formula::Mul(Box::new(Formula::Int(3)), Box::new(Formula::Int(4)));
        assert_eq!(constant_fold(f), Formula::Int(12));
    }

    #[test]
    fn test_constant_fold_int_div() {
        let f = Formula::Div(Box::new(Formula::Int(10)), Box::new(Formula::Int(3)));
        assert_eq!(constant_fold(f), Formula::Int(3));
    }

    #[test]
    fn test_constant_fold_div_by_zero_preserved() {
        let f = Formula::Div(Box::new(Formula::Int(10)), Box::new(Formula::Int(0)));
        // Should NOT fold -- division by zero preserved
        assert_eq!(
            constant_fold(f),
            Formula::Div(Box::new(Formula::Int(10)), Box::new(Formula::Int(0)))
        );
    }

    #[test]
    fn test_constant_fold_int_rem() {
        let f = Formula::Rem(Box::new(Formula::Int(10)), Box::new(Formula::Int(3)));
        assert_eq!(constant_fold(f), Formula::Int(1));
    }

    #[test]
    fn test_constant_fold_neg() {
        let f = Formula::Neg(Box::new(Formula::Int(5)));
        assert_eq!(constant_fold(f), Formula::Int(-5));
    }

    #[test]
    fn test_constant_fold_comparison_eq() {
        let f = Formula::Eq(Box::new(Formula::Int(3)), Box::new(Formula::Int(3)));
        assert_eq!(constant_fold(f), Formula::Bool(true));
    }

    #[test]
    fn test_constant_fold_comparison_lt() {
        let f = Formula::Lt(Box::new(Formula::Int(2)), Box::new(Formula::Int(3)));
        assert_eq!(constant_fold(f), Formula::Bool(true));
    }

    #[test]
    fn test_constant_fold_comparison_gt_false() {
        let f = Formula::Gt(Box::new(Formula::Int(2)), Box::new(Formula::Int(3)));
        assert_eq!(constant_fold(f), Formula::Bool(false));
    }

    #[test]
    fn test_constant_fold_implies_false_lhs() {
        let f = Formula::Implies(Box::new(Formula::Bool(false)), Box::new(var("x")));
        assert_eq!(constant_fold(f), Formula::Bool(true));
    }

    #[test]
    fn test_constant_fold_implies_true_rhs() {
        let f = Formula::Implies(Box::new(var("x")), Box::new(Formula::Bool(true)));
        assert_eq!(constant_fold(f), Formula::Bool(true));
    }

    #[test]
    fn test_constant_fold_ite_true() {
        let f = Formula::Ite(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Int(1)),
            Box::new(Formula::Int(2)),
        );
        assert_eq!(constant_fold(f), Formula::Int(1));
    }

    #[test]
    fn test_constant_fold_ite_false() {
        let f = Formula::Ite(
            Box::new(Formula::Bool(false)),
            Box::new(Formula::Int(1)),
            Box::new(Formula::Int(2)),
        );
        assert_eq!(constant_fold(f), Formula::Int(2));
    }

    #[test]
    fn test_constant_fold_nested() {
        // Not(Eq(Add(1,2), Int(3))) -> Not(Eq(3,3)) -> Not(true) -> false
        let f = Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::Add(Box::new(Formula::Int(1)), Box::new(Formula::Int(2)))),
            Box::new(Formula::Int(3)),
        )));
        assert_eq!(constant_fold(f), Formula::Bool(false));
    }

    #[test]
    fn test_constant_fold_preserves_vars() {
        let f = Formula::Add(Box::new(var("x")), Box::new(Formula::Int(1)));
        let result = constant_fold(f.clone());
        assert_eq!(result, f); // no change
    }

    // -----------------------------------------------------------------------
    // constant_fold overflow safety tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_constant_fold_add_no_overflow() {
        let f = Formula::Add(Box::new(Formula::Int(5)), Box::new(Formula::Int(3)));
        assert_eq!(constant_fold(f), Formula::Int(8));
    }

    #[test]
    fn test_constant_fold_add_overflow_unchanged() {
        // i128::MAX + 1 would wrap; must be left unsimplified for SMT.
        let f = Formula::Add(Box::new(Formula::Int(i128::MAX)), Box::new(Formula::Int(1)));
        assert_eq!(
            constant_fold(f),
            Formula::Add(Box::new(Formula::Int(i128::MAX)), Box::new(Formula::Int(1)),)
        );
    }

    #[test]
    fn test_constant_fold_sub_overflow_unchanged() {
        // i128::MIN - 1 would wrap; must be left unsimplified.
        let f = Formula::Sub(Box::new(Formula::Int(i128::MIN)), Box::new(Formula::Int(1)));
        assert_eq!(
            constant_fold(f),
            Formula::Sub(Box::new(Formula::Int(i128::MIN)), Box::new(Formula::Int(1)),)
        );
    }

    #[test]
    fn test_constant_fold_mul_overflow_unchanged() {
        // i128::MAX * 2 would wrap; must be left unsimplified.
        let f = Formula::Mul(Box::new(Formula::Int(i128::MAX)), Box::new(Formula::Int(2)));
        assert_eq!(
            constant_fold(f),
            Formula::Mul(Box::new(Formula::Int(i128::MAX)), Box::new(Formula::Int(2)),)
        );
    }

    #[test]
    fn test_constant_fold_neg_overflow_unchanged() {
        // -i128::MIN would wrap; must be left unsimplified.
        let f = Formula::Neg(Box::new(Formula::Int(i128::MIN)));
        assert_eq!(constant_fold(f), Formula::Neg(Box::new(Formula::Int(i128::MIN))));
    }

    #[test]
    fn test_constant_fold_div_overflow_unchanged() {
        // i128::MIN / -1 overflows; must be left unsimplified.
        let f = Formula::Div(Box::new(Formula::Int(i128::MIN)), Box::new(Formula::Int(-1)));
        assert_eq!(
            constant_fold(f),
            Formula::Div(Box::new(Formula::Int(i128::MIN)), Box::new(Formula::Int(-1)),)
        );
    }

    #[test]
    fn test_constant_fold_rem_overflow_unchanged() {
        // i128::MIN % -1 overflows; must be left unsimplified.
        let f = Formula::Rem(Box::new(Formula::Int(i128::MIN)), Box::new(Formula::Int(-1)));
        assert_eq!(
            constant_fold(f),
            Formula::Rem(Box::new(Formula::Int(i128::MIN)), Box::new(Formula::Int(-1)),)
        );
    }

    // -----------------------------------------------------------------------
    // boolean_simplify tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_boolean_simplify_and_identity() {
        // And(true, x) -> x
        let f = Formula::And(vec![Formula::Bool(true), var("x")]);
        assert_eq!(boolean_simplify(f), var("x"));
    }

    #[test]
    fn test_boolean_simplify_and_annihilation() {
        // And(false, x) -> false
        let f = Formula::And(vec![Formula::Bool(false), var("x")]);
        assert_eq!(boolean_simplify(f), Formula::Bool(false));
    }

    #[test]
    fn test_boolean_simplify_or_identity() {
        // Or(false, x) -> x
        let f = Formula::Or(vec![Formula::Bool(false), var("x")]);
        assert_eq!(boolean_simplify(f), var("x"));
    }

    #[test]
    fn test_boolean_simplify_or_annihilation() {
        // Or(true, x) -> true
        let f = Formula::Or(vec![Formula::Bool(true), var("x")]);
        assert_eq!(boolean_simplify(f), Formula::Bool(true));
    }

    #[test]
    fn test_boolean_simplify_double_negation() {
        // Not(Not(x)) -> x
        let f = Formula::Not(Box::new(Formula::Not(Box::new(var("x")))));
        assert_eq!(boolean_simplify(f), var("x"));
    }

    #[test]
    fn test_boolean_simplify_and_empty() {
        assert_eq!(boolean_simplify(Formula::And(vec![])), Formula::Bool(true));
    }

    #[test]
    fn test_boolean_simplify_or_empty() {
        assert_eq!(boolean_simplify(Formula::Or(vec![])), Formula::Bool(false));
    }

    #[test]
    fn test_boolean_simplify_and_singleton() {
        let f = Formula::And(vec![var("x")]);
        assert_eq!(boolean_simplify(f), var("x"));
    }

    #[test]
    fn test_boolean_simplify_or_singleton() {
        let f = Formula::Or(vec![var("x")]);
        assert_eq!(boolean_simplify(f), var("x"));
    }

    #[test]
    fn test_boolean_simplify_and_flatten() {
        // And(And(a, b), c) -> And(a, b, c)
        let f = Formula::And(vec![Formula::And(vec![var("a"), var("b")]), var("c")]);
        assert_eq!(boolean_simplify(f), Formula::And(vec![var("a"), var("b"), var("c")]));
    }

    #[test]
    fn test_boolean_simplify_or_flatten() {
        // Or(Or(a, b), c) -> Or(a, b, c)
        let f = Formula::Or(vec![Formula::Or(vec![var("a"), var("b")]), var("c")]);
        assert_eq!(boolean_simplify(f), Formula::Or(vec![var("a"), var("b"), var("c")]));
    }

    #[test]
    fn test_boolean_simplify_implies_false_lhs() {
        let f = Formula::Implies(Box::new(Formula::Bool(false)), Box::new(var("x")));
        assert_eq!(boolean_simplify(f), Formula::Bool(true));
    }

    #[test]
    fn test_boolean_simplify_implies_true_lhs() {
        let f = Formula::Implies(Box::new(Formula::Bool(true)), Box::new(var("x")));
        assert_eq!(boolean_simplify(f), var("x"));
    }

    #[test]
    fn test_boolean_simplify_implies_false_rhs() {
        let f = Formula::Implies(Box::new(var("x")), Box::new(Formula::Bool(false)));
        assert_eq!(boolean_simplify(f), Formula::Not(Box::new(var("x"))));
    }

    #[test]
    fn test_boolean_simplify_nested() {
        // And(true, Not(Not(x))) -> x
        let f = Formula::And(vec![
            Formula::Bool(true),
            Formula::Not(Box::new(Formula::Not(Box::new(var("x"))))),
        ]);
        assert_eq!(boolean_simplify(f), var("x"));
    }

    // -----------------------------------------------------------------------
    // dead_var_elimination tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_dead_var_elimination_removes_unused() {
        // Forall([x, y], x > 0) -> Forall([x], x > 0)
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int), ("y".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0)))),
        );
        let result = dead_var_elimination(f, &FxHashSet::default());
        match result {
            Formula::Forall(bindings, _) => {
                assert_eq!(bindings.len(), 1);
                assert_eq!(bindings[0].0, "x");
            }
            _ => panic!("expected Forall"),
        }
    }

    #[test]
    fn test_dead_var_elimination_removes_all_unused() {
        // Forall([x], true) -> true
        let f = Formula::Forall(vec![("x".into(), Sort::Int)], Box::new(Formula::Bool(true)));
        let result = dead_var_elimination(f, &FxHashSet::default());
        assert_eq!(result, Formula::Bool(true));
    }

    #[test]
    fn test_dead_var_elimination_keeps_all_used() {
        // Forall([x, y], x + y > 0) -> unchanged
        let body = Formula::Gt(
            Box::new(Formula::Add(Box::new(var("x")), Box::new(var("y")))),
            Box::new(Formula::Int(0)),
        );
        let f =
            Formula::Forall(vec![("x".into(), Sort::Int), ("y".into(), Sort::Int)], Box::new(body));
        let result = dead_var_elimination(f, &FxHashSet::default());
        match result {
            Formula::Forall(bindings, _) => assert_eq!(bindings.len(), 2),
            _ => panic!("expected Forall"),
        }
    }

    #[test]
    fn test_dead_var_elimination_exists() {
        // Exists([x, y], x > 0) -> Exists([x], x > 0)
        let f = Formula::Exists(
            vec![("x".into(), Sort::Int), ("y".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0)))),
        );
        let result = dead_var_elimination(f, &FxHashSet::default());
        match result {
            Formula::Exists(bindings, _) => {
                assert_eq!(bindings.len(), 1);
                assert_eq!(bindings[0].0, "x");
            }
            _ => panic!("expected Exists"),
        }
    }

    #[test]
    fn test_dead_var_elimination_respects_live_vars() {
        // Forall([x, y], x > 0) with y in live_vars -> keeps y
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int), ("y".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0)))),
        );
        let mut live = FxHashSet::default();
        live.insert("y".to_string());
        let result = dead_var_elimination(f, &live);
        match result {
            Formula::Forall(bindings, _) => {
                assert_eq!(bindings.len(), 2);
            }
            _ => panic!("expected Forall"),
        }
    }

    // -----------------------------------------------------------------------
    // measure_size tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_measure_size_leaf() {
        assert_eq!(measure_size(&Formula::Bool(true)), 1);
        assert_eq!(measure_size(&Formula::Int(42)), 1);
        assert_eq!(measure_size(&var("x")), 1);
    }

    #[test]
    fn test_measure_size_not() {
        let f = Formula::Not(Box::new(Formula::Bool(true)));
        assert_eq!(measure_size(&f), 2);
    }

    #[test]
    fn test_measure_size_complex() {
        // And(Not(x), Add(y, 1)) = And + Not + x + Add + y + 1 = 6
        let f = Formula::And(vec![
            Formula::Not(Box::new(var("x"))),
            Formula::Add(Box::new(var("y")), Box::new(Formula::Int(1))),
        ]);
        assert_eq!(measure_size(&f), 6);
    }

    // -----------------------------------------------------------------------
    // Pipeline tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_pipeline_reduces_complex_formula() {
        // And(true, Not(Not(Eq(Add(1,2), Int(3)))))
        // After constant_fold: And(true, Not(Not(true)))
        // After boolean_simplify: true
        let f = Formula::And(vec![
            Formula::Bool(true),
            Formula::Not(Box::new(Formula::Not(Box::new(Formula::Eq(
                Box::new(Formula::Add(Box::new(Formula::Int(1)), Box::new(Formula::Int(2)))),
                Box::new(Formula::Int(3)),
            ))))),
        ]);
        let before = measure_size(&f);
        let pipeline = SimplificationPipeline::default_pipeline();
        let (result, iters) = pipeline.run(f);
        let after = measure_size(&result);
        assert!(after < before, "pipeline should reduce size: {before} -> {after}");
        assert_eq!(result, Formula::Bool(true));
        assert!(iters <= 10);
    }

    #[test]
    fn test_pipeline_fixed_point_convergence() {
        // Already simplified formula should converge in 1 iteration
        let f = Formula::And(vec![var("x"), var("y")]);
        let pipeline = SimplificationPipeline::default_pipeline();
        let (result, iters) = pipeline.run(f.clone());
        assert_eq!(result, f);
        assert_eq!(iters, 1, "already-simplified formula should converge in 1 iter");
    }

    #[test]
    fn test_pipeline_with_dead_var_elimination() {
        let pipeline = SimplificationPipeline::new(
            vec![
                Box::new(ConstantFoldPass),
                Box::new(BooleanSimplifyPass),
                Box::new(DeadVarEliminationPass),
            ],
            10,
        );

        // Forall([x, y], And(true, x > 0)) -> Forall([x], x > 0)
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int), ("y".into(), Sort::Int)],
            Box::new(Formula::And(vec![
                Formula::Bool(true),
                Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))),
            ])),
        );

        let (result, _iters) = pipeline.run(f);
        match &result {
            Formula::Forall(bindings, _) => {
                assert_eq!(bindings.len(), 1, "y should be eliminated");
                assert_eq!(bindings[0].0, "x");
            }
            _ => panic!("expected Forall, got: {result:?}"),
        }
    }

    #[test]
    fn test_pipeline_max_iters_respected() {
        // A pass that always changes something (adds a Not wrapper)
        // should be bounded by max_iters. We test with max_iters=1.
        let pipeline = SimplificationPipeline::new(vec![], 1);
        let f = var("x");
        let (_result, iters) = pipeline.run(f);
        assert_eq!(iters, 1);
    }

    #[test]
    fn test_combined_constant_fold_and_boolean_simplify() {
        // Or(false, And(true, Le(1, 2)))
        // constant_fold: Or(false, And(true, true))
        // constant_fold on And: Or(false, true)
        // constant_fold on Or: true
        // (all in one bottom-up pass)
        let f = Formula::Or(vec![
            Formula::Bool(false),
            Formula::And(vec![
                Formula::Bool(true),
                Formula::Le(Box::new(Formula::Int(1)), Box::new(Formula::Int(2))),
            ]),
        ]);
        let pipeline = SimplificationPipeline::default_pipeline();
        let (result, _) = pipeline.run(f);
        assert_eq!(result, Formula::Bool(true));
    }

    // -----------------------------------------------------------------------
    // New simplification rules
    // -----------------------------------------------------------------------

    // --- Reflexive equality: Eq(x, x) -> true ---

    #[test]
    fn test_constant_fold_eq_reflexive_var() {
        let f = Formula::Eq(Box::new(var("x")), Box::new(var("x")));
        assert_eq!(constant_fold(f), Formula::Bool(true));
    }

    #[test]
    fn test_constant_fold_eq_reflexive_complex() {
        // Eq(Add(x, y), Add(x, y)) -> true
        let expr = Formula::Add(Box::new(var("x")), Box::new(var("y")));
        let f = Formula::Eq(Box::new(expr.clone()), Box::new(expr));
        assert_eq!(constant_fold(f), Formula::Bool(true));
    }

    #[test]
    fn test_constant_fold_eq_different_vars_not_folded() {
        let f = Formula::Eq(Box::new(var("x")), Box::new(var("y")));
        assert_eq!(constant_fold(f), Formula::Eq(Box::new(var("x")), Box::new(var("y"))));
    }

    // --- Contradiction detection: And([P, Not(P)]) -> false ---

    #[test]
    fn test_boolean_simplify_and_contradiction() {
        // And(x, Not(x)) -> false
        let f = Formula::And(vec![var("x"), Formula::Not(Box::new(var("x")))]);
        assert_eq!(boolean_simplify(f), Formula::Bool(false));
    }

    #[test]
    fn test_boolean_simplify_and_contradiction_with_extra_terms() {
        // And(y, x, Not(x)) -> false
        let f = Formula::And(vec![var("y"), var("x"), Formula::Not(Box::new(var("x")))]);
        assert_eq!(boolean_simplify(f), Formula::Bool(false));
    }

    #[test]
    fn test_boolean_simplify_and_contradiction_complex_formula() {
        // And(Gt(x, 0), Not(Gt(x, 0))) -> false
        let gt = Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0)));
        let f = Formula::And(vec![gt.clone(), Formula::Not(Box::new(gt))]);
        assert_eq!(boolean_simplify(f), Formula::Bool(false));
    }

    #[test]
    fn test_boolean_simplify_and_no_false_contradiction_different_terms() {
        // And(x, Not(y)) should NOT simplify to false (different formulas)
        let f = Formula::And(vec![var("x"), Formula::Not(Box::new(var("y")))]);
        assert_eq!(
            boolean_simplify(f),
            Formula::And(vec![var("x"), Formula::Not(Box::new(var("y")))])
        );
    }

    // --- Excluded middle: Or([P, Not(P)]) -> true ---

    #[test]
    fn test_boolean_simplify_or_excluded_middle() {
        // Or(x, Not(x)) -> true
        let f = Formula::Or(vec![var("x"), Formula::Not(Box::new(var("x")))]);
        assert_eq!(boolean_simplify(f), Formula::Bool(true));
    }

    #[test]
    fn test_boolean_simplify_or_excluded_middle_with_extra_terms() {
        // Or(y, x, Not(x)) -> true
        let f = Formula::Or(vec![var("y"), var("x"), Formula::Not(Box::new(var("x")))]);
        assert_eq!(boolean_simplify(f), Formula::Bool(true));
    }

    #[test]
    fn test_boolean_simplify_or_no_tautology_different_terms() {
        // Or(x, Not(y)) should NOT simplify to true
        let f = Formula::Or(vec![var("x"), Formula::Not(Box::new(var("y")))]);
        assert_eq!(
            boolean_simplify(f),
            Formula::Or(vec![var("x"), Formula::Not(Box::new(var("y")))])
        );
    }

    // --- Pipeline integration for new rules ---

    #[test]
    fn test_pipeline_eq_reflexive_in_and() {
        // And(Eq(x, x), Gt(y, 0)) -> Gt(y, 0)
        // constant_fold: And(true, Gt(y, 0))
        // boolean_simplify: Gt(y, 0)
        let f = Formula::And(vec![
            Formula::Eq(Box::new(var("x")), Box::new(var("x"))),
            Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(0))),
        ]);
        let pipeline = SimplificationPipeline::default_pipeline();
        let (result, _) = pipeline.run(f);
        assert_eq!(result, Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(0))));
    }

    #[test]
    fn test_pipeline_contradiction_simplifies() {
        // And(x, Not(x), y) -> false
        let f = Formula::And(vec![var("x"), Formula::Not(Box::new(var("x"))), var("y")]);
        let pipeline = SimplificationPipeline::default_pipeline();
        let (result, _) = pipeline.run(f);
        assert_eq!(result, Formula::Bool(false));
    }

    #[test]
    fn test_pipeline_excluded_middle_simplifies() {
        // Or(x, Not(x), y) -> true
        let f = Formula::Or(vec![var("x"), Formula::Not(Box::new(var("x"))), var("y")]);
        let pipeline = SimplificationPipeline::default_pipeline();
        let (result, _) = pipeline.run(f);
        assert_eq!(result, Formula::Bool(true));
    }
}
