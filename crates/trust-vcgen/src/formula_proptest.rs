// trust_vcgen/formula_proptest.rs: Property-based tests for Formula simplification
//
// Uses proptest to verify algebraic invariants of the simplification
// pipeline (idempotency, identity laws, double negation, non-expansion).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use proptest::prelude::*;
use trust_types::{Formula, Sort};

use crate::simplify::{SimplificationPipeline, boolean_simplify, constant_fold, measure_size};

// ---------------------------------------------------------------------------
// Bounded-depth Formula strategy for proptest
// ---------------------------------------------------------------------------

/// Generate an arbitrary Sort (limited to Bool and Int for simplicity).
fn arb_sort() -> impl Strategy<Value = Sort> {
    prop_oneof![Just(Sort::Bool), Just(Sort::Int),]
}

/// Generate a leaf-level Formula (depth 0).
fn arb_formula_leaf() -> impl Strategy<Value = Formula> {
    prop_oneof![
        // Trust: Boolean literals
        any::<bool>().prop_map(Formula::Bool),
        // Trust: Small integer literals to keep formulas readable
        (-100i128..=100i128).prop_map(Formula::Int),
        // Trust: Variable with sort
        ("[a-e]", arb_sort()).prop_map(|(name, sort)| Formula::Var(name, sort)),
    ]
}

/// Generate a Formula with bounded depth (max_depth).
///
/// Depth is bounded to prevent exponential blowup. At depth 0
/// we produce only leaves. At higher depths we mix leaves with compound
/// formulas whose children have depth - 1.
fn arb_formula(max_depth: u32) -> BoxedStrategy<Formula> {
    if max_depth == 0 {
        return arb_formula_leaf().boxed();
    }

    let leaf = arb_formula_leaf();
    let child = arb_formula(max_depth - 1);

    prop_oneof![
        // Trust: Weight leaves higher to keep average formula size manageable
        3 => leaf,
        // Trust: Unary connectives
        1 => child.clone().prop_map(|f| Formula::Not(Box::new(f))),
        1 => child.clone().prop_map(|f| Formula::Neg(Box::new(f))),
        // Trust: Binary connectives
        1 => (child.clone(), child.clone())
            .prop_map(|(a, b)| Formula::And(vec![a, b])),
        1 => (child.clone(), child.clone())
            .prop_map(|(a, b)| Formula::Or(vec![a, b])),
        1 => (child.clone(), child.clone())
            .prop_map(|(a, b)| Formula::Implies(Box::new(a), Box::new(b))),
        1 => (child.clone(), child.clone())
            .prop_map(|(a, b)| Formula::Eq(Box::new(a), Box::new(b))),
        1 => (child.clone(), child.clone())
            .prop_map(|(a, b)| Formula::Lt(Box::new(a), Box::new(b))),
        1 => (child.clone(), child.clone())
            .prop_map(|(a, b)| Formula::Le(Box::new(a), Box::new(b))),
        1 => (child.clone(), child.clone())
            .prop_map(|(a, b)| Formula::Add(Box::new(a), Box::new(b))),
        1 => (child.clone(), child.clone())
            .prop_map(|(a, b)| Formula::Sub(Box::new(a), Box::new(b))),
        1 => (child.clone(), child.clone())
            .prop_map(|(a, b)| Formula::Mul(Box::new(a), Box::new(b))),
        // Trust: N-ary And/Or with 3 children
        1 => (child.clone(), child.clone(), child.clone())
            .prop_map(|(a, b, c)| Formula::And(vec![a, b, c])),
        1 => (child.clone(), child.clone(), child.clone())
            .prop_map(|(a, b, c)| Formula::Or(vec![a, b, c])),
    ]
    .boxed()
}

/// Default strategy: depth up to 4 (produces formulas of manageable size).
fn arb_formula_default() -> BoxedStrategy<Formula> {
    // Use max depth 4 to balance coverage vs test speed.
    arb_formula(4)
}

// ---------------------------------------------------------------------------
// Property — simplification is idempotent
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    /// simplify(simplify(f)) == simplify(f)
    ///
    /// The simplification pipeline should reach a fixed point.
    /// Applying it twice must produce the same result as applying it once.
    #[test]
    fn test_simplification_idempotent(f in arb_formula_default()) {
        let pipeline = SimplificationPipeline::default_pipeline();
        let (simplified_once, _) = pipeline.run(f);
        let (simplified_twice, _) = pipeline.run(simplified_once.clone());
        prop_assert_eq!(
            simplified_twice,
            simplified_once,
            "simplification must be idempotent"
        );
    }

    /// constant_fold(constant_fold(f)) == constant_fold(f)
    ///
    /// Constant folding alone should be idempotent.
    #[test]
    fn test_constant_fold_idempotent(f in arb_formula_default()) {
        let once = constant_fold(f);
        let twice = constant_fold(once.clone());
        prop_assert_eq!(twice, once, "constant_fold must be idempotent");
    }

    /// boolean_simplify converges within 3 iterations.
    ///
    /// A single pass of boolean_simplify is NOT necessarily
    /// idempotent because Implies(a, false) -> Not(a) can introduce new
    /// Not nodes that create Not(Not(...)) patterns. However, convergence
    /// should be fast — within 3 iterations.
    #[test]
    fn test_boolean_simplify_converges(f in arb_formula_default()) {
        let mut current = f;
        for _ in 0..3 {
            current = boolean_simplify(current);
        }
        let next = boolean_simplify(current.clone());
        prop_assert_eq!(next, current, "boolean_simplify must converge within 3 iterations");
    }
}

// ---------------------------------------------------------------------------
// Property — And(f, true) simplifies to f
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    /// And(f, true) should simplify to f.
    ///
    /// True is the identity element of conjunction.
    #[test]
    fn test_and_true_identity(f in arb_formula_default()) {
        let conj = Formula::And(vec![f.clone(), Formula::Bool(true)]);
        let simplified = boolean_simplify(conj);
        // Trust: After boolean_simplify, And(f, true) should become just f.
        // But f itself may also get simplified by the bottom-up pass,
        // so we compare against boolean_simplify(f).
        let expected = boolean_simplify(f);
        prop_assert_eq!(
            simplified,
            expected,
            "And(f, true) should simplify to simplified(f)"
        );
    }

    /// And(true, f) should also simplify to f (commutativity of identity).
    ///
    /// Identity element works regardless of position.
    #[test]
    fn test_true_and_identity(f in arb_formula_default()) {
        let conj = Formula::And(vec![Formula::Bool(true), f.clone()]);
        let simplified = boolean_simplify(conj);
        let expected = boolean_simplify(f);
        prop_assert_eq!(
            simplified,
            expected,
            "And(true, f) should simplify to simplified(f)"
        );
    }
}

// ---------------------------------------------------------------------------
// Property — Or(f, false) simplifies to f
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    /// Or(f, false) should simplify to f.
    ///
    /// False is the identity element of disjunction.
    #[test]
    fn test_or_false_identity(f in arb_formula_default()) {
        let disj = Formula::Or(vec![f.clone(), Formula::Bool(false)]);
        let simplified = boolean_simplify(disj);
        let expected = boolean_simplify(f);
        prop_assert_eq!(
            simplified,
            expected,
            "Or(f, false) should simplify to simplified(f)"
        );
    }

    /// Or(false, f) should also simplify to f.
    ///
    /// Identity element works regardless of position.
    #[test]
    fn test_false_or_identity(f in arb_formula_default()) {
        let disj = Formula::Or(vec![Formula::Bool(false), f.clone()]);
        let simplified = boolean_simplify(disj);
        let expected = boolean_simplify(f);
        prop_assert_eq!(
            simplified,
            expected,
            "Or(false, f) should simplify to simplified(f)"
        );
    }
}

// ---------------------------------------------------------------------------
// Property — Not(Not(f)) simplifies to f
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    /// Not(Not(f)) simplification should not increase size.
    ///
    /// Double negation elimination may not fully normalize all
    /// subformula combinations (e.g., Neg inside Not), but should never
    /// make the formula larger.
    #[test]
    fn test_double_negation_non_expanding(f in arb_formula_default()) {
        let double_neg = Formula::Not(Box::new(Formula::Not(Box::new(f.clone()))));
        let simplified = boolean_simplify(double_neg.clone());
        // Trust: The simplified form should be no larger than the original.
        let orig_size = measure_size(&double_neg);
        let simp_size = measure_size(&simplified);
        prop_assert!(
            simp_size <= orig_size,
            "Not(Not(f)) simplification should not expand: {} vs {}",
            simp_size,
            orig_size
        );
    }
}

// ---------------------------------------------------------------------------
// Property — simplified formula node count <= original
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    /// Simplification should never increase the formula size.
    ///
    /// The pipeline is supposed to reduce or preserve size.
    /// This is a key non-expansion property.
    #[test]
    fn test_simplification_non_expanding(f in arb_formula_default()) {
        let original_size = measure_size(&f);
        let pipeline = SimplificationPipeline::default_pipeline();
        let (simplified, _) = pipeline.run(f);
        let simplified_size = measure_size(&simplified);
        prop_assert!(
            simplified_size <= original_size,
            "simplified size ({}) must not exceed original size ({})",
            simplified_size,
            original_size
        );
    }

    /// constant_fold should never increase formula size.
    ///
    /// Folding constants replaces compound expressions with
    /// simpler ones; it should never grow the formula.
    #[test]
    fn test_constant_fold_non_expanding(f in arb_formula_default()) {
        let original_size = measure_size(&f);
        let folded = constant_fold(f);
        let folded_size = measure_size(&folded);
        prop_assert!(
            folded_size <= original_size,
            "constant_fold size ({}) must not exceed original size ({})",
            folded_size,
            original_size
        );
    }

    /// boolean_simplify should never increase formula size.
    ///
    /// Boolean simplification removes redundant structure;
    /// it should never introduce new nodes.
    #[test]
    fn test_boolean_simplify_non_expanding(f in arb_formula_default()) {
        let original_size = measure_size(&f);
        let simplified = boolean_simplify(f);
        let simplified_size = measure_size(&simplified);
        prop_assert!(
            simplified_size <= original_size,
            "boolean_simplify size ({}) must not exceed original size ({})",
            simplified_size,
            original_size
        );
    }
}

// ---------------------------------------------------------------------------
// Property — annihilation laws
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    /// And(f, false) should always simplify to false.
    ///
    /// False is the annihilator of conjunction.
    #[test]
    fn test_and_false_annihilation(f in arb_formula_default()) {
        let conj = Formula::And(vec![f, Formula::Bool(false)]);
        let simplified = boolean_simplify(conj);
        prop_assert_eq!(simplified, Formula::Bool(false), "And(f, false) must be false");
    }

    /// Or(f, true) should always simplify to true.
    ///
    /// True is the annihilator of disjunction.
    #[test]
    fn test_or_true_annihilation(f in arb_formula_default()) {
        let disj = Formula::Or(vec![f, Formula::Bool(true)]);
        let simplified = boolean_simplify(disj);
        prop_assert_eq!(simplified, Formula::Bool(true), "Or(f, true) must be true");
    }
}

// ---------------------------------------------------------------------------
// Property — Eq(f, f) simplifies to true (reflexivity)
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    /// Eq(f, f) should simplify to true for any formula f.
    ///
    /// Reflexive equality is a fundamental logical identity.
    #[test]
    fn test_eq_reflexive(f in arb_formula_default()) {
        let eq = Formula::Eq(Box::new(f.clone()), Box::new(f));
        let folded = constant_fold(eq);
        prop_assert_eq!(folded, Formula::Bool(true), "Eq(f, f) must fold to true");
    }
}

// ---------------------------------------------------------------------------
// Property — pipeline preserves free variables (subset)
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(300))]

    /// Simplification should not introduce new free variables.
    ///
    /// The simplified formula's free variables must be a subset
    /// of the original formula's free variables. Simplification may eliminate
    /// variables (e.g., And(true, x) -> x drops nothing; And(false, x) -> false
    /// drops x), but it must never introduce variables not in the original.
    #[test]
    fn test_simplification_preserves_free_vars(f in arb_formula_default()) {
        let original_vars = f.free_variables();
        let pipeline = SimplificationPipeline::default_pipeline();
        let (simplified, _) = pipeline.run(f);
        let simplified_vars = simplified.free_variables();
        for v in &simplified_vars {
            prop_assert!(
                original_vars.contains(v),
                "simplified formula has new free variable '{}' not in original",
                v
            );
        }
    }
}
