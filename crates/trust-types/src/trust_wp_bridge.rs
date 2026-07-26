// trust-types/trust_wp_bridge.rs: Conversion bridge between trust_types::Formula and trust_wp_core PureExpr
//
// Phase 1 of trust_wp native integration. Converts trust-types
// Formula (SMT-oriented) to trust-wp-core PureExpr (Rust-oriented) for use
// by the TrustWpNativeBackend in trust-router.
//
// Design: designs/2026-04-13-trust-wp-integration-design.md
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::Arc;

use trust_wp_core::formula::{BinOp as SBinOp, ExprSort, PureExpr, UnOp as SUnOp};

use crate::formula::{Formula, Sort};

/// Convert a trust-types `Sort` to a trust-wp-core `ExprSort`.
///
/// Returns `None` for sorts that trust_wp does not support (bitvectors, arrays).
/// trust_wp operates on mathematical integers and booleans -- no BV theory.
#[must_use]
pub fn sort_to_expr_sort(sort: &Sort) -> Option<ExprSort> {
    match sort {
        Sort::Bool => Some(ExprSort::Bool),
        Sort::Int => Some(ExprSort::Int),
        // trust_wp has no bitvector theory -- reject
        Sort::BitVec(_) => None,
        // trust_wp has no array theory initially -- reject
        Sort::Array(_, _) => None,
        // `Sort` is #[non_exhaustive] (trust-ir-contract); fail-closed for any
        // sort outside trust_wp's int/bool fragment.
        _ => None,
    }
}

/// Convert a trust-types `Formula` to a trust-wp-core `PureExpr`.
///
/// Returns `None` if the formula contains unsupported constructs
/// (bitvectors, array theory). The caller should fall back to another backend.
///
/// # Design notes
///
/// - `Int(n)` where `n > i64::MAX` or `n < i64::MIN` returns `None` (trust-wp uses i64)
/// - `UInt(n)` where `n > i64::MAX` returns `None`
/// - `And(fs)` folds left: `fs[0] && fs[1] && ... && fs[n]`
/// - `Forall(vars, body)` nests: `Forall { var: vars[0], body: Forall { var: vars[1], ... } }`
/// - All BV variants return `None` immediately
/// - Select/Store (array theory) return `None`
#[must_use]
pub fn formula_to_pure_expr(formula: &Formula) -> Option<PureExpr> {
    match formula {
        // --- Literals ---
        Formula::Bool(b) => Some(PureExpr::Bool(*b)),
        Formula::Int(n) => {
            // trust-wp-core uses i64; reject values outside range
            let n64 = i64::try_from(*n).ok()?;
            Some(PureExpr::Int(n64))
        }
        Formula::UInt(n) => {
            let n64 = i64::try_from(*n).ok()?;
            Some(PureExpr::Int(n64))
        }
        // trust_wp has no bitvector theory
        Formula::BitVec { .. } => None,

        // --- Variables ---
        Formula::Var(name, sort) => {
            let expr_sort = sort_to_expr_sort(sort)?;
            Some(PureExpr::Var(name.clone(), Some(expr_sort)))
        }

        // --- Boolean connectives ---
        Formula::Not(a) => {
            let inner = formula_to_pure_expr(a)?;
            Some(PureExpr::UnOp(SUnOp::Not, Arc::new(inner)))
        }
        Formula::And(terms) => {
            if terms.is_empty() {
                return Some(PureExpr::Bool(true));
            }
            let mut result = formula_to_pure_expr(&terms[0])?;
            for term in &terms[1..] {
                let rhs = formula_to_pure_expr(term)?;
                result = PureExpr::BinOp(Arc::new(result), SBinOp::And, Arc::new(rhs));
            }
            Some(result)
        }
        Formula::Or(terms) => {
            if terms.is_empty() {
                return Some(PureExpr::Bool(false));
            }
            let mut result = formula_to_pure_expr(&terms[0])?;
            for term in &terms[1..] {
                let rhs = formula_to_pure_expr(term)?;
                result = PureExpr::BinOp(Arc::new(result), SBinOp::Or, Arc::new(rhs));
            }
            Some(result)
        }
        Formula::Implies(a, b) => {
            let lhs = formula_to_pure_expr(a)?;
            let rhs = formula_to_pure_expr(b)?;
            Some(PureExpr::BinOp(Arc::new(lhs), SBinOp::Implies, Arc::new(rhs)))
        }

        // --- Comparisons ---
        Formula::Eq(a, b) => bin_op(a, SBinOp::Eq, b),
        Formula::Lt(a, b) => bin_op(a, SBinOp::Lt, b),
        Formula::Le(a, b) => bin_op(a, SBinOp::Le, b),
        Formula::Gt(a, b) => bin_op(a, SBinOp::Gt, b),
        Formula::Ge(a, b) => bin_op(a, SBinOp::Ge, b),

        // --- Integer arithmetic ---
        Formula::Add(a, b) => bin_op(a, SBinOp::Add, b),
        Formula::Sub(a, b) => bin_op(a, SBinOp::Sub, b),
        Formula::Mul(a, b) => bin_op(a, SBinOp::Mul, b),
        Formula::Div(a, b) => bin_op(a, SBinOp::Div, b),
        Formula::Rem(a, b) => bin_op(a, SBinOp::Mod, b),
        Formula::Neg(a) => {
            let inner = formula_to_pure_expr(a)?;
            Some(PureExpr::UnOp(SUnOp::Neg, Arc::new(inner)))
        }

        // --- Bitvector arithmetic (unsupported) ---
        Formula::BvAdd(..)
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
        | Formula::BvAShr(..) => None,

        // --- Bitvector comparisons (unsupported) ---
        Formula::BvULt(..) | Formula::BvULe(..) | Formula::BvSLt(..) | Formula::BvSLe(..) => None,

        // --- Bitvector conversions (unsupported) ---
        Formula::BvToInt(..)
        | Formula::IntToBv(..)
        | Formula::BvExtract { .. }
        | Formula::BvConcat(..)
        | Formula::BvZeroExt(..)
        | Formula::BvSignExt(..) => None,

        // --- Conditional ---
        Formula::Ite(cond, then_, else_) => {
            let c = formula_to_pure_expr(cond)?;
            let t = formula_to_pure_expr(then_)?;
            let e = formula_to_pure_expr(else_)?;
            Some(PureExpr::Ite(Arc::new(c), Arc::new(t), Arc::new(e)))
        }

        // --- Quantifiers ---
        Formula::Forall(bindings, body) => {
            if bindings.is_empty() {
                return formula_to_pure_expr(body);
            }
            let body_expr = formula_to_pure_expr(body)?;
            // Nest quantifiers: one Forall per binding, innermost first
            let mut result = body_expr;
            for (name, sort) in bindings.iter().rev() {
                let var_sort = sort_to_expr_sort(sort)?;
                result = PureExpr::Forall {
                    var: name.as_str().to_owned(),
                    var_sort: Some(var_sort),
                    body: Arc::new(result),
                    triggers: vec![],
                };
            }
            Some(result)
        }
        Formula::Exists(bindings, body) => {
            if bindings.is_empty() {
                return formula_to_pure_expr(body);
            }
            let body_expr = formula_to_pure_expr(body)?;
            let mut result = body_expr;
            for (name, sort) in bindings.iter().rev() {
                let var_sort = sort_to_expr_sort(sort)?;
                result = PureExpr::Exists {
                    var: name.as_str().to_owned(),
                    var_sort: Some(var_sort),
                    body: Arc::new(result),
                    triggers: vec![],
                };
            }
            Some(result)
        }

        // --- Array theory (unsupported initially) ---
        Formula::Select(..) | Formula::Store(..) => None,

        // Trust: Handle future #[non_exhaustive] variants gracefully
        _ => None,
    }
}

/// Helper: create a binary operation PureExpr from two Formula operands.
fn bin_op(lhs: &Formula, op: SBinOp, rhs: &Formula) -> Option<PureExpr> {
    let l = formula_to_pure_expr(lhs)?;
    let r = formula_to_pure_expr(rhs)?;
    Some(PureExpr::BinOp(Arc::new(l), op, Arc::new(r)))
}

/// Batch-convert a slice of trust-types `Formula`s to trust-wp-core `PureExpr`s.
///
/// Used by the trust_wp backend to translate structured contract IR
/// (preconditions/postconditions) into PureExpr slices for
/// `SmtGenerator::generate_vc(requires, ensures)`.
///
/// Returns `None` if ANY formula in the slice fails to translate. This is
/// intentional: a partially-translated contract is unsound (missing a
/// precondition weakens the proof obligation). The caller should fall back
/// to the monolithic approach.
#[must_use]
pub fn translate_formulas(formulas: &[Formula]) -> Option<Vec<PureExpr>> {
    formulas.iter().map(formula_to_pure_expr).collect()
}

/// Cheap check: does this formula contain any bitvector operations or types?
///
/// Used by the trust_wp router to quickly reject formulas that cannot be translated
/// to `PureExpr` without a full translation attempt. Delegates to
/// `Formula::has_bitvectors()` which performs a recursive visit.
#[must_use]
pub fn has_bv_ops(formula: &Formula) -> bool {
    formula.has_bitvectors()
}

/// Cheap check: does this formula contain array theory operations (Select/Store)?
///
/// trust_wp has no array theory, so formulas with array ops must be routed elsewhere.
#[must_use]
pub fn has_array_ops(formula: &Formula) -> bool {
    let mut found = false;
    formula.visit(&mut |f| {
        if found {
            return;
        }
        match f {
            Formula::Select(..) | Formula::Store(..) => found = true,
            Formula::Var(_, Sort::Array(_, _)) => found = true,
            _ => {}
        }
    });
    found
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sort_to_expr_sort_int() {
        assert_eq!(sort_to_expr_sort(&Sort::Int), Some(ExprSort::Int));
    }

    #[test]
    fn test_sort_to_expr_sort_bool() {
        assert_eq!(sort_to_expr_sort(&Sort::Bool), Some(ExprSort::Bool));
    }

    #[test]
    fn test_sort_to_expr_sort_bitvec_rejected() {
        assert_eq!(sort_to_expr_sort(&Sort::BitVec(32)), None);
    }

    #[test]
    fn test_sort_to_expr_sort_array_rejected() {
        assert_eq!(sort_to_expr_sort(&Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int))), None,);
    }

    #[test]
    fn test_formula_bool_true() {
        assert_eq!(formula_to_pure_expr(&Formula::Bool(true)), Some(PureExpr::Bool(true)),);
    }

    #[test]
    fn test_formula_bool_false() {
        assert_eq!(formula_to_pure_expr(&Formula::Bool(false)), Some(PureExpr::Bool(false)),);
    }

    #[test]
    fn test_formula_int_within_i64() {
        assert_eq!(formula_to_pure_expr(&Formula::Int(42)), Some(PureExpr::Int(42)),);
    }

    #[test]
    fn test_formula_int_negative() {
        assert_eq!(formula_to_pure_expr(&Formula::Int(-100)), Some(PureExpr::Int(-100)),);
    }

    #[test]
    fn test_formula_int_exceeds_i64_rejected() {
        assert_eq!(formula_to_pure_expr(&Formula::Int(i128::from(i64::MAX) + 1)), None,);
    }

    #[test]
    fn test_formula_uint_within_i64() {
        assert_eq!(formula_to_pure_expr(&Formula::UInt(100)), Some(PureExpr::Int(100)),);
    }

    #[test]
    fn test_formula_uint_exceeds_i64_rejected() {
        assert_eq!(formula_to_pure_expr(&Formula::UInt(u128::from(i64::MAX as u64) + 1)), None,);
    }

    #[test]
    fn test_formula_bitvec_rejected() {
        assert_eq!(formula_to_pure_expr(&Formula::BitVec { value: 0, width: 32 }), None,);
    }

    #[test]
    fn test_formula_var_int() {
        assert_eq!(
            formula_to_pure_expr(&Formula::Var("x".into(), Sort::Int)),
            Some(PureExpr::Var("x".into(), Some(ExprSort::Int))),
        );
    }

    #[test]
    fn test_formula_var_bitvec_rejected() {
        assert_eq!(formula_to_pure_expr(&Formula::Var("x".into(), Sort::BitVec(64))), None,);
    }

    #[test]
    fn test_formula_not() {
        let f = Formula::Not(Box::new(Formula::Bool(true)));
        let result = formula_to_pure_expr(&f).unwrap();
        assert_eq!(result, PureExpr::UnOp(SUnOp::Not, Arc::new(PureExpr::Bool(true))),);
    }

    #[test]
    fn test_formula_and_two() {
        let f = Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]);
        let result = formula_to_pure_expr(&f).unwrap();
        assert_eq!(
            result,
            PureExpr::BinOp(
                Arc::new(PureExpr::Bool(true)),
                SBinOp::And,
                Arc::new(PureExpr::Bool(false)),
            ),
        );
    }

    #[test]
    fn test_formula_and_empty() {
        assert_eq!(formula_to_pure_expr(&Formula::And(vec![])), Some(PureExpr::Bool(true)),);
    }

    #[test]
    fn test_formula_or_empty() {
        assert_eq!(formula_to_pure_expr(&Formula::Or(vec![])), Some(PureExpr::Bool(false)),);
    }

    #[test]
    fn test_formula_implies() {
        let f = Formula::Implies(Box::new(Formula::Bool(true)), Box::new(Formula::Bool(false)));
        let result = formula_to_pure_expr(&f).unwrap();
        assert_eq!(
            result,
            PureExpr::BinOp(
                Arc::new(PureExpr::Bool(true)),
                SBinOp::Implies,
                Arc::new(PureExpr::Bool(false)),
            ),
        );
    }

    #[test]
    fn test_formula_comparison_lt() {
        let f =
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(10)));
        let result = formula_to_pure_expr(&f).unwrap();
        assert_eq!(
            result,
            PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".into(), Some(ExprSort::Int))),
                SBinOp::Lt,
                Arc::new(PureExpr::Int(10)),
            ),
        );
    }

    #[test]
    fn test_formula_arithmetic_add() {
        let f =
            Formula::Add(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(1)));
        let result = formula_to_pure_expr(&f).unwrap();
        assert_eq!(
            result,
            PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".into(), Some(ExprSort::Int))),
                SBinOp::Add,
                Arc::new(PureExpr::Int(1)),
            ),
        );
    }

    #[test]
    fn test_formula_neg() {
        let f = Formula::Neg(Box::new(Formula::Int(5)));
        let result = formula_to_pure_expr(&f).unwrap();
        assert_eq!(result, PureExpr::UnOp(SUnOp::Neg, Arc::new(PureExpr::Int(5))),);
    }

    #[test]
    fn test_formula_ite() {
        let f = Formula::Ite(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Int(1)),
            Box::new(Formula::Int(0)),
        );
        let result = formula_to_pure_expr(&f).unwrap();
        assert_eq!(
            result,
            PureExpr::Ite(
                Arc::new(PureExpr::Bool(true)),
                Arc::new(PureExpr::Int(1)),
                Arc::new(PureExpr::Int(0)),
            ),
        );
    }

    #[test]
    fn test_formula_forall_single_binding() {
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Gt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
        );
        let result = formula_to_pure_expr(&f).unwrap();
        assert!(matches!(result, PureExpr::Forall { var, .. } if var == "x"));
    }

    #[test]
    fn test_formula_forall_multiple_bindings_nests() {
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int), ("y".into(), Sort::Bool)],
            Box::new(Formula::Bool(true)),
        );
        let result = formula_to_pure_expr(&f).unwrap();
        // Should be Forall x { Forall y { true } }
        match result {
            PureExpr::Forall { var, body, .. } => {
                assert_eq!(var, "x");
                match body.as_ref() {
                    PureExpr::Forall { var: inner_var, .. } => {
                        assert_eq!(inner_var, "y");
                    }
                    other => panic!("expected nested Forall, got: {other:?}"),
                }
            }
            other => panic!("expected Forall, got: {other:?}"),
        }
    }

    #[test]
    fn test_formula_forall_bitvec_binding_rejected() {
        let f =
            Formula::Forall(vec![("x".into(), Sort::BitVec(32))], Box::new(Formula::Bool(true)));
        assert_eq!(formula_to_pure_expr(&f), None);
    }

    #[test]
    fn test_formula_exists() {
        let f = Formula::Exists(vec![("x".into(), Sort::Int)], Box::new(Formula::Bool(true)));
        let result = formula_to_pure_expr(&f).unwrap();
        assert!(matches!(result, PureExpr::Exists { var, .. } if var == "x"));
    }

    #[test]
    fn test_formula_select_rejected() {
        let f = Formula::Select(
            Box::new(Formula::Var(
                "arr".into(),
                Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
            )),
            Box::new(Formula::Int(0)),
        );
        assert_eq!(formula_to_pure_expr(&f), None);
    }

    #[test]
    fn test_formula_bv_arithmetic_rejected() {
        let f = Formula::BvAdd(
            Box::new(Formula::Var("x".into(), Sort::BitVec(64))),
            Box::new(Formula::Var("y".into(), Sort::BitVec(64))),
            64,
        );
        assert_eq!(formula_to_pure_expr(&f), None);
    }

    #[test]
    fn test_complex_formula() {
        // forall x: Int. (x > 0) implies (x + 1 > 0)
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Implies(
                Box::new(Formula::Gt(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                )),
                Box::new(Formula::Gt(
                    Box::new(Formula::Add(
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                        Box::new(Formula::Int(1)),
                    )),
                    Box::new(Formula::Int(0)),
                )),
            )),
        );
        let result = formula_to_pure_expr(&f);
        assert!(result.is_some(), "complex integer formula should translate");
    }

    #[test]
    fn test_mixed_bv_and_int_rejected() {
        // And(x > 0, bvadd(y, z) == 0) should reject because of BV
        let f = Formula::And(vec![
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0))),
            Formula::Eq(
                Box::new(Formula::BvAdd(
                    Box::new(Formula::Var("y".into(), Sort::BitVec(32))),
                    Box::new(Formula::Var("z".into(), Sort::BitVec(32))),
                    32,
                )),
                Box::new(Formula::Int(0)),
            ),
        ]);
        assert_eq!(formula_to_pure_expr(&f), None);
    }

    // --- has_bv_ops tests ---

    #[test]
    fn test_has_bv_ops_pure_int() {
        let f =
            Formula::Add(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(1)));
        assert!(!has_bv_ops(&f));
    }

    #[test]
    fn test_has_bv_ops_with_bv_literal() {
        let f = Formula::And(vec![Formula::Bool(true), Formula::BitVec { value: 42, width: 32 }]);
        assert!(has_bv_ops(&f));
    }

    #[test]
    fn test_has_bv_ops_with_bv_arithmetic() {
        let f = Formula::BvAdd(
            Box::new(Formula::Var("x".into(), Sort::BitVec(64))),
            Box::new(Formula::Var("y".into(), Sort::BitVec(64))),
            64,
        );
        assert!(has_bv_ops(&f));
    }

    // --- has_array_ops tests ---

    #[test]
    fn test_has_array_ops_pure_int() {
        let f =
            Formula::Add(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(1)));
        assert!(!has_array_ops(&f));
    }

    #[test]
    fn test_has_array_ops_with_select() {
        let f = Formula::Select(
            Box::new(Formula::Var(
                "arr".into(),
                Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
            )),
            Box::new(Formula::Int(0)),
        );
        assert!(has_array_ops(&f));
    }

    #[test]
    fn test_has_array_ops_with_store() {
        let f = Formula::Store(
            Box::new(Formula::Var(
                "arr".into(),
                Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
            )),
            Box::new(Formula::Int(0)),
            Box::new(Formula::Int(42)),
        );
        assert!(has_array_ops(&f));
    }

    #[test]
    fn test_has_array_ops_with_array_var() {
        let f = Formula::Var("arr".into(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)));
        assert!(has_array_ops(&f));
    }

    #[test]
    fn test_has_array_ops_nested() {
        let f = Formula::And(vec![
            Formula::Bool(true),
            Formula::Eq(
                Box::new(Formula::Select(
                    Box::new(Formula::Var(
                        "arr".into(),
                        Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
                    )),
                    Box::new(Formula::Int(0)),
                )),
                Box::new(Formula::Int(1)),
            ),
        ]);
        assert!(has_array_ops(&f));
    }

    // --- translate_formulas tests ---

    #[test]
    fn test_translate_formulas_empty() {
        assert_eq!(translate_formulas(&[]), Some(vec![]));
    }

    #[test]
    fn test_translate_formulas_single() {
        let formulas = vec![Formula::Bool(true)];
        let result = translate_formulas(&formulas).unwrap();
        assert_eq!(result, vec![PureExpr::Bool(true)]);
    }

    #[test]
    fn test_translate_formulas_multiple() {
        let formulas = vec![
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(Formula::Var("y".into(), Sort::Int)), Box::new(Formula::Int(100))),
        ];
        let result = translate_formulas(&formulas);
        assert!(result.is_some());
        assert_eq!(result.unwrap().len(), 2);
    }

    #[test]
    fn test_translate_formulas_fails_on_untranslatable() {
        let formulas = vec![
            Formula::Bool(true),
            Formula::BvAdd(
                Box::new(Formula::Var("x".into(), Sort::BitVec(32))),
                Box::new(Formula::Var("y".into(), Sort::BitVec(32))),
                32,
            ),
        ];
        // Should return None because second formula is untranslatable
        assert_eq!(translate_formulas(&formulas), None);
    }
}
