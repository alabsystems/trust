// trust-strengthen/weakest_precondition.rs: Classic weakest precondition calculus
//
// Implements Dijkstra's WP transform over our Formula type. Given a postcondition
// and a sequence of statements, computes the weakest precondition that guarantees
// the postcondition holds after execution.
//
// This is a core building block for LLM-free spec inference: given a failing
// postcondition, we can mechanically derive what precondition would make it hold.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, Sort};

/// A simplified statement for WP calculus.
///
/// This is a minimal IR sufficient for WP transforms. MIR statements are
/// lowered to this representation before WP computation.
#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    /// Assignment: `var := expr`.
    Assign {
        /// The variable being assigned.
        var: String,
        /// The sort (type) of the variable.
        sort: Sort,
        /// The expression being assigned.
        expr: Formula,
    },

    /// Assume a condition (e.g., branch condition on a taken path).
    Assume(Formula),

    /// Assert a condition (introduces a proof obligation).
    Assert(Formula),

    /// Conditional: `if cond { then_branch } else { else_branch }`.
    Conditional { condition: Formula, then_branch: Vec<Statement>, else_branch: Vec<Statement> },

    /// Loop with an invariant placeholder.
    ///
    /// For WP calculus, loops are handled by assuming the invariant holds
    /// on entry and exit. The invariant itself must be provided or inferred
    /// separately.
    Loop {
        /// The loop invariant (if known). If None, WP cannot proceed through the loop.
        invariant: Option<Formula>,
        /// The loop body (used for invariant checking, not WP directly).
        body: Vec<Statement>,
    },

    /// Sequential composition of multiple statements.
    Sequence(Vec<Statement>),

    /// No-op (skip).
    Skip,
}

/// Apply the weakest precondition transform for a single statement.
///
/// Given a postcondition Q and a statement S, computes wp(S, Q) such that:
///   { wp(S, Q) } S { Q }
///
/// This is the classic Dijkstra WP calculus:
/// - wp(x := e, Q) = Q[x <- e]  (substitute e for x in Q)
/// - wp(assume P, Q) = P => Q
/// - wp(assert P, Q) = P && Q
/// - wp(S1; S2, Q) = wp(S1, wp(S2, Q))
/// - wp(if C then S1 else S2, Q) = (C => wp(S1, Q)) && (!C => wp(S2, Q))
/// - wp(loop { inv I; body }, Q) = I  (loop uses invariant as WP)
/// - wp(skip, Q) = Q
#[must_use]
pub fn wp_transform(formula: &Formula, statement: &Statement) -> Formula {
    match statement {
        Statement::Assign { var, expr, .. } => substitute(formula, var, expr),

        Statement::Assume(condition) => {
            Formula::Implies(Box::new(condition.clone()), Box::new(formula.clone()))
        }

        Statement::Assert(condition) => Formula::And(vec![condition.clone(), formula.clone()]),

        Statement::Conditional { condition, then_branch, else_branch } => {
            let then_wp = compute_weakest_precondition(formula, then_branch);
            let else_wp = compute_weakest_precondition(formula, else_branch);

            Formula::And(vec![
                Formula::Implies(Box::new(condition.clone()), Box::new(then_wp)),
                Formula::Implies(
                    Box::new(Formula::Not(Box::new(condition.clone()))),
                    Box::new(else_wp),
                ),
            ])
        }

        Statement::Loop { invariant, .. } => {
            // For loops, WP = invariant (if known).
            // The invariant must be strong enough that:
            //   { I } loop body { I }   (preservation)
            //   I && !guard => Q         (on exit, postcondition holds)
            match invariant {
                Some(inv) => inv.clone(),
                // Without an invariant, we cannot compute WP through a loop.
                // Per Dijkstra's predicate transformer semantics, returning the
                // postcondition is UNSOUND — it assumes the loop is a no-op.
                // Return false (the strongest precondition): nothing can be proved
                // without an invariant, so all proof obligations will correctly fail.
                None => Formula::Bool(false),
            }
        }

        Statement::Sequence(stmts) => compute_weakest_precondition(formula, stmts),

        Statement::Skip => formula.clone(),
    }
}

/// Compute the weakest precondition for a sequence of statements.
///
/// Processes statements right-to-left: wp(S1; S2; ... Sn, Q) by starting
/// with Q and folding backward through the statement list.
#[must_use]
pub fn compute_weakest_precondition(postcondition: &Formula, path: &[Statement]) -> Formula {
    path.iter().rev().fold(postcondition.clone(), |acc, stmt| wp_transform(&acc, stmt))
}

/// Substitute all occurrences of variable `var` with expression `expr` in a formula.
///
/// This is the core operation for assignment WP: Q[x <- e].
#[must_use]
pub fn substitute(formula: &Formula, var: &str, expr: &Formula) -> Formula {
    match formula {
        Formula::Bool(_) | Formula::Int(_) | Formula::UInt(_) | Formula::BitVec { .. } => {
            formula.clone()
        }

        Formula::Var(name, _sort) => {
            if name == var {
                expr.clone()
            } else {
                formula.clone()
            }
        }

        Formula::Not(inner) => Formula::Not(Box::new(substitute(inner, var, expr))),

        Formula::And(children) => {
            Formula::And(children.iter().map(|c| substitute(c, var, expr)).collect())
        }

        Formula::Or(children) => {
            Formula::Or(children.iter().map(|c| substitute(c, var, expr)).collect())
        }

        Formula::Implies(lhs, rhs) => Formula::Implies(
            Box::new(substitute(lhs, var, expr)),
            Box::new(substitute(rhs, var, expr)),
        ),

        Formula::Eq(lhs, rhs) => {
            Formula::Eq(Box::new(substitute(lhs, var, expr)), Box::new(substitute(rhs, var, expr)))
        }

        Formula::Lt(lhs, rhs) => {
            Formula::Lt(Box::new(substitute(lhs, var, expr)), Box::new(substitute(rhs, var, expr)))
        }

        Formula::Le(lhs, rhs) => {
            Formula::Le(Box::new(substitute(lhs, var, expr)), Box::new(substitute(rhs, var, expr)))
        }

        Formula::Gt(lhs, rhs) => {
            Formula::Gt(Box::new(substitute(lhs, var, expr)), Box::new(substitute(rhs, var, expr)))
        }

        Formula::Ge(lhs, rhs) => {
            Formula::Ge(Box::new(substitute(lhs, var, expr)), Box::new(substitute(rhs, var, expr)))
        }

        Formula::Add(lhs, rhs) => {
            Formula::Add(Box::new(substitute(lhs, var, expr)), Box::new(substitute(rhs, var, expr)))
        }

        Formula::Sub(lhs, rhs) => {
            Formula::Sub(Box::new(substitute(lhs, var, expr)), Box::new(substitute(rhs, var, expr)))
        }

        Formula::Mul(lhs, rhs) => {
            Formula::Mul(Box::new(substitute(lhs, var, expr)), Box::new(substitute(rhs, var, expr)))
        }

        Formula::Div(lhs, rhs) => {
            Formula::Div(Box::new(substitute(lhs, var, expr)), Box::new(substitute(rhs, var, expr)))
        }

        Formula::Rem(lhs, rhs) => {
            Formula::Rem(Box::new(substitute(lhs, var, expr)), Box::new(substitute(rhs, var, expr)))
        }

        Formula::Neg(inner) => Formula::Neg(Box::new(substitute(inner, var, expr))),

        Formula::Ite(cond, then_f, else_f) => Formula::Ite(
            Box::new(substitute(cond, var, expr)),
            Box::new(substitute(then_f, var, expr)),
            Box::new(substitute(else_f, var, expr)),
        ),

        // Quantifiers: do NOT substitute if the variable is bound
        Formula::Forall(bindings, body) => {
            if bindings.iter().any(|(name, _)| name == var) {
                formula.clone() // var is shadowed by the quantifier
            } else {
                Formula::Forall(bindings.clone(), Box::new(substitute(body, var, expr)))
            }
        }

        Formula::Exists(bindings, body) => {
            if bindings.iter().any(|(name, _)| name == var) {
                formula.clone() // var is shadowed by the quantifier
            } else {
                Formula::Exists(bindings.clone(), Box::new(substitute(body, var, expr)))
            }
        }

        // Array operations
        Formula::Select(array, index) => Formula::Select(
            Box::new(substitute(array, var, expr)),
            Box::new(substitute(index, var, expr)),
        ),

        Formula::Store(array, index, value) => Formula::Store(
            Box::new(substitute(array, var, expr)),
            Box::new(substitute(index, var, expr)),
            Box::new(substitute(value, var, expr)),
        ),

        // Bitvector operations: substitute both operands
        Formula::BvAdd(l, r, w) => Formula::BvAdd(
            Box::new(substitute(l, var, expr)),
            Box::new(substitute(r, var, expr)),
            *w,
        ),
        Formula::BvSub(l, r, w) => Formula::BvSub(
            Box::new(substitute(l, var, expr)),
            Box::new(substitute(r, var, expr)),
            *w,
        ),
        Formula::BvMul(l, r, w) => Formula::BvMul(
            Box::new(substitute(l, var, expr)),
            Box::new(substitute(r, var, expr)),
            *w,
        ),
        Formula::BvUDiv(l, r, w) => Formula::BvUDiv(
            Box::new(substitute(l, var, expr)),
            Box::new(substitute(r, var, expr)),
            *w,
        ),
        Formula::BvSDiv(l, r, w) => Formula::BvSDiv(
            Box::new(substitute(l, var, expr)),
            Box::new(substitute(r, var, expr)),
            *w,
        ),
        Formula::BvURem(l, r, w) => Formula::BvURem(
            Box::new(substitute(l, var, expr)),
            Box::new(substitute(r, var, expr)),
            *w,
        ),
        Formula::BvSRem(l, r, w) => Formula::BvSRem(
            Box::new(substitute(l, var, expr)),
            Box::new(substitute(r, var, expr)),
            *w,
        ),
        Formula::BvAnd(l, r, w) => Formula::BvAnd(
            Box::new(substitute(l, var, expr)),
            Box::new(substitute(r, var, expr)),
            *w,
        ),
        Formula::BvOr(l, r, w) => Formula::BvOr(
            Box::new(substitute(l, var, expr)),
            Box::new(substitute(r, var, expr)),
            *w,
        ),
        Formula::BvXor(l, r, w) => Formula::BvXor(
            Box::new(substitute(l, var, expr)),
            Box::new(substitute(r, var, expr)),
            *w,
        ),
        Formula::BvNot(inner, w) => Formula::BvNot(Box::new(substitute(inner, var, expr)), *w),
        Formula::BvShl(l, r, w) => Formula::BvShl(
            Box::new(substitute(l, var, expr)),
            Box::new(substitute(r, var, expr)),
            *w,
        ),
        Formula::BvLShr(l, r, w) => Formula::BvLShr(
            Box::new(substitute(l, var, expr)),
            Box::new(substitute(r, var, expr)),
            *w,
        ),
        Formula::BvAShr(l, r, w) => Formula::BvAShr(
            Box::new(substitute(l, var, expr)),
            Box::new(substitute(r, var, expr)),
            *w,
        ),

        // Bitvector comparisons
        Formula::BvULt(l, r, w) => Formula::BvULt(
            Box::new(substitute(l, var, expr)),
            Box::new(substitute(r, var, expr)),
            *w,
        ),
        Formula::BvULe(l, r, w) => Formula::BvULe(
            Box::new(substitute(l, var, expr)),
            Box::new(substitute(r, var, expr)),
            *w,
        ),
        Formula::BvSLt(l, r, w) => Formula::BvSLt(
            Box::new(substitute(l, var, expr)),
            Box::new(substitute(r, var, expr)),
            *w,
        ),
        Formula::BvSLe(l, r, w) => Formula::BvSLe(
            Box::new(substitute(l, var, expr)),
            Box::new(substitute(r, var, expr)),
            *w,
        ),

        // Bitvector conversions
        Formula::BvToInt(inner, w, signed) => {
            Formula::BvToInt(Box::new(substitute(inner, var, expr)), *w, *signed)
        }
        Formula::IntToBv(inner, w) => Formula::IntToBv(Box::new(substitute(inner, var, expr)), *w),
        Formula::BvExtract { inner, high, low } => Formula::BvExtract {
            inner: Box::new(substitute(inner, var, expr)),
            high: *high,
            low: *low,
        },
        Formula::BvConcat(l, r) => Formula::BvConcat(
            Box::new(substitute(l, var, expr)),
            Box::new(substitute(r, var, expr)),
        ),
        Formula::BvZeroExt(inner, bits) => {
            Formula::BvZeroExt(Box::new(substitute(inner, var, expr)), *bits)
        }
        Formula::BvSignExt(inner, bits) => {
            Formula::BvSignExt(Box::new(substitute(inner, var, expr)), *bits)
        }
        _ => formula.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // --- Helper constructors ---

    fn var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    fn bv_var(name: &str, width: u32) -> Formula {
        Formula::Var(name.into(), Sort::BitVec(width))
    }

    fn int(n: i128) -> Formula {
        Formula::Int(n)
    }

    fn assign(name: &str, expr: Formula) -> Statement {
        Statement::Assign { var: name.into(), sort: Sort::Int, expr }
    }

    // --- Substitution tests ---

    #[test]
    fn test_substitute_var_match() {
        // Q = x > 0, substituting x <- 5
        let q = Formula::Gt(Box::new(var("x")), Box::new(int(0)));
        let result = substitute(&q, "x", &int(5));
        assert_eq!(result, Formula::Gt(Box::new(int(5)), Box::new(int(0))));
    }

    #[test]
    fn test_substitute_var_no_match() {
        // Q = y > 0, substituting x <- 5 (no match)
        let q = Formula::Gt(Box::new(var("y")), Box::new(int(0)));
        let result = substitute(&q, "x", &int(5));
        assert_eq!(result, q);
    }

    #[test]
    fn test_substitute_literal_unchanged() {
        let q = Formula::Bool(true);
        assert_eq!(substitute(&q, "x", &int(5)), Formula::Bool(true));

        let q2 = Formula::Int(42);
        assert_eq!(substitute(&q2, "x", &int(5)), Formula::Int(42));
    }

    #[test]
    fn test_substitute_in_and() {
        // Q = x > 0 && x < 10, substituting x <- y + 1
        let q = Formula::And(vec![
            Formula::Gt(Box::new(var("x")), Box::new(int(0))),
            Formula::Lt(Box::new(var("x")), Box::new(int(10))),
        ]);
        let replacement = Formula::Add(Box::new(var("y")), Box::new(int(1)));
        let result = substitute(&q, "x", &replacement);

        match result {
            Formula::And(children) => {
                assert_eq!(children.len(), 2);
                // First child: (y + 1) > 0
                assert_eq!(
                    children[0],
                    Formula::Gt(Box::new(replacement.clone()), Box::new(int(0)))
                );
                // Second child: (y + 1) < 10
                assert_eq!(children[1], Formula::Lt(Box::new(replacement), Box::new(int(10))));
            }
            other => panic!("expected And, got {other:?}"),
        }
    }

    #[test]
    fn test_substitute_in_not() {
        let q = Formula::Not(Box::new(var("x")));
        let result = substitute(&q, "x", &Formula::Bool(false));
        assert_eq!(result, Formula::Not(Box::new(Formula::Bool(false))));
    }

    #[test]
    fn test_substitute_in_implies() {
        let q = Formula::Implies(Box::new(var("x")), Box::new(var("y")));
        let result = substitute(&q, "x", &Formula::Bool(true));
        assert_eq!(result, Formula::Implies(Box::new(Formula::Bool(true)), Box::new(var("y"))));
    }

    #[test]
    fn test_substitute_respects_quantifier_binding() {
        // Q = forall x. x > 0
        // Substituting x <- 5 should NOT affect the bound variable
        let q = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(var("x")), Box::new(int(0)))),
        );
        let result = substitute(&q, "x", &int(5));
        assert_eq!(result, q, "bound variable should not be substituted");
    }

    #[test]
    fn test_substitute_free_var_under_quantifier() {
        // Q = forall y. x > y
        // Substituting x <- 5 should affect x but not y
        let q = Formula::Forall(
            vec![("y".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(var("x")), Box::new(var("y")))),
        );
        let result = substitute(&q, "x", &int(5));
        assert_eq!(
            result,
            Formula::Forall(
                vec![("y".into(), Sort::Int)],
                Box::new(Formula::Gt(Box::new(int(5)), Box::new(var("y")))),
            )
        );
    }

    #[test]
    fn test_substitute_in_arithmetic() {
        // Q = x + y, substituting x <- a * b
        let q = Formula::Add(Box::new(var("x")), Box::new(var("y")));
        let replacement = Formula::Mul(Box::new(var("a")), Box::new(var("b")));
        let result = substitute(&q, "x", &replacement);
        assert_eq!(result, Formula::Add(Box::new(replacement), Box::new(var("y"))));
    }

    #[test]
    fn test_substitute_in_ite() {
        let q = Formula::Ite(Box::new(var("c")), Box::new(var("x")), Box::new(var("y")));
        let result = substitute(&q, "x", &int(42));
        assert_eq!(
            result,
            Formula::Ite(Box::new(var("c")), Box::new(int(42)), Box::new(var("y")),)
        );
    }

    #[test]
    fn test_substitute_in_select_store() {
        // select(arr, x) -- substituting x <- 0
        let q = Formula::Select(Box::new(var("arr")), Box::new(var("x")));
        let result = substitute(&q, "x", &int(0));
        assert_eq!(result, Formula::Select(Box::new(var("arr")), Box::new(int(0))));

        // store(arr, x, v) -- substituting x <- 0
        let q2 = Formula::Store(Box::new(var("arr")), Box::new(var("x")), Box::new(var("v")));
        let result2 = substitute(&q2, "x", &int(0));
        assert_eq!(
            result2,
            Formula::Store(Box::new(var("arr")), Box::new(int(0)), Box::new(var("v")),)
        );
    }

    #[test]
    fn test_substitute_in_bitvector_ops() {
        let q = Formula::BvAdd(Box::new(bv_var("x", 32)), Box::new(bv_var("y", 32)), 32);
        let result = substitute(&q, "x", &Formula::BitVec { value: 5, width: 32 });
        assert_eq!(
            result,
            Formula::BvAdd(
                Box::new(Formula::BitVec { value: 5, width: 32 }),
                Box::new(bv_var("y", 32)),
                32,
            )
        );
    }

    // --- WP transform tests ---

    #[test]
    fn test_wp_skip() {
        let q = Formula::Gt(Box::new(var("x")), Box::new(int(0)));
        let result = wp_transform(&q, &Statement::Skip);
        assert_eq!(result, q, "wp(skip, Q) = Q");
    }

    #[test]
    fn test_wp_assignment_simple() {
        // wp(x := 5, x > 0) = 5 > 0
        let q = Formula::Gt(Box::new(var("x")), Box::new(int(0)));
        let s = assign("x", int(5));
        let result = wp_transform(&q, &s);
        assert_eq!(result, Formula::Gt(Box::new(int(5)), Box::new(int(0))));
    }

    #[test]
    fn test_wp_assignment_expression() {
        // wp(x := y + 1, x > 0) = (y + 1) > 0
        let q = Formula::Gt(Box::new(var("x")), Box::new(int(0)));
        let s = assign("x", Formula::Add(Box::new(var("y")), Box::new(int(1))));
        let result = wp_transform(&q, &s);
        assert_eq!(
            result,
            Formula::Gt(
                Box::new(Formula::Add(Box::new(var("y")), Box::new(int(1)))),
                Box::new(int(0))
            )
        );
    }

    #[test]
    fn test_wp_assume() {
        // wp(assume P, Q) = P => Q
        let p = Formula::Gt(Box::new(var("x")), Box::new(int(0)));
        let q = Formula::Lt(Box::new(var("x")), Box::new(int(100)));
        let result = wp_transform(&q, &Statement::Assume(p.clone()));
        assert_eq!(result, Formula::Implies(Box::new(p), Box::new(q)));
    }

    #[test]
    fn test_wp_assert() {
        // wp(assert P, Q) = P && Q
        let p = Formula::Gt(Box::new(var("x")), Box::new(int(0)));
        let q = Formula::Lt(Box::new(var("x")), Box::new(int(100)));
        let result = wp_transform(&q, &Statement::Assert(p.clone()));
        assert_eq!(result, Formula::And(vec![p, q]));
    }

    #[test]
    fn test_wp_conditional() {
        // wp(if c then x:=1 else x:=2, x > 0)
        // = (c => 1 > 0) && (!c => 2 > 0)
        let q = Formula::Gt(Box::new(var("x")), Box::new(int(0)));
        let s = Statement::Conditional {
            condition: var("c"),
            then_branch: vec![assign("x", int(1))],
            else_branch: vec![assign("x", int(2))],
        };
        let result = wp_transform(&q, &s);

        match result {
            Formula::And(children) => {
                assert_eq!(children.len(), 2);
                // c => (1 > 0)
                assert_eq!(
                    children[0],
                    Formula::Implies(
                        Box::new(var("c")),
                        Box::new(Formula::Gt(Box::new(int(1)), Box::new(int(0)))),
                    )
                );
                // !c => (2 > 0)
                assert_eq!(
                    children[1],
                    Formula::Implies(
                        Box::new(Formula::Not(Box::new(var("c")))),
                        Box::new(Formula::Gt(Box::new(int(2)), Box::new(int(0)))),
                    )
                );
            }
            other => panic!("expected And, got {other:?}"),
        }
    }

    #[test]
    fn test_wp_loop_with_invariant() {
        // wp(loop { inv I; ... }, Q) = I
        let invariant = Formula::And(vec![
            Formula::Ge(Box::new(var("i")), Box::new(int(0))),
            Formula::Le(Box::new(var("i")), Box::new(var("n"))),
        ]);
        let q = Formula::Eq(Box::new(var("i")), Box::new(var("n")));
        let s = Statement::Loop {
            invariant: Some(invariant.clone()),
            body: vec![assign("i", Formula::Add(Box::new(var("i")), Box::new(int(1))))],
        };

        let result = wp_transform(&q, &s);
        assert_eq!(result, invariant, "wp of loop should be the invariant");
    }

    #[test]
    fn test_wp_loop_without_invariant_returns_false() {
        // Without an invariant, WP must be false (nothing provable).
        // Returning the postcondition would be unsound — it assumes the loop
        // is a no-op, which can produce false proofs.
        let q = Formula::Eq(Box::new(var("i")), Box::new(var("n")));
        let s = Statement::Loop { invariant: None, body: vec![] };
        let result = wp_transform(&q, &s);
        assert_eq!(
            result,
            Formula::Bool(false),
            "without invariant, WP must be false (strongest precondition)"
        );
    }

    #[test]
    fn test_wp_loop_without_invariant_nonempty_body() {
        // Even with a non-trivial body, missing invariant => false
        let q = Formula::Gt(Box::new(var("x")), Box::new(int(0)));
        let s = Statement::Loop {
            invariant: None,
            body: vec![assign("x", Formula::Add(Box::new(var("x")), Box::new(int(1))))],
        };
        let result = wp_transform(&q, &s);
        assert_eq!(
            result,
            Formula::Bool(false),
            "loop without invariant must not pass through postcondition"
        );
    }

    #[test]
    fn test_wp_loop_without_invariant_in_sequence() {
        // A loop without invariant in a sequence should make the entire WP false,
        // preventing false proofs for any program containing the loop.
        let q = Formula::Gt(Box::new(var("result")), Box::new(int(0)));
        let path = vec![
            assign("x", int(0)),
            Statement::Loop {
                invariant: None,
                body: vec![assign("x", Formula::Add(Box::new(var("x")), Box::new(int(1))))],
            },
            assign("result", var("x")),
        ];
        let result = compute_weakest_precondition(&q, &path);
        // The loop WP is false; wp(x:=0, false) = false (substitution in false = false)
        assert_eq!(
            result,
            Formula::Bool(false),
            "sequence with uninvariant loop must produce false WP"
        );
    }

    // --- Sequence tests ---

    #[test]
    fn test_wp_sequence_empty() {
        let q = Formula::Gt(Box::new(var("x")), Box::new(int(0)));
        let result = compute_weakest_precondition(&q, &[]);
        assert_eq!(result, q, "wp of empty sequence is the postcondition");
    }

    #[test]
    fn test_wp_sequence_single() {
        let q = Formula::Gt(Box::new(var("x")), Box::new(int(0)));
        let result = compute_weakest_precondition(&q, &[assign("x", int(5))]);
        assert_eq!(result, Formula::Gt(Box::new(int(5)), Box::new(int(0))));
    }

    #[test]
    fn test_wp_sequence_two_assignments() {
        // Postcondition: x > 0
        // Path: y := 3; x := y + 1
        // wp(y:=3; x:=y+1, x > 0) = wp(y:=3, (y+1) > 0) = (3+1) > 0
        let q = Formula::Gt(Box::new(var("x")), Box::new(int(0)));
        let path = vec![
            assign("y", int(3)),
            assign("x", Formula::Add(Box::new(var("y")), Box::new(int(1)))),
        ];
        let result = compute_weakest_precondition(&q, &path);
        assert_eq!(
            result,
            Formula::Gt(
                Box::new(Formula::Add(Box::new(int(3)), Box::new(int(1)))),
                Box::new(int(0)),
            )
        );
    }

    #[test]
    fn test_wp_assume_then_assert() {
        // Path: assume x > 0; assert x >= 1
        // wp = (x > 0) => ((x >= 1) && Q)
        let q = Formula::Bool(true);
        let path = vec![
            Statement::Assume(Formula::Gt(Box::new(var("x")), Box::new(int(0)))),
            Statement::Assert(Formula::Ge(Box::new(var("x")), Box::new(int(1)))),
        ];
        let result = compute_weakest_precondition(&q, &path);

        // wp(assert x>=1, true) = (x>=1) && true
        // wp(assume x>0, (x>=1) && true) = (x>0) => ((x>=1) && true)
        assert_eq!(
            result,
            Formula::Implies(
                Box::new(Formula::Gt(Box::new(var("x")), Box::new(int(0)))),
                Box::new(Formula::And(vec![
                    Formula::Ge(Box::new(var("x")), Box::new(int(1))),
                    Formula::Bool(true),
                ])),
            )
        );
    }

    #[test]
    fn test_wp_nested_sequence() {
        let q = Formula::Gt(Box::new(var("x")), Box::new(int(0)));
        let inner = Statement::Sequence(vec![assign("x", int(5))]);
        let result = wp_transform(&q, &inner);
        assert_eq!(result, Formula::Gt(Box::new(int(5)), Box::new(int(0))));
    }

    // --- Concrete example: midpoint ---

    #[test]
    fn test_wp_midpoint_overflow_check() {
        // Modeling: fn midpoint(a: u64, b: u64) -> u64 { (a + b) / 2 }
        // Postcondition: result >= 0 (trivially true for u64, but demonstrates WP)
        // Path: result := (a + b) / 2
        // wp = ((a + b) / 2) >= 0
        let q = Formula::Ge(Box::new(var("result")), Box::new(int(0)));
        let path = vec![assign(
            "result",
            Formula::Div(
                Box::new(Formula::Add(Box::new(var("a")), Box::new(var("b")))),
                Box::new(int(2)),
            ),
        )];
        let result = compute_weakest_precondition(&q, &path);
        assert_eq!(
            result,
            Formula::Ge(
                Box::new(Formula::Div(
                    Box::new(Formula::Add(Box::new(var("a")), Box::new(var("b")))),
                    Box::new(int(2)),
                )),
                Box::new(int(0)),
            )
        );
    }

    #[test]
    fn test_wp_div_safety() {
        // Modeling: fn safe_div(x: i64, y: i64) -> i64 { x / y }
        // Postcondition: true (we just want the WP for y != 0 assertion)
        // Path: assert y != 0; result := x / y
        let q = Formula::Bool(true);
        let path = vec![
            Statement::Assert(Formula::Not(Box::new(Formula::Eq(
                Box::new(var("y")),
                Box::new(int(0)),
            )))),
            assign("result", Formula::Div(Box::new(var("x")), Box::new(var("y")))),
        ];
        let result = compute_weakest_precondition(&q, &path);

        // wp(result := x/y, true) = true
        // wp(assert y!=0, true) = (y!=0) && true
        assert_eq!(
            result,
            Formula::And(vec![
                Formula::Not(Box::new(Formula::Eq(Box::new(var("y")), Box::new(int(0)),))),
                Formula::Bool(true),
            ])
        );
    }

    #[test]
    fn test_wp_swap_pattern() {
        // Modeling: swap via temp
        // Path: tmp := x; x := y; y := tmp
        // Postcondition: x == old_y && y == old_x
        // We use fresh variables old_y, old_x to represent the original values
        let q = Formula::And(vec![
            Formula::Eq(Box::new(var("x")), Box::new(var("old_y"))),
            Formula::Eq(Box::new(var("y")), Box::new(var("old_x"))),
        ]);
        let path = vec![assign("tmp", var("x")), assign("x", var("y")), assign("y", var("tmp"))];

        let result = compute_weakest_precondition(&q, &path);

        // Working backward:
        // wp(y := tmp, Q) = Q[y <- tmp]
        //   = (x == old_y) && (tmp == old_x)
        // wp(x := y, ...) = [x <- y]
        //   = (y == old_y) && (tmp == old_x)
        // wp(tmp := x, ...) = [tmp <- x]
        //   = (y == old_y) && (x == old_x)
        assert_eq!(
            result,
            Formula::And(vec![
                Formula::Eq(Box::new(var("y")), Box::new(var("old_y"))),
                Formula::Eq(Box::new(var("x")), Box::new(var("old_x"))),
            ])
        );
    }
}
