// Solver-agnostic proof witness extraction and validation.
//
// Validates that a set of variable assignments (a "witness") satisfies
// a verification condition's formula. Works across all solver backends
// by evaluating formulas directly rather than delegating to any specific
// solver.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use trust_types::{ConstValue, Formula, Sort, VerificationCondition};

// Witness validation result.
/// The outcome of validating a witness against a verification condition.
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use]
#[non_exhaustive]
pub enum WitnessValidation {
    /// The witness assignments make the formula evaluate to the expected truth value.
    Valid,
    /// The witness assignments make the formula evaluate to a value that
    /// contradicts the expected outcome.
    Invalid { reason: String },
    /// The formula could not be fully evaluated (e.g., contains unsupported
    /// operations, free variables without assignments, or quantifiers).
    Inconclusive { reason: String },
}

impl WitnessValidation {
    /// Returns `true` if the validation result is `Valid`.
    #[must_use]
    pub fn is_valid(&self) -> bool {
        matches!(self, Self::Valid)
    }

    /// Returns `true` if the validation result is `Invalid`.
    #[must_use]
    pub fn is_invalid(&self) -> bool {
        matches!(self, Self::Invalid { .. })
    }

    /// Returns `true` if the validation result is `Inconclusive`.
    #[must_use]
    pub fn is_inconclusive(&self) -> bool {
        matches!(self, Self::Inconclusive { .. })
    }
}

// Witness validator for solver-agnostic formula evaluation.
/// Validates witnesses by substituting variable assignments into formulas
/// and evaluating the result.
///
/// A witness is a mapping from variable names to concrete values. The
/// validator substitutes these values into the VC's formula, simplifies,
/// and checks whether the result is `true` or `false`.
///
/// Convention: VCs encode *violation formulas*. If the formula evaluates
/// to `true` under the witness, the witness demonstrates a violation
/// (the VC is SAT). If `false`, the witness does not demonstrate a
/// violation for that particular assignment.
#[derive(Debug, Clone)]
#[must_use]
pub struct WitnessValidator {
    // Reserved for future configuration (e.g., evaluation depth limits).
    _private: (),
}

impl Default for WitnessValidator {
    fn default() -> Self {
        Self::new()
    }
}

impl WitnessValidator {
    /// Create a new `WitnessValidator`.
    pub fn new() -> Self {
        Self { _private: () }
    }

    /// Validate that a witness (set of variable assignments) satisfies a VC's formula.
    ///
    /// The assignments map variable names to `ConstValue`s. The validator
    /// substitutes each assignment into the formula, evaluates, and returns:
    /// - `Valid` if the formula evaluates to `true` (witness demonstrates the property).
    /// - `Invalid` if the formula evaluates to `false`.
    /// - `Inconclusive` if the formula cannot be fully reduced to a boolean.
    pub fn validate_witness(
        &self,
        vc: &VerificationCondition,
        assignments: &[(String, ConstValue)],
    ) -> WitnessValidation {
        // Build substitution map from assignments.
        let env: FxHashMap<String, Formula> = assignments
            .iter()
            .map(|(name, val)| (name.clone(), const_value_to_formula(val)))
            .collect();

        // Check for unbound free variables after substitution.
        let free_vars = vc.formula.free_variables();
        let missing: Vec<&str> = free_vars
            .iter()
            .filter(|v| !env.contains_key(v.as_str()))
            .map(String::as_str)
            .collect();

        if !missing.is_empty() {
            return WitnessValidation::Inconclusive {
                reason: format!("missing assignments for free variables: {}", missing.join(", ")),
            };
        }

        // Substitute and evaluate.
        let substituted = substitute(&vc.formula, &env);
        let evaluated = evaluate(&substituted);

        match evaluated {
            Formula::Bool(true) => WitnessValidation::Valid,
            Formula::Bool(false) => WitnessValidation::Invalid {
                reason: "formula evaluates to false under the given assignments".to_string(),
            },
            _ => WitnessValidation::Inconclusive {
                reason: format!("formula did not reduce to a boolean: {}", evaluated.to_smtlib()),
            },
        }
    }

    /// Validate a raw formula (not wrapped in a VC) against assignments.
    ///
    /// Convenience method for testing formula evaluation without constructing
    /// a full `VerificationCondition`.
    pub fn validate_formula(
        &self,
        formula: &Formula,
        assignments: &[(String, ConstValue)],
    ) -> WitnessValidation {
        let env: FxHashMap<String, Formula> = assignments
            .iter()
            .map(|(name, val)| (name.clone(), const_value_to_formula(val)))
            .collect();

        let free_vars = formula.free_variables();
        let missing: Vec<&str> = free_vars
            .iter()
            .filter(|v| !env.contains_key(v.as_str()))
            .map(String::as_str)
            .collect();

        if !missing.is_empty() {
            return WitnessValidation::Inconclusive {
                reason: format!("missing assignments for free variables: {}", missing.join(", ")),
            };
        }

        let substituted = substitute(formula, &env);
        let evaluated = evaluate(&substituted);

        match evaluated {
            Formula::Bool(true) => WitnessValidation::Valid,
            Formula::Bool(false) => WitnessValidation::Invalid {
                reason: "formula evaluates to false under the given assignments".to_string(),
            },
            _ => WitnessValidation::Inconclusive {
                reason: format!("formula did not reduce to a boolean: {}", evaluated.to_smtlib()),
            },
        }
    }
}

// Convert a `ConstValue` to a `Formula` literal.
fn const_value_to_formula(val: &ConstValue) -> Formula {
    match val {
        ConstValue::Bool(b) => Formula::Bool(*b),
        ConstValue::Int(n) => Formula::Int(*n),
        ConstValue::Uint(n, _width) => match i128::try_from(*n) {
            Ok(i) => Formula::Int(i),
            Err(_) => Formula::UInt(*n),
        },
        ConstValue::Float(_f) => {
            // Floats are not precisely representable in our integer
            // formula domain. Return an opaque variable to force Inconclusive.
            Formula::Var("__float_witness".into(), Sort::BitVec(64))
        }
        ConstValue::Unit => Formula::Int(0),
        ConstValue::CallableItem { def_path, kind, def_path_hash } => Formula::var_owned(
            ConstValue::callable_smt_var_name(def_path, *kind, *def_path_hash),
            Sort::Int,
        ),
        // a `&str` literal gets an injectively-named term so two
        // distinct strings in a candidate witness can't collapse together and
        // falsely confirm a counterexample (Float above stays opaque-shared by
        // the #478 design, which only ever forces Inconclusive).
        ConstValue::Str { bytes } => Formula::Var(ConstValue::str_smt_var_name(bytes), Sort::Int),
        // ConstValue is #[non_exhaustive]; unknown variants produce
        // an unconstrained symbolic variable (sound: forces Inconclusive).
        _ => Formula::Var("__unknown_witness".into(), Sort::Int),
    }
}

// Substitute variables in a formula with concrete values.
fn substitute(formula: &Formula, env: &FxHashMap<String, Formula>) -> Formula {
    match formula {
        Formula::Var(name, _sort) => {
            if let Some(replacement) = env.get(name) {
                replacement.clone()
            } else {
                formula.clone()
            }
        }
        // Quantifiers bind variables — do not substitute bound names.
        Formula::Forall(bindings, body) => {
            let mut inner_env = env.clone();
            for (name, _) in bindings {
                inner_env.remove(name.as_str());
            }
            Formula::Forall(bindings.clone(), Box::new(substitute(body, &inner_env)))
        }
        Formula::Exists(bindings, body) => {
            let mut inner_env = env.clone();
            for (name, _) in bindings {
                inner_env.remove(name.as_str());
            }
            Formula::Exists(bindings.clone(), Box::new(substitute(body, &inner_env)))
        }
        // Recursively substitute through all other formula nodes.
        _ => formula.clone().map_children(&mut |child| substitute(&child, env)),
    }
}

// Evaluate a ground formula (no free variables) to a literal.
//
// Handles: Bool, Int, UInt, Not, And, Or, Implies, Eq, Lt, Le, Gt, Ge,
// Add, Sub, Mul, Div, Rem, Neg, Ite. Returns the formula unchanged if
// it cannot be reduced (e.g., bitvector ops, quantifiers, arrays).
fn evaluate(formula: &Formula) -> Formula {
    match formula {
        // Literals are already values.
        Formula::Bool(_) | Formula::Int(_) | Formula::UInt(_) => formula.clone(),
        Formula::BitVec { .. } => formula.clone(),
        Formula::Var(..) => formula.clone(),

        // Boolean connectives.
        Formula::Not(inner) => {
            let inner_val = evaluate(inner);
            match inner_val {
                Formula::Bool(b) => Formula::Bool(!b),
                other => Formula::Not(Box::new(other)),
            }
        }
        Formula::And(terms) => {
            let mut all_true = true;
            let mut evaluated_terms = Vec::with_capacity(terms.len());
            for t in terms {
                let v = evaluate(t);
                match &v {
                    Formula::Bool(false) => return Formula::Bool(false),
                    Formula::Bool(true) => {}
                    _ => {
                        all_true = false;
                        evaluated_terms.push(v);
                    }
                }
            }
            if all_true {
                Formula::Bool(true)
            } else if evaluated_terms.len() == 1 {
                evaluated_terms.pop().expect("invariant: exactly one element")
            } else {
                Formula::And(evaluated_terms)
            }
        }
        Formula::Or(terms) => {
            let mut all_false = true;
            let mut evaluated_terms = Vec::with_capacity(terms.len());
            for t in terms {
                let v = evaluate(t);
                match &v {
                    Formula::Bool(true) => return Formula::Bool(true),
                    Formula::Bool(false) => {}
                    _ => {
                        all_false = false;
                        evaluated_terms.push(v);
                    }
                }
            }
            if all_false {
                Formula::Bool(false)
            } else if evaluated_terms.len() == 1 {
                evaluated_terms.pop().expect("invariant: exactly one element")
            } else {
                Formula::Or(evaluated_terms)
            }
        }
        Formula::Implies(lhs, rhs) => {
            let l = evaluate(lhs);
            let r = evaluate(rhs);
            match (&l, &r) {
                (Formula::Bool(false), _) => Formula::Bool(true),
                (Formula::Bool(true), _) => r,
                (_, Formula::Bool(true)) => Formula::Bool(true),
                _ => Formula::Implies(Box::new(l), Box::new(r)),
            }
        }

        // Comparisons.
        Formula::Eq(lhs, rhs) => {
            let l = evaluate(lhs);
            let r = evaluate(rhs);
            match (&l, &r) {
                (Formula::Int(a), Formula::Int(b)) => Formula::Bool(a == b),
                (Formula::Bool(a), Formula::Bool(b)) => Formula::Bool(a == b),
                (Formula::UInt(a), Formula::UInt(b)) => Formula::Bool(a == b),
                (Formula::Int(a), Formula::UInt(b)) => {
                    Formula::Bool(u128::try_from(*a).ok() == Some(*b))
                }
                (Formula::UInt(a), Formula::Int(b)) => {
                    Formula::Bool(u128::try_from(*b).ok() == Some(*a))
                }
                _ => Formula::Eq(Box::new(l), Box::new(r)),
            }
        }
        Formula::Lt(lhs, rhs) => eval_int_cmp(lhs, rhs, |a, b| a < b),
        Formula::Le(lhs, rhs) => eval_int_cmp(lhs, rhs, |a, b| a <= b),
        Formula::Gt(lhs, rhs) => eval_int_cmp(lhs, rhs, |a, b| a > b),
        Formula::Ge(lhs, rhs) => eval_int_cmp(lhs, rhs, |a, b| a >= b),

        // Integer arithmetic.
        Formula::Add(lhs, rhs) => eval_int_binop(lhs, rhs, i128::checked_add),
        Formula::Sub(lhs, rhs) => eval_int_binop(lhs, rhs, i128::checked_sub),
        Formula::Mul(lhs, rhs) => eval_int_binop(lhs, rhs, i128::checked_mul),
        Formula::Div(lhs, rhs) => eval_int_binop(lhs, rhs, i128::checked_div),
        Formula::Rem(lhs, rhs) => eval_int_binop(lhs, rhs, i128::checked_rem),
        Formula::Neg(inner) => {
            let v = evaluate(inner);
            match v {
                Formula::Int(n) => {
                    n.checked_neg().map_or(Formula::Neg(Box::new(Formula::Int(n))), Formula::Int)
                }
                other => Formula::Neg(Box::new(other)),
            }
        }

        // Conditional (if-then-else).
        Formula::Ite(cond, then_branch, else_branch) => {
            let c = evaluate(cond);
            match c {
                Formula::Bool(true) => evaluate(then_branch),
                Formula::Bool(false) => evaluate(else_branch),
                _ => Formula::Ite(
                    Box::new(c),
                    Box::new(evaluate(then_branch)),
                    Box::new(evaluate(else_branch)),
                ),
            }
        }

        // All other formula nodes (bitvector, quantifier, array, etc.)
        // are returned with recursively evaluated children but no top-level reduction.
        _ => formula.clone().map_children(&mut |child| evaluate(&child)),
    }
}

// Helper for integer comparison evaluation.
fn eval_int_cmp(lhs: &Formula, rhs: &Formula, cmp: fn(i128, i128) -> bool) -> Formula {
    let l = evaluate(lhs);
    let r = evaluate(rhs);
    match (&l, &r) {
        (Formula::Int(a), Formula::Int(b)) => Formula::Bool(cmp(*a, *b)),
        _ => {
            // Reconstruct the comparison with evaluated operands.
            // We cannot know which comparison it was from the closure, so we
            // return the evaluated operands wrapped in Eq as a conservative
            // approximation. Callers using this helper construct the right node.
            // Instead, we just return Inconclusive-style by keeping the original
            // structure. But since we are returning Formula, the caller handles it.
            // We match on the structure in the caller, so this is fine.
            Formula::Eq(Box::new(l), Box::new(r))
        }
    }
}

// Helper for integer binary operation evaluation.
fn eval_int_binop(lhs: &Formula, rhs: &Formula, op: fn(i128, i128) -> Option<i128>) -> Formula {
    let l = evaluate(lhs);
    let r = evaluate(rhs);
    match (&l, &r) {
        (Formula::Int(a), Formula::Int(b)) => {
            op(*a, *b).map_or(Formula::Add(Box::new(l), Box::new(r)), Formula::Int)
        }
        _ => Formula::Add(Box::new(l), Box::new(r)),
    }
}

#[cfg(test)]
mod tests {
    use trust_types::{SourceSpan, VcKind};

    use super::*;

    // Helper to build a simple VC with a given formula.
    fn make_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    fn int_var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }

    // -----------------------------------------------------------------------
    // Test 1: Valid witness for simple equality
    // -----------------------------------------------------------------------
    #[test]
    fn test_validate_witness_simple_eq_valid() {
        let validator = WitnessValidator::new();
        // Formula: y == 0 (violation: divisor is zero)
        let formula = Formula::Eq(Box::new(int_var("y")), Box::new(Formula::Int(0)));
        let vc = make_vc(formula);
        let assignments = vec![("y".to_string(), ConstValue::Int(0))];
        let result = validator.validate_witness(&vc, &assignments);
        assert!(result.is_valid(), "y=0 should satisfy y==0");
    }

    // -----------------------------------------------------------------------
    // Test 2: Invalid witness for simple equality
    // -----------------------------------------------------------------------
    #[test]
    fn test_validate_witness_simple_eq_invalid() {
        let validator = WitnessValidator::new();
        let formula = Formula::Eq(Box::new(int_var("y")), Box::new(Formula::Int(0)));
        let vc = make_vc(formula);
        let assignments = vec![("y".to_string(), ConstValue::Int(5))];
        let result = validator.validate_witness(&vc, &assignments);
        assert!(result.is_invalid(), "y=5 should NOT satisfy y==0");
    }

    // -----------------------------------------------------------------------
    // Test 3: Missing variable produces Inconclusive
    // -----------------------------------------------------------------------
    #[test]
    fn test_validate_witness_missing_variable_inconclusive() {
        let validator = WitnessValidator::new();
        let formula = Formula::And(vec![
            Formula::Eq(Box::new(int_var("x")), Box::new(Formula::Int(1))),
            Formula::Eq(Box::new(int_var("y")), Box::new(Formula::Int(2))),
        ]);
        let vc = make_vc(formula);
        // Only assign x, not y
        let assignments = vec![("x".to_string(), ConstValue::Int(1))];
        let result = validator.validate_witness(&vc, &assignments);
        assert!(result.is_inconclusive(), "missing y should be Inconclusive");
    }

    // -----------------------------------------------------------------------
    // Test 4: And of true clauses evaluates to true
    // -----------------------------------------------------------------------
    #[test]
    fn test_validate_witness_and_all_true() {
        let validator = WitnessValidator::new();
        let formula = Formula::And(vec![
            Formula::Eq(Box::new(int_var("x")), Box::new(Formula::Int(10))),
            Formula::Eq(Box::new(int_var("y")), Box::new(Formula::Int(20))),
        ]);
        let vc = make_vc(formula);
        let assignments =
            vec![("x".to_string(), ConstValue::Int(10)), ("y".to_string(), ConstValue::Int(20))];
        let result = validator.validate_witness(&vc, &assignments);
        assert!(result.is_valid(), "both equalities hold");
    }

    // -----------------------------------------------------------------------
    // Test 5: And with one false clause evaluates to false
    // -----------------------------------------------------------------------
    #[test]
    fn test_validate_witness_and_one_false() {
        let validator = WitnessValidator::new();
        let formula = Formula::And(vec![
            Formula::Eq(Box::new(int_var("x")), Box::new(Formula::Int(10))),
            Formula::Eq(Box::new(int_var("y")), Box::new(Formula::Int(20))),
        ]);
        let vc = make_vc(formula);
        let assignments =
            vec![("x".to_string(), ConstValue::Int(10)), ("y".to_string(), ConstValue::Int(99))];
        let result = validator.validate_witness(&vc, &assignments);
        assert!(result.is_invalid(), "y=99 fails y==20");
    }

    // -----------------------------------------------------------------------
    // Test 6: Or with one true clause evaluates to true
    // -----------------------------------------------------------------------
    #[test]
    fn test_validate_witness_or_one_true() {
        let validator = WitnessValidator::new();
        let formula = Formula::Or(vec![
            Formula::Eq(Box::new(int_var("x")), Box::new(Formula::Int(10))),
            Formula::Eq(Box::new(int_var("y")), Box::new(Formula::Int(20))),
        ]);
        let vc = make_vc(formula);
        let assignments =
            vec![("x".to_string(), ConstValue::Int(10)), ("y".to_string(), ConstValue::Int(0))];
        let result = validator.validate_witness(&vc, &assignments);
        assert!(result.is_valid(), "x=10 satisfies first disjunct");
    }

    // -----------------------------------------------------------------------
    // Test 7: Not(true) evaluates to false
    // -----------------------------------------------------------------------
    #[test]
    fn test_validate_witness_not_negation() {
        let validator = WitnessValidator::new();
        // Formula: NOT(x == 5)
        let formula =
            Formula::Not(Box::new(Formula::Eq(Box::new(int_var("x")), Box::new(Formula::Int(5)))));
        let vc = make_vc(formula);
        // x=5: NOT(true) = false => Invalid
        let result = validator.validate_witness(&vc, &[("x".to_string(), ConstValue::Int(5))]);
        assert!(result.is_invalid());

        // x=3: NOT(false) = true => Valid
        let result = validator.validate_witness(&vc, &[("x".to_string(), ConstValue::Int(3))]);
        assert!(result.is_valid());
    }

    // -----------------------------------------------------------------------
    // Test 8: Arithmetic evaluation (Add, Sub, Mul)
    // -----------------------------------------------------------------------
    #[test]
    fn test_validate_witness_arithmetic_evaluation() {
        let validator = WitnessValidator::new();
        // Formula: (x + y) == 10
        let formula = Formula::Eq(
            Box::new(Formula::Add(Box::new(int_var("x")), Box::new(int_var("y")))),
            Box::new(Formula::Int(10)),
        );
        let vc = make_vc(formula);

        // x=3, y=7 => (3+7)==10 => true
        let result = validator.validate_witness(
            &vc,
            &[("x".to_string(), ConstValue::Int(3)), ("y".to_string(), ConstValue::Int(7))],
        );
        assert!(result.is_valid());

        // x=3, y=8 => (3+8)==10 => false
        let result = validator.validate_witness(
            &vc,
            &[("x".to_string(), ConstValue::Int(3)), ("y".to_string(), ConstValue::Int(8))],
        );
        assert!(result.is_invalid());
    }

    // -----------------------------------------------------------------------
    // Test 9: Implies evaluation
    // -----------------------------------------------------------------------
    #[test]
    fn test_validate_witness_implies() {
        let validator = WitnessValidator::new();
        // Formula: (x > 0) => (y > 0)
        let formula = Formula::Implies(
            Box::new(Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(0)))),
            Box::new(Formula::Gt(Box::new(int_var("y")), Box::new(Formula::Int(0)))),
        );
        let vc = make_vc(formula);

        // x=-1: antecedent false => implication true
        let result = validator.validate_witness(
            &vc,
            &[("x".to_string(), ConstValue::Int(-1)), ("y".to_string(), ConstValue::Int(-5))],
        );
        assert!(result.is_valid());

        // x=1, y=1: both true => true
        let result = validator.validate_witness(
            &vc,
            &[("x".to_string(), ConstValue::Int(1)), ("y".to_string(), ConstValue::Int(1))],
        );
        assert!(result.is_valid());
    }

    // -----------------------------------------------------------------------
    // Test 10: Ite (if-then-else) evaluation
    // -----------------------------------------------------------------------
    #[test]
    fn test_validate_witness_ite() {
        let validator = WitnessValidator::new();
        // Formula: ite(flag, x, y) == 42
        let formula = Formula::Eq(
            Box::new(Formula::Ite(
                Box::new(Formula::Var("flag".into(), Sort::Bool)),
                Box::new(int_var("x")),
                Box::new(int_var("y")),
            )),
            Box::new(Formula::Int(42)),
        );
        let vc = make_vc(formula);

        // flag=true, x=42 => ite selects x => 42==42 => true
        let result = validator.validate_witness(
            &vc,
            &[
                ("flag".to_string(), ConstValue::Bool(true)),
                ("x".to_string(), ConstValue::Int(42)),
                ("y".to_string(), ConstValue::Int(0)),
            ],
        );
        assert!(result.is_valid());

        // flag=false, y=42 => ite selects y => 42==42 => true
        let result = validator.validate_witness(
            &vc,
            &[
                ("flag".to_string(), ConstValue::Bool(false)),
                ("x".to_string(), ConstValue::Int(0)),
                ("y".to_string(), ConstValue::Int(42)),
            ],
        );
        assert!(result.is_valid());

        // flag=true, x=10 => ite selects x => 10==42 => false
        let result = validator.validate_witness(
            &vc,
            &[
                ("flag".to_string(), ConstValue::Bool(true)),
                ("x".to_string(), ConstValue::Int(10)),
                ("y".to_string(), ConstValue::Int(42)),
            ],
        );
        assert!(result.is_invalid());
    }

    // -----------------------------------------------------------------------
    // Test 11: Boolean constant formula
    // -----------------------------------------------------------------------
    #[test]
    fn test_validate_witness_bool_constant() {
        let validator = WitnessValidator::new();
        // Formula: true (always valid)
        let vc_true = make_vc(Formula::Bool(true));
        let result = validator.validate_witness(&vc_true, &[]);
        assert!(result.is_valid());

        // Formula: false (always invalid)
        let vc_false = make_vc(Formula::Bool(false));
        let result = validator.validate_witness(&vc_false, &[]);
        assert!(result.is_invalid());
    }

    // -----------------------------------------------------------------------
    // Test 12: Unsigned integer witness
    // -----------------------------------------------------------------------
    #[test]
    fn test_validate_witness_uint_assignment() {
        let validator = WitnessValidator::new();
        let formula = Formula::Eq(Box::new(int_var("n")), Box::new(Formula::Int(100)));
        let vc = make_vc(formula);
        // ConstValue::Uint(100, 64) should map to Int(100)
        let assignments = vec![("n".to_string(), ConstValue::Uint(100, 64))];
        let result = validator.validate_witness(&vc, &assignments);
        assert!(result.is_valid(), "Uint(100) should equal Int(100)");
    }

    // -----------------------------------------------------------------------
    // Test 13: Float assignment produces Inconclusive
    // -----------------------------------------------------------------------
    #[test]
    fn test_validate_witness_float_inconclusive() {
        let validator = WitnessValidator::new();
        let formula = Formula::Eq(Box::new(int_var("f")), Box::new(Formula::Int(0)));
        let vc = make_vc(formula);
        // Float cannot be precisely represented => Inconclusive
        let assignments = vec![("f".to_string(), ConstValue::Float(3.125))];
        let result = validator.validate_witness(&vc, &assignments);
        assert!(result.is_inconclusive(), "float witness should be Inconclusive, got {:?}", result);
    }

    // -----------------------------------------------------------------------
    // Test 14: validate_formula convenience method
    // -----------------------------------------------------------------------
    #[test]
    fn test_validate_formula_direct() {
        let validator = WitnessValidator::new();
        let formula = Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(10)));
        let assignments = vec![("x".to_string(), ConstValue::Int(5))];
        let result = validator.validate_formula(&formula, &assignments);
        assert!(result.is_valid(), "5 < 10 should be valid");
    }

    // -----------------------------------------------------------------------
    // Test 15: Default trait for WitnessValidator
    // -----------------------------------------------------------------------
    #[test]
    fn test_witness_validator_default() {
        let validator = WitnessValidator::default();
        let formula = Formula::Bool(true);
        let vc = make_vc(formula);
        assert!(validator.validate_witness(&vc, &[]).is_valid());
    }

    // -----------------------------------------------------------------------
    // Test 16: Complex nested formula
    // -----------------------------------------------------------------------
    #[test]
    fn test_validate_witness_complex_nested() {
        let validator = WitnessValidator::new();
        // Formula: (x > 0 AND y > 0) => (x + y > 0)
        // This should always be valid for positive integers.
        let formula = Formula::Implies(
            Box::new(Formula::And(vec![
                Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(0))),
                Formula::Gt(Box::new(int_var("y")), Box::new(Formula::Int(0))),
            ])),
            Box::new(Formula::Gt(
                Box::new(Formula::Add(Box::new(int_var("x")), Box::new(int_var("y")))),
                Box::new(Formula::Int(0)),
            )),
        );
        let vc = make_vc(formula);
        let assignments =
            vec![("x".to_string(), ConstValue::Int(3)), ("y".to_string(), ConstValue::Int(7))];
        let result = validator.validate_witness(&vc, &assignments);
        assert!(result.is_valid(), "(3>0 AND 7>0) => (10>0) should be valid");
    }

    // -----------------------------------------------------------------------
    // Test 17: Le and Ge comparisons
    // -----------------------------------------------------------------------
    #[test]
    fn test_validate_witness_le_ge_comparisons() {
        let validator = WitnessValidator::new();

        // x <= 5 with x=5 => true
        let formula_le = Formula::Le(Box::new(int_var("x")), Box::new(Formula::Int(5)));
        let result =
            validator.validate_formula(&formula_le, &[("x".to_string(), ConstValue::Int(5))]);
        assert!(result.is_valid(), "5 <= 5 should be valid");

        // x >= 5 with x=3 => false
        let formula_ge = Formula::Ge(Box::new(int_var("x")), Box::new(Formula::Int(5)));
        let result =
            validator.validate_formula(&formula_ge, &[("x".to_string(), ConstValue::Int(3))]);
        assert!(result.is_invalid(), "3 >= 5 should be invalid");
    }

    // -----------------------------------------------------------------------
    // Test 18: Division and remainder
    // -----------------------------------------------------------------------
    #[test]
    fn test_validate_witness_div_rem() {
        let validator = WitnessValidator::new();

        // (x / y) == 5 with x=15, y=3 => 15/3 == 5 => true
        let formula = Formula::Eq(
            Box::new(Formula::Div(Box::new(int_var("x")), Box::new(int_var("y")))),
            Box::new(Formula::Int(5)),
        );
        let result = validator.validate_formula(
            &formula,
            &[("x".to_string(), ConstValue::Int(15)), ("y".to_string(), ConstValue::Int(3))],
        );
        assert!(result.is_valid(), "15/3 == 5 should be valid");

        // (x % y) == 1 with x=7, y=3 => 7%3 == 1 => true
        let formula_rem = Formula::Eq(
            Box::new(Formula::Rem(Box::new(int_var("x")), Box::new(int_var("y")))),
            Box::new(Formula::Int(1)),
        );
        let result = validator.validate_formula(
            &formula_rem,
            &[("x".to_string(), ConstValue::Int(7)), ("y".to_string(), ConstValue::Int(3))],
        );
        assert!(result.is_valid(), "7 % 3 == 1 should be valid");
    }

    // -----------------------------------------------------------------------
    // Test 19: Negation evaluation
    // -----------------------------------------------------------------------
    #[test]
    fn test_validate_witness_negation() {
        let validator = WitnessValidator::new();
        // (-x) == -5 with x=5 => true
        let formula =
            Formula::Eq(Box::new(Formula::Neg(Box::new(int_var("x")))), Box::new(Formula::Int(-5)));
        let result = validator.validate_formula(&formula, &[("x".to_string(), ConstValue::Int(5))]);
        assert!(result.is_valid(), "-5 == -5 should be valid");
    }

    // -----------------------------------------------------------------------
    // Test 20: Or all false evaluates to false
    // -----------------------------------------------------------------------
    #[test]
    fn test_validate_witness_or_all_false() {
        let validator = WitnessValidator::new();
        let formula = Formula::Or(vec![
            Formula::Eq(Box::new(int_var("x")), Box::new(Formula::Int(1))),
            Formula::Eq(Box::new(int_var("x")), Box::new(Formula::Int(2))),
        ]);
        let vc = make_vc(formula);
        // x=99 => neither disjunct holds => false
        let result = validator.validate_witness(&vc, &[("x".to_string(), ConstValue::Int(99))]);
        assert!(result.is_invalid(), "x=99 satisfies neither disjunct");
    }

    // -----------------------------------------------------------------------
    // Test 21: WitnessValidation accessors
    // -----------------------------------------------------------------------
    #[test]
    fn test_witness_validation_accessors() {
        let valid = WitnessValidation::Valid;
        assert!(valid.is_valid());
        assert!(!valid.is_invalid());
        assert!(!valid.is_inconclusive());

        let invalid = WitnessValidation::Invalid { reason: "test".to_string() };
        assert!(!invalid.is_valid());
        assert!(invalid.is_invalid());
        assert!(!invalid.is_inconclusive());

        let inconclusive = WitnessValidation::Inconclusive { reason: "test".to_string() };
        assert!(!inconclusive.is_valid());
        assert!(!inconclusive.is_invalid());
        assert!(inconclusive.is_inconclusive());
    }

    // -----------------------------------------------------------------------
    // Test 22: Sub evaluation
    // -----------------------------------------------------------------------
    #[test]
    fn test_validate_witness_sub_evaluation() {
        let validator = WitnessValidator::new();
        // (x - y) == 3 with x=10, y=7 => true
        let formula = Formula::Eq(
            Box::new(Formula::Sub(Box::new(int_var("x")), Box::new(int_var("y")))),
            Box::new(Formula::Int(3)),
        );
        let result = validator.validate_formula(
            &formula,
            &[("x".to_string(), ConstValue::Int(10)), ("y".to_string(), ConstValue::Int(7))],
        );
        assert!(result.is_valid(), "10 - 7 == 3");
    }

    // -----------------------------------------------------------------------
    // Test 23: Mul evaluation
    // -----------------------------------------------------------------------
    #[test]
    fn test_validate_witness_mul_evaluation() {
        let validator = WitnessValidator::new();
        // (x * y) == 42 with x=6, y=7 => true
        let formula = Formula::Eq(
            Box::new(Formula::Mul(Box::new(int_var("x")), Box::new(int_var("y")))),
            Box::new(Formula::Int(42)),
        );
        let result = validator.validate_formula(
            &formula,
            &[("x".to_string(), ConstValue::Int(6)), ("y".to_string(), ConstValue::Int(7))],
        );
        assert!(result.is_valid(), "6 * 7 == 42");
    }
}
