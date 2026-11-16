// trust-types/spec_float_eq.rs: what a contract `==` between floats means.
//
// SPEC-FLOAT-EQ-STRUCTURAL-1. A contract is Rust, so `x == y` in a `requires`,
// `ensures` or `invariant` clause is Rust's `PartialEq::eq`. For an integer or a
// bool that is the formula language's `Eq`. For an IEEE float it is NOT: Rust's
// `==` is IEEE equality — `NaN == NaN` is false and `0.0 == -0.0` is true —
// while `Formula::Eq` is SMT-LIB `=`, which is structural (every NaN is the one
// NaN value, and +0 and -0 are distinct values). `Formula::FpEq` is the IEEE
// node (`fp.eq`).
//
// Spelling a float `==` as `Eq` was a live lie in both directions: the callsite
// precondition `requires x == y` was PROVED for `c(f64::NAN, f64::NAN)` (the
// binary then broke the clause), and REFUTED for `c(0.0, -0.0)`, which the clause
// admits. This module is the one rule every producer of a contract formula
// applies once the operand sorts are known: the parser (a float literal fixes
// the sort at parse time), `retype_formula_variables` (a signature sort fixes it
// afterwards), the compiler-domain rebinding in `model.rs`, and the
// compiler-proposition lowering in trust-mir-extract. All of them must agree,
// because several consumers compare their outputs structurally.
//
// What this module deliberately does NOT do: reinterpret `Formula::Eq` itself.
// `Eq` over a float sort stays structural `=` everywhere, because that is what
// the body encoding needs — vcgen defines a float temporary with the equation
// `Eq(FpFromBits(dest), fp.add(..))`, and reading that equation as `fp.eq` would
// make every NaN-producing definition unsatisfiable (a vacuous proof). The fix is
// therefore at the producer of the CONTRACT formula, not at the solver bridge.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::{Formula, Sort};

/// Whether `operand` is a FLOAT operand of a contract comparison.
///
/// An operand whose sort checks to an IEEE `Sort::Float` is one. An operand
/// whose sort cannot be established (`check_formula_sort` errs) is one as soon
/// as any of its leaves is float-sorted: the comparison is ill-sorted either
/// way and every sort-checking consumer still refuses it, but spelling it
/// `FpEq` keeps a sort-blind consumer from reading it as structural `=`.
#[must_use]
pub fn spec_operand_is_float(operand: &Formula) -> bool {
    match crate::smt_logic::check_formula_sort_cow(operand) {
        Ok(sort) => matches!(sort.as_ref(), Sort::Float { .. }),
        Err(_) => crate::any_formula_node(operand, &mut |node| {
            matches!(
                node,
                Formula::FpConst { .. }
                    | Formula::FpNaN { .. }
                    | Formula::FpInf { .. }
                    | Formula::FpZero { .. }
            ) || matches!(node.var_sort(), Some(Sort::Float { .. }))
        }),
    }
}

/// The formula a contract `lhs == rhs` denotes: Rust `PartialEq`.
///
/// IEEE [`Formula::FpEq`] when either operand is a float operand
/// ([`spec_operand_is_float`]), structural [`Formula::Eq`] otherwise. A contract
/// `lhs != rhs` is `Not` of this: Rust's float `!=` is exactly the negation of
/// IEEE equality (true when either side is NaN).
#[must_use]
pub fn spec_equality(lhs: Box<Formula>, rhs: Box<Formula>) -> Formula {
    if spec_operand_is_float(&lhs) || spec_operand_is_float(&rhs) {
        Formula::FpEq(lhs, rhs)
    } else {
        Formula::Eq(lhs, rhs)
    }
}

/// Rewrite every contract `Eq` whose operands are float operands into IEEE
/// `FpEq`, bottom-up. Every other node, including an `Eq` over non-float
/// operands and an existing `FpEq`, is returned unchanged.
///
/// Only for CONTRACT formulas (source clauses after their sorts are known). A
/// body or VC formula's `Eq` is a structural equation by design and must never
/// pass through here.
#[must_use]
pub fn normalize_spec_float_equality(formula: Formula) -> Formula {
    if !contains_structural_float_equality(&formula) {
        return formula;
    }
    formula.map(&mut |node| match node {
        Formula::Eq(lhs, rhs) => spec_equality(lhs, rhs),
        other => other,
    })
}

/// Whether `formula` contains a structural `Eq` whose operand is a float
/// operand — the shape [`normalize_spec_float_equality`] removes. A contract
/// formula that still has one after normalization was built by a producer that
/// bypassed this module.
#[must_use]
pub fn contains_structural_float_equality(formula: &Formula) -> bool {
    crate::any_formula_node(formula, &mut |node| {
        matches!(
            node,
            Formula::Eq(lhs, rhs)
                if spec_operand_is_float(lhs) || spec_operand_is_float(rhs)
        )
    })
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;

    const F64: Sort = Sort::Float { eb: 11, sb: 53 };
    const F32: Sort = Sort::Float { eb: 8, sb: 24 };

    fn fv(name: &str) -> Box<Formula> {
        Box::new(Formula::Var(name.to_string(), F64))
    }

    fn lit(value: f64) -> Box<Formula> {
        Box::new(Formula::FpConst { bits: u128::from(value.to_bits()), eb: 11, sb: 53 })
    }

    fn f64_sorts(names: &[&str]) -> BTreeMap<String, Sort> {
        names.iter().map(|name| ((*name).to_string(), F64)).collect()
    }

    #[test]
    fn float_literal_comparison_parses_to_ieee_equality() {
        // `x == 1.0`: the literal fixes the comparison's sort at parse time.
        let parsed = crate::parse_spec_expr("x == 1.0").expect("parses");
        assert_eq!(parsed, Formula::FpEq(fv("x"), lit(1.0)));
        // `x != 0.0` is the negation of IEEE equality (true for NaN).
        let parsed = crate::parse_spec_expr("x != 0.0").expect("parses");
        assert_eq!(parsed, Formula::Not(Box::new(Formula::FpEq(fv("x"), lit(0.0)))));
        // A negative literal folds into a float constant and still selects FpEq.
        let parsed = crate::parse_spec_expr("x == -0.0").expect("parses");
        assert_eq!(parsed, Formula::FpEq(fv("x"), lit(-0.0)));
    }

    #[test]
    fn integer_and_bool_comparisons_stay_structural() {
        let parsed = crate::parse_spec_expr("i == 3").expect("parses");
        assert!(matches!(parsed, Formula::Eq(..)), "{parsed:?}");
        let mut sorts = BTreeMap::new();
        sorts.insert("flag".to_string(), Sort::Bool);
        let typed = crate::retype_formula_variables(
            crate::parse_spec_expr("flag == true").expect("parses"),
            &sorts,
        );
        assert!(matches!(typed, Formula::Eq(..)), "{typed:?}");
        assert!(!contains_structural_float_equality(&typed));
    }

    #[test]
    fn retype_turns_a_float_parameter_equality_into_fp_eq() {
        // `x == y` between two bare parameters parses Int-sorted: only the
        // signature knows they are f64. The retype is where the meaning is fixed.
        let parsed = crate::parse_spec_expr("x == y").expect("parses");
        assert!(matches!(parsed, Formula::Eq(..)));
        let typed = crate::retype_formula_variables(parsed, &f64_sorts(&["x", "y"]));
        assert_eq!(typed, Formula::FpEq(fv("x"), fv("y")));
        assert_eq!(crate::check_formula_sort(&typed), Ok(Sort::Bool));

        let parsed = crate::parse_spec_expr("x != y").expect("parses");
        let typed = crate::retype_formula_variables(parsed, &f64_sorts(&["x", "y"]));
        assert_eq!(typed, Formula::Not(Box::new(Formula::FpEq(fv("x"), fv("y")))));
    }

    #[test]
    fn retype_rewrites_nested_equalities_bottom_up() {
        let parsed = crate::parse_spec_expr("(x == y || i < 4) && !(x == z)").expect("parses");
        let mut sorts = f64_sorts(&["x", "y", "z"]);
        sorts.insert("i".to_string(), Sort::Int);
        let typed = crate::retype_formula_variables(parsed, &sorts);
        assert!(!contains_structural_float_equality(&typed), "{typed:?}");
        let mut fp_eqs = 0;
        typed.visit(&mut |node| {
            if matches!(node, Formula::FpEq(..)) {
                fp_eqs += 1;
            }
        });
        assert_eq!(fp_eqs, 2, "{typed:?}");
    }

    #[test]
    fn rendered_fp_eq_round_trips_through_the_canonicalizer() {
        // The renderer spells FpEq `==`; the reparse yields `Eq` over Int
        // leaves, and the retype with the signature sorts restores FpEq exactly.
        let sorts = f64_sorts(&["x", "y"]);
        let canonical = crate::canonicalize_spec_expr_with_sorts("x == y", &sorts)
            .expect("float equality canonicalizes");
        assert_eq!(canonical, "(x == y)");
        let canonical = crate::canonicalize_spec_expr_with_sorts("x != y", &sorts)
            .expect("float disequality canonicalizes");
        assert_eq!(canonical, "!((x == y))");
        assert_eq!(
            crate::formula_to_spec_expr(&Formula::FpEq(fv("x"), fv("y"))).expect("renders"),
            "(x == y)"
        );
    }

    #[test]
    fn mixed_format_equality_is_fp_eq_and_still_ill_sorted() {
        // An f32 parameter against a binary64 literal it cannot represent: the
        // comparison stays ill-sorted (refused by every checker), but it is never
        // spelled as structural `=`.
        let mut sorts = BTreeMap::new();
        sorts.insert("s".to_string(), F32);
        let typed = crate::retype_formula_variables(
            crate::parse_spec_expr("s == 0.1").expect("parses"),
            &sorts,
        );
        assert!(matches!(typed, Formula::FpEq(..)), "{typed:?}");
        assert!(crate::check_formula_sort(&typed).is_err());
    }

    #[test]
    fn ill_sorted_operand_with_a_float_leaf_counts_as_float() {
        // `x + 1.0` has no formula sort (`Add` is Int/Real only), but a float
        // leaf decides that its equality is not structural.
        let sum = Formula::Add(fv("x"), lit(1.0));
        assert!(crate::check_formula_sort(&sum).is_err());
        assert!(spec_operand_is_float(&sum));
        assert!(matches!(spec_equality(Box::new(sum), lit(2.0)), Formula::FpEq(..)));
        // An Int-sorted term with no float leaf is not.
        assert!(!spec_operand_is_float(&Formula::Var("i".into(), Sort::Int)));
    }

    #[test]
    fn spec_attrs_lowering_agrees_with_the_parser() {
        // The high-level attribute AST lowers `x == 1.0` through the same rule.
        let attr = crate::parse_spec_attr("requires", "x == 1.0").expect("parses");
        let crate::HighLevelSpecAttr::Requires(expr) = attr else {
            panic!("requires attribute expected");
        };
        let formula = crate::try_spec_expr_to_formula(&expr).expect("lowers");
        assert!(matches!(formula, Formula::FpEq(..)), "{formula:?}");
    }

    /// The trust-types half of trust-mir-extract's canonical-source round trip:
    /// rebinding the parsed text to the compiler's float domains must give the
    /// `FpEq` the proposition lowering builds, an `f32` literal narrowed.
    #[test]
    fn compiler_domain_rebinding_spells_float_equality_as_fp_eq() {
        use crate::{CompilerContractValueDomain as Domain, CompilerContractVariableDomain};
        let domain =
            |name: &str, domain| CompilerContractVariableDomain { name: name.to_string(), domain };
        let f64s =
            [domain("x", Domain::Float { width: 64 }), domain("y", Domain::Float { width: 64 })];
        let parsed = crate::parse_spec_expr("x == y").expect("parses");
        assert_eq!(
            crate::compiler_contract_formula_with_domains(&parsed, &f64s),
            Some(Formula::FpEq(fv("x"), fv("y")))
        );
        let f32s = [domain("x", Domain::Float { width: 32 })];
        let parsed = crate::parse_spec_expr("x == 1.0").expect("parses");
        assert_eq!(
            crate::compiler_contract_formula_with_domains(&parsed, &f32s),
            Some(Formula::FpEq(
                Box::new(Formula::Var("x".into(), F32)),
                Box::new(Formula::FpConst { bits: u128::from(1.0_f32.to_bits()), eb: 8, sb: 24 }),
            ))
        );
        let ints = [domain("i", Domain::MachineInt { width: 8, signed: false })];
        let parsed = crate::parse_spec_expr("i == 3").expect("parses");
        assert!(matches!(
            crate::compiler_contract_formula_with_domains(&parsed, &ints),
            Some(Formula::Eq(..))
        ));
    }

    #[test]
    fn normalization_is_idempotent_and_leaves_fp_eq_alone() {
        let once = normalize_spec_float_equality(Formula::Eq(fv("x"), lit(1.0)));
        assert_eq!(once, Formula::FpEq(fv("x"), lit(1.0)));
        assert_eq!(normalize_spec_float_equality(once.clone()), once);
    }
}
