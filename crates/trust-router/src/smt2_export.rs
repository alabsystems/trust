// trust-router/smt2_export.rs: SMT-LIB2 debug export format
//
// Provides --emit=smt2 functionality: exports VCs as standard SMT-LIB2 scripts
// for debugging and interop with any SMT-LIB2 compliant solver (`ay`, cvc5, etc.).
//
// Delegates formula/sort serialization to the canonical `to_smtlib()` methods
// in trust-types. This module adds VC-level structure: metadata comments,
// (set-logic), (declare-fun), (assert), (check-sat), and batch export.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use trust_types::{Formula, Sort, escape_smtlib_symbol, pred_arg_sorts};

/// Convert a formula to its SMT-LIB2 text representation.
///
/// Delegates to the canonical `Formula::to_smtlib()` in trust-types.
#[must_use]
pub(crate) fn formula_to_smt2(formula: &Formula) -> String {
    formula.to_smtlib()
}

/// Convert a sort to its SMT-LIB2 text representation.
///
/// Delegates to the canonical `Sort::to_smtlib()` in trust-types.
#[must_use]
pub(crate) fn sort_to_smt2(sort: &Sort) -> String {
    sort.to_smtlib()
}

/// Collect `(declare-fun ...)` declarations for all free variables in a formula.
///
/// Returns declarations sorted by variable name for deterministic output.
/// Quantifier-bound variables are excluded.
#[must_use]
pub(crate) fn emit_declarations(formula: &Formula) -> Vec<String> {
    let vars = collect_free_vars(formula);

    // Lever A: datatype sorts must be DECLARED before any `declare-fun` that
    // uses them. Gather every datatype declaration reachable from the free
    // vars' sorts, de-duplicated and topologically ordered (a referenced
    // datatype before the one that uses it). A datatype that appears only as a
    // BY-NAME reference (empty constructors — a recursive back-edge whose full
    // definition is modeled by the flat-`Ty::Adt` encoding, not as a real SMT
    // datatype) has no `declare-datatype`; it is declared as an uninterpreted
    // sort (`declare-sort … 0`) so the referencing `declare-fun` is well-formed.
    // Without this, a `(declare-fun e () Expr)` over an undeclared sort `Expr`
    // makes the whole SMT query malformed.
    let mut decls: Vec<String> = Vec::new();
    let mut datatype_decls: Vec<String> = Vec::new();
    for (_, sort) in &vars {
        for d in sort.datatype_declarations() {
            if !datatype_decls.contains(&d) {
                datatype_decls.push(d);
            }
        }
    }
    // Record full-datatype names so a name that has a real definition is NOT
    // also emitted as an uninterpreted sort (which would be a redeclaration).
    let mut defined_dt: BTreeSet<String> = BTreeSet::new();
    for d in &datatype_decls {
        if let Some(name) =
            d.strip_prefix("(declare-datatype ").and_then(|r| r.split_whitespace().next())
        {
            defined_dt.insert(name.to_string());
        }
    }
    let mut uninterpreted_names: BTreeSet<String> = BTreeSet::new();
    for (_, sort) in &vars {
        collect_uninterpreted_datatype_refs(sort, &defined_dt, &mut uninterpreted_names);
    }
    for name in &uninterpreted_names {
        decls.push(format!("(declare-sort {} 0)", escape_smtlib_symbol(name)));
    }
    decls.extend(datatype_decls);

    decls.extend(vars.into_iter().map(|(name, sort)| {
        format!("(declare-fun {} () {})", escape_smtlib_symbol(&name), sort_to_smt2(&sort))
    }));

    // safe-api: uninterpreted predicate symbols (Formula::Pred) need an
    // ARITY declare-fun returning Bool. Their argument Vars are already declared
    // above (Pred's args are its children, visited by collect_free_vars).
    // Without this, an application like `(dir_open d)` references an undeclared
    // function and the solver errors.
    let mut preds: BTreeMap<String, Vec<Sort>> = BTreeMap::new();
    collect_pred_symbols(formula, &mut preds);
    for (name, arg_sorts) in preds {
        let params: Vec<String> = arg_sorts.iter().map(sort_to_smt2).collect();
        decls.push(format!(
            "(declare-fun {} ({}) Bool)",
            escape_smtlib_symbol(&name),
            params.join(" ")
        ));
    }

    decls
}

/// Collect the names of BY-NAME datatype references (empty-constructor
/// `Sort::Datatype`) reachable from `sort`, EXCLUDING any name that already has
/// a full definition (in `defined`). These are the recursive back-edges that
/// need a `(declare-sort … 0)` so the referencing declaration is well-formed.
fn collect_uninterpreted_datatype_refs(
    sort: &Sort,
    defined: &BTreeSet<String>,
    out: &mut BTreeSet<String>,
) {
    match sort {
        Sort::Datatype { name, constructors } if constructors.is_empty() => {
            if !defined.contains(name) {
                out.insert(name.clone());
            }
        }
        Sort::Datatype { constructors, .. } => {
            for (_, fields) in constructors {
                for (_, fsort) in fields {
                    collect_uninterpreted_datatype_refs(fsort, defined, out);
                }
            }
        }
        Sort::Array(idx, elem) => {
            collect_uninterpreted_datatype_refs(idx, defined, out);
            collect_uninterpreted_datatype_refs(elem, defined, out);
        }
        _ => {}
    }
}

/// Detect the appropriate SMT-LIB2 logic string for a formula.
///
/// Analyzes the formula structure to select the most specific logic:
/// - `QF_LIA` for quantifier-free linear integer arithmetic
/// - `QF_BV` for quantifier-free bitvectors
/// - `QF_AUFLIA` for quantifier-free arrays + integers
/// - `QF_ABV` for quantifier-free arrays + bitvectors
/// - `AUFBVLIA` for quantified arrays + bitvectors + integers
/// - `ALL` as fallback for mixed theories
#[must_use]
pub(crate) fn detect_logic(formula: &Formula) -> &'static str {
    // Lever A: if any free variable carries a datatype (or datatype-back-edge
    // uninterpreted) sort, the query needs the datatype theory. Rather than
    // enumerate every datatype×theory combination (QF_DT / QF_UFDT / AUFDT / …),
    // select `ALL` — ay accepts it and it admits datatypes alongside the BV/Int/
    // UF scalar fields a recursive ADT's leaves produce. SOUNDNESS: `ALL` only
    // WIDENS the admissible theory set; it never changes a formula's models, so
    // it cannot turn a SAT violation into UNSAT (no false-prove).
    if formula_has_datatype_sort(formula) {
        return "ALL";
    }

    let features = analyze_formula(formula);

    // SMT-LIB has no small standard logic name for the mixed FP/BV/array/UF
    // combinations produced by reinterpretation and model formulas. Pure
    // quantifier-free floating point is `QF_FP`; every mix uses the honest
    // `ALL` superset rather than advertising an unrelated integer logic.
    if features.has_floating_point {
        if !features.has_bitvectors
            && !features.has_arrays
            && !features.has_quantifiers
            && !features.has_uninterpreted_functions
        {
            return "QF_FP";
        }
        return "ALL";
    }

    match (
        features.has_bitvectors,
        features.has_arrays,
        features.has_quantifiers,
        features.has_uninterpreted_functions,
    ) {
        // Bitvectors.
        (true, false, false, false) => "QF_BV",
        (true, false, true, false) => "BV",
        (true, false, false, true) => "QF_UFBV",
        (true, false, true, true) => "UFBV",
        // Bitvectors + arrays.
        (true, true, false, false) => "QF_ABV",
        (true, true, true, false) => "ABV",
        (true, true, false, true) => "QF_AUFBV",
        (true, true, true, true) => "AUFBV",
        // Integers + arrays. AUFLIA already includes UF.
        (false, true, false, _) => "QF_AUFLIA",
        (false, true, true, _) => "AUFLIA",
        // Pure UF / integer arithmetic.
        (false, false, false, true) => "QF_UFLIA",
        (false, false, true, true) => "UFLIA",
        (false, false, false, false) => "QF_LIA",
        (false, false, true, false) => "LIA",
    }
}

// --- Internal helpers ---

/// True iff any `Var`/`SymVar` in `formula` carries a sort that is (or
/// transitively contains) a datatype sort — including a by-name datatype
/// back-edge reference. Drives the `ALL`-logic selection in `detect_logic`.
fn formula_has_datatype_sort(formula: &Formula) -> bool {
    let mut found = false;
    formula.visit(&mut |node| match node {
        Formula::Var(_, sort) | Formula::SymVar(_, sort) if sort.contains_datatype() => {
            found = true;
        }
        _ => {}
    });
    found
}

/// Formula features relevant to logic detection.
struct FormulaFeatures {
    has_bitvectors: bool,
    has_floating_point: bool,
    has_arrays: bool,
    has_quantifiers: bool,
    has_uninterpreted_functions: bool,
}

/// Analyze a formula for theory features.
fn analyze_formula(formula: &Formula) -> FormulaFeatures {
    let mut features = FormulaFeatures {
        has_bitvectors: false,
        has_floating_point: false,
        has_arrays: false,
        has_quantifiers: false,
        has_uninterpreted_functions: false,
    };

    formula.visit(&mut |node| {
        match node {
            // Bitvector detection
            Formula::BitVec { .. }
            | Formula::BvAdd(..)
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
            | Formula::BvAShr(..)
            | Formula::BvULt(..)
            | Formula::BvULe(..)
            | Formula::BvSLt(..)
            | Formula::BvSLe(..)
            | Formula::BvToInt(..)
            | Formula::IntToBv(..)
            | Formula::BvExtract { .. }
            | Formula::BvConcat(..)
            | Formula::BvZeroExt(..)
            | Formula::BvSignExt(..) => features.has_bitvectors = true,

            Formula::Var(_, Sort::BitVec(_)) | Formula::SymVar(_, Sort::BitVec(_)) => {
                features.has_bitvectors = true;
            }

            // Floating-point detection. `FpToIeeeBv` deliberately sets both
            // feature bits because it mixes FP input with BV output.
            Formula::FpToIeeeBv(..) => {
                features.has_bitvectors = true;
                features.has_floating_point = true;
            }
            Formula::FpConst { .. }
            | Formula::FpNaN { .. }
            | Formula::FpInf { .. }
            | Formula::FpZero { .. }
            | Formula::FpRoundingMode(..)
            | Formula::FpFromBits { .. }
            | Formula::FpAdd(..)
            | Formula::FpSub(..)
            | Formula::FpMul(..)
            | Formula::FpDiv(..)
            | Formula::FpFma(..)
            | Formula::FpSqrt(..)
            | Formula::FpRem(..)
            | Formula::FpNeg(..)
            | Formula::FpAbs(..)
            | Formula::FpMin(..)
            | Formula::FpMax(..)
            | Formula::FpEq(..)
            | Formula::FpLt(..)
            | Formula::FpLe(..)
            | Formula::FpGt(..)
            | Formula::FpGe(..)
            | Formula::FpIsNaN(..)
            | Formula::FpIsInfinite(..)
            | Formula::FpIsZero(..)
            | Formula::FpIsNormal(..)
            | Formula::FpIsSubnormal(..)
            | Formula::FpIsNegative(..)
            | Formula::FpIsPositive(..) => features.has_floating_point = true,
            Formula::Var(_, Sort::Float { .. } | Sort::RoundingMode)
            | Formula::SymVar(_, Sort::Float { .. } | Sort::RoundingMode) => {
                features.has_floating_point = true;
            }

            // Array detection
            Formula::Select(..) | Formula::Store(..) => features.has_arrays = true,
            Formula::Var(_, Sort::Array(..)) | Formula::SymVar(_, Sort::Array(..)) => {
                features.has_arrays = true;
            }

            // Quantifier detection
            Formula::Forall(..) | Formula::Exists(..) => features.has_quantifiers = true,
            Formula::Pred(..) => features.has_uninterpreted_functions = true,

            _ => {}
        }
    });

    features
}

/// Collect all free variables (name, sort) from a formula, excluding
/// quantifier-bound names. Both string-backed [`Formula::Var`] and interned
/// [`Formula::SymVar`] nodes share this one collector so the native AY program
/// and its canonical SMT transcript cannot disagree about declarations.
pub(crate) fn collect_free_vars(formula: &Formula) -> BTreeSet<(String, Sort)> {
    fn collect(
        formula: &Formula,
        bound_names: &BTreeSet<String>,
        free_vars: &mut BTreeSet<(String, Sort)>,
    ) {
        match formula {
            Formula::Var(name, sort) => {
                if !bound_names.contains(name) {
                    free_vars.insert((name.clone(), sort.clone()));
                }
            }
            Formula::SymVar(name, sort) => {
                let name = name.as_str().to_string();
                if !bound_names.contains(&name) {
                    free_vars.insert((name, sort.clone()));
                }
            }
            Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
                let mut nested_bound_names = bound_names.clone();
                nested_bound_names
                    .extend(bindings.iter().map(|(name, _)| name.as_str().to_string()));
                collect(body, &nested_bound_names, free_vars);
            }
            _ => {
                for child in formula.children() {
                    collect(child, bound_names, free_vars);
                }
            }
        }
    }

    let mut free_vars = BTreeSet::new();
    collect(formula, &BTreeSet::new(), &mut free_vars);
    free_vars
}

/// Collect uninterpreted predicate symbols (name -> declared argument sorts)
/// from a formula, for arity `declare-fun` emission. A predicate's signature is
/// fixed by the closed vocabulary, so we key by name and take the canonical
/// `pred_arg_sorts`; any out-of-vocabulary predicate (should not occur — `Pred`
/// is vocab-gated at parse time) falls back to all-`Int` of the applied arity.
fn collect_pred_symbols(formula: &Formula, preds: &mut BTreeMap<String, Vec<Sort>>) {
    formula.visit(&mut |node| {
        if let Formula::Pred(name, args) = node {
            let arg_sorts = pred_arg_sorts(name.as_str())
                .map(<[Sort]>::to_vec)
                .unwrap_or_else(|| vec![Sort::Int; args.len()]);
            preds.entry(name.as_str().to_string()).or_insert(arg_sorts);
        }
    });
}

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;

    // --- Helpers ---

    fn int_var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    fn bv_var(name: &str, w: u32) -> Formula {
        Formula::Var(name.into(), Sort::BitVec(w))
    }

    // -- Lever A: datatype preamble emission --------------------------------

    /// A by-name recursive-datatype reference (the shape the minimal Lever A
    /// lowering produces for a recursive ADT value) must (1) select a
    /// datatype-capable logic and (2) be DECLARED — as an uninterpreted sort —
    /// BEFORE the `declare-fun` that uses it, so the SMT query is well-formed.
    #[test]
    fn by_name_datatype_var_emits_declare_sort_before_declare_fun() {
        let dt = Sort::Datatype { name: "Expr".into(), constructors: Vec::new() };
        let f = Formula::Eq(
            Box::new(Formula::Var("e".into(), dt.clone())),
            Box::new(Formula::Var("e".into(), dt)),
        );
        assert_eq!(detect_logic(&f), "ALL", "a datatype var must select a datatype-capable logic");

        let decls = emit_declarations(&f);
        let sort_pos = decls.iter().position(|d| d.contains("(declare-sort Expr 0)"));
        let fun_pos = decls.iter().position(|d| d.contains("(declare-fun e () Expr)"));
        assert!(sort_pos.is_some(), "Expr must be declared as a sort: {decls:?}");
        assert!(fun_pos.is_some(), "e must be declared with sort Expr: {decls:?}");
        assert!(
            sort_pos < fun_pos,
            "the sort declaration must precede the const that uses it: {decls:?}"
        );
    }

    /// A FULL datatype sort emits a `declare-datatype` (not a bare sort), and the
    /// recursive self-reference inside it stays a by-name `Expr` (finite output).
    #[test]
    fn full_datatype_var_emits_declare_datatype() {
        let expr_ref = Sort::Datatype { name: "Expr".into(), constructors: Vec::new() };
        let full = Sort::Datatype {
            name: "Expr".into(),
            constructors: vec![
                ("Const".into(), vec![("c".into(), Sort::BitVec(32))]),
                ("App".into(), vec![("f".into(), expr_ref.clone()), ("x".into(), expr_ref)]),
            ],
        };
        let f = Formula::Eq(
            Box::new(Formula::Var("e".into(), full.clone())),
            Box::new(Formula::Var("e".into(), full)),
        );
        let decls = emit_declarations(&f);
        let dt_pos = decls.iter().position(|d| d.contains("(declare-datatype Expr"));
        assert!(dt_pos.is_some(), "a full datatype var must emit a declare-datatype: {decls:?}");
        // Exactly one datatype declaration (self-recursion is by-name, not expanded).
        assert_eq!(
            decls.iter().filter(|d| d.contains("declare-datatype")).count(),
            1,
            "self-recursion must not duplicate the datatype declaration: {decls:?}"
        );
        // And NOT also a redundant (declare-sort Expr 0).
        assert!(
            !decls.iter().any(|d| d.contains("(declare-sort Expr 0)")),
            "a fully-defined datatype must not also be declared as an uninterpreted sort: {decls:?}"
        );
        // The definition still precedes the const that uses it.
        let fun_pos = decls.iter().position(|d| d.contains("(declare-fun e () Expr)"));
        assert!(fun_pos.is_some(), "e must be declared with sort Expr: {decls:?}");
        assert!(dt_pos < fun_pos, "declare-datatype must precede its uses: {decls:?}");
    }

    /// A formula with NO datatype content keeps its precise (non-`ALL`) logic and
    /// emits no sort-declaration preamble — Lever A must not perturb the
    /// existing scalar path.
    #[test]
    fn non_datatype_formula_keeps_precise_logic_and_empty_preamble() {
        let f = Formula::BvAdd(Box::new(bv_var("x", 32)), Box::new(bv_var("y", 32)), 32);
        assert_eq!(detect_logic(&f), "QF_BV");
        let decls = emit_declarations(&f);
        assert!(
            !decls.iter().any(|d| d.contains("declare-sort") || d.contains("declare-datatype")),
            "no datatype content must emit no datatype preamble: {decls:?}"
        );
    }

    // --- formula_to_smt2 tests ---

    #[test]
    fn test_formula_to_smt2_bool_literals() {
        assert_eq!(formula_to_smt2(&Formula::Bool(true)), "true");
        assert_eq!(formula_to_smt2(&Formula::Bool(false)), "false");
    }

    #[test]
    fn test_formula_to_smt2_int_literals() {
        assert_eq!(formula_to_smt2(&Formula::Int(0)), "0");
        assert_eq!(formula_to_smt2(&Formula::Int(42)), "42");
        assert_eq!(formula_to_smt2(&Formula::Int(-7)), "(- 7)");
    }

    #[test]
    fn test_formula_to_smt2_uint_literal() {
        assert_eq!(formula_to_smt2(&Formula::UInt(u128::MAX)), u128::MAX.to_string());
    }

    #[test]
    fn test_formula_to_smt2_bitvec_literal() {
        assert_eq!(formula_to_smt2(&Formula::BitVec { value: 10, width: 32 }), "(_ bv10 32)");
    }

    #[test]
    fn test_formula_to_smt2_variables() {
        assert_eq!(formula_to_smt2(&int_var("x")), "x");
        assert_eq!(formula_to_smt2(&bv_var("y", 64)), "y");
    }

    #[test]
    fn test_formula_to_smt2_boolean_connectives() {
        let p = Formula::Var("p".into(), Sort::Bool);
        let q = Formula::Var("q".into(), Sort::Bool);

        assert_eq!(formula_to_smt2(&Formula::Not(Box::new(p.clone()))), "(not p)");
        assert_eq!(formula_to_smt2(&Formula::And(vec![p.clone(), q.clone()])), "(and p q)");
        assert_eq!(formula_to_smt2(&Formula::Or(vec![p.clone(), q.clone()])), "(or p q)");
        assert_eq!(formula_to_smt2(&Formula::Implies(Box::new(p), Box::new(q))), "(=> p q)");
    }

    #[test]
    fn test_formula_to_smt2_arithmetic() {
        let a = int_var("a");
        let b = int_var("b");

        assert_eq!(
            formula_to_smt2(&Formula::Add(Box::new(a.clone()), Box::new(b.clone()))),
            "(+ a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::Sub(Box::new(a.clone()), Box::new(b.clone()))),
            "(- a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::Mul(Box::new(a.clone()), Box::new(b.clone()))),
            "(* a b)"
        );
        // soundness (round-7): Rust `/` and `%` are TRUNCATED, so they lower
        // to the sign-corrected encoding (not bare Euclidean div/mod). See
        // trust-types/src/formula/smtlib.rs.
        assert_eq!(
            formula_to_smt2(&Formula::Div(Box::new(a.clone()), Box::new(b.clone()))),
            "(div (- a (ite (>= a 0) (mod a b) (- (mod (- a) b)))) b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::Rem(Box::new(a.clone()), Box::new(b.clone()))),
            "(ite (>= a 0) (mod a b) (- (mod (- a) b)))"
        );
        assert_eq!(formula_to_smt2(&Formula::Neg(Box::new(a))), "(- a)");
    }

    #[test]
    fn test_formula_to_smt2_comparisons() {
        let a = int_var("a");
        let b = int_var("b");

        assert_eq!(
            formula_to_smt2(&Formula::Eq(Box::new(a.clone()), Box::new(b.clone()))),
            "(= a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::Lt(Box::new(a.clone()), Box::new(b.clone()))),
            "(< a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::Le(Box::new(a.clone()), Box::new(b.clone()))),
            "(<= a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::Gt(Box::new(a.clone()), Box::new(b.clone()))),
            "(> a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::Ge(Box::new(a.clone()), Box::new(b.clone()))),
            "(>= a b)"
        );
    }

    #[test]
    fn test_formula_to_smt2_bitvector_ops() {
        let a = bv_var("a", 32);
        let b = bv_var("b", 32);

        assert_eq!(
            formula_to_smt2(&Formula::BvAdd(Box::new(a.clone()), Box::new(b.clone()), 32)),
            "(bvadd a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvSub(Box::new(a.clone()), Box::new(b.clone()), 32)),
            "(bvsub a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvAnd(Box::new(a.clone()), Box::new(b.clone()), 32)),
            "(bvand a b)"
        );
        assert_eq!(formula_to_smt2(&Formula::BvNot(Box::new(a.clone()), 32)), "(bvnot a)");
        assert_eq!(
            formula_to_smt2(&Formula::BvULt(Box::new(a.clone()), Box::new(b.clone()), 32)),
            "(bvult a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvSLe(Box::new(a.clone()), Box::new(b.clone()), 32)),
            "(bvsle a b)"
        );
    }

    #[test]
    fn test_formula_to_smt2_bv_conversions() {
        let x = bv_var("x", 32);

        assert_eq!(
            formula_to_smt2(&Formula::BvToInt(Box::new(x.clone()), 32, false)),
            "(bv2nat x)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::IntToBv(Box::new(int_var("n")), 32)),
            "((_ int2bv 32) n)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvExtract { inner: Box::new(x.clone()), high: 15, low: 0 }),
            "((_ extract 15 0) x)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvConcat(Box::new(x.clone()), Box::new(bv_var("y", 32)))),
            "(concat x y)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvZeroExt(Box::new(x.clone()), 32)),
            "((_ zero_extend 32) x)"
        );
        assert_eq!(formula_to_smt2(&Formula::BvSignExt(Box::new(x), 16)), "((_ sign_extend 16) x)");
    }

    #[test]
    fn test_formula_to_smt2_quantifiers() {
        let body = Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(0)));
        let forall = Formula::Forall(vec![("x".into(), Sort::Int)], Box::new(body.clone()));
        assert_eq!(formula_to_smt2(&forall), "(forall ((x Int)) (> x 0))");

        let exists = Formula::Exists(vec![("x".into(), Sort::Int)], Box::new(body));
        assert_eq!(formula_to_smt2(&exists), "(exists ((x Int)) (> x 0))");
    }

    #[test]
    fn test_formula_to_smt2_arrays() {
        let arr = Formula::Var("arr".into(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)));
        let idx = Formula::Int(0);
        let val = Formula::Int(42);

        assert_eq!(
            formula_to_smt2(&Formula::Select(Box::new(arr.clone()), Box::new(idx.clone()))),
            "(select arr 0)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::Store(Box::new(arr), Box::new(idx), Box::new(val))),
            "(store arr 0 42)"
        );
    }

    #[test]
    fn test_formula_to_smt2_ite() {
        let f = Formula::Ite(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Int(1)),
            Box::new(Formula::Int(0)),
        );
        assert_eq!(formula_to_smt2(&f), "(ite true 1 0)");
    }

    // --- sort_to_smt2 tests ---

    #[test]
    fn test_sort_to_smt2_basic() {
        assert_eq!(sort_to_smt2(&Sort::Bool), "Bool");
        assert_eq!(sort_to_smt2(&Sort::Int), "Int");
        assert_eq!(sort_to_smt2(&Sort::BitVec(32)), "(_ BitVec 32)");
        assert_eq!(
            sort_to_smt2(&Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int))),
            "(Array Int Int)"
        );
    }

    #[test]
    fn test_sort_to_smt2_nested_array() {
        let nested = Sort::Array(
            Box::new(Sort::BitVec(64)),
            Box::new(Sort::Array(Box::new(Sort::Int), Box::new(Sort::Bool))),
        );
        assert_eq!(sort_to_smt2(&nested), "(Array (_ BitVec 64) (Array Int Bool))");
    }

    // --- emit_declarations tests ---

    #[test]
    fn test_emit_declarations_simple() {
        let f = Formula::Add(Box::new(int_var("x")), Box::new(int_var("y")));
        let decls = emit_declarations(&f);
        assert_eq!(decls.len(), 2);
        assert_eq!(decls[0], "(declare-fun x () Int)");
        assert_eq!(decls[1], "(declare-fun y () Int)");
    }

    #[test]
    fn test_emit_declarations_includes_symbol_variables() {
        let f = Formula::SymVar(Symbol::intern("interned_bits"), Sort::BitVec(32));
        assert_eq!(emit_declarations(&f), vec!["(declare-fun interned_bits () (_ BitVec 32))"]);
        assert_eq!(detect_logic(&f), "QF_BV");
    }

    #[test]
    fn test_emit_declarations_excludes_bound_symbol_variables() {
        let f = Formula::Forall(
            vec![(Symbol::intern("q"), Sort::Int)],
            Box::new(Formula::Eq(
                Box::new(Formula::SymVar(Symbol::intern("q"), Sort::Int)),
                Box::new(Formula::SymVar(Symbol::intern("free"), Sort::Int)),
            )),
        );
        assert_eq!(emit_declarations(&f), vec!["(declare-fun free () Int)"]);
    }

    #[test]
    fn test_emit_declarations_respects_lexical_quantifier_shadowing() {
        let f = Formula::And(vec![
            Formula::Eq(
                Box::new(Formula::SymVar(Symbol::intern("q"), Sort::Int)),
                Box::new(Formula::Int(7)),
            ),
            Formula::Forall(
                vec![(Symbol::intern("q"), Sort::Bool)],
                Box::new(Formula::Eq(
                    Box::new(Formula::SymVar(Symbol::intern("q"), Sort::Bool)),
                    Box::new(Formula::Bool(true)),
                )),
            ),
        ]);
        assert_eq!(emit_declarations(&f), vec!["(declare-fun q () Int)"]);
    }

    #[test]
    fn test_detect_logic_for_floating_point_and_fp_bv_mix() {
        let fp_sort = Sort::Float { eb: 8, sb: 24 };
        let fp = Formula::FpEq(
            Box::new(Formula::SymVar(Symbol::intern("f"), fp_sort.clone())),
            Box::new(Formula::FpZero { neg: false, eb: 8, sb: 24 }),
        );
        assert_eq!(detect_logic(&fp), "QF_FP");
        assert_eq!(emit_declarations(&fp), vec!["(declare-fun f () (_ FloatingPoint 8 24))"]);

        let fp_bits = Formula::Eq(
            Box::new(Formula::FpToIeeeBv(Box::new(Formula::SymVar(Symbol::intern("f"), fp_sort)))),
            Box::new(Formula::BitVec { value: 0, width: 32 }),
        );
        assert_eq!(detect_logic(&fp_bits), "ALL");
    }

    #[test]
    fn test_emit_declarations_deduplicates() {
        let f = Formula::Add(Box::new(int_var("x")), Box::new(int_var("x")));
        let decls = emit_declarations(&f);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn test_emit_declarations_excludes_quantifier_bound() {
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Add(Box::new(int_var("x")), Box::new(int_var("y")))),
        );
        let decls = emit_declarations(&f);
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0], "(declare-fun y () Int)");
    }

    #[test]
    fn test_emit_declarations_no_vars() {
        let f = Formula::Bool(true);
        let decls = emit_declarations(&f);
        assert!(decls.is_empty());
    }

    #[test]
    fn test_emit_declarations_bitvec_sort() {
        let f = bv_var("bits", 64);
        let decls = emit_declarations(&f);
        assert_eq!(decls[0], "(declare-fun bits () (_ BitVec 64))");
    }

    #[test]
    fn test_emit_declarations_array_sort() {
        let arr = Formula::Var(
            "mem".into(),
            Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
        );
        let decls = emit_declarations(&arr);
        assert_eq!(decls[0], "(declare-fun mem () (Array (_ BitVec 64) (_ BitVec 8)))");
    }

    // --- detect_logic tests ---

    #[test]
    fn test_detect_logic_pure_int() {
        let f = Formula::Add(Box::new(int_var("x")), Box::new(Formula::Int(1)));
        assert_eq!(detect_logic(&f), "QF_LIA");
    }

    #[test]
    fn test_detect_logic_bitvector() {
        let f = Formula::BvAdd(Box::new(bv_var("a", 32)), Box::new(bv_var("b", 32)), 32);
        assert_eq!(detect_logic(&f), "QF_BV");
    }

    #[test]
    fn test_detect_logic_arrays_int() {
        let arr = Formula::Var("arr".into(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)));
        let f = Formula::Select(Box::new(arr), Box::new(Formula::Int(0)));
        assert_eq!(detect_logic(&f), "QF_AUFLIA");
    }

    #[test]
    fn test_detect_logic_arrays_bv() {
        let arr = Formula::Var(
            "mem".into(),
            Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
        );
        let f = Formula::Select(Box::new(arr), Box::new(bv_var("addr", 64)));
        assert_eq!(detect_logic(&f), "QF_ABV");
    }

    #[test]
    fn test_detect_logic_quantified_int() {
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(0)))),
        );
        assert_eq!(detect_logic(&f), "LIA");
    }

    #[test]
    fn test_detect_logic_quantified_bv() {
        let f = Formula::Forall(
            vec![("x".into(), Sort::BitVec(32))],
            Box::new(Formula::BvULt(
                Box::new(bv_var("x", 32)),
                Box::new(Formula::BitVec { value: 100, width: 32 }),
                32,
            )),
        );
        assert_eq!(detect_logic(&f), "BV");
    }

    #[test]
    fn test_detect_logic_pure_bool() {
        let f = Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]);
        assert_eq!(detect_logic(&f), "QF_LIA");
    }

    // --- Additional bitvector operation coverage ---

    #[test]
    fn test_formula_to_smt2_bv_mul_div_rem() {
        let a = bv_var("a", 32);
        let b = bv_var("b", 32);

        assert_eq!(
            formula_to_smt2(&Formula::BvMul(Box::new(a.clone()), Box::new(b.clone()), 32)),
            "(bvmul a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvUDiv(Box::new(a.clone()), Box::new(b.clone()), 32)),
            "(bvudiv a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvSDiv(Box::new(a.clone()), Box::new(b.clone()), 32)),
            "(bvsdiv a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvURem(Box::new(a.clone()), Box::new(b.clone()), 32)),
            "(bvurem a b)"
        );
        assert_eq!(formula_to_smt2(&Formula::BvSRem(Box::new(a), Box::new(b), 32)), "(bvsrem a b)");
    }

    #[test]
    fn test_formula_to_smt2_bv_or_xor_shifts() {
        let a = bv_var("a", 16);
        let b = bv_var("b", 16);

        assert_eq!(
            formula_to_smt2(&Formula::BvOr(Box::new(a.clone()), Box::new(b.clone()), 16)),
            "(bvor a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvXor(Box::new(a.clone()), Box::new(b.clone()), 16)),
            "(bvxor a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvShl(Box::new(a.clone()), Box::new(b.clone()), 16)),
            "(bvshl a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvLShr(Box::new(a.clone()), Box::new(b.clone()), 16)),
            "(bvlshr a b)"
        );
        assert_eq!(formula_to_smt2(&Formula::BvAShr(Box::new(a), Box::new(b), 16)), "(bvashr a b)");
    }

    #[test]
    fn test_formula_to_smt2_bv_comparisons_all() {
        let a = bv_var("a", 8);
        let b = bv_var("b", 8);

        assert_eq!(
            formula_to_smt2(&Formula::BvULt(Box::new(a.clone()), Box::new(b.clone()), 8)),
            "(bvult a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvULe(Box::new(a.clone()), Box::new(b.clone()), 8)),
            "(bvule a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvSLt(Box::new(a.clone()), Box::new(b.clone()), 8)),
            "(bvslt a b)"
        );
        assert_eq!(formula_to_smt2(&Formula::BvSLe(Box::new(a), Box::new(b), 8)), "(bvsle a b)");
    }

    #[test]
    fn test_formula_to_smt2_and_or_empty_and_single() {
        // Empty And => "true", Empty Or => "false"
        assert_eq!(formula_to_smt2(&Formula::And(vec![])), "true");
        assert_eq!(formula_to_smt2(&Formula::Or(vec![])), "false");

        // Single-element And/Or => unwrapped
        assert_eq!(formula_to_smt2(&Formula::And(vec![Formula::Bool(true)])), "true");
        assert_eq!(formula_to_smt2(&Formula::Or(vec![Formula::Bool(false)])), "false");
    }

    #[test]
    fn test_formula_to_smt2_negative_bitvec() {
        // Negative bitvector values should be rendered as two's complement
        let f = Formula::BitVec { value: -1, width: 8 };
        let smt2 = formula_to_smt2(&f);
        // -1 in 8-bit two's complement = 255
        assert_eq!(smt2, "(_ bv255 8)");
    }

    #[test]
    fn test_emit_declarations_declares_pred_symbols() {
        // `(dir_open d)` needs BOTH the arg var `d` (nullary) AND the predicate
        // symbol `dir_open` declared as `(Int) Bool` — otherwise the solver sees
        // an undeclared function (safe-api).
        let f =
            Formula::Pred(Symbol::intern("dir_open"), vec![Formula::Var("d".into(), Sort::Int)]);
        let decls = emit_declarations(&f);
        assert!(
            decls.iter().any(|d| d == "(declare-fun d () Int)"),
            "arg var must be declared: {decls:?}"
        );
        assert!(
            decls.iter().any(|d| d == "(declare-fun dir_open (Int) Bool)"),
            "predicate symbol must be declared with its arity: {decls:?}"
        );
    }

    #[test]
    fn test_emit_declarations_nullary_pred() {
        let f = Formula::Pred(Symbol::intern("priv_dropped"), vec![]);
        let decls = emit_declarations(&f);
        assert!(
            decls.iter().any(|d| d == "(declare-fun priv_dropped () Bool)"),
            "nullary predicate must be declared: {decls:?}"
        );
    }
}
