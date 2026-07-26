// trust-types/smt_printer.rs: SMT-LIB2 pretty printer for formulas
//
// Produces human-readable, properly indented SMT-LIB2 output.
// Uses Formula::to_smtlib() as the base serializer, then adds
// formatting (indentation, line breaking) and benchmark scaffolding
// (set-logic, declare-fun, assert, check-sat).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::smt_logic::{collect_free_var_decls, split_top_level};
use crate::{Formula, Sort};

/// Configuration for the SMT-LIB2 pretty printer.
#[derive(Debug, Clone, PartialEq)]
pub struct PrintConfig {
    /// Number of spaces per indentation level.
    pub indent_size: usize,
    /// Target maximum line width before breaking.
    pub line_width: usize,
    /// Whether to use `(! ... :named ...)` annotations for sub-expressions.
    pub use_named_lets: bool,
}

impl Default for PrintConfig {
    fn default() -> Self {
        Self { indent_size: 2, line_width: 80, use_named_lets: false }
    }
}

/// SMT-LIB2 pretty printer for `Formula` and related types.
///
/// Wraps a `PrintConfig` and provides methods for emitting well-formatted
/// SMT-LIB2 text. Each method returns a `String` — the printer is stateless
/// between calls.
#[derive(Debug, Clone)]
pub struct SmtPrinter {
    config: PrintConfig,
}

impl SmtPrinter {
    /// Create a printer with the given configuration.
    #[must_use]
    pub fn new(config: PrintConfig) -> Self {
        Self { config }
    }

    /// Create a printer with default configuration.
    #[must_use]
    pub fn with_defaults() -> Self {
        Self::new(PrintConfig::default())
    }

    // ------------------------------------------------------------------
    // Core formula rendering
    // ------------------------------------------------------------------

    /// Convert a formula to a pretty-printed SMT-LIB2 string.
    ///
    /// Delegates to `Formula::to_smtlib()` for the raw representation,
    /// then applies indentation and line-breaking according to `PrintConfig`.
    #[must_use]
    pub fn to_smtlib2(&self, formula: &Formula) -> String {
        let raw = formula.to_smtlib();
        self.pretty_format(&raw)
    }

    // ------------------------------------------------------------------
    // Command emitters
    // ------------------------------------------------------------------

    /// Emit a `(declare-fun name (param_sorts...) return_sort)` command.
    #[must_use]
    pub fn print_declare_fun(
        &self,
        name: &str,
        param_sorts: &[Sort],
        return_sort: &Sort,
    ) -> String {
        let params: Vec<String> = param_sorts.iter().map(|s| s.to_smtlib()).collect();
        format!("(declare-fun {} ({}) {})", name, params.join(" "), return_sort.to_smtlib())
    }

    /// Emit an `(assert <formula>)` command with pretty-printed body.
    #[must_use]
    pub fn print_assert(&self, formula: &Formula) -> String {
        let body = self.to_smtlib2(formula);
        if body.len() + 9 <= self.config.line_width {
            // 9 = len("(assert ") + len(")")
            format!("(assert {body})")
        } else {
            let indent = " ".repeat(self.config.indent_size);
            format!("(assert\n{indent}{body})")
        }
    }

    /// Emit a `(check-sat)` command.
    #[must_use]
    pub fn print_check_sat(&self) -> String {
        "(check-sat)".to_string()
    }

    // ------------------------------------------------------------------
    // Benchmark generation
    // ------------------------------------------------------------------

    /// Produce a complete SMT-LIB2 benchmark string.
    ///
    /// The benchmark includes:
    ///   1. `(set-logic ...)` if a logic name is provided
    ///   2. `(declare-fun ...)` for each free variable in the formula
    ///   3. `(assert <formula>)`
    ///   4. `(check-sat)`
    ///
    /// Variable sorts are extracted from `Formula::Var` nodes.
    #[must_use]
    pub fn format_benchmark(&self, logic: Option<&str>, formula: &Formula) -> String {
        let mut lines: Vec<String> = Vec::new();

        // Set-logic
        if let Some(logic_name) = logic {
            lines.push(format!("(set-logic {logic_name})"));
        }

        // Collect free variable declarations.
        // Already sorted — collect_free_var_decls returns a BTreeSet.
        let decls = self.collect_variable_decls(formula);
        for (name, sort) in &decls {
            lines.push(self.print_declare_fun(name, &[], sort));
        }

        // Assert
        lines.push(self.print_assert(formula));

        // Check-sat
        lines.push(self.print_check_sat());

        lines.join("\n")
    }

    // ------------------------------------------------------------------
    // Internal helpers
    // ------------------------------------------------------------------

    /// Collect `(name, sort)` pairs for all free variables in the formula.
    ///
    /// Delegates to `smt_logic::collect_free_var_decls` — the canonical
    /// free variable collector — and converts the BTreeSet to a sorted Vec.
    fn collect_variable_decls(&self, formula: &Formula) -> Vec<(String, Sort)> {
        collect_free_var_decls(formula).into_iter().collect()
    }

    /// Apply indentation and line-breaking to a raw s-expression string.
    ///
    /// Strategy: if the entire expression fits within `line_width`, return it
    /// unchanged. Otherwise break after each top-level operand, indenting
    /// children by one level.
    fn pretty_format(&self, sexp: &str) -> String {
        if sexp.len() <= self.config.line_width {
            return sexp.to_string();
        }
        self.indent_sexp(sexp, 0)
    }

    /// Recursively indent an s-expression.
    fn indent_sexp(&self, sexp: &str, depth: usize) -> String {
        let sexp = sexp.trim();
        // Fits on one line — keep it.
        let current_indent = depth * self.config.indent_size;
        if sexp.len() + current_indent <= self.config.line_width {
            return sexp.to_string();
        }
        // Not an s-expression — return as-is.
        if !sexp.starts_with('(') || !sexp.ends_with(')') {
            return sexp.to_string();
        }
        // Strip outer parens.
        let inner = &sexp[1..sexp.len() - 1];
        let parts = self.split_top_level(inner);
        if parts.len() <= 1 {
            return sexp.to_string();
        }
        let indent = " ".repeat((depth + 1) * self.config.indent_size);
        let head = &parts[0];
        let rest: Vec<String> = parts[1..].iter().map(|p| self.indent_sexp(p, depth + 1)).collect();
        format!("({head}\n{indent}{})", rest.join(&format!("\n{indent}")))
    }

    /// Split an s-expression body into its top-level tokens/sub-expressions.
    ///
    /// Delegates to `smt_logic::split_top_level` — the canonical
    /// s-expression splitter shared across all SMT printers.
    fn split_top_level<'a>(&self, input: &'a str) -> Vec<&'a str> {
        split_top_level(input)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Formula, Sort};

    fn var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    fn bv_var(name: &str, w: u32) -> Formula {
        Formula::Var(name.into(), Sort::BitVec(w))
    }

    fn printer() -> SmtPrinter {
        SmtPrinter::with_defaults()
    }

    // -----------------------------------------------------------------
    // 1. to_smtlib2 — basic formula rendering
    // -----------------------------------------------------------------

    #[test]
    fn test_to_smtlib2_bool_literal() {
        let p = printer();
        assert_eq!(p.to_smtlib2(&Formula::Bool(true)), "true");
        assert_eq!(p.to_smtlib2(&Formula::Bool(false)), "false");
    }

    #[test]
    fn test_to_smtlib2_integer_literals() {
        let p = printer();
        assert_eq!(p.to_smtlib2(&Formula::Int(42)), "42");
        assert_eq!(p.to_smtlib2(&Formula::Int(-7)), "(- 7)");
        assert_eq!(p.to_smtlib2(&Formula::UInt(100)), "100");
    }

    #[test]
    fn test_to_smtlib2_variable() {
        let p = printer();
        assert_eq!(p.to_smtlib2(&var("x")), "x");
    }

    #[test]
    fn test_to_smtlib2_binary_operations() {
        let p = printer();
        let f = Formula::Add(Box::new(var("x")), Box::new(var("y")));
        assert_eq!(p.to_smtlib2(&f), "(+ x y)");
    }

    #[test]
    fn test_to_smtlib2_and_connective() {
        let p = printer();
        let f = Formula::And(vec![var("a"), var("b"), var("c")]);
        assert_eq!(p.to_smtlib2(&f), "(and a b c)");
    }

    // -----------------------------------------------------------------
    // 2. print_declare_fun
    // -----------------------------------------------------------------

    #[test]
    fn test_print_declare_fun_no_params() {
        let p = printer();
        assert_eq!(p.print_declare_fun("x", &[], &Sort::Int), "(declare-fun x () Int)");
    }

    #[test]
    fn test_print_declare_fun_with_params() {
        let p = printer();
        assert_eq!(
            p.print_declare_fun("f", &[Sort::Int, Sort::Bool], &Sort::BitVec(32)),
            "(declare-fun f (Int Bool) (_ BitVec 32))"
        );
    }

    // -----------------------------------------------------------------
    // 3. print_assert
    // -----------------------------------------------------------------

    #[test]
    fn test_print_assert_short_formula() {
        let p = printer();
        let f = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        assert_eq!(p.print_assert(&f), "(assert (= x 0))");
    }

    #[test]
    fn test_print_assert_long_formula_breaks() {
        let config = PrintConfig { line_width: 20, ..Default::default() };
        let p = SmtPrinter::new(config);
        let f = Formula::And(vec![
            Formula::Eq(Box::new(var("very_long_name_alpha")), Box::new(Formula::Int(1))),
            Formula::Eq(Box::new(var("very_long_name_beta")), Box::new(Formula::Int(2))),
        ]);
        let result = p.print_assert(&f);
        assert!(result.starts_with("(assert\n"));
    }

    // -----------------------------------------------------------------
    // 4. print_check_sat
    // -----------------------------------------------------------------

    #[test]
    fn test_print_check_sat() {
        let p = printer();
        assert_eq!(p.print_check_sat(), "(check-sat)");
    }

    // -----------------------------------------------------------------
    // 5. format_benchmark — full benchmark generation
    // -----------------------------------------------------------------

    #[test]
    fn test_format_benchmark_with_logic() {
        let p = printer();
        let f = Formula::Lt(Box::new(var("x")), Box::new(Formula::Int(10)));
        let bench = p.format_benchmark(Some("QF_LIA"), &f);
        assert!(bench.starts_with("(set-logic QF_LIA)"));
        assert!(bench.contains("(declare-fun x () Int)"));
        assert!(bench.contains("(assert (< x 10))"));
        assert!(bench.ends_with("(check-sat)"));
    }

    #[test]
    fn test_format_benchmark_no_logic() {
        let p = printer();
        let f = Formula::Bool(true);
        let bench = p.format_benchmark(None, &f);
        assert!(!bench.contains("set-logic"));
        assert!(bench.contains("(assert true)"));
        assert!(bench.contains("(check-sat)"));
    }

    #[test]
    fn test_format_benchmark_multiple_variables() {
        let p = printer();
        let f = Formula::And(vec![
            Formula::Lt(Box::new(var("a")), Box::new(var("b"))),
            Formula::Gt(Box::new(var("b")), Box::new(Formula::Int(0))),
        ]);
        let bench = p.format_benchmark(Some("QF_LIA"), &f);
        assert!(bench.contains("(declare-fun a () Int)"));
        assert!(bench.contains("(declare-fun b () Int)"));
    }

    #[test]
    fn test_format_benchmark_bitvector_variables() {
        let p = printer();
        let f = Formula::BvAdd(Box::new(bv_var("x", 32)), Box::new(bv_var("y", 32)), 32);
        let bench = p.format_benchmark(Some("QF_BV"), &f);
        assert!(bench.contains("(declare-fun x () (_ BitVec 32))"));
        assert!(bench.contains("(declare-fun y () (_ BitVec 32))"));
        assert!(bench.contains("(assert (bvadd x y))"));
    }

    // -----------------------------------------------------------------
    // 6. Indentation and line breaking
    // -----------------------------------------------------------------

    #[test]
    fn test_pretty_format_short_unchanged() {
        let p = printer();
        let raw = "(+ x y)";
        assert_eq!(p.pretty_format(raw), raw);
    }

    #[test]
    fn test_pretty_format_long_breaks_lines() {
        let config = PrintConfig { line_width: 15, ..Default::default() };
        let p = SmtPrinter::new(config);
        let raw = "(and (> x 0) (< y 100) (= z 42))";
        let result = p.pretty_format(raw);
        assert!(result.contains('\n'), "Long expression should be broken across lines");
    }

    // -----------------------------------------------------------------
    // 7. PrintConfig defaults
    // -----------------------------------------------------------------

    #[test]
    fn test_print_config_defaults() {
        let cfg = PrintConfig::default();
        assert_eq!(cfg.indent_size, 2);
        assert_eq!(cfg.line_width, 80);
        assert!(!cfg.use_named_lets);
    }

    // -----------------------------------------------------------------
    // 8. Quantifier rendering
    // -----------------------------------------------------------------

    #[test]
    fn test_to_smtlib2_forall() {
        let p = printer();
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0)))),
        );
        assert_eq!(p.to_smtlib2(&f), "(forall ((x Int)) (> x 0))");
    }

    // -----------------------------------------------------------------
    // 9. Bound variables excluded from declarations
    // -----------------------------------------------------------------

    #[test]
    fn test_benchmark_excludes_bound_variables() {
        let p = printer();
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(var("x")), Box::new(var("y")))),
        );
        let bench = p.format_benchmark(None, &f);
        // y is free, x is bound
        assert!(bench.contains("(declare-fun y () Int)"));
        assert!(!bench.contains("(declare-fun x "));
    }

    // -----------------------------------------------------------------
    // 10. Bitvector literals
    // -----------------------------------------------------------------

    #[test]
    fn test_to_smtlib2_bitvec_literal() {
        let p = printer();
        let f = Formula::BitVec { value: 255, width: 8 };
        assert_eq!(p.to_smtlib2(&f), "(_ bv255 8)");
    }

    // -----------------------------------------------------------------
    // 11. ITE rendering
    // -----------------------------------------------------------------

    #[test]
    fn test_to_smtlib2_ite() {
        let p = printer();
        let f = Formula::Ite(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Int(1)),
            Box::new(Formula::Int(0)),
        );
        assert_eq!(p.to_smtlib2(&f), "(ite true 1 0)");
    }

    // -----------------------------------------------------------------
    // 12. Array operations
    // -----------------------------------------------------------------

    #[test]
    fn test_to_smtlib2_select_store() {
        let p = printer();
        let arr = Formula::Var("a".into(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)));
        let sel = Formula::Select(Box::new(arr.clone()), Box::new(Formula::Int(0)));
        assert_eq!(p.to_smtlib2(&sel), "(select a 0)");

        let st =
            Formula::Store(Box::new(arr), Box::new(Formula::Int(0)), Box::new(Formula::Int(42)));
        assert_eq!(p.to_smtlib2(&st), "(store a 0 42)");
    }
}
