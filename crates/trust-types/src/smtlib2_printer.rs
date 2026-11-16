// trust-types/smtlib2_printer.rs: SMT-LIB2 pretty printer for string-based interop
//
// Converts string representations of formulas and types to SMT-LIB2 format
// for debugging and interop with SMT-LIB2 solvers (`ay`, cvc5, etc.).
//
// Unlike `smt_printer` which operates on `Formula`/`Sort` types, this module
// works with plain string inputs — useful for pipeline stages that don't have
// typed formula access.
//
// WHY THIS IS NOT FOLDED ONTO THE SHARED LOGIC SELECTOR.
//
// This is the workspace's THIRD complete `(set-logic)/(declare-const)/(assert)/
// (check-sat)` emitter (after `smt_printer` and trust-router's `smt2_export`),
// and the first two were reconciled onto one admissibility table
// (`logic_lattice::LOGIC_LATTICE`) precisely so that no emitter could write a
// logic line its own body contradicts. This one CANNOT join them, and the
// reason is structural rather than a deferral: it never sees a `Formula`. Its
// inputs are `&str` declarations and `&str` assertion bodies that it only
// re-indents, so there is no feature record to compute and nothing to select
// from — `logic_lattice::formula_theories` takes a typed `Formula`.
//
// What replaces selection here is a FIXED CHOICE AT THE TOP OF THE LATTICE:
// `SmtLib2Config::default_logic` is `ALL`, the row that admits
// `Theories::EVERYTHING`. `ALL` is admissible for every possible body, so this
// emitter is the one case where the invariant holds without a classifier, and
// `the_default_logic_is_the_lattice_top` pins it against the shared table so a
// future edit cannot quietly narrow the default to a name that could be too
// weak for a string this printer was handed. A caller that HAS a typed formula
// must use `smt_printer`/`smt2_export` and get a precise name; this one is for
// debug and interop dumps, and it has no in-tree caller beyond the crate's
// re-export.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::smt_logic::split_top_level;

/// Configuration for the SMT-LIB2 pretty printer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SmtLib2Config {
    /// Number of spaces per indentation level.
    pub indent_width: usize,
    /// Target maximum line width before breaking.
    pub line_width: usize,
    /// Whether to wrap assertions with `(! ... :named ...)` annotations.
    pub use_named_asserts: bool,
    /// Whether to include a `(set-logic ...)` command in full queries.
    pub include_logic: bool,
    /// Default logic to use when `include_logic` is true.
    ///
    /// Defaults to `ALL` — the TOP of the shared admissibility table
    /// ([`crate::logic_lattice::LOGIC_LATTICE`]). This printer is handed
    /// strings, not a `Formula`, so it cannot compute a feature record and
    /// cannot select a precise name; the top row is the only choice that is
    /// admissible for every body it might be given. Narrowing this default
    /// would put a logic line over text nothing has classified. See the module
    /// header.
    pub default_logic: String,
}

impl Default for SmtLib2Config {
    fn default() -> Self {
        Self {
            indent_width: 2,
            line_width: 80,
            use_named_asserts: false,
            include_logic: true,
            default_logic: "ALL".to_string(),
        }
    }
}

/// SMT-LIB2 pretty printer operating on string representations.
///
/// Stateless between calls. Each method returns a formatted `String`.
#[derive(Debug, Clone)]
pub struct SmtLib2Printer {
    config: SmtLib2Config,
}

impl SmtLib2Printer {
    /// Create a printer with default configuration.
    #[must_use]
    pub fn new() -> Self {
        Self { config: SmtLib2Config::default() }
    }

    /// Create a printer with the given configuration.
    #[must_use]
    pub fn with_config(config: SmtLib2Config) -> Self {
        Self { config }
    }

    // ------------------------------------------------------------------
    // Formula conversion
    // ------------------------------------------------------------------

    /// Convert a formula string representation to SMT-LIB2 format.
    ///
    /// Applies indentation and line-breaking according to the config.
    /// If the input already fits within `line_width`, returns it unchanged.
    #[must_use]
    pub fn formula_to_smt(&self, formula: &str) -> String {
        let trimmed = formula.trim();
        if trimmed.len() <= self.config.line_width {
            return trimmed.to_string();
        }
        let mut out = String::with_capacity(trimmed.len() + 32);
        self.indent_sexp_into(trimmed, 0, &mut out);
        out
    }

    // ------------------------------------------------------------------
    // Command emitters
    // ------------------------------------------------------------------

    /// Emit a `(declare-const name sort)` command.
    #[must_use]
    pub fn emit_declare_const(&self, name: &str, sort: &str) -> String {
        let mut out = String::with_capacity(name.len() + sort.len() + 20);
        write_declare_const(&mut out, name, sort);
        out
    }

    /// Emit an `(assert expr)` command.
    ///
    /// If `use_named_asserts` is enabled, wraps as `(assert (! expr :named aNN))`.
    #[must_use]
    pub fn emit_assert(&self, expr: &str) -> String {
        let formatted = self.formula_to_smt(expr);
        format!("(assert {formatted})")
    }

    /// Emit a `(check-sat)` command.
    #[must_use]
    pub fn emit_check_sat(&self) -> String {
        "(check-sat)".to_string()
    }

    /// Emit a `(get-model)` command.
    #[must_use]
    pub fn emit_get_model(&self) -> String {
        "(get-model)".to_string()
    }

    /// Emit a `(push 1)` command.
    #[must_use]
    pub fn emit_push(&self) -> String {
        "(push 1)".to_string()
    }

    /// Emit a `(pop 1)` command.
    #[must_use]
    pub fn emit_pop(&self) -> String {
        "(pop 1)".to_string()
    }

    /// Emit a `(set-logic logic)` command.
    #[must_use]
    pub fn emit_set_logic(&self, logic: &str) -> String {
        format!("(set-logic {logic})")
    }

    // ------------------------------------------------------------------
    // Full query generation
    // ------------------------------------------------------------------

    /// Produce a complete SMT-LIB2 query string.
    ///
    /// Includes:
    ///   1. `(set-logic ...)` if `include_logic` is true
    ///   2. `(declare-const ...)` for each declaration
    ///   3. `(assert ...)` for each assertion
    ///   4. `(check-sat)`
    #[must_use]
    pub fn emit_full_query(&self, declarations: &[(&str, &str)], assertions: &[&str]) -> String {
        use std::fmt::Write as _;
        let mut out = String::with_capacity(
            (if self.config.include_logic { self.config.default_logic.len() + 13 } else { 0 })
                + declarations.len() * 28
                + assertions.len() * 24
                + 11,
        );

        if self.config.include_logic {
            out.push_str("(set-logic ");
            out.push_str(&self.config.default_logic);
            out.push_str(")\n");
        }

        for &(name, sort) in declarations {
            write_declare_const(&mut out, name, sort);
            out.push('\n');
        }

        if self.config.use_named_asserts {
            for (i, &expr) in assertions.iter().enumerate() {
                let formatted = self.formula_to_smt(expr);
                let _ = writeln!(out, "(assert (! {formatted} :named a{i}))");
            }
        } else {
            for &expr in assertions {
                let formatted = self.formula_to_smt(expr);
                out.push_str("(assert ");
                out.push_str(&formatted);
                out.push_str(")\n");
            }
        }

        out.push_str("(check-sat)");
        out
    }

    // ------------------------------------------------------------------
    // Internal helpers
    // ------------------------------------------------------------------

    /// Recursively indent an s-expression into `out`.
    ///
    /// Uses `smt_logic::split_top_level` — the canonical
    /// s-expression splitter shared across all SMT printers.
    fn indent_sexp_into(&self, sexp: &str, depth: usize, out: &mut String) {
        let sexp = sexp.trim();
        let current_indent = depth * self.config.indent_width;
        if sexp.len() + current_indent <= self.config.line_width {
            out.push_str(sexp);
            return;
        }
        if !sexp.starts_with('(') || !sexp.ends_with(')') {
            out.push_str(sexp);
            return;
        }
        let inner = &sexp[1..sexp.len() - 1];
        let parts = split_top_level(inner);
        if parts.len() <= 1 {
            out.push_str(sexp);
            return;
        }
        let child_indent = (depth + 1) * self.config.indent_width;
        out.push('(');
        out.push_str(parts[0]);
        for part in &parts[1..] {
            out.push('\n');
            out.extend(std::iter::repeat_n(' ', child_indent));
            self.indent_sexp_into(part, depth + 1, out);
        }
        out.push(')');
    }
}

impl Default for SmtLib2Printer {
    fn default() -> Self {
        Self::new()
    }
}

// ======================================================================
// Free functions
// ======================================================================

/// Escape a string for use as an SMT-LIB2 quoted symbol.
///
/// If the identifier contains characters that are not valid in simple symbols,
/// wraps it in `|...|` with internal `|` and `\` escaped.
#[must_use]
pub fn escape_smt_string(s: &str) -> String {
    if s.is_empty() {
        return "\"\"".to_string();
    }
    // SMT-LIB2 strings use double-quotes with internal `"` escaped as `""`
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for ch in s.chars() {
        if ch == '"' {
            out.push_str("\"\"");
        } else {
            out.push(ch);
        }
    }
    out.push('"');
    out
}

/// Check whether a string is a valid SMT-LIB2 simple symbol.
///
/// Simple symbols consist of letters, digits, and `~ ! @ $ % ^ & * _ - + = < > . ? /`
/// and must not start with a digit.
#[must_use]
pub fn is_valid_smt_identifier(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }
    let first = s.as_bytes()[0];
    if first.is_ascii_digit() {
        return false;
    }
    s.bytes().all(|b| {
        b.is_ascii_alphanumeric()
            || matches!(
                b,
                b'~' | b'!'
                    | b'@'
                    | b'$'
                    | b'%'
                    | b'^'
                    | b'&'
                    | b'*'
                    | b'_'
                    | b'-'
                    | b'+'
                    | b'='
                    | b'<'
                    | b'>'
                    | b'.'
                    | b'?'
                    | b'/'
            )
    })
}

/// Map a Rust type name to the corresponding SMT-LIB2 sort.
///
/// Examples:
/// - `"bool"` -> `"Bool"`
/// - `"i32"`, `"u32"` etc. -> `"(_ BitVec N)"`
/// - `"int"` -> `"Int"`
#[must_use]
pub fn sort_to_smt(sort: &str) -> String {
    sort_to_smt_str(sort).to_string()
}

fn sort_to_smt_str(sort: &str) -> &str {
    match sort {
        "bool" | "Bool" => "Bool",
        "int" | "Int" | "integer" => "Int",
        "real" | "Real" => "Real",
        "i8" | "u8" => "(_ BitVec 8)",
        "i16" | "u16" => "(_ BitVec 16)",
        "i32" | "u32" => "(_ BitVec 32)",
        "i64" | "u64" | "isize" | "usize" => "(_ BitVec 64)",
        "i128" | "u128" => "(_ BitVec 128)",
        "f32" => "(_ FloatingPoint 8 24)",
        "f64" => "(_ FloatingPoint 11 53)",
        // Already SMT-LIB format — pass through
        _ => sort,
    }
}

/// Map a Rust-style operator to its SMT-LIB2 equivalent.
///
/// Examples:
/// - `"+"` -> `"+"`
/// - `"&&"` -> `"and"`
/// - `"!="` -> `"distinct"`
#[must_use]
pub fn operator_to_smt(op: &str) -> String {
    match op {
        "/" => "div",
        "%" => "mod",
        "==" => "=",
        "!=" => "distinct",
        "&&" => "and",
        "||" => "or",
        "!" => "not",
        "&" => "bvand",
        "|" => "bvor",
        "^" => "bvxor",
        "~" => "bvnot",
        "<<" => "bvshl",
        ">>" => "bvashr",  // signed (arithmetic) right shift
        ">>>" => "bvlshr", // unsigned (logical) right shift
        _ => op,
    }
    .to_string()
}

// ======================================================================
// Internal helpers
// ======================================================================

fn write_declare_const(out: &mut String, name: &str, sort: &str) {
    let sort_smt = sort_to_smt_str(sort);
    out.push_str("(declare-const ");
    write_smt_symbol(out, name);
    out.push(' ');
    out.push_str(sort_smt);
    out.push(')');
}

fn write_smt_symbol(out: &mut String, name: &str) {
    if is_valid_smt_identifier(name) {
        out.push_str(name);
    } else {
        out.push('|');
        for ch in name.chars() {
            if ch == '|' || ch == '\\' {
                out.push('\\');
            }
            out.push(ch);
        }
        out.push('|');
    }
}

/// Escape a symbol name for use as a simple or quoted SMT-LIB2 symbol.
#[cfg(test)]
fn escape_smt_symbol(name: &str) -> String {
    if is_valid_smt_identifier(name) {
        name.to_string()
    } else {
        let mut out = String::with_capacity(name.len() + 2);
        write_smt_symbol(&mut out, name);
        out
    }
}

// split_top_level removed — now uses smt_logic::split_top_level.

// ======================================================================
// Tests
// ======================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn printer() -> SmtLib2Printer {
        SmtLib2Printer::new()
    }

    // -----------------------------------------------------------------
    // 1. SmtLib2Config defaults
    // -----------------------------------------------------------------

    #[test]
    fn test_config_defaults() {
        let cfg = SmtLib2Config::default();
        assert_eq!(cfg.indent_width, 2);
        assert_eq!(cfg.line_width, 80);
        assert!(!cfg.use_named_asserts);
        assert!(cfg.include_logic);
        assert_eq!(cfg.default_logic, "ALL");
    }

    // -----------------------------------------------------------------
    // 2. formula_to_smt
    // -----------------------------------------------------------------

    #[test]
    fn test_formula_to_smt_short_passthrough() {
        let p = printer();
        assert_eq!(p.formula_to_smt("(+ x y)"), "(+ x y)");
    }

    #[test]
    fn test_formula_to_smt_trims_whitespace() {
        let p = printer();
        assert_eq!(p.formula_to_smt("  (+ x y)  "), "(+ x y)");
    }

    #[test]
    fn test_formula_to_smt_long_breaks_lines() {
        let config = SmtLib2Config { line_width: 15, ..Default::default() };
        let p = SmtLib2Printer::with_config(config);
        let result = p.formula_to_smt("(and (> x 0) (< y 100) (= z 42))");
        assert!(result.contains('\n'), "Long expression should be broken across lines");
    }

    // -----------------------------------------------------------------
    // 3. emit_declare_const
    // -----------------------------------------------------------------

    #[test]
    fn test_emit_declare_const_int() {
        let p = printer();
        assert_eq!(p.emit_declare_const("x", "Int"), "(declare-const x Int)");
    }

    #[test]
    fn test_emit_declare_const_rust_type() {
        let p = printer();
        assert_eq!(p.emit_declare_const("count", "u32"), "(declare-const count (_ BitVec 32))");
    }

    #[test]
    fn test_emit_declare_const_quoted_symbol() {
        let p = printer();
        let result = p.emit_declare_const("my var", "bool");
        assert_eq!(result, "(declare-const |my var| Bool)");
    }

    // -----------------------------------------------------------------
    // 4. emit_assert
    // -----------------------------------------------------------------

    #[test]
    fn test_emit_assert_simple() {
        let p = printer();
        assert_eq!(p.emit_assert("(= x 0)"), "(assert (= x 0))");
    }

    // -----------------------------------------------------------------
    // 5. emit_check_sat / emit_get_model
    // -----------------------------------------------------------------

    #[test]
    fn test_emit_check_sat() {
        assert_eq!(printer().emit_check_sat(), "(check-sat)");
    }

    #[test]
    fn test_emit_get_model() {
        assert_eq!(printer().emit_get_model(), "(get-model)");
    }

    // -----------------------------------------------------------------
    // 6. emit_push / emit_pop
    // -----------------------------------------------------------------

    #[test]
    fn test_emit_push_pop() {
        let p = printer();
        assert_eq!(p.emit_push(), "(push 1)");
        assert_eq!(p.emit_pop(), "(pop 1)");
    }

    // -----------------------------------------------------------------
    // 7. emit_set_logic
    // -----------------------------------------------------------------

    #[test]
    fn test_emit_set_logic() {
        let p = printer();
        assert_eq!(p.emit_set_logic("QF_LIA"), "(set-logic QF_LIA)");
    }

    /// This emitter has no `Formula` to classify, so its one defence against
    /// writing a logic line its own body contradicts is that the default name
    /// is the TOP of the shared admissibility table. Pinned against that table
    /// rather than against the literal `"ALL"`, so the two cannot drift: if a
    /// future edit narrows the default, or if `ALL` ever stops admitting
    /// everything, this fails.
    #[test]
    fn the_default_logic_is_the_lattice_top() {
        let default_logic = SmtLib2Config::default().default_logic;
        assert_eq!(
            crate::logic_lattice::logic_admits(&default_logic),
            Some(crate::logic_lattice::Theories::EVERYTHING),
            "`{default_logic}` is this printer's default over UNCLASSIFIED text, so it must be \
             the row that admits every theory"
        );
    }

    // -----------------------------------------------------------------
    // 8. emit_full_query
    // -----------------------------------------------------------------

    #[test]
    fn test_emit_full_query_basic() {
        let p = printer();
        let result = p.emit_full_query(&[("x", "Int"), ("y", "Int")], &["(> x 0)", "(< y 10)"]);
        assert!(result.contains("(set-logic ALL)"));
        assert!(result.contains("(declare-const x Int)"));
        assert!(result.contains("(declare-const y Int)"));
        assert!(result.contains("(assert (> x 0))"));
        assert!(result.contains("(assert (< y 10))"));
        assert!(result.contains("(check-sat)"));
    }

    #[test]
    fn test_emit_full_query_no_logic() {
        let config = SmtLib2Config { include_logic: false, ..Default::default() };
        let p = SmtLib2Printer::with_config(config);
        let result = p.emit_full_query(&[("x", "bool")], &["x"]);
        assert!(!result.contains("set-logic"));
        assert!(result.contains("(declare-const x Bool)"));
    }

    #[test]
    fn test_emit_full_query_named_asserts() {
        let config = SmtLib2Config { use_named_asserts: true, ..Default::default() };
        let p = SmtLib2Printer::with_config(config);
        let result = p.emit_full_query(&[], &["(= x 1)", "(= y 2)"]);
        assert!(result.contains("(assert (! (= x 1) :named a0))"));
        assert!(result.contains("(assert (! (= y 2) :named a1))"));
    }

    #[test]
    fn test_emit_full_query_empty() {
        let p = printer();
        let result = p.emit_full_query(&[], &[]);
        assert_eq!(result, "(set-logic ALL)\n(check-sat)");
    }

    #[test]
    fn test_emit_full_query_rust_types() {
        let p = printer();
        let result =
            p.emit_full_query(&[("a", "i32"), ("b", "u64"), ("flag", "bool")], &["(bvadd a b)"]);
        assert!(result.contains("(declare-const a (_ BitVec 32))"));
        assert!(result.contains("(declare-const b (_ BitVec 64))"));
        assert!(result.contains("(declare-const flag Bool)"));
    }

    // -----------------------------------------------------------------
    // 9. escape_smt_string
    // -----------------------------------------------------------------

    #[test]
    fn test_escape_smt_string_simple() {
        assert_eq!(escape_smt_string("hello"), "\"hello\"");
    }

    #[test]
    fn test_escape_smt_string_with_quotes() {
        assert_eq!(escape_smt_string("say \"hi\""), "\"say \"\"hi\"\"\"");
    }

    #[test]
    fn test_escape_smt_string_empty() {
        assert_eq!(escape_smt_string(""), "\"\"");
    }

    // -----------------------------------------------------------------
    // 10. is_valid_smt_identifier
    // -----------------------------------------------------------------

    #[test]
    fn test_is_valid_smt_identifier_simple() {
        assert!(is_valid_smt_identifier("x"));
        assert!(is_valid_smt_identifier("foo_bar"));
        assert!(is_valid_smt_identifier("x123"));
        assert!(is_valid_smt_identifier("+"));
        assert!(is_valid_smt_identifier("<="));
    }

    #[test]
    fn test_is_valid_smt_identifier_invalid() {
        assert!(!is_valid_smt_identifier(""));
        assert!(!is_valid_smt_identifier("123abc"));
        assert!(!is_valid_smt_identifier("foo bar"));
        assert!(!is_valid_smt_identifier("x{y}"));
    }

    // -----------------------------------------------------------------
    // 11. sort_to_smt
    // -----------------------------------------------------------------

    #[test]
    fn test_sort_to_smt_bool() {
        assert_eq!(sort_to_smt("bool"), "Bool");
        assert_eq!(sort_to_smt("Bool"), "Bool");
    }

    #[test]
    fn test_sort_to_smt_int() {
        assert_eq!(sort_to_smt("int"), "Int");
        assert_eq!(sort_to_smt("Int"), "Int");
        assert_eq!(sort_to_smt("integer"), "Int");
    }

    #[test]
    fn test_sort_to_smt_bitvec() {
        assert_eq!(sort_to_smt("i32"), "(_ BitVec 32)");
        assert_eq!(sort_to_smt("u32"), "(_ BitVec 32)");
        assert_eq!(sort_to_smt("i64"), "(_ BitVec 64)");
        assert_eq!(sort_to_smt("u8"), "(_ BitVec 8)");
        assert_eq!(sort_to_smt("i128"), "(_ BitVec 128)");
        assert_eq!(sort_to_smt("usize"), "(_ BitVec 64)");
    }

    #[test]
    fn test_sort_to_smt_passthrough() {
        assert_eq!(sort_to_smt("(_ BitVec 256)"), "(_ BitVec 256)");
        assert_eq!(sort_to_smt("(Array Int Int)"), "(Array Int Int)");
    }

    // -----------------------------------------------------------------
    // 12. operator_to_smt
    // -----------------------------------------------------------------

    #[test]
    fn test_operator_to_smt_arithmetic() {
        assert_eq!(operator_to_smt("+"), "+");
        assert_eq!(operator_to_smt("-"), "-");
        assert_eq!(operator_to_smt("*"), "*");
        assert_eq!(operator_to_smt("/"), "div");
        assert_eq!(operator_to_smt("%"), "mod");
    }

    #[test]
    fn test_operator_to_smt_comparison() {
        assert_eq!(operator_to_smt("=="), "=");
        assert_eq!(operator_to_smt("!="), "distinct");
        assert_eq!(operator_to_smt("<"), "<");
        assert_eq!(operator_to_smt("<="), "<=");
        assert_eq!(operator_to_smt(">"), ">");
        assert_eq!(operator_to_smt(">="), ">=");
    }

    #[test]
    fn test_operator_to_smt_logical() {
        assert_eq!(operator_to_smt("&&"), "and");
        assert_eq!(operator_to_smt("||"), "or");
        assert_eq!(operator_to_smt("!"), "not");
    }

    #[test]
    fn test_operator_to_smt_bitwise() {
        assert_eq!(operator_to_smt("&"), "bvand");
        assert_eq!(operator_to_smt("|"), "bvor");
        assert_eq!(operator_to_smt("^"), "bvxor");
        assert_eq!(operator_to_smt("~"), "bvnot");
        assert_eq!(operator_to_smt("<<"), "bvshl");
        assert_eq!(operator_to_smt(">>"), "bvashr");
        assert_eq!(operator_to_smt(">>>"), "bvlshr");
    }

    // -----------------------------------------------------------------
    // 12b. operator_to_smt — shift signedness
    // -----------------------------------------------------------------

    #[test]
    fn test_operator_to_smt_signed_shift_right() {
        // Signed (arithmetic) shift: sign-extends the high bits.
        assert_eq!(operator_to_smt(">>"), "bvashr");
    }

    #[test]
    fn test_operator_to_smt_unsigned_shift_right() {
        // Unsigned (logical) shift: zero-fills the high bits.
        assert_eq!(operator_to_smt(">>>"), "bvlshr");
    }

    #[test]
    fn test_operator_to_smt_passthrough() {
        assert_eq!(operator_to_smt("bvadd"), "bvadd");
        assert_eq!(operator_to_smt("custom_op"), "custom_op");
    }

    // -----------------------------------------------------------------
    // 13. Indentation depth
    // -----------------------------------------------------------------

    #[test]
    fn test_indent_preserves_structure() {
        let config = SmtLib2Config { line_width: 20, indent_width: 4, ..Default::default() };
        let p = SmtLib2Printer::with_config(config);
        let result = p.formula_to_smt("(and (> x 0) (< y 100) (= z 42))");
        // Should break into multiple lines
        let lines: Vec<&str> = result.lines().collect();
        assert!(lines.len() > 1, "Should have multiple lines");
        assert!(lines[0].starts_with("(and"));
    }

    // -----------------------------------------------------------------
    // 14. Default trait
    // -----------------------------------------------------------------

    #[test]
    fn test_default_printer() {
        let p = SmtLib2Printer::default();
        assert_eq!(p.emit_check_sat(), "(check-sat)");
    }

    // -----------------------------------------------------------------
    // 15. escape_smt_symbol (quoted symbols)
    // -----------------------------------------------------------------

    #[test]
    fn test_escape_smt_symbol_simple() {
        assert_eq!(escape_smt_symbol("x"), "x");
        assert_eq!(escape_smt_symbol("foo_bar"), "foo_bar");
    }

    #[test]
    fn test_escape_smt_symbol_needs_quoting() {
        assert_eq!(escape_smt_symbol("my var"), "|my var|");
        assert_eq!(escape_smt_symbol("x{0}"), "|x{0}|");
    }

    #[test]
    fn test_escape_smt_symbol_pipe_escape() {
        assert_eq!(escape_smt_symbol("a|b"), "|a\\|b|");
    }
}
