// trust-strengthen/structural_gate.rs: Structural validation gate for spec proposals
//
// Validates that LLM-proposed specifications are well-formed, safe, and non-trivial
// before they are accepted into the prove-strengthen-backprop loop. Prevents unsound
// proposals like assume(false), #[trusted], panic!(), and trivial tautologies.
//
// Per issue #142 and Verification Loop Architecture v2 (Section 2).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::parse_spec_expr_result;

use crate::gate_diagnostics::{
    DiagnosticKind, FixSuggestion, GateDiagnostic, Severity, suggest_fix,
};
use crate::proposer::{Proposal, ProposalKind};

/// Configuration for the structural gate.
#[derive(Debug, Clone)]
pub struct GateConfig {
    /// Maximum depth of nested expressions allowed in a spec body.
    pub max_depth: usize,
    /// Maximum number of operators (&&, ||, ==, <, >, etc.) allowed.
    pub max_operators: usize,
    /// Maximum length of the spec body string (characters).
    pub max_length: usize,
    /// Known variables in scope at the annotation point.
    /// If empty, scope checking is skipped.
    pub scope_vars: Vec<ScopedVar>,
    /// Existing specs for the function (for contradiction detection).
    pub existing_specs: Vec<String>,
    /// Whether to treat warnings as rejections.
    pub strict_mode: bool,
}

impl Default for GateConfig {
    fn default() -> Self {
        Self {
            max_depth: 10,
            max_operators: 20,
            max_length: 500,
            scope_vars: Vec::new(),
            existing_specs: Vec::new(),
            strict_mode: false,
        }
    }
}

/// A variable known to be in scope at the annotation point.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScopedVar {
    /// Variable name.
    pub name: String,
    /// Type as a string (e.g., "u64", "&[i32]").
    pub ty: String,
}

impl ScopedVar {
    /// Create a new scoped variable.
    #[must_use]
    pub fn new(name: impl Into<String>, ty: impl Into<String>) -> Self {
        Self { name: name.into(), ty: ty.into() }
    }
}

/// Result of running a proposal through the structural gate.
#[derive(Debug, Clone)]
pub struct GateResult {
    /// Whether the proposal passed the gate.
    pub passed: bool,
    /// All diagnostics produced during validation.
    pub diagnostics: Vec<GateDiagnostic>,
    /// The proposal that was checked (for traceability).
    pub function_name: String,
    /// Which spec body was checked.
    pub spec_body: String,
}

impl GateResult {
    /// Number of rejections in the result.
    #[must_use]
    pub fn rejection_count(&self) -> usize {
        self.diagnostics.iter().filter(|d| d.severity == Severity::Reject).count()
    }

    /// Number of warnings in the result.
    #[must_use]
    pub fn warning_count(&self) -> usize {
        self.diagnostics.iter().filter(|d| d.severity == Severity::Warn).count()
    }

    /// Get all rejection diagnostics.
    #[must_use]
    pub fn rejections(&self) -> Vec<&GateDiagnostic> {
        self.diagnostics.iter().filter(|d| d.severity == Severity::Reject).collect()
    }
}

/// The structural gate that validates spec proposals before acceptance.
///
/// Runs a sequence of checks on each proposal's spec body:
/// 1. Empty spec detection
/// 2. Syntax validation (balanced parens, valid identifiers)
/// 3. Unsafe content detection (assume(false), panic!(), unreachable!(), etc.)
/// 4. Tautology detection (true, x == x, etc.)
/// 5. Contradiction/trivial weakening detection (requires(false))
/// 6. Complexity bounds enforcement
/// 7. Side effect detection (function calls, assignments)
/// 8. Scope checking (if scope info is available)
#[derive(Debug, Clone)]
pub struct StructuralGate {
    config: GateConfig,
}

impl StructuralGate {
    /// Create a new structural gate with default configuration.
    #[must_use]
    pub fn new() -> Self {
        Self { config: GateConfig::default() }
    }

    /// Create a structural gate with custom configuration.
    #[must_use]
    pub fn with_config(config: GateConfig) -> Self {
        Self { config }
    }

    /// Validate a single proposal through the gate.
    #[must_use]
    pub fn check(&self, proposal: &Proposal) -> GateResult {
        let spec_body = extract_spec_body(&proposal.kind);
        let mut diagnostics = Vec::new();

        // Run all checks
        self.check_empty(&spec_body, &mut diagnostics);
        self.check_syntax(&spec_body, &proposal.kind, &mut diagnostics);
        self.check_unsafe_content(&spec_body, &mut diagnostics);
        self.check_tautology(&spec_body, &proposal.kind, &mut diagnostics);
        self.check_contradiction(&spec_body, &proposal.kind, &mut diagnostics);
        self.check_complexity(&spec_body, &mut diagnostics);
        self.check_side_effects(&spec_body, &mut diagnostics);
        self.check_scope(&spec_body, &mut diagnostics);

        // Attach fix suggestions to diagnostics that lack them
        for diag in &mut diagnostics {
            if diag.suggestion.is_none()
                && let Some(fix) = suggest_fix(&diag.kind, &spec_body)
            {
                diag.suggestion = Some(fix);
            }
        }

        let passed = if self.config.strict_mode {
            !diagnostics.iter().any(|d| d.severity >= Severity::Warn)
        } else {
            !diagnostics.iter().any(|d| d.severity == Severity::Reject)
        };

        GateResult { passed, diagnostics, function_name: proposal.function_name.clone(), spec_body }
    }

    /// Validate multiple proposals, returning results for each.
    #[must_use]
    pub fn check_all(&self, proposals: &[Proposal]) -> Vec<GateResult> {
        proposals.iter().map(|p| self.check(p)).collect()
    }

    /// Filter proposals, keeping only those that pass the gate.
    #[must_use]
    pub fn filter(&self, proposals: Vec<Proposal>) -> Vec<Proposal> {
        proposals.into_iter().filter(|p| self.check(p).passed).collect()
    }

    // --- Individual checks ---

    fn check_empty(&self, spec_body: &str, diagnostics: &mut Vec<GateDiagnostic>) {
        if spec_body.trim().is_empty() {
            diagnostics.push(GateDiagnostic::reject(
                DiagnosticKind::EmptySpec,
                "spec body is empty or whitespace-only",
                spec_body,
            ));
        }
    }

    fn check_syntax(
        &self,
        spec_body: &str,
        kind: &ProposalKind,
        diagnostics: &mut Vec<GateDiagnostic>,
    ) {
        let trimmed = spec_body.trim();
        if trimmed.is_empty() {
            return; // Already caught by check_empty
        }

        // Check balanced parentheses
        let mut depth: i32 = 0;
        for ch in trimmed.chars() {
            match ch {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth < 0 {
                        diagnostics.push(GateDiagnostic::reject(
                            DiagnosticKind::SyntaxError,
                            "unbalanced parentheses: unexpected closing ')'",
                            trimmed,
                        ));
                        return;
                    }
                }
                _ => {}
            }
        }
        if depth != 0 {
            diagnostics.push(GateDiagnostic::reject(
                DiagnosticKind::SyntaxError,
                format!("unbalanced parentheses: {depth} unclosed '('"),
                trimmed,
            ));
            return;
        }

        // Check balanced brackets
        let mut bracket_depth: i32 = 0;
        for ch in trimmed.chars() {
            match ch {
                '[' => bracket_depth += 1,
                ']' => {
                    bracket_depth -= 1;
                    if bracket_depth < 0 {
                        diagnostics.push(GateDiagnostic::reject(
                            DiagnosticKind::SyntaxError,
                            "unbalanced brackets: unexpected closing ']'",
                            trimmed,
                        ));
                        return;
                    }
                }
                _ => {}
            }
        }
        if bracket_depth != 0 {
            diagnostics.push(GateDiagnostic::reject(
                DiagnosticKind::SyntaxError,
                format!("unbalanced brackets: {bracket_depth} unclosed '['"),
                trimmed,
            ));
            return;
        }

        // Check for obviously invalid tokens: bare semicolons (statements, not expressions)
        if trimmed.contains(';') {
            diagnostics.push(GateDiagnostic::reject(
                DiagnosticKind::SyntaxError,
                "spec body contains semicolons; specs must be expressions, not statements",
                trimmed,
            ));
        }

        // Check for bare curly braces (block expressions / code injection)
        if trimmed.contains('{') || trimmed.contains('}') {
            diagnostics.push(GateDiagnostic::reject(
                DiagnosticKind::SyntaxError,
                "spec body contains curly braces; specs must be simple expressions",
                trimmed,
            ));
        }

        // Parser-based validation for spec-bearing kinds only.
        // SafeArithmetic, AddBoundsCheck, and AddNonZeroCheck contain Rust code,
        // not spec expressions, so we skip the spec parser for those.
        if is_spec_bearing_kind(kind)
            && let Err(parse_err) = parse_spec_expr_result(trimmed)
        {
            diagnostics.push(GateDiagnostic::reject(
                DiagnosticKind::SyntaxError,
                format!("spec body failed to parse as a valid spec expression: {parse_err}"),
                trimmed,
            ));
        }
    }

    fn check_unsafe_content(&self, spec_body: &str, diagnostics: &mut Vec<GateDiagnostic>) {
        let lower = spec_body.to_lowercase();

        // assume(false) -- introduces unsoundness
        if contains_call(spec_body, "assume") && lower.contains("false") {
            diagnostics.push(
                GateDiagnostic::reject(
                    DiagnosticKind::Unsoundness,
                    "spec contains assume(false), which introduces unsoundness",
                    spec_body,
                )
                .with_suggestion(FixSuggestion::with_replacement(
                    "Replace assume(false) with a meaningful precondition",
                    "true /* replace with actual precondition */",
                )),
            );
        }

        // #[trusted] attribute
        if spec_body.contains("#[trusted]")
            || spec_body.contains("trusted") && spec_body.contains('#')
        {
            diagnostics.push(GateDiagnostic::reject(
                DiagnosticKind::UnsafeContent,
                "spec contains #[trusted] attribute, which bypasses verification",
                spec_body,
            ));
        }

        // panic!() -- not a pure expression
        if spec_body.contains("panic!") {
            diagnostics.push(GateDiagnostic::reject(
                DiagnosticKind::UnsafeContent,
                "spec contains panic!(), which is not a pure boolean expression",
                spec_body,
            ));
        }

        // unreachable!() -- not a pure expression
        if spec_body.contains("unreachable!") {
            diagnostics.push(GateDiagnostic::reject(
                DiagnosticKind::UnsafeContent,
                "spec contains unreachable!(), which is not a pure boolean expression",
                spec_body,
            ));
        }

        // todo!() / unimplemented!() -- not pure
        if spec_body.contains("todo!") {
            diagnostics.push(GateDiagnostic::reject(
                DiagnosticKind::UnsafeContent,
                "spec contains todo!(), which is not a pure boolean expression",
                spec_body,
            ));
        }
        if spec_body.contains("unimplemented!") {
            diagnostics.push(GateDiagnostic::reject(
                DiagnosticKind::UnsafeContent,
                "spec contains unimplemented!(), which is not a pure boolean expression",
                spec_body,
            ));
        }

        // unsafe block
        if spec_body.contains("unsafe") {
            diagnostics.push(GateDiagnostic::reject(
                DiagnosticKind::UnsafeContent,
                "spec contains 'unsafe' keyword, which must not appear in specifications",
                spec_body,
            ));
        }

        // std::process::exit, std::process::abort
        if spec_body.contains("process::exit") || spec_body.contains("process::abort") {
            diagnostics.push(GateDiagnostic::reject(
                DiagnosticKind::UnsafeContent,
                "spec contains process termination, which is not a pure expression",
                spec_body,
            ));
        }
    }

    fn check_tautology(
        &self,
        spec_body: &str,
        kind: &ProposalKind,
        diagnostics: &mut Vec<GateDiagnostic>,
    ) {
        let trimmed = spec_body.trim();

        // Literal "true"
        if trimmed == "true" {
            diagnostics.push(GateDiagnostic::reject(
                DiagnosticKind::Tautology,
                "spec is trivially true (literal 'true')",
                trimmed,
            ));
            return;
        }

        // x == x pattern (with whitespace flexibility)
        if is_self_equality(trimmed) {
            diagnostics.push(GateDiagnostic::reject(
                DiagnosticKind::Tautology,
                "spec is a tautology: both sides of == are identical",
                trimmed,
            ));
            return;
        }

        // x >= x or x <= x
        if is_self_reflexive_comparison(trimmed) {
            diagnostics.push(GateDiagnostic::reject(
                DiagnosticKind::Tautology,
                "spec is a tautology: reflexive comparison is always true",
                trimmed,
            ));
            return;
        }

        // x || !x (or !x || x) -- but only simple cases
        if is_or_complement(trimmed) {
            diagnostics.push(GateDiagnostic::reject(
                DiagnosticKind::Tautology,
                "spec is a tautology: disjunction with its own complement",
                trimmed,
            ));
            return;
        }

        // true && X or X && true -- warn but don't reject
        if contains_redundant_true(trimmed) {
            diagnostics.push(GateDiagnostic::warn(
                DiagnosticKind::Tautology,
                "spec contains redundant 'true' conjunct",
                trimmed,
            ));
        }

        // For postconditions, check if spec just says "result == result"
        if matches!(kind, ProposalKind::AddPostcondition { .. })
            && (trimmed == "result == result" || trimmed == "ret == ret")
        {
            diagnostics.push(GateDiagnostic::reject(
                DiagnosticKind::Tautology,
                "postcondition is a tautology on the return value",
                trimmed,
            ));
        }
    }

    fn check_contradiction(
        &self,
        spec_body: &str,
        kind: &ProposalKind,
        diagnostics: &mut Vec<GateDiagnostic>,
    ) {
        let trimmed = spec_body.trim();

        // Literal "false"
        if trimmed == "false" {
            match kind {
                ProposalKind::AddPrecondition { .. } => {
                    diagnostics.push(GateDiagnostic::reject(
                        DiagnosticKind::TrivialWeakening,
                        "requires(false) makes the function unreachable, trivially satisfying \
                         all postconditions -- this weakens, not strengthens, verification",
                        trimmed,
                    ));
                }
                ProposalKind::AddPostcondition { .. } => {
                    diagnostics.push(GateDiagnostic::reject(
                        DiagnosticKind::Contradiction,
                        "ensures(false) is impossible to satisfy -- no implementation can \
                         establish this postcondition",
                        trimmed,
                    ));
                }
                ProposalKind::AddInvariant { .. } => {
                    diagnostics.push(GateDiagnostic::reject(
                        DiagnosticKind::Contradiction,
                        "invariant(false) can never hold -- loop body would need to maintain \
                         an impossible condition",
                        trimmed,
                    ));
                }
                _ => {}
            }
            return;
        }

        // x && !x or !x && x
        if is_and_contradiction(trimmed) {
            diagnostics.push(GateDiagnostic::reject(
                DiagnosticKind::Contradiction,
                "spec is a contradiction: conjunction with its own negation",
                trimmed,
            ));
            return;
        }

        // Check against existing specs for direct contradictions
        for existing in &self.config.existing_specs {
            let existing_trimmed = existing.trim();
            // Direct negation: new spec is !existing or vice versa
            if trimmed == format!("!{existing_trimmed}")
                || trimmed == format!("!({})", existing_trimmed)
                || format!("!{trimmed}") == existing_trimmed
                || format!("!({})", trimmed) == existing_trimmed
            {
                diagnostics.push(GateDiagnostic::reject(
                    DiagnosticKind::Contradiction,
                    format!(
                        "spec contradicts existing spec '{}' (direct negation)",
                        existing_trimmed
                    ),
                    trimmed,
                ));
            }
        }
    }

    fn check_complexity(&self, spec_body: &str, diagnostics: &mut Vec<GateDiagnostic>) {
        let trimmed = spec_body.trim();

        // Length check
        if trimmed.len() > self.config.max_length {
            diagnostics.push(GateDiagnostic::reject(
                DiagnosticKind::ComplexityExceeded,
                format!(
                    "spec body length {} exceeds maximum {}",
                    trimmed.len(),
                    self.config.max_length
                ),
                &trimmed[..trimmed.len().min(80)],
            ));
            return;
        }

        // Operator count check
        let op_count = count_operators(trimmed);
        if op_count > self.config.max_operators {
            diagnostics.push(GateDiagnostic::reject(
                DiagnosticKind::ComplexityExceeded,
                format!(
                    "spec contains {op_count} operators, exceeding maximum {}",
                    self.config.max_operators
                ),
                trimmed,
            ));
        }

        // Nesting depth check
        let depth = max_nesting_depth(trimmed);
        if depth > self.config.max_depth {
            diagnostics.push(GateDiagnostic::reject(
                DiagnosticKind::ComplexityExceeded,
                format!("spec nesting depth {depth} exceeds maximum {}", self.config.max_depth),
                trimmed,
            ));
        }
    }

    fn check_side_effects(&self, spec_body: &str, diagnostics: &mut Vec<GateDiagnostic>) {
        let trimmed = spec_body.trim();

        // Assignment operators
        if contains_assignment(trimmed) {
            diagnostics.push(GateDiagnostic::reject(
                DiagnosticKind::SideEffect,
                "spec contains assignment operator; specs must be pure expressions",
                trimmed,
            ));
        }

        // Mutable references
        if trimmed.contains("&mut ") {
            diagnostics.push(GateDiagnostic::reject(
                DiagnosticKind::SideEffect,
                "spec contains mutable reference; specs must be pure expressions",
                trimmed,
            ));
        }

        // println!, eprintln!, print!, write! -- I/O
        for io_macro in &["println!", "eprintln!", "print!", "write!", "writeln!"] {
            if trimmed.contains(io_macro) {
                diagnostics.push(GateDiagnostic::reject(
                    DiagnosticKind::SideEffect,
                    format!("spec contains I/O macro {}; specs must be pure", io_macro),
                    trimmed,
                ));
            }
        }
    }

    fn check_scope(&self, spec_body: &str, diagnostics: &mut Vec<GateDiagnostic>) {
        if self.config.scope_vars.is_empty() {
            return; // No scope info available, skip
        }

        let identifiers = extract_identifiers(spec_body);
        let scope_names: Vec<&str> =
            self.config.scope_vars.iter().map(|v| v.name.as_str()).collect();

        // Built-in identifiers that are always in scope for specs
        let builtins: &[&str] = &[
            "true", "false", "result", "ret", "old", "self", "usize", "u8", "u16", "u32", "u64",
            "u128", "isize", "i8", "i16", "i32", "i64", "i128", "f32", "f64", "bool", "MAX", "MIN",
            "len",
        ];

        for ident in &identifiers {
            if !scope_names.contains(&ident.as_str())
                && !builtins.contains(&ident.as_str())
                && !is_type_method(ident)
            {
                diagnostics.push(GateDiagnostic::reject(
                    DiagnosticKind::ScopeViolation,
                    format!("identifier '{ident}' is not in scope at the annotation point"),
                    ident,
                ));
            }
        }
    }
}

impl Default for StructuralGate {
    fn default() -> Self {
        Self::new()
    }
}

// --- Helper functions ---

/// Returns true if the proposal kind carries a spec expression (parseable by spec parser).
/// Code-bearing kinds (SafeArithmetic, AddBoundsCheck, AddNonZeroCheck) contain Rust code
/// and should not be validated by the spec parser.
fn is_spec_bearing_kind(kind: &ProposalKind) -> bool {
    matches!(
        kind,
        ProposalKind::AddPrecondition { .. }
            | ProposalKind::AddPostcondition { .. }
            | ProposalKind::AddInvariant { .. }
    )
}

/// Extract the spec body string from a ProposalKind.
fn extract_spec_body(kind: &ProposalKind) -> String {
    match kind {
        ProposalKind::AddPrecondition { spec_body } => spec_body.clone(),
        ProposalKind::AddPostcondition { spec_body } => spec_body.clone(),
        ProposalKind::AddInvariant { spec_body } => spec_body.clone(),
        ProposalKind::SafeArithmetic { replacement, .. } => replacement.clone(),
        ProposalKind::AddBoundsCheck { check_expr } => check_expr.clone(),
        ProposalKind::AddNonZeroCheck { check_expr } => check_expr.clone(),
    }
}

/// Check if an expression is of the form `x == x` (self-equality).
fn is_self_equality(s: &str) -> bool {
    if let Some((left, right)) = split_binary_op(s, "==") {
        return left == right;
    }
    false
}

/// Check if an expression is of the form `x >= x` or `x <= x`.
fn is_self_reflexive_comparison(s: &str) -> bool {
    for op in &[">=", "<="] {
        if let Some((left, right)) = split_binary_op(s, op)
            && left == right
        {
            return true;
        }
    }
    false
}

/// Check if an expression is of the form `x || !x` or `!x || x`.
fn is_or_complement(s: &str) -> bool {
    if let Some((left, right)) = split_binary_op(s, "||") {
        let left = left.trim();
        let right = right.trim();
        if right == format!("!{left}") || left == format!("!{right}") {
            return true;
        }
        // Parenthesized: !(x) || x
        if right == format!("!({})", left) || left == format!("!({})", right) {
            return true;
        }
    }
    false
}

/// Check if an expression is of the form `x && !x` or `!x && x`.
fn is_and_contradiction(s: &str) -> bool {
    if let Some((left, right)) = split_binary_op(s, "&&") {
        let left = left.trim();
        let right = right.trim();
        if right == format!("!{left}") || left == format!("!{right}") {
            return true;
        }
        if right == format!("!({})", left) || left == format!("!({})", right) {
            return true;
        }
    }
    false
}

/// Check if an expression contains redundant `true` in a conjunction.
fn contains_redundant_true(s: &str) -> bool {
    if let Some((left, right)) = split_binary_op(s, "&&") {
        return left.trim() == "true" || right.trim() == "true";
    }
    false
}

/// Split an expression on a binary operator, returning left and right sides.
/// Only splits on the first occurrence that is not inside parentheses.
fn split_binary_op<'a>(s: &'a str, op: &str) -> Option<(&'a str, &'a str)> {
    let mut depth = 0i32;
    let bytes = s.as_bytes();
    let op_bytes = op.as_bytes();
    let op_len = op_bytes.len();

    if bytes.len() < op_len {
        return None;
    }

    let mut i = 0;
    while i <= bytes.len() - op_len {
        match bytes[i] {
            b'(' => depth += 1,
            b')' => depth -= 1,
            _ => {}
        }
        if depth == 0 && &bytes[i..i + op_len] == op_bytes {
            // Ensure we don't match substrings like "!=" when looking for "="
            // or ">=" when looking for ">"
            let before_ok = if i == 0 {
                true
            } else {
                let prev = bytes[i - 1];
                // For "==", ensure previous char is not '!' or '>' or '<'
                if op == "==" { prev != b'!' && prev != b'>' && prev != b'<' } else { true }
            };
            let after_ok = if i + op_len >= bytes.len() {
                true
            } else {
                let next = bytes[i + op_len];
                // For "||", ensure next char is not '|'
                // For "&&", ensure next char is not '&'
                if op == "||" {
                    next != b'|'
                } else if op == "&&" {
                    next != b'&'
                } else if op == "==" {
                    next != b'='
                } else {
                    true
                }
            };
            if before_ok && after_ok {
                let left = s[..i].trim();
                let right = s[i + op_len..].trim();
                if !left.is_empty() && !right.is_empty() {
                    return Some((left, right));
                }
            }
        }
        i += 1;
    }
    None
}

/// Check if a spec body contains a function call pattern.
fn contains_call(s: &str, func_name: &str) -> bool {
    // Match func_name followed by '(' with optional whitespace
    let mut search = func_name.to_string();
    search.push('(');
    if s.contains(&search) {
        return true;
    }
    // Also check with space before paren
    let mut search_space = func_name.to_string();
    search_space.push_str("( ");
    if s.contains(&search_space) {
        return true;
    }
    search_space = func_name.to_string();
    search_space.push_str(" (");
    s.contains(&search_space)
}

/// Check if a string contains an assignment operator (= but not ==, !=, >=, <=).
fn contains_assignment(s: &str) -> bool {
    let bytes = s.as_bytes();
    for i in 0..bytes.len() {
        if bytes[i] == b'=' {
            // Check it's not part of ==, !=, >=, <=, =>
            let prev = if i > 0 { Some(bytes[i - 1]) } else { None };
            let next = if i + 1 < bytes.len() { Some(bytes[i + 1]) } else { None };

            let is_comparison = matches!(prev, Some(b'!' | b'>' | b'<' | b'='))
                || matches!(next, Some(b'=' | b'>'));

            if !is_comparison {
                return true;
            }
        }
    }
    false
}

/// Count operators in an expression string.
fn count_operators(s: &str) -> usize {
    let mut count = 0;
    let ops = ["&&", "||", "==", "!=", ">=", "<=", ">>", "<<"];
    let single_ops = ['<', '>', '+', '-', '*', '/', '%', '!', '&', '|', '^'];

    // Count two-character operators
    for op in &ops {
        count += s.matches(op).count();
    }

    // Count single-character operators, excluding those already counted as part of two-char ops
    let bytes = s.as_bytes();
    for i in 0..bytes.len() {
        let ch = bytes[i] as char;
        if single_ops.contains(&ch) {
            // Skip if part of a two-character operator
            let prev = if i > 0 { Some(bytes[i - 1] as char) } else { None };
            let next = if i + 1 < bytes.len() { Some(bytes[i + 1] as char) } else { None };

            let is_double = match ch {
                '&' => matches!(prev, Some('&')) || matches!(next, Some('&')),
                '|' => matches!(prev, Some('|')) || matches!(next, Some('|')),
                '=' => matches!(prev, Some('=' | '!' | '>' | '<')) || matches!(next, Some('=')),
                '<' => matches!(next, Some('=' | '<')),
                '>' => matches!(next, Some('=' | '>')) || matches!(prev, Some('>')),
                _ => false,
            };

            if !is_double {
                count += 1;
            }
        }
    }

    count
}

/// Calculate maximum nesting depth (parentheses).
fn max_nesting_depth(s: &str) -> usize {
    let mut max_depth: usize = 0;
    let mut current: usize = 0;
    for ch in s.chars() {
        if ch == '(' {
            current += 1;
            max_depth = max_depth.max(current);
        } else if ch == ')' {
            current = current.saturating_sub(1);
        }
    }
    max_depth
}

/// Extract identifiers from a spec body string (simple heuristic).
fn extract_identifiers(s: &str) -> Vec<String> {
    let mut identifiers = Vec::new();
    let mut current = String::new();

    for ch in s.chars() {
        if ch.is_alphanumeric() || ch == '_' {
            current.push(ch);
        } else {
            if !current.is_empty()
                && current.chars().next().is_some_and(|c| c.is_alphabetic() || c == '_')
            {
                identifiers.push(current.clone());
            }
            current.clear();
        }
    }
    if !current.is_empty() && current.chars().next().is_some_and(|c| c.is_alphabetic() || c == '_')
    {
        identifiers.push(current);
    }

    identifiers
}

/// Check if an identifier looks like a type method (e.g., checked_add, try_from).
fn is_type_method(ident: &str) -> bool {
    let known_methods = [
        "checked_add",
        "checked_sub",
        "checked_mul",
        "checked_div",
        "checked_neg",
        "checked_shl",
        "checked_shr",
        "saturating_add",
        "saturating_sub",
        "saturating_mul",
        "wrapping_add",
        "wrapping_sub",
        "wrapping_mul",
        "try_from",
        "try_into",
        "expect",
        "unwrap",
        "len",
        "is_empty",
        "contains",
        "size_of",
    ];
    known_methods.contains(&ident)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::proposer::{Proposal, ProposalKind};

    fn make_precondition(spec: &str) -> Proposal {
        Proposal {
            function_path: "test::func".into(),
            function_name: "func".into(),
            kind: ProposalKind::AddPrecondition { spec_body: spec.into() },
            confidence: 0.8,
            rationale: "test".into(),
        }
    }

    fn make_postcondition(spec: &str) -> Proposal {
        Proposal {
            function_path: "test::func".into(),
            function_name: "func".into(),
            kind: ProposalKind::AddPostcondition { spec_body: spec.into() },
            confidence: 0.8,
            rationale: "test".into(),
        }
    }

    fn make_invariant(spec: &str) -> Proposal {
        Proposal {
            function_path: "test::func".into(),
            function_name: "func".into(),
            kind: ProposalKind::AddInvariant { spec_body: spec.into() },
            confidence: 0.8,
            rationale: "test".into(),
        }
    }

    // --- Empty spec tests ---

    #[test]
    fn test_gate_rejects_empty_spec() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition(""));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::EmptySpec));
    }

    #[test]
    fn test_gate_rejects_whitespace_only_spec() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("   \t\n  "));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::EmptySpec));
    }

    // --- Syntax validation tests ---

    #[test]
    fn test_gate_rejects_unbalanced_parens_open() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("((x + y)"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::SyntaxError));
    }

    #[test]
    fn test_gate_rejects_unbalanced_parens_close() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("(x + y))"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::SyntaxError));
    }

    #[test]
    fn test_gate_rejects_semicolons() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("x > 0; y > 0"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::SyntaxError));
    }

    #[test]
    fn test_gate_rejects_curly_braces() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("{ x > 0 }"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::SyntaxError));
    }

    #[test]
    fn test_gate_rejects_unbalanced_brackets() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("arr[0"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::SyntaxError));
    }

    #[test]
    fn test_gate_accepts_balanced_parens() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("(x + y) > 0"));
        // Should not have syntax errors (may have other warnings)
        assert!(!result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::SyntaxError));
    }

    // --- Unsafe content tests ---

    #[test]
    fn test_gate_rejects_assume_false() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("assume(false)"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::Unsoundness));
    }

    #[test]
    fn test_gate_rejects_panic() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("panic!(\"bad\")"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::UnsafeContent));
    }

    #[test]
    fn test_gate_rejects_unreachable() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("unreachable!()"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::UnsafeContent));
    }

    #[test]
    fn test_gate_rejects_todo() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("todo!()"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::UnsafeContent));
    }

    #[test]
    fn test_gate_rejects_unimplemented() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("unimplemented!()"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::UnsafeContent));
    }

    #[test]
    fn test_gate_rejects_unsafe_keyword() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("unsafe { *ptr }"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::UnsafeContent));
    }

    #[test]
    fn test_gate_rejects_process_exit() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("process::exit(1)"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::UnsafeContent));
    }

    #[test]
    fn test_gate_rejects_trusted_attribute() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("#[trusted]"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::UnsafeContent));
    }

    // --- Tautology tests ---

    #[test]
    fn test_gate_rejects_literal_true() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("true"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::Tautology));
    }

    #[test]
    fn test_gate_rejects_self_equality() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("x == x"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::Tautology));
    }

    #[test]
    fn test_gate_rejects_self_ge() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("x >= x"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::Tautology));
    }

    #[test]
    fn test_gate_rejects_self_le() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("x <= x"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::Tautology));
    }

    #[test]
    fn test_gate_rejects_or_complement() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("x || !x"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::Tautology));
    }

    #[test]
    fn test_gate_warns_redundant_true() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("true && x > 0"));
        // Should pass (warning, not rejection)
        assert!(result.passed);
        assert!(
            result
                .diagnostics
                .iter()
                .any(|d| { d.kind == DiagnosticKind::Tautology && d.severity == Severity::Warn })
        );
    }

    #[test]
    fn test_gate_rejects_result_self_equality_postcondition() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_postcondition("result == result"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::Tautology));
    }

    // --- Contradiction / trivial weakening tests ---

    #[test]
    fn test_gate_rejects_requires_false() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("false"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::TrivialWeakening));
    }

    #[test]
    fn test_gate_rejects_ensures_false() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_postcondition("false"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::Contradiction));
    }

    #[test]
    fn test_gate_rejects_invariant_false() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_invariant("false"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::Contradiction));
    }

    #[test]
    fn test_gate_rejects_and_contradiction() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("x && !x"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::Contradiction));
    }

    #[test]
    fn test_gate_rejects_contradiction_with_existing_spec() {
        let config = GateConfig { existing_specs: vec!["x > 0".to_string()], ..Default::default() };
        let gate = StructuralGate::with_config(config);
        let result = gate.check(&make_precondition("!(x > 0)"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::Contradiction));
    }

    // --- Complexity tests ---

    #[test]
    fn test_gate_rejects_too_long_spec() {
        let config = GateConfig { max_length: 20, ..Default::default() };
        let gate = StructuralGate::with_config(config);
        let result = gate.check(&make_precondition("very_long_variable_name > another_long_name"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::ComplexityExceeded));
    }

    #[test]
    fn test_gate_rejects_too_many_operators() {
        let config = GateConfig { max_operators: 2, ..Default::default() };
        let gate = StructuralGate::with_config(config);
        let result = gate.check(&make_precondition("a > 0 && b > 0 && c > 0"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::ComplexityExceeded));
    }

    #[test]
    fn test_gate_rejects_too_deep_nesting() {
        let config = GateConfig { max_depth: 2, ..Default::default() };
        let gate = StructuralGate::with_config(config);
        let result = gate.check(&make_precondition("(((x > 0)))"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::ComplexityExceeded));
    }

    #[test]
    fn test_gate_accepts_within_complexity_bounds() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("x > 0 && y > 0"));
        // Should not have complexity issues
        assert!(!result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::ComplexityExceeded));
    }

    // --- Side effect tests ---

    #[test]
    fn test_gate_rejects_assignment() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("x = 5"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::SideEffect));
    }

    #[test]
    fn test_gate_accepts_equality_comparison() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("x == 5"));
        // Should not flag as side effect
        assert!(!result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::SideEffect));
    }

    #[test]
    fn test_gate_accepts_not_equal_comparison() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("x != 0"));
        assert!(!result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::SideEffect));
    }

    #[test]
    fn test_gate_rejects_mutable_reference() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("&mut x"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::SideEffect));
    }

    #[test]
    fn test_gate_rejects_println() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("println!(\"test\")"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::SideEffect));
    }

    // --- Scope tests ---

    #[test]
    fn test_gate_rejects_out_of_scope_variable() {
        let config = GateConfig {
            scope_vars: vec![ScopedVar::new("x", "u64"), ScopedVar::new("y", "u64")],
            ..Default::default()
        };
        let gate = StructuralGate::with_config(config);
        let result = gate.check(&make_precondition("z > 0"));
        assert!(!result.passed);
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::ScopeViolation));
    }

    #[test]
    fn test_gate_accepts_in_scope_variables() {
        let config = GateConfig {
            scope_vars: vec![ScopedVar::new("x", "u64"), ScopedVar::new("y", "u64")],
            ..Default::default()
        };
        let gate = StructuralGate::with_config(config);
        let result = gate.check(&make_precondition("x > y"));
        // Should not have scope violations
        assert!(!result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::ScopeViolation));
    }

    #[test]
    fn test_gate_allows_builtins_in_scope() {
        let config =
            GateConfig { scope_vars: vec![ScopedVar::new("x", "u64")], ..Default::default() };
        let gate = StructuralGate::with_config(config);
        let result = gate.check(&make_precondition("x < u64::MAX"));
        // "u64" and "MAX" are builtins
        assert!(!result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::ScopeViolation));
    }

    #[test]
    fn test_gate_skips_scope_when_no_vars() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("any_var > 0"));
        // No scope info, so no scope violations
        assert!(!result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::ScopeViolation));
    }

    // --- Integration tests ---

    #[test]
    fn test_gate_accepts_valid_precondition() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("x != 0"));
        assert!(result.passed);
        assert_eq!(result.rejection_count(), 0);
    }

    #[test]
    fn test_gate_accepts_valid_postcondition() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_postcondition("result > 0"));
        assert!(result.passed);
        assert_eq!(result.rejection_count(), 0);
    }

    #[test]
    fn test_gate_accepts_valid_invariant() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_invariant("i < n"));
        assert!(result.passed);
        assert_eq!(result.rejection_count(), 0);
    }

    #[test]
    fn test_gate_accepts_complex_valid_spec() {
        let gate = StructuralGate::new();
        // Use a parseable spec expression (parser does not support :: paths)
        let result = gate.check(&make_precondition("a + b >= a && a + b >= b"));
        assert!(result.passed);
        assert_eq!(result.rejection_count(), 0);
    }

    #[test]
    fn test_gate_check_all() {
        let gate = StructuralGate::new();
        let proposals = vec![
            make_precondition("x > 0"),
            make_precondition("true"), // tautology
            make_precondition("y != 0"),
        ];
        let results = gate.check_all(&proposals);
        assert_eq!(results.len(), 3);
        assert!(results[0].passed);
        assert!(!results[1].passed);
        assert!(results[2].passed);
    }

    #[test]
    fn test_gate_filter() {
        let gate = StructuralGate::new();
        let proposals = vec![
            make_precondition("x > 0"),
            make_precondition("true"),          // tautology -- rejected
            make_precondition("assume(false)"), // unsound -- rejected
            make_precondition("y != 0"),
        ];
        let filtered = gate.filter(proposals);
        assert_eq!(filtered.len(), 2);
    }

    #[test]
    fn test_gate_strict_mode_rejects_warnings() {
        let config = GateConfig { strict_mode: true, ..Default::default() };
        let gate = StructuralGate::with_config(config);
        let result = gate.check(&make_precondition("true && x > 0"));
        // In strict mode, the redundant-true warning becomes a rejection
        assert!(!result.passed);
    }

    #[test]
    fn test_gate_multiple_diagnostics_per_proposal() {
        let gate = StructuralGate::new();
        // This has both unsafe content AND side effect issues
        let result = gate.check(&make_precondition("panic!(\"oops\")"));
        assert!(!result.passed);
        // Should have at least UnsafeContent
        assert!(result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::UnsafeContent));
    }

    #[test]
    fn test_gate_result_function_name() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("x > 0"));
        assert_eq!(result.function_name, "func");
    }

    #[test]
    fn test_gate_result_spec_body() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("x > 0"));
        assert_eq!(result.spec_body, "x > 0");
    }

    #[test]
    fn test_gate_diagnostics_have_suggestions() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("true"));
        // Tautology diagnostic should have a fix suggestion
        let taut = result.diagnostics.iter().find(|d| d.kind == DiagnosticKind::Tautology);
        assert!(taut.is_some());
        assert!(taut.is_some_and(|d| d.suggestion.is_some()));
    }

    #[test]
    fn test_gate_safe_arithmetic_proposal() {
        let gate = StructuralGate::new();
        let proposal = Proposal {
            function_path: "test::func".into(),
            function_name: "func".into(),
            kind: ProposalKind::SafeArithmetic {
                original: "a + b".into(),
                replacement: "a.checked_add(b).expect(\"overflow\")".into(),
            },
            confidence: 0.75,
            rationale: "test".into(),
        };
        let result = gate.check(&proposal);
        assert!(result.passed);
    }

    #[test]
    fn test_gate_bounds_check_proposal() {
        let gate = StructuralGate::new();
        let proposal = Proposal {
            function_path: "test::func".into(),
            function_name: "func".into(),
            kind: ProposalKind::AddBoundsCheck {
                check_expr: "assert!(i < arr.len(), \"oob\")".into(),
            },
            confidence: 0.8,
            rationale: "test".into(),
        };
        let result = gate.check(&proposal);
        // bounds check may have syntax issues (contains ! for assert!) but
        // the check_expr pattern is acceptable for bounds checks
        assert_eq!(result.function_name, "func");
    }

    // --- Helper function tests ---

    #[test]
    fn test_split_binary_op_simple() {
        let result = split_binary_op("x == y", "==");
        assert_eq!(result, Some(("x", "y")));
    }

    #[test]
    fn test_split_binary_op_with_spaces() {
        let result = split_binary_op("x  ==  y", "==");
        assert_eq!(result, Some(("x", "y")));
    }

    #[test]
    fn test_split_binary_op_nested_parens() {
        let result = split_binary_op("(a + b) == (c + d)", "==");
        assert_eq!(result, Some(("(a + b)", "(c + d)")));
    }

    #[test]
    fn test_split_binary_op_not_found() {
        let result = split_binary_op("x > y", "==");
        assert!(result.is_none());
    }

    #[test]
    fn test_count_operators_simple() {
        assert_eq!(count_operators("x > 0"), 1);
    }

    #[test]
    fn test_count_operators_compound() {
        let count = count_operators("a > 0 && b > 0");
        assert!(count >= 3); // >, &&, >
    }

    #[test]
    fn test_max_nesting_depth_flat() {
        assert_eq!(max_nesting_depth("x > 0"), 0);
    }

    #[test]
    fn test_max_nesting_depth_nested() {
        assert_eq!(max_nesting_depth("((x))"), 2);
    }

    #[test]
    fn test_max_nesting_depth_three() {
        assert_eq!(max_nesting_depth("(((x)))"), 3);
    }

    #[test]
    fn test_extract_identifiers_simple() {
        let ids = extract_identifiers("x > 0");
        assert!(ids.contains(&"x".to_string()));
    }

    #[test]
    fn test_extract_identifiers_multiple() {
        let ids = extract_identifiers("x > y && z != 0");
        assert!(ids.contains(&"x".to_string()));
        assert!(ids.contains(&"y".to_string()));
        assert!(ids.contains(&"z".to_string()));
    }

    #[test]
    fn test_contains_assignment_true() {
        assert!(contains_assignment("x = 5"));
    }

    #[test]
    fn test_contains_assignment_false_for_eq() {
        assert!(!contains_assignment("x == 5"));
    }

    #[test]
    fn test_contains_assignment_false_for_ne() {
        assert!(!contains_assignment("x != 5"));
    }

    #[test]
    fn test_contains_assignment_false_for_ge() {
        assert!(!contains_assignment("x >= 5"));
    }

    #[test]
    fn test_contains_assignment_false_for_le() {
        assert!(!contains_assignment("x <= 5"));
    }

    #[test]
    fn test_is_type_method() {
        assert!(is_type_method("checked_add"));
        assert!(is_type_method("len"));
        assert!(!is_type_method("my_func"));
    }

    #[test]
    fn test_gate_default_impl() {
        let gate = StructuralGate::default();
        let result = gate.check(&make_precondition("x > 0"));
        assert!(result.passed);
    }

    // --- Parser integration tests (issue #142) ---

    #[test]
    fn test_parser_rejects_unparseable_precondition() {
        let gate = StructuralGate::new();
        // "@@invalid" is not a valid spec expression
        let result = gate.check(&make_precondition("@@invalid"));
        assert!(!result.passed);
        assert!(
            result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::SyntaxError),
            "should produce SyntaxError for unparseable spec"
        );
    }

    #[test]
    fn test_parser_rejects_natural_language_spec() {
        let gate = StructuralGate::new();
        // Natural-language spec that LLMs sometimes produce
        let result = gate.check(&make_precondition("addition does not overflow"));
        assert!(!result.passed);
        assert!(
            result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::SyntaxError),
            "should reject natural-language specs via parser"
        );
    }

    #[test]
    fn test_parser_accepts_simple_comparison() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("x > 0"));
        assert!(result.passed);
        assert_eq!(result.rejection_count(), 0);
    }

    #[test]
    fn test_parser_accepts_boolean_conjunction() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("x > 0 && y != 0"));
        assert!(result.passed);
        assert_eq!(result.rejection_count(), 0);
    }

    #[test]
    fn test_parser_accepts_arithmetic_in_spec() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("a + b > a"));
        assert!(result.passed);
        assert_eq!(result.rejection_count(), 0);
    }

    #[test]
    fn test_parser_accepts_negation_spec() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("!(x == 0)"));
        assert!(result.passed);
        assert_eq!(result.rejection_count(), 0);
    }

    #[test]
    fn test_parser_accepts_implication_spec() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_precondition("x > 0 => y > 0"));
        assert!(result.passed);
        assert_eq!(result.rejection_count(), 0);
    }

    #[test]
    fn test_parser_accepts_postcondition() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_postcondition("result > 0"));
        assert!(result.passed);
        assert_eq!(result.rejection_count(), 0);
    }

    #[test]
    fn test_parser_accepts_invariant() {
        let gate = StructuralGate::new();
        let result = gate.check(&make_invariant("i < n"));
        assert!(result.passed);
        assert_eq!(result.rejection_count(), 0);
    }

    #[test]
    fn test_parser_skips_safe_arithmetic_kind() {
        let gate = StructuralGate::new();
        // SafeArithmetic contains Rust code, not spec expressions.
        // The parser should not be applied to it.
        let proposal = Proposal {
            function_path: "test::func".into(),
            function_name: "func".into(),
            kind: ProposalKind::SafeArithmetic {
                original: "a + b".into(),
                replacement: "a.checked_add(b).expect(\"overflow\")".into(),
            },
            confidence: 0.75,
            rationale: "test".into(),
        };
        let result = gate.check(&proposal);
        // Should not get a parser SyntaxError (Rust code is not spec expr)
        assert!(
            !result.diagnostics.iter().any(|d| {
                d.kind == DiagnosticKind::SyntaxError && d.message.contains("failed to parse")
            }),
            "parser should not be applied to SafeArithmetic proposals"
        );
    }

    #[test]
    fn test_parser_skips_bounds_check_kind() {
        let gate = StructuralGate::new();
        let proposal = Proposal {
            function_path: "test::func".into(),
            function_name: "func".into(),
            kind: ProposalKind::AddBoundsCheck {
                check_expr: "assert!(i < arr.len(), \"oob\")".into(),
            },
            confidence: 0.8,
            rationale: "test".into(),
        };
        let result = gate.check(&proposal);
        // Should not get a parser-based SyntaxError
        assert!(
            !result.diagnostics.iter().any(|d| {
                d.kind == DiagnosticKind::SyntaxError && d.message.contains("failed to parse")
            }),
            "parser should not be applied to AddBoundsCheck proposals"
        );
    }

    #[test]
    fn test_parser_skips_non_zero_check_kind() {
        let gate = StructuralGate::new();
        let proposal = Proposal {
            function_path: "test::func".into(),
            function_name: "func".into(),
            kind: ProposalKind::AddNonZeroCheck {
                check_expr: "assert!(divisor != 0, \"division by zero\")".into(),
            },
            confidence: 0.8,
            rationale: "test".into(),
        };
        let result = gate.check(&proposal);
        assert!(
            !result.diagnostics.iter().any(|d| {
                d.kind == DiagnosticKind::SyntaxError && d.message.contains("failed to parse")
            }),
            "parser should not be applied to AddNonZeroCheck proposals"
        );
    }

    #[test]
    fn test_parser_rejects_trailing_tokens() {
        let gate = StructuralGate::new();
        // "x > 0 y" has trailing token "y" after a complete expression
        let result = gate.check(&make_precondition("x > 0 y"));
        assert!(!result.passed);
        assert!(
            result.diagnostics.iter().any(|d| d.kind == DiagnosticKind::SyntaxError),
            "should reject spec with trailing tokens"
        );
    }

    #[test]
    fn test_is_spec_bearing_kind_classification() {
        assert!(is_spec_bearing_kind(&ProposalKind::AddPrecondition { spec_body: String::new() }));
        assert!(is_spec_bearing_kind(&ProposalKind::AddPostcondition { spec_body: String::new() }));
        assert!(is_spec_bearing_kind(&ProposalKind::AddInvariant { spec_body: String::new() }));
        assert!(!is_spec_bearing_kind(&ProposalKind::SafeArithmetic {
            original: String::new(),
            replacement: String::new(),
        }));
        assert!(!is_spec_bearing_kind(&ProposalKind::AddBoundsCheck { check_expr: String::new() }));
        assert!(!is_spec_bearing_kind(&ProposalKind::AddNonZeroCheck {
            check_expr: String::new()
        }));
    }
}
