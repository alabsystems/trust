// trust_vcgen/vc_simplifier.rs: Multi-pass VC simplification pipeline
//
// Reduces verification condition size before sending to solvers.
// Operates on textual VC representations (SMT-LIB2-style strings) for
// interoperability with external tools and solver frontends.
//
// Complements simplify.rs (which operates on Formula AST) by providing
// a string-level pipeline with configurable passes, statistics tracking,
// and tautology/contradiction detection.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

// ---------------------------------------------------------------------------
// VcSimplificationPass enum
// ---------------------------------------------------------------------------

/// Available simplification passes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum VcSimplificationPass {
    /// Evaluate constant sub-expressions (e.g., `(+ 1 2)` -> `3`).
    ConstantFolding,
    /// Remove bindings for variables not referenced in the body.
    DeadVariableElimination,
    /// Remove duplicate or subsumed constraints from conjunctions.
    RedundantConstraintRemoval,
    /// Simplify chains of implications (A => B => C).
    ImpliesChainSimplification,
    /// Detect and share repeated sub-expressions.
    CommonSubexprElimination,
    /// Propagate known truth values (true, false) through formulas.
    TruthValuePropagation,
}

// ---------------------------------------------------------------------------
// SimplificationConfig
// ---------------------------------------------------------------------------

/// Configuration for the simplification pipeline.
#[derive(Debug, Clone)]
pub struct SimplificationConfig {
    /// Ordered list of passes to apply.
    pub passes: Vec<VcSimplificationPass>,
    /// Maximum fixed-point iterations before stopping.
    pub max_iterations: usize,
    /// Whether to collect detailed statistics.
    pub enable_stats: bool,
}

impl Default for SimplificationConfig {
    fn default() -> Self {
        VcSimplifier::default_config()
    }
}

// ---------------------------------------------------------------------------
// SimplificationStats
// ---------------------------------------------------------------------------

/// Statistics gathered during simplification.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SimplificationStats {
    /// Size of the input VC (token count).
    pub original_size: usize,
    /// Size after simplification.
    pub simplified_size: usize,
    /// Number of pass iterations applied.
    pub passes_applied: usize,
    /// Constants folded during ConstantFolding.
    pub constants_folded: usize,
    /// Dead variables eliminated.
    pub dead_vars_eliminated: usize,
    /// Redundant constraints removed.
    pub redundant_removed: usize,
}

impl SimplificationStats {
    /// Reduction ratio (0.0 = no reduction, 1.0 = fully eliminated).
    #[must_use]
    pub fn reduction_ratio(&self) -> f64 {
        if self.original_size == 0 {
            return 0.0;
        }
        1.0 - (self.simplified_size as f64 / self.original_size as f64)
    }
}

// ---------------------------------------------------------------------------
// SimplifiedVc
// ---------------------------------------------------------------------------

/// Result of VC simplification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SimplifiedVc {
    /// The simplified formula string.
    pub formula: String,
    /// Statistics from the simplification process.
    pub stats: SimplificationStats,
    /// Whether the formula is trivially true (tautology).
    pub is_trivially_true: bool,
}

// ---------------------------------------------------------------------------
// VcSimplifier
// ---------------------------------------------------------------------------

/// Multi-pass verification condition simplifier.
///
/// Applies a configurable sequence of passes to reduce VC size before
/// dispatch to solvers. Operates on string-level VC representations.
pub struct VcSimplifier {
    config: SimplificationConfig,
    stats: SimplificationStats,
}

impl VcSimplifier {
    /// Create a simplifier with the given configuration.
    #[must_use]
    pub fn new(config: SimplificationConfig) -> Self {
        Self { config, stats: SimplificationStats::default() }
    }

    /// Standard pass ordering for general use.
    #[must_use]
    pub fn default_config() -> SimplificationConfig {
        SimplificationConfig {
            passes: vec![
                VcSimplificationPass::ConstantFolding,
                VcSimplificationPass::TruthValuePropagation,
                VcSimplificationPass::DeadVariableElimination,
                VcSimplificationPass::RedundantConstraintRemoval,
                VcSimplificationPass::ImpliesChainSimplification,
                VcSimplificationPass::CommonSubexprElimination,
            ],
            max_iterations: 10,
            enable_stats: true,
        }
    }

    /// Simplify a verification condition string.
    ///
    /// Runs all configured passes in order, iterating until fixed point
    /// (no size change) or `max_iterations` is reached.
    #[must_use]
    pub fn simplify(&mut self, vc: &str) -> SimplifiedVc {
        let original_size = expression_size(vc);
        self.stats = SimplificationStats { original_size, ..Default::default() };

        let mut current = vc.to_string();
        let mut iteration = 0;

        let passes = self.config.passes.clone();
        for _ in 0..self.config.max_iterations {
            let before_size = expression_size(&current);
            for pass in &passes {
                current = self.apply_pass(&current, pass);
            }
            iteration += 1;
            let after_size = expression_size(&current);
            if after_size >= before_size {
                break;
            }
        }

        let simplified_size = expression_size(&current);
        self.stats.simplified_size = simplified_size;
        self.stats.passes_applied = iteration;

        let is_trivially_true = is_tautology(&current);

        SimplifiedVc { formula: current, stats: self.stats.clone(), is_trivially_true }
    }

    /// Apply a single simplification pass.
    #[must_use]
    pub fn apply_pass(&mut self, vc: &str, pass: &VcSimplificationPass) -> String {
        match pass {
            VcSimplificationPass::ConstantFolding => self.fold_constants(vc),
            VcSimplificationPass::DeadVariableElimination => {
                // Collect all variable references and pass to eliminator
                let live: Vec<&str> = extract_variable_names(vc);
                self.eliminate_dead_vars(vc, &live)
            }
            VcSimplificationPass::RedundantConstraintRemoval => {
                let constraints = extract_constraints(vc);
                let reduced = self.remove_redundant(&constraints);
                if reduced.len() < constraints.len() {
                    if self.config.enable_stats {
                        self.stats.redundant_removed += constraints.len() - reduced.len();
                    }
                    rejoin_constraints(&reduced)
                } else {
                    vc.to_string()
                }
            }
            VcSimplificationPass::ImpliesChainSimplification => {
                let chain = extract_implies_chain(vc);
                if chain.len() > 1 { self.simplify_implies_chain(&chain) } else { vc.to_string() }
            }
            VcSimplificationPass::CommonSubexprElimination => eliminate_common_subexprs(vc),
            VcSimplificationPass::TruthValuePropagation => propagate_truth_values(vc),
        }
    }

    /// Fold constant expressions in the VC string.
    ///
    /// Evaluates sub-expressions like `(and true P)` -> `P`,
    /// `(or false P)` -> `P`, `(not true)` -> `false`, arithmetic
    /// on integer literals, etc.
    ///
    /// Also applies:
    /// - Double negation: `(not (not P))` -> `P`
    /// - Identity removal: `(and P)` -> `P`, `(or P)` -> `P`
    /// - Reflexive equality: `(= x x)` -> `true`
    /// - Contradiction detection: `(and ... P ... (not P) ...)` -> `false`
    /// - Tautology detection: `(or ... P ... (not P) ...)` -> `true`
    #[must_use]
    pub fn fold_constants(&mut self, expr: &str) -> String {
        let trimmed = expr.trim();

        // Boolean constants: (not true) -> false, (not false) -> true
        if trimmed == "(not true)" {
            if self.config.enable_stats {
                self.stats.constants_folded += 1;
            }
            return "false".to_string();
        }
        if trimmed == "(not false)" {
            if self.config.enable_stats {
                self.stats.constants_folded += 1;
            }
            return "true".to_string();
        }

        // Double negation: (not (not P)) -> P
        if let Some(inner) = trimmed.strip_prefix("(not ").and_then(|s| s.strip_suffix(')')) {
            let inner = inner.trim();
            if let Some(double_inner) =
                inner.strip_prefix("(not ").and_then(|s| s.strip_suffix(')'))
            {
                if self.config.enable_stats {
                    self.stats.constants_folded += 1;
                }
                return double_inner.trim().to_string();
            }
        }

        // And/Or with boolean constants, identity removal, and contradiction detection
        if let Some(inner) = trimmed.strip_prefix("(and ").and_then(|s| s.strip_suffix(')')) {
            let parts = split_sexp_args(inner);

            // Short-circuit on false
            if parts.iter().any(|p| p.trim() == "false") {
                if self.config.enable_stats {
                    self.stats.constants_folded += 1;
                }
                return "false".to_string();
            }

            // Contradiction detection: And([..., P, ..., (not P), ...]) -> false
            if has_contradiction(&parts) {
                if self.config.enable_stats {
                    self.stats.constants_folded += 1;
                }
                return "false".to_string();
            }

            // Filter out true constants
            let filtered: Vec<&str> =
                parts.iter().filter(|p| p.trim() != "true").copied().collect();
            if filtered.len() < parts.len() {
                if self.config.enable_stats {
                    self.stats.constants_folded += parts.len() - filtered.len();
                }
                return match filtered.len() {
                    0 => "true".to_string(),
                    1 => filtered[0].to_string(),
                    _ => format!("(and {})", filtered.join(" ")),
                };
            }

            // Identity removal: (and P) -> P (singleton unwrap)
            if parts.len() == 1 {
                return parts[0].to_string();
            }
        }

        if let Some(inner) = trimmed.strip_prefix("(or ").and_then(|s| s.strip_suffix(')')) {
            let parts = split_sexp_args(inner);

            // Short-circuit on true
            if parts.iter().any(|p| p.trim() == "true") {
                if self.config.enable_stats {
                    self.stats.constants_folded += 1;
                }
                return "true".to_string();
            }

            // Tautology detection: Or([..., P, ..., (not P), ...]) -> true
            if has_contradiction(&parts) {
                // same check: if P and (not P) both appear, Or is a tautology
                if self.config.enable_stats {
                    self.stats.constants_folded += 1;
                }
                return "true".to_string();
            }

            // Filter out false constants
            let filtered: Vec<&str> =
                parts.iter().filter(|p| p.trim() != "false").copied().collect();
            if filtered.len() < parts.len() {
                if self.config.enable_stats {
                    self.stats.constants_folded += parts.len() - filtered.len();
                }
                return match filtered.len() {
                    0 => "false".to_string(),
                    1 => filtered[0].to_string(),
                    _ => format!("(or {})", filtered.join(" ")),
                };
            }

            // Identity removal: (or P) -> P (singleton unwrap)
            if parts.len() == 1 {
                return parts[0].to_string();
            }
        }

        // Implies with boolean constants
        if let Some(inner) = trimmed.strip_prefix("(=> ").and_then(|s| s.strip_suffix(')')) {
            let parts = split_sexp_args(inner);
            if parts.len() == 2 {
                if parts[0].trim() == "false" || parts[1].trim() == "true" {
                    if self.config.enable_stats {
                        self.stats.constants_folded += 1;
                    }
                    return "true".to_string();
                }
                if parts[0].trim() == "true" {
                    if self.config.enable_stats {
                        self.stats.constants_folded += 1;
                    }
                    return parts[1].to_string();
                }
            }
        }

        // Reflexive equality: (= x x) -> true
        if let Some(inner) = trimmed.strip_prefix("(= ").and_then(|s| s.strip_suffix(')')) {
            let parts = split_sexp_args(inner);
            if parts.len() == 2 && parts[0].trim() == parts[1].trim() {
                if self.config.enable_stats {
                    self.stats.constants_folded += 1;
                }
                return "true".to_string();
            }
        }

        // Integer arithmetic on literals
        if let Some(result) = try_fold_arithmetic(trimmed) {
            if self.config.enable_stats {
                self.stats.constants_folded += 1;
            }
            return result;
        }

        trimmed.to_string()
    }

    /// Remove bindings for dead variables.
    ///
    /// Given a VC and a set of live variable names, removes quantifier
    /// bindings that are not referenced.
    #[must_use]
    pub fn eliminate_dead_vars(&mut self, vc: &str, live_vars: &[&str]) -> String {
        let trimmed = vc.trim();
        let live_set: FxHashSet<&str> = live_vars.iter().copied().collect();

        // Handle (forall (...) body) and (exists (...) body) patterns
        for quantifier in &["forall", "exists"] {
            let prefix = format!("({quantifier} (");
            if let Some(rest) = trimmed.strip_prefix(prefix.as_str())
                && let Some(paren_end) = find_matching_paren(rest)
            {
                let bindings_str = &rest[..paren_end];
                let body = rest[paren_end + 1..].trim();
                let body = body.strip_suffix(')').unwrap_or(body);

                let binding_pairs = parse_bindings(bindings_str);
                let body_vars: FxHashSet<&str> = extract_variable_names(body).into_iter().collect();

                let mut eliminated = 0usize;
                let kept: Vec<String> = binding_pairs
                    .into_iter()
                    .filter(|(name, _)| {
                        let keep =
                            body_vars.contains(name.as_str()) || live_set.contains(name.as_str());
                        if !keep {
                            eliminated += 1;
                        }
                        keep
                    })
                    .map(|(name, sort)| format!("({name} {sort})"))
                    .collect();

                if self.config.enable_stats {
                    self.stats.dead_vars_eliminated += eliminated;
                }

                return if kept.is_empty() {
                    body.to_string()
                } else {
                    format!("({quantifier} ({}) {body})", kept.join(" "))
                };
            }
        }

        trimmed.to_string()
    }

    /// Remove redundant constraints from a conjunction.
    ///
    /// Eliminates exact duplicates and constraints subsumed by others.
    #[must_use]
    pub fn remove_redundant(&self, constraints: &[String]) -> Vec<String> {
        let mut seen: FxHashSet<String> = FxHashSet::default();
        let mut result = Vec::new();

        for c in constraints {
            let normalized = c.trim().to_string();
            if normalized.is_empty() || normalized == "true" {
                continue;
            }
            if seen.insert(normalized.clone()) {
                result.push(normalized);
            }
        }

        result
    }

    /// Simplify a chain of implications.
    ///
    /// Given [A, B, C] representing (A => (B => C)), simplifies to
    /// `(=> (and A B) C)` when the chain length >= 2.
    #[must_use]
    pub fn simplify_implies_chain(&self, chain: &[String]) -> String {
        if chain.is_empty() {
            return "true".to_string();
        }
        if chain.len() == 1 {
            return chain[0].clone();
        }

        let conclusion = &chain[chain.len() - 1];
        let premises: Vec<&String> = chain[..chain.len() - 1].iter().collect();

        if premises.len() == 1 {
            format!("(=> {} {conclusion})", premises[0])
        } else {
            let and_part = premises.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(" ");
            format!("(=> (and {and_part}) {conclusion})")
        }
    }

    /// Access the current simplification statistics.
    #[must_use]
    pub fn stats(&self) -> &SimplificationStats {
        &self.stats
    }
}

// ---------------------------------------------------------------------------
// Free functions
// ---------------------------------------------------------------------------

/// Check whether an expression is a tautology (always true).
///
/// Detects: literal `true`, `(and true ... true)`, `(=> false _)`,
/// `(=> _ true)`, `(or ... true ...)`, `(= x x)` syntactic identity,
/// `(or ... P ... (not P) ...)` excluded middle.
#[must_use]
pub fn is_tautology(expr: &str) -> bool {
    let trimmed = expr.trim();
    if trimmed == "true" {
        return true;
    }

    // (not false) -> true
    if trimmed == "(not false)" {
        return true;
    }

    // (and true true ... true)
    if let Some(inner) = trimmed.strip_prefix("(and ").and_then(|s| s.strip_suffix(')')) {
        let parts = split_sexp_args(inner);
        return parts.iter().all(|p| is_tautology(p));
    }

    // (or ... true ...) or (or ... P ... (not P) ...) excluded middle
    if let Some(inner) = trimmed.strip_prefix("(or ").and_then(|s| s.strip_suffix(')')) {
        let parts = split_sexp_args(inner);
        if parts.iter().any(|p| is_tautology(p)) {
            return true;
        }
        // Excluded middle: Or(P, Not(P)) -> true
        if has_contradiction(&parts) {
            return true;
        }
    }

    // (=> false _) or (=> _ true)
    if let Some(inner) = trimmed.strip_prefix("(=> ").and_then(|s| s.strip_suffix(')')) {
        let parts = split_sexp_args(inner);
        if parts.len() == 2 {
            return parts[0].trim() == "false" || is_tautology(parts[1]);
        }
    }

    // (= x x) syntactic identity
    if let Some(inner) = trimmed.strip_prefix("(= ").and_then(|s| s.strip_suffix(')')) {
        let parts = split_sexp_args(inner);
        if parts.len() == 2 && parts[0].trim() == parts[1].trim() {
            return true;
        }
    }

    false
}

/// Check whether an expression is a contradiction (always false).
///
/// Detects: literal `false`, `(and ... false ...)`, `(or false ... false)`,
/// `(not true)`, `(and ... P ... (not P) ...)` contradiction.
#[must_use]
pub fn is_contradiction(expr: &str) -> bool {
    let trimmed = expr.trim();
    if trimmed == "false" {
        return true;
    }

    if trimmed == "(not true)" {
        return true;
    }

    // (and ... false ...) or (and ... P ... (not P) ...) contradiction
    if let Some(inner) = trimmed.strip_prefix("(and ").and_then(|s| s.strip_suffix(')')) {
        let parts = split_sexp_args(inner);
        if parts.iter().any(|p| is_contradiction(p)) {
            return true;
        }
        // Contradiction: And(P, Not(P)) -> false
        if has_contradiction(&parts) {
            return true;
        }
        return false;
    }

    // (or false false ... false)
    if let Some(inner) = trimmed.strip_prefix("(or ").and_then(|s| s.strip_suffix(')')) {
        let parts = split_sexp_args(inner);
        return parts.iter().all(|p| is_contradiction(p));
    }

    false
}

/// Count the number of tokens (atoms and parentheses) in an expression.
#[must_use]
pub fn expression_size(expr: &str) -> usize {
    let trimmed = expr.trim();
    if trimmed.is_empty() {
        return 0;
    }
    // Simple tokenizer: split on whitespace, count parens as separate tokens
    let mut count = 0usize;
    let mut in_token = false;

    for ch in trimmed.chars() {
        match ch {
            '(' | ')' => {
                if in_token {
                    count += 1;
                    in_token = false;
                }
                count += 1;
            }
            ' ' | '\t' | '\n' | '\r' => {
                if in_token {
                    count += 1;
                    in_token = false;
                }
            }
            _ => {
                in_token = true;
            }
        }
    }
    if in_token {
        count += 1;
    }
    count
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Split S-expression arguments at the top level (respecting nested parens).
fn split_sexp_args(s: &str) -> Vec<&str> {
    let mut result = Vec::new();
    let mut depth = 0i32;
    let mut start = 0;
    let bytes = s.as_bytes();

    for (i, &b) in bytes.iter().enumerate() {
        match b {
            b'(' => depth += 1,
            b')' => depth -= 1,
            b' ' | b'\t' | b'\n' if depth == 0 => {
                let token = s[start..i].trim();
                if !token.is_empty() {
                    result.push(token);
                }
                start = i + 1;
            }
            _ => {}
        }
    }
    let last = s[start..].trim();
    if !last.is_empty() {
        result.push(last);
    }
    result
}

/// Find the index of the matching closing paren (starting after an open paren).
fn find_matching_paren(s: &str) -> Option<usize> {
    let mut depth = 1i32;
    for (i, ch) in s.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Extract variable names from an S-expression string.
fn extract_variable_names(expr: &str) -> Vec<&str> {
    let mut names = Vec::new();
    let mut in_token = false;
    let mut start = 0;

    for (i, ch) in expr.char_indices() {
        match ch {
            '(' | ')' | ' ' | '\t' | '\n' | '\r' => {
                if in_token {
                    let token = &expr[start..i];
                    // Variable names: not keywords, not numbers, not booleans
                    if is_variable_name(token) {
                        names.push(token);
                    }
                    in_token = false;
                }
            }
            _ => {
                if !in_token {
                    start = i;
                    in_token = true;
                }
            }
        }
    }
    if in_token {
        let token = &expr[start..];
        if is_variable_name(token) {
            names.push(token);
        }
    }
    names
}

/// Check if a token is a variable name (not a keyword or literal).
fn is_variable_name(token: &str) -> bool {
    if token.is_empty() {
        return false;
    }
    // Not a boolean literal
    if token == "true" || token == "false" {
        return false;
    }
    // Not a number (possibly negative)
    if token.parse::<i128>().is_ok() {
        return false;
    }
    // Not an SMT-LIB keyword
    const KEYWORDS: &[&str] = &[
        "and",
        "or",
        "not",
        "=>",
        "forall",
        "exists",
        "let",
        "=",
        "<",
        "<=",
        ">",
        ">=",
        "+",
        "-",
        "*",
        "/",
        "mod",
        "ite",
        "Int",
        "Bool",
        "BitVec",
        "Array",
        "assert",
        "declare-fun",
        "define-fun",
        "check-sat",
    ];
    !KEYWORDS.contains(&token)
}

/// Parse quantifier bindings like `(x Int) (y Bool)`.
fn parse_bindings(s: &str) -> Vec<(String, String)> {
    let mut result = Vec::new();
    let mut depth = 0i32;
    let mut start = 0;

    for (i, ch) in s.char_indices() {
        match ch {
            '(' => {
                if depth == 0 {
                    start = i + 1;
                }
                depth += 1;
            }
            ')' => {
                depth -= 1;
                if depth == 0 {
                    let binding = s[start..i].trim();
                    if let Some(space_idx) = binding.find(' ') {
                        let name = binding[..space_idx].trim().to_string();
                        let sort = binding[space_idx + 1..].trim().to_string();
                        result.push((name, sort));
                    }
                }
            }
            _ => {}
        }
    }
    result
}

/// Extract constraints from a top-level conjunction.
fn extract_constraints(vc: &str) -> Vec<String> {
    let trimmed = vc.trim();
    if let Some(inner) = trimmed.strip_prefix("(and ").and_then(|s| s.strip_suffix(')')) {
        split_sexp_args(inner).into_iter().map(|s| s.to_string()).collect()
    } else {
        vec![trimmed.to_string()]
    }
}

/// Rejoin constraints into a conjunction.
fn rejoin_constraints(constraints: &[String]) -> String {
    match constraints.len() {
        0 => "true".to_string(),
        1 => constraints[0].clone(),
        _ => format!("(and {})", constraints.join(" ")),
    }
}

/// Extract an implies chain: (=> A (=> B C)) -> [A, B, C].
fn extract_implies_chain(vc: &str) -> Vec<String> {
    let trimmed = vc.trim();
    if let Some(inner) = trimmed.strip_prefix("(=> ").and_then(|s| s.strip_suffix(')')) {
        let parts = split_sexp_args(inner);
        if parts.len() == 2 {
            let mut chain = vec![parts[0].to_string()];
            chain.extend(extract_implies_chain(parts[1]));
            return chain;
        }
    }
    vec![trimmed.to_string()]
}

/// Eliminate common sub-expressions by let-binding.
fn eliminate_common_subexprs(vc: &str) -> String {
    let trimmed = vc.trim();

    // Simple approach: find repeated sub-expressions >= 5 chars
    let subexprs = find_subexpressions(trimmed);
    let mut counts: FxHashMap<&str, usize> = FxHashMap::default();
    for s in &subexprs {
        *counts.entry(s).or_insert(0) += 1;
    }

    // Find sub-expressions appearing more than once, at least 5 chars
    let mut repeated: Vec<(&str, usize)> = counts
        .into_iter()
        .filter(|(s, c)| *c > 1 && s.len() >= 5 && *s != "true" && *s != "false")
        .collect();
    repeated.sort_by(|a, b| b.1.cmp(&a.1).then(b.0.len().cmp(&a.0.len())));

    if repeated.is_empty() {
        return trimmed.to_string();
    }

    // Apply CSE for the most repeated sub-expression
    let (target, _count) = repeated[0];
    let cse_var = format!("__cse_{}", hash_string(target) % 1000);
    let replaced = trimmed.replace(target, &cse_var);
    format!("(let (({cse_var} {target})) {replaced})")
}

/// Find top-level parenthesized sub-expressions.
fn find_subexpressions(s: &str) -> Vec<&str> {
    let mut result = Vec::new();
    let bytes = s.as_bytes();
    let mut i = 0;

    while i < bytes.len() {
        if bytes[i] == b'(' {
            let mut depth = 1i32;
            let start = i;
            i += 1;
            while i < bytes.len() && depth > 0 {
                match bytes[i] {
                    b'(' => depth += 1,
                    b')' => depth -= 1,
                    _ => {}
                }
                i += 1;
            }
            let subexpr = &s[start..i];
            if subexpr.len() >= 5 {
                result.push(subexpr);
            }
        } else {
            i += 1;
        }
    }
    result
}

/// Simple string hash for CSE variable naming.
fn hash_string(s: &str) -> usize {
    let mut h: usize = 0;
    for b in s.bytes() {
        h = h.wrapping_mul(31).wrapping_add(b as usize);
    }
    h
}

/// Propagate known truth values through a formula.
fn propagate_truth_values(vc: &str) -> String {
    let trimmed = vc.trim();

    // (and true P) -> P, (and P true) -> P
    if let Some(inner) = trimmed.strip_prefix("(and ").and_then(|s| s.strip_suffix(')')) {
        let parts = split_sexp_args(inner);
        let non_true: Vec<&str> = parts.iter().filter(|p| p.trim() != "true").copied().collect();
        if parts.iter().any(|p| p.trim() == "false") {
            return "false".to_string();
        }
        if non_true.len() < parts.len() {
            return match non_true.len() {
                0 => "true".to_string(),
                1 => non_true[0].to_string(),
                _ => format!("(and {})", non_true.join(" ")),
            };
        }
    }

    // (or false P) -> P, (or P false) -> P
    if let Some(inner) = trimmed.strip_prefix("(or ").and_then(|s| s.strip_suffix(')')) {
        let parts = split_sexp_args(inner);
        let non_false: Vec<&str> = parts.iter().filter(|p| p.trim() != "false").copied().collect();
        if parts.iter().any(|p| p.trim() == "true") {
            return "true".to_string();
        }
        if non_false.len() < parts.len() {
            return match non_false.len() {
                0 => "false".to_string(),
                1 => non_false[0].to_string(),
                _ => format!("(or {})", non_false.join(" ")),
            };
        }
    }

    // (not true) -> false, (not false) -> true
    if trimmed == "(not true)" {
        return "false".to_string();
    }
    if trimmed == "(not false)" {
        return "true".to_string();
    }

    trimmed.to_string()
}

/// Check whether a set of conjuncts/disjuncts contains both P and (not P)
/// for some sub-expression P.
///
/// Used for contradiction detection in And and tautology detection in Or.
fn has_contradiction(parts: &[&str]) -> bool {
    let mut positives: FxHashSet<&str> = FxHashSet::default();
    let mut negatives: FxHashSet<&str> = FxHashSet::default();

    for part in parts {
        let p = part.trim();
        if let Some(inner) = p.strip_prefix("(not ").and_then(|s| s.strip_suffix(')')) {
            negatives.insert(inner.trim());
        } else {
            positives.insert(p);
        }
    }

    // Check if any positive appears as a negative or vice versa
    positives.iter().any(|p| negatives.contains(p))
}

/// Try to fold integer arithmetic: (+ 1 2) -> 3, etc.
#[allow(clippy::type_complexity)]
fn try_fold_arithmetic(expr: &str) -> Option<String> {
    let trimmed = expr.trim();

    let ops: &[(&str, fn(i128, i128) -> Option<i128>)] = &[
        ("(+ ", |a, b| Some(a.wrapping_add(b))),
        ("(- ", |a, b| Some(a.wrapping_sub(b))),
        ("(* ", |a, b| Some(a.wrapping_mul(b))),
        ("(/ ", |a, b| if b != 0 { Some(a / b) } else { None }),
        ("(mod ", |a, b| if b != 0 { Some(a % b) } else { None }),
    ];

    for (prefix, op) in ops {
        if let Some(inner) = trimmed.strip_prefix(prefix).and_then(|s| s.strip_suffix(')')) {
            let parts = split_sexp_args(inner);
            if parts.len() == 2
                && let (Ok(a), Ok(b)) = (parts[0].parse::<i128>(), parts[1].parse::<i128>())
                && let Some(result) = op(a, b)
            {
                return Some(result.to_string());
            }
        }
    }

    // Comparison folding
    let cmp_ops: &[(&str, fn(i128, i128) -> bool)] = &[
        ("(= ", |a, b| a == b),
        ("(< ", |a, b| a < b),
        ("(<= ", |a, b| a <= b),
        ("(> ", |a, b| a > b),
        ("(>= ", |a, b| a >= b),
    ];

    for (prefix, op) in cmp_ops {
        if let Some(inner) = trimmed.strip_prefix(prefix).and_then(|s| s.strip_suffix(')')) {
            let parts = split_sexp_args(inner);
            if parts.len() == 2
                && let (Ok(a), Ok(b)) = (parts[0].parse::<i128>(), parts[1].parse::<i128>())
            {
                return Some(if op(a, b) { "true" } else { "false" }.to_string());
            }
        }
    }

    None
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -----------------------------------------------------------------------
    // expression_size tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_expression_size_atom() {
        assert_eq!(expression_size("true"), 1);
        assert_eq!(expression_size("x"), 1);
        assert_eq!(expression_size("42"), 1);
    }

    #[test]
    fn test_expression_size_sexp() {
        // (and x y) = ( + and + x + y + ) = 5
        assert_eq!(expression_size("(and x y)"), 5);
    }

    #[test]
    fn test_expression_size_empty() {
        assert_eq!(expression_size(""), 0);
        assert_eq!(expression_size("  "), 0);
    }

    #[test]
    fn test_expression_size_nested() {
        // (and (or a b) c) = ( and ( or a b ) c ) = 9
        assert_eq!(expression_size("(and (or a b) c)"), 9);
    }

    // -----------------------------------------------------------------------
    // is_tautology tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_is_tautology_true() {
        assert!(is_tautology("true"));
    }

    #[test]
    fn test_is_tautology_false() {
        assert!(!is_tautology("false"));
    }

    #[test]
    fn test_is_tautology_and_all_true() {
        assert!(is_tautology("(and true true true)"));
    }

    #[test]
    fn test_is_tautology_or_contains_true() {
        assert!(is_tautology("(or false true x)"));
    }

    #[test]
    fn test_is_tautology_implies_false_lhs() {
        assert!(is_tautology("(=> false x)"));
    }

    #[test]
    fn test_is_tautology_implies_true_rhs() {
        assert!(is_tautology("(=> x true)"));
    }

    #[test]
    fn test_is_tautology_eq_reflexive() {
        assert!(is_tautology("(= x x)"));
    }

    #[test]
    fn test_is_tautology_variable_not_tautology() {
        assert!(!is_tautology("x"));
    }

    // -----------------------------------------------------------------------
    // is_contradiction tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_is_contradiction_false() {
        assert!(is_contradiction("false"));
    }

    #[test]
    fn test_is_contradiction_true() {
        assert!(!is_contradiction("true"));
    }

    #[test]
    fn test_is_contradiction_not_true() {
        assert!(is_contradiction("(not true)"));
    }

    #[test]
    fn test_is_contradiction_and_contains_false() {
        assert!(is_contradiction("(and x false y)"));
    }

    #[test]
    fn test_is_contradiction_or_all_false() {
        assert!(is_contradiction("(or false false)"));
    }

    #[test]
    fn test_is_contradiction_variable_not_contradiction() {
        assert!(!is_contradiction("x"));
    }

    // -----------------------------------------------------------------------
    // VcSimplifier tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_simplifier_fold_constants_and_true() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.fold_constants("(and true x)");
        assert_eq!(result, "x");
    }

    #[test]
    fn test_simplifier_fold_constants_and_false() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.fold_constants("(and x false)");
        assert_eq!(result, "false");
    }

    #[test]
    fn test_simplifier_fold_constants_or_true() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.fold_constants("(or x true)");
        assert_eq!(result, "true");
    }

    #[test]
    fn test_simplifier_fold_constants_arithmetic() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        assert_eq!(s.fold_constants("(+ 3 4)"), "7");
        assert_eq!(s.fold_constants("(- 10 3)"), "7");
        assert_eq!(s.fold_constants("(* 3 4)"), "12");
        assert_eq!(s.fold_constants("(/ 10 3)"), "3");
        assert_eq!(s.fold_constants("(mod 10 3)"), "1");
    }

    #[test]
    fn test_simplifier_fold_constants_comparison() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        assert_eq!(s.fold_constants("(= 3 3)"), "true");
        assert_eq!(s.fold_constants("(< 2 3)"), "true");
        assert_eq!(s.fold_constants("(> 2 3)"), "false");
    }

    #[test]
    fn test_simplifier_fold_implies_false_lhs() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.fold_constants("(=> false x)");
        assert_eq!(result, "true");
    }

    #[test]
    fn test_simplifier_fold_implies_true_lhs() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.fold_constants("(=> true x)");
        assert_eq!(result, "x");
    }

    #[test]
    fn test_simplifier_remove_redundant() {
        let s = VcSimplifier::new(VcSimplifier::default_config());
        let constraints = vec![
            "(> x 0)".to_string(),
            "(< y 10)".to_string(),
            "(> x 0)".to_string(), // duplicate
            "true".to_string(),    // trivial
        ];
        let result = s.remove_redundant(&constraints);
        assert_eq!(result.len(), 2);
        assert_eq!(result[0], "(> x 0)");
        assert_eq!(result[1], "(< y 10)");
    }

    #[test]
    fn test_simplifier_implies_chain() {
        let s = VcSimplifier::new(VcSimplifier::default_config());
        let chain = vec!["(> x 0)".to_string(), "(< y 10)".to_string(), "(= z 5)".to_string()];
        let result = s.simplify_implies_chain(&chain);
        assert_eq!(result, "(=> (and (> x 0) (< y 10)) (= z 5))");
    }

    #[test]
    fn test_simplifier_implies_chain_single() {
        let s = VcSimplifier::new(VcSimplifier::default_config());
        let chain = vec!["(> x 0)".to_string()];
        assert_eq!(s.simplify_implies_chain(&chain), "(> x 0)");
    }

    #[test]
    fn test_simplifier_implies_chain_pair() {
        let s = VcSimplifier::new(VcSimplifier::default_config());
        let chain = vec!["(> x 0)".to_string(), "(< y 10)".to_string()];
        assert_eq!(s.simplify_implies_chain(&chain), "(=> (> x 0) (< y 10))");
    }

    #[test]
    fn test_simplifier_dead_var_elimination() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.eliminate_dead_vars("(forall ((x Int) (y Int)) (> x 0))", &[]);
        assert_eq!(result, "(forall ((x Int)) (> x 0))");
        assert_eq!(s.stats().dead_vars_eliminated, 1);
    }

    #[test]
    fn test_simplifier_dead_var_keeps_live() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.eliminate_dead_vars("(forall ((x Int) (y Int)) (> x 0))", &["y"]);
        assert_eq!(result, "(forall ((x Int) (y Int)) (> x 0))");
    }

    #[test]
    fn test_simplifier_dead_var_all_dead() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.eliminate_dead_vars("(exists ((x Int)) true)", &[]);
        assert_eq!(result, "true");
    }

    #[test]
    fn test_simplify_full_pipeline() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.simplify("(and true (> x 0))");
        assert_eq!(result.formula, "(> x 0)");
        assert!(result.stats.original_size > result.stats.simplified_size);
    }

    #[test]
    fn test_simplify_tautology_detection() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.simplify("(and true true)");
        assert!(result.is_trivially_true);
        assert_eq!(result.formula, "true");
    }

    #[test]
    fn test_simplify_already_simple() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.simplify("(> x 0)");
        assert_eq!(result.formula, "(> x 0)");
        assert!(!result.is_trivially_true);
    }

    #[test]
    fn test_simplify_stats_tracking() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.simplify("(and true (> x 0) true)");
        assert!(result.stats.passes_applied >= 1);
        assert!(result.stats.original_size > 0);
    }

    #[test]
    fn test_simplification_config_default() {
        let config = SimplificationConfig::default();
        assert_eq!(config.passes.len(), 6);
        assert_eq!(config.max_iterations, 10);
        assert!(config.enable_stats);
    }

    #[test]
    fn test_stats_reduction_ratio() {
        let stats =
            SimplificationStats { original_size: 100, simplified_size: 75, ..Default::default() };
        let ratio = stats.reduction_ratio();
        assert!((ratio - 0.25).abs() < 1e-10);
    }

    #[test]
    fn test_stats_reduction_ratio_zero_original() {
        let stats = SimplificationStats::default();
        assert!((stats.reduction_ratio()).abs() < 1e-10);
    }

    #[test]
    fn test_truth_value_propagation_not() {
        assert_eq!(propagate_truth_values("(not true)"), "false");
        assert_eq!(propagate_truth_values("(not false)"), "true");
    }

    #[test]
    fn test_extract_implies_chain() {
        let chain = extract_implies_chain("(=> a (=> b c))");
        assert_eq!(chain, vec!["a", "b", "c"]);
    }

    #[test]
    fn test_extract_implies_chain_no_chain() {
        let chain = extract_implies_chain("(> x 0)");
        assert_eq!(chain, vec!["(> x 0)"]);
    }

    #[test]
    fn test_split_sexp_args_simple() {
        let args = split_sexp_args("x y z");
        assert_eq!(args, vec!["x", "y", "z"]);
    }

    #[test]
    fn test_split_sexp_args_nested() {
        let args = split_sexp_args("(+ a b) c");
        assert_eq!(args, vec!["(+ a b)", "c"]);
    }

    #[test]
    fn test_div_by_zero_not_folded() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.fold_constants("(/ 10 0)");
        assert_eq!(result, "(/ 10 0)");
    }

    // -----------------------------------------------------------------------
    // New simplification rules
    // -----------------------------------------------------------------------

    // --- Double negation elimination ---

    #[test]
    fn test_fold_double_negation() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.fold_constants("(not (not x))");
        assert_eq!(result, "x");
    }

    #[test]
    fn test_fold_double_negation_nested_expr() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.fold_constants("(not (not (> x 0)))");
        assert_eq!(result, "(> x 0)");
    }

    // --- Identity removal (singleton unwrap) ---

    #[test]
    fn test_fold_and_singleton() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.fold_constants("(and (> x 0))");
        assert_eq!(result, "(> x 0)");
    }

    #[test]
    fn test_fold_or_singleton() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.fold_constants("(or (> x 0))");
        assert_eq!(result, "(> x 0)");
    }

    // --- Reflexive equality ---

    #[test]
    fn test_fold_eq_reflexive_variable() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.fold_constants("(= x x)");
        assert_eq!(result, "true");
    }

    #[test]
    fn test_fold_eq_reflexive_expr() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.fold_constants("(= (+ a b) (+ a b))");
        assert_eq!(result, "true");
    }

    #[test]
    fn test_fold_eq_different_exprs_not_folded() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.fold_constants("(= x y)");
        assert_eq!(result, "(= x y)");
    }

    // --- Contradiction detection ---

    #[test]
    fn test_fold_and_contradiction() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.fold_constants("(and x (not x))");
        assert_eq!(result, "false");
    }

    #[test]
    fn test_fold_and_contradiction_complex_subexpr() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.fold_constants("(and (> x 0) (not (> x 0)))");
        assert_eq!(result, "false");
    }

    #[test]
    fn test_fold_and_contradiction_with_other_terms() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.fold_constants("(and (< y 5) x (not x))");
        assert_eq!(result, "false");
    }

    // --- Tautology detection (excluded middle in Or) ---

    #[test]
    fn test_fold_or_excluded_middle() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.fold_constants("(or x (not x))");
        assert_eq!(result, "true");
    }

    #[test]
    fn test_fold_or_excluded_middle_complex() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.fold_constants("(or (> x 0) (not (> x 0)))");
        assert_eq!(result, "true");
    }

    // --- is_tautology enhancements ---

    #[test]
    fn test_is_tautology_not_false() {
        assert!(is_tautology("(not false)"));
    }

    #[test]
    fn test_is_tautology_or_excluded_middle() {
        assert!(is_tautology("(or x (not x))"));
    }

    #[test]
    fn test_is_tautology_or_excluded_middle_complex() {
        assert!(is_tautology("(or (> a 0) (not (> a 0)))"));
    }

    // --- is_contradiction enhancements ---

    #[test]
    fn test_is_contradiction_and_p_not_p() {
        assert!(is_contradiction("(and x (not x))"));
    }

    #[test]
    fn test_is_contradiction_and_complex_p_not_p() {
        assert!(is_contradiction("(and (> x 0) y (not (> x 0)))"));
    }

    #[test]
    fn test_is_contradiction_not_triggered_for_different_terms() {
        assert!(!is_contradiction("(and x (not y))"));
    }

    // --- Full pipeline with new rules ---

    #[test]
    fn test_simplify_pipeline_double_negation() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.simplify("(not (not (> x 0)))");
        assert_eq!(result.formula, "(> x 0)");
    }

    #[test]
    fn test_simplify_pipeline_contradiction_becomes_false() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.simplify("(and x (not x))");
        assert_eq!(result.formula, "false");
        assert!(!result.is_trivially_true);
    }

    #[test]
    fn test_simplify_pipeline_eq_reflexive() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        let result = s.simplify("(= x x)");
        assert_eq!(result.formula, "true");
        assert!(result.is_trivially_true);
    }

    #[test]
    fn test_simplify_pipeline_and_with_true_from_eq_reflexive() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        // (and true (> y 0)) should simplify to (> y 0)
        // Note: the string-level pipeline operates on the top-level expression,
        // so (= x x) must already be folded to true at this point.
        let result = s.simplify("(and true (> y 0))");
        assert_eq!(result.formula, "(> y 0)");
    }

    #[test]
    fn test_simplify_pipeline_eq_reflexive_standalone() {
        let mut s = VcSimplifier::new(VcSimplifier::default_config());
        // Top-level (= x x) should fold to true
        let result = s.simplify("(= x x)");
        assert_eq!(result.formula, "true");
        assert!(result.is_trivially_true);
    }
}
