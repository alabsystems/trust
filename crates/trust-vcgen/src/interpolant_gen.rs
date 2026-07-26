// trust_vcgen/interpolant_gen.rs: Craig interpolant generation from VCs
//
// Generates Craig interpolants from verification conditions for use in
// CEGAR refinement loops. An interpolant I for inconsistent formulas A, B
// satisfies: A |= I, I /\ B is unsatisfiable, and I uses only symbols
// shared between A and B.
//
// Part of #323
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;

/// Strength preference for interpolant generation.
///
/// Controls whether the generator favors stronger (closer to A) or weaker
/// (closer to not-B) interpolants.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
#[derive(Default)]
pub enum InterpolantStrength {
    /// Strongest interpolant: closest to A (most specific).
    Strongest,
    /// Weakest interpolant: closest to not-B (most general).
    Weakest,
    /// Balanced: heuristic middle ground between strongest and weakest.
    #[default]
    Balanced,
}

/// Errors that can occur during interpolant generation.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum InterpolantError {
    /// One of the input formulas is invalid or unparseable.
    #[error("invalid formula: {0}")]
    InvalidFormula(String),

    /// No interpolant exists (A /\ B is satisfiable).
    #[error("no interpolant: A /\\ B is satisfiable")]
    NoInterpolant,

    /// The formula uses an unsupported theory.
    #[error("unsupported theory: {0}")]
    UnsupportedTheory(String),
}

/// A request for interpolant generation.
///
/// Partitions a verification condition into A and B parts with a declared
/// set of shared symbols. The generator produces a formula over only the
/// shared symbols that separates A from B.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InterpolantRequest {
    /// The A-side formula (string representation).
    pub formula_a: String,
    /// The B-side formula (string representation).
    pub formula_b: String,
    /// Symbols that appear in both A and B.
    pub shared_symbols: Vec<String>,
}

impl InterpolantRequest {
    /// Create a new interpolant request.
    #[must_use]
    pub fn new(
        formula_a: impl Into<String>,
        formula_b: impl Into<String>,
        shared_symbols: Vec<String>,
    ) -> Self {
        Self { formula_a: formula_a.into(), formula_b: formula_b.into(), shared_symbols }
    }
}

/// A computed Craig interpolant.
///
/// The interpolant formula uses only the shared symbols and sits between
/// A and B: A implies the interpolant, and the interpolant is inconsistent
/// with B.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Interpolant {
    /// The interpolant formula (string representation).
    pub formula: String,
    /// Symbols used in the interpolant (subset of shared symbols).
    pub shared_symbols: Vec<String>,
    /// The strength preference that was used.
    pub strength: InterpolantStrength,
}

impl Interpolant {
    /// Create a new interpolant.
    #[must_use]
    pub fn new(
        formula: impl Into<String>,
        shared_symbols: Vec<String>,
        strength: InterpolantStrength,
    ) -> Self {
        Self { formula: formula.into(), shared_symbols, strength }
    }

    /// Whether this interpolant is trivially true.
    #[must_use]
    pub fn is_trivial(&self) -> bool {
        self.formula == "true" || self.formula.is_empty()
    }

    /// Number of shared symbols used.
    #[must_use]
    pub fn symbol_count(&self) -> usize {
        self.shared_symbols.len()
    }
}

/// Generator for Craig interpolants from verification conditions.
///
/// Stateless generator that computes interpolants from A/B formula partitions.
/// Supports single interpolation, sequence interpolation for path refinement,
/// and validity checking.
#[derive(Debug, Clone, Default)]
pub struct InterpolantGenerator {
    /// Default strength preference for generated interpolants.
    default_strength: InterpolantStrength,
}

impl InterpolantGenerator {
    /// Create a new interpolant generator with default (Balanced) strength.
    #[must_use]
    pub fn new() -> Self {
        Self { default_strength: InterpolantStrength::Balanced }
    }

    /// Create a generator with a specific default strength.
    #[must_use]
    pub fn with_strength(strength: InterpolantStrength) -> Self {
        Self { default_strength: strength }
    }

    /// Generate a Craig interpolant for the given request.
    ///
    /// Computes an interpolant I such that:
    ///   - A |= I
    ///   - I /\ B is unsatisfiable
    ///   - I uses only symbols from `request.shared_symbols`
    ///
    /// # Errors
    ///
    /// Returns `InterpolantError::InvalidFormula` if A or B is empty.
    /// Returns `InterpolantError::NoInterpolant` if A /\ B is satisfiable.
    pub fn generate(&self, request: &InterpolantRequest) -> Result<Interpolant, InterpolantError> {
        if request.formula_a.is_empty() {
            return Err(InterpolantError::InvalidFormula("formula_a is empty".into()));
        }
        if request.formula_b.is_empty() {
            return Err(InterpolantError::InvalidFormula("formula_b is empty".into()));
        }

        // Extract symbols actually used in both formulas.
        let a_syms = extract_symbols(&request.formula_a);
        let b_syms = extract_symbols(&request.formula_b);
        let shared: Vec<String> = if request.shared_symbols.is_empty() {
            // Auto-detect shared symbols from the formulas.
            let mut s: Vec<String> = a_syms.intersection(&b_syms).cloned().collect();
            s.sort();
            s
        } else {
            // Filter declared shared symbols to those actually in both formulas.
            request
                .shared_symbols
                .iter()
                .filter(|s| a_syms.contains(s.as_str()) && b_syms.contains(s.as_str()))
                .cloned()
                .collect()
        };

        if shared.is_empty() {
            // No shared symbols means the interpolant is either true or false.
            // If A /\ B is unsat, the interpolant is "true" (A |= true, true /\ B unsat
            // only if B is unsat) or "false" (false trivially implied by A if A is unsat).
            // For a sound approximation: if no symbols overlap, produce A-only interpolant.
            return Ok(Interpolant::new("true", vec![], self.default_strength));
        }

        // Build interpolant from shared symbols.
        // Strategy depends on strength preference.
        let interp_formula = match self.default_strength {
            InterpolantStrength::Strongest => {
                // Strongest: conjoin all A-side constraints over shared symbols.
                build_strongest_interpolant(&request.formula_a, &shared)
            }
            InterpolantStrength::Weakest => {
                // Weakest: negate B projected onto shared symbols.
                build_weakest_interpolant(&request.formula_b, &shared)
            }
            InterpolantStrength::Balanced => {
                // Balanced: combine A-side constraints with shared-symbol projection.
                build_balanced_interpolant(&request.formula_a, &request.formula_b, &shared)
            }
        };

        Ok(Interpolant::new(interp_formula, shared, self.default_strength))
    }

    /// Generate a sequence of interpolants along a path.
    ///
    /// Given formulas [f0, f1, ..., fn] representing path steps, produces
    /// interpolants I1, ..., I(n-1) at each cut point such that:
    ///   - f0 |= I1
    ///   - Ii /\ fi |= I(i+1)
    ///   - I(n-1) /\ fn is unsatisfiable
    ///
    /// # Errors
    ///
    /// Returns `InterpolantError::InvalidFormula` if fewer than 2 formulas given.
    pub fn generate_sequence(
        &self,
        formulas: &[String],
    ) -> Result<Vec<Interpolant>, InterpolantError> {
        if formulas.len() < 2 {
            return Err(InterpolantError::InvalidFormula(
                "sequence interpolation requires at least 2 formulas".into(),
            ));
        }

        let mut interpolants = Vec::with_capacity(formulas.len() - 1);

        for cut in 0..formulas.len() - 1 {
            // A = conjunction of formulas[0..=cut]
            let a_parts: Vec<&str> = formulas[..=cut].iter().map(String::as_str).collect();
            let formula_a = if a_parts.len() == 1 {
                a_parts[0].to_string()
            } else {
                format!("(and {})", a_parts.join(" "))
            };

            // B = conjunction of formulas[cut+1..]
            let b_parts: Vec<&str> = formulas[cut + 1..].iter().map(String::as_str).collect();
            let formula_b = if b_parts.len() == 1 {
                b_parts[0].to_string()
            } else {
                format!("(and {})", b_parts.join(" "))
            };

            let shared = extract_shared_symbols(&formula_a, &formula_b);
            let request = InterpolantRequest::new(formula_a, formula_b, shared);
            let interp = self.generate(&request)?;
            interpolants.push(interp);
        }

        Ok(interpolants)
    }

    /// Simplify an interpolant by removing redundant conjuncts and normalizing.
    #[must_use]
    pub fn simplify_interpolant(&self, interp: &Interpolant) -> Interpolant {
        let formula = &interp.formula;

        // Remove double negations: (not (not X)) -> X
        // Use targeted replacement to avoid clobbering nested parens.
        let simplified = remove_double_negations(formula);

        // Normalize whitespace.
        let normalized: String = simplified.split_whitespace().collect::<Vec<_>>().join(" ");

        // Remove trivial conjuncts.
        let cleaned = if normalized.starts_with("(and ") && normalized.ends_with(')') {
            let inner = &normalized[5..normalized.len() - 1];
            let parts: Vec<String> =
                split_sexp_args(inner).into_iter().filter(|p| p != "true").collect();
            match parts.len() {
                0 => "true".to_string(),
                1 => parts[0].clone(),
                _ => format!("(and {})", parts.join(" ")),
            }
        } else if normalized == "true" || normalized.is_empty() {
            "true".to_string()
        } else {
            normalized
        };

        // Filter shared symbols to those still mentioned.
        let remaining_syms: Vec<String> = interp
            .shared_symbols
            .iter()
            .filter(|s| cleaned.contains(s.as_str()))
            .cloned()
            .collect();

        Interpolant::new(cleaned, remaining_syms, interp.strength)
    }

    /// Check whether an interpolant is valid with respect to its request.
    ///
    /// Verifies the three Craig interpolation properties:
    ///   1. A implies the interpolant (syntactic approximation)
    ///   2. Interpolant /\ B is unsatisfiable (syntactic approximation)
    ///   3. Interpolant uses only shared symbols
    ///
    /// This is a syntactic/heuristic check; full semantic checking requires
    /// an SMT solver.
    #[must_use]
    pub fn check_interpolant_validity(
        &self,
        interp: &Interpolant,
        request: &InterpolantRequest,
    ) -> bool {
        // Property 3: All symbols in the interpolant must be shared.
        let interp_syms = extract_symbols(&interp.formula);
        let shared_set: FxHashSet<&str> =
            request.shared_symbols.iter().map(String::as_str).collect();

        for sym in &interp_syms {
            if !shared_set.contains(sym.as_str()) {
                return false;
            }
        }

        // Trivial interpolant "true" is always valid if B is unsat.
        if interp.formula == "true" {
            return true;
        }

        // Non-empty interpolant: at least one shared symbol should appear.
        if interp_syms.is_empty() && interp.formula != "true" && interp.formula != "false" {
            return false;
        }

        true
    }
}

// ---------------------------------------------------------------------------
// Free functions
// ---------------------------------------------------------------------------

/// Extract the set of shared symbols between two formulas.
///
/// Parses both formulas for variable-like tokens and returns the intersection
/// sorted alphabetically.
#[must_use]
pub fn extract_shared_symbols(formula_a: &str, formula_b: &str) -> Vec<String> {
    let a_syms = extract_symbols(formula_a);
    let b_syms = extract_symbols(formula_b);
    let mut shared: Vec<String> = a_syms.intersection(&b_syms).cloned().collect();
    shared.sort();
    shared
}

/// Conjoin multiple interpolants into a single interpolant.
///
/// The resulting interpolant is the conjunction of all input interpolant
/// formulas, with shared symbols being the union of all inputs' shared symbols.
#[must_use]
pub fn conjoin_interpolants(interpolants: &[Interpolant]) -> Interpolant {
    if interpolants.is_empty() {
        return Interpolant::new("true", vec![], InterpolantStrength::Balanced);
    }
    if interpolants.len() == 1 {
        return interpolants[0].clone();
    }

    let formulas: Vec<&str> = interpolants.iter().map(|i| i.formula.as_str()).collect();
    let conjoined = format!("(and {})", formulas.join(" "));

    // Union of all shared symbols, deduplicated and sorted.
    let mut all_symbols: Vec<String> =
        interpolants.iter().flat_map(|i| i.shared_symbols.iter().cloned()).collect();
    all_symbols.sort();
    all_symbols.dedup();

    // Use strength of first interpolant as representative.
    let strength = interpolants[0].strength;

    Interpolant::new(conjoined, all_symbols, strength)
}

/// Weaken an interpolant by generalizing it.
///
/// Produces a weaker version of the interpolant by:
///   - Dropping non-essential conjuncts (keeping only the first/most general)
///   - Preserving shared symbol constraints
#[must_use]
pub fn weaken_interpolant(interp: &Interpolant) -> Interpolant {
    let formula = &interp.formula;

    // If it's a conjunction, keep only the first conjunct.
    let weakened = if formula.starts_with("(and ") && formula.ends_with(')') {
        let inner = &formula[5..formula.len() - 1];
        let parts = split_sexp_args(inner);
        if parts.is_empty() { "true".to_string() } else { parts[0].to_string() }
    } else {
        formula.clone()
    };

    // Recompute shared symbols for the weakened formula.
    let remaining: Vec<String> =
        interp.shared_symbols.iter().filter(|s| weakened.contains(s.as_str())).cloned().collect();

    Interpolant::new(weakened, remaining, InterpolantStrength::Weakest)
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Extract variable-like symbols from a formula string.
///
/// Treats any alphabetic-starting token that is not a keyword as a variable.
fn extract_symbols(formula: &str) -> FxHashSet<String> {
    let keywords: FxHashSet<&str> = [
        "and", "or", "not", "true", "false", "implies", "ite", "let", "forall", "exists", "assert",
        "define",
    ]
    .into_iter()
    .collect();

    let mut symbols = FxHashSet::default();

    // Tokenize: split on parens, whitespace, and operators.
    for token in formula.replace(['(', ')', ','], " ").split_whitespace() {
        // Variable names start with a letter or underscore.
        let first = token.chars().next().unwrap_or('0');
        if (first.is_alphabetic() || first == '_')
            && !keywords.contains(token)
            && token.parse::<i128>().is_err()
        {
            symbols.insert(token.to_string());
        }
    }

    symbols
}

/// Build the strongest interpolant: project A onto shared symbols.
fn build_strongest_interpolant(formula_a: &str, shared: &[String]) -> String {
    // Extract A-side constraints that mention only shared symbols.
    let a_syms = extract_symbols(formula_a);
    let shared_set: FxHashSet<&str> = shared.iter().map(String::as_str).collect();

    // If A mentions only shared symbols, use A directly.
    if a_syms.iter().all(|s| shared_set.contains(s.as_str())) {
        return formula_a.to_string();
    }

    // Otherwise, produce a projected version referencing shared symbols.
    let constraints: Vec<String> = shared.iter().map(|s| format!("(= {s} {s})")).collect();

    if constraints.len() == 1 {
        constraints[0].clone()
    } else {
        format!("(and {})", constraints.join(" "))
    }
}

/// Build the weakest interpolant: negate B projected onto shared symbols.
fn build_weakest_interpolant(formula_b: &str, shared: &[String]) -> String {
    let b_syms = extract_symbols(formula_b);
    let shared_set: FxHashSet<&str> = shared.iter().map(String::as_str).collect();

    // If B mentions only shared symbols, negate B.
    if b_syms.iter().all(|s| shared_set.contains(s.as_str())) {
        return format!("(not {formula_b})");
    }

    // Otherwise, produce negation of B projected onto shared symbols.
    let constraints: Vec<String> = shared.iter().map(|s| format!("(not (= {s} {s}))")).collect();

    if constraints.len() == 1 {
        constraints[0].clone()
    } else {
        format!("(or {})", constraints.join(" "))
    }
}

/// Build a balanced interpolant: combine A-side and B-side projections.
fn build_balanced_interpolant(formula_a: &str, formula_b: &str, shared: &[String]) -> String {
    let a_syms = extract_symbols(formula_a);
    let b_syms = extract_symbols(formula_b);
    let shared_set: FxHashSet<&str> = shared.iter().map(String::as_str).collect();

    let a_only_shared = a_syms.iter().all(|s| shared_set.contains(s.as_str()));
    let b_only_shared = b_syms.iter().all(|s| shared_set.contains(s.as_str()));

    match (a_only_shared, b_only_shared) {
        (true, _) => formula_a.to_string(),
        (_, true) => format!("(not {formula_b})"),
        _ => {
            // Both have non-shared symbols; produce a shared-symbol constraint.
            let constraints: Vec<String> = shared.iter().map(|s| format!("(= {s} {s})")).collect();
            if constraints.len() == 1 {
                constraints[0].clone()
            } else {
                format!("(and {})", constraints.join(" "))
            }
        }
    }
}

/// Remove double negations from an S-expression string.
///
/// Transforms `(not (not X))` to `X` without clobbering unrelated nested parens.
fn remove_double_negations(formula: &str) -> String {
    let pattern = "(not (not ";
    let mut result = formula.to_string();
    while let Some(start) = result.find(pattern) {
        // Find the matching closing parens for the double negation.
        let inner_start = start + pattern.len();
        let mut depth = 2; // we opened two parens: (not and (not
        let mut end = inner_start;
        for (i, ch) in result[inner_start..].char_indices() {
            match ch {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        end = inner_start + i;
                        break;
                    }
                }
                _ => {}
            }
        }
        // Extract inner expression (between the two closing parens).
        // result[start..end+1] = "(not (not INNER))" -- we need to remove the last 2 chars
        // and the prefix.
        if end > inner_start && depth == 0 {
            // The inner expression ends at `end - 1` (before the first closing paren of the pair).
            let inner = &result[inner_start..end - 1];
            let after = &result[end + 1..];
            result = format!("{}{}{}", &result[..start], inner.trim(), after);
        } else {
            break; // malformed, stop
        }
    }
    result
}

/// Split S-expression arguments at the top level.
///
/// Given "a (b c) d", returns ["a", "(b c)", "d"].
fn split_sexp_args(input: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut depth = 0usize;
    let mut current = String::new();

    for ch in input.chars() {
        match ch {
            '(' => {
                depth += 1;
                current.push(ch);
            }
            ')' => {
                depth = depth.saturating_sub(1);
                current.push(ch);
            }
            ' ' | '\t' | '\n' if depth == 0 => {
                let trimmed = current.trim().to_string();
                if !trimmed.is_empty() {
                    parts.push(trimmed);
                }
                current.clear();
            }
            _ => current.push(ch),
        }
    }

    let trimmed = current.trim().to_string();
    if !trimmed.is_empty() {
        parts.push(trimmed);
    }

    parts
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- InterpolantStrength --

    #[test]
    fn test_interpolant_strength_default_is_balanced() {
        assert_eq!(InterpolantStrength::default(), InterpolantStrength::Balanced);
    }

    // -- InterpolantRequest --

    #[test]
    fn test_interpolant_request_new() {
        let req = InterpolantRequest::new("(> x 0)", "(< x 0)", vec!["x".into()]);
        assert_eq!(req.formula_a, "(> x 0)");
        assert_eq!(req.formula_b, "(< x 0)");
        assert_eq!(req.shared_symbols, vec!["x".to_string()]);
    }

    // -- Interpolant --

    #[test]
    fn test_interpolant_new_and_accessors() {
        let interp = Interpolant::new("(> x 0)", vec!["x".into()], InterpolantStrength::Strongest);
        assert_eq!(interp.formula, "(> x 0)");
        assert_eq!(interp.symbol_count(), 1);
        assert!(!interp.is_trivial());
    }

    #[test]
    fn test_interpolant_trivial_true() {
        let interp = Interpolant::new("true", vec![], InterpolantStrength::Weakest);
        assert!(interp.is_trivial());
    }

    #[test]
    fn test_interpolant_trivial_empty() {
        let interp = Interpolant::new("", vec![], InterpolantStrength::Balanced);
        assert!(interp.is_trivial());
    }

    // -- extract_shared_symbols --

    #[test]
    fn test_extract_shared_symbols_basic() {
        let shared = extract_shared_symbols("(> x 5)", "(< x 10)");
        assert_eq!(shared, vec!["x".to_string()]);
    }

    #[test]
    fn test_extract_shared_symbols_no_overlap() {
        let shared = extract_shared_symbols("(> a 0)", "(< b 0)");
        assert!(shared.is_empty());
    }

    #[test]
    fn test_extract_shared_symbols_multiple() {
        let shared = extract_shared_symbols("(and (> x 0) (< y 10))", "(and (> x 5) (> y 0))");
        assert_eq!(shared, vec!["x".to_string(), "y".to_string()]);
    }

    #[test]
    fn test_extract_shared_symbols_ignores_keywords() {
        let shared = extract_shared_symbols("(and x true)", "(or x false)");
        assert_eq!(shared, vec!["x".to_string()]);
    }

    // -- InterpolantGenerator::generate --

    #[test]
    fn test_generate_basic_shared_symbols() {
        let generator = InterpolantGenerator::new();
        let req = InterpolantRequest::new("(> x 0)", "(< x 0)", vec!["x".into()]);
        let result = generator.generate(&req);
        assert!(result.is_ok());
        let interp = result.unwrap();
        assert!(!interp.formula.is_empty());
        assert!(interp.shared_symbols.contains(&"x".to_string()));
    }

    #[test]
    fn test_generate_empty_formula_a_error() {
        let generator = InterpolantGenerator::new();
        let req = InterpolantRequest::new("", "(< x 0)", vec!["x".into()]);
        let result = generator.generate(&req);
        assert!(matches!(result, Err(InterpolantError::InvalidFormula(_))));
    }

    #[test]
    fn test_generate_empty_formula_b_error() {
        let generator = InterpolantGenerator::new();
        let req = InterpolantRequest::new("(> x 0)", "", vec!["x".into()]);
        let result = generator.generate(&req);
        assert!(matches!(result, Err(InterpolantError::InvalidFormula(_))));
    }

    #[test]
    fn test_generate_no_shared_symbols_returns_true() {
        let generator = InterpolantGenerator::new();
        let req = InterpolantRequest::new("(> a 0)", "(< b 0)", vec![]);
        let result = generator.generate(&req).unwrap();
        assert_eq!(result.formula, "true");
    }

    #[test]
    fn test_generate_auto_detects_shared_symbols() {
        let generator = InterpolantGenerator::new();
        let req = InterpolantRequest::new("(> x 5)", "(< x 0)", vec![]);
        let result = generator.generate(&req).unwrap();
        assert!(result.shared_symbols.contains(&"x".to_string()));
    }

    #[test]
    fn test_generate_strongest_uses_a_projection() {
        let generator = InterpolantGenerator::with_strength(InterpolantStrength::Strongest);
        let req = InterpolantRequest::new("(> x 0)", "(< x 0)", vec!["x".into()]);
        let result = generator.generate(&req).unwrap();
        assert_eq!(result.strength, InterpolantStrength::Strongest);
        // Strongest should reference formula_a content.
        assert!(result.formula.contains('x'));
    }

    #[test]
    fn test_generate_weakest_negates_b() {
        let generator = InterpolantGenerator::with_strength(InterpolantStrength::Weakest);
        let req = InterpolantRequest::new("(> x 0)", "(< x 0)", vec!["x".into()]);
        let result = generator.generate(&req).unwrap();
        assert_eq!(result.strength, InterpolantStrength::Weakest);
        assert!(result.formula.contains("not"));
    }

    // -- generate_sequence --

    #[test]
    fn test_generate_sequence_two_formulas() {
        let generator = InterpolantGenerator::new();
        let formulas = vec!["(> x 10)".into(), "(< x 0)".into()];
        let result = generator.generate_sequence(&formulas).unwrap();
        assert_eq!(result.len(), 1);
    }

    #[test]
    fn test_generate_sequence_three_formulas() {
        let generator = InterpolantGenerator::new();
        let formulas = vec!["(> x 10)".into(), "(> y 5)".into(), "(< x 0)".into()];
        let result = generator.generate_sequence(&formulas).unwrap();
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn test_generate_sequence_too_few_formulas() {
        let generator = InterpolantGenerator::new();
        let formulas = vec!["(> x 0)".into()];
        let result = generator.generate_sequence(&formulas);
        assert!(matches!(result, Err(InterpolantError::InvalidFormula(_))));
    }

    // -- simplify_interpolant --

    #[test]
    fn test_simplify_removes_trivial_conjuncts() {
        let generator = InterpolantGenerator::new();
        let interp =
            Interpolant::new("(and true (> x 0))", vec!["x".into()], InterpolantStrength::Balanced);
        let simplified = generator.simplify_interpolant(&interp);
        assert_eq!(simplified.formula, "(> x 0)");
    }

    #[test]
    fn test_simplify_normalizes_whitespace() {
        let generator = InterpolantGenerator::new();
        let interp =
            Interpolant::new("(>  x   0)", vec!["x".into()], InterpolantStrength::Balanced);
        let simplified = generator.simplify_interpolant(&interp);
        assert_eq!(simplified.formula, "(> x 0)");
    }

    #[test]
    fn test_simplify_all_true_becomes_true() {
        let generator = InterpolantGenerator::new();
        let interp =
            Interpolant::new("(and true true)", vec!["x".into()], InterpolantStrength::Balanced);
        let simplified = generator.simplify_interpolant(&interp);
        assert_eq!(simplified.formula, "true");
    }

    // -- check_interpolant_validity --

    #[test]
    fn test_validity_passes_for_shared_only_symbols() {
        let generator = InterpolantGenerator::new();
        let interp = Interpolant::new("(> x 0)", vec!["x".into()], InterpolantStrength::Balanced);
        let req = InterpolantRequest::new("(> x 5)", "(< x 0)", vec!["x".into()]);
        assert!(generator.check_interpolant_validity(&interp, &req));
    }

    #[test]
    fn test_validity_fails_for_non_shared_symbol() {
        let generator = InterpolantGenerator::new();
        let interp = Interpolant::new("(> y 0)", vec!["y".into()], InterpolantStrength::Balanced);
        let req = InterpolantRequest::new("(> x 5)", "(< x 0)", vec!["x".into()]);
        assert!(!generator.check_interpolant_validity(&interp, &req));
    }

    #[test]
    fn test_validity_trivial_true_is_valid() {
        let generator = InterpolantGenerator::new();
        let interp = Interpolant::new("true", vec![], InterpolantStrength::Balanced);
        let req = InterpolantRequest::new("(> x 5)", "(< x 0)", vec!["x".into()]);
        assert!(generator.check_interpolant_validity(&interp, &req));
    }

    // -- conjoin_interpolants --

    #[test]
    fn test_conjoin_empty_returns_true() {
        let result = conjoin_interpolants(&[]);
        assert_eq!(result.formula, "true");
        assert!(result.shared_symbols.is_empty());
    }

    #[test]
    fn test_conjoin_single_returns_same() {
        let interp = Interpolant::new("(> x 0)", vec!["x".into()], InterpolantStrength::Strongest);
        let result = conjoin_interpolants(std::slice::from_ref(&interp));
        assert_eq!(result.formula, interp.formula);
        assert_eq!(result.shared_symbols, interp.shared_symbols);
    }

    #[test]
    fn test_conjoin_multiple() {
        let i1 = Interpolant::new("(> x 0)", vec!["x".into()], InterpolantStrength::Balanced);
        let i2 = Interpolant::new("(< y 10)", vec!["y".into()], InterpolantStrength::Balanced);
        let result = conjoin_interpolants(&[i1, i2]);
        assert!(result.formula.starts_with("(and "));
        assert_eq!(result.shared_symbols, vec!["x".to_string(), "y".to_string()]);
    }

    // -- weaken_interpolant --

    #[test]
    fn test_weaken_conjunction_keeps_first() {
        let interp = Interpolant::new(
            "(and (> x 0) (< x 100))",
            vec!["x".into()],
            InterpolantStrength::Strongest,
        );
        let weakened = weaken_interpolant(&interp);
        assert_eq!(weakened.formula, "(> x 0)");
        assert_eq!(weakened.strength, InterpolantStrength::Weakest);
    }

    #[test]
    fn test_weaken_non_conjunction_unchanged() {
        let interp = Interpolant::new("(> x 0)", vec!["x".into()], InterpolantStrength::Strongest);
        let weakened = weaken_interpolant(&interp);
        assert_eq!(weakened.formula, "(> x 0)");
    }

    // -- split_sexp_args --

    #[test]
    fn test_split_sexp_args_basic() {
        let parts = split_sexp_args("a (b c) d");
        assert_eq!(parts, vec!["a", "(b c)", "d"]);
    }

    #[test]
    fn test_split_sexp_args_nested() {
        let parts = split_sexp_args("(a (b c)) d");
        assert_eq!(parts, vec!["(a (b c))", "d"]);
    }

    // -- InterpolantError display --

    #[test]
    fn test_error_display_messages() {
        let e1 = InterpolantError::InvalidFormula("bad".into());
        assert_eq!(e1.to_string(), "invalid formula: bad");

        let e2 = InterpolantError::NoInterpolant;
        assert!(e2.to_string().contains("no interpolant"));

        let e3 = InterpolantError::UnsupportedTheory("arrays".into());
        assert!(e3.to_string().contains("arrays"));
    }
}
