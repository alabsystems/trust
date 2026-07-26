// trust-strengthen/spec_proposal.rs: Structured spec proposals for source annotation
//
// Represents inferred specifications as structured proposals that can be
// rendered back to source as first-class signature/loop clauses.
// Each proposal carries provenance (which LLM iteration, confidence, rationale)
// and validation status against the function signature.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt;

use crate::proposer::ProposalKind;

/// The kind of specification being proposed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpecKind {
    /// `requires ...` -- precondition on function inputs.
    Requires,
    /// `ensures ...` -- postcondition on function output.
    Ensures,
    /// `invariant ...` -- loop invariant.
    Invariant,
}

impl fmt::Display for SpecKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Requires => write!(f, "requires"),
            Self::Ensures => write!(f, "ensures"),
            Self::Invariant => write!(f, "invariant"),
        }
    }
}

/// A structured specification proposal ready to be rendered to source.
#[derive(Debug, Clone)]
pub struct SpecProposal {
    /// The target function's fully qualified path.
    pub function_path: String,
    /// The target function's short name.
    pub function_name: String,
    /// What kind of first-class clause.
    pub kind: SpecKind,
    /// The spec expression body (without a clause keyword).
    pub spec_body: String,
    /// Confidence score (0.0-1.0).
    pub confidence: f64,
    /// Human-readable rationale explaining why this spec was proposed.
    pub rationale: String,
    /// Which feedback loop iteration produced this proposal.
    pub iteration: usize,
    /// Whether this proposal has been validated against the function signature.
    pub validated: bool,
    /// Validation errors, if any.
    pub validation_errors: Vec<String>,
}

impl SpecProposal {
    /// Render this proposal as a first-class Trust clause.
    ///
    /// Example: `requires a <= usize::MAX - b`
    #[must_use]
    pub fn to_clause(&self) -> String {
        format!("{} {}", self.kind, self.spec_body.trim())
    }

    /// Render as a suggestion comment block for display.
    #[must_use]
    pub fn to_suggestion(&self) -> String {
        format!(
            "// Suggested by trust-strengthen (confidence: {:.0}%, iteration {})\n\
             // Rationale: {}\n\
             {}",
            self.confidence * 100.0,
            self.iteration,
            self.rationale,
            self.to_clause(),
        )
    }

    /// Convert from a `ProposalKind` and metadata.
    #[must_use]
    pub fn from_proposal_kind(
        kind: &ProposalKind,
        function_path: &str,
        function_name: &str,
        confidence: f64,
        rationale: &str,
        iteration: usize,
    ) -> Option<Self> {
        let (spec_kind, spec_body) = match kind {
            ProposalKind::AddPrecondition { spec_body } => (SpecKind::Requires, spec_body.clone()),
            ProposalKind::AddPostcondition { spec_body } => (SpecKind::Ensures, spec_body.clone()),
            ProposalKind::AddInvariant { spec_body } => (SpecKind::Invariant, spec_body.clone()),
            // SafeArithmetic, AddBoundsCheck, AddNonZeroCheck are code changes, not specs
            _ => return None,
        };

        Some(Self {
            function_path: function_path.to_string(),
            function_name: function_name.to_string(),
            kind: spec_kind,
            spec_body,
            confidence,
            rationale: rationale.to_string(),
            iteration,
            validated: false,
            validation_errors: Vec::new(),
        })
    }
}

/// Validate a spec proposal against a function's parameter names and types.
///
/// Checks that variable names referenced in the spec body actually exist
/// as parameters of the function. Returns a list of validation errors.
#[must_use]
pub fn validate_spec(
    proposal: &SpecProposal,
    param_names: &[String],
    return_type: Option<&str>,
) -> Vec<String> {
    let mut errors = Vec::new();
    let body = &proposal.spec_body;

    // Check that "result" is only used in ensures clauses
    if body.contains("result") && proposal.kind != SpecKind::Ensures {
        errors.push(format!("\"result\" used in {} clause (only valid in ensures)", proposal.kind));
    }

    // Check that ensures clauses for void functions don't reference result
    if proposal.kind == SpecKind::Ensures && return_type.is_none() && body.contains("result") {
        errors.push("\"result\" used in ensures clause but function returns ()".to_string());
    }

    // Check for obviously malformed expressions
    if body.trim().is_empty() {
        errors.push("empty spec body".to_string());
    }

    // Compatibility spellings are input-only. Do not let an inference lane
    // regenerate them as native source proposals.
    if body.contains("old(") || body.contains("old (") {
        errors.push(
            "`old(...)` is not native syntax; use entry names and `result`/primed outputs"
                .to_string(),
        );
    }
    if body.contains("forall |") || body.contains("exists |") {
        errors.push("closure-shaped quantifiers are not native syntax; use `forall x: T, ...` / `exists x: T, ...`".to_string());
    }

    // Check balanced parentheses
    let mut paren_depth: i32 = 0;
    for ch in body.chars() {
        match ch {
            '(' => paren_depth += 1,
            ')' => paren_depth -= 1,
            _ => {}
        }
        if paren_depth < 0 {
            errors.push("unbalanced parentheses in spec body".to_string());
            break;
        }
    }
    if paren_depth > 0 {
        errors.push("unbalanced parentheses in spec body".to_string());
    }

    // Warn if spec references identifiers that are not parameters
    // (heuristic: extract word-like tokens and check against params)
    if !param_names.is_empty() {
        let tokens = extract_identifiers(body);
        let known: Vec<&str> = param_names.iter().map(|s| s.as_str()).collect();
        // Keywords and common names that are not parameters
        let builtins = [
            "result", "self", "true", "false", "len", "MAX", "MIN", "usize", "u8", "u16", "u32",
            "u64", "u128", "isize", "i8", "i16", "i32", "i64", "i128", "f32", "f64", "bool", "out",
            "forall", "exists", "int", "nat",
        ];
        for token in &tokens {
            if !known.contains(&token.as_str())
                && !builtins.contains(&token.as_str())
                && !token.contains("::")
                && token.len() > 1
            // skip single-char tokens like operators
            {
                // This is a soft warning, not a hard error
                errors.push(format!("identifier \"{token}\" not found in function parameters"));
            }
        }
    }

    errors
}

/// Extract word-like identifiers from a spec expression.
fn extract_identifiers(spec: &str) -> Vec<String> {
    let mut ids = Vec::new();
    let mut current = String::new();

    for ch in spec.chars() {
        if ch.is_alphanumeric() || ch == '_' {
            current.push(ch);
        } else {
            if !current.is_empty() && !current.chars().next().unwrap_or('0').is_ascii_digit() {
                ids.push(std::mem::take(&mut current));
            } else {
                current.clear();
            }
        }
    }
    if !current.is_empty() && !current.chars().next().unwrap_or('0').is_ascii_digit() {
        ids.push(current);
    }

    ids
}

/// Collect all spec proposals for a function and format them as a suggestion block.
#[must_use]
pub fn format_suggestions(proposals: &[SpecProposal]) -> String {
    if proposals.is_empty() {
        return String::new();
    }

    let mut lines = Vec::new();
    let fn_name = proposals.first().map(|p| p.function_name.as_str()).unwrap_or("unknown");

    lines.push(format!("// === Suggested specs for `{fn_name}` ==="));
    for proposal in proposals {
        lines.push(proposal.to_suggestion());
    }
    lines.push("// === End suggestions ===".to_string());

    lines.join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_requires(body: &str, confidence: f64) -> SpecProposal {
        SpecProposal {
            function_path: "test::func".into(),
            function_name: "func".into(),
            kind: SpecKind::Requires,
            spec_body: body.into(),
            confidence,
            rationale: "test rationale".into(),
            iteration: 1,
            validated: false,
            validation_errors: Vec::new(),
        }
    }

    fn make_ensures(body: &str, confidence: f64) -> SpecProposal {
        SpecProposal {
            function_path: "test::func".into(),
            function_name: "func".into(),
            kind: SpecKind::Ensures,
            spec_body: body.into(),
            confidence,
            rationale: "test rationale".into(),
            iteration: 1,
            validated: false,
            validation_errors: Vec::new(),
        }
    }

    // --- SpecKind display ---

    #[test]
    fn test_spec_kind_display() {
        assert_eq!(SpecKind::Requires.to_string(), "requires");
        assert_eq!(SpecKind::Ensures.to_string(), "ensures");
        assert_eq!(SpecKind::Invariant.to_string(), "invariant");
    }

    // --- to_clause ---

    #[test]
    fn test_to_clause_requires() {
        let p = make_requires("a <= usize::MAX - b", 0.9);
        assert_eq!(p.to_clause(), "requires a <= usize::MAX - b");
    }

    #[test]
    fn test_to_clause_ensures() {
        let p = make_ensures("result >= a && result >= b", 0.8);
        assert_eq!(p.to_clause(), "ensures result >= a && result >= b");
    }

    #[test]
    fn test_to_clause_invariant() {
        let p = SpecProposal {
            function_path: "test::f".into(),
            function_name: "f".into(),
            kind: SpecKind::Invariant,
            spec_body: "i < n".into(),
            confidence: 0.7,
            rationale: "loop bound".into(),
            iteration: 2,
            validated: false,
            validation_errors: Vec::new(),
        };
        assert_eq!(p.to_clause(), "invariant i < n");
    }

    // --- to_suggestion ---

    #[test]
    fn test_to_suggestion_format() {
        let p = make_requires("x > 0", 0.85);
        let s = p.to_suggestion();
        assert!(s.contains("confidence: 85%"));
        assert!(s.contains("iteration 1"));
        assert!(s.contains("test rationale"));
        assert!(s.contains("requires x > 0"));
    }

    // --- from_proposal_kind ---

    #[test]
    fn test_from_precondition_kind() {
        let kind = ProposalKind::AddPrecondition { spec_body: "x != 0".into() };
        let p = SpecProposal::from_proposal_kind(&kind, "test::f", "f", 0.9, "div guard", 3);
        assert!(p.is_some());
        let p = p.unwrap();
        assert_eq!(p.kind, SpecKind::Requires);
        assert_eq!(p.spec_body, "x != 0");
        assert_eq!(p.iteration, 3);
    }

    #[test]
    fn test_from_postcondition_kind() {
        let kind = ProposalKind::AddPostcondition { spec_body: "result > 0".into() };
        let p = SpecProposal::from_proposal_kind(&kind, "test::f", "f", 0.8, "positive", 1);
        assert!(p.is_some());
        assert_eq!(p.unwrap().kind, SpecKind::Ensures);
    }

    #[test]
    fn test_from_invariant_kind() {
        let kind = ProposalKind::AddInvariant { spec_body: "i < len".into() };
        let p = SpecProposal::from_proposal_kind(&kind, "test::f", "f", 0.7, "bound", 1);
        assert!(p.is_some());
        assert_eq!(p.unwrap().kind, SpecKind::Invariant);
    }

    #[test]
    fn test_from_non_spec_kind_returns_none() {
        let kind = ProposalKind::SafeArithmetic {
            original: "a + b".into(),
            replacement: "a.checked_add(b)".into(),
        };
        let p = SpecProposal::from_proposal_kind(&kind, "test::f", "f", 0.7, "safe", 1);
        assert!(p.is_none());
    }

    // --- validate_spec ---

    #[test]
    fn test_validate_valid_requires() {
        let p = make_requires("a <= usize::MAX - b", 0.9);
        let errors = validate_spec(&p, &["a".into(), "b".into()], Some("usize"));
        assert!(errors.is_empty(), "should have no errors: {errors:?}");
    }

    #[test]
    fn test_validate_result_in_requires_is_error() {
        let p = make_requires("result > 0", 0.9);
        let errors = validate_spec(&p, &["x".into()], Some("i32"));
        assert!(errors.iter().any(|e| e.contains("result")), "should flag result in requires");
    }

    #[test]
    fn test_validate_result_in_ensures_is_ok() {
        let p = make_ensures("result > 0", 0.9);
        let errors = validate_spec(&p, &["x".into()], Some("i32"));
        // "result" in ensures is fine
        assert!(
            !errors.iter().any(|e| e.contains("\"result\" used in ensures")),
            "result in ensures should be valid"
        );
    }

    #[test]
    fn test_validate_result_in_void_ensures() {
        let p = make_ensures("result > 0", 0.9);
        let errors = validate_spec(&p, &["x".into()], None);
        assert!(
            errors.iter().any(|e| e.contains("returns ()")),
            "should flag result for void function"
        );
    }

    #[test]
    fn test_validate_empty_body() {
        let p = make_requires("", 0.5);
        let errors = validate_spec(&p, &[], None);
        assert!(errors.iter().any(|e| e.contains("empty")));
    }

    #[test]
    fn test_validate_unbalanced_parens() {
        let p = make_requires("(a + b", 0.5);
        let errors = validate_spec(&p, &["a".into(), "b".into()], Some("i32"));
        assert!(errors.iter().any(|e| e.contains("parentheses")));
    }

    #[test]
    fn test_validate_unknown_identifiers() {
        let p = make_requires("xyz > 0", 0.5);
        let errors = validate_spec(&p, &["a".into(), "b".into()], Some("i32"));
        assert!(
            errors.iter().any(|e| e.contains("xyz")),
            "should warn about unknown identifier 'xyz'"
        );
    }

    #[test]
    fn test_validate_known_builtins_not_flagged() {
        let p = make_requires("a <= usize::MAX", 0.9);
        let errors = validate_spec(&p, &["a".into()], Some("usize"));
        // "usize" and "MAX" are builtins, should not be flagged
        assert!(
            !errors.iter().any(|e| e.contains("usize") || e.contains("MAX")),
            "builtins should not be flagged: {errors:?}"
        );
    }

    // --- extract_identifiers ---

    #[test]
    fn test_extract_identifiers_simple() {
        let ids = extract_identifiers("a <= b + c");
        assert!(ids.contains(&"a".into()));
        assert!(ids.contains(&"b".into()));
        assert!(ids.contains(&"c".into()));
    }

    #[test]
    fn test_extract_identifiers_skips_numbers() {
        let ids = extract_identifiers("x > 0 && y < 100");
        assert!(ids.contains(&"x".into()));
        assert!(ids.contains(&"y".into()));
        assert!(!ids.contains(&"0".into()));
        assert!(!ids.contains(&"100".into()));
    }

    #[test]
    fn test_extract_identifiers_with_underscores() {
        let ids = extract_identifiers("my_var != other_var");
        assert!(ids.contains(&"my_var".into()));
        assert!(ids.contains(&"other_var".into()));
    }

    // --- format_suggestions ---

    #[test]
    fn test_format_suggestions_empty() {
        assert_eq!(format_suggestions(&[]), "");
    }

    #[test]
    fn test_format_suggestions_multiple() {
        let proposals = vec![make_requires("a > 0", 0.9), make_ensures("result > 0", 0.8)];
        let text = format_suggestions(&proposals);
        assert!(text.contains("Suggested specs for `func`"));
        assert!(text.contains("requires a > 0"));
        assert!(text.contains("ensures result > 0"));
        assert!(text.contains("End suggestions"));
    }
}
