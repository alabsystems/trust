// trust-strengthen/gate_diagnostics.rs: Diagnostic reporting for structural gate failures
//
// Provides structured diagnostic types for each failure category when spec proposals
// fail the structural gate. Includes severity levels, fix suggestions, and formatted
// output for integration with trust-report.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt;
use std::fmt::Write;

/// Severity of a gate diagnostic.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Severity {
    /// Informational -- spec passed but has a note.
    Info,
    /// Warning -- spec passed but may have issues.
    Warn,
    /// Rejection -- spec failed the gate and must not be applied.
    Reject,
}

impl fmt::Display for Severity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Severity::Info => write!(f, "info"),
            Severity::Warn => write!(f, "warn"),
            Severity::Reject => write!(f, "reject"),
        }
    }
}

/// Category of gate failure.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum DiagnosticKind {
    /// Spec body failed to parse as a valid expression.
    SyntaxError,
    /// Spec references a variable not in scope.
    ScopeViolation,
    /// Spec contains an unsafe construct (assume(false), panic!(), etc.).
    UnsafeContent,
    /// Spec is trivially true (tautology).
    Tautology,
    /// Spec is trivially false or contradicts existing specs.
    Contradiction,
    /// Spec exceeds complexity bounds.
    ComplexityExceeded,
    /// Spec would introduce unsoundness.
    Unsoundness,
    /// Spec body is empty or whitespace-only.
    EmptySpec,
    /// Spec contains side effects or non-pure expressions.
    SideEffect,
    /// Spec weakens verification (e.g., requires(false) makes function unreachable).
    TrivialWeakening,
}

impl fmt::Display for DiagnosticKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DiagnosticKind::SyntaxError => write!(f, "syntax_error"),
            DiagnosticKind::ScopeViolation => write!(f, "scope_violation"),
            DiagnosticKind::UnsafeContent => write!(f, "unsafe_content"),
            DiagnosticKind::Tautology => write!(f, "tautology"),
            DiagnosticKind::Contradiction => write!(f, "contradiction"),
            DiagnosticKind::ComplexityExceeded => write!(f, "complexity_exceeded"),
            DiagnosticKind::Unsoundness => write!(f, "unsoundness"),
            DiagnosticKind::EmptySpec => write!(f, "empty_spec"),
            DiagnosticKind::SideEffect => write!(f, "side_effect"),
            DiagnosticKind::TrivialWeakening => write!(f, "trivial_weakening"),
        }
    }
}

/// A single diagnostic produced by the structural gate.
#[derive(Debug, Clone, PartialEq)]
pub struct GateDiagnostic {
    /// Severity level.
    pub severity: Severity,
    /// What kind of issue was detected.
    pub kind: DiagnosticKind,
    /// Human-readable message explaining the failure.
    pub message: String,
    /// The spec body (or fragment) that triggered the diagnostic.
    pub span: String,
    /// Optional suggestion for how to fix the issue.
    pub suggestion: Option<FixSuggestion>,
}

impl GateDiagnostic {
    /// Create a new rejection diagnostic.
    #[must_use]
    pub fn reject(
        kind: DiagnosticKind,
        message: impl Into<String>,
        span: impl Into<String>,
    ) -> Self {
        Self {
            severity: Severity::Reject,
            kind,
            message: message.into(),
            span: span.into(),
            suggestion: None,
        }
    }

    /// Create a new warning diagnostic.
    #[must_use]
    pub fn warn(kind: DiagnosticKind, message: impl Into<String>, span: impl Into<String>) -> Self {
        Self {
            severity: Severity::Warn,
            kind,
            message: message.into(),
            span: span.into(),
            suggestion: None,
        }
    }

    /// Create a new informational diagnostic.
    #[must_use]
    pub fn info(kind: DiagnosticKind, message: impl Into<String>, span: impl Into<String>) -> Self {
        Self {
            severity: Severity::Info,
            kind,
            message: message.into(),
            span: span.into(),
            suggestion: None,
        }
    }

    /// Attach a fix suggestion to this diagnostic.
    #[must_use]
    pub fn with_suggestion(mut self, suggestion: FixSuggestion) -> Self {
        self.suggestion = Some(suggestion);
        self
    }

    /// Whether this diagnostic is a hard rejection.
    #[must_use]
    pub fn is_rejection(&self) -> bool {
        self.severity == Severity::Reject
    }
}

impl fmt::Display for GateDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}] {}: {}", self.severity, self.kind, self.message)?;
        if !self.span.is_empty() {
            write!(f, " (in `{}`)", self.span)?;
        }
        if let Some(ref suggestion) = self.suggestion {
            write!(f, " -- suggestion: {}", suggestion.description)?;
        }
        Ok(())
    }
}

/// A suggested fix when a spec fails the gate.
#[derive(Debug, Clone, PartialEq)]
pub struct FixSuggestion {
    /// Human-readable description of the fix.
    pub description: String,
    /// The replacement spec body, if applicable.
    pub replacement: Option<String>,
}

impl FixSuggestion {
    /// Create a new fix suggestion.
    #[must_use]
    pub fn new(description: impl Into<String>) -> Self {
        Self { description: description.into(), replacement: None }
    }

    /// Create a fix suggestion with a replacement spec body.
    #[must_use]
    pub fn with_replacement(
        description: impl Into<String>,
        replacement: impl Into<String>,
    ) -> Self {
        Self { description: description.into(), replacement: Some(replacement.into()) }
    }
}

/// Produce a fix suggestion for a given diagnostic kind.
#[must_use]
pub fn suggest_fix(kind: &DiagnosticKind, spec_body: &str) -> Option<FixSuggestion> {
    match kind {
        DiagnosticKind::EmptySpec => {
            Some(FixSuggestion::new("Provide a non-empty boolean expression as the spec body"))
        }
        DiagnosticKind::Tautology => {
            // If it's x == x, suggest removing
            if spec_body.contains("==") {
                let parts: Vec<&str> = spec_body.splitn(2, "==").collect();
                if parts.len() == 2 && parts[0].trim() == parts[1].trim() {
                    return Some(FixSuggestion::new(
                        "Remove tautological spec; both sides of == are identical",
                    ));
                }
            }
            Some(FixSuggestion::new("Replace with a meaningful constraint that restricts behavior"))
        }
        DiagnosticKind::UnsafeContent => {
            if spec_body.contains("assume(false)") || spec_body.contains("assume( false)") {
                return Some(FixSuggestion::with_replacement(
                    "Replace assume(false) with a meaningful precondition",
                    "true /* replace with actual precondition */",
                ));
            }
            if spec_body.contains("panic!") {
                return Some(FixSuggestion::new(
                    "Remove panic!() -- specs must be pure boolean expressions",
                ));
            }
            if spec_body.contains("unreachable!") {
                return Some(FixSuggestion::new(
                    "Remove unreachable!() -- specs must be pure boolean expressions",
                ));
            }
            Some(FixSuggestion::new("Remove unsafe constructs from the spec body"))
        }
        DiagnosticKind::Contradiction => Some(FixSuggestion::new(
            "Check for contradictions with existing specs; ensure requires(false) is not used",
        )),
        DiagnosticKind::TrivialWeakening => Some(FixSuggestion::new(
            "requires(false) makes the function trivially correct by making it unreachable; \
             use a meaningful precondition instead",
        )),
        DiagnosticKind::ComplexityExceeded => {
            Some(FixSuggestion::new("Simplify the spec or break it into multiple simpler specs"))
        }
        DiagnosticKind::SyntaxError => Some(FixSuggestion::new(
            "Check for unbalanced parentheses, missing operators, or invalid identifiers",
        )),
        DiagnosticKind::ScopeViolation => {
            Some(FixSuggestion::new("Only reference function parameters and return value in specs"))
        }
        DiagnosticKind::SideEffect => Some(FixSuggestion::new(
            "Specs must be pure boolean expressions with no side effects (no function calls, \
             assignments, or I/O)",
        )),
        DiagnosticKind::Unsoundness => Some(FixSuggestion::new(
            "Remove constructs that could introduce unsoundness (e.g., assuming false premises)",
        )),
    }
}

/// Format a collection of diagnostics into a human-readable report.
#[must_use]
pub fn format_diagnostics(diagnostics: &[GateDiagnostic]) -> String {
    if diagnostics.is_empty() {
        return "No diagnostics.".to_string();
    }

    let rejections: Vec<_> =
        diagnostics.iter().filter(|d| d.severity == Severity::Reject).collect();
    let warnings: Vec<_> = diagnostics.iter().filter(|d| d.severity == Severity::Warn).collect();
    let infos: Vec<_> = diagnostics.iter().filter(|d| d.severity == Severity::Info).collect();

    let mut out = String::new();
    let _ = writeln!(
        out,
        "Gate diagnostics: {} rejection(s), {} warning(s), {} info(s)",
        rejections.len(),
        warnings.len(),
        infos.len(),
    );

    for d in diagnostics {
        let _ = writeln!(out, "  {d}");
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_severity_ordering() {
        assert!(Severity::Info < Severity::Warn);
        assert!(Severity::Warn < Severity::Reject);
    }

    #[test]
    fn test_severity_display() {
        assert_eq!(Severity::Info.to_string(), "info");
        assert_eq!(Severity::Warn.to_string(), "warn");
        assert_eq!(Severity::Reject.to_string(), "reject");
    }

    #[test]
    fn test_diagnostic_kind_display() {
        assert_eq!(DiagnosticKind::SyntaxError.to_string(), "syntax_error");
        assert_eq!(DiagnosticKind::Tautology.to_string(), "tautology");
        assert_eq!(DiagnosticKind::UnsafeContent.to_string(), "unsafe_content");
    }

    #[test]
    fn test_reject_diagnostic_creation() {
        let d = GateDiagnostic::reject(
            DiagnosticKind::UnsafeContent,
            "contains assume(false)",
            "assume(false)",
        );
        assert_eq!(d.severity, Severity::Reject);
        assert!(d.is_rejection());
        assert!(d.suggestion.is_none());
    }

    #[test]
    fn test_warn_diagnostic_creation() {
        let d = GateDiagnostic::warn(DiagnosticKind::Tautology, "spec is always true", "true");
        assert_eq!(d.severity, Severity::Warn);
        assert!(!d.is_rejection());
    }

    #[test]
    fn test_info_diagnostic_creation() {
        let d = GateDiagnostic::info(
            DiagnosticKind::ComplexityExceeded,
            "spec is complex but acceptable",
            "a && b && c",
        );
        assert_eq!(d.severity, Severity::Info);
        assert!(!d.is_rejection());
    }

    #[test]
    fn test_diagnostic_with_suggestion() {
        let d = GateDiagnostic::reject(DiagnosticKind::EmptySpec, "empty spec body", "")
            .with_suggestion(FixSuggestion::new("provide a boolean expression"));
        assert!(d.suggestion.is_some());
        assert_eq!(
            d.suggestion.as_ref().map(|s| s.description.as_str()),
            Some("provide a boolean expression")
        );
    }

    #[test]
    fn test_diagnostic_display_with_span() {
        let d = GateDiagnostic::reject(
            DiagnosticKind::UnsafeContent,
            "contains panic!()",
            "panic!(\"bad\")",
        );
        let s = d.to_string();
        assert!(s.contains("[reject]"));
        assert!(s.contains("unsafe_content"));
        assert!(s.contains("panic!"));
    }

    #[test]
    fn test_diagnostic_display_empty_span() {
        let d = GateDiagnostic::reject(DiagnosticKind::EmptySpec, "empty spec body", "");
        let s = d.to_string();
        assert!(!s.contains("(in "));
    }

    #[test]
    fn test_diagnostic_display_with_suggestion() {
        let d = GateDiagnostic::reject(DiagnosticKind::Tautology, "always true", "true")
            .with_suggestion(FixSuggestion::new("use meaningful constraint"));
        let s = d.to_string();
        assert!(s.contains("suggestion:"));
        assert!(s.contains("meaningful constraint"));
    }

    #[test]
    fn test_fix_suggestion_new() {
        let s = FixSuggestion::new("do something");
        assert_eq!(s.description, "do something");
        assert!(s.replacement.is_none());
    }

    #[test]
    fn test_fix_suggestion_with_replacement() {
        let s = FixSuggestion::with_replacement("replace X with Y", "Y");
        assert_eq!(s.description, "replace X with Y");
        assert_eq!(s.replacement, Some("Y".to_string()));
    }

    #[test]
    fn test_suggest_fix_empty_spec() {
        let fix = suggest_fix(&DiagnosticKind::EmptySpec, "");
        assert!(fix.is_some());
        assert!(fix.as_ref().is_some_and(|f| f.description.contains("non-empty")));
    }

    #[test]
    fn test_suggest_fix_tautology_eq() {
        let fix = suggest_fix(&DiagnosticKind::Tautology, "x == x");
        assert!(fix.is_some());
        assert!(fix.as_ref().is_some_and(|f| f.description.contains("identical")));
    }

    #[test]
    fn test_suggest_fix_tautology_generic() {
        let fix = suggest_fix(&DiagnosticKind::Tautology, "true");
        assert!(fix.is_some());
        assert!(fix.as_ref().is_some_and(|f| f.description.contains("meaningful")));
    }

    #[test]
    fn test_suggest_fix_unsafe_assume_false() {
        let fix = suggest_fix(&DiagnosticKind::UnsafeContent, "assume(false)");
        assert!(fix.is_some());
        let f = fix.as_ref().expect("should have fix");
        assert!(f.replacement.is_some());
    }

    #[test]
    fn test_suggest_fix_unsafe_panic() {
        let fix = suggest_fix(&DiagnosticKind::UnsafeContent, "panic!(\"oops\")");
        assert!(fix.is_some());
        assert!(fix.as_ref().is_some_and(|f| f.description.contains("panic!")));
    }

    #[test]
    fn test_suggest_fix_unsafe_unreachable() {
        let fix = suggest_fix(&DiagnosticKind::UnsafeContent, "unreachable!()");
        assert!(fix.is_some());
        assert!(fix.as_ref().is_some_and(|f| f.description.contains("unreachable!")));
    }

    #[test]
    fn test_suggest_fix_contradiction() {
        let fix = suggest_fix(&DiagnosticKind::Contradiction, "false");
        assert!(fix.is_some());
    }

    #[test]
    fn test_suggest_fix_trivial_weakening() {
        let fix = suggest_fix(&DiagnosticKind::TrivialWeakening, "false");
        assert!(fix.is_some());
        assert!(fix.as_ref().is_some_and(|f| f.description.contains("requires(false)")));
    }

    #[test]
    fn test_suggest_fix_complexity() {
        let fix = suggest_fix(&DiagnosticKind::ComplexityExceeded, "a && b && c && d && e");
        assert!(fix.is_some());
        assert!(fix.as_ref().is_some_and(|f| f.description.contains("implify")));
    }

    #[test]
    fn test_suggest_fix_syntax_error() {
        let fix = suggest_fix(&DiagnosticKind::SyntaxError, "((x + y");
        assert!(fix.is_some());
        assert!(fix.as_ref().is_some_and(|f| f.description.contains("parentheses")));
    }

    #[test]
    fn test_suggest_fix_scope_violation() {
        let fix = suggest_fix(&DiagnosticKind::ScopeViolation, "global_var > 0");
        assert!(fix.is_some());
    }

    #[test]
    fn test_suggest_fix_side_effect() {
        let fix = suggest_fix(&DiagnosticKind::SideEffect, "foo()");
        assert!(fix.is_some());
        assert!(fix.as_ref().is_some_and(|f| f.description.contains("pure")));
    }

    #[test]
    fn test_suggest_fix_unsoundness() {
        let fix = suggest_fix(&DiagnosticKind::Unsoundness, "assume(false)");
        assert!(fix.is_some());
    }

    #[test]
    fn test_format_diagnostics_empty() {
        let s = format_diagnostics(&[]);
        assert_eq!(s, "No diagnostics.");
    }

    #[test]
    fn test_format_diagnostics_mixed() {
        let diagnostics = vec![
            GateDiagnostic::reject(DiagnosticKind::UnsafeContent, "bad", "panic!()"),
            GateDiagnostic::warn(DiagnosticKind::Tautology, "always true", "true"),
            GateDiagnostic::info(DiagnosticKind::ComplexityExceeded, "complex", "a && b"),
        ];
        let s = format_diagnostics(&diagnostics);
        assert!(s.contains("1 rejection(s)"));
        assert!(s.contains("1 warning(s)"));
        assert!(s.contains("1 info(s)"));
    }

    #[test]
    fn test_format_diagnostics_multiple_rejections() {
        let diagnostics = vec![
            GateDiagnostic::reject(DiagnosticKind::UnsafeContent, "bad1", "a"),
            GateDiagnostic::reject(DiagnosticKind::Tautology, "bad2", "b"),
        ];
        let s = format_diagnostics(&diagnostics);
        assert!(s.contains("2 rejection(s)"));
        assert!(s.contains("0 warning(s)"));
    }
}
