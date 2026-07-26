// trust-report/diagnostics.rs: Rich rustc-style verification diagnostics
//
// Formats verification failures as rustc-style error messages with error codes,
// source locations, descriptions, and suggested fixes.
//
// Example output:
//   error[E-TRUST-001]: possible arithmetic overflow
//     --> src/midpoint.rs:5:5
//     |
//   5 |     a + b
//     |     ^^^^^ Add on (usize, usize) may overflow
//     |
//     = help: use `checked_add()` or add a bounds check before this operation
//     = note: counterexample: a = 18446744073709551615, b = 1
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt::Write;

use trust_types::{
    FunctionProofReport, JsonProofReport, ObligationOutcome, ObligationReport, SourceSpan,
};

// ---------------------------------------------------------------------------
// Error code catalog
// ---------------------------------------------------------------------------

/// Structured error code for a verification diagnostic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ErrorCode {
    /// Numeric part of the code (e.g., 1 for E-TRUST-001).
    pub number: u16,
    /// Short human-readable title.
    pub title: &'static str,
}

impl ErrorCode {
    /// Format as `E-TRUST-NNN`.
    #[must_use]
    pub fn code(&self) -> String {
        format!("E-TRUST-{:03}", self.number)
    }
}

impl std::fmt::Display for ErrorCode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "E-TRUST-{:03}", self.number)
    }
}

// Error code constants — one per VcKind category.
pub const E_ARITHMETIC_OVERFLOW: ErrorCode =
    ErrorCode { number: 1, title: "possible arithmetic overflow" };
pub const E_SHIFT_OVERFLOW: ErrorCode = ErrorCode { number: 2, title: "possible shift overflow" };
pub const E_DIVISION_BY_ZERO: ErrorCode =
    ErrorCode { number: 3, title: "possible division by zero" };
pub const E_REMAINDER_BY_ZERO: ErrorCode =
    ErrorCode { number: 4, title: "possible remainder by zero" };
pub const E_INDEX_OUT_OF_BOUNDS: ErrorCode =
    ErrorCode { number: 5, title: "possible index out of bounds" };
pub const E_SLICE_BOUNDS_CHECK: ErrorCode =
    ErrorCode { number: 6, title: "possible slice bounds violation" };
pub const E_ASSERTION_FAILURE: ErrorCode = ErrorCode { number: 7, title: "assertion may fail" };
pub const E_PRECONDITION: ErrorCode = ErrorCode { number: 8, title: "precondition may not hold" };
pub const E_POSTCONDITION: ErrorCode = ErrorCode { number: 9, title: "postcondition may not hold" };
pub const E_CAST_OVERFLOW: ErrorCode = ErrorCode { number: 10, title: "possible cast overflow" };
pub const E_NEGATION_OVERFLOW: ErrorCode =
    ErrorCode { number: 11, title: "possible negation overflow" };
pub const E_UNREACHABLE: ErrorCode =
    ErrorCode { number: 12, title: "unreachable code may be reached" };
pub const E_DEAD_STATE: ErrorCode = ErrorCode { number: 13, title: "dead state reachable" };
pub const E_DEADLOCK: ErrorCode = ErrorCode { number: 14, title: "possible deadlock" };
pub const E_TEMPORAL: ErrorCode = ErrorCode { number: 15, title: "temporal property violation" };
pub const E_LIVENESS: ErrorCode = ErrorCode { number: 16, title: "liveness property violation" };
pub const E_FAIRNESS: ErrorCode = ErrorCode { number: 17, title: "fairness constraint violation" };
pub const E_TAINT_VIOLATION: ErrorCode = ErrorCode { number: 18, title: "taint policy violation" };
pub const E_REFINEMENT_VIOLATION: ErrorCode =
    ErrorCode { number: 19, title: "refinement violation" };
pub const E_RESILIENCE_VIOLATION: ErrorCode =
    ErrorCode { number: 20, title: "resilience violation" };
pub const E_PROTOCOL_VIOLATION: ErrorCode = ErrorCode { number: 21, title: "protocol violation" };
pub const E_NON_TERMINATION: ErrorCode =
    ErrorCode { number: 22, title: "possible non-termination" };
pub const E_BINARY_COPY_SINK_LENGTH: ErrorCode =
    ErrorCode { number: 23, title: "binary copy-sink length violation" };
pub const E_UNSUPPORTED_BINARY_SEMANTICS: ErrorCode =
    ErrorCode { number: 24, title: "unsupported binary semantics" };

/// Map an obligation kind tag to its error code.
#[must_use]
pub fn error_code_for_kind(kind: &str) -> ErrorCode {
    if kind.starts_with("arithmetic_overflow") {
        E_ARITHMETIC_OVERFLOW
    } else if kind.starts_with("shift_overflow") {
        E_SHIFT_OVERFLOW
    } else {
        match kind {
            "division_by_zero" => E_DIVISION_BY_ZERO,
            "remainder_by_zero" => E_REMAINDER_BY_ZERO,
            "index_out_of_bounds" => E_INDEX_OUT_OF_BOUNDS,
            "slice_bounds_check" => E_SLICE_BOUNDS_CHECK,
            "assertion" => E_ASSERTION_FAILURE,
            "precondition" => E_PRECONDITION,
            "postcondition" => E_POSTCONDITION,
            "cast_overflow" => E_CAST_OVERFLOW,
            "negation_overflow" => E_NEGATION_OVERFLOW,
            "unreachable" => E_UNREACHABLE,
            "dead_state" => E_DEAD_STATE,
            "deadlock" => E_DEADLOCK,
            "temporal" => E_TEMPORAL,
            "liveness" => E_LIVENESS,
            "fairness" => E_FAIRNESS,
            "taint_violation" => E_TAINT_VIOLATION,
            "refinement_violation" => E_REFINEMENT_VIOLATION,
            "resilience_violation" => E_RESILIENCE_VIOLATION,
            "protocol_violation" => E_PROTOCOL_VIOLATION,
            "non_termination" => E_NON_TERMINATION,
            "binary_copy_sink_length_violation" => E_BINARY_COPY_SINK_LENGTH,
            "unsupported_mir"
            | "aarch64_atomic_acquire_ordering_unsupported"
            | "aarch64_atomic_release_ordering_unsupported"
            | "aarch64_atomic_semantics_unsupported"
            | "aarch64_exclusive_monitor_unsupported"
            | "aarch64_exclusive_monitor_status_unsupported" => E_UNSUPPORTED_BINARY_SEMANTICS,
            // Unknown kinds fall back to assertion
            _ => E_ASSERTION_FAILURE,
        }
    }
}

/// Suggested fix for a given obligation kind tag.
#[must_use]
pub fn suggested_fix(kind: &str) -> &'static str {
    if kind.starts_with("arithmetic_overflow") {
        "use checked arithmetic (e.g., `checked_add()`) or add a bounds check"
    } else if kind.starts_with("shift_overflow") {
        "ensure the shift amount is less than the bit width of the type"
    } else {
        match kind {
            "division_by_zero" => "add a zero check before dividing (e.g., `if divisor != 0`)",
            "remainder_by_zero" => "add a zero check before the remainder operation",
            "index_out_of_bounds" => {
                "add a bounds check or use `.get()` instead of direct indexing"
            }
            "slice_bounds_check" => "verify slice indices are within range before slicing",
            "assertion" => "review the assertion condition and ensure it holds for all inputs",
            "precondition" => {
                "add a function-signature `requires <predicate>` clause, or validate inputs"
            }
            "postcondition" => {
                "add a function-signature `ensures <predicate>` clause, or fix the implementation"
            }
            "cast_overflow" => "use `try_into()` or add a range check before casting",
            "negation_overflow" => "check for minimum value before negation (e.g., `i32::MIN`)",
            "unreachable" => "remove the unreachable annotation or fix the control flow",
            "dead_state" => "remove the dead state or add a transition out of it",
            "deadlock" => "review lock ordering and ensure all locks are released",
            "temporal" => "review the temporal property and fix the state machine",
            "liveness" => "ensure progress is guaranteed (add fairness or fix starvation)",
            "fairness" => "ensure the fairness constraint is satisfiable",
            "taint_violation" => "sanitize the tainted data before it reaches the sink",
            "refinement_violation" => "fix the implementation to match the specification",
            "resilience_violation" => "add error handling for the external service failure mode",
            "protocol_violation" => "fix the protocol implementation to match the specification",
            "non_termination" => {
                "for recursion, add a function-signature `decreases <measure>` clause; for loops, add a loop-local `decreases <measure>` clause and make the progress step unconditional, or restructure the loop"
            }
            "binary_copy_sink_length_violation" => {
                "prove the copy length is within the destination capacity or add an explicit bounds check"
            }
            "copy_bounds_violation" => {
                "bounds-check the copy/slice count against the source and destination allocation sizes before the unchecked raw copy"
            }
            "externally_mutable_allocation_bounds" => {
                "re-validate the captured length against the live backing size before each access (a concurrent truncation makes a once-captured length unsound: SIGBUS / out-of-bounds read)"
            }
            "aarch64_atomic_acquire_ordering_unsupported"
            | "aarch64_atomic_release_ordering_unsupported" => {
                "provide proof-consumed ordering, synchronization-edge, thread-identity, and happens-before witnesses"
            }
            "aarch64_exclusive_monitor_unsupported"
            | "aarch64_exclusive_monitor_status_unsupported" => {
                "provide proof-consumed exclusive-monitor reservation, invalidation, thread-identity, and status witnesses"
            }
            "aarch64_atomic_semantics_unsupported" | "unsupported_mir" => {
                "add an exact proof consumer for the unsupported MIR/binary semantics"
            }
            _ => "review the verification condition and fix the code",
        }
    }
}

/// Rich, AI-actionable guidance for an obligation: the structured remediation
/// (must-hold property, failure mode, ranked source fixes, and a proof sketch)
/// keyed off the obligation *kind* itself rather than a string tag.
///
/// This is the structured complement to [`suggested_fix`]: where that returns a
/// single generic sentence, this returns the full
/// [`trust_types::AgenticGuidance`] an AI coding loop can act on. Callers with a
/// solver counterexample should enrich the result via
/// [`trust_types::AgenticGuidance::with_counterexample`]. Returns `None` when
/// Trust has no specific structured guidance for the kind.
#[must_use]
pub fn rich_guidance(kind: &trust_types::VcKind) -> Option<trust_types::AgenticGuidance> {
    kind.agentic_guidance()
}

#[cfg(test)]
mod guidance_tests {
    use super::rich_guidance;

    #[test]
    fn rich_guidance_surfaces_structured_remediation_for_new_classes() {
        let g = rich_guidance(&trust_types::VcKind::ExternallyMutableAllocationBounds {
            allocation_kind: "mmap_file".into(),
            live_size: "live_file_len".into(),
            detail: String::new(),
        })
        .expect("externally-mutable bounds obligation must carry structured guidance");
        assert_eq!(g.suggested_fixes[0].kind, "revalidate_length");

        let c = rich_guidance(&trust_types::VcKind::CopyBoundsViolation {
            callee: "copy_nonoverlapping".into(),
            direction: "dst".into(),
            detail: String::new(),
        })
        .expect("copy bounds obligation must carry structured guidance");
        assert_eq!(c.suggested_fixes[0].kind, "bounds_check");
    }
}

// ---------------------------------------------------------------------------
// DiagnosticFormatter
// ---------------------------------------------------------------------------

/// Formats verification results as rustc-style diagnostic messages.
///
/// Produces output like:
/// ```text
/// error[E-TRUST-001]: possible arithmetic overflow
///   --> src/midpoint.rs:5:5
///   = help: use checked arithmetic (e.g., `checked_add()`) or add a bounds check
///   = note: counterexample: a = 18446744073709551615, b = 1
/// ```
pub struct DiagnosticFormatter {
    /// Whether to include suggested fixes in the output.
    include_help: bool,
    /// Whether to include counterexample details.
    include_counterexamples: bool,
}

impl Default for DiagnosticFormatter {
    fn default() -> Self {
        Self { include_help: true, include_counterexamples: true }
    }
}

impl DiagnosticFormatter {
    /// Create a new formatter with all options enabled.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Set whether to include `= help:` lines.
    #[must_use]
    pub fn with_help(mut self, include: bool) -> Self {
        self.include_help = include;
        self
    }

    /// Set whether to include counterexample details.
    #[must_use]
    pub fn with_counterexamples(mut self, include: bool) -> Self {
        self.include_counterexamples = include;
        self
    }

    /// Format a single obligation as a rustc-style diagnostic string.
    ///
    /// Only produces output for non-proved obligations (failed, unknown, timeout).
    /// Returns `None` for proved or runtime-checked obligations.
    #[must_use]
    pub fn format_obligation(&self, obligation: &ObligationReport) -> Option<String> {
        let severity = match &obligation.outcome {
            ObligationOutcome::Proved { .. } | ObligationOutcome::RuntimeChecked { .. } => {
                return None;
            }
            ObligationOutcome::Failed { .. } => "error",
            ObligationOutcome::Unknown { .. } | ObligationOutcome::Timeout { .. } => "warning",
            // a hardened-boundary design mandate is an advisory
            // ("move off a raw/opaque API"), not a proof failure.
            ObligationOutcome::DesignRequirement { .. } => "warning",
            _ => "unknown",
        };

        let error_code = error_code_for_kind(&obligation.kind);
        let mut lines = Vec::new();

        // Header: error[E-TRUST-001]: possible arithmetic overflow
        lines.push(format!("{severity}[{}]: {}", error_code.code(), error_code.title));

        // Location: --> src/midpoint.rs:5:5
        if let Some(loc) = &obligation.location {
            lines.push(format_location(loc));
        }

        // Description from the obligation
        lines.push(format!("   = note: {}", obligation.description));

        // Counterexample for failures
        if self.include_counterexamples
            && let ObligationOutcome::Failed { counterexample: Some(cex) } = &obligation.outcome
        {
            let vars: Vec<String> =
                cex.variables.iter().map(|v| format!("{} = {}", v.name, v.display)).collect();
            if !vars.is_empty() {
                lines.push(format!("   = note: counterexample: {}", vars.join(", ")));
            }
        }

        // Reason for unknown/timeout
        match &obligation.outcome {
            ObligationOutcome::Unknown { reason } => {
                lines.push(format!("   = note: solver returned unknown: {reason}"));
            }
            ObligationOutcome::Timeout { timeout_ms } => {
                lines.push(format!("   = note: solver timed out after {timeout_ms}ms"));
            }
            ObligationOutcome::DesignRequirement { detail } => {
                lines.push(format!("   = note: hardened-boundary design requirement: {detail}"));
            }
            _ => {}
        }

        // Suggested fix
        if self.include_help {
            lines.push(format!("   = help: {}", suggested_fix(&obligation.kind)));
        }

        Some(lines.join("\n"))
    }

    /// Format all non-proved obligations from a function report.
    #[must_use]
    pub fn format_function(&self, function: &FunctionProofReport) -> String {
        let diagnostics: Vec<String> =
            function.obligations.iter().filter_map(|ob| self.format_obligation(ob)).collect();

        diagnostics.join("\n\n")
    }

    /// Format all non-proved obligations from a full proof report.
    #[must_use]
    pub fn format_report(&self, report: &JsonProofReport) -> String {
        let mut sections: Vec<String> = Vec::new();

        for func in &report.functions {
            let formatted = self.format_function(func);
            if !formatted.is_empty() {
                sections.push(formatted);
            }
        }

        if sections.is_empty() {
            return String::new();
        }

        let mut result = sections.join("\n\n");

        // Append summary
        let error_count = report.summary.total_failed;
        let warning_count = report.summary.total_unknown;
        let mut summary_parts = Vec::new();
        if error_count > 0 {
            summary_parts.push(format!(
                "{error_count} error{} emitted",
                if error_count == 1 { "" } else { "s" }
            ));
        }
        if warning_count > 0 {
            summary_parts.push(format!(
                "{warning_count} warning{} emitted",
                if warning_count == 1 { "" } else { "s" }
            ));
        }
        if !summary_parts.is_empty() {
            let _ = write!(result, "\n\n{}", summary_parts.join("; "));
        }

        result
    }
}

/// Format a single obligation as a diagnostic string using default settings.
///
/// Convenience function equivalent to `DiagnosticFormatter::new().format_obligation(ob)`.
#[must_use]
pub fn format_diagnostic(obligation: &ObligationReport) -> Option<String> {
    DiagnosticFormatter::new().format_obligation(obligation)
}

/// Format a full report as diagnostics using default settings.
///
/// Convenience function equivalent to `DiagnosticFormatter::new().format_report(report)`.
#[must_use]
pub fn format_diagnostics(report: &JsonProofReport) -> String {
    DiagnosticFormatter::new().format_report(report)
}

/// Format a source location in rustc style: `  --> file:line:col`
fn format_location(loc: &SourceSpan) -> String {
    format!("  --> {}:{}:{}", loc.file, loc.line_start, loc.col_start)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;
    use crate::build_json_report;

    // -- Error code tests --

    #[test]
    fn test_error_code_format() {
        assert_eq!(E_ARITHMETIC_OVERFLOW.code(), "E-TRUST-001");
        assert_eq!(E_DIVISION_BY_ZERO.code(), "E-TRUST-003");
        assert_eq!(E_NON_TERMINATION.code(), "E-TRUST-022");
    }

    #[test]
    fn test_error_code_display() {
        assert_eq!(format!("{}", E_ARITHMETIC_OVERFLOW), "E-TRUST-001");
        assert_eq!(format!("{}", E_DEADLOCK), "E-TRUST-014");
    }

    #[test]
    fn test_error_code_for_all_kinds() {
        assert_eq!(error_code_for_kind("arithmetic_overflow_add"), E_ARITHMETIC_OVERFLOW);
        assert_eq!(error_code_for_kind("arithmetic_overflow_mul"), E_ARITHMETIC_OVERFLOW);
        assert_eq!(error_code_for_kind("shift_overflow_shl"), E_SHIFT_OVERFLOW);
        assert_eq!(error_code_for_kind("division_by_zero"), E_DIVISION_BY_ZERO);
        assert_eq!(error_code_for_kind("remainder_by_zero"), E_REMAINDER_BY_ZERO);
        assert_eq!(error_code_for_kind("index_out_of_bounds"), E_INDEX_OUT_OF_BOUNDS);
        assert_eq!(error_code_for_kind("slice_bounds_check"), E_SLICE_BOUNDS_CHECK);
        assert_eq!(error_code_for_kind("assertion"), E_ASSERTION_FAILURE);
        assert_eq!(error_code_for_kind("precondition"), E_PRECONDITION);
        assert_eq!(error_code_for_kind("postcondition"), E_POSTCONDITION);
        assert_eq!(error_code_for_kind("cast_overflow"), E_CAST_OVERFLOW);
        assert_eq!(error_code_for_kind("negation_overflow"), E_NEGATION_OVERFLOW);
        assert_eq!(error_code_for_kind("unreachable"), E_UNREACHABLE);
        assert_eq!(error_code_for_kind("dead_state"), E_DEAD_STATE);
        assert_eq!(error_code_for_kind("deadlock"), E_DEADLOCK);
        assert_eq!(error_code_for_kind("temporal"), E_TEMPORAL);
        assert_eq!(error_code_for_kind("liveness"), E_LIVENESS);
        assert_eq!(error_code_for_kind("fairness"), E_FAIRNESS);
        assert_eq!(error_code_for_kind("taint_violation"), E_TAINT_VIOLATION);
        assert_eq!(error_code_for_kind("refinement_violation"), E_REFINEMENT_VIOLATION);
        assert_eq!(error_code_for_kind("resilience_violation"), E_RESILIENCE_VIOLATION);
        assert_eq!(error_code_for_kind("protocol_violation"), E_PROTOCOL_VIOLATION);
        assert_eq!(error_code_for_kind("non_termination"), E_NON_TERMINATION);
        assert_eq!(
            error_code_for_kind("binary_copy_sink_length_violation"),
            E_BINARY_COPY_SINK_LENGTH
        );
        assert_eq!(
            error_code_for_kind("aarch64_atomic_acquire_ordering_unsupported"),
            E_UNSUPPORTED_BINARY_SEMANTICS
        );
        assert_eq!(
            error_code_for_kind("aarch64_exclusive_monitor_status_unsupported"),
            E_UNSUPPORTED_BINARY_SEMANTICS
        );
    }

    #[test]
    fn test_error_code_unknown_kind_fallback() {
        assert_eq!(error_code_for_kind("some_unknown_kind"), E_ASSERTION_FAILURE);
    }

    #[test]
    fn test_suggested_fix_returns_nonempty_for_all_kinds() {
        let kinds = [
            "arithmetic_overflow_add",
            "shift_overflow_shl",
            "division_by_zero",
            "remainder_by_zero",
            "index_out_of_bounds",
            "slice_bounds_check",
            "assertion",
            "precondition",
            "postcondition",
            "cast_overflow",
            "negation_overflow",
            "unreachable",
            "dead_state",
            "deadlock",
            "temporal",
            "liveness",
            "fairness",
            "taint_violation",
            "refinement_violation",
            "resilience_violation",
            "protocol_violation",
            "non_termination",
            "binary_copy_sink_length_violation",
            "aarch64_atomic_acquire_ordering_unsupported",
            "aarch64_atomic_release_ordering_unsupported",
            "aarch64_exclusive_monitor_unsupported",
            "aarch64_exclusive_monitor_status_unsupported",
        ];
        for kind in &kinds {
            let fix = suggested_fix(kind);
            assert!(!fix.is_empty(), "suggested_fix for '{kind}' should not be empty");
        }
    }

    #[test]
    fn nontermination_fix_distinguishes_recursion_from_unwired_loop_metadata() {
        let fix = suggested_fix("non_termination");
        assert!(fix.contains("for recursion"));
        assert!(fix.contains("for loops"));
        assert!(fix.contains("function-signature `decreases <measure>`"));
        assert!(fix.contains("loop-local `decreases <measure>`"));
        assert!(!fix.contains("#[decreases"));
        assert!(!fix.contains("loop/recursion variant"));
    }

    // -- Diagnostic formatting tests --

    fn failed_overflow_obligation() -> ObligationReport {
        ObligationReport {
            obligation_id: None,
            description: "arithmetic overflow (Add)".to_string(),
            kind: "arithmetic_overflow_add".to_string(),
            proof_level: ProofLevel::L0Safety,
            location: Some(SourceSpan {
                file: "src/midpoint.rs".to_string(),
                line_start: 5,
                col_start: 5,
                line_end: 5,
                col_end: 10,
            }),
            outcome: ObligationOutcome::Failed {
                counterexample: Some(CounterexampleReport {
                    variables: vec![
                        CounterexampleVariable {
                            name: "a".to_string(),
                            value: "18446744073709551615".to_string(),
                            value_type: "uint".to_string(),
                            display: "18446744073709551615".to_string(),
                        },
                        CounterexampleVariable {
                            name: "b".to_string(),
                            value: "1".to_string(),
                            value_type: "uint".to_string(),
                            display: "1".to_string(),
                        },
                    ],
                }),
            },
            solver: "ay".into(),
            time_ms: 3,
            evidence: None,
            proof_evidence: None,
            transport_evidence: None,
        }
    }

    fn proved_divzero_obligation() -> ObligationReport {
        ObligationReport {
            obligation_id: None,
            description: "division by zero".to_string(),
            kind: "division_by_zero".to_string(),
            proof_level: ProofLevel::L0Safety,
            location: Some(SourceSpan {
                file: "src/midpoint.rs".to_string(),
                line_start: 5,
                col_start: 18,
                line_end: 5,
                col_end: 23,
            }),
            outcome: ObligationOutcome::Proved { strength: ProofStrength::smt_unsat() },
            solver: "ay".into(),
            time_ms: 1,
            evidence: None,
            proof_evidence: None,
            transport_evidence: None,
        }
    }

    fn unknown_obligation() -> ObligationReport {
        ObligationReport {
            obligation_id: None,
            description: "index out of bounds".to_string(),
            kind: "index_out_of_bounds".to_string(),
            proof_level: ProofLevel::L0Safety,
            location: Some(SourceSpan {
                file: "src/lookup.rs".to_string(),
                line_start: 12,
                col_start: 9,
                line_end: 12,
                col_end: 20,
            }),
            outcome: ObligationOutcome::Unknown { reason: "nonlinear arithmetic".to_string() },
            solver: "ay".into(),
            time_ms: 50,
            evidence: None,
            proof_evidence: None,
            transport_evidence: None,
        }
    }

    fn timeout_obligation() -> ObligationReport {
        ObligationReport {
            obligation_id: None,
            description: "postcondition".to_string(),
            kind: "postcondition".to_string(),
            proof_level: ProofLevel::L1Functional,
            location: None,
            outcome: ObligationOutcome::Timeout { timeout_ms: 5000 },
            solver: "ay".into(),
            time_ms: 5000,
            evidence: None,
            proof_evidence: None,
            transport_evidence: None,
        }
    }

    #[test]
    fn test_format_diagnostic_failed_with_counterexample() {
        let ob = failed_overflow_obligation();
        let diag = format_diagnostic(&ob).expect("should produce diagnostic for failure");

        assert!(diag.contains("error[E-TRUST-001]"));
        assert!(diag.contains("possible arithmetic overflow"));
        assert!(diag.contains("--> src/midpoint.rs:5:5"));
        assert!(diag.contains("arithmetic overflow (Add)"));
        assert!(diag.contains("counterexample: a = 18446744073709551615, b = 1"));
        assert!(diag.contains("= help:"));
        assert!(diag.contains("checked_add()"));
    }

    #[test]
    fn test_format_diagnostic_proved_returns_none() {
        let ob = proved_divzero_obligation();
        assert!(format_diagnostic(&ob).is_none());
    }

    #[test]
    fn test_format_diagnostic_unknown() {
        let ob = unknown_obligation();
        let diag = format_diagnostic(&ob).expect("should produce diagnostic for unknown");

        assert!(diag.contains("warning[E-TRUST-005]"));
        assert!(diag.contains("possible index out of bounds"));
        assert!(diag.contains("--> src/lookup.rs:12:9"));
        assert!(diag.contains("solver returned unknown: nonlinear arithmetic"));
        assert!(diag.contains("= help:"));
        assert!(diag.contains(".get()"));
    }

    #[test]
    fn test_format_diagnostic_timeout() {
        let ob = timeout_obligation();
        let diag = format_diagnostic(&ob).expect("should produce diagnostic for timeout");

        assert!(diag.contains("warning[E-TRUST-009]"));
        assert!(diag.contains("postcondition may not hold"));
        assert!(diag.contains("timed out after 5000ms"));
        assert!(diag.contains("= help:"));
    }

    #[test]
    fn test_format_diagnostic_no_location() {
        let ob = timeout_obligation();
        let diag = format_diagnostic(&ob).expect("should produce diagnostic");

        // No --> line when location is absent
        assert!(!diag.contains("-->"));
    }

    #[test]
    fn test_format_diagnostic_without_help() {
        let formatter = DiagnosticFormatter::new().with_help(false);
        let ob = failed_overflow_obligation();
        let diag = formatter.format_obligation(&ob).expect("should produce diagnostic");

        assert!(diag.contains("error[E-TRUST-001]"));
        assert!(!diag.contains("= help:"));
    }

    #[test]
    fn test_format_diagnostic_without_counterexamples() {
        let formatter = DiagnosticFormatter::new().with_counterexamples(false);
        let ob = failed_overflow_obligation();
        let diag = formatter.format_obligation(&ob).expect("should produce diagnostic");

        assert!(diag.contains("error[E-TRUST-001]"));
        assert!(!diag.contains("counterexample:"));
    }

    #[test]
    fn test_format_diagnostic_runtime_checked_returns_none() {
        let ob = ObligationReport {
            obligation_id: None,
            description: "runtime safety check".to_string(),
            kind: "postcondition".to_string(),
            proof_level: ProofLevel::L0Safety,
            location: None,
            outcome: ObligationOutcome::RuntimeChecked {
                note: Some("validated by runtime".to_string()),
            },
            solver: "runtime".into(),
            time_ms: 1,
            evidence: None,
            proof_evidence: None,
            transport_evidence: None,
        };
        assert!(format_diagnostic(&ob).is_none());
    }

    // -- Full report diagnostic tests --

    #[test]
    fn test_format_diagnostics_full_report() {
        let results = vec![
            (
                VerificationCondition {
                    kind: VcKind::ArithmeticOverflow {
                        op: BinOp::Add,
                        operand_tys: (Ty::usize(), Ty::usize()),
                    },
                    function: "get_midpoint".into(),
                    location: SourceSpan {
                        file: "src/midpoint.rs".to_string(),
                        line_start: 5,
                        col_start: 5,
                        line_end: 5,
                        col_end: 10,
                    },
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                VerificationResult::Failed {
                    solver: "ay".into(),
                    time_ms: 3,
                    counterexample: Some(Counterexample::new(vec![
                        ("a".to_string(), CounterexampleValue::Uint(u64::MAX as u128)),
                        ("b".to_string(), CounterexampleValue::Uint(1)),
                    ])),
                },
            ),
            (
                VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "get_midpoint".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(false),
                    contract_metadata: None,
                },
                VerificationResult::Proved {
                    solver: "ay".into(),
                    time_ms: 1,
                    strength: ProofStrength::smt_unsat(),
                    proof_certificate: None,
                    solver_warnings: None,
                    native_proof_envelope: None,
                },
            ),
            // Use Postcondition (no runtime fallback) so Auto policy keeps it as Unknown.
            (
                VerificationCondition {
                    kind: VcKind::Postcondition,
                    function: "lookup".into(),
                    location: SourceSpan {
                        file: "src/lookup.rs".to_string(),
                        line_start: 12,
                        col_start: 9,
                        line_end: 12,
                        col_end: 20,
                    },
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                VerificationResult::Unknown {
                    solver: "ay".into(),
                    time_ms: 50,
                    reason: "nonlinear arithmetic".to_string(),
                },
            ),
        ];

        let report = build_json_report("test_crate", &results);
        let output = format_diagnostics(&report);

        // Should contain the failure diagnostic
        assert!(output.contains("error[E-TRUST-001]"));
        assert!(output.contains("possible arithmetic overflow"));

        // Should contain the unknown diagnostic (Postcondition has no runtime fallback)
        assert!(output.contains("warning[E-TRUST-009]"));
        assert!(output.contains("postcondition may not hold"));

        // A raw `Proved` status without structured proof/transport evidence is
        // fail-closed to Unknown and therefore remains diagnostic-visible.
        assert!(output.contains("warning[E-TRUST-003]"));

        // Summary line
        assert!(output.contains("1 error emitted"));
        assert!(output.contains("2 warnings emitted"));
    }

    #[test]
    fn test_format_diagnostics_raw_proved_without_evidence_is_visible() {
        let results = vec![(
            VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: "safe_fn".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
            },
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )];

        let report = build_json_report("safe_crate", &results);
        let output = format_diagnostics(&report);
        assert!(output.contains("warning[E-TRUST-003]"));
        assert!(output.contains("proof_evidence is missing"));
        assert!(output.contains("1 warning emitted"));
    }

    #[test]
    fn test_format_diagnostics_multiple_errors_summary() {
        let results = vec![
            (
                VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "f".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                VerificationResult::Failed {
                    solver: "ay".into(),
                    time_ms: 1,
                    counterexample: None,
                },
            ),
            (
                VerificationCondition {
                    kind: VcKind::IndexOutOfBounds,
                    function: "f".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                VerificationResult::Failed {
                    solver: "ay".into(),
                    time_ms: 2,
                    counterexample: None,
                },
            ),
        ];

        let report = build_json_report("multi_err", &results);
        let output = format_diagnostics(&report);

        assert!(output.contains("2 errors emitted"));
    }

    #[test]
    fn test_format_function_mixed_obligations() {
        let formatter = DiagnosticFormatter::new();
        let func = FunctionProofReport {
            function: "test_fn".into(),
            summary: FunctionSummary {
                total_obligations: 3,
                proved: 1,
                runtime_checked: 0,
                failed: 1,
                unknown: 1,
                timed_out: 0,
                design_requirements: 0,
                unattributed_failed: 0,
                unattributed_unknown: 0,
                unattributed_proved: 0,
                total_time_ms: 54,
                max_proof_level: Some(ProofLevel::L0Safety),
                verdict: FunctionVerdict::HasViolations,
            },
            obligations: vec![
                failed_overflow_obligation(),
                proved_divzero_obligation(),
                unknown_obligation(),
            ],
        };

        let output = formatter.format_function(&func);

        // Contains the failure and unknown, but not the proved one
        assert!(output.contains("error[E-TRUST-001]"));
        assert!(output.contains("warning[E-TRUST-005]"));
        assert!(!output.contains("E-TRUST-003"));
    }

    #[test]
    fn test_format_diagnostic_failed_no_counterexample() {
        let ob = ObligationReport {
            obligation_id: None,
            description: "division by zero".to_string(),
            kind: "division_by_zero".to_string(),
            proof_level: ProofLevel::L0Safety,
            location: Some(SourceSpan {
                file: "src/math.rs".to_string(),
                line_start: 10,
                col_start: 1,
                line_end: 10,
                col_end: 15,
            }),
            outcome: ObligationOutcome::Failed { counterexample: None },
            solver: "ay".into(),
            time_ms: 5,
            evidence: None,
            proof_evidence: None,
            transport_evidence: None,
        };

        let diag = format_diagnostic(&ob).expect("should produce diagnostic");
        assert!(diag.contains("error[E-TRUST-003]"));
        assert!(diag.contains("possible division by zero"));
        assert!(diag.contains("--> src/math.rs:10:1"));
        assert!(!diag.contains("counterexample:"));
        assert!(diag.contains("= help:"));
        assert!(diag.contains("zero check"));
    }
}
