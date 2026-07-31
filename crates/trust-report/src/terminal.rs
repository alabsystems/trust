// trust-report/terminal.rs: Colored terminal proof report formatter
//
// Renders a JsonProofReport as ANSI-colored terminal output.
// Respects the NO_COLOR environment variable (https://no-color.org/).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{CrateVerdict, FunctionVerdict, JsonProofReport, ObligationOutcome};

use crate::{
    function_verdict_label, monitor_evidence_label, proof_evidence_label_with_monitor,
    proof_level_label, proof_strength_label,
};

// ANSI escape codes
const GREEN: &str = "\x1b[32m";
const BLUE: &str = "\x1b[34m";
const RED: &str = "\x1b[31m";
const YELLOW: &str = "\x1b[33m";
const BOLD: &str = "\x1b[1m";
const DIM: &str = "\x1b[2m";
const RESET: &str = "\x1b[0m";

/// Whether ANSI color codes should be emitted.
///
/// Returns `false` when the `NO_COLOR` environment variable is set
/// (any value, including empty), per <https://no-color.org/>.
fn use_color() -> bool {
    std::env::var_os("NO_COLOR").is_none()
}

/// ANSI helper: wraps `text` in the given code if color is enabled.
fn ansi(code: &str, text: &str, color: bool) -> String {
    if color { format!("{code}{text}{RESET}") } else { text.to_string() }
}

/// Format a `JsonProofReport` as a colored terminal string.
///
/// The output includes:
/// - A header with crate name and metadata
/// - Per-function groups with obligation details
/// - A summary line at the bottom: "X proved, Y runtime-checked, Z failed, W unknown"
///
/// Respects `NO_COLOR` environment variable.
pub fn format_terminal_report(report: &JsonProofReport) -> String {
    format_terminal_report_impl(report, use_color())
}

/// Internal implementation that accepts an explicit color flag.
///
/// Exposed as `pub(crate)` so tests can exercise both colored and
/// plain output without mutating process-global environment variables.
pub(crate) fn format_terminal_report_impl(report: &JsonProofReport, color: bool) -> String {
    let mut lines: Vec<String> = Vec::new();

    // Header
    lines.push(format!(
        "{} {} {}",
        ansi(BOLD, "Trust verification report:", color),
        ansi(BOLD, &report.crate_name, color),
        ansi(
            DIM,
            &format!("(v{}, {}ms)", report.metadata.trust_version, report.metadata.total_time_ms),
            color,
        ),
    ));
    lines.push(String::new());

    // Per-function groups
    for func in &report.functions {
        let verdict_str = match func.summary.verdict {
            FunctionVerdict::Verified => {
                ansi(GREEN, function_verdict_label(func.summary.verdict), color)
            }
            FunctionVerdict::RuntimeChecked => {
                ansi(BLUE, function_verdict_label(func.summary.verdict), color)
            }
            FunctionVerdict::HasViolations => {
                ansi(RED, function_verdict_label(func.summary.verdict), color)
            }
            FunctionVerdict::Inconclusive => {
                ansi(YELLOW, function_verdict_label(func.summary.verdict), color)
            }
            FunctionVerdict::NoObligations => {
                ansi(DIM, function_verdict_label(func.summary.verdict), color)
            }
            _ => "UNKNOWN".to_string(),
        };
        lines.push(format!("  {} [{}]", ansi(BOLD, &func.function, color), verdict_str,));
        lines.push(format!(
            "    {}",
            ansi(
                DIM,
                &format!(
                    "{} proved, {} runtime-checked, {} failed, {} | {} obligations | max level: {} | {}ms{}",
                    func.summary.proved,
                    func.summary.runtime_checked,
                    func.summary.failed,
                    pending_summary(func.summary.unknown, func.summary.timed_out),
                    func.summary.total_obligations,
                    proof_level_label(func.summary.max_proof_level),
                    func.summary.total_time_ms,
                    unattributed_suffix(
                        func.summary.unattributed_proved,
                        func.summary.unattributed_failed,
                        func.summary.unattributed_unknown,
                    )
                ),
                color,
            )
        ));

        for ob in &func.obligations {
            let monitor =
                ob.transport_evidence.as_ref().and_then(|transport| transport.monitor.as_ref());
            let status_colored = match &ob.outcome {
                ObligationOutcome::Proved { strength } => {
                    ansi(GREEN, &format!("PROVED [{}]", proof_strength_label(strength)), color)
                }
                ObligationOutcome::RuntimeChecked { .. } => ansi(BLUE, "RUNTIME-CHECKED", color),
                ObligationOutcome::Failed { .. } => ansi(RED, "FAILED", color),
                ObligationOutcome::Unknown { .. } => ansi(YELLOW, "UNKNOWN", color),
                ObligationOutcome::Timeout { .. } => ansi(YELLOW, "TIMEOUT", color),
                _ => "UNKNOWN".to_string(),
            };

            let location_str = ob
                .location
                .as_ref()
                .map(|loc| format!(" {}:{}", loc.file, loc.line_start))
                .unwrap_or_default();

            let id_str =
                ob.obligation_id.as_ref().map(|id| format!(", id {id}")).unwrap_or_default();
            let meta = ansi(
                DIM,
                &format!("({}, {}ms{}{})", ob.solver, ob.time_ms, location_str, id_str),
                color,
            );

            lines.push(format!("    {} [{}] {} {}", status_colored, ob.kind, ob.description, meta));

            // The legacy strength remains in the compact status token for CLI
            // compatibility; the next line is the authoritative multi-axis
            // evidence view. It is derived only, so rendering cannot change a
            // verdict or mint standing that the legacy evidence did not carry.
            if let ObligationOutcome::Proved { strength } = &ob.outcome {
                lines.push(format!(
                    "      {} {}",
                    ansi(DIM, "grade:", color),
                    proof_evidence_label_with_monitor(strength, monitor),
                ));
            }

            if let Some(evidence) = &ob.proof_evidence {
                if matches!(&ob.outcome, ObligationOutcome::Proved { .. }) {
                    lines.push(format!(
                        "      {} backend: {}, provenance: {}, strength: {}",
                        ansi(GREEN, "proof evidence:", color),
                        evidence.backend,
                        evidence_provenance_label(&evidence.provenance),
                        proof_evidence_label_with_monitor(&evidence.strength, monitor),
                    ));
                } else {
                    lines.push(format!(
                        "      {} backend: {}, provenance: {}, claimed strength: {}",
                        ansi(
                            YELLOW,
                            "untrusted serialized evidence (diagnostic only; no proof authority):",
                            color,
                        ),
                        evidence.backend,
                        evidence_provenance_label(&evidence.provenance),
                        proof_evidence_label_with_monitor(&evidence.strength, monitor),
                    ));
                }
            }

            if !matches!(&ob.outcome, ObligationOutcome::Proved { .. })
                && let Some(monitor) = monitor
            {
                lines.push(format!(
                    "      {} {}",
                    ansi(DIM, "grade:", color),
                    monitor_evidence_label(monitor),
                ));
            }

            // Extra detail for failures with counterexamples
            if let ObligationOutcome::Failed { counterexample: Some(cex) } = &ob.outcome {
                let vars: Vec<String> =
                    cex.variables.iter().map(|v| format!("{} = {}", v.name, v.display)).collect();
                lines.push(format!(
                    "      {} {}",
                    ansi(RED, "counterexample:", color),
                    vars.join(", "),
                ));
            }

            // Extra detail for unknown reasons
            if let ObligationOutcome::Unknown { reason } = &ob.outcome {
                lines.push(format!("      {} {}", ansi(YELLOW, "reason:", color), reason,));
            }

            // Extra detail for runtime-checked notes
            if let ObligationOutcome::RuntimeChecked { note: Some(note) } = &ob.outcome {
                lines.push(format!("      {} {}", ansi(BLUE, "note:", color), note,));
            }

            // Extra detail for timeouts
            if let ObligationOutcome::Timeout { timeout_ms } = &ob.outcome {
                lines.push(format!(
                    "      {} after {}ms",
                    ansi(YELLOW, "timed out", color),
                    timeout_ms,
                ));
            }
        }
        lines.push(String::new());
    }

    // Summary line
    let s = &report.summary;
    let proved_str = if s.total_proved > 0 {
        ansi(GREEN, &format!("{} proved", s.total_proved), color)
    } else {
        format!("{} proved", s.total_proved)
    };
    let runtime_checked_str = if s.total_runtime_checked > 0 {
        ansi(BLUE, &format!("{} runtime-checked", s.total_runtime_checked), color)
    } else {
        format!("{} runtime-checked", s.total_runtime_checked)
    };
    let failed_str = if s.total_failed > 0 {
        ansi(RED, &format!("{} failed", s.total_failed), color)
    } else {
        format!("{} failed", s.total_failed)
    };
    let pending_label = pending_summary(s.total_unknown, s.total_timed_out);
    let pending_str =
        if s.total_unknown > 0 { ansi(YELLOW, &pending_label, color) } else { pending_label };
    let mut summary_line =
        format!("{}, {}, {}, {}", proved_str, runtime_checked_str, failed_str, pending_str);
    // surface hardened-boundary design mandates in their own
    // segment — they are not failures, but they are not "all clear" either.
    if s.total_design_requirements > 0 {
        summary_line.push_str(&format!(
            ", {}",
            ansi(YELLOW, &format!("{} design-required", s.total_design_requirements), color)
        ));
    }
    let suffix = unattributed_suffix(
        s.total_unattributed_proved,
        s.total_unattributed_failed,
        s.total_unattributed_unknown,
    );
    if !suffix.is_empty() {
        summary_line.push_str(&suffix);
    }
    lines.push(summary_line);

    // Trust: per-kind composition of the blended totals above — a green count
    // means nothing unless you can see WHICH kinds were proved, so admissions
    // and lowering-gap markers cannot hide inside an aggregate.
    let mut crate_breakdown = crate::formatting::KindBreakdown::default();
    for func in &report.functions {
        crate_breakdown.add(&func.obligations);
    }
    for line in crate_breakdown.lines("  ") {
        lines.push(ansi(DIM, &line, color));
    }

    // Trust: session-end Trust Surface — vanilla rustc accepts this crate
    // unchanged; this section states, split by strength of basis, exactly what
    // Trust additionally proved (certified/smt-backed), runtime-checked, left
    // unknown, or rested on an assumed/trusted dependency. Bolds the header and
    // dims the detail to match the surrounding summary style.
    let surface_lines = crate::formatting::trust_surface_lines(&report.functions);
    if let Some((header, detail)) = surface_lines.split_first() {
        lines.push(ansi(BOLD, header, color));
        for line in detail {
            lines.push(ansi(DIM, &format!("  {line}"), color));
        }
    }

    // Verdict
    let verdict_str = match s.verdict {
        CrateVerdict::Verified => ansi(GREEN, "VERIFIED", color),
        CrateVerdict::RuntimeChecked => ansi(BLUE, "RUNTIME CHECKED", color),
        CrateVerdict::HasViolations => ansi(RED, "HAS VIOLATIONS", color),
        CrateVerdict::Inconclusive => ansi(YELLOW, "INCONCLUSIVE", color),
        CrateVerdict::NoObligations => ansi(DIM, "NO OBLIGATIONS", color),
        _ => "UNKNOWN".to_string(),
    };
    lines.push(format!("Verdict: {}", verdict_str));

    lines.join("\n")
}

fn pending_summary(pending: usize, timed_out: usize) -> String {
    let unknown = pending.saturating_sub(timed_out);
    if timed_out > 0 {
        format!("{unknown} unknown, {timed_out} {}", timeout_word(timed_out))
    } else {
        format!("{unknown} unknown")
    }
}

fn timeout_word(count: usize) -> &'static str {
    if count == 1 { "timeout" } else { "timeouts" }
}

fn unattributed_suffix(proved: usize, failed: usize, unknown: usize) -> String {
    if proved == 0 && failed == 0 && unknown == 0 {
        String::new()
    } else {
        format!(" | unattributed: {} proved, {} failed, {} pending", proved, failed, unknown)
    }
}

fn evidence_provenance_label(
    provenance: &trust_types::ObligationEvidenceProvenanceReport,
) -> String {
    match provenance {
        trust_types::ObligationEvidenceProvenanceReport::RouterAttributed => {
            "router_attributed".to_string()
        }
        trust_types::ObligationEvidenceProvenanceReport::NativeBackend { verifier } => {
            format!("native_backend:{verifier}")
        }
        _ => "unknown".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;
    use crate::{SCHEMA_VERSION, TRUST_VERSION, build_json_report};

    /// Helper: build a report with one function containing mixed results.
    fn mixed_report() -> JsonProofReport {
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
                    location: SourceSpan {
                        file: "src/midpoint.rs".to_string(),
                        line_start: 5,
                        col_start: 18,
                        line_end: 5,
                        col_end: 23,
                    },
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
            (
                VerificationCondition {
                    kind: VcKind::CastOverflow { from_ty: Ty::usize(), to_ty: Ty::u32() },
                    function: "get_midpoint".into(),
                    location: SourceSpan::default(),
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
        build_json_report("midpoint", &results)
    }

    fn runtime_checked_report() -> JsonProofReport {
        JsonProofReport {
            metadata: ReportMetadata {
                schema_version: SCHEMA_VERSION.to_string(),
                trust_version: TRUST_VERSION.to_string(),
                timestamp: "0".to_string(),
                total_time_ms: 11,
                timeout_ms: None,
                function_budget_ms: None,
            },
            crate_name: "runtime_checked".to_string(),
            summary: CrateSummary {
                proof_grade_engine_statuses: Vec::new(),
                functions_analyzed: 1,
                functions_verified: 0,
                functions_runtime_checked: 1,
                functions_with_violations: 0,
                functions_inconclusive: 0,
                total_obligations: 1,
                total_proved: 0,
                total_runtime_checked: 1,
                total_failed: 0,
                total_unknown: 0,
                total_timed_out: 0,
                total_design_requirements: 0,
                total_unattributed_failed: 0,
                total_unattributed_unknown: 0,
                total_unattributed_proved: 0,
                verdict: CrateVerdict::RuntimeChecked,
            },
            functions: vec![FunctionProofReport {
                function: "dynamic_check".into(),
                summary: FunctionSummary {
                    total_obligations: 1,
                    proved: 0,
                    runtime_checked: 1,
                    failed: 0,
                    unknown: 0,
                    timed_out: 0,
                    design_requirements: 0,
                    unattributed_failed: 0,
                    unattributed_unknown: 0,
                    unattributed_proved: 0,
                    total_time_ms: 11,
                    max_proof_level: Some(ProofLevel::L0Safety),
                    verdict: FunctionVerdict::RuntimeChecked,
                },
                obligations: vec![ObligationReport {
                    obligation_id: None,
                    description: "runtime safety check".to_string(),
                    kind: "postcondition".to_string(),
                    proof_level: ProofLevel::L0Safety,
                    location: Some(SourceSpan {
                        file: "src/runtime.rs".to_string(),
                        line_start: 10,
                        col_start: 1,
                        line_end: 10,
                        col_end: 12,
                    }),
                    outcome: ObligationOutcome::RuntimeChecked {
                        note: Some("validated by runtime instrumentation".to_string()),
                    },
                    solver: "runtime".into(),
                    time_ms: 11,
                    evidence: None,
                    proof_evidence: None,
                    transport_evidence: None,
                }],
            }],
            hardened: None,
            assumptions: Vec::new(),
            verification_gate: None,
            cargo_proof_inventory: None,
        }
    }

    #[test]
    fn test_terminal_report_basic() {
        let report = mixed_report();
        // Explicitly request color=true for deterministic test
        let output = format_terminal_report_impl(&report, true);

        // Header present
        assert!(output.contains("Trust verification report:"));
        assert!(output.contains("midpoint"));

        // Function name in bold
        assert!(output.contains(&format!("{BOLD}get_midpoint{RESET}")));

        // FAILED in red
        assert!(output.contains(&format!("{RED}FAILED{RESET}")));

        // UNKNOWN in yellow
        assert!(output.contains(&format!("{YELLOW}UNKNOWN{RESET}")));

        // Counterexample detail
        assert!(output.contains("counterexample:"));
        assert!(output.contains("a = 18446744073709551615"));

        // Solver metadata in dim
        assert!(output.contains("ay"));

        // Summary line: "X proved, Y failed, Z unknown"
        assert!(output.contains("0 proved"));
        assert!(output.contains("1 failed"));
        assert!(output.contains("2 unknown"));
        assert!(output.contains("proof_evidence is missing"));
        assert!(output.contains("max level: L0 safety"));

        // Verdict
        assert!(output.contains("Verdict:"));
    }

    #[test]
    fn test_terminal_no_color() {
        let report = mixed_report();
        // Explicitly request color=false (equivalent to NO_COLOR being set)
        let output = format_terminal_report_impl(&report, false);

        // No ANSI escape sequences anywhere
        assert!(
            !output.contains("\x1b["),
            "output should not contain ANSI escape codes when color is disabled"
        );

        // Content still present (plain text)
        assert!(output.contains("UNKNOWN"));
        assert!(output.contains("proof_evidence is missing"));
        assert!(output.contains("FAILED"));
        assert!(output.contains("get_midpoint"));
        assert!(output.contains("0 proved"));
        assert!(output.contains("1 failed"));
        assert!(output.contains("2 unknown"));
        assert!(output.contains("max level: L0 safety"));
    }

    // Trust: the session-end Trust Surface section renders the deviation from
    // vanilla rustc, split by strength of basis, and reconciles with the report.
    #[test]
    fn test_terminal_trust_surface_section() {
        let report = mixed_report(); // 1 raw proof status, 1 failed, 1 unknown
        let output = format_terminal_report_impl(&report, false);

        assert!(
            output.contains("Trust Surface (deviation from vanilla rustc)"),
            "missing Trust Surface header:\n{output}"
        );
        assert!(
            output.contains("vanilla rustc accepts this unchanged"),
            "missing vanilla framing:\n{output}"
        );
        // The raw proof status has no structured publication evidence.
        assert!(
            output.contains("additionally proved=0 (certified=0, smt-backed=0)"),
            "surface must split proved by assurance:\n{output}"
        );
        // Both the original Unknown and downgraded raw status are surfaced.
        assert!(output.contains("left unknown=2"), "surface must report unknowns:\n{output}");
        assert!(output.contains("refuted=1"), "surface must report refutations:\n{output}");
    }

    #[test]
    fn test_terminal_summary_line() {
        // Build a report with known counts: two raw proof statuses, one failure,
        // and one timeout. The raw statuses must become unknown.
        let results = vec![
            (
                VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "f1".into(),
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
            (
                VerificationCondition {
                    kind: VcKind::ArithmeticOverflow {
                        op: BinOp::Add,
                        operand_tys: (Ty::u32(), Ty::u32()),
                    },
                    function: "f1".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(false),
                    contract_metadata: None,
                },
                VerificationResult::Proved {
                    solver: "ay".into(),
                    time_ms: 2,
                    strength: ProofStrength::smt_unsat(),
                    proof_certificate: None,
                    solver_warnings: None,
                    native_proof_envelope: None,
                },
            ),
            (
                VerificationCondition {
                    kind: VcKind::IndexOutOfBounds,
                    function: "f2".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                VerificationResult::Failed {
                    solver: "ay".into(),
                    time_ms: 5,
                    counterexample: None,
                },
            ),
            (
                VerificationCondition {
                    kind: VcKind::Postcondition,
                    function: "f3".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                VerificationResult::Timeout { solver: "ay".into(), timeout_ms: 5000 },
            ),
        ];
        let report = build_json_report("counts", &results);
        // Use color=false so we can match exact text without ANSI codes
        let output = format_terminal_report_impl(&report, false);

        // Verify the exact counts in the summary line
        assert!(output.contains("0 proved"), "expected '0 proved' in output:\n{output}");
        assert!(output.contains("1 failed"), "expected '1 failed' in output:\n{output}");
        assert!(
            output.contains("2 unknown, 1 timeout"),
            "expected timeout split in output:\n{output}"
        );
        assert!(output.contains("max level: L0 safety"));
    }

    #[test]
    fn test_terminal_runtime_checked_status() {
        let report = runtime_checked_report();
        let output = format_terminal_report_impl(&report, false);

        assert!(output.contains("RUNTIME CHECKED"));
        assert!(output.contains("1 runtime-checked"));
        assert!(output.contains("validated by runtime instrumentation"));
        assert!(output.contains("Verdict: RUNTIME CHECKED"));
    }

    #[test]
    fn test_terminal_unmatched_e4_row_is_explicitly_unmonitored() {
        let mut report = runtime_checked_report();
        let obligation = &mut report.functions[0].obligations[0];
        obligation.kind = "loop_invariant".into();
        obligation.description = "prove loop invariant".into();
        obligation.outcome = ObligationOutcome::Unknown { reason: "static proof open".into() };
        obligation.transport_evidence = Some(ObligationTransportEvidenceReport {
            obligation_id: Some("obligation:loop_invariant:0".into()),
            claim_digest_sha256: None,
            typed_kind: Some(Box::new(VcKind::LoopInvariantInitiation {
                invariant: "i <= n".into(),
                header_block: 1,
            })),
            native_trust_ir: None,
            proof_evidence: None,
            monitor: Some(TransportMonitorEvidence {
                status: TransportMonitorStatus::Unmonitored,
                reason: "no kernel-certified loop monitor evidence matched this row".into(),
                predicate_digest: format!("sha256:{}", "f".repeat(64)),
            }),
        });

        let output = format_terminal_report_impl(&report, false);
        assert!(output.contains("executability: unmonitored"), "{output}");
        assert!(!output.contains("executability: monitored"), "{output}");
        assert!(output.contains("static proof open"), "{output}");
    }

    #[test]
    fn test_terminal_native_evidence_and_unattributed_counts() {
        let report = JsonProofReport {
            metadata: ReportMetadata {
                schema_version: SCHEMA_VERSION.to_string(),
                trust_version: TRUST_VERSION.to_string(),
                timestamp: "0".to_string(),
                total_time_ms: 9,
                timeout_ms: None,
                function_budget_ms: None,
            },
            crate_name: "native".to_string(),
            summary: CrateSummary {
                proof_grade_engine_statuses: Vec::new(),
                functions_analyzed: 1,
                functions_verified: 0,
                functions_runtime_checked: 0,
                functions_with_violations: 0,
                functions_inconclusive: 1,
                total_obligations: 1,
                total_proved: 1,
                total_runtime_checked: 0,
                total_failed: 0,
                total_unknown: 0,
                total_timed_out: 0,
                total_design_requirements: 0,
                total_unattributed_failed: 0,
                total_unattributed_unknown: 0,
                total_unattributed_proved: 1,
                verdict: CrateVerdict::Inconclusive,
            },
            functions: vec![FunctionProofReport {
                function: "native::f".into(),
                summary: FunctionSummary {
                    total_obligations: 1,
                    proved: 1,
                    runtime_checked: 0,
                    failed: 0,
                    unknown: 0,
                    timed_out: 0,
                    design_requirements: 0,
                    unattributed_failed: 0,
                    unattributed_unknown: 0,
                    unattributed_proved: 1,
                    total_time_ms: 9,
                    max_proof_level: Some(ProofLevel::L1Functional),
                    verdict: FunctionVerdict::Inconclusive,
                },
                obligations: vec![ObligationReport {
                    obligation_id: Some("abc:0".to_string()),
                    description: "postcondition".to_string(),
                    kind: "postcondition".to_string(),
                    proof_level: ProofLevel::L1Functional,
                    location: None,
                    outcome: ObligationOutcome::Proved { strength: ProofStrength::inductive() },
                    solver: "trust-wp-lib".into(),
                    time_ms: 9,
                    evidence: Some(ProofStrength::inductive().into()),
                    proof_evidence: Some(ObligationProofEvidenceReport {
                        suite: None,
                        backend: "trust-wp-lib".to_string(),
                        request_id: None,
                        proof_id: None,
                        native_id: None,
                        status: None,
                        provenance: ObligationEvidenceProvenanceReport::NativeBackend {
                            verifier: "trust-wp-lib".to_string(),
                        },
                        strength: ProofStrength::inductive(),
                        evidence: ProofStrength::inductive().into(),
                        proof_certificate: None,
                        native_trust_ir: None,
                        artifacts: Vec::new(),
                        diagnostics: Vec::new(),
                        solver_warnings: None,
                    }),
                    transport_evidence: None,
                }],
            }],
            hardened: None,
            assumptions: Vec::new(),
            verification_gate: None,
            cargo_proof_inventory: None,
        };

        let output = format_terminal_report_impl(&report, false);

        assert!(output.contains("id abc:0"));
        assert!(output.contains("proof evidence: backend: trust-wp-lib"));
        assert!(output.contains("provenance: native_backend:trust-wp-lib"));
        assert!(output.contains("unattributed: 1 proved, 0 failed, 0 pending"));

        let saved: JsonProofReport =
            serde_json::from_slice(&serde_json::to_vec(&report).expect("serialize saved report"))
                .expect("deserialize saved report");
        let saved_output = format_terminal_report_impl(&saved, false);
        assert!(saved_output.contains("UNKNOWN"));
        assert!(
            saved_output
                .contains("untrusted serialized evidence (diagnostic only; no proof authority):")
        );
        assert!(!saved_output.contains("      proof evidence:"));
    }
}
