//! Text formatting for proof reports.
//!
//! Human-readable text output derived from the canonical JSON report.
//! Includes verdict labels, proof strength labels, and summary formatting.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use trust_types::grade::{
    AxiomClosure, CoverageBound, Executability, ProofValidation, ReflectionTier,
};
use trust_types::*;

/// Format a JSON proof report as a human-readable summary string.
///
/// This is the text format derived from the canonical JSON.
pub fn format_json_summary(report: &JsonProofReport) -> String {
    let mut lines = Vec::new();

    for func in &report.functions {
        let verdict_tag = function_verdict_label(func.summary.verdict);
        lines.push(format!(
            "  {} [{}] ({} obligations: {} proved, {} runtime-checked, {} failed, {}; {}ms; max level: {})",
            func.function,
            verdict_tag,
            func.summary.total_obligations,
            func.summary.proved,
            func.summary.runtime_checked,
            func.summary.failed,
            pending_summary(func.summary.unknown, func.summary.timed_out),
            func.summary.total_time_ms,
            proof_level_label(func.summary.max_proof_level)
        ));

        // Trust: show the per-kind composition of this function's outcomes. A
        // single `proved` total is a lie by blending — a green count only means
        // something if you can see WHAT was proved, so the synthetic admission
        // and lowering-gap markers cannot hide inside it.
        let mut func_breakdown = KindBreakdown::default();
        func_breakdown.add(&func.obligations);
        lines.extend(func_breakdown.lines("    "));

        for ob in &func.obligations {
            let monitor =
                ob.transport_evidence.as_ref().and_then(|transport| transport.monitor.as_ref());
            let status_line = match &ob.outcome {
                ObligationOutcome::Proved { strength } => {
                    format!(
                        "    [{}] {} PROVED ({}, {}, {}ms)",
                        ob.kind,
                        ob.description,
                        ob.solver,
                        proof_evidence_label_with_monitor(strength, monitor),
                        ob.time_ms
                    )
                }
                ObligationOutcome::Failed { counterexample } => {
                    let cex_str = counterexample
                        .as_ref()
                        .map(|c| {
                            let vars: Vec<String> = c
                                .variables
                                .iter()
                                .map(|v| format!("{} = {}", v.name, v.display))
                                .collect();
                            format!(" counterexample: {}", vars.join(", "))
                        })
                        .unwrap_or_default();
                    format!("    [{}] {} FAILED ({}){cex_str}", ob.kind, ob.description, ob.solver)
                }
                ObligationOutcome::Unknown { reason } => {
                    format!(
                        "    [{}] {} UNKNOWN ({}: {})",
                        ob.kind, ob.description, ob.solver, reason
                    )
                }
                ObligationOutcome::RuntimeChecked { note } => {
                    let note_str = note.as_ref().map(|n| format!(": {n}")).unwrap_or_default();
                    format!(
                        "    [{}] {} RUNTIME CHECKED ({}{})",
                        ob.kind, ob.description, ob.solver, note_str
                    )
                }
                ObligationOutcome::Timeout { timeout_ms } => {
                    format!(
                        "    [{}] {} TIMEOUT ({}, {}ms)",
                        ob.kind, ob.description, ob.solver, timeout_ms
                    )
                }
                ObligationOutcome::DesignRequirement { detail } => {
                    format!("    [{}] {} DESIGN-REQUIRED ({detail})", ob.kind, ob.description)
                }
                _ => format!("    [{}] {} UNKNOWN ({})", ob.kind, ob.description, ob.solver),
            };
            lines.push(status_line);
            if !matches!(&ob.outcome, ObligationOutcome::Proved { .. })
                && let Some(monitor) = monitor
            {
                lines.push(format!("      {}", monitor_evidence_label(monitor)));
            }
        }
    }

    lines.push(String::new());
    let s = &report.summary;
    lines.push(format!(
        "  {} functions, {} proved, {} runtime-checked, {} failed, {}",
        s.functions_analyzed,
        s.total_proved,
        s.total_runtime_checked,
        s.total_failed,
        pending_summary(s.total_unknown, s.total_timed_out)
    ));

    // Trust: crate-level per-kind composition, computed from the obligation
    // lists (the source of truth) so it always reconciles with the detail
    // above. This is the headline anti-vacuity surface: the blended
    // `{} proved` total above is never presented without its breakdown.
    let mut crate_breakdown = KindBreakdown::default();
    for func in &report.functions {
        crate_breakdown.add(&func.obligations);
    }
    lines.extend(crate_breakdown.lines("  "));

    // Trust: session-end Trust Surface — what Trust proved/checked/assumed on top
    // of code that vanilla rustc already accepts, split by strength of basis so
    // the blended `total_proved` above is never read as a single assurance claim.
    for line in trust_surface_lines(&report.functions) {
        lines.push(format!("  {line}"));
    }

    let verdict_tag = match s.verdict {
        CrateVerdict::Verified => "VERIFIED",
        CrateVerdict::RuntimeChecked => "RUNTIME CHECKED",
        CrateVerdict::HasViolations => "HAS VIOLATIONS",
        CrateVerdict::Inconclusive => "INCONCLUSIVE",
        CrateVerdict::NoObligations => "NO OBLIGATIONS",
        _ => "unknown",
    };
    lines.push(format!("  Verdict: {verdict_tag}"));

    // Trust (green front door, Stage 2): the tiered exit-code gate decision,
    // rendered SEPARATELY from the verdict above. The verdict stays fail-closed;
    // this line answers why `targo trust check` exited as it did.
    if let Some(gate) = &report.verification_gate {
        // Trust (T9 contract-panic): the contract-panic count is rendered
        // UNCONDITIONALLY — a pass conditional on an intentional panic must
        // never be visually indistinguishable from an all-proved pass.
        lines.push(format!(
            "  Gate: {} [{} lane, exit {}] ({} proved, {} failed, {} runtime-checked, {} assumed, {} mandated, {} contract-panic, {} unknown / {} total)",
            gate.decision.to_ascii_uppercase(),
            gate.lane,
            gate.exit_code,
            gate.counts.proved,
            gate.counts.failed,
            gate.counts.runtime_checked,
            gate.counts.assumed,
            gate.counts.mandated,
            gate.counts.contract_panics,
            gate.counts.unknown,
            gate.counts.total,
        ));
    }

    lines.join("\n")
}

/// Trust: per-kind composition of obligation outcomes.
///
/// The report must never present a single blended `proved` total. Verification
/// is only meaningful if a reader can see WHAT was proved — which kinds, and in
/// what proportion — so that the synthetic trust-mc admission, lowering-gap
/// `custom` markers, and any other non-safety obligation cannot hide inside an
/// aggregate green number. Buckets are keyed by the obligation's `kind` tag and
/// derived directly from the obligation list, so they always reconcile with the
/// per-obligation detail.
#[derive(Default)]
pub(crate) struct KindBreakdown {
    proved: BTreeMap<String, usize>,
    failed: BTreeMap<String, usize>,
    unknown: BTreeMap<String, usize>,
    runtime_checked: BTreeMap<String, usize>,
}

impl KindBreakdown {
    pub(crate) fn add(&mut self, obligations: &[ObligationReport]) {
        for ob in obligations {
            let bucket = match &ob.outcome {
                ObligationOutcome::Proved { .. } => &mut self.proved,
                ObligationOutcome::Failed { .. } => &mut self.failed,
                ObligationOutcome::Unknown { .. } | ObligationOutcome::Timeout { .. } => {
                    &mut self.unknown
                }
                ObligationOutcome::RuntimeChecked { .. } => &mut self.runtime_checked,
                // A design requirement is a mandate, not a proof outcome, so it
                // is left out of every bucket. Any future outcome variant lands
                // in `unknown` rather than silently reading as proved.
                ObligationOutcome::DesignRequirement { .. } => continue,
                _ => &mut self.unknown,
            };
            *bucket.entry(ob.kind.clone()).or_insert(0) += 1;
        }
    }

    /// Render the non-empty per-kind lines, each prefixed by `indent`.
    pub(crate) fn lines(&self, indent: &str) -> Vec<String> {
        let mut out = Vec::new();
        for (label, map) in [
            ("proved", &self.proved),
            ("failed", &self.failed),
            ("unknown", &self.unknown),
            ("runtime-checked", &self.runtime_checked),
        ] {
            if let Some(line) = format_kind_map(label, map) {
                out.push(format!("{indent}{line}"));
            }
        }
        out
    }
}

/// Trust: render the per-compile "Trust Surface" — the deviation from what
/// vanilla rustc accepts unchanged. Vanilla rustc compiles this crate with none
/// of these obligations; Trust adds them and this section states, by strength of
/// basis, exactly what that bought. The classification is derived from the
/// obligation lists (the source of truth) via [`TrustSurface::from_functions`],
/// so it always reconciles with the per-obligation detail and never inflates a
/// blended `proved` total into an assurance claim it cannot support.
///
/// Each line is returned unprefixed/uncolored; callers add indentation and color.
pub(crate) fn trust_surface_lines(functions: &[FunctionProofReport]) -> Vec<String> {
    let surface = TrustSurface::from_functions(functions);
    if surface.total_obligations == 0 {
        return Vec::new();
    }
    let mut out = Vec::new();
    out.push("Trust Surface (deviation from vanilla rustc):".to_string());
    out.push(format!(
        "vanilla rustc accepts this unchanged; Trust added {} obligation{}",
        surface.total_obligations,
        plural(surface.total_obligations),
    ));
    // Counts are written label-first ("proved=N"), not "N proved": the blended
    // summary line above owns the "N proved" / "N unknown" phrasings that the
    // exact-substring report tests assert on, and this surface must not collide
    // with them while restating the same data split by strength of basis.
    let refuted =
        if surface.failed > 0 { format!(", refuted={}", surface.failed) } else { String::new() };
    out.push(format!(
        "additionally proved={} (certified={}, smt-backed={}), runtime-checked={}, left unknown={}, rests on assumed/trusted={} (contract-assumed={}, fully-trusted={}){}",
        surface.additionally_proved(),
        surface.certified,
        surface.smt_backed,
        surface.runtime_checked,
        surface.unknown,
        surface.assumed_or_trusted(),
        surface.contract_assumed,
        surface.fully_trusted,
        refuted,
    ));
    out
}

fn plural(n: usize) -> &'static str {
    if n == 1 { "" } else { "s" }
}

fn format_kind_map(label: &str, map: &BTreeMap<String, usize>) -> Option<String> {
    if map.is_empty() {
        return None;
    }
    let parts: Vec<String> = map.iter().map(|(kind, count)| format!("{kind}={count}")).collect();
    Some(format!("{label} by kind: {}", parts.join(", ")))
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

/// Human-readable label for a function or crate-level verdict.
pub fn function_verdict_label(verdict: FunctionVerdict) -> &'static str {
    match verdict {
        FunctionVerdict::Verified => "VERIFIED",
        FunctionVerdict::RuntimeChecked => "RUNTIME CHECKED",
        FunctionVerdict::HasViolations => "VIOLATIONS",
        FunctionVerdict::Inconclusive => "INCONCLUSIVE",
        FunctionVerdict::NoObligations => "NO OBLIGATIONS",
        _ => "unknown",
    }
}

/// Human-readable label for a proof strength.
pub fn proof_strength_label(strength: &ProofStrength) -> String {
    use trust_types::ReasoningKind;
    let reasoning = match &strength.reasoning {
        ReasoningKind::Smt => "SMT UNSAT".to_string(),
        ReasoningKind::BoundedModelCheck { depth } => format!("BOUNDED (depth {depth})"),
        ReasoningKind::Inductive => "INDUCTIVE".to_string(),
        ReasoningKind::Deductive => "DEDUCTIVE".to_string(),
        ReasoningKind::Constructive => "CONSTRUCTIVE".to_string(),
        ReasoningKind::Pdr => "PDR".to_string(),
        ReasoningKind::ChcSpacer => "CHC/SPACER".to_string(),
        _ => "UNKNOWN".to_string(),
    };
    if strength.is_bounded()
        && let Some(depth) = strength.bounded_depth()
    {
        return format!("{reasoning} [bounded depth {depth}]");
    }
    reasoning
}

/// Human-readable label for a `ProofEvidence` (the #190 replacement for `ProofStrength`).
///
/// Converts a `ProofStrength` to `ProofEvidence` via `From` and then formats both
/// the reasoning method and assurance level. This is the first downstream caller
/// of `ProofEvidence` outside trust-types.
pub fn proof_evidence_label(strength: &ProofStrength) -> String {
    proof_evidence_label_with_monitor(strength, None)
}

/// Human-readable multi-axis proof label with the exact clause monitor status
/// attached to the independent executability axis.
///
/// Static proof and runtime executability are deliberately orthogonal. A
/// clause can be statically proved yet explicitly unmonitored, or carry a
/// distinct E5 `measured` evaluator/placement record.
pub fn proof_evidence_label_with_monitor(
    strength: &ProofStrength,
    monitor: Option<&TransportMonitorEvidence>,
) -> String {
    let evidence: ProofEvidence = strength.clone().into();
    let reasoning = match &evidence.reasoning {
        ReasoningKind::Smt => "SMT UNSAT",
        ReasoningKind::BoundedModelCheck { .. } => "BOUNDED",
        ReasoningKind::Inductive => "INDUCTIVE",
        ReasoningKind::Deductive => "DEDUCTIVE",
        ReasoningKind::Constructive => "CONSTRUCTIVE",
        ReasoningKind::Pdr => "PDR",
        ReasoningKind::ChcSpacer => "CHC/SPACER",
        _ => "UNKNOWN",
    };
    let assurance = match &evidence.assurance {
        AssuranceLevel::Certified => "certified",
        AssuranceLevel::SmtBacked => "smt-backed",
        AssuranceLevel::Trusted => "trusted",
        AssuranceLevel::Unchecked => "unchecked",
        AssuranceLevel::BoundedSound { .. } => "trusted",
        _ => "unknown",
    };
    let grade = evidence.grade_with_monitor(monitor);
    let validation = match &grade.validation {
        ProofValidation::KernelRechecked => "kernel-rechecked",
        ProofValidation::SolverValidated => "solver-validated",
        ProofValidation::SoundAnalysis => "sound-analysis",
        ProofValidation::TrustedVerdict => "trusted-verdict",
        ProofValidation::BoundedExploration => "bounded-exploration",
        ProofValidation::FiniteModelCheck => "finite-model-check",
        ProofValidation::HeuristicOnly => "heuristic",
        ProofValidation::Unvalidated => "unvalidated",
        ProofValidation::Pending => "pending",
        _ => "unknown",
    };
    let closure = match &grade.axiom_closure {
        AxiomClosure::Empty => "empty".to_string(),
        AxiomClosure::Named(names) => format!("named:{}", names.len()),
        AxiomClosure::Unrecorded => "unrecorded".to_string(),
        _ => "unknown".to_string(),
    };
    let coverage = match &grade.coverage {
        CoverageBound::Unbounded => "unbounded".to_string(),
        CoverageBound::UnwindBounded { depth } => format!("unwind:{depth}"),
        CoverageBound::ModelBounded { size } => format!("model:{size}"),
        CoverageBound::Unrecorded => "unrecorded".to_string(),
        _ => "unknown".to_string(),
    };
    let execution = match grade.executability {
        Executability::Monitored => "monitored",
        Executability::Measured => "measured",
        Executability::Unmonitored => "unmonitored",
        Executability::Unrecorded => "unrecorded",
        _ => "unknown",
    };
    let reflection = match grade.reflection {
        ReflectionTier::Fragment(id) => format!("fragment:{id}"),
        ReflectionTier::Unlinked => "unlinked".to_string(),
        ReflectionTier::Unrecorded => "unrecorded".to_string(),
        _ => "unknown".to_string(),
    };
    format!(
        "{reasoning} ({assurance}; validation={validation}, closure={closure}, coverage={coverage}, execution={execution}, reflection={reflection})"
    )
}

/// Human-readable rendering of runtime-monitor evidence for a clause whose
/// static outcome has no proof-strength label of its own.
pub fn monitor_evidence_label(monitor: &TransportMonitorEvidence) -> String {
    let execution = monitor_executability_label(monitor);
    format!("executability: {execution} ({}; {})", monitor.reason, monitor.predicate_digest)
}

/// Compact value for report tables that still uses the typed §7 mapping.
pub fn monitor_executability_label(monitor: &TransportMonitorEvidence) -> &'static str {
    match monitor.status.executability() {
        Executability::Monitored => "monitored",
        Executability::Measured => "measured",
        Executability::Unmonitored => "unmonitored",
        Executability::Unrecorded => "unrecorded",
        _ => "unknown",
    }
}

#[cfg(test)]
mod multi_axis_grade_output_tests {
    use super::*;

    #[test]
    fn report_label_surfaces_every_grade_axis_without_upgrading_standing() {
        let label = proof_evidence_label(&ProofStrength::bounded(17));
        assert!(label.contains("BOUNDED"));
        assert!(label.contains("validation=bounded-exploration"));
        assert!(label.contains("closure=unrecorded"));
        assert!(label.contains("coverage=unwind:17"));
        assert!(label.contains("execution=unrecorded"));
        assert!(label.contains("reflection=unrecorded"));
        assert!(!label.contains("kernel-rechecked"));
    }

    #[test]
    fn unmatched_e4_row_reports_explicitly_unmonitored_execution() {
        let monitor = TransportMonitorEvidence {
            status: TransportMonitorStatus::Unmonitored,
            reason: "no kernel-certified loop monitor evidence matched this row".into(),
            predicate_digest: format!("sha256:{}", "e".repeat(64)),
        };
        let label = proof_evidence_label_with_monitor(&ProofStrength::inductive(), Some(&monitor));

        assert!(label.contains("INDUCTIVE"));
        assert!(label.contains("execution=unmonitored"));
        assert!(!label.contains("execution=monitored"));
    }

    #[test]
    fn e5_scalar_binding_reports_measured_not_boolean_monitored() {
        let measure = TransportMonitorEvidence {
            status: TransportMonitorStatus::Measured,
            reason: "kernel-bound scalar plus authenticated transition placement".into(),
            predicate_digest: format!("sha256:{}", "f".repeat(64)),
        };
        let label = proof_evidence_label_with_monitor(&ProofStrength::inductive(), Some(&measure));

        assert!(label.contains("execution=measured"));
        assert_eq!(monitor_executability_label(&measure), "measured");
        assert!(monitor_evidence_label(&measure).contains("executability: measured"));
    }
}

/// Human-readable label for the strongest proof level seen in a function.
pub fn proof_level_label(level: Option<ProofLevel>) -> &'static str {
    match level {
        None => "none",
        Some(ProofLevel::L0Safety) => "L0 safety",
        Some(ProofLevel::L1Functional) => "L1 functional",
        Some(ProofLevel::L2Domain) => "L2 domain",
        _ => "unknown",
    }
}

#[cfg(test)]
mod kind_breakdown_tests {
    use super::*;

    fn ob(kind: &str, outcome: ObligationOutcome) -> ObligationReport {
        ObligationReport {
            obligation_id: None,
            description: kind.to_string(),
            kind: kind.to_string(),
            proof_level: ProofLevel::L0Safety,
            location: None,
            outcome,
            solver: "ay".to_string(),
            time_ms: 1,
            evidence: None,
            proof_evidence: None,
            transport_evidence: None,
        }
    }

    fn proved() -> ObligationOutcome {
        ObligationOutcome::Proved { strength: ProofStrength::smt_unsat() }
    }

    #[test]
    fn per_kind_breakdown_shows_composition_not_a_blended_total() {
        let obligations = vec![
            ob("arithmetic_overflow", proved()),
            ob("arithmetic_overflow", proved()),
            ob("bounds_check", proved()),
            ob("custom", ObligationOutcome::Unknown { reason: "unsupported MIR".to_string() }),
            ob("custom", ObligationOutcome::Unknown { reason: "unsupported MIR".to_string() }),
            ob("arithmetic_overflow", ObligationOutcome::Failed { counterexample: None }),
        ];
        let mut breakdown = KindBreakdown::default();
        breakdown.add(&obligations);
        let joined = breakdown.lines("  ").join("\n");

        // The composition of "proved" is visible by kind — never a blended total.
        assert!(
            joined.contains("proved by kind: arithmetic_overflow=2, bounds_check=1"),
            "got:\n{joined}"
        );
        // Lowering-gap `custom` markers surface as unknown, never as proved.
        assert!(joined.contains("unknown by kind: custom=2"), "got:\n{joined}");
        assert!(joined.contains("failed by kind: arithmetic_overflow=1"), "got:\n{joined}");
        // Empty buckets are omitted.
        assert!(!joined.contains("runtime-checked by kind"), "got:\n{joined}");
    }

    #[test]
    fn design_requirement_is_not_counted_as_any_outcome() {
        let obligations = vec![ob(
            "hardened_boundary",
            ObligationOutcome::DesignRequirement { detail: "x".into() },
        )];
        let mut breakdown = KindBreakdown::default();
        breakdown.add(&obligations);
        assert!(breakdown.lines("  ").is_empty(), "a design mandate is not a proof outcome");
    }
}
