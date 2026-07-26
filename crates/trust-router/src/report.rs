// trust-router/report.rs: Native router proof report adapter
//
// Converts per-obligation verifier results into the canonical JSON report
// shape without collapsing unattributed backend proofs into successes.

use trust_types::{
    AssuranceLevel, BinOp, Counterexample, CounterexampleReport, CounterexampleValue,
    CounterexampleVariable, CrateSummary, CrateVerdict, FunctionProofReport, FunctionSummary,
    FunctionVerdict, JsonProofReport, ObligationEvidenceProvenanceReport, ObligationOutcome,
    ObligationProofEvidenceReport, ObligationReport, ProofLevel, ReportMetadata, SourceSpan,
    VcKind, VerificationResult,
};

/// Minimum assurance for a `Proved` to be REPORTED as proved. Per the assurance
/// design (`result.rs` `require_assurance`/`AssuranceLevel`), a real reported
/// proof requires `SmtBacked` or stronger; weaker results (`Unchecked` — a bare
/// unvalidated solver "unsat", `Heuristic`, etc.) are downgraded to `Unknown`.
const MIN_REPORTED_ASSURANCE: AssuranceLevel = AssuranceLevel::SmtBacked;

use crate::verifier_result::{
    ObligationEvidenceProvenance, ObligationProofEvidence, VerifierFunctionResult,
};

const ROUTER_REPORT_SCHEMA_VERSION: &str = "0.1.0";
const ROUTER_REPORT_TRUST_VERSION: &str = env!("CARGO_PKG_VERSION");

/// Build a canonical JSON report from native router per-obligation results.
///
/// Unattributed backend proofs never increment `proved`/`total_proved`; the
/// publication gate demotes their optimistic summary count to
/// `unattributed_unknown`. Attributed `VerificationResult` and
/// `ObligationProofEvidence` values are also public status records, not proof
/// authority: raw certificate bytes and strength labels cannot publish a proof
/// without the exact request-bound TrustIr artifact graph and matching
/// transport evidence.
#[must_use]
pub fn build_json_report_from_verifier_results(
    crate_name: &str,
    results: &[VerifierFunctionResult],
) -> JsonProofReport {
    let start = std::time::Instant::now();
    let mut functions: Vec<FunctionProofReport> =
        results.iter().map(build_function_report).collect();
    functions.sort_by(|a, b| a.function.cmp(&b.function));

    let summary = build_crate_summary(&functions);
    let total_time_ms = start.elapsed().as_millis() as u64
        + functions.iter().map(|function| function.summary.total_time_ms).sum::<u64>();

    let mut report = JsonProofReport {
        metadata: ReportMetadata {
            schema_version: ROUTER_REPORT_SCHEMA_VERSION.to_string(),
            trust_version: ROUTER_REPORT_TRUST_VERSION.to_string(),
            timestamp: now_timestamp(),
            total_time_ms,
            timeout_ms: None,
            function_budget_ms: None,
        },
        crate_name: crate_name.to_string(),
        summary,
        functions,
        hardened: None,
        assumptions: Vec::new(),
        cargo_proof_inventory: None,
        verification_gate: None,
    };

    // Reuse the canonical publication gate at the live in-memory boundary.
    // Besides validating evidence, it recomputes every summary and verdict, so
    // a freely constructed result cannot leave stale positive counts behind.
    let _ = report.sanitize_deserialized();
    report
}

fn build_function_report(result: &VerifierFunctionResult) -> FunctionProofReport {
    let obligations: Vec<ObligationReport> = result
        .obligations
        .iter()
        .map(|obligation_result| {
            let proof_evidence = obligation_result.evidence.as_ref().map(proof_evidence_report);
            ObligationReport {
                obligation_id: Some(obligation_result.obligation.id.to_string()),
                description: obligation_result.obligation.kind.description(),
                kind: result_kind_tag(
                    &obligation_result.obligation.kind,
                    &obligation_result.result,
                ),
                proof_level: obligation_result.obligation.kind.proof_level(),
                location: span_to_location(&obligation_result.obligation.span),
                outcome: raw_result_to_outcome(&obligation_result.result),
                solver: obligation_result.result.solver_name().to_string(),
                time_ms: obligation_result.result.time_ms(),
                evidence: proof_evidence.as_ref().map(|evidence| evidence.evidence.clone()),
                proof_evidence,
                transport_evidence: None,
            }
        })
        .collect();

    let mut summary = build_function_summary(&obligations);
    summary.unattributed_failed = result.summary.unattributed_failed;
    summary.unattributed_unknown = result.summary.unattributed_unknown;
    summary.unattributed_proved = result.summary.unattributed_proved;
    summary.total_time_ms +=
        result.unattributed.iter().map(|artifact| artifact.result.time_ms()).sum::<u64>();
    summary.verdict = function_verdict(&summary);

    FunctionProofReport { function: result.def_path.clone(), summary, obligations }
}

fn proof_evidence_report(evidence: &ObligationProofEvidence) -> ObligationProofEvidenceReport {
    ObligationProofEvidenceReport {
        suite: None,
        backend: evidence.verifier.clone(),
        request_id: None,
        proof_id: None,
        native_id: None,
        status: None,
        provenance: match &evidence.provenance {
            ObligationEvidenceProvenance::RouterAttributed => {
                ObligationEvidenceProvenanceReport::RouterAttributed
            }
            ObligationEvidenceProvenance::NativeBackend { verifier } => {
                ObligationEvidenceProvenanceReport::NativeBackend { verifier: verifier.clone() }
            }
        },
        strength: evidence.strength.clone(),
        evidence: evidence.evidence.clone(),
        proof_certificate: evidence.proof_certificate.clone(),
        native_trust_ir: None,
        artifacts: Vec::new(),
        diagnostics: Vec::new(),
        solver_warnings: evidence.solver_warnings.clone(),
    }
}

fn raw_result_to_outcome(result: &VerificationResult) -> ObligationOutcome {
    // (un-forgeable-Proved gate): this is the single boundary
    // every result flows through on its way to a reported outcome. Apply the
    // assurance gate HERE so no upstream path — cache replay, transport/JSON
    // deserialize, a hand-built result — can surface a reported `Proved` from
    // unvalidated/heuristic/forged assurance. A `Proved` below the floor becomes
    // `Unknown` (a sound false-FAIL), never a false-PROVE.
    let gated = result.clone().require_assurance(MIN_REPORTED_ASSURANCE);
    let result = &gated;
    match result {
        VerificationResult::Proved { strength, .. } => {
            ObligationOutcome::Proved { strength: strength.clone() }
        }
        VerificationResult::Failed { counterexample, .. } => {
            ObligationOutcome::Failed { counterexample: counterexample.as_ref().map(cex_to_report) }
        }
        VerificationResult::Unknown { reason, .. } => ObligationOutcome::Unknown {
            reason: result.release_blocking_proof_gap_reason().unwrap_or_else(|| reason.clone()),
        },
        VerificationResult::Timeout { timeout_ms, .. } => {
            ObligationOutcome::Timeout { timeout_ms: *timeout_ms }
        }
        _ => ObligationOutcome::Unknown {
            reason: "unhandled verification result variant".to_string(),
        },
    }
}

fn build_function_summary(obligations: &[ObligationReport]) -> FunctionSummary {
    let mut proved = 0usize;
    let mut runtime_checked = 0usize;
    let mut failed = 0usize;
    let mut unknown = 0usize;
    let mut timed_out = 0usize;
    let mut design_requirements = 0usize;
    let mut total_time_ms = 0u64;
    let mut max_proof_level: Option<ProofLevel> = None;

    for obligation in obligations {
        match &obligation.outcome {
            ObligationOutcome::Proved { .. } => proved += 1,
            ObligationOutcome::RuntimeChecked { .. } => runtime_checked += 1,
            ObligationOutcome::Failed { .. } => failed += 1,
            ObligationOutcome::Unknown { .. } => unknown += 1,
            ObligationOutcome::Timeout { .. } => {
                unknown += 1;
                timed_out += 1;
            }
            ObligationOutcome::DesignRequirement { .. } => design_requirements += 1,
            _ => {}
        }
        total_time_ms += obligation.time_ms;
        max_proof_level = Some(match max_proof_level {
            None => obligation.proof_level,
            Some(current) => current.max(obligation.proof_level),
        });
    }

    let mut summary = FunctionSummary {
        total_obligations: obligations.len(),
        proved,
        runtime_checked,
        failed,
        unknown,
        timed_out,
        design_requirements,
        unattributed_failed: 0,
        unattributed_unknown: 0,
        unattributed_proved: 0,
        total_time_ms,
        max_proof_level,
        verdict: FunctionVerdict::NoObligations,
    };
    summary.verdict = function_verdict(&summary);
    summary
}

fn function_verdict(summary: &FunctionSummary) -> FunctionVerdict {
    trust_types::ScopeVerdict::from_counts(trust_types::ScopeVerdictCounts::from(summary))
}

fn build_crate_summary(functions: &[FunctionProofReport]) -> CrateSummary {
    let mut functions_verified = 0usize;
    let mut functions_runtime_checked = 0usize;
    let mut functions_with_violations = 0usize;
    let mut functions_inconclusive = 0usize;
    let mut total_obligations = 0usize;
    let mut total_proved = 0usize;
    let mut total_runtime_checked = 0usize;
    let mut total_failed = 0usize;
    let mut total_unknown = 0usize;
    let mut total_timed_out = 0usize;
    let mut total_design_requirements = 0usize;
    let mut total_unattributed_failed = 0usize;
    let mut total_unattributed_unknown = 0usize;
    let mut total_unattributed_proved = 0usize;

    for function in functions {
        match function.summary.verdict {
            FunctionVerdict::Verified => functions_verified += 1,
            FunctionVerdict::RuntimeChecked => functions_runtime_checked += 1,
            FunctionVerdict::HasViolations => functions_with_violations += 1,
            FunctionVerdict::Inconclusive => functions_inconclusive += 1,
            FunctionVerdict::NoObligations => {}
            _ => {}
        }
        total_obligations += function.summary.total_obligations;
        total_proved += function.summary.proved;
        total_runtime_checked += function.summary.runtime_checked;
        total_failed += function.summary.failed;
        total_unknown += function.summary.unknown;
        total_timed_out += function.summary.timed_out;
        total_design_requirements += function.summary.design_requirements;
        total_unattributed_failed += function.summary.unattributed_failed;
        total_unattributed_unknown += function.summary.unattributed_unknown;
        total_unattributed_proved += function.summary.unattributed_proved;
    }

    let verdict = if functions.is_empty()
        || (total_obligations == 0
            && total_unattributed_failed == 0
            && total_unattributed_unknown == 0
            && total_unattributed_proved == 0)
    {
        CrateVerdict::NoObligations
    } else if total_failed > 0 || total_unattributed_failed > 0 {
        CrateVerdict::HasViolations
    } else if total_unknown > 0 || total_unattributed_unknown > 0 || total_unattributed_proved > 0 {
        CrateVerdict::Inconclusive
    } else if total_runtime_checked > 0 {
        CrateVerdict::RuntimeChecked
    } else if total_proved == total_obligations && total_proved > 0 {
        CrateVerdict::Verified
    } else {
        // positive invariant — see `function_verdict`.
        CrateVerdict::Inconclusive
    };

    CrateSummary {
        functions_analyzed: functions.len(),
        functions_verified,
        functions_runtime_checked,
        functions_with_violations,
        functions_inconclusive,
        total_obligations,
        total_proved,
        total_runtime_checked,
        total_failed,
        total_unknown,
        total_timed_out,
        total_design_requirements,
        total_unattributed_failed,
        total_unattributed_unknown,
        total_unattributed_proved,
        proof_grade_engine_statuses: Vec::new(),
        verdict,
    }
}

fn span_to_location(span: &SourceSpan) -> Option<SourceSpan> {
    if span.file.is_empty() && span.line_start == 0 { None } else { Some(span.clone()) }
}

fn cex_to_report(cex: &Counterexample) -> CounterexampleReport {
    CounterexampleReport {
        variables: cex
            .assignments
            .iter()
            .map(|(name, value)| {
                let (value_string, value_type) = match value {
                    CounterexampleValue::Bool(value) => (value.to_string(), "bool"),
                    CounterexampleValue::Int(value) => (value.to_string(), "int"),
                    CounterexampleValue::Uint(value) => (value.to_string(), "uint"),
                    CounterexampleValue::Float(value) => (value.to_string(), "float"),
                    _ => ("unknown".to_string(), "unknown"),
                };
                CounterexampleVariable {
                    name: name.clone(),
                    value: value_string,
                    value_type: value_type.to_string(),
                    display: value.to_string(),
                }
            })
            .collect(),
    }
}

fn result_kind_tag(kind: &VcKind, result: &VerificationResult) -> String {
    if matches!(result, VerificationResult::Timeout { .. }) {
        "solver_timeout".to_string()
    } else if result.is_memory_guard_solver_skip() {
        "memory_guard_resource_proof_gap".to_string()
    } else {
        vc_kind_tag(kind)
    }
}

fn vc_kind_tag(kind: &VcKind) -> String {
    if let Some(tag) = kind.hardened_family_tag() {
        return tag;
    }
    if let Some(tag) = unsupported_mir_kind_tag(kind) {
        return tag.to_string();
    }

    match kind {
        VcKind::ArithmeticOverflow { op, .. } => format!("arithmetic_overflow_{}", op_tag(op)),
        VcKind::ShiftOverflow { op, .. } => format!("shift_overflow_{}", op_tag(op)),
        VcKind::DivisionByZero => "division_by_zero".to_string(),
        VcKind::RemainderByZero => "remainder_by_zero".to_string(),
        VcKind::IndexOutOfBounds => "index_out_of_bounds".to_string(),
        VcKind::SliceBoundsCheck => "slice_bounds_check".to_string(),
        VcKind::CastOverflow { .. } => "cast_overflow".to_string(),
        VcKind::NegationOverflow { .. } => "negation_overflow".to_string(),
        VcKind::Assertion { .. } => "assertion".to_string(),
        VcKind::Precondition { .. } => "precondition".to_string(),
        VcKind::Postcondition => "postcondition".to_string(),
        VcKind::UnsupportedMir { .. } => "unsupported_mir".to_string(),
        VcKind::Unreachable => "unreachable".to_string(),
        VcKind::DeadState { .. } => "dead_state".to_string(),
        VcKind::Deadlock => "deadlock".to_string(),
        VcKind::Temporal { .. } => "temporal".to_string(),
        VcKind::Liveness { .. } => "liveness".to_string(),
        VcKind::Fairness { .. } => "fairness".to_string(),
        VcKind::TaintViolation { .. } => "taint_violation".to_string(),
        VcKind::RefinementViolation { .. } => "refinement_violation".to_string(),
        VcKind::ResilienceViolation { .. } => "resilience_violation".to_string(),
        VcKind::ProtocolViolation { .. } => "protocol_violation".to_string(),
        VcKind::NonTermination { .. } => "non_termination".to_string(),
        VcKind::DataRace { .. } => "data_race".to_string(),
        VcKind::InsufficientOrdering { .. } => "insufficient_ordering".to_string(),
        VcKind::TranslationValidation { .. } => "translation_validation".to_string(),
        VcKind::FloatDivisionByZero => "float_division_by_zero".to_string(),
        VcKind::FloatOverflowToInfinity { .. } => "float_overflow_to_infinity".to_string(),
        VcKind::InvalidDiscriminant { .. } => "invalid_discriminant".to_string(),
        VcKind::AggregateArrayLengthMismatch { .. } => {
            "aggregate_array_length_mismatch".to_string()
        }
        VcKind::UnsafeOperation { .. } => "unsafe_operation".to_string(),
        _ => "unknown".to_string(),
    }
}

fn unsupported_mir_kind_tag(kind: &VcKind) -> Option<&'static str> {
    let VcKind::UnsupportedMir { kind, detail } = kind else {
        return None;
    };
    if kind == "SourceBackpropagationGateBlocker" || kind == "source_backpropagation_gate" {
        return Some(source_backpropagation_gate_kind_tag(detail));
    }
    if is_symbolic_formula_not_consumed_kind(kind) {
        return Some("trust_symbolic_formula_not_consumed");
    }
    if kind == "ConcurrencyOrderingCoverageGap" {
        return Some("concurrency_ordering_coverage_gap");
    }
    if kind != "AArch64AtomicSemanticFactNotProofConsumed" {
        return Some("unsupported_mir");
    }

    let detail = detail.to_ascii_lowercase();
    if detail.contains("exclusive_monitor=loadreserve")
        || detail.contains("exclusive_monitor=storeconditional")
        || detail.contains("exclusive-monitor")
    {
        if detail.contains("store-conditional status result")
            || detail.contains("status semantics")
            || detail.contains("reports_status=true")
        {
            return Some("aarch64_exclusive_monitor_status_unsupported");
        }
        return Some("aarch64_exclusive_monitor_unsupported");
    }
    if detail.contains("ordering=acquire")
        || detail.contains("opcode=ldar")
        || detail.contains("acquire ordering")
    {
        return Some("aarch64_atomic_acquire_ordering_unsupported");
    }
    if detail.contains("ordering=release")
        || detail.contains("opcode=stlr")
        || detail.contains("release ordering")
    {
        return Some("aarch64_atomic_release_ordering_unsupported");
    }
    Some("aarch64_atomic_semantics_unsupported")
}

fn is_symbolic_formula_not_consumed_kind(kind: &str) -> bool {
    matches!(
        kind,
        "TrustSymbolicFormulaNotProofConsumed"
            | "SymbolicFormulaNotProofConsumed"
            | "trust_symbolic.formula"
    )
}

fn source_backpropagation_gate_kind_tag(detail: &str) -> &'static str {
    let detail = detail.to_ascii_lowercase();
    let normalized = detail.replace(['_', '-'], " ");
    if detail.contains("missing_reconstruction")
        || normalized.contains("missing reconstruction")
        || normalized.contains("accepted reconstruction")
    {
        "source_backpropagation_missing_reconstruction"
    } else if detail.contains("type_ownership")
        || normalized.contains("type ownership")
        || normalized.contains("exact source type fact ownership")
        || normalized.contains("source type fact ownership")
        || normalized.contains("type fact owner")
        || normalized.contains("type fact ownership")
    {
        "source_backpropagation_type_ownership"
    } else if detail.contains("exact_source_provenance")
        || normalized.contains("exact source provenance")
    {
        "source_backpropagation_exact_source_provenance"
    } else if detail.contains("target_validation")
        || normalized.contains("target validation")
        || normalized.contains("target semantic")
        || normalized.contains("target proof consumer")
        || detail.contains("target/formula consumer")
        || detail.contains("target/formula consumers")
        || normalized.contains("target formula consumer")
        || normalized.contains("formula consumer")
        || detail.contains("trust_symbolic.formula")
        || detail.contains("binary-proof-obligation-pending-refinement-metadata")
        || normalized.contains("pending refinement metadata")
        || normalized.contains("bidirectional refinement")
    {
        "source_backpropagation_target_validation"
    } else if detail.contains("checked_certificate_identity")
        || normalized.contains("checked certificate identity")
        || normalized.contains("checked certificate readback")
        || normalized.contains("checked proof cert readback")
        || normalized.contains("proof cert readback")
        || normalized.contains("proof certificate readback")
        || normalized.contains("certificate identity")
        || normalized.contains("proof certificate identity")
    {
        "source_backpropagation_checked_certificate_identity"
    } else if detail.contains("replay_identity")
        || normalized.contains("replay identity")
        || normalized.contains("replay attestation")
        || normalized.contains("replay backend attested")
        || normalized.contains("replay attested")
        || normalized.contains("replay byte/range identity")
        || normalized.contains("replay byte range identity")
        || normalized.contains("byte range identity")
        || normalized.contains("step witness")
        || normalized.contains("machine effect witness")
        || normalized.contains("effect witness")
        || normalized.contains("concrete scalar memory address")
        || normalized.contains("replay source backprop")
    {
        "source_backpropagation_replay_identity"
    } else {
        "source_backpropagation_gate_unsupported"
    }
}

fn op_tag(op: &BinOp) -> &'static str {
    match op {
        BinOp::Add => "add",
        BinOp::Sub => "sub",
        BinOp::Mul => "mul",
        BinOp::Div => "div",
        BinOp::Rem => "rem",
        BinOp::Shl => "shl",
        BinOp::Shr => "shr",
        BinOp::Eq => "eq",
        BinOp::Ne => "ne",
        BinOp::Lt => "lt",
        BinOp::Le => "le",
        BinOp::Gt => "gt",
        BinOp::Ge => "ge",
        BinOp::BitAnd => "bitand",
        BinOp::BitOr => "bitor",
        BinOp::BitXor => "bitxor",
        BinOp::Cmp => "cmp",
        _ => "unknown",
    }
}

fn now_timestamp() -> String {
    let now = std::time::SystemTime::now();
    let duration = now.duration_since(std::time::UNIX_EPOCH).unwrap_or_default();
    duration.as_secs().to_string()
}

#[cfg(test)]
mod tests {
    use trust_types::{
        BinOp, Formula, HardenedVcCategory, ObligationEvidenceProvenanceReport, ProofStrength,
        SourceSpan, Ty, VcKind, VerificationCondition, VerificationResult,
    };

    use super::*;
    use crate::{VerifierFunctionResult, VerifierObligationResult, descriptors_for_vcs};

    #[test]
    fn unchecked_proved_is_gated_to_unknown_at_report_boundary() {
        // a `Proved` carrying only `Unchecked` assurance (a
        // bare unvalidated solver "unsat", e.g. a poisoned/corrupt cache replay)
        // must NOT surface as a reported proof — the report boundary downgrades
        // it to Unknown (a sound false-FAIL), never a false-PROVE.
        let unchecked = VerificationResult::Proved {
            solver: "cached:x".into(),
            time_ms: 0,
            strength: ProofStrength::smt_unsat_unvalidated(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        };
        assert!(
            matches!(raw_result_to_outcome(&unchecked), ObligationOutcome::Unknown { .. }),
            "Unchecked Proved must be gated to Unknown, not reported as proved"
        );

        // A genuine SMT-backed proof (>= SmtBacked) still reports as Proved.
        let backed = VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: 1,
            strength: ProofStrength::inductive(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        };
        assert!(
            matches!(raw_result_to_outcome(&backed), ObligationOutcome::Proved { .. }),
            "a real proof must still report as Proved"
        );
    }

    fn vc(kind: VcKind, function: &str) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: function.into(),
            location: SourceSpan {
                file: "src/lib.rs".to_string(),
                line_start: 7,
                col_start: 1,
                line_end: 7,
                col_end: 10,
            },
            formula: Formula::Bool(true),
            contract_metadata: None,
        }
    }

    #[test]
    fn native_status_evidence_is_serialized_but_not_published_as_proof() {
        let vc = vc(VcKind::Postcondition, "crate::f");
        let descriptor = descriptors_for_vcs([&vc], None).remove(0);
        let function_result = VerifierFunctionResult::from_function_level_result(
            "crate::f".to_string(),
            "trust-wp-lib",
            vec![descriptor],
            VerificationResult::Proved {
                solver: "trust-wp-lib".into(),
                time_ms: 12,
                strength: ProofStrength::inductive(),
                proof_certificate: Some(vec![1, 2, 3]),
                solver_warnings: Some(vec!["kept native certificate".to_string()]),
                native_proof_envelope: None,
            },
        );

        let report = build_json_report_from_verifier_results("native", &[function_result]);
        assert_eq!(report.summary.total_proved, 0);
        assert_eq!(report.summary.total_unknown, 1);
        assert_eq!(report.summary.verdict, CrateVerdict::Inconclusive);
        assert_eq!(report.summary.total_unattributed_proved, 0);

        let obligation = &report.functions[0].obligations[0];
        assert!(obligation.obligation_id.as_deref().is_some_and(|id| id.contains(':')));
        let evidence = obligation.proof_evidence.as_ref().expect("proof evidence");
        assert_eq!(evidence.backend, "trust-wp-lib");
        assert_eq!(evidence.strength, ProofStrength::inductive());
        assert_eq!(evidence.proof_certificate.as_deref(), Some(&[1, 2, 3][..]));
        assert!(matches!(
            &obligation.outcome,
            ObligationOutcome::Unknown { reason }
                if reason.contains("proof_evidence.suite is missing")
        ));
        assert!(matches!(
            evidence.provenance,
            ObligationEvidenceProvenanceReport::NativeBackend { ref verifier }
                if verifier == "trust-wp-lib"
        ));

        let json = serde_json::to_value(&report).expect("serialize report");
        assert!(json["functions"][0]["obligations"][0]["obligation_id"].is_string());
        assert_eq!(
            json["functions"][0]["obligations"][0]["proof_evidence"]["backend"],
            "trust-wp-lib"
        );
    }

    #[test]
    fn memory_guard_solver_skip_is_release_blocking_proof_gap_in_native_report() {
        let vc = vc(VcKind::Postcondition, "crate::memory_guard");
        let descriptor = descriptors_for_vcs([&vc], None).remove(0);
        let function_result = VerifierFunctionResult::from_function_level_result(
            "crate::memory_guard".to_string(),
            "memory-guard",
            vec![descriptor],
            VerificationResult::Unknown {
                solver: "memory-guard".into(),
                time_ms: 0,
                reason: "memory limit exceeded: 2048MB used, 1024MB limit (peak: 2048MB) - skipping solver dispatch".to_string(),
            },
        );

        let report = build_json_report_from_verifier_results("native", &[function_result]);
        let obligation = &report.functions[0].obligations[0];

        assert_eq!(report.summary.total_unknown, 1);
        assert_eq!(report.summary.verdict, CrateVerdict::Inconclusive);
        assert_eq!(obligation.kind, "memory_guard_resource_proof_gap");
        assert_eq!(obligation.solver, "memory-guard");
        assert!(matches!(
            &obligation.outcome,
            ObligationOutcome::Unknown { reason }
                if reason.contains("release-blocking proof gap")
                    && reason.contains("memory guard skipped solver dispatch")
        ));
    }

    #[test]
    fn solver_timeout_is_visible_as_release_blocking_report_kind() {
        let vc = vc(VcKind::Postcondition, "crate::timeout");
        let descriptor = descriptors_for_vcs([&vc], None).remove(0);
        let function_result = VerifierFunctionResult::from_function_level_result(
            "crate::timeout".to_string(),
            "trust-wp-lib",
            vec![descriptor],
            VerificationResult::Timeout { solver: "trust-wp-lib".into(), timeout_ms: 30_000 },
        );

        let report = build_json_report_from_verifier_results("native", &[function_result]);
        let obligation = &report.functions[0].obligations[0];

        assert_eq!(report.summary.total_unknown, 1);
        assert_eq!(report.summary.total_timed_out, 1);
        assert_eq!(report.summary.verdict, CrateVerdict::Inconclusive);
        assert_eq!(report.functions[0].summary.timed_out, 1);
        assert_eq!(report.functions[0].summary.verdict, FunctionVerdict::Inconclusive);
        assert_eq!(obligation.kind, "solver_timeout");
        assert_ne!(obligation.kind, "postcondition");
        assert_eq!(obligation.solver, "trust-wp-lib");
        assert!(matches!(
            &obligation.outcome,
            ObligationOutcome::Timeout { timeout_ms } if *timeout_ms == 30_000
        ));
        assert!(obligation.proof_evidence.is_none());
    }

    #[test]
    fn mixed_timeout_and_unknown_summaries_keep_unknown_compatibility() {
        let vcs =
            [vc(VcKind::Postcondition, "crate::mixed"), vc(VcKind::DivisionByZero, "crate::mixed")];
        let descriptors = descriptors_for_vcs(vcs.iter(), None);
        let results = [
            VerificationResult::Unknown {
                solver: "trust-wp-lib".into(),
                time_ms: 7,
                reason: "solver returned unknown".to_string(),
            },
            VerificationResult::Timeout { solver: "trust-wp-lib".into(), timeout_ms: 10_000 },
        ];
        let obligations = descriptors
            .into_iter()
            .zip(results)
            .map(|(descriptor, result)| VerifierObligationResult::new(descriptor, result))
            .collect::<Vec<_>>();
        let function_result = VerifierFunctionResult::from_obligation_results(
            "crate::mixed".to_string(),
            obligations,
        );

        let report = build_json_report_from_verifier_results("native", &[function_result]);
        let function_summary = &report.functions[0].summary;

        assert_eq!(function_summary.unknown, 2);
        assert_eq!(function_summary.timed_out, 1);
        assert_eq!(report.summary.total_unknown, 2);
        assert_eq!(report.summary.total_timed_out, 1);
        assert_eq!(function_summary.verdict, FunctionVerdict::Inconclusive);
        assert_eq!(report.summary.verdict, CrateVerdict::Inconclusive);
        assert_eq!(report.functions[0].obligations[0].kind, "postcondition");
        assert_eq!(report.functions[0].obligations[1].kind, "solver_timeout");

        let json = serde_json::to_value(&report).expect("serialize report");
        assert_eq!(json["functions"][0]["summary"]["unknown"], 2);
        assert_eq!(json["functions"][0]["summary"]["timed_out"], 1);
        assert_eq!(json["summary"]["total_unknown"], 2);
        assert_eq!(json["summary"]["total_timed_out"], 1);
    }

    #[test]
    fn unattributed_proved_is_demoted_without_upgrading_unknowns() {
        let vcs = [
            vc(
                VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::u32(), Ty::u32()) },
                "crate::g",
            ),
            vc(VcKind::DivisionByZero, "crate::g"),
        ];
        let descriptors = descriptors_for_vcs(vcs.iter(), None);
        let function_result = VerifierFunctionResult::from_function_level_result(
            "crate::g".to_string(),
            "trust-mc-lib",
            descriptors,
            VerificationResult::Proved {
                solver: "trust-mc-lib".into(),
                time_ms: 9,
                strength: ProofStrength::bounded(8),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        );

        let report = build_json_report_from_verifier_results("native", &[function_result]);

        // The backend returned ONE function-level `Proved` for two obligations
        // with no per-obligation IDs, so it is recorded as an UNATTRIBUTED
        // artifact and the obligations themselves stay `unknown` (never
        // upgraded). `build_json_report_from_verifier_results` finishes through
        // the canonical publication gate (`sanitize_deserialized`), which
        // fail-closes every proof claim that carries no replayed per-obligation
        // evidence — so the unattributed function-level `Proved` is preserved as
        // an unattributed *unknown* residual rather than an unattributed
        // `proved` one. Either way the crate stays Inconclusive with the two
        // obligations unresolved; the gate only refuses to echo an unevidenced
        // positive count. (Pre-hardening this surfaced as
        // total_unattributed_proved == 1; the residual is now carried in
        // total_unattributed_unknown, so no information is dropped.)
        assert_eq!(report.summary.total_obligations, 2);
        assert_eq!(report.summary.total_proved, 0);
        assert_eq!(report.summary.total_unknown, 2);
        assert_eq!(report.summary.total_unattributed_proved, 0);
        assert_eq!(report.summary.total_unattributed_unknown, 1);
        assert_eq!(report.summary.verdict, CrateVerdict::Inconclusive);
        assert_eq!(report.functions[0].summary.unattributed_proved, 0);
        assert_eq!(report.functions[0].summary.unattributed_unknown, 1);
        assert!(
            report.functions[0]
                .obligations
                .iter()
                .all(|obligation| obligation.proof_evidence.is_none())
        );
    }

    #[test]
    fn hardened_boundary_kind_uses_hardened_family_tag_in_native_report() {
        let vc = vc(
            VcKind::HardenedBoundary {
                category: HardenedVcCategory::RawPathApi,
                callee: "std::fs::remove_file".to_string(),
                detail: "path removal re-resolves a mutable direntry".to_string(),
            },
            "crate::hardened_path",
        );
        let descriptors = descriptors_for_vcs([&vc], None);
        let function_result = VerifierFunctionResult::from_function_level_result(
            "crate::hardened_path".to_string(),
            "router",
            descriptors,
            VerificationResult::Unknown {
                solver: "router".into(),
                time_ms: 0,
                reason: "hardened boundary requires stable path identity proof".to_string(),
            },
        );

        let report = build_json_report_from_verifier_results("native", &[function_result]);
        let obligation = &report.functions[0].obligations[0];

        assert_eq!(obligation.kind, "hardened_raw_path_api");
        assert_ne!(obligation.kind, "unknown");
    }

    #[test]
    fn legacy_hardened_functional_correctness_uses_hardened_family_tag_in_native_report() {
        let vc = vc(
            VcKind::FunctionalCorrectness {
                property: "hardened::byte_loss".to_string(),
                context: "to_string_lossy: lossy OS/path conversion".to_string(),
            },
            "crate::hardened_bytes",
        );
        let descriptors = descriptors_for_vcs([&vc], None);
        let function_result = VerifierFunctionResult::from_function_level_result(
            "crate::hardened_bytes".to_string(),
            "router",
            descriptors,
            VerificationResult::Unknown {
                solver: "router".into(),
                time_ms: 0,
                reason: "legacy hardened byte-loss row requires proof evidence".to_string(),
            },
        );

        let report = build_json_report_from_verifier_results("native", &[function_result]);
        let obligation = &report.functions[0].obligations[0];

        assert_eq!(obligation.kind, "hardened_byte_loss");
        assert_ne!(obligation.kind, "unknown");
    }

    #[test]
    fn unsupported_aarch64_atomic_fact_is_visible_in_native_report() {
        let vc = vc(
            VcKind::UnsupportedMir {
                kind: "AArch64AtomicSemanticFactNotProofConsumed".to_string(),
                detail: "opcode=ldar; AArch64 LDAR semantic fact is present but not proof-consumed; missing witnesses: acquire ordering event, synchronization edge, thread identity, happens-before witness; access=Read; ordering=Acquire; exclusive_monitor=None; reports_status=false".to_string(),
            },
            "binary::atomic",
        );
        let descriptors = descriptors_for_vcs([&vc], None);
        let function_result = VerifierFunctionResult::from_function_level_result(
            "binary::atomic".to_string(),
            "router",
            descriptors,
            VerificationResult::Unknown {
                solver: "router".into(),
                time_ms: 0,
                reason: "unsupported MIR AArch64AtomicSemanticFactNotProofConsumed [aarch64_atomic_acquire_ordering_unsupported] preserved in TrustIr: AArch64 LDAR semantic fact is present but not proof-consumed; missing witnesses: acquire ordering event, synchronization edge, thread identity, happens-before witness".to_string(),
            },
        );

        let report = build_json_report_from_verifier_results("binary", &[function_result]);

        assert_eq!(report.summary.total_obligations, 1);
        assert_eq!(report.summary.total_unknown, 1);
        assert_eq!(report.summary.verdict, CrateVerdict::Inconclusive);
        let obligation = &report.functions[0].obligations[0];
        assert_eq!(obligation.kind, "aarch64_atomic_acquire_ordering_unsupported");
        assert!(obligation.description.contains("happens-before witness"));
        assert!(matches!(
            &obligation.outcome,
            ObligationOutcome::Unknown { reason }
                if reason.contains("aarch64_atomic_acquire_ordering_unsupported")
                    && reason.contains("not proof-consumed")
                    && reason.contains("AArch64AtomicSemanticFactNotProofConsumed")
        ));
        assert!(obligation.proof_evidence.is_none());
    }

    #[test]
    fn concurrency_ordering_coverage_gap_is_visible_in_native_report() {
        let detail = "ordering requirement references missing atomic access index 3 \
            (access log length 2); required=Acquire; reason=release/acquire handoff";
        let vc = vc(
            VcKind::UnsupportedMir {
                kind: "ConcurrencyOrderingCoverageGap".to_string(),
                detail: detail.to_string(),
            },
            "crate::concurrency",
        );
        let descriptors = descriptors_for_vcs([&vc], None);
        let function_result = VerifierFunctionResult::from_function_level_result(
            "crate::concurrency".to_string(),
            "router",
            descriptors,
            VerificationResult::Unknown {
                solver: "router".into(),
                time_ms: 0,
                reason: format!(
                    "unsupported MIR ConcurrencyOrderingCoverageGap \
                     [concurrency_ordering_coverage_gap] preserved in TrustIr: {detail}"
                ),
            },
        );

        let report = build_json_report_from_verifier_results("native", &[function_result]);
        let obligation = &report.functions[0].obligations[0];

        assert_eq!(report.summary.total_unknown, 1);
        assert_eq!(report.summary.verdict, CrateVerdict::Inconclusive);
        assert_eq!(report.functions[0].summary.verdict, FunctionVerdict::Inconclusive);
        assert_eq!(obligation.kind, "concurrency_ordering_coverage_gap");
        assert!(obligation.description.contains("ConcurrencyOrderingCoverageGap"));
        assert!(obligation.description.contains("missing atomic access index 3"));
        assert!(matches!(
            &obligation.outcome,
            ObligationOutcome::Unknown { reason }
                if reason.contains("ConcurrencyOrderingCoverageGap")
                    && reason.contains("concurrency_ordering_coverage_gap")
                    && reason.contains("release/acquire handoff")
        ));
        assert!(obligation.proof_evidence.is_none());
    }

    #[test]
    fn source_backpropagation_gate_blockers_are_visible_in_native_report() {
        let labels = [
            "missing_reconstruction",
            "exact_source_provenance",
            "type_ownership",
            "target_validation",
            "checked_certificate_identity",
            "replay_identity",
        ];
        let vcs = labels
            .iter()
            .map(|label| {
                vc(
                    VcKind::UnsupportedMir {
                        kind: "SourceBackpropagationGateBlocker".to_string(),
                        detail: format!(
                            "source_backpropagation_gate label={label}; source backpropagation evidence `{label}` is missing"
                        ),
                    },
                    "binary::source_backprop",
                )
            })
            .collect::<Vec<_>>();
        let descriptors = descriptors_for_vcs(vcs.iter(), None);
        let obligations = descriptors
            .into_iter()
            .zip(labels)
            .map(|(descriptor, label)| {
                VerifierObligationResult::new(
                    descriptor,
                    VerificationResult::Unknown {
                        solver: "router".into(),
                        time_ms: 0,
                        reason: format!(
                            "unsupported MIR SourceBackpropagationGateBlocker preserved in TrustIr: source_backpropagation_gate label={label}"
                        ),
                    },
                )
            })
            .collect::<Vec<_>>();
        let function_result = VerifierFunctionResult::from_obligation_results(
            "binary::source_backprop".to_string(),
            obligations,
        );

        let report = build_json_report_from_verifier_results("binary", &[function_result]);
        let obligations = &report.functions[0].obligations;
        let kinds =
            obligations.iter().map(|obligation| obligation.kind.as_str()).collect::<Vec<_>>();

        assert_eq!(
            kinds,
            vec![
                "source_backpropagation_missing_reconstruction",
                "source_backpropagation_exact_source_provenance",
                "source_backpropagation_type_ownership",
                "source_backpropagation_target_validation",
                "source_backpropagation_checked_certificate_identity",
                "source_backpropagation_replay_identity",
            ]
        );
        for (obligation, label) in obligations.iter().zip(labels) {
            assert!(obligation.description.contains(label));
            assert!(matches!(
                &obligation.outcome,
                ObligationOutcome::Unknown { reason }
                    if reason.contains("SourceBackpropagationGateBlocker")
                        && reason.contains(label)
            ));
        }
    }

    #[test]
    fn recent_source_backpropagation_gate_details_are_visible_in_native_report() {
        let cases = [
            (
                "checked proof-cert readback row accepted for proof-grade release; manifest_identity_sha256=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa; source_backpropagation_gate_sha256=bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
                "source_backpropagation_checked_certificate_identity",
                "manifest_identity_sha256",
            ),
            (
                "source-backprop requires machine-effect witnesses consumed for every replayed instruction step: machine-code replay backend omitted memory_write effect witness memory_access#0:8B; concrete scalar memory address/width evidence is required",
                "source_backpropagation_replay_identity",
                "concrete scalar memory address",
            ),
            (
                "source-backprop blocked: exact source type fact ownership is missing; recovered source span has no bridge-owned type fact owner",
                "source_backpropagation_type_ownership",
                "type fact owner",
            ),
            (
                "trust-cg target proof consumer consumed binary proof inputs, but binary-proof-obligation-pending-refinement-metadata remains; bidirectional refinement metadata is missing",
                "source_backpropagation_target_validation",
                "bidirectional refinement metadata",
            ),
        ];
        let vcs = cases
            .iter()
            .map(|(detail, _, _)| {
                vc(
                    VcKind::UnsupportedMir {
                        kind: "SourceBackpropagationGateBlocker".to_string(),
                        detail: (*detail).to_string(),
                    },
                    "binary::source_backprop",
                )
            })
            .collect::<Vec<_>>();
        let descriptors = descriptors_for_vcs(vcs.iter(), None);
        let obligations = descriptors
            .into_iter()
            .zip(cases)
            .map(|(descriptor, (detail, expected, _))| {
                VerifierObligationResult::new(
                    descriptor,
                    VerificationResult::Unknown {
                        solver: "router".into(),
                        time_ms: 0,
                        reason: format!(
                            "unsupported MIR SourceBackpropagationGateBlocker [{expected}] preserved in TrustIr: {detail}"
                        ),
                    },
                )
            })
            .collect::<Vec<_>>();
        let function_result = VerifierFunctionResult::from_obligation_results(
            "binary::source_backprop".to_string(),
            obligations,
        );

        let report = build_json_report_from_verifier_results("binary", &[function_result]);
        let obligations = &report.functions[0].obligations;
        let kinds =
            obligations.iter().map(|obligation| obligation.kind.as_str()).collect::<Vec<_>>();

        assert_eq!(kinds, cases.iter().map(|(_, expected, _)| *expected).collect::<Vec<_>>());
        for (obligation, (detail, expected, marker)) in obligations.iter().zip(cases) {
            assert_eq!(obligation.kind, expected);
            assert!(obligation.description.contains(marker));
            assert!(obligation.description.contains(detail));
            assert!(matches!(
                &obligation.outcome,
                ObligationOutcome::Unknown { reason }
                    if reason.contains("SourceBackpropagationGateBlocker")
                        && reason.contains(marker)
            ));
        }
    }

    #[test]
    fn symbolic_formula_consumer_blocker_is_visible_in_native_report() {
        let detail = "trust_symbolic.formula location=bb0[1].rvalue; structured formula payload is preserved but no schema-aware proof consumer accepted it; rejecting instead of Undef";
        let vc = vc(
            VcKind::UnsupportedMir {
                kind: "TrustSymbolicFormulaNotProofConsumed".to_string(),
                detail: detail.to_string(),
            },
            "binary::symbolic_formula",
        );
        let descriptors = descriptors_for_vcs([&vc], None);
        let function_result = VerifierFunctionResult::from_function_level_result(
            "binary::symbolic_formula".to_string(),
            "router",
            descriptors,
            VerificationResult::Unknown {
                solver: "router".into(),
                time_ms: 0,
                reason: format!(
                    "unsupported MIR TrustSymbolicFormulaNotProofConsumed [trust_symbolic_formula_not_consumed] preserved in TrustIr: {detail}"
                ),
            },
        );

        let report = build_json_report_from_verifier_results("binary", &[function_result]);
        let obligation = &report.functions[0].obligations[0];

        assert_eq!(report.summary.total_unknown, 1);
        assert_eq!(report.summary.verdict, CrateVerdict::Inconclusive);
        assert_eq!(obligation.kind, "trust_symbolic_formula_not_consumed");
        assert!(obligation.description.contains("trust_symbolic.formula"));
        assert!(matches!(
            &obligation.outcome,
            ObligationOutcome::Unknown { reason }
                if reason.contains("TrustSymbolicFormulaNotProofConsumed")
                    && reason.contains("trust_symbolic_formula_not_consumed")
                    && reason.contains("Undef")
        ));
        assert!(obligation.proof_evidence.is_none());
    }
}
