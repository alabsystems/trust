//! JSON report construction from raw verification results.
//!
//! This module contains the core logic for building the canonical JSON proof
//! report from raw `(VerificationCondition, VerificationResult)` pairs and
//! from proof annotations.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use trust_types::{
    AnnotationStatus, BinOp, Counterexample, CounterexampleValue, ProofLevel, ProofStrength,
    RuntimeCheckPolicy, RuntimeDisposition, SourceSpan, VcKind, VerificationCondition,
    VerificationResult, classify_runtime_disposition, *,
};

use crate::{SCHEMA_VERSION, TRUST_VERSION};

/// Build the canonical JSON proof report from raw verification results.
///
/// This is the primary report builder. The JSON report includes:
/// - Crate-level metadata (schema version, timestamp, timing)
/// - Crate-level summary (aggregated counts, verdict)
/// - Per-function reports with summaries and per-obligation detail
///
/// All other output formats should be derived from a `JsonProofReport`.
///
/// `VerificationResult` is a public, freely constructible status object. It
/// does not carry the request-bound TrustIr artifact graph required to publish
/// a proof. Consequently this adapter is fail-closed: a raw `Proved` result is
/// retained as diagnostic evidence but is reported as `Unknown` unless the
/// resulting obligation contains publication-grade structured proof and
/// transport evidence. Likewise, selecting a runtime-check policy does not
/// install or authenticate a certified monitor; without Targo's private live
/// compiler-transport receipt, a tentative `RuntimeChecked` disposition is
/// published as `Unknown`.
pub fn build_json_report(
    crate_name: &str,
    results: &[(VerificationCondition, VerificationResult)],
) -> JsonProofReport {
    build_json_report_with_policy(crate_name, results, RuntimeCheckPolicy::Auto, true)
}

/// Build the canonical JSON proof report from raw verification results using
/// the provided runtime-check policy and overflow-check configuration.
pub fn build_json_report_with_policy(
    crate_name: &str,
    results: &[(VerificationCondition, VerificationResult)],
    policy: RuntimeCheckPolicy,
    overflow_checks: bool,
) -> JsonProofReport {
    let start = std::time::Instant::now();

    let functions = build_function_reports(results, Some(policy), Some(overflow_checks));

    let summary = build_crate_summary(&functions);
    let total_time_ms = start.elapsed().as_millis() as u64
        + functions.iter().map(|f| f.summary.total_time_ms).sum::<u64>();

    gate_report_for_publication(JsonProofReport {
        metadata: ReportMetadata {
            schema_version: SCHEMA_VERSION.to_string(),
            trust_version: TRUST_VERSION.to_string(),
            timestamp: now_iso8601(),
            total_time_ms,
            timeout_ms: None,
            function_budget_ms: None,
        },
        crate_name: crate_name.to_string(),
        summary,
        functions,
        hardened: None,
        assumptions: Vec::new(),
        verification_gate: None,
        cargo_proof_inventory: None,
    })
}

/// Build the canonical JSON proof report from proof annotations.
///
/// This variant consumes the proof-carrying MIR annotation format emitted by
/// `trust-types` and converts it into the canonical JSON report structure.
/// An annotation is a serializable status record, not replay-bound proof
/// authority, so this path applies the same structured-evidence publication
/// gate as the raw-result path.
pub fn build_json_report_from_annotations(
    crate_name: &str,
    annotations: &[ProofAnnotation],
) -> JsonProofReport {
    let start = std::time::Instant::now();

    let mut functions: Vec<FunctionProofReport> = annotations
        .iter()
        .map(|annotation| {
            let obligations: Vec<ObligationReport> = annotation
                .obligations
                .iter()
                .map(|obligation| {
                    // Derive ProofEvidence from annotation strength.
                    let evidence = obligation.strength.as_ref().map(|s| s.clone().into());
                    ObligationReport {
                        obligation_id: None,
                        description: obligation.description.clone(),
                        kind: obligation.kind.clone(),
                        proof_level: obligation.proof_level,
                        location: convert_annotation_location(obligation.location.clone()),
                        outcome: convert_annotation_status(
                            obligation.status,
                            obligation.strength.clone(),
                            obligation.counterexample.as_ref(),
                            obligation.time_ms,
                        ),
                        solver: obligation.solver.clone(),
                        time_ms: obligation.time_ms,
                        evidence,
                        proof_evidence: None,
                        transport_evidence: None,
                    }
                })
                .collect();

            // (un-forgeable-Verified gate, round-A #1 false-PROVE fix): recount the
            // function summary + verdict from the FLOOR-GATED obligations via the
            // SAME helper the results path uses — NOT from the deserialized
            // annotation.summary counts. An annotation is an untrusted transport
            // form: a stale/hand-edited report could claim summary.proved=N with
            // zero genuinely-proved obligations, and previously function_verdict was
            // computed from those counts (and the emitted summary copied them), so a
            // crate rendered Verified while its obligation was below-floor Unknown.
            // The per-obligation floor gate (convert_annotation_status) already
            // downgraded below-floor Proved to Unknown; recounting here makes the
            // function/crate verdict provably match the gated obligations — exactly
            // what JsonProofReport::sanitize_deserialized does for the JSON path.
            debug_assert_eq!(annotation.summary.total, obligations.len());
            let summary = build_function_summary(&obligations);

            FunctionProofReport {
                function: if annotation.function_path.is_empty() {
                    annotation.function_name.clone()
                } else {
                    annotation.function_path.clone()
                },
                summary,
                obligations,
            }
        })
        .collect();

    functions.sort_by(|a, b| a.function.cmp(&b.function));

    let summary = build_crate_summary(&functions);
    let total_time_ms = start.elapsed().as_millis() as u64
        + functions.iter().map(|function| function.summary.total_time_ms).sum::<u64>();

    gate_report_for_publication(JsonProofReport {
        metadata: ReportMetadata {
            schema_version: SCHEMA_VERSION.to_string(),
            trust_version: TRUST_VERSION.to_string(),
            timestamp: now_iso8601(),
            total_time_ms,
            timeout_ms: None,
            function_budget_ms: None,
        },
        crate_name: crate_name.to_string(),
        summary,
        functions,
        hardened: None,
        assumptions: Vec::new(),
        verification_gate: None,
        cargo_proof_inventory: None,
    })
}

/// Apply the canonical proof-publication gate to reports assembled from
/// unstructured status records.
///
/// The canonical routine is named for its original disk/transport use, but the
/// same threat exists at an in-memory public API: callers can freely construct
/// `VerificationResult` and `ProofAnnotation` values, and a policy choice is
/// not a compiler/monitor capability. Reusing the one gate also keeps
/// obligation outcomes, summaries, and verdicts in lockstep.
fn gate_report_for_publication(mut report: JsonProofReport) -> JsonProofReport {
    let _ = report.sanitize_deserialized();
    report
}

/// Build per-function reports from raw (VC, result) pairs.
fn build_function_reports(
    results: &[(VerificationCondition, VerificationResult)],
    policy: Option<RuntimeCheckPolicy>,
    overflow_checks: Option<bool>,
) -> Vec<FunctionProofReport> {
    // Group by function name, preserving insertion order.
    let mut by_function: Vec<(String, Vec<(&VerificationCondition, &VerificationResult)>)> =
        Vec::new();
    let mut index_map: FxHashMap<Symbol, usize> = FxHashMap::default(); // Trust: FxHashMap OK — lookup only, no iteration

    for (vc, result) in results {
        if let Some(&idx) = index_map.get(&vc.function) {
            by_function[idx].1.push((vc, result));
        } else {
            let idx = by_function.len();
            index_map.insert(vc.function, idx);
            by_function.push((vc.function.as_str().to_string(), vec![(vc, result)]));
        }
    }

    let mut functions: Vec<FunctionProofReport> = by_function
        .into_iter()
        .map(|(func_name, pairs)| {
            let obligations = build_obligations(&pairs, policy, overflow_checks);
            let summary = build_function_summary(&obligations);
            FunctionProofReport { function: func_name, summary, obligations }
        })
        .collect();

    functions.sort_by(|a, b| a.function.cmp(&b.function));
    functions
}

/// Build per-obligation reports from (VC, result) pairs for one function.
fn build_obligations(
    pairs: &[(&VerificationCondition, &VerificationResult)],
    policy: Option<RuntimeCheckPolicy>,
    overflow_checks: Option<bool>,
) -> Vec<ObligationReport> {
    pairs
        .iter()
        .map(|(vc, result)| {
            let location = span_to_location(&vc.location);
            let (outcome, solver, time_ms) =
                result_to_outcome(&vc.kind, result, policy, overflow_checks);
            // a hardened-boundary obligation whose violation
            // condition is the tautology `true` is a DESIGN MANDATE (move off a
            // raw/opaque API), not a discharge target. Reclassify so it never
            // surfaces as `FAILED`/`UNKNOWN` or counts against the proof totals.
            let outcome = match hardened_design_mandate(&vc.kind, &vc.formula) {
                Some(detail) => ObligationOutcome::DesignRequirement { detail },
                None => outcome,
            };
            // Derive ProofEvidence from the VerificationResult.
            let evidence = result.evidence();

            ObligationReport {
                obligation_id: None,
                description: vc.kind.description(),
                kind: result_kind_tag(&vc.kind, result),
                proof_level: vc.kind.proof_level(),
                location,
                outcome,
                solver,
                time_ms,
                evidence,
                proof_evidence: None,
                transport_evidence: None,
            }
        })
        .collect()
}

/// Convert a SourceSpan to Option<SourceSpan>, returning None for empty spans.
fn span_to_location(span: &SourceSpan) -> Option<SourceSpan> {
    if span.file.is_empty() && span.line_start == 0 {
        return None;
    }
    Some(SourceSpan {
        file: span.file.clone(),
        line_start: span.line_start,
        col_start: span.col_start,
        line_end: span.line_end,
        col_end: span.col_end,
    })
}

/// Convert an annotation status to an obligation outcome.
fn convert_annotation_status(
    status: AnnotationStatus,
    strength: Option<ProofStrength>,
    counterexample: Option<&Counterexample>,
    time_ms: u64,
) -> ObligationOutcome {
    match status {
        AnnotationStatus::Proved => {
            // (un-forgeable-Proved gate): an annotation is a DESERIALIZED transport
            // form, so a Proved carrying below-floor assurance (Unchecked/Heuristic/
            // Trusted) must not surface as a reported proof — same deserialized-side-
            // channel class the report/router/sanitize gates already close. Mirror
            // the SmtBacked floor here (the sole VR path is gated in result_to_outcome).
            let strength = strength.unwrap_or_else(ProofStrength::smt_unsat);
            if !strength.assurance.meets_reporting_floor() {
                ObligationOutcome::Unknown {
                    reason: format!(
                        "annotation proof assurance {:?} below required SmtBacked; \
                         downgraded to Unknown (un-forgeable-Proved gate)",
                        strength.assurance
                    ),
                }
            } else {
                ObligationOutcome::Proved { strength }
            }
        }
        AnnotationStatus::Failed => {
            ObligationOutcome::Failed { counterexample: counterexample.map(cex_to_report) }
        }
        AnnotationStatus::Unknown => {
            ObligationOutcome::Unknown { reason: "annotation reported unknown".to_string() }
        }
        AnnotationStatus::RuntimeChecked => ObligationOutcome::RuntimeChecked { note: None },
        AnnotationStatus::Timeout => ObligationOutcome::Timeout { timeout_ms: time_ms },
        _ => ObligationOutcome::Unknown { reason: "unhandled annotation status".to_string() },
    }
}

/// Convert an optional annotation span to an obligation location.
fn convert_annotation_location(location: Option<SourceSpan>) -> Option<SourceSpan> {
    location.as_ref().and_then(span_to_location)
}

/// identify a hardened-boundary DESIGN MANDATE — a
/// `HardenedBoundary` VC whose violation condition is the tautology `true`.
/// Such a VC is unprovable by construction (it is a mandate to move off a
/// raw/opaque API, not a property to discharge), so it must be reported as a
/// design requirement rather than ride the proof `failed`/`unknown` channel.
/// MIR-assert hardened VCs carry a real condition and are NOT matched here.
fn hardened_design_mandate(kind: &VcKind, formula: &Formula) -> Option<String> {
    match kind {
        VcKind::HardenedBoundary { callee, detail, .. }
            if matches!(formula, Formula::Bool(true)) =>
        {
            Some(format!("{callee}: {detail}"))
        }
        _ => None,
    }
}

/// Convert a VerificationResult to (ObligationOutcome, solver_name, time_ms).
fn result_to_outcome(
    vc_kind: &VcKind,
    result: &VerificationResult,
    policy: Option<RuntimeCheckPolicy>,
    overflow_checks: Option<bool>,
) -> (ObligationOutcome, String, u64) {
    // (un-forgeable-Proved gate, single chokepoint): apply the reported-proof
    // floor (`SmtBacked`) ONCE here, before either the disposition path or the
    // raw path runs, so neither can surface a below-floor `Proved`. Previously
    // only `raw_result_to_outcome` gated; the policy path
    // (`classify_runtime_disposition` -> `disposition_to_outcome`) matched
    // `Proved { .. }` regardless of assurance and built `ObligationOutcome::Proved`
    // directly, so a `Proved{Unchecked}` (deserialized/cached/weak) under a
    // `#[trust(...)]` runtime-check policy reached a reported proof, bypassing the
    // floor. require_assurance is monotone (only weakens Proved->Unknown), so this
    // is fail-closed and idempotent w.r.t. the inner gate that remains in
    // raw_result_to_outcome. (T-GATE, docs/PROOF_OF_PERFECTION.md.)
    let gated = result.clone().require_reporting_floor();
    let result = &gated;

    let outcome = if result.is_memory_guard_solver_skip() {
        raw_result_to_outcome(result)
    } else {
        match policy {
            Some(policy) => {
                let disposition = classify_runtime_disposition(
                    vc_kind,
                    result,
                    policy,
                    overflow_checks.unwrap_or(true),
                );
                disposition_to_outcome(result, disposition)
            }
            None => raw_result_to_outcome(result),
        }
    };

    (outcome, result.solver_name().to_string(), result.time_ms())
}

fn raw_result_to_outcome(result: &VerificationResult) -> ObligationOutcome {
    // (un-forgeable-Proved gate): mirror trust-router's report
    // boundary — a `Proved` whose assurance is below the reported-proof floor
    // (`SmtBacked`) is downgraded to `Unknown`, so no deserialized/cached/forged
    // weak-assurance result surfaces as a reported proof.
    let gated = result.clone().require_reporting_floor();
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

fn disposition_to_outcome(
    result: &VerificationResult,
    disposition: RuntimeDisposition,
) -> ObligationOutcome {
    match disposition {
        RuntimeDisposition::Proved => match result {
            VerificationResult::Proved { strength, .. } => {
                ObligationOutcome::Proved { strength: strength.clone() }
            }
            _ => ObligationOutcome::Unknown {
                reason: "proved disposition but result is not Proved".to_string(),
            },
        },
        RuntimeDisposition::RuntimeChecked { note } => {
            ObligationOutcome::RuntimeChecked { note: Some(note) }
        }
        RuntimeDisposition::Failed => match result {
            VerificationResult::Failed { counterexample, .. } => ObligationOutcome::Failed {
                counterexample: counterexample.as_ref().map(cex_to_report),
            },
            _ => ObligationOutcome::Unknown {
                reason: "failed disposition but result is not Failed".to_string(),
            },
        },
        RuntimeDisposition::Unknown { reason } => ObligationOutcome::Unknown {
            reason: result.release_blocking_proof_gap_reason().unwrap_or(reason),
        },
        RuntimeDisposition::Timeout { timeout_ms } => ObligationOutcome::Timeout { timeout_ms },
        RuntimeDisposition::CompileError { reason } => ObligationOutcome::Unknown { reason },
        _ => ObligationOutcome::Unknown {
            reason: "unhandled verification result variant".to_string(),
        },
    }
}

/// Convert a legacy Counterexample to a CounterexampleReport.
fn cex_to_report(cex: &Counterexample) -> CounterexampleReport {
    CounterexampleReport {
        variables: cex
            .assignments
            .iter()
            .map(|(name, val)| {
                let (value_str, value_type) = match val {
                    CounterexampleValue::Bool(b) => (b.to_string(), "bool"),
                    CounterexampleValue::Int(n) => (n.to_string(), "int"),
                    CounterexampleValue::Uint(n) => (n.to_string(), "uint"),
                    CounterexampleValue::Float(n) => (n.to_string(), "float"),
                    _ => ("unknown".to_string(), "unknown"),
                };
                CounterexampleVariable {
                    name: name.clone(),
                    value: value_str.clone(),
                    value_type: value_type.to_string(),
                    display: val.to_string(),
                }
            })
            .collect(),
    }
}

fn result_kind_tag(kind: &VcKind, result: &VerificationResult) -> String {
    if result.is_memory_guard_solver_skip() {
        "memory_guard_resource_proof_gap".to_string()
    } else {
        vc_kind_tag(kind)
    }
}

/// Machine-parseable kind tag string for a VcKind.
pub(crate) fn vc_kind_tag(kind: &VcKind) -> String {
    if let Some(tag) = kind.hardened_family_tag() {
        return tag;
    }
    if let Some(tag) = kind.binary_copy_sink_length_family_tag() {
        return tag.to_string();
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
        VcKind::Unreachable => "unreachable".to_string(),
        VcKind::DeadState { .. } => "dead_state".to_string(),
        VcKind::Deadlock => "deadlock".to_string(),
        VcKind::Temporal { .. } => "temporal".to_string(),
        // Trust: Liveness and fairness kind tags.
        VcKind::Liveness { .. } => "liveness".to_string(),
        VcKind::Fairness { .. } => "fairness".to_string(),
        VcKind::TaintViolation { .. } => "taint_violation".to_string(),
        VcKind::RefinementViolation { .. } => "refinement_violation".to_string(),
        VcKind::ResilienceViolation { .. } => "resilience_violation".to_string(),
        VcKind::ProtocolViolation { .. } => "protocol_violation".to_string(),
        VcKind::NonTermination { .. } => "non_termination".to_string(),
        // Data race and memory ordering tags.
        VcKind::DataRace { .. } => "data_race".to_string(),
        VcKind::InsufficientOrdering { .. } => "insufficient_ordering".to_string(),
        // Translation validation tag.
        VcKind::TranslationValidation { .. } => "translation_validation".to_string(),
        // Floating-point operation tags.
        VcKind::FloatDivisionByZero => "float_division_by_zero".to_string(),
        VcKind::FloatOverflowToInfinity { .. } => "float_overflow_to_infinity".to_string(),
        // Rvalue safety VC tags.
        VcKind::InvalidDiscriminant { .. } => "invalid_discriminant".to_string(),
        VcKind::AggregateArrayLengthMismatch { .. } => {
            "aggregate_array_length_mismatch".to_string()
        }
        // Unsafe operation tag.
        VcKind::UnsafeOperation { .. } => "unsafe_operation".to_string(),
        VcKind::SavedReturnAddressOverwrite { .. } => "saved_return_address_overwrite".to_string(),
        VcKind::FormatStringViolation { .. } => "format_string_violation".to_string(),
        VcKind::TaintedIndirectBranch { .. } => "tainted_indirect_branch".to_string(),
        VcKind::BinaryAbiContradiction { .. } => "binary_abi_contradiction".to_string(),
        VcKind::FfiBoundaryViolation { .. } => "ffi_boundary_violation".to_string(),
        VcKind::CopyBoundsViolation { .. } => "copy_bounds_violation".to_string(),
        VcKind::ExternallyMutableAllocationBounds { .. } => {
            "externally_mutable_allocation_bounds".to_string()
        }
        VcKind::UnboundedAllocation { .. } => "unbounded_allocation".to_string(),
        VcKind::UseAfterFree => "use_after_free".to_string(),
        VcKind::DoubleFree => "double_free".to_string(),
        VcKind::AliasingViolation { .. } => "aliasing_violation".to_string(),
        VcKind::LifetimeViolation => "lifetime_violation".to_string(),
        VcKind::SendViolation => "send_violation".to_string(),
        VcKind::SyncViolation => "sync_violation".to_string(),
        VcKind::FunctionalCorrectness { .. } => "functional_correctness".to_string(),
        VcKind::LoopInvariantInitiation { .. } => "loop_invariant_initiation".to_string(),
        VcKind::LoopInvariantConsecution { .. } => "loop_invariant_consecution".to_string(),
        VcKind::LoopInvariantSufficiency { .. } => "loop_invariant_sufficiency".to_string(),
        VcKind::TypeRefinementViolation { .. } => "type_refinement_violation".to_string(),
        VcKind::FrameConditionViolation { .. } => "frame_condition_violation".to_string(),
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

/// Lowercase tag for a BinOp.
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

/// Build a FunctionSummary from a list of obligation reports.
fn build_function_summary(obligations: &[ObligationReport]) -> FunctionSummary {
    let mut proved = 0usize;
    let mut runtime_checked = 0usize;
    let mut failed = 0usize;
    let mut unknown = 0usize;
    let mut timed_out = 0usize;
    let mut design_requirements = 0usize;
    let mut total_time_ms = 0u64;
    let mut max_proof_level: Option<ProofLevel> = None;

    for ob in obligations {
        match &ob.outcome {
            ObligationOutcome::Proved { .. } => proved += 1,
            ObligationOutcome::RuntimeChecked { .. } => runtime_checked += 1,
            ObligationOutcome::Failed { .. } => failed += 1,
            ObligationOutcome::Unknown { .. } => unknown += 1,
            ObligationOutcome::Timeout { .. } => {
                unknown += 1;
                timed_out += 1;
            }
            // Hardened-boundary design mandate: counted in its own bucket, never
            // as proved or failed.
            ObligationOutcome::DesignRequirement { .. } => design_requirements += 1,
            // A future `#[non_exhaustive]` variant is left uncounted here; the
            // positive `proved == total` invariant in the verdict below fails it
            // closed to `Inconclusive` rather than minting a false `Verified`.
            _ => {}
        }
        total_time_ms += ob.time_ms;
        max_proof_level = Some(match max_proof_level {
            None => ob.proof_level,
            Some(current) => std::cmp::max(current, ob.proof_level),
        });
    }

    let verdict = ScopeVerdict::from_counts(ScopeVerdictCounts {
        total: obligations.len(),
        proved,
        runtime_checked,
        failed,
        unknown,
        ..ScopeVerdictCounts::default()
    });

    FunctionSummary {
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
        verdict,
    }
}

/// Build a CrateSummary from all function reports.
pub(crate) fn build_crate_summary(functions: &[FunctionProofReport]) -> CrateSummary {
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

    for func in functions {
        match func.summary.verdict {
            FunctionVerdict::Verified => functions_verified += 1,
            FunctionVerdict::RuntimeChecked => functions_runtime_checked += 1,
            FunctionVerdict::HasViolations => functions_with_violations += 1,
            FunctionVerdict::Inconclusive => functions_inconclusive += 1,
            FunctionVerdict::NoObligations => {}
            // A future `#[non_exhaustive]` verdict variant is left uncounted; the
            // positive `total_proved == total_obligations` invariant below fails
            // it closed rather than counting it toward a `Verified` crate.
            _ => {}
        }
        total_obligations += func.summary.total_obligations;
        total_proved += func.summary.proved;
        total_runtime_checked += func.summary.runtime_checked;
        total_failed += func.summary.failed;
        total_unknown += func.summary.unknown;
        total_timed_out += func.summary.timed_out;
        total_design_requirements += func.summary.design_requirements;
        total_unattributed_failed += func.summary.unattributed_failed;
        total_unattributed_unknown += func.summary.unattributed_unknown;
        total_unattributed_proved += func.summary.unattributed_proved;
    }

    let verdict = ScopeVerdict::from_counts(ScopeVerdictCounts {
        total: total_obligations,
        proved: total_proved,
        runtime_checked: total_runtime_checked,
        failed: total_failed,
        unknown: total_unknown,
        unattributed_failed: total_unattributed_failed,
        unattributed_unknown: total_unattributed_unknown,
        unattributed_proved: total_unattributed_proved,
    });

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

/// Get current time as ISO 8601 string.
///
/// Uses a minimal implementation to avoid pulling in chrono/time crates.
pub(crate) fn now_iso8601() -> String {
    // Use SystemTime for a basic ISO 8601 timestamp.
    let now = std::time::SystemTime::now();
    let duration = now.duration_since(std::time::UNIX_EPOCH).unwrap_or_default();
    let secs = duration.as_secs();
    // Simple UTC timestamp: seconds since epoch formatted as pseudo-ISO.
    // For production, replace with a proper time library.
    format!("{secs}")
}

#[cfg(test)]
mod verdict_invariant_tests {
    //! regression: a positive `Verified` invariant. `Verified`
    //! must require *every* obligation to be `Proved`, never merely the absence
    //! of failures/unknowns — otherwise an uncounted obligation (e.g. a future
    //! `#[non_exhaustive]` `ObligationOutcome` variant) could be minted into a
    //! false proof.
    use trust_types::{
        CrateVerdict, Formula, FunctionVerdict, HardenedVcCategory, ObligationOutcome,
        ObligationReport, ProofLevel, ProofStrength, ScopeVerdict, ScopeVerdictCounts, VcKind,
    };

    use super::{build_function_summary, hardened_design_mandate};

    fn ob(outcome: ObligationOutcome) -> ObligationReport {
        ObligationReport {
            obligation_id: None,
            description: "t".into(),
            kind: "t".into(),
            proof_level: ProofLevel::L0Safety,
            location: None,
            outcome,
            solver: "test".into(),
            time_ms: 0,
            evidence: None,
            proof_evidence: None,
            transport_evidence: None,
        }
    }

    fn proved() -> ObligationOutcome {
        ObligationOutcome::Proved { strength: ProofStrength::smt_unsat() }
    }

    #[test]
    fn policy_path_gates_below_floor_proved() {
        // T-GATE (docs/PROOF_OF_PERFECTION.md): a `Proved` carrying BELOW-floor
        // assurance (Unchecked — a deserialized/cached/weak result) must NOT
        // surface as a reported proof on the runtime-check-policy path.
        // Previously `disposition_to_outcome` built `ObligationOutcome::Proved`
        // without the floor gate that `raw_result_to_outcome` applies; the single
        // chokepoint gate in `result_to_outcome` now covers both paths.
        use trust_types::{RuntimeCheckPolicy, Symbol, VerificationResult};

        use super::result_to_outcome;

        let weak = VerificationResult::Proved {
            solver: Symbol::from("ay"),
            time_ms: 1,
            strength: ProofStrength::smt_unsat_unvalidated(), // Unchecked, below SmtBacked
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        };
        let (outcome, _, _) = result_to_outcome(
            &VcKind::DivisionByZero,
            &weak,
            Some(RuntimeCheckPolicy::Auto),
            Some(true),
        );
        assert!(
            !matches!(outcome, ObligationOutcome::Proved { .. }),
            "below-floor Proved must NOT surface as Proved on the policy path; got {outcome:?}"
        );

        // Control: an at-floor (SmtBacked) Proved still surfaces as Proved.
        let strong = VerificationResult::Proved {
            solver: Symbol::from("ay"),
            time_ms: 1,
            strength: ProofStrength::smt_unsat(), // SmtBacked, at floor
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        };
        let (outcome2, _, _) = result_to_outcome(
            &VcKind::DivisionByZero,
            &strong,
            Some(RuntimeCheckPolicy::Auto),
            Some(true),
        );
        assert!(
            matches!(outcome2, ObligationOutcome::Proved { .. }),
            "at-floor Proved must still surface as Proved on the policy path; got {outcome2:?}"
        );
    }

    #[test]
    fn raw_result_path_gates_below_floor_proved() {
        // T-GATE (docs/PROOF_OF_PERFECTION.md): the RAW path (policy = None ->
        // `raw_result_to_outcome`) must also enforce the SmtBacked reported-proof
        // floor. A `Proved` carrying BELOW-floor assurance (Unchecked — a
        // deserialized/cached/weak result) must NOT surface as a reported proof.
        // Mirrors `policy_path_gates_below_floor_proved` but drives the raw edge.
        use trust_types::{Symbol, VerificationResult};

        use super::result_to_outcome;

        let weak = VerificationResult::Proved {
            solver: Symbol::from("ay"),
            time_ms: 1,
            strength: ProofStrength::smt_unsat_unvalidated(), // Unchecked, below SmtBacked
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        };
        // policy = None selects the raw path (`raw_result_to_outcome`).
        let (outcome, _, _) = result_to_outcome(&VcKind::DivisionByZero, &weak, None, Some(true));
        assert!(
            !matches!(outcome, ObligationOutcome::Proved { .. }),
            "below-floor Proved must NOT surface as Proved on the raw path; got {outcome:?}"
        );

        // Control: an at-floor (SmtBacked) Proved still surfaces as Proved.
        let strong = VerificationResult::Proved {
            solver: Symbol::from("ay"),
            time_ms: 1,
            strength: ProofStrength::smt_unsat(), // SmtBacked, at floor
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        };
        let (outcome2, _, _) =
            result_to_outcome(&VcKind::DivisionByZero, &strong, None, Some(true));
        assert!(
            matches!(outcome2, ObligationOutcome::Proved { .. }),
            "at-floor Proved must still surface as Proved on the raw path; got {outcome2:?}"
        );
    }

    #[test]
    fn proved_construction_sites_are_accounted_for() {
        // Source-level regression guard. Every site that constructs an
        // `ObligationOutcome::Proved` value is a floor-gate concern: a newly-added
        // *ungated* construction is exactly the false-PROVE hazard T-GATE closes.
        // We count every verbatim occurrence of the marker (built from fragments
        // as `needle` so this comment/test does not itself perturb the count) in
        // THIS file — construction sites AND `{ .. }` match/`matches!` patterns
        // share that prefix — and pin it, so adding any new occurrence (most
        // importantly a new ungated construction) breaks this test and forces a
        // human to confirm the new site is floor-gated and update this count.
        //
        // KNOWN occurrences of the marker (exact count = 12). NOTE: every mention
        // in these comments is split (e.g. "Proved"+" {") so it is NOT counted;
        // only real code occurrences contribute. They are:
        //
        //   PRODUCTION construction sites (each gated — must NOT mint below-floor):
        //     1. convert_annotation_status   — gated by the SmtBacked check above it
        //     2. raw_result_to_outcome       — gated by require_assurance(SmtBacked)
        //     3. disposition_to_outcome      — gated at the result_to_outcome chokepoint
        //
        //   PRODUCTION match pattern (NOT a construction):
        //     4. build_function_summary "{ .." counting arm
        //
        //   TEST module occurrences (matches! patterns + the proved() helper):
        //     5.  proved() helper — construction
        //     6.  policy_path_gates_below_floor_proved      matches!(outcome, ..)
        //     7.  policy_path_gates_below_floor_proved      matches!(outcome2, ..)
        //     8.  raw_result_path_gates_below_floor_proved  matches!(outcome, ..)
        //     9.  raw_result_path_gates_below_floor_proved  matches!(outcome2, ..)
        //     10. annotation_proved_gated_through_floor     matches!(weak, ..)
        //     11. annotation_proved_gated_through_floor     matches!(strong, ..)
        //     12. annotation_proved_gated_through_floor     matches!(dflt, ..)
        //
        // Build the needle from fragments so the marker does NOT appear verbatim
        // anywhere in this test (comment or code) — keeping the count honest.
        let needle = concat!("ObligationOutcome::", "Proved", " {");
        let src = include_str!("report_builder.rs");
        let count = src.matches(needle).count();
        const EXPECTED: usize = 12;
        assert_eq!(
            count, EXPECTED,
            "occurrences of `{needle}` changed ({count} != {EXPECTED}). If you added a \
             new `ObligationOutcome::Proved` CONSTRUCTION, confirm it enforces the \
             SmtBacked reported-proof floor (require_assurance / chokepoint gate), then \
             update EXPECTED and the site list in this test."
        );
    }

    #[test]
    fn annotation_inflated_summary_cannot_mint_verified() {
        // round-A #1 false-PROVE regression: a stale/hand-edited annotation that
        // claims summary.proved=1 while its single obligation carries below-floor
        // (Unchecked) strength must NOT render Verified. The verdict + emitted
        // summary are recounted from the floor-gated obligations, not the
        // deserialized summary counts.
        use trust_types::{
            AnnotationStatus, AnnotationSummary, ObligationAnnotation, ProofAnnotation, ProofLevel,
        };

        use super::build_json_report_from_annotations;
        let ann = ProofAnnotation {
            function_name: "f".into(),
            function_path: "crate::f".into(),
            obligations: vec![ObligationAnnotation {
                description: "o".into(),
                kind: "division_by_zero".into(),
                proof_level: ProofLevel::L0Safety,
                status: AnnotationStatus::Proved,
                strength: Some(ProofStrength::smt_unsat_unvalidated()), // Unchecked, below floor
                solver: "ay".into(),
                time_ms: 0,
                location: None,
                counterexample: None,
                fingerprint: [0, 0],
            }],
            summary: AnnotationSummary {
                total: 1,
                proved: 1, // INFLATED — the obligation is actually below-floor
                failed: 0,
                unknown: 0,
                runtime_checked: 0,
                max_level: Some(ProofLevel::L0Safety),
            },
            certificate: None,
        };
        let report = build_json_report_from_annotations("c", &[ann]);
        assert_eq!(
            report.functions[0].summary.proved, 0,
            "inflated summary.proved must be recounted to 0 from the gated obligation"
        );
        assert_ne!(
            report.functions[0].summary.verdict,
            FunctionVerdict::Verified,
            "function must not be Verified when its obligation is below-floor"
        );
        assert_ne!(report.summary.verdict, CrateVerdict::Verified, "crate must not be Verified");
    }

    #[test]
    fn annotation_proved_gated_through_floor() {
        // T-GATE: the deserialized-annotation edge must also enforce the floor.
        use trust_types::AnnotationStatus;

        use super::convert_annotation_status;

        // Below-floor annotation strength must NOT surface as Proved.
        let weak = convert_annotation_status(
            AnnotationStatus::Proved,
            Some(ProofStrength::smt_unsat_unvalidated()), // Unchecked
            None,
            0,
        );
        assert!(
            !matches!(weak, ObligationOutcome::Proved { .. }),
            "below-floor annotation Proved must be gated to Unknown; got {weak:?}"
        );
        // At-floor (SmtBacked) and the None default (smt_unsat = SmtBacked) stay Proved.
        let strong = convert_annotation_status(
            AnnotationStatus::Proved,
            Some(ProofStrength::smt_unsat()),
            None,
            0,
        );
        assert!(matches!(strong, ObligationOutcome::Proved { .. }));
        let dflt = convert_annotation_status(AnnotationStatus::Proved, None, None, 0);
        assert!(matches!(dflt, ObligationOutcome::Proved { .. }));
    }

    #[test]
    fn function_verified_only_when_all_proved() {
        // All proved -> Verified.
        let s = build_function_summary(&[ob(proved()), ob(proved())]);
        assert_eq!(s.verdict, FunctionVerdict::Verified);
        assert_eq!(s.proved, 2);

        // Empty -> NoObligations, never Verified.
        assert_eq!(build_function_summary(&[]).verdict, FunctionVerdict::NoObligations);

        // One unknown alongside a proof -> Inconclusive, never Verified.
        let mixed = build_function_summary(&[
            ob(proved()),
            ob(ObligationOutcome::Unknown { reason: "x".into() }),
        ]);
        assert_eq!(mixed.verdict, FunctionVerdict::Inconclusive);
    }

    fn attributed(total: usize, proved: usize) -> ScopeVerdictCounts {
        ScopeVerdictCounts { total, proved, ..ScopeVerdictCounts::default() }
    }

    #[test]
    fn function_uncounted_obligation_fails_closed() {
        // Simulates a future `#[non_exhaustive]` variant that the counting match
        // leaves uncounted: total exceeds the sum of all classified buckets.
        // The positive invariant must reject `Verified` and fail closed.
        assert_eq!(
            ScopeVerdict::from_counts(attributed(3, 1)),
            FunctionVerdict::Inconclusive,
            "an uncounted obligation must never be promoted to Verified"
        );
        // All accounted for and proved -> Verified.
        assert_eq!(ScopeVerdict::from_counts(attributed(3, 3)), FunctionVerdict::Verified);
        // Zero proved with everything uncounted -> not Verified.
        assert_eq!(ScopeVerdict::from_counts(attributed(2, 0)), FunctionVerdict::Inconclusive);
    }

    #[test]
    fn crate_verified_only_when_all_proved() {
        // total=5, proved=5 -> Verified.
        assert_eq!(ScopeVerdict::from_counts(attributed(5, 5)), CrateVerdict::Verified);
        // total=5, proved=4, 1 uncounted -> fail closed.
        assert_eq!(
            ScopeVerdict::from_counts(attributed(5, 4)),
            CrateVerdict::Inconclusive,
            "an uncounted obligation must never be promoted to a Verified crate"
        );
        // Unattributed proved leakage -> Inconclusive (pre-existing guard).
        assert_eq!(
            ScopeVerdict::from_counts(ScopeVerdictCounts {
                unattributed_proved: 1,
                ..attributed(5, 5)
            }),
            CrateVerdict::Inconclusive
        );
        // No obligations -> NoObligations.
        assert_eq!(ScopeVerdict::from_counts(attributed(0, 0)), CrateVerdict::NoObligations);
        // Residual backend bad news must precede the empty concrete inventory.
        assert_eq!(
            ScopeVerdict::from_counts(ScopeVerdictCounts {
                unattributed_failed: 1,
                ..ScopeVerdictCounts::default()
            }),
            CrateVerdict::HasViolations
        );
        assert_eq!(
            ScopeVerdict::from_counts(ScopeVerdictCounts {
                unattributed_unknown: 1,
                ..ScopeVerdictCounts::default()
            }),
            CrateVerdict::Inconclusive
        );
        assert_eq!(
            ScopeVerdict::from_counts(ScopeVerdictCounts {
                unattributed_proved: 1,
                ..ScopeVerdictCounts::default()
            }),
            CrateVerdict::Inconclusive
        );
    }

    #[test]
    fn hardened_tautology_boundary_is_a_design_mandate() {
        let kind = VcKind::HardenedBoundary {
            category: HardenedVcCategory::RawPathApi,
            callee: "std::fs::remove_file".into(),
            detail: "raw path API".into(),
        };
        // A hardened boundary whose violation condition is the tautology `true`
        // is a design mandate (unprovable by construction).
        assert!(hardened_design_mandate(&kind, &Formula::Bool(true)).is_some());
        // A hardened boundary carrying a real condition (here, any non-`true`
        // formula) is a genuine obligation, not a mandate.
        assert!(hardened_design_mandate(&kind, &Formula::Bool(false)).is_none());
        // A non-hardened VC is never a design mandate, even with a `true` formula.
        assert!(hardened_design_mandate(&VcKind::DivisionByZero, &Formula::Bool(true)).is_none());
    }

    #[test]
    fn design_requirement_not_counted_as_failed_or_proved() {
        let s = build_function_summary(&[
            ob(proved()),
            ob(ObligationOutcome::DesignRequirement { detail: "move off raw path API".into() }),
        ]);
        assert_eq!(s.proved, 1);
        assert_eq!(s.failed, 0, "a design mandate must never count as a failure");
        assert_eq!(s.unknown, 0);
        assert_eq!(s.design_requirements, 1);
        // Not every obligation is proved, so not Verified — but it's an advisory,
        // not a violation.
        assert_eq!(s.verdict, FunctionVerdict::Inconclusive);
    }
}
