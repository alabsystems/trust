// Helpers for analyzing verification failures, classifying them, building
// strengthen proposals, and summarizing proposals for the rewrite loop.

use trust_backprop::SourceRewrite;
use trust_strengthen::{FailureAnalysis, FailurePattern, Proposal, ProposalKind, analyze_failure};
use trust_types::{VerificationCondition, VerificationResult as TrustVr};

#[cfg(test)]
use super::backprop_gate::{
    source_backed_location_path_for_backprop, source_backed_path,
    source_backpropagation_allowed_for_result,
};
#[cfg(test)]
use super::provenance::RuntimeBinarySourceProvenance;
use super::types::RewriteProposal;
use crate::types::{VerificationOutcome, VerificationResult};

#[cfg(test)]
/// Analyze verification failures and propose rewrites.
///
/// This is the CLI-level equivalent of trust-strengthen. It maps failed VCs
/// to rewrite proposals based on the failure kind (overflow, div-by-zero, etc.).
pub(crate) fn propose_rewrites(failures: &[VerificationResult]) -> Vec<RewriteProposal> {
    failures
        .iter()
        .filter(|r| r.outcome == VerificationOutcome::Failed)
        .map(|r| {
            let (kind, description) = classify_failure(r);
            RewriteProposal {
                function: extract_function_name(&r.raw_line),
                kind: kind.to_string(),
                description: description.to_string(),
            }
        })
        .collect()
}

#[cfg(test)]
/// Classify a verification failure into a rewrite category.
pub(super) fn classify_failure(result: &VerificationResult) -> (&'static str, &'static str) {
    let kind_lower = result.kind.to_lowercase();
    if kind_lower.contains("overflow") {
        ("safe_arithmetic", "Replace raw arithmetic with checked variant")
    } else if kind_lower.contains("div") && kind_lower.contains("zero") {
        ("non_zero_check", "Add divisor != 0 assertion before division")
    } else if kind_lower.contains("bounds") || kind_lower.contains("oob") {
        ("bounds_check", "Add index < len assertion before array access")
    } else {
        ("add_precondition", "Add precondition to constrain inputs")
    }
}

/// Extract a function name from a raw compiler diagnostic line, if present.
pub(super) fn extract_function_name(line: &str) -> String {
    // Look for patterns like "fn_name" or "mod::fn_name" in the line.
    // Fallback to "unknown" if we can't parse it.
    if let Some(idx) = line.find("Trust [") {
        let after = &line[idx..];
        if let Some(bracket_end) = after.find(']') {
            let kind = &after[7..bracket_end]; // after "Trust ["
            return kind.to_string();
        }
    }
    "unknown".to_string()
}

pub(super) fn to_failure_analysis(result: &VerificationResult) -> FailureAnalysis {
    let (vc, vr) = to_trust_pair(result);
    analyze_failure(&vc, &vr)
}

/// Reclassify a failed obligation's VC kind for the strengthen pass. Under the
/// hardened profile (which the loop enables by default) an arithmetic overflow
/// surfaces as a GENERIC `assertion` — `hardened boundary (panic_boundary):
/// mir_assert::Overflow(Add)` — which `parse_vc_kind` maps to `Assertion`. So
/// `analyze_failure` routes it to the generic/bounds placeholder path instead of
/// `propose_overflow_fix` (which yields a concrete `a <= MAX - b` precondition).
/// Exact structured transport wins: it preserves the real operand types and
/// prevents an unrelated `UnsupportedMir` diagnostic from becoming an
/// arithmetic repair merely because its text mentions `Overflow(Add)`. Only a
/// fieldless legacy row may use the narrow compatibility recovery below.
fn reclassified_vc_kind(result: &VerificationResult) -> trust_types::VcKind {
    use trust_types::{BinOp, VcKind};

    match crate::types::exact_structured_transport_vc_kind(result) {
        Ok(Some(kind)) => return kind,
        Err(()) => {
            return VcKind::UnsupportedMir {
                kind: result.kind.clone(),
                detail: "typed VC kind disagrees with its compact tag or description".to_string(),
            };
        }
        Ok(None) => {}
    }

    let op = match result.kind.as_str() {
        "overflow:add" | "arithmetic_overflow:add" | "arithmetic_overflow_add" => Some(BinOp::Add),
        "overflow:sub" | "arithmetic_overflow:sub" | "arithmetic_overflow_sub" => Some(BinOp::Sub),
        "overflow:mul" | "arithmetic_overflow:mul" | "arithmetic_overflow_mul" => Some(BinOp::Mul),
        kind if matches!(
            kind,
            "hardened_panic_boundary"
                | "hardened::panic_boundary"
                | "hardened:panic_boundary"
                | "hardened_panic"
                | "hardened::panic"
                | "hardened:panic"
        ) =>
        {
            if result.message.contains("mir_assert::Overflow(Add)") {
                Some(BinOp::Add)
            } else if result.message.contains("mir_assert::Overflow(Sub)") {
                Some(BinOp::Sub)
            } else if result.message.contains("mir_assert::Overflow(Mul)") {
                Some(BinOp::Mul)
            } else {
                None
            }
        }
        _ => None,
    };
    if let Some(op) = op {
        return VcKind::ArithmeticOverflow {
            op,
            operand_tys: (trust_types::Ty::u64(), trust_types::Ty::u64()),
        };
    }

    crate::report::parse_vc_kind(&result.kind)
}

pub(super) fn to_trust_pair(result: &VerificationResult) -> (VerificationCondition, TrustVr) {
    let vc = VerificationCondition {
        kind: reclassified_vc_kind(result),
        function: if result.function.is_empty() {
            result.kind.clone().into()
        } else {
            result.function.clone().into()
        },
        location: result.location.clone().unwrap_or_default(),
        formula: trust_types::Formula::Bool(true),
        contract_metadata: None,
        // Not a contract-derived VC: no obligation to back-reference.
        obligation: None,
    };
    let vr = match result.outcome {
        VerificationOutcome::Proved => TrustVr::Proved {
            solver: result.backend.clone().into(),
            time_ms: result.time_ms.unwrap_or(0),
            strength: trust_types::ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        },
        VerificationOutcome::Failed => TrustVr::Failed {
            solver: result.backend.clone().into(),
            time_ms: result.time_ms.unwrap_or(0),
            counterexample: result.counterexample.clone(),
        },
        VerificationOutcome::Unknown => TrustVr::Unknown {
            solver: result.backend.clone().into(),
            time_ms: result.time_ms.unwrap_or(0),
            reason: result.reason.clone().unwrap_or_else(|| "unknown".to_string()),
        },
        VerificationOutcome::RuntimeChecked => TrustVr::Unknown {
            solver: result.backend.clone().into(),
            time_ms: result.time_ms.unwrap_or(0),
            reason: result
                .reason
                .clone()
                .unwrap_or_else(|| "unproved obligation with runtime check".to_string()),
        },
        VerificationOutcome::Timeout => TrustVr::Timeout {
            solver: result.backend.clone().into(),
            timeout_ms: result.time_ms.unwrap_or(0),
        },
    };
    (vc, vr)
}

#[cfg(test)]
mod typed_kind_tests {
    use trust_types::{BinOp, TransportObligationResult, Ty, VcKind};

    use super::reclassified_vc_kind;
    use crate::types::{VerificationOutcome, VerificationResult, transport_to_verification_result};

    #[test]
    fn exact_typed_arithmetic_kind_keeps_real_operand_types_for_repair() {
        let typed_kind = VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (
                Ty::Int { width: 8, signed: false },
                Ty::Int { width: 16, signed: false },
            ),
        };
        let transport = TransportObligationResult {
            obligation_id: None,
            claim_digest_sha256: None,
            kind: typed_kind.transport_tag(),
            typed_kind: Some(Box::new(typed_kind.clone())),
            description: typed_kind.description(),
            location: None,
            outcome: trust_types::Outcome::Failed,
            solver: "ay".to_string(),
            time_ms: 1,
            counterexample: None,
            counterexample_model: None,
            reason: None,
            design_mandate: false,
            native_trust_ir: None,
            proof_evidence: None,
            monitor: None,
        };
        let result = transport_to_verification_result("crate::mixed_add", &transport);

        assert_eq!(reclassified_vc_kind(&result), typed_kind);
    }

    #[test]
    fn arbitrary_unsupported_text_cannot_fabricate_an_arithmetic_repair_kind() {
        let result = VerificationResult {
            function: "crate::opaque".to_string(),
            kind: "unknown".to_string(),
            message: "unsupported semantic gap mentions mir_assert::Overflow(Add) diagnostically"
                .to_string(),
            outcome: VerificationOutcome::Failed,
            backend: "trust-full-verifier".to_string(),
            time_ms: Some(1),
            location: None,
            counterexample: None,
            reason: None,
            raw_line: String::new(),
        };

        assert!(matches!(reclassified_vc_kind(&result), VcKind::UnsupportedMir { .. }));
    }

    #[test]
    fn fieldless_legacy_arithmetic_tag_retains_narrow_repair_compatibility() {
        let result = VerificationResult {
            function: "crate::legacy_add".to_string(),
            kind: "overflow:add".to_string(),
            message: "arithmetic overflow (Add)".to_string(),
            outcome: VerificationOutcome::Failed,
            backend: "ay".to_string(),
            time_ms: Some(1),
            location: None,
            counterexample: None,
            reason: None,
            raw_line: String::new(),
        };

        assert!(matches!(
            reclassified_vc_kind(&result),
            VcKind::ArithmeticOverflow { op: BinOp::Add, .. }
        ));
    }
}

pub(super) fn proposal_kind_tag(kind: &ProposalKind) -> &'static str {
    match kind {
        ProposalKind::AddPrecondition { .. } => "precondition",
        ProposalKind::AddPostcondition { .. } => "postcondition",
        ProposalKind::AddInvariant { .. } => "invariant",
        ProposalKind::SafeArithmetic { .. } => "safe_arithmetic",
        ProposalKind::AddBoundsCheck { .. } => "bounds_check",
        ProposalKind::AddNonZeroCheck { .. } => "non_zero_check",
    }
}

pub(super) fn summarize_proposal(proposal: &Proposal) -> RewriteProposal {
    let description = match &proposal.kind {
        ProposalKind::AddPrecondition { spec_body }
        | ProposalKind::AddPostcondition { spec_body }
        | ProposalKind::AddInvariant { spec_body } => spec_body.clone(),
        ProposalKind::SafeArithmetic { replacement, .. } => replacement.clone(),
        ProposalKind::AddBoundsCheck { check_expr }
        | ProposalKind::AddNonZeroCheck { check_expr } => check_expr.clone(),
    };
    RewriteProposal {
        function: proposal.function_name.clone(),
        kind: proposal_kind_tag(&proposal.kind).to_string(),
        description,
    }
}

pub(super) fn failure_pattern_label(pattern: &FailurePattern) -> &'static str {
    match pattern {
        FailurePattern::ArithmeticOverflow { .. } => "arithmetic_overflow",
        FailurePattern::DivisionByZero => "division_by_zero",
        FailurePattern::IndexOutOfBounds => "index_out_of_bounds",
        FailurePattern::CastOverflow => "cast_overflow",
        FailurePattern::NegationOverflow => "negation_overflow",
        FailurePattern::ShiftOverflow => "shift_overflow",
        FailurePattern::AssertionFailure { .. } => "assertion_failure",
        FailurePattern::PreconditionViolation { .. } => "precondition_violation",
        FailurePattern::PostconditionViolation => "postcondition_violation",
        FailurePattern::UnreachableReached => "unreachable",
        FailurePattern::Temporal => "temporal",
        FailurePattern::UnboundedAllocation { .. } => "unbounded_allocation",
        FailurePattern::Unknown => "unknown",
    }
}

pub(super) fn rewrite_spec_delta(
    rewrite: &SourceRewrite,
) -> (Option<String>, Option<String>, bool) {
    match &rewrite.kind {
        trust_backprop::RewriteKind::InsertContractClause { clause, expression } => {
            (None, Some(format!("{} {}", clause.keyword(), expression)), true)
        }
        trust_backprop::RewriteKind::InsertAttribute { attribute } => {
            (None, Some(attribute.clone()), true)
        }
        trust_backprop::RewriteKind::ReplaceExpression { old_text, new_text } => {
            (Some(old_text.clone()), Some(new_text.clone()), false)
        }
        trust_backprop::RewriteKind::InsertAssertion { assertion } => {
            (None, Some(assertion.clone()), true)
        }
        _ => (None, None, false),
    }
}

#[cfg(test)]
/// Convert a CLI-level `RewriteProposal` into a `trust_strengthen::Proposal`.
///
/// Maps the proposal kind string to the appropriate `ProposalKind` variant,
/// using the raw verification result line to extract file path information.
/// Falls back to `default_source_file` when the verification result lacks an
/// extractable path.
pub(super) fn to_strengthen_proposal(
    proposal: &RewriteProposal,
    verification_results: &[VerificationResult],
    default_source_file: Option<&str>,
    source_provenance: Option<&RuntimeBinarySourceProvenance>,
) -> Proposal {
    // Try to extract file path from the matching verification result's raw line.
    // The raw_line may contain a path like "src/lib.rs:10:5".
    let matching_failure = verification_results
        .iter()
        .find(|r| r.outcome == VerificationOutcome::Failed && r.kind == proposal.function);
    let file_path = matching_failure
        .and_then(|r| {
            source_backed_location_path_for_backprop(r, source_provenance)
                .map(str::to_string)
                .or_else(|| {
                    extract_file_path(&r.raw_line)
                        .and_then(|path| source_backed_path(&path).map(str::to_string))
                        .filter(|_| source_backpropagation_allowed_for_result(r, source_provenance))
                })
        })
        .or_else(|| {
            if matching_failure.is_none() {
                default_source_file.and_then(source_backed_path).map(String::from)
            } else {
                None
            }
        })
        .unwrap_or_else(|| proposal.function.clone());

    let kind = match proposal.kind.as_str() {
        "safe_arithmetic" => ProposalKind::SafeArithmetic {
            original: String::new(), // Resolved by trust-backprop locator from source
            replacement: String::new(),
        },
        "non_zero_check" => ProposalKind::AddNonZeroCheck {
            check_expr: "assert!(divisor != 0, \"divisor must be non-zero\")".into(),
        },
        "bounds_check" => ProposalKind::AddBoundsCheck {
            check_expr: "assert!(index < collection.len(), \"index out of bounds\")".into(),
        },
        _ => ProposalKind::AddPrecondition { spec_body: proposal.description.clone() },
    };

    Proposal {
        function_path: file_path,
        function_name: proposal.function.clone(),
        kind,
        confidence: 0.8,
        rationale: proposal.description.clone(),
    }
}

#[cfg(test)]
pub(super) fn proposal_has_binary_only_span(
    proposal: &RewriteProposal,
    verification_results: &[VerificationResult],
) -> bool {
    use super::backprop_gate::has_binary_only_location;
    verification_results.iter().any(|r| {
        r.outcome == VerificationOutcome::Failed
            && r.kind == proposal.function
            && has_binary_only_location(r)
    })
}

#[cfg(test)]
pub(super) fn proposal_has_rejected_binary_source_span(
    proposal: &RewriteProposal,
    verification_results: &[VerificationResult],
    source_provenance: Option<&RuntimeBinarySourceProvenance>,
) -> bool {
    use super::backprop_gate::{is_binary_derived_result, source_backed_location_path};
    verification_results.iter().any(|r| {
        r.outcome == VerificationOutcome::Failed
            && r.kind == proposal.function
            && is_binary_derived_result(r)
            && source_backed_location_path(r).is_some()
            && !source_backpropagation_allowed_for_result(r, source_provenance)
    })
}

#[cfg(test)]
/// Try to extract a file path from a raw compiler diagnostic line.
///
/// Looks for patterns like `/path/to/file.rs:10:5` or `src/file.rs:10`.
pub(super) fn extract_file_path(line: &str) -> Option<String> {
    // Look for a .rs file reference with line number
    for segment in line.split_whitespace() {
        let cleaned = segment.trim_start_matches('(').trim_end_matches(')');
        if cleaned.ends_with(".rs") || cleaned.contains(".rs:") {
            // Strip line:col suffix
            let path =
                if let Some(idx) = cleaned.find(".rs:") { &cleaned[..idx + 3] } else { cleaned };
            return Some(path.to_string());
        }
    }
    None
}
