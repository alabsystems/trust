// trust-strengthen/heuristic.rs: LLM-free specification strengthening via program analysis
//
// Provides a fast, deterministic fallback for spec inference that uses pattern
// recognition, counterexample analysis, and signature-based heuristics instead
// of LLM calls. Suitable for offline use, CI/CD pipelines, and as a first-pass
// before expensive LLM invocations.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;
use trust_types::{BinOp, Counterexample, VcKind, VerificationResult};

use crate::analyzer::FailurePattern;
use crate::counterexample::{extract_hints, hints_to_preconditions, hints_to_spec_body};
use crate::patterns::{pattern_matches_to_proposals, recognize_patterns};
use crate::proposer::{Proposal, ProposalKind};

/// A verification failure with enough context for heuristic strengthening.
#[derive(Debug, Clone)]
pub struct VerificationFailure {
    /// The VC kind that failed.
    pub vc_kind: VcKind,
    /// The function containing the failure.
    pub function_path: String,
    /// Human-readable function name.
    pub function_name: String,
    /// Solver counterexample, if available.
    pub counterexample: Option<Counterexample>,
    /// The verification result.
    pub result: VerificationResult,
}

/// A function signature for signature-based inference.
#[derive(Debug, Clone)]
pub struct FunctionSignature {
    /// Fully-qualified path (e.g., "crate::module::func").
    pub path: String,
    /// Short name (e.g., "func").
    pub name: String,
    /// Parameters: (name, type_string).
    pub params: Vec<(String, String)>,
    /// Return type, if any.
    pub return_type: Option<String>,
}

/// LLM-free spec strengthener using program analysis heuristics.
///
/// Combines three strategies:
/// 1. **Pattern-based**: Recognizes common code patterns (binary search, sort, etc.)
///    and proposes known-good specs for them.
/// 2. **Counterexample-guided**: Analyzes failing counterexamples to derive guard
///    conditions that prevent the failure.
/// 3. **Signature-based**: Infers preconditions and postconditions from parameter
///    types and return types alone.
pub struct HeuristicStrengthener {
    /// Minimum confidence threshold for proposals.
    min_confidence: f64,
    /// Maximum proposals per function.
    max_proposals: usize,
}

impl HeuristicStrengthener {
    /// Create a new heuristic strengthener with the given thresholds.
    #[must_use]
    pub fn new(min_confidence: f64, max_proposals: usize) -> Self {
        Self { min_confidence, max_proposals }
    }

    /// Strengthen from a verification failure using all available heuristics.
    ///
    /// Combines pattern-based, counterexample-guided, and failure-pattern strategies.
    /// Returns proposals sorted by confidence (highest first), filtered by
    /// `min_confidence`, and capped at `max_proposals`.
    #[must_use]
    pub fn strengthen_from_failure(&self, failure: &VerificationFailure) -> Vec<Proposal> {
        let mut proposals = Vec::new();

        // Strategy 1: Pattern-based inference from function name + VC kind
        let pattern_proposals =
            recognize_patterns(&failure.function_name, std::slice::from_ref(&failure.vc_kind));
        proposals.extend(pattern_matches_to_proposals(
            &failure.function_path,
            &failure.function_name,
            &pattern_proposals,
        ));

        // Strategy 2: Counterexample-guided inference
        if let Some(ref cex) = failure.counterexample {
            let pattern = classify_failure_pattern(&failure.vc_kind);
            let hints = extract_hints(cex, &pattern, &failure.vc_kind);

            // Build preconditions from hints
            let preconditions = hints_to_preconditions(&hints);
            for pre in &preconditions {
                let confidence_boost: f64 =
                    hints.iter().map(|h| h.confidence_boost).sum::<f64>().min(0.2);
                proposals.push(Proposal {
                    function_path: failure.function_path.clone(),
                    function_name: failure.function_name.clone(),
                    kind: ProposalKind::AddPrecondition { spec_body: pre.clone() },
                    confidence: (0.8 + confidence_boost).min(1.0),
                    rationale: format!(
                        "Counterexample-guided: concrete violation suggests {}",
                        pre
                    ),
                });
            }

            // Build a combined spec body
            if let Some(spec_body) = hints_to_spec_body(&hints, &pattern) {
                proposals.push(Proposal {
                    function_path: failure.function_path.clone(),
                    function_name: failure.function_name.clone(),
                    kind: ProposalKind::AddPrecondition { spec_body: spec_body.clone() },
                    confidence: 0.85,
                    rationale: format!("Counterexample-guided combined guard: {spec_body}"),
                });
            }
        }

        // Strategy 3: Failure-pattern-specific proposals
        proposals.extend(failure_pattern_proposals(
            &failure.function_path,
            &failure.function_name,
            &failure.vc_kind,
        ));

        // Deduplicate by spec body
        dedup_proposals(&mut proposals);

        // Filter and sort
        proposals.retain(|p| p.confidence >= self.min_confidence);
        proposals.sort_by(|a, b| {
            b.confidence.partial_cmp(&a.confidence).unwrap_or(std::cmp::Ordering::Equal)
        });
        proposals.truncate(self.max_proposals);

        proposals
    }

    /// Infer specs purely from a function's signature (no failure information needed).
    ///
    /// Useful as a pre-verification pass: derive obvious preconditions from parameter
    /// types before any solver runs.
    #[must_use]
    pub fn strengthen_from_signature(&self, sig: &FunctionSignature) -> Vec<Proposal> {
        let mut proposals = Vec::new();

        // Pattern recognition from function name alone
        let pattern_matches = recognize_patterns(&sig.name, &[]);
        proposals.extend(pattern_matches_to_proposals(&sig.path, &sig.name, &pattern_matches));

        // Type-based precondition inference
        for (param_name, param_type) in &sig.params {
            proposals.extend(infer_from_param_type(&sig.path, &sig.name, param_name, param_type));
        }

        // Return-type-based postcondition inference
        if let Some(ref ret_ty) = sig.return_type {
            proposals.extend(infer_from_return_type(&sig.path, &sig.name, ret_ty));
        }

        // Deduplicate, filter, sort
        dedup_proposals(&mut proposals);
        proposals.retain(|p| p.confidence >= self.min_confidence);
        proposals.sort_by(|a, b| {
            b.confidence.partial_cmp(&a.confidence).unwrap_or(std::cmp::Ordering::Equal)
        });
        proposals.truncate(self.max_proposals);

        proposals
    }
}

impl Default for HeuristicStrengthener {
    fn default() -> Self {
        Self::new(0.5, 10)
    }
}

/// Classify a VcKind into a FailurePattern for counterexample extraction.
fn classify_failure_pattern(vc_kind: &VcKind) -> FailurePattern {
    match vc_kind {
        VcKind::ArithmeticOverflow { op, .. } => FailurePattern::ArithmeticOverflow { op: *op },
        VcKind::DivisionByZero | VcKind::RemainderByZero => FailurePattern::DivisionByZero,
        VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => FailurePattern::IndexOutOfBounds,
        VcKind::CastOverflow { .. } => FailurePattern::CastOverflow,
        VcKind::NegationOverflow { .. } => FailurePattern::NegationOverflow,
        VcKind::ShiftOverflow { .. } => FailurePattern::ShiftOverflow,
        VcKind::Assertion { message } => {
            FailurePattern::AssertionFailure { message: message.clone() }
        }
        VcKind::Precondition { callee } => {
            FailurePattern::PreconditionViolation { callee: callee.clone() }
        }
        VcKind::Postcondition => FailurePattern::PostconditionViolation,
        VcKind::Unreachable => FailurePattern::UnreachableReached,
        _ => FailurePattern::Unknown,
    }
}

/// Generate proposals from the VC kind alone (no counterexample needed).
fn failure_pattern_proposals(
    function_path: &str,
    function_name: &str,
    vc_kind: &VcKind,
) -> Vec<Proposal> {
    match vc_kind {
        VcKind::ArithmeticOverflow { op, .. } => {
            let op_name = match op {
                BinOp::Add => "addition",
                BinOp::Sub => "subtraction",
                BinOp::Mul => "multiplication",
                _ => "operation",
            };
            vec![Proposal {
                function_path: function_path.into(),
                function_name: function_name.into(),
                kind: ProposalKind::AddPrecondition {
                    spec_body: format!("{op_name} does not overflow"),
                },
                confidence: 0.7,
                rationale: format!("Arithmetic {op_name} may overflow"),
            }]
        }
        VcKind::DivisionByZero | VcKind::RemainderByZero => {
            vec![Proposal {
                function_path: function_path.into(),
                function_name: function_name.into(),
                kind: ProposalKind::AddPrecondition { spec_body: "divisor != 0".into() },
                confidence: 0.95,
                rationale: "Division by zero possible".into(),
            }]
        }
        VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => {
            vec![Proposal {
                function_path: function_path.into(),
                function_name: function_name.into(),
                kind: ProposalKind::AddPrecondition { spec_body: "index < slice.len()".into() },
                confidence: 0.9,
                rationale: "Index out of bounds possible".into(),
            }]
        }
        VcKind::CastOverflow { .. } => {
            vec![Proposal {
                function_path: function_path.into(),
                function_name: function_name.into(),
                kind: ProposalKind::AddPrecondition {
                    spec_body: "value fits in target type".into(),
                },
                confidence: 0.7,
                rationale: "Cast may overflow target type".into(),
            }]
        }
        VcKind::NegationOverflow { .. } => {
            vec![Proposal {
                function_path: function_path.into(),
                function_name: function_name.into(),
                kind: ProposalKind::AddPrecondition { spec_body: "value != MIN".into() },
                confidence: 0.9,
                rationale: "Negation of MIN overflows".into(),
            }]
        }
        VcKind::ShiftOverflow { .. } => {
            vec![Proposal {
                function_path: function_path.into(),
                function_name: function_name.into(),
                kind: ProposalKind::AddPrecondition { spec_body: "shift < bit_width".into() },
                confidence: 0.9,
                rationale: "Shift amount must be less than bit width".into(),
            }]
        }
        _ => vec![],
    }
}

/// Infer preconditions from a parameter's type.
fn infer_from_param_type(
    function_path: &str,
    function_name: &str,
    param_name: &str,
    param_type: &str,
) -> Vec<Proposal> {
    let mut proposals = Vec::new();
    let trimmed = param_type.trim();

    // Slice/array parameters: non-empty checks
    if trimmed.starts_with("&[") || trimmed.starts_with("&mut [") {
        proposals.push(Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddPrecondition { spec_body: format!("{param_name}.len() > 0") },
            confidence: 0.5,
            rationale: format!("Slice parameter `{param_name}` may need non-empty precondition"),
        });
    }

    // usize parameters used as indices: bounded check
    if trimmed == "usize" && is_likely_index(param_name) {
        proposals.push(Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddPrecondition {
                spec_body: format!("{param_name} < collection.len()"),
            },
            confidence: 0.6,
            rationale: format!("Parameter `{param_name}: usize` likely used as index"),
        });
    }

    // Numeric divisor parameters: non-zero check
    if is_likely_divisor(param_name) && is_numeric_type(trimmed) {
        proposals.push(Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddPrecondition { spec_body: format!("{param_name} != 0") },
            confidence: 0.8,
            rationale: format!("Parameter `{param_name}` likely used as divisor"),
        });
    }

    // Option/Result unwrap safety
    if trimmed.starts_with("Option<") {
        proposals.push(Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddPrecondition { spec_body: format!("{param_name}.is_some()") },
            confidence: 0.5,
            rationale: format!("Option parameter `{param_name}` may be unwrapped"),
        });
    }

    proposals
}

/// Infer postconditions from a function's return type.
fn infer_from_return_type(
    function_path: &str,
    function_name: &str,
    return_type: &str,
) -> Vec<Proposal> {
    let mut proposals = Vec::new();
    let trimmed = return_type.trim();

    // Result return: error path postcondition
    if trimmed.starts_with("Result<") {
        proposals.push(Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddPostcondition {
                spec_body: "result.is_ok() ==> postcondition holds".into(),
            },
            confidence: 0.5,
            rationale: "Result-returning function: postcondition on Ok path".into(),
        });
    }

    // Option return: None means not found
    if trimmed.starts_with("Option<") {
        proposals.push(Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddPostcondition {
                spec_body: "result.is_none() ==> element not present".into(),
            },
            confidence: 0.5,
            rationale: "Option-returning function: None means not found".into(),
        });
    }

    // Bool return: predicate postcondition
    if trimmed == "bool" {
        proposals.push(Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddPostcondition {
                spec_body: "result == (predicate holds)".into(),
            },
            confidence: 0.4,
            rationale: "Bool-returning function: result encodes a predicate".into(),
        });
    }

    // Vec return: length relationship
    if trimmed.starts_with("Vec<") {
        proposals.push(Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddPostcondition {
                spec_body: "result.len() <= input.len()".into(),
            },
            confidence: 0.4,
            rationale: "Vec-returning function: output length bounded by input".into(),
        });
    }

    // Numeric return with same type as input: range preservation
    if is_numeric_type(trimmed) {
        proposals.push(Proposal {
            function_path: function_path.into(),
            function_name: function_name.into(),
            kind: ProposalKind::AddPostcondition { spec_body: format!("result fits in {trimmed}") },
            confidence: 0.6,
            rationale: format!("Numeric return `{trimmed}`: result within type bounds"),
        });
    }

    proposals
}

/// Remove duplicate proposals (same kind + spec_body).
fn dedup_proposals(proposals: &mut Vec<Proposal>) {
    let mut seen = FxHashSet::default();
    proposals.retain(|p| {
        let key = format!("{:?}:{}", std::mem::discriminant(&p.kind), spec_body_of(&p.kind));
        seen.insert(key)
    });
}

/// Extract the spec body string from a ProposalKind for dedup purposes.
fn spec_body_of(kind: &ProposalKind) -> String {
    match kind {
        ProposalKind::AddPrecondition { spec_body }
        | ProposalKind::AddPostcondition { spec_body }
        | ProposalKind::AddInvariant { spec_body } => spec_body.clone(),
        ProposalKind::SafeArithmetic { original, replacement } => {
            format!("{original}->{replacement}")
        }
        ProposalKind::AddBoundsCheck { check_expr } => check_expr.clone(),
        ProposalKind::AddNonZeroCheck { check_expr } => check_expr.clone(),
    }
}

/// Check if a parameter name looks like an index variable.
fn is_likely_index(name: &str) -> bool {
    let lower = name.to_lowercase();
    lower == "i"
        || lower == "j"
        || lower == "k"
        || lower == "idx"
        || lower == "index"
        || lower == "pos"
        || lower == "offset"
        || lower.ends_with("_idx")
        || lower.ends_with("_index")
}

/// Check if a parameter name looks like a divisor.
fn is_likely_divisor(name: &str) -> bool {
    let lower = name.to_lowercase();
    lower == "divisor"
        || lower == "denominator"
        || lower == "denom"
        || lower == "d"
        || lower == "y"
        || lower == "b"
        || lower == "n"
        || lower == "modulus"
        || lower.ends_with("_divisor")
}

/// Check if a type string represents a numeric type.
fn is_numeric_type(ty: &str) -> bool {
    matches!(
        ty,
        "u8" | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "f32"
            | "f64"
    )
}

#[cfg(test)]
mod tests {
    use trust_types::{CounterexampleValue, Ty};

    use super::*;

    fn make_failure(
        vc_kind: VcKind,
        func_name: &str,
        counterexample: Option<Counterexample>,
    ) -> VerificationFailure {
        VerificationFailure {
            vc_kind,
            function_path: format!("test::{func_name}"),
            function_name: func_name.into(),
            counterexample,
            result: VerificationResult::Failed {
                solver: "ay".into(),
                time_ms: 1,
                counterexample: None,
            },
        }
    }

    fn make_signature(
        name: &str,
        params: Vec<(&str, &str)>,
        return_type: Option<&str>,
    ) -> FunctionSignature {
        FunctionSignature {
            path: format!("test::{name}"),
            name: name.into(),
            params: params.into_iter().map(|(n, t)| (n.into(), t.into())).collect(),
            return_type: return_type.map(Into::into),
        }
    }

    // --- HeuristicStrengthener::strengthen_from_failure ---

    #[test]
    fn test_strengthen_overflow_no_cex() {
        let strengthener = HeuristicStrengthener::default();
        let failure = make_failure(
            VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (
                    Ty::Int { width: 64, signed: false },
                    Ty::Int { width: 64, signed: false },
                ),
            },
            "get_midpoint",
            None,
        );

        let proposals = strengthener.strengthen_from_failure(&failure);
        assert!(!proposals.is_empty(), "should produce proposals for overflow");

        let has_precondition =
            proposals.iter().any(|p| matches!(p.kind, ProposalKind::AddPrecondition { .. }));
        assert!(has_precondition, "should have at least one precondition proposal");
    }

    #[test]
    fn test_strengthen_div_zero_with_counterexample() {
        let strengthener = HeuristicStrengthener::default();
        let cex = Counterexample::new(vec![
            ("x".into(), CounterexampleValue::Uint(42)),
            ("y".into(), CounterexampleValue::Uint(0)),
        ]);
        let failure = make_failure(VcKind::DivisionByZero, "safe_divide", Some(cex));

        let proposals = strengthener.strengthen_from_failure(&failure);
        assert!(!proposals.is_empty());

        // Should have a non-zero precondition from the counterexample
        let has_nonzero = proposals.iter().any(|p| {
            if let ProposalKind::AddPrecondition { spec_body } = &p.kind {
                spec_body.contains("!= 0")
            } else {
                false
            }
        });
        assert!(has_nonzero, "should derive non-zero precondition from counterexample");
    }

    #[test]
    fn test_strengthen_oob_no_cex() {
        let strengthener = HeuristicStrengthener::default();
        let failure = make_failure(VcKind::IndexOutOfBounds, "get_element", None);

        let proposals = strengthener.strengthen_from_failure(&failure);
        assert!(!proposals.is_empty());

        let has_bounds = proposals.iter().any(|p| {
            if let ProposalKind::AddPrecondition { spec_body } = &p.kind {
                spec_body.contains("< ") && spec_body.contains("len")
            } else {
                false
            }
        });
        assert!(has_bounds, "should propose bounds check for OOB");
    }

    #[test]
    fn test_strengthen_overflow_with_counterexample() {
        let strengthener = HeuristicStrengthener::default();
        let cex = Counterexample::new(vec![
            ("a".into(), CounterexampleValue::Uint(u64::MAX as u128)),
            ("b".into(), CounterexampleValue::Uint(1)),
        ]);
        let failure = make_failure(
            VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (
                    Ty::Int { width: 64, signed: false },
                    Ty::Int { width: 64, signed: false },
                ),
            },
            "get_midpoint",
            Some(cex),
        );

        let proposals = strengthener.strengthen_from_failure(&failure);
        assert!(
            proposals.len() >= 2,
            "overflow with CEX should produce multiple proposals, got {}",
            proposals.len()
        );
    }

    #[test]
    fn test_strengthen_respects_min_confidence() {
        let strengthener = HeuristicStrengthener::new(0.99, 10);
        let failure = make_failure(VcKind::DivisionByZero, "unknown_func", None);

        let proposals = strengthener.strengthen_from_failure(&failure);
        for p in &proposals {
            assert!(
                p.confidence >= 0.99,
                "proposal confidence {} below threshold 0.99",
                p.confidence
            );
        }
    }

    #[test]
    fn test_strengthen_respects_max_proposals() {
        let strengthener = HeuristicStrengthener::new(0.0, 2);
        let cex = Counterexample::new(vec![
            ("a".into(), CounterexampleValue::Uint(u64::MAX as u128)),
            ("b".into(), CounterexampleValue::Uint(1)),
        ]);
        let failure = make_failure(
            VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (
                    Ty::Int { width: 64, signed: false },
                    Ty::Int { width: 64, signed: false },
                ),
            },
            "midpoint",
            Some(cex),
        );

        let proposals = strengthener.strengthen_from_failure(&failure);
        assert!(proposals.len() <= 2, "should cap at max_proposals=2");
    }

    #[test]
    fn test_strengthen_sorted_by_confidence_descending() {
        let strengthener = HeuristicStrengthener::new(0.0, 50);
        let cex = Counterexample::new(vec![
            ("a".into(), CounterexampleValue::Uint(u64::MAX as u128)),
            ("b".into(), CounterexampleValue::Uint(1)),
        ]);
        let failure = make_failure(
            VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (
                    Ty::Int { width: 64, signed: false },
                    Ty::Int { width: 64, signed: false },
                ),
            },
            "midpoint",
            Some(cex),
        );

        let proposals = strengthener.strengthen_from_failure(&failure);
        for window in proposals.windows(2) {
            assert!(
                window[0].confidence >= window[1].confidence,
                "proposals should be sorted descending: {} >= {}",
                window[0].confidence,
                window[1].confidence
            );
        }
    }

    // --- HeuristicStrengthener::strengthen_from_signature ---

    #[test]
    fn test_signature_binary_search() {
        let strengthener = HeuristicStrengthener::default();
        let sig = make_signature(
            "binary_search",
            vec![("slice", "&[i32]"), ("target", "i32")],
            Some("Option<usize>"),
        );

        let proposals = strengthener.strengthen_from_signature(&sig);
        assert!(!proposals.is_empty(), "binary_search should produce proposals");

        // Should recognize the binary search pattern
        let has_sorted_precondition = proposals.iter().any(|p| {
            if let ProposalKind::AddPrecondition { spec_body } = &p.kind {
                spec_body.contains("sorted")
            } else {
                false
            }
        });
        assert!(has_sorted_precondition, "should recognize binary search pattern");
    }

    #[test]
    fn test_signature_slice_nonempty() {
        let strengthener = HeuristicStrengthener::default();
        let sig = make_signature("sum", vec![("data", "&[f64]")], Some("f64"));

        let proposals = strengthener.strengthen_from_signature(&sig);
        let has_nonempty = proposals.iter().any(|p| {
            if let ProposalKind::AddPrecondition { spec_body } = &p.kind {
                spec_body.contains("data.len() > 0")
            } else {
                false
            }
        });
        assert!(has_nonempty, "should propose non-empty precondition for slice param");
    }

    #[test]
    fn test_signature_index_param() {
        let strengthener = HeuristicStrengthener::default();
        let sig = make_signature("get", vec![("arr", "&[i32]"), ("idx", "usize")], Some("i32"));

        let proposals = strengthener.strengthen_from_signature(&sig);
        let has_bounds = proposals.iter().any(|p| {
            if let ProposalKind::AddPrecondition { spec_body } = &p.kind {
                spec_body.contains("idx") && spec_body.contains("len")
            } else {
                false
            }
        });
        assert!(has_bounds, "should propose index bounds check for `idx: usize`");
    }

    #[test]
    fn test_signature_divisor_param() {
        let strengthener = HeuristicStrengthener::default();
        let sig =
            make_signature("safe_divide", vec![("x", "u64"), ("divisor", "u64")], Some("u64"));

        let proposals = strengthener.strengthen_from_signature(&sig);
        let has_nonzero = proposals.iter().any(|p| {
            if let ProposalKind::AddPrecondition { spec_body } = &p.kind {
                spec_body.contains("divisor != 0")
            } else {
                false
            }
        });
        assert!(has_nonzero, "should propose non-zero check for `divisor: u64`");
    }

    #[test]
    fn test_signature_result_return() {
        let strengthener = HeuristicStrengthener::default();
        let sig =
            make_signature("parse_config", vec![("input", "&str")], Some("Result<Config, Error>"));

        let proposals = strengthener.strengthen_from_signature(&sig);
        let has_result_post =
            proposals.iter().any(|p| matches!(p.kind, ProposalKind::AddPostcondition { .. }));
        assert!(has_result_post, "should propose postcondition for Result return");
    }

    #[test]
    fn test_signature_option_return() {
        let strengthener = HeuristicStrengthener::default();
        let sig = make_signature(
            "find_item",
            vec![("items", "&[Item]"), ("key", "&str")],
            Some("Option<&Item>"),
        );

        let proposals = strengthener.strengthen_from_signature(&sig);
        let has_option_post = proposals.iter().any(|p| {
            if let ProposalKind::AddPostcondition { spec_body } = &p.kind {
                spec_body.contains("is_none")
            } else {
                false
            }
        });
        assert!(has_option_post, "should propose postcondition for Option return");
    }

    #[test]
    fn test_signature_empty_params() {
        let strengthener = HeuristicStrengthener::default();
        let sig = make_signature("get_version", vec![], Some("u32"));

        let proposals = strengthener.strengthen_from_signature(&sig);
        // Should still produce a numeric postcondition
        let has_numeric_post =
            proposals.iter().any(|p| matches!(p.kind, ProposalKind::AddPostcondition { .. }));
        assert!(has_numeric_post, "numeric return should produce postcondition");
    }

    #[test]
    fn test_signature_unknown_function() {
        let strengthener = HeuristicStrengthener::default();
        let sig = make_signature("frobulate", vec![("x", "i32")], Some("i32"));

        let proposals = strengthener.strengthen_from_signature(&sig);
        // Should still produce basic type-based proposals
        let has_proposals =
            proposals.iter().any(|p| matches!(p.kind, ProposalKind::AddPostcondition { .. }));
        assert!(has_proposals, "even unknown functions should get type-based proposals");
    }

    // --- Utility function tests ---

    #[test]
    fn test_is_likely_index() {
        assert!(is_likely_index("i"));
        assert!(is_likely_index("idx"));
        assert!(is_likely_index("index"));
        assert!(is_likely_index("pos"));
        assert!(is_likely_index("row_idx"));
        assert!(!is_likely_index("name"));
        assert!(!is_likely_index("value"));
    }

    #[test]
    fn test_is_likely_divisor() {
        assert!(is_likely_divisor("divisor"));
        assert!(is_likely_divisor("denominator"));
        assert!(is_likely_divisor("d"));
        assert!(is_likely_divisor("modulus"));
        assert!(!is_likely_divisor("name"));
        assert!(!is_likely_divisor("result"));
    }

    #[test]
    fn test_is_numeric_type() {
        assert!(is_numeric_type("u64"));
        assert!(is_numeric_type("i32"));
        assert!(is_numeric_type("usize"));
        assert!(is_numeric_type("f64"));
        assert!(!is_numeric_type("String"));
        assert!(!is_numeric_type("Vec<u8>"));
        assert!(!is_numeric_type("&str"));
    }

    #[test]
    fn test_dedup_removes_same_spec_body() {
        let mut proposals = vec![
            Proposal {
                function_path: "test::f".into(),
                function_name: "f".into(),
                kind: ProposalKind::AddPrecondition { spec_body: "x != 0".into() },
                confidence: 0.9,
                rationale: "first".into(),
            },
            Proposal {
                function_path: "test::f".into(),
                function_name: "f".into(),
                kind: ProposalKind::AddPrecondition { spec_body: "x != 0".into() },
                confidence: 0.8,
                rationale: "second".into(),
            },
        ];
        dedup_proposals(&mut proposals);
        assert_eq!(proposals.len(), 1, "duplicate proposals should be removed");
    }

    #[test]
    fn test_dedup_keeps_different_kinds() {
        let mut proposals = vec![
            Proposal {
                function_path: "test::f".into(),
                function_name: "f".into(),
                kind: ProposalKind::AddPrecondition { spec_body: "x != 0".into() },
                confidence: 0.9,
                rationale: "pre".into(),
            },
            Proposal {
                function_path: "test::f".into(),
                function_name: "f".into(),
                kind: ProposalKind::AddPostcondition { spec_body: "x != 0".into() },
                confidence: 0.8,
                rationale: "post".into(),
            },
        ];
        dedup_proposals(&mut proposals);
        assert_eq!(proposals.len(), 2, "different kinds should not be deduped");
    }

    #[test]
    fn test_option_param_precondition() {
        let strengthener = HeuristicStrengthener::default();
        let sig = make_signature("process", vec![("config", "Option<Config>")], Some("()"));

        let proposals = strengthener.strengthen_from_signature(&sig);
        let has_some = proposals.iter().any(|p| {
            if let ProposalKind::AddPrecondition { spec_body } = &p.kind {
                spec_body.contains("is_some")
            } else {
                false
            }
        });
        assert!(has_some, "Option param should get is_some() precondition");
    }

    #[test]
    fn test_strengthen_cast_overflow() {
        let strengthener = HeuristicStrengthener::default();
        let failure = make_failure(
            VcKind::CastOverflow {
                from_ty: Ty::Int { width: 64, signed: false },
                to_ty: Ty::Int { width: 32, signed: false },
            },
            "narrow",
            None,
        );

        let proposals = strengthener.strengthen_from_failure(&failure);
        assert!(!proposals.is_empty(), "cast overflow should produce proposals");
    }

    #[test]
    fn test_strengthen_negation_overflow() {
        let strengthener = HeuristicStrengthener::default();
        let failure = make_failure(
            VcKind::NegationOverflow { ty: Ty::Int { width: 64, signed: true } },
            "negate",
            None,
        );

        let proposals = strengthener.strengthen_from_failure(&failure);
        let has_min_check = proposals.iter().any(|p| {
            if let ProposalKind::AddPrecondition { spec_body } = &p.kind {
                spec_body.contains("MIN")
            } else {
                false
            }
        });
        assert!(has_min_check, "negation overflow should propose != MIN check");
    }

    #[test]
    fn test_strengthen_shift_overflow() {
        let strengthener = HeuristicStrengthener::default();
        let failure = make_failure(
            VcKind::ShiftOverflow {
                op: BinOp::Shl,
                operand_ty: Ty::Int { width: 64, signed: false },
                shift_ty: Ty::Int { width: 64, signed: false },
            },
            "shift_left",
            None,
        );

        let proposals = strengthener.strengthen_from_failure(&failure);
        let has_shift_check = proposals.iter().any(|p| {
            if let ProposalKind::AddPrecondition { spec_body } = &p.kind {
                spec_body.contains("bit_width")
            } else {
                false
            }
        });
        assert!(has_shift_check, "shift overflow should propose bit_width check");
    }
}
