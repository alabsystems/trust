// trust-strengthen/spec_inference.rs: Function-level spec inference from VcKind
//
// Generates structured StrengtheningProposal for each VcKind variant.
// Each proposal carries native clause text, an insertion target, and
// confidence score. This bridges the gap between failed VCs and actionable
// source annotations.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{BinOp, Counterexample, VcKind, VerificationCondition};

use crate::cex_guided::{CexModel, CounterexampleAnalyzer};

/// Where to insert a proposed specification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InsertionTarget {
    /// Fully qualified function path (e.g., "crate::module::func").
    pub function_path: String,
    /// Human-readable function name.
    pub function_name: String,
    /// Source file path, if known.
    pub file: Option<String>,
    /// Line number in the source file, if known.
    pub line: Option<u32>,
}

/// A structured proposal to strengthen a function's specification.
///
/// Generated from a failing `VerificationCondition`, each proposal contains
/// the exact native clause text to insert (e.g., `requires divisor != 0`),
/// the target location, and a confidence score.
#[derive(Debug, Clone)]
pub struct StrengtheningProposal {
    /// Native clause text (e.g., `requires a <= usize::MAX - b`) or a
    /// clearly labelled non-contract code suggestion.
    pub spec_text: String,
    /// Where to insert this spec.
    pub target: InsertionTarget,
    /// Confidence in this proposal (0.0 = speculative, 1.0 = certain).
    pub confidence: f64,
    /// Which VcKind triggered this proposal.
    pub vc_kind_name: String,
    /// Human-readable rationale.
    pub rationale: String,
}

/// Generate strengthening proposals for a failed verification condition.
///
/// Dispatches to per-VcKind generators. Returns one or more proposals
/// sorted by confidence (highest first).
#[must_use]
pub fn infer_specs(vc: &VerificationCondition) -> Vec<StrengtheningProposal> {
    let target = InsertionTarget {
        function_path: vc.function.as_str().to_string(),
        function_name: short_name(vc.function.as_str()),
        file: if vc.location.file.is_empty() { None } else { Some(vc.location.file.clone()) },
        line: if vc.location.line_start == 0 { None } else { Some(vc.location.line_start) },
    };

    let mut proposals = match &vc.kind {
        VcKind::ArithmeticOverflow { op, operand_tys } => {
            infer_arithmetic_overflow(&target, op, operand_tys)
        }
        VcKind::DivisionByZero | VcKind::RemainderByZero => infer_division_by_zero(&target),
        VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => infer_index_out_of_bounds(&target),
        VcKind::NegationOverflow { ty } => infer_negation_overflow(&target, ty),
        VcKind::CastOverflow { from_ty, to_ty } => infer_cast_overflow(&target, from_ty, to_ty),
        VcKind::ShiftOverflow { op: _, operand_ty, shift_ty: _ } => {
            infer_shift_overflow(&target, operand_ty)
        }
        VcKind::Assertion { message } => infer_assertion_failure(&target, message),
        VcKind::Precondition { callee } => infer_precondition_violation(&target, callee),
        VcKind::Postcondition => infer_postcondition_violation(&target),
        VcKind::Unreachable => infer_unreachable(&target),
        // VcKinds without a specialized generator (temporal, neural, ...) yield
        // nothing. A proposal whose body is a note-to-self is not a proposal: it
        // ranks against real candidates and can be applied as a comment that
        // changes no obligation.
        _ => Vec::new(),
    };

    // Sort by confidence descending
    proposals.sort_by(|a, b| {
        b.confidence.partial_cmp(&a.confidence).unwrap_or(std::cmp::Ordering::Equal)
    });

    proposals
}

/// Enhanced spec inference using a counterexample model from ay.
///
/// When a counterexample is available, this produces tighter proposals with
/// higher confidence than the heuristic-only `infer_specs()`. The concrete
/// variable assignments from the counterexample are used to:
/// - Identify exactly which variable is at a boundary value
/// - Produce precise preconditions with real variable names
/// - Boost confidence because the proposal is grounded in a concrete witness
///
/// Falls back to heuristic-only proposals if the counterexample provides no
/// useful refinement (e.g., no recognized variable patterns).
#[must_use]
pub fn infer_specs_with_cex(
    vc: &VerificationCondition,
    counterexample: &Counterexample,
) -> Vec<StrengtheningProposal> {
    let cex_model = CexModel::from_counterexample(counterexample);
    let cex_proposals = CounterexampleAnalyzer::refine(vc, &cex_model);

    if cex_proposals.is_empty() {
        // No useful refinement from cex; fall back to heuristic
        return infer_specs(vc);
    }

    cex_proposals
}

// ---------------------------------------------------------------------------
// Per-VcKind generators
// ---------------------------------------------------------------------------

fn infer_arithmetic_overflow(
    target: &InsertionTarget,
    op: &BinOp,
    operand_tys: &(trust_types::Ty, trust_types::Ty),
) -> Vec<StrengtheningProposal> {
    let (op_name, op_sym) = match op {
        BinOp::Add => ("addition", "+"),
        BinOp::Sub => ("subtraction", "-"),
        BinOp::Mul => ("multiplication", "*"),
        _ => ("operation", "?"),
    };

    let type_name = ty_to_rust_name(&operand_tys.0);
    let max_expr = format!("{type_name}::MAX");

    // Build the spec body based on operator
    let spec_body = match op {
        BinOp::Add => format!("a <= {max_expr} - b"),
        BinOp::Sub => "a >= b".to_string(),
        BinOp::Mul => format!("a == 0 || b <= {max_expr} / a"),
        _ => format!("{op_name} does not overflow"),
    };

    let checked_method = match op {
        BinOp::Add => "checked_add",
        BinOp::Sub => "checked_sub",
        BinOp::Mul => "checked_mul",
        _ => {
            return vec![make_proposal(
                target,
                "// Unsupported arithmetic operation: inspect and add a native requires clause",
                0.2,
                &format!("ArithmeticOverflow::{op_name}"),
                &format!("Arithmetic {op_name} can overflow"),
            )];
        }
    };

    vec![
        make_proposal(
            target,
            &format!("requires {spec_body}"),
            0.85,
            &format!("ArithmeticOverflow::{op_name}"),
            &format!(
                "Arithmetic {op_name} on {type_name} can overflow -- add precondition bounding operands"
            ),
        ),
        make_proposal(
            target,
            &format!("// Use a.{checked_method}(b) instead of a {op_sym} b"),
            0.75,
            &format!("ArithmeticOverflow::{op_name}"),
            &format!("Replace raw {op_name} with {checked_method}() for safe arithmetic"),
        ),
    ]
}

fn infer_division_by_zero(target: &InsertionTarget) -> Vec<StrengtheningProposal> {
    vec![
        make_proposal(
            target,
            "requires divisor != 0",
            0.95,
            "DivisionByZero",
            "Division by zero possible -- require divisor != 0",
        ),
        make_proposal(
            target,
            "// Add: assert!(divisor != 0, \"division by zero\")",
            0.80,
            "DivisionByZero",
            "Add runtime non-zero check before division",
        ),
    ]
}

fn infer_index_out_of_bounds(target: &InsertionTarget) -> Vec<StrengtheningProposal> {
    vec![
        make_proposal(
            target,
            "requires index < slice.len()",
            0.90,
            "IndexOutOfBounds",
            "Index out of bounds possible -- require index < slice.len()",
        ),
        make_proposal(
            target,
            "// Add: assert!(index < slice.len(), \"index out of bounds\")",
            0.80,
            "IndexOutOfBounds",
            "Add explicit bounds check before indexing",
        ),
    ]
}

fn infer_negation_overflow(
    target: &InsertionTarget,
    ty: &trust_types::Ty,
) -> Vec<StrengtheningProposal> {
    let type_name = ty_to_rust_name(ty);
    vec![
        make_proposal(
            target,
            &format!("requires x != {type_name}::MIN"),
            0.90,
            "NegationOverflow",
            &format!("Negation of {type_name}::MIN overflows -- require x != MIN"),
        ),
        make_proposal(
            target,
            "// Use x.checked_neg() instead of -x",
            0.80,
            "NegationOverflow",
            "Replace unary negation with checked_neg() for safety",
        ),
    ]
}

fn infer_cast_overflow(
    target: &InsertionTarget,
    from_ty: &trust_types::Ty,
    to_ty: &trust_types::Ty,
) -> Vec<StrengtheningProposal> {
    let from_name = ty_to_rust_name(from_ty);
    let to_name = ty_to_rust_name(to_ty);
    vec![
        make_proposal(
            target,
            &format!("requires value <= {to_name}::MAX as {from_name}"),
            0.85,
            "CastOverflow",
            &format!("Cast from {from_name} to {to_name} may overflow -- add range check"),
        ),
        make_proposal(
            target,
            &format!("// Use {to_name}::try_from(value) instead of value as {to_name}"),
            0.70,
            "CastOverflow",
            &format!("Replace `as {to_name}` with TryFrom for safe conversion"),
        ),
    ]
}

fn infer_shift_overflow(
    target: &InsertionTarget,
    operand_ty: &trust_types::Ty,
) -> Vec<StrengtheningProposal> {
    let bit_width = match operand_ty {
        trust_types::Ty::Int { width, .. } => *width,
        _ => 64,
    };
    vec![
        make_proposal(
            target,
            &format!("requires shift < {bit_width}"),
            0.90,
            "ShiftOverflow",
            &format!("Shift amount must be less than bit width ({bit_width})"),
        ),
        make_proposal(
            target,
            "// Use value.checked_shl(shift) instead of value << shift",
            0.75,
            "ShiftOverflow",
            "Replace raw shift with checked_shl() for safe shifting",
        ),
    ]
}

fn infer_assertion_failure(target: &InsertionTarget, message: &str) -> Vec<StrengtheningProposal> {
    vec![make_proposal(
        target,
        "// Inspect the failing assertion and propose a typed native clause",
        0.20,
        "Assertion",
        &format!("Assertion `{message}` can fail; diagnostic prose is not a contract expression"),
    )]
}

fn infer_precondition_violation(
    target: &InsertionTarget,
    callee: &str,
) -> Vec<StrengtheningProposal> {
    vec![make_proposal(
        target,
        &format!("// Propagate `{callee}`'s exact typed requires clause to this caller"),
        0.30,
        "Precondition",
        &format!(
            "Call to {callee} violates its precondition; no predicate is invented without the callee summary"
        ),
    )]
}

fn infer_postcondition_violation(target: &InsertionTarget) -> Vec<StrengtheningProposal> {
    vec![make_proposal(
        target,
        "// Strengthen the implementation or revise the exact native ensures clause",
        0.20,
        "Postcondition",
        "Postcondition not established; refusing to fabricate a predicate from prose",
    )]
}

fn infer_unreachable(target: &InsertionTarget) -> Vec<StrengtheningProposal> {
    vec![make_proposal(
        target,
        "// Add a typed native requires clause covering the handled variants",
        0.20,
        "Unreachable",
        "Unreachable code reached -- add precondition for exhaustiveness",
    )]
}

// ---------------------------------------------------------------------------
// Null-pointer / Option unwrap inference (requested in issue)
// ---------------------------------------------------------------------------

/// Infer specs for potential null-pointer dereferences.
///
/// In Rust, null pointers manifest as `Option::None` unwraps or raw pointer derefs.
/// This generates `is_some()` / `is_not_null()` preconditions.
///
/// Called externally when analysis detects an Option unwrap or raw pointer deref
/// pattern, since there is no dedicated `NullPointerDeref` VcKind.
#[must_use]
pub fn infer_null_deref(
    function_path: &str,
    function_name: &str,
    param_name: &str,
    is_raw_pointer: bool,
) -> Vec<StrengtheningProposal> {
    let target = InsertionTarget {
        function_path: function_path.to_string(),
        function_name: function_name.to_string(),
        file: None,
        line: None,
    };

    if is_raw_pointer {
        vec![
            make_proposal(
                &target,
                &format!("requires !{param_name}.is_null()"),
                0.90,
                "NullPointerDeref",
                &format!("Raw pointer `{param_name}` may be null -- require is_not_null()"),
            ),
            make_proposal(
                &target,
                &format!("// Add: assert!(!{param_name}.is_null(), \"null pointer\")"),
                0.80,
                "NullPointerDeref",
                &format!("Add runtime null check before dereferencing `{param_name}`"),
            ),
        ]
    } else {
        vec![
            make_proposal(
                &target,
                &format!("requires {param_name}.is_some()"),
                0.90,
                "NullPointerDeref",
                &format!("Option `{param_name}` may be None -- require is_some() precondition"),
            ),
            make_proposal(
                &target,
                &format!("// Use {param_name}.unwrap_or_default() or match instead of unwrap()"),
                0.75,
                "NullPointerDeref",
                &format!("Replace `{param_name}.unwrap()` with safe alternative"),
            ),
        ]
    }
}

// ---------------------------------------------------------------------------
// Binary search precondition inference
// ---------------------------------------------------------------------------

/// Infer specifications for binary search functions.
///
/// Given a function recognized as a binary search (by name or pattern), this
/// generates the key Level 1 (functional correctness) specifications:
///
/// - `requires slice.is_sorted()` -- the sorted precondition
/// - `requires !slice.is_empty()` -- non-empty precondition
/// - `ensures result.is_some() ==> slice[result.unwrap()] == target` -- correctness postcondition
///
/// The `slice_param` and `target_param` names are used in the generated specs.
/// If not known, pass `"slice"` and `"target"` as defaults.
///
/// These appear in the proof report as "inferred specifications" at Level 1
/// (functional correctness), complementing the Level 0 (safety) overflow
/// detection from vcgen.
#[must_use]
pub fn infer_binary_search_specs(
    function_path: &str,
    function_name: &str,
    slice_param: &str,
    target_param: &str,
) -> Vec<StrengtheningProposal> {
    let target = InsertionTarget {
        function_path: function_path.to_string(),
        function_name: function_name.to_string(),
        file: None,
        line: None,
    };

    vec![
        // Primary: is_sorted precondition (the key M4 requirement)
        make_proposal(
            &target,
            &format!("requires {slice_param}.is_sorted()"),
            0.95,
            "BinarySearchPrecondition",
            &format!(
                "Binary search requires `{slice_param}` to be sorted in ascending order -- \
                 without this precondition, the algorithm may return incorrect results"
            ),
        ),
        // Non-empty precondition
        make_proposal(
            &target,
            &format!("requires !{slice_param}.is_empty()"),
            0.90,
            "BinarySearchPrecondition",
            &format!("Binary search requires `{slice_param}` to be non-empty"),
        ),
        // Correctness postcondition: found element matches target
        make_proposal(
            &target,
            &format!(
                "ensures result.is_some() ==> {slice_param}[result.unwrap()] == {target_param}"
            ),
            0.90,
            "BinarySearchPostcondition",
            &format!("If binary search returns Some(i), then `{slice_param}[i] == {target_param}`"),
        ),
        // Completeness postcondition: not found means absent
        make_proposal(
            &target,
            &format!(
                "ensures result.is_none() ==> forall i: usize, i < {slice_param}.len() \
                 ==> {slice_param}[i] != {target_param}"
            ),
            0.85,
            "BinarySearchPostcondition",
            &format!(
                "If binary search returns None, then `{target_param}` is not in `{slice_param}`"
            ),
        ),
    ]
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn make_proposal(
    target: &InsertionTarget,
    spec_text: &str,
    confidence: f64,
    vc_kind_name: &str,
    rationale: &str,
) -> StrengtheningProposal {
    StrengtheningProposal {
        spec_text: spec_text.to_string(),
        target: target.clone(),
        confidence,
        vc_kind_name: vc_kind_name.to_string(),
        rationale: rationale.to_string(),
    }
}

fn short_name(path: &str) -> String {
    path.rsplit("::").next().unwrap_or(path).to_string()
}

fn ty_to_rust_name(ty: &trust_types::Ty) -> String {
    match ty {
        trust_types::Ty::Int { width, signed } => {
            let prefix = if *signed { "i" } else { "u" };
            // width == 0 means pointer-width (usize/isize)
            if *width == 0 { format!("{prefix}size") } else { format!("{prefix}{width}") }
        }
        trust_types::Ty::Float { width } => format!("f{width}"),
        trust_types::Ty::Bool => "bool".to_string(),
        trust_types::Ty::Unit => "()".to_string(),
        _ => "T".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use trust_types::{Formula, SourceSpan, Ty};

    use super::*;

    fn make_vc(kind: VcKind, function: &str) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: function.into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        }
    }

    fn make_vc_with_location(
        kind: VcKind,
        function: &str,
        file: &str,
        line: u32,
    ) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: function.into(),
            location: SourceSpan {
                file: file.into(),
                line_start: line,
                col_start: 1,
                line_end: line,
                col_end: 1,
            },
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        }
    }

    // --- ArithmeticOverflow ---

    #[test]
    fn test_overflow_add_proposals() {
        let vc = make_vc(
            VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (
                    Ty::Int { width: 64, signed: false },
                    Ty::Int { width: 64, signed: false },
                ),
            },
            "crate::math::get_midpoint",
        );

        let proposals = infer_specs(&vc);
        assert_eq!(proposals.len(), 2);

        // First proposal: precondition
        assert!(proposals[0].spec_text.starts_with("requires "));
        assert!(proposals[0].spec_text.contains("u64::MAX"));
        assert_eq!(proposals[0].confidence, 0.85);
        assert_eq!(proposals[0].target.function_name, "get_midpoint");

        // Second proposal: checked_add suggestion
        assert!(proposals[1].spec_text.contains("checked_add"));
        assert_eq!(proposals[1].confidence, 0.75);
    }

    #[test]
    fn test_overflow_sub_proposals() {
        let vc = make_vc(
            VcKind::ArithmeticOverflow {
                op: BinOp::Sub,
                operand_tys: (
                    Ty::Int { width: 32, signed: true },
                    Ty::Int { width: 32, signed: true },
                ),
            },
            "math::subtract",
        );

        let proposals = infer_specs(&vc);
        assert_eq!(proposals.len(), 2);
        assert!(proposals[0].spec_text.contains("a >= b"));
    }

    #[test]
    fn test_overflow_mul_proposals() {
        let vc = make_vc(
            VcKind::ArithmeticOverflow {
                op: BinOp::Mul,
                operand_tys: (
                    Ty::Int { width: 64, signed: false },
                    Ty::Int { width: 64, signed: false },
                ),
            },
            "math::multiply",
        );

        let proposals = infer_specs(&vc);
        assert_eq!(proposals.len(), 2);
        assert!(proposals[0].spec_text.contains("u64::MAX / a"));
        assert!(proposals[1].spec_text.contains("checked_mul"));
    }

    // --- DivisionByZero ---

    #[test]
    fn test_div_zero_proposals() {
        let vc = make_vc(VcKind::DivisionByZero, "math::safe_divide");

        let proposals = infer_specs(&vc);
        assert_eq!(proposals.len(), 2);
        assert_eq!(proposals[0].spec_text, "requires divisor != 0");
        assert_eq!(proposals[0].confidence, 0.95);
        assert!(proposals[1].spec_text.contains("assert!(divisor != 0"));
        assert_eq!(proposals[1].confidence, 0.80);
    }

    #[test]
    fn test_remainder_by_zero_same_as_div() {
        let vc = make_vc(VcKind::RemainderByZero, "math::modulo");

        let proposals = infer_specs(&vc);
        assert_eq!(proposals.len(), 2);
        assert!(proposals[0].spec_text.contains("divisor != 0"));
    }

    // --- IndexOutOfBounds ---

    #[test]
    fn test_index_oob_proposals() {
        let vc = make_vc(VcKind::IndexOutOfBounds, "collection::get_element");

        let proposals = infer_specs(&vc);
        assert_eq!(proposals.len(), 2);
        assert_eq!(proposals[0].spec_text, "requires index < slice.len()");
        assert_eq!(proposals[0].confidence, 0.90);
        assert!(proposals[1].spec_text.contains("assert!(index < slice.len()"));
    }

    #[test]
    fn test_slice_bounds_check_same_as_oob() {
        let vc = make_vc(VcKind::SliceBoundsCheck, "collection::slice_range");

        let proposals = infer_specs(&vc);
        assert_eq!(proposals.len(), 2);
        assert!(proposals[0].spec_text.contains("index < slice.len()"));
    }

    // --- NullPointerDeref (via infer_null_deref) ---

    #[test]
    fn test_null_deref_option_proposals() {
        let proposals = infer_null_deref("crate::process", "process", "config", false);

        assert_eq!(proposals.len(), 2);
        assert_eq!(proposals[0].spec_text, "requires config.is_some()");
        assert_eq!(proposals[0].confidence, 0.90);
        assert!(proposals[1].spec_text.contains("unwrap_or_default"));
        assert_eq!(proposals[1].confidence, 0.75);
        assert_eq!(proposals[0].target.function_name, "process");
    }

    #[test]
    fn test_null_deref_raw_pointer_proposals() {
        let proposals = infer_null_deref("crate::ffi::call", "call", "ptr", true);

        assert_eq!(proposals.len(), 2);
        assert_eq!(proposals[0].spec_text, "requires !ptr.is_null()");
        assert_eq!(proposals[0].confidence, 0.90);
        assert!(proposals[1].spec_text.contains("assert!(!ptr.is_null()"));
        assert_eq!(proposals[1].confidence, 0.80);
    }

    // --- Other VcKinds ---

    #[test]
    fn test_negation_overflow_proposals() {
        let vc = make_vc(
            VcKind::NegationOverflow { ty: Ty::Int { width: 64, signed: true } },
            "math::negate",
        );

        let proposals = infer_specs(&vc);
        assert_eq!(proposals.len(), 2);
        assert!(proposals[0].spec_text.contains("i64::MIN"));
        assert!(proposals[1].spec_text.contains("checked_neg"));
    }

    #[test]
    fn test_cast_overflow_proposals() {
        let vc = make_vc(
            VcKind::CastOverflow {
                from_ty: Ty::Int { width: 64, signed: false },
                to_ty: Ty::Int { width: 32, signed: false },
            },
            "convert::narrow",
        );

        let proposals = infer_specs(&vc);
        assert_eq!(proposals.len(), 2);
        assert!(proposals[0].spec_text.contains("u32::MAX"));
        assert!(proposals[0].spec_text.contains("u64"));
        assert!(proposals[1].spec_text.contains("try_from"));
    }

    #[test]
    fn test_shift_overflow_proposals() {
        let vc = make_vc(
            VcKind::ShiftOverflow {
                op: BinOp::Shl,
                operand_ty: Ty::Int { width: 32, signed: false },
                shift_ty: Ty::Int { width: 32, signed: false },
            },
            "bits::shift_left",
        );

        let proposals = infer_specs(&vc);
        assert_eq!(proposals.len(), 2);
        assert!(proposals[0].spec_text.contains("shift < 32"));
        assert!(proposals[1].spec_text.contains("checked_shl"));
    }

    #[test]
    fn test_assertion_failure_proposals() {
        let vc = make_vc(VcKind::Assertion { message: "x > 0".into() }, "validate::check_positive");

        let proposals = infer_specs(&vc);
        assert_eq!(proposals.len(), 1);
        assert!(proposals[0].spec_text.starts_with("//"));
        assert_eq!(proposals[0].confidence, 0.20);
    }

    #[test]
    fn test_precondition_violation_proposals() {
        let vc = make_vc(VcKind::Precondition { callee: "safe_divide".into() }, "compute::process");

        let proposals = infer_specs(&vc);
        assert_eq!(proposals.len(), 1);
        assert!(proposals[0].spec_text.contains("safe_divide"));
        assert_eq!(proposals[0].confidence, 0.30);
    }

    #[test]
    fn test_postcondition_violation_proposals() {
        let vc = make_vc(VcKind::Postcondition, "builder::build_result");

        let proposals = infer_specs(&vc);
        assert_eq!(proposals.len(), 1);
        assert!(proposals[0].spec_text.starts_with("//"));
        assert_eq!(proposals[0].confidence, 0.20);
    }

    #[test]
    fn test_unreachable_proposals() {
        let vc = make_vc(VcKind::Unreachable, "match_handler::dispatch");

        let proposals = infer_specs(&vc);
        assert_eq!(proposals.len(), 1);
        assert!(proposals[0].spec_text.contains("handled variants"));
    }

    #[test]
    fn test_unhandled_vc_kind_produces_nothing() {
        let vc = make_vc(VcKind::Deadlock, "service::event_loop");

        let proposals = infer_specs(&vc);
        assert!(
            proposals.is_empty(),
            "a VcKind with no specialized generator must yield nothing to rank, got {proposals:?}"
        );
    }

    // --- Target extraction ---

    #[test]
    fn test_target_extracts_function_name() {
        let vc = make_vc(VcKind::DivisionByZero, "crate::module::submod::my_func");

        let proposals = infer_specs(&vc);
        assert_eq!(proposals[0].target.function_name, "my_func");
        assert_eq!(proposals[0].target.function_path, "crate::module::submod::my_func");
    }

    #[test]
    fn test_target_includes_location_when_available() {
        let vc = make_vc_with_location(VcKind::DivisionByZero, "math::divide", "src/math.rs", 42);

        let proposals = infer_specs(&vc);
        assert_eq!(proposals[0].target.file, Some("src/math.rs".into()));
        assert_eq!(proposals[0].target.line, Some(42));
    }

    #[test]
    fn test_target_omits_location_when_default() {
        let vc = make_vc(VcKind::DivisionByZero, "math::divide");

        let proposals = infer_specs(&vc);
        assert_eq!(proposals[0].target.file, None);
        assert_eq!(proposals[0].target.line, None);
    }

    // --- Confidence ordering ---

    #[test]
    fn test_proposals_sorted_by_confidence_descending() {
        let vc = make_vc(VcKind::Postcondition, "f");

        let proposals = infer_specs(&vc);
        for window in proposals.windows(2) {
            assert!(
                window[0].confidence >= window[1].confidence,
                "proposals must be sorted by confidence: {} >= {}",
                window[0].confidence,
                window[1].confidence
            );
        }
    }

    // --- All proposals have valid confidence ---

    #[test]
    fn test_all_proposals_have_valid_confidence() {
        let vc_kinds = vec![
            VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (
                    Ty::Int { width: 64, signed: false },
                    Ty::Int { width: 64, signed: false },
                ),
            },
            VcKind::DivisionByZero,
            VcKind::RemainderByZero,
            VcKind::IndexOutOfBounds,
            VcKind::SliceBoundsCheck,
            VcKind::NegationOverflow { ty: Ty::Int { width: 64, signed: true } },
            VcKind::CastOverflow {
                from_ty: Ty::Int { width: 64, signed: false },
                to_ty: Ty::Int { width: 32, signed: false },
            },
            VcKind::ShiftOverflow {
                op: BinOp::Shl,
                operand_ty: Ty::Int { width: 64, signed: false },
                shift_ty: Ty::Int { width: 64, signed: false },
            },
            VcKind::Assertion { message: "x > 0".into() },
            VcKind::Precondition { callee: "f".into() },
            VcKind::Postcondition,
            VcKind::Unreachable,
        ];

        for kind in &vc_kinds {
            let vc = make_vc(kind.clone(), "test::f");
            let proposals = infer_specs(&vc);
            assert!(
                !proposals.is_empty(),
                "VcKind {:?} should produce at least one proposal",
                kind
            );
            for p in &proposals {
                assert!(
                    (0.0..=1.0).contains(&p.confidence),
                    "VcKind {:?} proposal has invalid confidence {}: {}",
                    kind,
                    p.confidence,
                    p.spec_text
                );
            }
        }
    }

    // --- Null deref edge cases ---

    #[test]
    fn test_null_deref_preserves_param_name() {
        let proposals = infer_null_deref("mod::f", "f", "my_option", false);
        assert!(proposals[0].spec_text.contains("my_option.is_some()"));
    }

    #[test]
    fn test_null_deref_raw_pointer_preserves_param_name() {
        let proposals = infer_null_deref("mod::f", "f", "data_ptr", true);
        assert!(proposals[0].spec_text.contains("!data_ptr.is_null()"));
    }

    // --- ty_to_rust_name ---

    #[test]
    fn test_ty_to_rust_name_unsigned() {
        assert_eq!(ty_to_rust_name(&Ty::Int { width: 8, signed: false }), "u8");
        assert_eq!(ty_to_rust_name(&Ty::Int { width: 64, signed: false }), "u64");
        assert_eq!(ty_to_rust_name(&Ty::Int { width: 128, signed: false }), "u128");
    }

    #[test]
    fn test_ty_to_rust_name_signed() {
        assert_eq!(ty_to_rust_name(&Ty::Int { width: 32, signed: true }), "i32");
        assert_eq!(ty_to_rust_name(&Ty::Int { width: 64, signed: true }), "i64");
    }

    #[test]
    fn test_ty_to_rust_name_pointer_width() {
        assert_eq!(ty_to_rust_name(&Ty::Int { width: 0, signed: false }), "usize");
        assert_eq!(ty_to_rust_name(&Ty::Int { width: 0, signed: true }), "isize");
    }

    #[test]
    fn test_ty_to_rust_name_float() {
        assert_eq!(ty_to_rust_name(&Ty::Float { width: 32 }), "f32");
        assert_eq!(ty_to_rust_name(&Ty::Float { width: 64 }), "f64");
    }

    #[test]
    fn test_ty_to_rust_name_other() {
        assert_eq!(ty_to_rust_name(&Ty::Bool), "bool");
        assert_eq!(ty_to_rust_name(&Ty::Unit), "()");
    }

    // --- short_name ---

    #[test]
    fn test_short_name_extracts_last_segment() {
        assert_eq!(short_name("crate::module::func"), "func");
        assert_eq!(short_name("func"), "func");
        assert_eq!(short_name("a::b::c::d"), "d");
    }

    // --- infer_specs_with_cex integration tests ---

    #[test]
    fn test_infer_specs_with_cex_div_zero() {
        use trust_types::CounterexampleValue;

        let vc = make_vc(VcKind::DivisionByZero, "math::divide");
        let cex = Counterexample::new(vec![
            ("x".into(), CounterexampleValue::Int(42)),
            ("y".into(), CounterexampleValue::Int(0)),
        ]);

        let proposals = infer_specs_with_cex(&vc, &cex);
        assert!(!proposals.is_empty());

        let top = &proposals[0];
        assert!(
            top.spec_text.contains("y != 0"),
            "should name the concrete variable: {}",
            top.spec_text
        );
        assert!(top.confidence >= 0.95);
    }

    #[test]
    fn test_infer_specs_with_cex_overflow() {
        use trust_types::CounterexampleValue;

        let vc = make_vc(
            VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (
                    Ty::Int { width: 64, signed: false },
                    Ty::Int { width: 64, signed: false },
                ),
            },
            "math::midpoint",
        );
        let cex = Counterexample::new(vec![
            ("a".into(), CounterexampleValue::Uint(u64::MAX as u128)),
            ("b".into(), CounterexampleValue::Uint(1)),
        ]);

        let proposals = infer_specs_with_cex(&vc, &cex);
        assert!(!proposals.is_empty());

        let top = &proposals[0];
        assert!(top.confidence >= 0.90);
        assert!(top.spec_text.contains("a") && top.spec_text.contains("MAX"));
    }

    #[test]
    fn test_infer_specs_with_cex_oob() {
        use trust_types::CounterexampleValue;

        let vc = make_vc(VcKind::IndexOutOfBounds, "coll::get");
        let cex = Counterexample::new(vec![
            ("index".into(), CounterexampleValue::Uint(10)),
            ("len".into(), CounterexampleValue::Uint(5)),
        ]);

        let proposals = infer_specs_with_cex(&vc, &cex);
        assert!(!proposals.is_empty());

        let top = &proposals[0];
        assert!(top.spec_text.contains("index < len"));
        assert!(top.confidence >= 0.95);
    }

    #[test]
    fn test_infer_specs_with_cex_higher_confidence_than_heuristic() {
        use trust_types::CounterexampleValue;

        let vc = make_vc(VcKind::DivisionByZero, "f");
        let cex = Counterexample::new(vec![("d".into(), CounterexampleValue::Int(0))]);

        let cex_proposals = infer_specs_with_cex(&vc, &cex);
        let heuristic_proposals = infer_specs(&vc);

        assert!(
            cex_proposals[0].confidence >= heuristic_proposals[0].confidence,
            "cex-guided ({}) should be >= heuristic ({})",
            cex_proposals[0].confidence,
            heuristic_proposals[0].confidence,
        );
    }
}
