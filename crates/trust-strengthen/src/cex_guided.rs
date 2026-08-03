// trust-strengthen/cex_guided.rs: Counterexample-guided spec refinement
//
// When ay returns a SAT model (counterexample), this module uses the concrete
// variable assignments to produce tighter, more targeted StrengtheningProposals
// than pure heuristic inference. The CounterexampleAnalyzer bridges the
// counterexample hint extraction (counterexample.rs) with spec proposal
// generation (spec_inference.rs).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use trust_types::{BinOp, Counterexample, CounterexampleValue, Ty, VcKind, VerificationCondition};

use crate::analyzer::FailurePattern;
use crate::counterexample::{self, CounterexampleHint, HintKind};
use crate::spec_inference::{InsertionTarget, StrengtheningProposal};

/// Concrete values from a solver counterexample, keyed by variable name.
///
/// This is a higher-level abstraction over `Counterexample` that normalizes
/// the value representation for analysis.
#[derive(Debug, Clone)]
pub struct CexModel {
    /// Variable name -> concrete value.
    pub values: BTreeMap<String, CexValue>,
}

/// A normalized concrete value from a counterexample.
#[derive(Debug, Clone, PartialEq)]
pub enum CexValue {
    Integer(i128),
    Unsigned(u128),
    Boolean(bool),
    Float(f64),
}

impl CexModel {
    /// Build a `CexModel` from a trust-types `Counterexample`.
    #[must_use]
    pub fn from_counterexample(cex: &Counterexample) -> Self {
        let values = cex
            .assignments
            .iter()
            .map(|(name, val)| {
                let v = match val {
                    CounterexampleValue::Int(i) => CexValue::Integer(*i),
                    CounterexampleValue::Uint(u) => CexValue::Unsigned(*u),
                    CounterexampleValue::Bool(b) => CexValue::Boolean(*b),
                    CounterexampleValue::Float(f) => CexValue::Float(*f),
                    _ => CexValue::Integer(0),
                };
                (name.clone(), v)
            })
            .collect();
        CexModel { values }
    }

    /// Build a `CexModel` from raw (name, value) pairs for testing.
    #[must_use]
    pub fn from_pairs(pairs: Vec<(String, CexValue)>) -> Self {
        CexModel { values: pairs.into_iter().collect() }
    }

    /// Convert back to trust-types `Counterexample` for use with hint extraction.
    #[must_use]
    pub fn to_counterexample(&self) -> Counterexample {
        let assignments = sorted_cex_values(&self.values)
            .into_iter()
            .map(|(name, val)| {
                let cv = match val {
                    CexValue::Integer(i) => CounterexampleValue::Int(*i),
                    CexValue::Unsigned(u) => CounterexampleValue::Uint(*u),
                    CexValue::Boolean(b) => CounterexampleValue::Bool(*b),
                    CexValue::Float(f) => CounterexampleValue::Float(*f),
                };
                (name.clone(), cv)
            })
            .collect();
        Counterexample::new(assignments)
    }
}

/// Analyzes counterexamples to produce refined strengthening proposals.
///
/// When a VC fails with a concrete counterexample from ay, the analyzer:
/// 1. Classifies the VC kind into a failure pattern
/// 2. Extracts counterexample hints (variable bounds, non-zero constraints)
/// 3. Uses the concrete values to produce tighter preconditions than heuristics
///
/// The resulting proposals have higher confidence than heuristic-only proposals
/// because they are grounded in concrete violating assignments.
pub struct CounterexampleAnalyzer;

impl CounterexampleAnalyzer {
    /// Refine a failing VC using a concrete counterexample model.
    ///
    /// Returns proposals sorted by confidence (highest first). When the
    /// counterexample provides useful information, proposals will have a
    /// confidence boost over their heuristic-only equivalents.
    #[must_use]
    pub fn refine(vc: &VerificationCondition, cex_model: &CexModel) -> Vec<StrengtheningProposal> {
        let target = build_target(vc);
        let pattern = classify_vc_kind(&vc.kind);
        let cex = cex_model.to_counterexample();

        // Extract hints using the existing counterexample hint system
        let hints = counterexample::extract_hints(&cex, &pattern, &vc.kind);

        // Produce refined proposals based on VcKind + concrete hints
        let mut proposals = match &vc.kind {
            VcKind::ArithmeticOverflow { op, operand_tys } => {
                refine_arithmetic_overflow(&target, op, operand_tys, &hints, cex_model)
            }
            VcKind::DivisionByZero | VcKind::RemainderByZero => {
                refine_division_by_zero(&target, &hints, cex_model)
            }
            VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => {
                refine_index_out_of_bounds(&target, &hints, cex_model)
            }
            VcKind::NegationOverflow { ty } => {
                refine_negation_overflow(&target, ty, &hints, cex_model)
            }
            VcKind::CastOverflow { from_ty, to_ty } => {
                refine_cast_overflow(&target, from_ty, to_ty, &hints)
            }
            VcKind::ShiftOverflow { operand_ty, shift_ty: _, op: _ } => {
                refine_shift_overflow(&target, operand_ty, &hints)
            }
            _ => {
                // For other VcKinds, fall back to hint-derived proposals
                refine_from_hints_generic(&target, &vc.kind, &hints)
            }
        };

        // Sort by confidence descending
        proposals.sort_by(compare_strengthening_proposals);

        proposals
    }
}

// ---------------------------------------------------------------------------
// Per-VcKind refinement
// ---------------------------------------------------------------------------

fn refine_arithmetic_overflow(
    target: &InsertionTarget,
    op: &BinOp,
    operand_tys: &(Ty, Ty),
    hints: &[CounterexampleHint],
    cex_model: &CexModel,
) -> Vec<StrengtheningProposal> {
    let mut proposals = Vec::new();
    let type_name = ty_to_rust_name(&operand_tys.0);

    // Check if any variable in the cex is at the type's MAX boundary
    let (bit_width, is_signed) = extract_type_info(&operand_tys.0);
    let max_val = compute_max(bit_width, is_signed);

    let at_max_vars: Vec<&String> = sorted_cex_values(&cex_model.values)
        .into_iter()
        .filter(|(_, v)| is_at_max(v, max_val, bit_width))
        .map(|(name, _)| name)
        .collect();

    if !at_max_vars.is_empty() {
        // Concrete evidence: variable is at MAX, propose x < TYPE::MAX
        let var = &at_max_vars[0];
        let (op_name, _) = op_info(op);
        proposals.push(make_cex_proposal(
            target,
            &format!("requires {var} < {type_name}::MAX"),
            0.95,
            &format!("ArithmeticOverflow::{op_name}"),
            &format!("Counterexample shows {var}={type_name}::MAX causing {op_name} overflow"),
        ));
    }

    // Use combined bound expression from hints if available
    for hint in hints {
        if let HintKind::BoundExpr { spec_fragment } = &hint.kind
            && spec_fragment.contains(" <= ")
            && spec_fragment.contains(" - ")
        {
            proposals.push(make_cex_proposal(
                target,
                &format!("requires {spec_fragment}"),
                0.92,
                &format!("ArithmeticOverflow::{}", op_info(op).0),
                &format!("Counterexample-derived bound: {spec_fragment}"),
            ));
        }
    }

    // Suggest checked arithmetic (always applicable)
    let checked = match op {
        BinOp::Add => Some("checked_add"),
        BinOp::Sub => Some("checked_sub"),
        BinOp::Mul => Some("checked_mul"),
        _ => None,
    };
    if let Some(method) = checked {
        let sym = op_info(op).1;
        proposals.push(make_cex_proposal(
            target,
            &format!("// Use a.{method}(b) instead of a {sym} b"),
            0.80,
            &format!("ArithmeticOverflow::{}", op_info(op).0),
            &format!("Replace raw {sym} with {method}() for safe arithmetic"),
        ));
    }

    proposals
}

fn refine_division_by_zero(
    target: &InsertionTarget,
    hints: &[CounterexampleHint],
    cex_model: &CexModel,
) -> Vec<StrengtheningProposal> {
    let mut proposals = Vec::new();

    // Find the zero-valued variable from the cex
    let zero_var = sorted_cex_values(&cex_model.values)
        .into_iter()
        .find(|(_, v)| matches!(v, CexValue::Integer(0) | CexValue::Unsigned(0)));

    if let Some((var_name, _)) = zero_var {
        // Concrete evidence: variable is 0
        proposals.push(make_cex_proposal(
            target,
            &format!("requires {var_name} != 0"),
            0.98,
            "DivisionByZero",
            &format!("Counterexample shows {var_name}=0 causing division by zero"),
        ));
    } else {
        // Hints found zero but no named variable match; use generic
        let has_nonzero_hint = hints.iter().any(|h| matches!(h.kind, HintKind::NonZero));
        if has_nonzero_hint {
            let var = hints
                .iter()
                .find(|h| matches!(h.kind, HintKind::NonZero))
                .map(|h| h.variable.as_str())
                .unwrap_or("divisor");
            proposals.push(make_cex_proposal(
                target,
                &format!("requires {var} != 0"),
                0.96,
                "DivisionByZero",
                &format!("Counterexample hints confirm {var} can be zero"),
            ));
        } else {
            proposals.push(make_cex_proposal(
                target,
                "requires divisor != 0",
                0.95,
                "DivisionByZero",
                "Division by zero possible (no specific variable identified in cex)",
            ));
        }
    }

    // Runtime check suggestion
    proposals.push(make_cex_proposal(
        target,
        "// Add: assert!(divisor != 0, \"division by zero\")",
        0.80,
        "DivisionByZero",
        "Add runtime non-zero check before division",
    ));

    proposals
}

fn refine_index_out_of_bounds(
    target: &InsertionTarget,
    hints: &[CounterexampleHint],
    cex_model: &CexModel,
) -> Vec<StrengtheningProposal> {
    let mut proposals = Vec::new();

    // Look for index >= len pattern in the cex values
    let sorted_values = sorted_cex_values(&cex_model.values);
    let idx_var = sorted_values
        .iter()
        .copied()
        .find(|(name, _)| name.contains("index") || name.contains("idx") || name.as_str() == "i");
    let len_var = sorted_values
        .iter()
        .copied()
        .find(|(name, _)| name.contains("len") || name.contains("length") || name.contains("size"));

    if let (Some((idx_name, idx_val)), Some((len_name, len_val))) = (idx_var, len_var) {
        let idx_str = format_cex_value(idx_val);
        let len_str = format_cex_value(len_val);
        proposals.push(make_cex_proposal(
            target,
            &format!("requires {idx_name} < {len_name}"),
            0.97,
            "IndexOutOfBounds",
            &format!("Counterexample shows {idx_name}={idx_str} >= {len_name}={len_str}"),
        ));
    } else {
        // Use hints if available
        let lt_hint = hints.iter().find(|h| matches!(&h.kind, HintKind::LessThan { .. }));
        if let Some(h) = lt_hint {
            if let HintKind::LessThan { other } = &h.kind {
                proposals.push(make_cex_proposal(
                    target,
                    &format!("requires {} < {other}", h.variable),
                    0.95,
                    "IndexOutOfBounds",
                    &format!("Counterexample hints: {} must be less than {other}", h.variable),
                ));
            }
        } else {
            proposals.push(make_cex_proposal(
                target,
                "requires index < slice.len()",
                0.90,
                "IndexOutOfBounds",
                "Index out of bounds (specific variables not identified in cex)",
            ));
        }
    }

    // Bounds check suggestion
    proposals.push(make_cex_proposal(
        target,
        "// Add: assert!(index < slice.len(), \"index out of bounds\")",
        0.80,
        "IndexOutOfBounds",
        "Add explicit bounds check before indexing",
    ));

    proposals
}

fn refine_negation_overflow(
    target: &InsertionTarget,
    ty: &Ty,
    hints: &[CounterexampleHint],
    cex_model: &CexModel,
) -> Vec<StrengtheningProposal> {
    let mut proposals = Vec::new();
    let type_name = ty_to_rust_name(ty);

    // Find variable at MIN value
    let (bit_width, _) = extract_type_info(ty);
    let min_val = -(1i128 << (bit_width - 1));

    let at_min_var = sorted_cex_values(&cex_model.values)
        .into_iter()
        .find(|(_, v)| matches!(v, CexValue::Integer(i) if *i == min_val));

    if let Some((var_name, _)) = at_min_var {
        proposals.push(make_cex_proposal(
            target,
            &format!("requires {var_name} != {type_name}::MIN"),
            0.97,
            "NegationOverflow",
            &format!("Counterexample shows {var_name}={type_name}::MIN, negation overflows"),
        ));
    } else {
        // Use hints
        let ne_hint = hints.iter().find(|h| matches!(&h.kind, HintKind::NotEqual { .. }));
        if let Some(h) = ne_hint {
            proposals.push(make_cex_proposal(
                target,
                &format!("requires {} != {type_name}::MIN", h.variable),
                0.93,
                "NegationOverflow",
                &format!("Counterexample hints: {} must not equal {type_name}::MIN", h.variable),
            ));
        } else {
            proposals.push(make_cex_proposal(
                target,
                &format!("requires x != {type_name}::MIN"),
                0.90,
                "NegationOverflow",
                &format!("Negation of {type_name}::MIN overflows"),
            ));
        }
    }

    proposals.push(make_cex_proposal(
        target,
        "// Use x.checked_neg() instead of -x",
        0.80,
        "NegationOverflow",
        "Replace unary negation with checked_neg() for safety",
    ));

    proposals
}

fn refine_cast_overflow(
    target: &InsertionTarget,
    from_ty: &Ty,
    to_ty: &Ty,
    hints: &[CounterexampleHint],
) -> Vec<StrengtheningProposal> {
    let mut proposals = Vec::new();
    let from_name = ty_to_rust_name(from_ty);
    let to_name = ty_to_rust_name(to_ty);

    // Use hint upper bounds for concrete refinement
    let ub_hint = hints.iter().find(|h| matches!(&h.kind, HintKind::UpperBound { .. }));

    if let Some(h) = ub_hint {
        if let HintKind::UpperBound { bound } = &h.kind {
            proposals.push(make_cex_proposal(
                target,
                &format!("requires {} <= {bound}", h.variable),
                0.93,
                "CastOverflow",
                &format!(
                    "Counterexample shows {} exceeds {to_name} range (max {bound})",
                    h.variable
                ),
            ));
        }
    } else {
        proposals.push(make_cex_proposal(
            target,
            &format!("requires value <= {to_name}::MAX as {from_name}"),
            0.85,
            "CastOverflow",
            &format!("Cast from {from_name} to {to_name} may overflow"),
        ));
    }

    proposals.push(make_cex_proposal(
        target,
        &format!("// Use {to_name}::try_from(value) instead of value as {to_name}"),
        0.70,
        "CastOverflow",
        &format!("Replace `as {to_name}` with TryFrom for safe conversion"),
    ));

    proposals
}

fn refine_shift_overflow(
    target: &InsertionTarget,
    operand_ty: &Ty,
    hints: &[CounterexampleHint],
) -> Vec<StrengtheningProposal> {
    let mut proposals = Vec::new();
    let bit_width = extract_type_info(operand_ty).0;

    let ub_hint = hints.iter().find(|h| matches!(&h.kind, HintKind::UpperBound { .. }));

    if let Some(h) = ub_hint {
        proposals.push(make_cex_proposal(
            target,
            &format!("requires {} < {bit_width}", h.variable),
            0.95,
            "ShiftOverflow",
            &format!("Counterexample shows {} >= {bit_width}, shift overflows", h.variable),
        ));
    } else {
        proposals.push(make_cex_proposal(
            target,
            &format!("requires shift < {bit_width}"),
            0.90,
            "ShiftOverflow",
            &format!("Shift amount must be less than bit width ({bit_width})"),
        ));
    }

    proposals.push(make_cex_proposal(
        target,
        "// Use value.checked_shl(shift) instead of value << shift",
        0.75,
        "ShiftOverflow",
        "Replace raw shift with checked_shl() for safe shifting",
    ));

    proposals
}

fn refine_from_hints_generic(
    target: &InsertionTarget,
    vc_kind: &VcKind,
    hints: &[CounterexampleHint],
) -> Vec<StrengtheningProposal> {
    let preconditions = counterexample::hints_to_preconditions(hints);
    // No rule matched the counterexample: propose nothing. A proposal whose body
    // is a note-to-self ranks against real candidates and can be applied as a
    // comment that changes no obligation.
    if preconditions.is_empty() {
        return Vec::new();
    }

    preconditions
        .into_iter()
        .map(|prec| {
            make_cex_proposal(
                target,
                &format!("requires {prec}"),
                0.80,
                &format!("{vc_kind:?}"),
                &format!("Counterexample-derived precondition: {prec}"),
            )
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn build_target(vc: &VerificationCondition) -> InsertionTarget {
    InsertionTarget {
        function_path: vc.function.as_str().to_string(),
        function_name: short_name(vc.function.as_str()),
        file: if vc.location.file.is_empty() { None } else { Some(vc.location.file.clone()) },
        line: if vc.location.line_start == 0 { None } else { Some(vc.location.line_start) },
    }
}

fn make_cex_proposal(
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

fn ty_to_rust_name(ty: &Ty) -> String {
    match ty {
        Ty::Int { width, signed } => {
            let prefix = if *signed { "i" } else { "u" };
            if *width == 0 { format!("{prefix}size") } else { format!("{prefix}{width}") }
        }
        Ty::Float { width } => format!("f{width}"),
        Ty::Bool => "bool".to_string(),
        Ty::Unit => "()".to_string(),
        _ => "T".to_string(),
    }
}

fn extract_type_info(ty: &Ty) -> (u32, bool) {
    match ty {
        Ty::Int { width, signed } => (*width, *signed),
        _ => (64, false),
    }
}

fn compute_max(bit_width: u32, is_signed: bool) -> i128 {
    if is_signed {
        (1i128 << (bit_width - 1)) - 1
    } else if bit_width >= 128 {
        i128::MAX
    } else {
        (1i128 << bit_width) - 1
    }
}

fn is_at_max(val: &CexValue, max_val: i128, bit_width: u32) -> bool {
    match val {
        CexValue::Integer(i) => *i == max_val,
        CexValue::Unsigned(u) => {
            let u_i128 = *u as i128;
            u_i128 == max_val || (bit_width < 128 && *u == (1u128 << bit_width) - 1)
        }
        _ => false,
    }
}

fn op_info(op: &BinOp) -> (&'static str, &'static str) {
    match op {
        BinOp::Add => ("addition", "+"),
        BinOp::Sub => ("subtraction", "-"),
        BinOp::Mul => ("multiplication", "*"),
        _ => ("operation", "?"),
    }
}

fn classify_vc_kind(kind: &VcKind) -> FailurePattern {
    match kind {
        VcKind::ArithmeticOverflow { op, .. } => FailurePattern::ArithmeticOverflow { op: *op },
        VcKind::DivisionByZero | VcKind::RemainderByZero => FailurePattern::DivisionByZero,
        VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => FailurePattern::IndexOutOfBounds,
        VcKind::CastOverflow { .. } => FailurePattern::CastOverflow,
        VcKind::NegationOverflow { .. } => FailurePattern::NegationOverflow,
        VcKind::ShiftOverflow { .. } => FailurePattern::ShiftOverflow,
        _ => FailurePattern::Unknown,
    }
}

fn format_cex_value(val: &CexValue) -> String {
    match val {
        CexValue::Integer(i) => format!("{i}"),
        CexValue::Unsigned(u) => format!("{u}"),
        CexValue::Boolean(b) => format!("{b}"),
        CexValue::Float(f) => format!("{f}"),
    }
}

fn sorted_cex_values(values: &BTreeMap<String, CexValue>) -> Vec<(&String, &CexValue)> {
    values.iter().collect()
}

fn compare_strengthening_proposals(
    a: &StrengtheningProposal,
    b: &StrengtheningProposal,
) -> std::cmp::Ordering {
    b.confidence
        .partial_cmp(&a.confidence)
        .unwrap_or(std::cmp::Ordering::Equal)
        .then_with(|| a.vc_kind_name.cmp(&b.vc_kind_name))
        .then_with(|| a.spec_text.cmp(&b.spec_text))
        .then_with(|| a.target.function_path.cmp(&b.target.function_path))
        .then_with(|| a.target.function_name.cmp(&b.target.function_name))
        .then_with(|| a.rationale.cmp(&b.rationale))
}

#[cfg(test)]
mod tests {
    use trust_types::{Formula, SourceSpan};

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

    // --- ArithmeticOverflow tests ---

    #[test]
    fn test_overflow_add_x_at_max() {
        let vc = make_vc(
            VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (
                    Ty::Int { width: 64, signed: false },
                    Ty::Int { width: 64, signed: false },
                ),
            },
            "math::get_midpoint",
        );
        let cex = CexModel::from_pairs(vec![
            ("a".into(), CexValue::Unsigned(u64::MAX as u128)),
            ("b".into(), CexValue::Unsigned(1)),
        ]);

        let proposals = CounterexampleAnalyzer::refine(&vc, &cex);
        assert!(!proposals.is_empty());

        // Should have a high-confidence proposal mentioning a < u64::MAX
        let top = &proposals[0];
        assert!(
            top.confidence >= 0.90,
            "top proposal confidence should be >= 0.90, got {}",
            top.confidence
        );
        assert!(
            top.spec_text.contains("a") && top.spec_text.contains("MAX"),
            "should reference the variable at MAX: {}",
            top.spec_text
        );
        assert!(
            top.rationale.contains("Counterexample"),
            "rationale should mention counterexample"
        );
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
        let cex = CexModel::from_pairs(vec![
            ("x".into(), CexValue::Integer(i32::MIN as i128)),
            ("y".into(), CexValue::Integer(1)),
        ]);

        let proposals = CounterexampleAnalyzer::refine(&vc, &cex);
        assert!(!proposals.is_empty());
        // Should suggest checked_sub
        let has_checked = proposals.iter().any(|p| p.spec_text.contains("checked_sub"));
        assert!(has_checked, "should suggest checked_sub");
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
        let cex = CexModel::from_pairs(vec![
            ("a".into(), CexValue::Unsigned(u64::MAX as u128)),
            ("b".into(), CexValue::Unsigned(2)),
        ]);

        let proposals = CounterexampleAnalyzer::refine(&vc, &cex);
        assert!(!proposals.is_empty());
        let has_checked = proposals.iter().any(|p| p.spec_text.contains("checked_mul"));
        assert!(has_checked, "should suggest checked_mul");
    }

    // --- DivisionByZero tests ---

    #[test]
    fn test_div_zero_cex_shows_zero() {
        let vc = make_vc(VcKind::DivisionByZero, "math::safe_divide");
        let cex = CexModel::from_pairs(vec![
            ("x".into(), CexValue::Integer(42)),
            ("divisor".into(), CexValue::Integer(0)),
        ]);

        let proposals = CounterexampleAnalyzer::refine(&vc, &cex);
        assert!(!proposals.is_empty());

        let top = &proposals[0];
        assert!(
            top.confidence >= 0.95,
            "div-by-zero with concrete cex should be high confidence: {}",
            top.confidence
        );
        assert!(
            top.spec_text.contains("divisor != 0"),
            "should propose divisor != 0: {}",
            top.spec_text
        );
        assert!(
            top.rationale.contains("Counterexample") && top.rationale.contains("divisor=0"),
            "rationale should reference concrete value: {}",
            top.rationale
        );
    }

    #[test]
    fn test_div_zero_cex_uint_zero() {
        let vc = make_vc(VcKind::RemainderByZero, "math::modulo");
        let cex = CexModel::from_pairs(vec![
            ("n".into(), CexValue::Unsigned(100)),
            ("d".into(), CexValue::Unsigned(0)),
        ]);

        let proposals = CounterexampleAnalyzer::refine(&vc, &cex);
        let top = &proposals[0];
        assert!(top.spec_text.contains("d != 0"));
    }

    // --- IndexOutOfBounds tests ---

    #[test]
    fn test_oob_cex_idx_ge_len() {
        let vc = make_vc(VcKind::IndexOutOfBounds, "collection::get_element");
        let cex = CexModel::from_pairs(vec![
            ("index".into(), CexValue::Unsigned(10)),
            ("len".into(), CexValue::Unsigned(5)),
        ]);

        let proposals = CounterexampleAnalyzer::refine(&vc, &cex);
        assert!(!proposals.is_empty());

        let top = &proposals[0];
        assert!(
            top.confidence >= 0.95,
            "OOB with concrete idx/len should be high confidence: {}",
            top.confidence
        );
        assert!(
            top.spec_text.contains("index < len"),
            "should propose index < len: {}",
            top.spec_text
        );
        assert!(
            top.rationale.contains("index=10") && top.rationale.contains("len=5"),
            "rationale should reference concrete values: {}",
            top.rationale
        );
    }

    #[test]
    fn test_oob_cex_unnamed_vars() {
        let vc = make_vc(VcKind::SliceBoundsCheck, "collection::slice_range");
        let cex = CexModel::from_pairs(vec![("n".into(), CexValue::Unsigned(100))]);

        let proposals = CounterexampleAnalyzer::refine(&vc, &cex);
        assert!(!proposals.is_empty());
        // Should still produce a bounds-related proposal
        let has_bounds =
            proposals.iter().any(|p| p.spec_text.contains("< ") || p.spec_text.contains("len"));
        assert!(has_bounds, "should produce some bounds-related proposal");
    }

    // --- NegationOverflow tests ---

    #[test]
    fn test_negation_overflow_at_min() {
        let vc = make_vc(
            VcKind::NegationOverflow { ty: Ty::Int { width: 64, signed: true } },
            "math::negate",
        );
        let cex = CexModel::from_pairs(vec![("x".into(), CexValue::Integer(i64::MIN as i128))]);

        let proposals = CounterexampleAnalyzer::refine(&vc, &cex);
        assert!(!proposals.is_empty());

        let top = &proposals[0];
        assert!(top.confidence >= 0.95);
        assert!(
            top.spec_text.contains("x != i64::MIN"),
            "should propose x != i64::MIN: {}",
            top.spec_text
        );
    }

    // --- CastOverflow tests ---

    #[test]
    fn test_cast_overflow_u64_to_u32() {
        let vc = make_vc(
            VcKind::CastOverflow {
                from_ty: Ty::Int { width: 64, signed: false },
                to_ty: Ty::Int { width: 32, signed: false },
            },
            "convert::narrow",
        );
        let cex =
            CexModel::from_pairs(vec![("x".into(), CexValue::Unsigned(u32::MAX as u128 + 1))]);

        let proposals = CounterexampleAnalyzer::refine(&vc, &cex);
        assert!(!proposals.is_empty());

        let top = &proposals[0];
        assert!(
            top.spec_text.contains("<=") && top.spec_text.contains(&format!("{}", u32::MAX)),
            "should propose value <= u32::MAX: {}",
            top.spec_text
        );
    }

    // --- ShiftOverflow tests ---

    #[test]
    fn test_shift_overflow_large_shift() {
        let vc = make_vc(
            VcKind::ShiftOverflow {
                op: BinOp::Shl,
                operand_ty: Ty::Int { width: 32, signed: false },
                shift_ty: Ty::Int { width: 32, signed: false },
            },
            "bits::shift_left",
        );
        let cex = CexModel::from_pairs(vec![
            ("val".into(), CexValue::Unsigned(1)),
            ("shift".into(), CexValue::Unsigned(32)),
        ]);

        let proposals = CounterexampleAnalyzer::refine(&vc, &cex);
        assert!(!proposals.is_empty());

        let top = &proposals[0];
        assert!(
            top.spec_text.contains("shift < 32"),
            "should propose shift < 32: {}",
            top.spec_text
        );
    }

    // --- CexModel conversion tests ---

    #[test]
    fn test_cex_model_from_counterexample() {
        let cex = Counterexample::new(vec![
            ("a".into(), CounterexampleValue::Int(42)),
            ("b".into(), CounterexampleValue::Uint(100)),
            ("c".into(), CounterexampleValue::Bool(true)),
        ]);

        let model = CexModel::from_counterexample(&cex);
        assert_eq!(model.values.len(), 3);
        assert_eq!(model.values["a"], CexValue::Integer(42));
        assert_eq!(model.values["b"], CexValue::Unsigned(100));
        assert_eq!(model.values["c"], CexValue::Boolean(true));
    }

    #[test]
    fn test_cex_model_roundtrip() {
        let original = CexModel::from_pairs(vec![
            ("x".into(), CexValue::Integer(-5)),
            ("y".into(), CexValue::Unsigned(10)),
        ]);

        let cex = original.to_counterexample();
        let roundtrip = CexModel::from_counterexample(&cex);

        assert_eq!(roundtrip.values.len(), 2);
        assert_eq!(roundtrip.values["x"], CexValue::Integer(-5));
        assert_eq!(roundtrip.values["y"], CexValue::Unsigned(10));
    }

    // --- Confidence ordering ---

    #[test]
    fn test_proposals_sorted_by_confidence_descending() {
        let vc = make_vc(
            VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (
                    Ty::Int { width: 64, signed: false },
                    Ty::Int { width: 64, signed: false },
                ),
            },
            "f",
        );
        let cex = CexModel::from_pairs(vec![
            ("a".into(), CexValue::Unsigned(u64::MAX as u128)),
            ("b".into(), CexValue::Unsigned(1)),
        ]);

        let proposals = CounterexampleAnalyzer::refine(&vc, &cex);
        for window in proposals.windows(2) {
            assert!(
                window[0].confidence >= window[1].confidence,
                "proposals must be sorted by confidence: {} >= {}",
                window[0].confidence,
                window[1].confidence
            );
        }
    }

    // --- Cex-guided proposals have higher confidence than heuristic ---

    #[test]
    fn test_cex_guided_higher_confidence_than_heuristic() {
        let vc = make_vc(VcKind::DivisionByZero, "math::divide");
        let cex = CexModel::from_pairs(vec![
            ("x".into(), CexValue::Integer(42)),
            ("y".into(), CexValue::Integer(0)),
        ]);

        let cex_proposals = CounterexampleAnalyzer::refine(&vc, &cex);
        let heuristic_proposals = crate::spec_inference::infer_specs(&vc);

        let cex_top = cex_proposals[0].confidence;
        let heuristic_top = heuristic_proposals[0].confidence;

        assert!(
            cex_top >= heuristic_top,
            "cex-guided confidence ({cex_top}) should be >= heuristic ({heuristic_top})"
        );
    }

    // --- Unknown VcKind with no hints ---

    #[test]
    fn test_unmatched_vc_kind_with_cex_produces_nothing() {
        let vc = make_vc(VcKind::Deadlock, "service::event_loop");
        let cex = CexModel::from_pairs(vec![("state".into(), CexValue::Integer(3))]);

        let proposals = CounterexampleAnalyzer::refine(&vc, &cex);
        assert!(
            proposals.is_empty(),
            "a counterexample no refinement rule matches must yield nothing to rank, \
             got {proposals:?}"
        );
    }

    // --- Every VcKind a refinement rule covers produces at least one proposal ---

    #[test]
    fn test_all_refinable_vc_kinds_produce_proposals() {
        let vc_cex_pairs: Vec<(VcKind, CexModel)> = vec![
            (
                VcKind::ArithmeticOverflow {
                    op: BinOp::Add,
                    operand_tys: (
                        Ty::Int { width: 64, signed: false },
                        Ty::Int { width: 64, signed: false },
                    ),
                },
                CexModel::from_pairs(vec![
                    ("a".into(), CexValue::Unsigned(u64::MAX as u128)),
                    ("b".into(), CexValue::Unsigned(1)),
                ]),
            ),
            (
                VcKind::DivisionByZero,
                CexModel::from_pairs(vec![
                    ("x".into(), CexValue::Integer(42)),
                    ("y".into(), CexValue::Integer(0)),
                ]),
            ),
            (
                VcKind::IndexOutOfBounds,
                CexModel::from_pairs(vec![
                    ("index".into(), CexValue::Unsigned(10)),
                    ("len".into(), CexValue::Unsigned(5)),
                ]),
            ),
            (
                VcKind::NegationOverflow { ty: Ty::Int { width: 64, signed: true } },
                CexModel::from_pairs(vec![("x".into(), CexValue::Integer(i64::MIN as i128))]),
            ),
            (
                VcKind::CastOverflow {
                    from_ty: Ty::Int { width: 64, signed: false },
                    to_ty: Ty::Int { width: 32, signed: false },
                },
                CexModel::from_pairs(vec![("x".into(), CexValue::Unsigned(u32::MAX as u128 + 1))]),
            ),
            (
                VcKind::ShiftOverflow {
                    op: BinOp::Shl,
                    operand_ty: Ty::Int { width: 64, signed: false },
                    shift_ty: Ty::Int { width: 64, signed: false },
                },
                CexModel::from_pairs(vec![("shift".into(), CexValue::Unsigned(64))]),
            ),
        ];

        for (kind, cex) in &vc_cex_pairs {
            let vc = make_vc(kind.clone(), "test::f");
            let proposals = CounterexampleAnalyzer::refine(&vc, cex);
            assert!(
                !proposals.is_empty(),
                "VcKind {:?} should produce at least one proposal",
                kind
            );
            for p in &proposals {
                assert!(
                    (0.0..=1.0).contains(&p.confidence),
                    "VcKind {:?} has invalid confidence {}: {}",
                    kind,
                    p.confidence,
                    p.spec_text
                );
            }
        }
    }
}
