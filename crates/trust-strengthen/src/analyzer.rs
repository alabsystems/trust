// trust-strengthen/analyzer.rs: Failure pattern analysis
//
// Classifies failed VCs into actionable patterns that the proposer can
// turn into spec suggestions.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{BinOp, VcKind, VerificationCondition, VerificationResult};

/// A classified failure ready for the proposer.
#[derive(Debug, Clone)]
pub struct FailureAnalysis {
    /// The VC that failed.
    pub vc_kind: VcKind,
    /// The function containing the failure.
    pub function: String,
    /// The classified pattern.
    pub pattern: FailurePattern,
    /// Solver that reported the failure.
    pub solver: Option<String>,
}

/// Classified failure patterns that map to spec proposals.
#[derive(Debug, Clone, PartialEq)]
pub enum FailurePattern {
    ArithmeticOverflow { op: BinOp },
    DivisionByZero,
    IndexOutOfBounds,
    /// A bulk allocation whose element count may reach the unbounded-allocation
    /// ceiling. `count` is the SMT-lib rendering of the size expression.
    UnboundedAllocation { callee: String, count: String },
    CastOverflow,
    NegationOverflow,
    ShiftOverflow,
    AssertionFailure { message: String },
    PreconditionViolation { callee: String },
    PostconditionViolation,
    UnreachableReached,
    Temporal,
    Unknown,
}

/// Analyze a single failed VC and classify it.
///
/// Used by both the crate-level `run()` function and by compiler-side
/// strengthening in `rustc_mir_transform::trust_verify`.
pub fn analyze_failure(vc: &VerificationCondition, result: &VerificationResult) -> FailureAnalysis {
    let solver = match result {
        VerificationResult::Failed { solver, .. } => Some(solver.to_string()),
        _ => None,
    };
    let pattern = classify_vc_kind(&vc.kind);
    FailureAnalysis {
        vc_kind: vc.kind.clone(),
        function: vc.function.as_str().to_string(),
        pattern,
        solver,
    }
}

fn classify_vc_kind(kind: &VcKind) -> FailurePattern {
    match kind {
        VcKind::ArithmeticOverflow { op, .. } => FailurePattern::ArithmeticOverflow { op: *op },
        VcKind::DivisionByZero | VcKind::RemainderByZero => FailurePattern::DivisionByZero,
        VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => FailurePattern::IndexOutOfBounds,
        VcKind::UnboundedAllocation { callee, count, .. } => {
            FailurePattern::UnboundedAllocation { callee: callee.clone(), count: count.clone() }
        }
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
        VcKind::DeadState { .. }
        | VcKind::Deadlock
        | VcKind::Temporal { .. }
        | VcKind::Liveness { .. }
        | VcKind::Fairness { .. } => FailurePattern::Temporal,
        _ => FailurePattern::Unknown,
    }
}

#[cfg(test)]
mod tests {
    use trust_types::{Formula, SourceSpan, Ty};

    use super::*;

    fn failed_result() -> VerificationResult {
        VerificationResult::Failed { solver: "ay".into(), time_ms: 1, counterexample: None }
    }

    fn make_vc(kind: VcKind) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        }
    }

    #[test]
    fn test_classify_overflow() {
        let vc = make_vc(VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (
                Ty::Int { width: 64, signed: false },
                Ty::Int { width: 64, signed: false },
            ),
        });
        let analysis = analyze_failure(&vc, &failed_result());
        assert!(matches!(analysis.pattern, FailurePattern::ArithmeticOverflow { op: BinOp::Add }));
    }

    #[test]
    fn test_classify_div_zero() {
        let analysis = analyze_failure(&make_vc(VcKind::DivisionByZero), &failed_result());
        assert_eq!(analysis.pattern, FailurePattern::DivisionByZero);
    }

    #[test]
    fn test_classify_oob() {
        let analysis = analyze_failure(&make_vc(VcKind::IndexOutOfBounds), &failed_result());
        assert_eq!(analysis.pattern, FailurePattern::IndexOutOfBounds);
    }

    #[test]
    fn test_classify_assertion() {
        let vc = make_vc(VcKind::Assertion { message: "x > 0".into() });
        let analysis = analyze_failure(&vc, &failed_result());
        assert!(matches!(analysis.pattern, FailurePattern::AssertionFailure { .. }));
    }

    #[test]
    fn test_classify_temporal() {
        let analysis = analyze_failure(&make_vc(VcKind::Deadlock), &failed_result());
        assert_eq!(analysis.pattern, FailurePattern::Temporal);
    }
}
