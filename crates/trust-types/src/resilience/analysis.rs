// trust-types/resilience/analysis: ResilienceAnalysis implementation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::{BinOp, Rvalue, SourceSpan, Statement, Terminator, VerifiableFunction};

use super::external_patterns::extract_failure_model;
use super::helpers::{assert_msg_description, classify_error_handling, detect_panic_call};
use super::types::*;

/// Resilience analyzer: inspects a `VerifiableFunction` and produces a `ResilienceReport`.
pub struct ResilienceAnalysis;

impl ResilienceAnalysis {
    /// Analyze a function for resilience properties.
    ///
    /// Detects panic paths, unwrap calls, unchecked arithmetic, and classifies
    /// error handling patterns to produce a comprehensive resilience report.
    pub fn analyze_function(func: &VerifiableFunction) -> ResilienceReport {
        let panic_paths = Self::detect_panic_paths(func);
        let unchecked_arithmetic = Self::detect_unchecked_arithmetic(func);
        let error_handling = Self::detect_error_handling(func);
        let failure_model = extract_failure_model(func);
        let fault_model = Self::classify_fault_model(&panic_paths, &error_handling);
        let properties = Self::detect_properties(func, &panic_paths);
        let risk_score =
            Self::compute_risk_score(&panic_paths, &unchecked_arithmetic, &failure_model);
        let recommendations =
            Self::generate_recommendations(&panic_paths, &unchecked_arithmetic, &error_handling);

        ResilienceReport {
            function: func.def_path.clone(),
            fault_model,
            properties,
            risk_score,
            recommendations,
            panic_paths,
            unchecked_arithmetic,
            error_handling,
            failure_model,
        }
    }

    /// Detect all panic paths in the function body.
    fn detect_panic_paths(func: &VerifiableFunction) -> Vec<PanicPath> {
        let mut paths = Vec::new();

        for block in &func.body.blocks {
            // Check terminators for assert failures and panics.
            match &block.terminator {
                Terminator::Assert { msg, span, .. } => {
                    let kind = match msg {
                        crate::AssertMessage::Overflow(_) => PanicKind::Overflow,
                        crate::AssertMessage::BoundsCheck => PanicKind::BoundsCheck,
                        crate::AssertMessage::DivisionByZero
                        | crate::AssertMessage::RemainderByZero => PanicKind::DivisionByZero,
                        crate::AssertMessage::OverflowNeg => PanicKind::Overflow,
                        _ => PanicKind::Assert,
                    };
                    paths.push(PanicPath {
                        block: block.id,
                        span: span.clone(),
                        description: format!("assert may fail: {}", assert_msg_description(msg)),
                        kind,
                    });
                }
                Terminator::Call { func: call_func, span, .. } => {
                    if let Some(kind) = detect_panic_call(call_func) {
                        paths.push(PanicPath {
                            block: block.id,
                            span: span.clone(),
                            description: format!("call to `{}` may panic", call_func),
                            kind,
                        });
                    }
                }
                Terminator::Unreachable => {
                    paths.push(PanicPath {
                        block: block.id,
                        span: SourceSpan::default(),
                        description: "unreachable terminator".to_string(),
                        kind: PanicKind::ExplicitPanic,
                    });
                }
                _ => {}
            }
        }

        paths
    }

    /// Detect unchecked arithmetic operations (non-checked BinaryOp with overflow-prone ops).
    fn detect_unchecked_arithmetic(func: &VerifiableFunction) -> Vec<UncheckedArithmetic> {
        let mut results = Vec::new();

        for block in &func.body.blocks {
            for stmt in &block.stmts {
                if let Statement::Assign { rvalue: Rvalue::BinaryOp(op, _, _), span, .. } = stmt {
                    if op.can_overflow() {
                        results.push(UncheckedArithmetic {
                            block: block.id,
                            op: *op,
                            span: span.clone(),
                            description: format!(
                                "unchecked {:?} may overflow (use CheckedBinaryOp instead)",
                                op
                            ),
                        });
                    }
                    if op.is_division() {
                        results.push(UncheckedArithmetic {
                            block: block.id,
                            op: *op,
                            span: span.clone(),
                            description: format!(
                                "unchecked {:?} may divide by zero (no preceding assert)",
                                op
                            ),
                        });
                    }
                }
            }
        }

        results
    }

    /// Detect error handling patterns from call terminators.
    fn detect_error_handling(func: &VerifiableFunction) -> Vec<ErrorHandlingPattern> {
        let mut patterns = Vec::new();

        for block in &func.body.blocks {
            if let Terminator::Call { func: call_func, span: _, dest, target, .. } =
                &block.terminator
            {
                // If the call target block exists, check how the result is used.
                if let Some(target_block_id) = target
                    && let Some(target_block) =
                        func.body.blocks.iter().find(|b| b.id == *target_block_id)
                {
                    let pattern = classify_error_handling(call_func, block.id, dest, target_block);
                    patterns.push(pattern);
                }
            }
        }

        patterns
    }

    /// Classify the overall fault model from detected patterns.
    fn classify_fault_model(
        panic_paths: &[PanicPath],
        error_handling: &[ErrorHandlingPattern],
    ) -> FaultModel {
        let has_panics = panic_paths.iter().any(|p| {
            matches!(p.kind, PanicKind::Unwrap | PanicKind::Expect | PanicKind::ExplicitPanic)
        });
        let has_panicking_handler =
            error_handling.iter().any(|e| matches!(e, ErrorHandlingPattern::Panicking { .. }));
        let has_propagation =
            error_handling.iter().any(|e| matches!(e, ErrorHandlingPattern::Propagation { .. }));
        let has_swallowing =
            error_handling.iter().any(|e| matches!(e, ErrorHandlingPattern::Swallowing { .. }));

        // Panics are the most dangerous: if the function can panic, that dominates.
        if has_panics || has_panicking_handler {
            FaultModel::PanicOnError
        } else if has_swallowing && !has_propagation {
            // Only swallowing with no propagation = silent corruption.
            FaultModel::SilentCorruption
        } else if has_propagation {
            FaultModel::ReturnError
        } else if has_swallowing {
            // Swallowing alongside propagation = mixed, lean toward silent corruption.
            FaultModel::SilentCorruption
        } else if panic_paths.is_empty() && error_handling.is_empty() {
            // Pure function with no error paths.
            FaultModel::ReturnError
        } else {
            FaultModel::PanicOnError
        }
    }

    /// Detect resilience properties from function structure.
    fn detect_properties(
        func: &VerifiableFunction,
        panic_paths: &[PanicPath],
    ) -> Vec<ResilienceProperty> {
        let mut props = Vec::new();

        // A function with no panic paths and no side effects is crash-consistent.
        if panic_paths.is_empty() {
            props.push(ResilienceProperty::CrashConsistent);
        }

        // Check for commutative binary operations (heuristic: if the function
        // body is a single commutative binop, the function is commutative).
        if func.body.arg_count == 2 && func.body.blocks.len() <= 2 {
            let has_commutative_op = func.body.blocks.iter().any(|block| {
                block.stmts.iter().any(|stmt| {
                    matches!(
                        stmt,
                        Statement::Assign {
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add
                                    | BinOp::Mul
                                    | BinOp::BitAnd
                                    | BinOp::BitOr
                                    | BinOp::BitXor
                                    | BinOp::Eq
                                    | BinOp::Ne,
                                _,
                                _
                            ),
                            ..
                        } | Statement::Assign {
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Add
                                    | BinOp::Mul
                                    | BinOp::BitAnd
                                    | BinOp::BitOr
                                    | BinOp::BitXor
                                    | BinOp::Eq
                                    | BinOp::Ne,
                                _,
                                _
                            ),
                            ..
                        }
                    )
                })
            });
            if has_commutative_op {
                props.push(ResilienceProperty::Commutative);
            }
        }

        props
    }

    /// Compute a risk score from 0.0 (safe) to 1.0 (high risk).
    pub(in crate::resilience) fn compute_risk_score(
        panic_paths: &[PanicPath],
        unchecked_arithmetic: &[UncheckedArithmetic],
        failure_model: &FailureModel,
    ) -> f64 {
        let panic_score = (panic_paths.len() as f64 * 0.15).min(0.5);
        let arith_score = (unchecked_arithmetic.len() as f64 * 0.1).min(0.3);
        let dep_score = (failure_model.dependencies.len() as f64 * 0.05).min(0.2);
        (panic_score + arith_score + dep_score).min(1.0)
    }

    /// Generate recommendations for improving resilience.
    fn generate_recommendations(
        panic_paths: &[PanicPath],
        unchecked_arithmetic: &[UncheckedArithmetic],
        error_handling: &[ErrorHandlingPattern],
    ) -> Vec<String> {
        let mut recs = Vec::new();

        let unwrap_count =
            panic_paths.iter().filter(|p| matches!(p.kind, PanicKind::Unwrap)).count();
        if unwrap_count > 0 {
            recs.push(format!(
                "Replace {} unwrap() call(s) with proper error handling using `?` or match",
                unwrap_count
            ));
        }

        let expect_count =
            panic_paths.iter().filter(|p| matches!(p.kind, PanicKind::Expect)).count();
        if expect_count > 0 {
            recs.push(format!(
                "Replace {} expect() call(s) with `?` or match for recoverable errors",
                expect_count
            ));
        }

        if !unchecked_arithmetic.is_empty() {
            recs.push(format!(
                "Use checked arithmetic (checked_add, checked_mul, etc.) for {} operation(s)",
                unchecked_arithmetic.len()
            ));
        }

        let swallow_count = error_handling
            .iter()
            .filter(|e| matches!(e, ErrorHandlingPattern::Swallowing { .. }))
            .count();
        if swallow_count > 0 {
            recs.push(format!(
                "Investigate {} swallowed error(s) \u{2014} silent error suppression may mask bugs",
                swallow_count
            ));
        }

        recs
    }
}
