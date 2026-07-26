// trust-strengthen/counterexample.rs: Counterexample-guided spec inference
//
// Extracts variable bindings from solver counterexamples and infers tighter
// preconditions based on concrete values that violate the property.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Counterexample, CounterexampleValue, VcKind};

use crate::analyzer::FailurePattern;

/// A hint derived from a counterexample that guides spec inference.
#[derive(Debug, Clone, PartialEq)]
pub struct CounterexampleHint {
    /// The variable name from the counterexample.
    pub variable: String,
    /// What kind of bound or constraint the hint suggests.
    pub kind: HintKind,
    /// Confidence boost this hint provides (added to base confidence).
    pub confidence_boost: f64,
}

/// The kind of constraint inferred from a counterexample value.
#[derive(Debug, Clone, PartialEq)]
pub enum HintKind {
    /// Variable must be less than this upper bound.
    UpperBound { bound: i128 },
    /// Variable must be greater than this lower bound.
    LowerBound { bound: i128 },
    /// Variable must not equal this value.
    NotEqual { value: i128 },
    /// Variable must be non-zero.
    NonZero,
    /// Variable must be less than another variable (e.g., index < len).
    LessThan { other: String },
    /// A specific bound expression for the spec body.
    BoundExpr { spec_fragment: String },
}

/// Extract hints from a counterexample given the failure pattern.
///
/// Uses the concrete variable assignments to infer what constraints would
/// prevent the failure. For example, if the counterexample shows a=MAX, b=1
/// for an overflow, we infer that a + b must not overflow.
#[must_use]
pub(crate) fn extract_hints(
    counterexample: &Counterexample,
    pattern: &FailurePattern,
    vc_kind: &VcKind,
) -> Vec<CounterexampleHint> {
    match pattern {
        FailurePattern::ArithmeticOverflow { .. } => {
            extract_overflow_hints(counterexample, vc_kind)
        }
        FailurePattern::DivisionByZero => extract_div_zero_hints(counterexample),
        FailurePattern::IndexOutOfBounds => extract_oob_hints(counterexample),
        FailurePattern::NegationOverflow => extract_negation_hints(counterexample),
        FailurePattern::ShiftOverflow => extract_shift_hints(counterexample, vc_kind),
        FailurePattern::CastOverflow => extract_cast_hints(counterexample, vc_kind),
        _ => vec![],
    }
}

/// Build a spec body string from a set of hints for a given failure pattern.
#[must_use]
pub(crate) fn hints_to_spec_body(
    hints: &[CounterexampleHint],
    pattern: &FailurePattern,
) -> Option<String> {
    if hints.is_empty() {
        return None;
    }

    let parts: Vec<String> = hints
        .iter()
        .map(|h| match &h.kind {
            HintKind::UpperBound { bound } => format!("{} <= {bound}", h.variable),
            HintKind::LowerBound { bound } => format!("{} >= {bound}", h.variable),
            HintKind::NotEqual { value } => format!("{} != {value}", h.variable),
            HintKind::NonZero => format!("{} != 0", h.variable),
            HintKind::LessThan { other } => format!("{} < {other}", h.variable),
            HintKind::BoundExpr { spec_fragment } => spec_fragment.clone(),
        })
        .collect();

    if parts.is_empty() {
        return None;
    }

    // For overflow patterns, wrap in a more descriptive spec if we have two operands
    if matches!(pattern, FailurePattern::ArithmeticOverflow { .. }) && parts.len() == 1 {
        // SAFETY: We checked parts.is_empty() above and returned None.
        return Some(
            parts
                .into_iter()
                .next()
                .unwrap_or_else(|| unreachable!("parts empty after non-empty check")),
        );
    }

    Some(parts.join(" && "))
}

/// Convert a list of counterexample hints into precondition formula strings.
///
/// Each hint is translated into a standalone precondition expression suitable
/// for use as a native `requires ...` clause. Returns one precondition per hint.
#[must_use]
pub(crate) fn hints_to_preconditions(hints: &[CounterexampleHint]) -> Vec<String> {
    hints
        .iter()
        .map(|h| match &h.kind {
            HintKind::UpperBound { bound } => format!("{} <= {bound}", h.variable),
            HintKind::LowerBound { bound } => format!("{} >= {bound}", h.variable),
            HintKind::NotEqual { value } => format!("{} != {value}", h.variable),
            HintKind::NonZero => format!("{} != 0", h.variable),
            HintKind::LessThan { other } => format!("{} < {other}", h.variable),
            HintKind::BoundExpr { spec_fragment } => spec_fragment.clone(),
        })
        .collect()
}

// --- Extraction helpers ---

fn extract_overflow_hints(
    counterexample: &Counterexample,
    vc_kind: &VcKind,
) -> Vec<CounterexampleHint> {
    let mut hints = Vec::new();
    let assignments = &counterexample.assignments;

    // Identify the operand variables and their types from VcKind
    let (bit_width, is_signed) = match vc_kind {
        VcKind::ArithmeticOverflow { operand_tys, .. } => extract_type_info(&operand_tys.0),
        _ => (64, false),
    };

    let max_val = if is_signed {
        (1i128 << (bit_width - 1)) - 1
    } else if bit_width >= 128 {
        i128::MAX
    } else {
        (1i128 << bit_width) - 1
    };

    // Look for variables at boundary values
    for (name, value) in assignments {
        match value {
            CounterexampleValue::Uint(v) => {
                let v_i128 = *v as i128;
                if v_i128 == max_val || (bit_width < 128 && *v == (1u128 << bit_width) - 1) {
                    hints.push(CounterexampleHint {
                        variable: name.clone(),
                        kind: HintKind::UpperBound { bound: max_val - 1 },
                        confidence_boost: 0.1,
                    });
                } else if *v > 0 {
                    hints.push(CounterexampleHint {
                        variable: name.clone(),
                        kind: HintKind::BoundExpr {
                            spec_fragment: format!("{name} <= {max_val} - <other_operand>"),
                        },
                        confidence_boost: 0.05,
                    });
                }
            }
            CounterexampleValue::Int(v) if *v == max_val || (is_signed && *v == -(max_val + 1)) => {
                hints.push(CounterexampleHint {
                    variable: name.clone(),
                    kind: HintKind::UpperBound { bound: max_val - 1 },
                    confidence_boost: 0.1,
                });
            }
            _ => {}
        }
    }

    // If we have exactly two numeric variables, produce a combined bound
    let numeric_vars: Vec<_> = assignments
        .iter()
        .filter(|(_, v)| matches!(v, CounterexampleValue::Uint(_) | CounterexampleValue::Int(_)))
        .collect();

    if numeric_vars.len() == 2 {
        let (name_a, _) = numeric_vars[0];
        let (name_b, _) = numeric_vars[1];
        hints.push(CounterexampleHint {
            variable: name_a.clone(),
            kind: HintKind::BoundExpr {
                spec_fragment: format!("{name_a} <= {max_val} - {name_b}"),
            },
            confidence_boost: 0.1,
        });
    }

    hints
}

fn extract_div_zero_hints(counterexample: &Counterexample) -> Vec<CounterexampleHint> {
    counterexample
        .assignments
        .iter()
        .filter_map(|(name, value): &(String, CounterexampleValue)| {
            let is_zero =
                matches!(value, CounterexampleValue::Int(0) | CounterexampleValue::Uint(0));
            if is_zero {
                Some(CounterexampleHint {
                    variable: name.clone(),
                    kind: HintKind::NonZero,
                    confidence_boost: 0.1,
                })
            } else {
                None
            }
        })
        .collect()
}

fn extract_oob_hints(counterexample: &Counterexample) -> Vec<CounterexampleHint> {
    let mut hints = Vec::new();
    let assignments = &counterexample.assignments;

    // Look for index/len variable pairs
    let index_var = assignments
        .iter()
        .find(|(name, _)| name.contains("index") || name.contains("idx") || name == "i");
    let len_var = assignments
        .iter()
        .find(|(name, _)| name.contains("len") || name.contains("length") || name.contains("size"));

    if let (Some((idx_name, idx_val)), Some((len_name, _))) = (index_var, len_var) {
        // We found both -- suggest index < len
        hints.push(CounterexampleHint {
            variable: idx_name.clone(),
            kind: HintKind::LessThan { other: len_name.clone() },
            confidence_boost: 0.1,
        });

        // Also add a concrete bound from the counterexample
        if let Some(idx_int) = to_i128(idx_val) {
            hints.push(CounterexampleHint {
                variable: idx_name.clone(),
                kind: HintKind::UpperBound { bound: idx_int - 1 },
                confidence_boost: 0.05,
            });
        }
    } else {
        // No recognized variable names -- just flag any large index value
        for (name, value) in assignments {
            if let Some(v) = to_i128(value)
                && v > 0
            {
                hints.push(CounterexampleHint {
                    variable: name.clone(),
                    kind: HintKind::BoundExpr { spec_fragment: format!("{name} < arr.len()") },
                    confidence_boost: 0.05,
                });
            }
        }
    }

    hints
}

fn extract_negation_hints(counterexample: &Counterexample) -> Vec<CounterexampleHint> {
    counterexample
        .assignments
        .iter()
        .filter_map(|(name, value): &(String, CounterexampleValue)| match value {
            CounterexampleValue::Int(v)
                if *v == i128::MIN
                    || *v == i64::MIN as i128
                    || *v == i32::MIN as i128
                    || *v == i16::MIN as i128
                    || *v == i8::MIN as i128 =>
            {
                Some(CounterexampleHint {
                    variable: name.clone(),
                    kind: HintKind::NotEqual { value: *v },
                    confidence_boost: 0.1,
                })
            }
            _ => None,
        })
        .collect()
}

fn extract_shift_hints(
    counterexample: &Counterexample,
    vc_kind: &VcKind,
) -> Vec<CounterexampleHint> {
    let bit_width = match vc_kind {
        VcKind::ShiftOverflow { operand_ty, .. } => extract_type_info(operand_ty).0,
        _ => 64,
    };

    counterexample
        .assignments
        .iter()
        .filter_map(|(name, value): &(String, CounterexampleValue)| {
            if let Some(v) = to_i128(value)
                && v >= bit_width as i128
            {
                return Some(CounterexampleHint {
                    variable: name.clone(),
                    kind: HintKind::UpperBound { bound: bit_width as i128 - 1 },
                    confidence_boost: 0.1,
                });
            }
            None
        })
        .collect()
}

fn extract_cast_hints(
    counterexample: &Counterexample,
    vc_kind: &VcKind,
) -> Vec<CounterexampleHint> {
    let target_max = match vc_kind {
        VcKind::CastOverflow { to_ty, .. } => {
            let (bw, signed) = extract_type_info(to_ty);
            if signed {
                (1i128 << (bw - 1)) - 1
            } else if bw >= 128 {
                i128::MAX
            } else {
                (1i128 << bw) - 1
            }
        }
        _ => return vec![],
    };

    counterexample
        .assignments
        .iter()
        .filter_map(|(name, value): &(String, CounterexampleValue)| {
            if let Some(v) = to_i128(value)
                && v > target_max
            {
                return Some(CounterexampleHint {
                    variable: name.clone(),
                    kind: HintKind::UpperBound { bound: target_max },
                    confidence_boost: 0.1,
                });
            }
            None
        })
        .collect()
}

// --- Utility helpers ---

fn extract_type_info(ty: &trust_types::Ty) -> (u32, bool) {
    match ty {
        trust_types::Ty::Int { width, signed } => (*width, *signed),
        _ => (64, false),
    }
}

fn to_i128(value: &CounterexampleValue) -> Option<i128> {
    match value {
        CounterexampleValue::Int(v) => Some(*v),
        CounterexampleValue::Uint(v) => i128::try_from(*v).ok(),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use trust_types::{BinOp, Ty};

    use super::*;

    fn make_counterexample(assignments: Vec<(&str, CounterexampleValue)>) -> Counterexample {
        Counterexample::new(
            assignments.into_iter().map(|(name, val)| (name.to_string(), val)).collect(),
        )
    }

    // --- Overflow hint tests ---

    #[test]
    fn test_extract_overflow_hints_u64_max() {
        let cx = make_counterexample(vec![
            ("a", CounterexampleValue::Uint(u64::MAX as u128)),
            ("b", CounterexampleValue::Uint(1)),
        ]);
        let kind = VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (
                Ty::Int { width: 64, signed: false },
                Ty::Int { width: 64, signed: false },
            ),
        };
        let hints =
            extract_hints(&cx, &FailurePattern::ArithmeticOverflow { op: BinOp::Add }, &kind);
        assert!(!hints.is_empty(), "should produce hints for overflow at MAX");

        let combined = hints.iter().find(|h| {
            matches!(&h.kind, HintKind::BoundExpr { spec_fragment } if spec_fragment.contains(" <= "))
        });
        assert!(combined.is_some(), "should produce a combined bound expression");
    }

    #[test]
    fn test_extract_overflow_hints_signed() {
        let cx = make_counterexample(vec![
            ("x", CounterexampleValue::Int(i64::MAX as i128)),
            ("y", CounterexampleValue::Int(1)),
        ]);
        let kind = VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (Ty::Int { width: 64, signed: true }, Ty::Int { width: 64, signed: true }),
        };
        let hints =
            extract_hints(&cx, &FailurePattern::ArithmeticOverflow { op: BinOp::Add }, &kind);
        assert!(!hints.is_empty(), "should produce hints for signed overflow");
    }

    // --- Division by zero hint tests ---

    #[test]
    fn test_extract_div_zero_hints_int() {
        let cx = make_counterexample(vec![
            ("x", CounterexampleValue::Int(42)),
            ("y", CounterexampleValue::Int(0)),
        ]);
        let hints = extract_hints(&cx, &FailurePattern::DivisionByZero, &VcKind::DivisionByZero);
        assert_eq!(hints.len(), 1);
        assert_eq!(hints[0].variable, "y");
        assert_eq!(hints[0].kind, HintKind::NonZero);
    }

    #[test]
    fn test_extract_div_zero_hints_uint() {
        let cx = make_counterexample(vec![
            ("a", CounterexampleValue::Uint(100)),
            ("b", CounterexampleValue::Uint(0)),
        ]);
        let hints = extract_hints(&cx, &FailurePattern::DivisionByZero, &VcKind::DivisionByZero);
        assert_eq!(hints.len(), 1);
        assert_eq!(hints[0].variable, "b");
        assert_eq!(hints[0].kind, HintKind::NonZero);
    }

    // --- Index out of bounds hint tests ---

    #[test]
    fn test_extract_oob_hints_named_vars() {
        let cx = make_counterexample(vec![
            ("index", CounterexampleValue::Uint(5)),
            ("len", CounterexampleValue::Uint(3)),
        ]);
        let hints =
            extract_hints(&cx, &FailurePattern::IndexOutOfBounds, &VcKind::IndexOutOfBounds);
        assert!(!hints.is_empty());

        let lt_hint = hints.iter().find(|h| matches!(&h.kind, HintKind::LessThan { .. }));
        assert!(lt_hint.is_some(), "should produce index < len hint");
        if let Some(h) = lt_hint {
            assert_eq!(h.variable, "index");
            assert!(matches!(&h.kind, HintKind::LessThan { other } if other == "len"));
        }
    }

    #[test]
    fn test_extract_oob_hints_unnamed_vars() {
        let cx = make_counterexample(vec![("n", CounterexampleValue::Uint(10))]);
        let hints =
            extract_hints(&cx, &FailurePattern::IndexOutOfBounds, &VcKind::IndexOutOfBounds);
        assert!(!hints.is_empty());

        let bound = hints.iter().find(|h| matches!(&h.kind, HintKind::BoundExpr { .. }));
        assert!(bound.is_some(), "should produce a bound expression for unnamed vars");
    }

    // --- Negation overflow hint tests ---

    #[test]
    fn test_extract_negation_hints_i64_min() {
        let cx = make_counterexample(vec![("x", CounterexampleValue::Int(i64::MIN as i128))]);
        let hints = extract_hints(
            &cx,
            &FailurePattern::NegationOverflow,
            &VcKind::NegationOverflow { ty: Ty::Int { width: 64, signed: true } },
        );
        assert_eq!(hints.len(), 1);
        assert_eq!(hints[0].variable, "x");
        assert!(matches!(hints[0].kind, HintKind::NotEqual { value } if value == i64::MIN as i128));
    }

    // --- Shift overflow hint tests ---

    #[test]
    fn test_extract_shift_hints_large_shift() {
        let cx = make_counterexample(vec![
            ("val", CounterexampleValue::Uint(1)),
            ("shift", CounterexampleValue::Uint(64)),
        ]);
        let kind = VcKind::ShiftOverflow {
            op: BinOp::Shl,
            operand_ty: Ty::Int { width: 64, signed: false },
            shift_ty: Ty::Int { width: 64, signed: false },
        };
        let hints = extract_hints(&cx, &FailurePattern::ShiftOverflow, &kind);
        assert!(!hints.is_empty());

        let shift_hint = hints.iter().find(|h| h.variable == "shift");
        assert!(shift_hint.is_some());
        assert!(matches!(shift_hint.unwrap().kind, HintKind::UpperBound { bound: 63 }));
    }

    // --- Cast overflow hint tests ---

    #[test]
    fn test_extract_cast_hints_u64_to_u32() {
        let cx = make_counterexample(vec![("x", CounterexampleValue::Uint(u32::MAX as u128 + 1))]);
        let kind = VcKind::CastOverflow {
            from_ty: Ty::Int { width: 64, signed: false },
            to_ty: Ty::Int { width: 32, signed: false },
        };
        let hints = extract_hints(&cx, &FailurePattern::CastOverflow, &kind);
        assert_eq!(hints.len(), 1);
        assert_eq!(hints[0].variable, "x");
        assert!(
            matches!(hints[0].kind, HintKind::UpperBound { bound } if bound == u32::MAX as i128)
        );
    }

    // --- hints_to_spec_body tests ---

    #[test]
    fn test_hints_to_spec_body_nonzero() {
        let hints = vec![CounterexampleHint {
            variable: "y".into(),
            kind: HintKind::NonZero,
            confidence_boost: 0.1,
        }];
        let spec = hints_to_spec_body(&hints, &FailurePattern::DivisionByZero);
        assert_eq!(spec, Some("y != 0".to_string()));
    }

    #[test]
    fn test_hints_to_spec_body_multiple() {
        let hints = vec![
            CounterexampleHint {
                variable: "x".into(),
                kind: HintKind::LowerBound { bound: 0 },
                confidence_boost: 0.05,
            },
            CounterexampleHint {
                variable: "x".into(),
                kind: HintKind::UpperBound { bound: 100 },
                confidence_boost: 0.05,
            },
        ];
        let spec = hints_to_spec_body(&hints, &FailurePattern::CastOverflow);
        assert_eq!(spec, Some("x >= 0 && x <= 100".to_string()));
    }

    #[test]
    fn test_hints_to_spec_body_empty() {
        let hints: Vec<CounterexampleHint> = vec![];
        let spec = hints_to_spec_body(&hints, &FailurePattern::Unknown);
        assert_eq!(spec, None);
    }

    #[test]
    fn test_hints_to_spec_body_less_than() {
        let hints = vec![CounterexampleHint {
            variable: "index".into(),
            kind: HintKind::LessThan { other: "len".into() },
            confidence_boost: 0.1,
        }];
        let spec = hints_to_spec_body(&hints, &FailurePattern::IndexOutOfBounds);
        assert_eq!(spec, Some("index < len".to_string()));
    }

    // --- No hints for irrelevant patterns ---

    #[test]
    fn test_extract_hints_unknown_pattern_returns_empty() {
        let cx = make_counterexample(vec![("x", CounterexampleValue::Int(42))]);
        let hints = extract_hints(&cx, &FailurePattern::Unknown, &VcKind::Unreachable);
        assert!(hints.is_empty());
    }

    // --- hints_to_preconditions tests ---

    #[test]
    fn test_hints_to_preconditions_empty() {
        let precs = hints_to_preconditions(&[]);
        assert!(precs.is_empty());
    }

    #[test]
    fn test_hints_to_preconditions_upper_bound() {
        let hints = vec![CounterexampleHint {
            variable: "x".into(),
            kind: HintKind::UpperBound { bound: 255 },
            confidence_boost: 0.1,
        }];
        let precs = hints_to_preconditions(&hints);
        assert_eq!(precs, vec!["x <= 255"]);
    }

    #[test]
    fn test_hints_to_preconditions_lower_bound() {
        let hints = vec![CounterexampleHint {
            variable: "y".into(),
            kind: HintKind::LowerBound { bound: 0 },
            confidence_boost: 0.05,
        }];
        let precs = hints_to_preconditions(&hints);
        assert_eq!(precs, vec!["y >= 0"]);
    }

    #[test]
    fn test_hints_to_preconditions_nonzero() {
        let hints = vec![CounterexampleHint {
            variable: "divisor".into(),
            kind: HintKind::NonZero,
            confidence_boost: 0.1,
        }];
        let precs = hints_to_preconditions(&hints);
        assert_eq!(precs, vec!["divisor != 0"]);
    }

    #[test]
    fn test_hints_to_preconditions_not_equal() {
        let hints = vec![CounterexampleHint {
            variable: "x".into(),
            kind: HintKind::NotEqual { value: i64::MIN as i128 },
            confidence_boost: 0.1,
        }];
        let precs = hints_to_preconditions(&hints);
        assert_eq!(precs.len(), 1);
        assert!(precs[0].starts_with("x != "));
    }

    #[test]
    fn test_hints_to_preconditions_less_than() {
        let hints = vec![CounterexampleHint {
            variable: "idx".into(),
            kind: HintKind::LessThan { other: "len".into() },
            confidence_boost: 0.1,
        }];
        let precs = hints_to_preconditions(&hints);
        assert_eq!(precs, vec!["idx < len"]);
    }

    #[test]
    fn test_hints_to_preconditions_bound_expr() {
        let hints = vec![CounterexampleHint {
            variable: "a".into(),
            kind: HintKind::BoundExpr { spec_fragment: "a <= u64::MAX - b".into() },
            confidence_boost: 0.1,
        }];
        let precs = hints_to_preconditions(&hints);
        assert_eq!(precs, vec!["a <= u64::MAX - b"]);
    }

    #[test]
    fn test_hints_to_preconditions_multiple() {
        let hints = vec![
            CounterexampleHint {
                variable: "x".into(),
                kind: HintKind::LowerBound { bound: 0 },
                confidence_boost: 0.05,
            },
            CounterexampleHint {
                variable: "x".into(),
                kind: HintKind::UpperBound { bound: 100 },
                confidence_boost: 0.05,
            },
            CounterexampleHint {
                variable: "y".into(),
                kind: HintKind::NonZero,
                confidence_boost: 0.1,
            },
        ];
        let precs = hints_to_preconditions(&hints);
        assert_eq!(precs.len(), 3);
        assert_eq!(precs[0], "x >= 0");
        assert_eq!(precs[1], "x <= 100");
        assert_eq!(precs[2], "y != 0");
    }
}
