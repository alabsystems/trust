// Termination dispatch — separate termination from safety routing.
//
// PDR, k-induction, and BMC prove safety properties (AG !bad), NOT termination.
// Termination requires ranking functions, well-founded orderings, or decreases
// clauses. This module classifies properties and validates dispatch decisions.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{VcKind, VerificationCondition};

// ---------------------------------------------------------------------------
// Property classification
// ---------------------------------------------------------------------------

/// Semantic property kind for dispatch validation.
///
/// Safety and termination require fundamentally different proof techniques.
/// Conflating them (e.g., routing termination to PDR) produces unsound results.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum PropertyKind {
    /// Invariant holds on all reachable states (AG !bad).
    /// Provable by PDR, IC3, k-induction, BMC, SMT.
    Safety,
    /// Something good eventually happens (AF good, GF good).
    /// Requires fairness assumptions + ranking or Buchi automata.
    Liveness,
    /// All executions terminate (well-founded ordering exists).
    /// Requires ranking function synthesis, NOT safety checkers.
    Termination,
    /// If it terminates, the postcondition holds ({P} S {Q}).
    /// Provable by WP/SP calculus, deductive verification.
    PartialCorrectness,
}

// ---------------------------------------------------------------------------
// Classification
// ---------------------------------------------------------------------------

/// Classify a VC into its semantic property kind.
///
/// Inspects `VcKind` to determine whether the obligation is safety,
/// liveness, termination, or correctness. This classification drives
/// dispatch validation.
#[must_use]
pub(crate) fn classify_property(vc: &VerificationCondition) -> PropertyKind {
    match &vc.kind {
        // Termination
        VcKind::NonTermination { .. } => PropertyKind::Termination,

        // Liveness / temporal
        VcKind::Liveness { .. } | VcKind::Fairness { .. } => PropertyKind::Liveness,
        VcKind::Temporal { .. } => PropertyKind::Liveness,

        // Safety: all runtime-checkable panic conditions
        VcKind::ArithmeticOverflow { .. }
        | VcKind::ShiftOverflow { .. }
        | VcKind::DivisionByZero
        | VcKind::RemainderByZero
        | VcKind::IndexOutOfBounds
        | VcKind::SliceBoundsCheck
        | VcKind::CastOverflow { .. }
        | VcKind::NegationOverflow { .. }
        | VcKind::Unreachable
        | VcKind::DataRace { .. } => PropertyKind::Safety,

        // Safety: state machine deadlock / dead state
        VcKind::DeadState { .. } | VcKind::Deadlock => PropertyKind::Safety,

        // Partial correctness: contract-based
        VcKind::Precondition { .. }
        | VcKind::Postcondition
        | VcKind::TranslationValidation { .. } => PropertyKind::PartialCorrectness,

        // Safety: assertions are runtime-checkable invariants
        VcKind::Assertion { .. } => PropertyKind::Safety,

        // Safety/correctness: domain-specific
        VcKind::TaintViolation { .. }
        | VcKind::RefinementViolation { .. }
        | VcKind::ResilienceViolation { .. }
        | VcKind::ProtocolViolation { .. } => PropertyKind::Safety,

        // Safety: concurrency ordering
        VcKind::InsufficientOrdering { .. } => PropertyKind::Safety,

        // Floating-point safety checks
        VcKind::FloatDivisionByZero | VcKind::FloatOverflowToInfinity { .. } => {
            PropertyKind::Safety
        }
        // Rvalue safety VCs — type-level safety checks
        VcKind::InvalidDiscriminant { .. } | VcKind::AggregateArrayLengthMismatch { .. } => {
            PropertyKind::Safety
        }
        // Unsafe operations are safety properties.
        VcKind::UnsafeOperation { .. } => PropertyKind::Safety,
        // Ownership/memory safety VcKinds
        VcKind::UseAfterFree
        | VcKind::DoubleFree
        | VcKind::AliasingViolation { .. }
        | VcKind::LifetimeViolation
        | VcKind::SendViolation
        | VcKind::SyncViolation => PropertyKind::Safety,
        // FFI boundary violations are safety properties.
        VcKind::FfiBoundaryViolation { .. } => PropertyKind::Safety,
        // Functional correctness is partial correctness.
        VcKind::FunctionalCorrectness { .. } => PropertyKind::PartialCorrectness,
        // non-panicking fallback for #[non_exhaustive] forward compat
        _ => PropertyKind::Safety,
    }
}

// ---------------------------------------------------------------------------
// Solver capability checks
// ---------------------------------------------------------------------------

/// Returns true if the solver can ONLY prove safety properties.
///
/// PDR, IC3, k-induction, and BMC prove that bad states are unreachable
/// (AG !bad). They do NOT prove termination or liveness.
#[must_use]
pub(crate) fn is_safety_only(solver: &str) -> bool {
    matches!(
        solver.to_lowercase().as_str(),
        "pdr" | "ic3" | "k-induction" | "k_induction" | "bmc" | "ay-chc"
    )
}

// ---------------------------------------------------------------------------
// Dispatch validation
// ---------------------------------------------------------------------------

/// Result of validating a solver dispatch decision.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DispatchValidity {
    /// The solver can handle this property kind correctly.
    Valid,
    /// The solver fundamentally cannot handle this property kind.
    /// Dispatching to it would produce unsound or meaningless results.
    Invalid { reason: String },
    /// The solver can partially handle this but results may be incomplete.
    /// E.g., bounded unrolling for termination finds bugs but cannot prove it.
    Degraded { reason: String },
}

impl DispatchValidity {
    #[must_use]
    pub(crate) fn is_invalid(&self) -> bool {
        matches!(self, DispatchValidity::Invalid { .. })
    }
}

/// Validate that a solver can handle the given property kind.
///
/// This is the core guard that prevents the bug described in issue #194:
/// routing termination obligations to PDR/k-induction/BMC, which only
/// prove safety.
#[must_use]
pub(crate) fn validate_dispatch(property: PropertyKind, solver: &str) -> DispatchValidity {
    let solver_lower = solver.to_lowercase();
    let solver_str = solver_lower.as_str();

    match property {
        PropertyKind::Safety => {
            // All solvers can handle safety to some degree.
            DispatchValidity::Valid
        }

        PropertyKind::Termination => {
            if is_safety_only(solver_str) {
                DispatchValidity::Invalid {
                    reason: format!(
                        "{solver} proves safety (AG !bad), not termination. \
                         Use ranking function synthesis (clean, ay) instead."
                    ),
                }
            } else if solver_str == "trust-mc" {
                // trust_mc can find non-termination bugs via bounded unrolling
                // but cannot prove termination.
                DispatchValidity::Degraded {
                    reason: format!(
                        "{solver} can detect non-termination via lasso witnesses \
                         but cannot prove termination. Use clean or ay for proofs."
                    ),
                }
            } else if solver_str == "clean" || solver_str == "ay" || solver_str == "trust-wp" {
                DispatchValidity::Valid
            } else {
                DispatchValidity::Degraded {
                    reason: format!("{solver} has unknown termination proving capability."),
                }
            }
        }

        PropertyKind::Liveness => {
            if is_safety_only(solver_str) {
                DispatchValidity::Invalid {
                    reason: format!(
                        "{solver} proves safety only. Liveness requires \
                         fairness assumptions + ranking or Buchi automata. Use ty."
                    ),
                }
            } else if solver_str == "ty" || solver_str == "clean" {
                DispatchValidity::Valid
            } else {
                DispatchValidity::Degraded {
                    reason: format!("{solver} may not fully support liveness checking."),
                }
            }
        }

        PropertyKind::PartialCorrectness => {
            // Most solvers can handle partial correctness (WP/SP).
            DispatchValidity::Valid
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;

    /// Helper: build a VC with the given kind.
    fn make_vc(kind: VcKind) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        }
    }

    // -------------------------------------------------------------------
    // classify_property tests
    // -------------------------------------------------------------------

    #[test]
    fn test_classify_safety_division_by_zero() {
        let vc = make_vc(VcKind::DivisionByZero);
        assert_eq!(classify_property(&vc), PropertyKind::Safety);
    }

    #[test]
    fn test_classify_safety_arithmetic_overflow() {
        let vc = make_vc(VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (Ty::usize(), Ty::usize()),
        });
        assert_eq!(classify_property(&vc), PropertyKind::Safety);
    }

    #[test]
    fn test_classify_safety_index_out_of_bounds() {
        let vc = make_vc(VcKind::IndexOutOfBounds);
        assert_eq!(classify_property(&vc), PropertyKind::Safety);
    }

    #[test]
    fn test_classify_safety_assertion() {
        let vc = make_vc(VcKind::Assertion { message: "loop invariant".to_string() });
        assert_eq!(classify_property(&vc), PropertyKind::Safety);
    }

    #[test]
    fn test_classify_termination_non_termination() {
        let vc = make_vc(VcKind::NonTermination {
            context: "loop".to_string(),
            measure: "n".to_string(),
        });
        assert_eq!(classify_property(&vc), PropertyKind::Termination);
    }

    #[test]
    fn test_classify_liveness_temporal() {
        let vc =
            make_vc(VcKind::Temporal { property: "eventually done".to_string(), machine: None });
        assert_eq!(classify_property(&vc), PropertyKind::Liveness);
    }

    #[test]
    fn test_classify_liveness_fairness() {
        let vc = make_vc(VcKind::Fairness {
            constraint: FairnessConstraint::Strong {
                action: "sched".to_string(),
                vars: vec!["x".to_string()],
            },
        });
        assert_eq!(classify_property(&vc), PropertyKind::Liveness);
    }

    #[test]
    fn test_classify_partial_correctness_postcondition() {
        let vc = make_vc(VcKind::Postcondition);
        assert_eq!(classify_property(&vc), PropertyKind::PartialCorrectness);
    }

    #[test]
    fn test_classify_partial_correctness_precondition() {
        let vc = make_vc(VcKind::Precondition { callee: "foo".to_string() });
        assert_eq!(classify_property(&vc), PropertyKind::PartialCorrectness);
    }

    #[test]
    fn test_classify_safety_data_race() {
        let vc = make_vc(VcKind::DataRace {
            variable: "x".to_string(),
            thread_a: "t1".to_string(),
            thread_b: "t2".to_string(),
        });
        assert_eq!(classify_property(&vc), PropertyKind::Safety);
    }

    // -------------------------------------------------------------------
    // is_safety_only tests
    // -------------------------------------------------------------------

    #[test]
    fn test_pdr_is_safety_only() {
        assert!(is_safety_only("pdr"));
        assert!(is_safety_only("PDR"));
    }

    #[test]
    fn test_ic3_is_safety_only() {
        assert!(is_safety_only("ic3"));
        assert!(is_safety_only("IC3"));
    }

    #[test]
    fn test_k_induction_is_safety_only() {
        assert!(is_safety_only("k-induction"));
        assert!(is_safety_only("k_induction"));
        assert!(is_safety_only("K-Induction"));
    }

    #[test]
    fn test_bmc_is_safety_only() {
        assert!(is_safety_only("bmc"));
        assert!(is_safety_only("BMC"));
    }

    #[test]
    fn test_ay_chc_is_safety_only() {
        assert!(is_safety_only("ay-chc"));
    }

    #[test]
    fn test_clean_is_not_safety_only() {
        assert!(!is_safety_only("clean"));
    }

    #[test]
    fn test_ay_is_not_safety_only() {
        assert!(!is_safety_only("ay"));
    }

    // -------------------------------------------------------------------
    // validate_dispatch tests
    // -------------------------------------------------------------------

    #[test]
    fn test_validate_pdr_for_safety_is_valid() {
        let result = validate_dispatch(PropertyKind::Safety, "pdr");
        assert_eq!(result, DispatchValidity::Valid);
    }

    #[test]
    fn test_validate_pdr_for_termination_is_invalid() {
        let result = validate_dispatch(PropertyKind::Termination, "pdr");
        assert!(result.is_invalid(), "PDR must not handle termination: {result:?}");
    }

    #[test]
    fn test_validate_k_induction_for_termination_is_invalid() {
        let result = validate_dispatch(PropertyKind::Termination, "k-induction");
        assert!(result.is_invalid());
    }

    #[test]
    fn test_validate_bmc_for_termination_is_invalid() {
        let result = validate_dispatch(PropertyKind::Termination, "BMC");
        assert!(result.is_invalid());
    }

    #[test]
    fn test_validate_ic3_for_liveness_is_invalid() {
        let result = validate_dispatch(PropertyKind::Liveness, "ic3");
        assert!(result.is_invalid());
    }

    #[test]
    fn test_validate_clean_for_termination_is_valid() {
        let result = validate_dispatch(PropertyKind::Termination, "clean");
        assert_eq!(result, DispatchValidity::Valid);
    }

    #[test]
    fn test_validate_ay_for_termination_is_valid() {
        let result = validate_dispatch(PropertyKind::Termination, "ay");
        assert_eq!(result, DispatchValidity::Valid);
    }

    #[test]
    fn test_validate_trust_mc_for_termination_is_degraded() {
        let result = validate_dispatch(PropertyKind::Termination, "trust-mc");
        assert!(
            matches!(result, DispatchValidity::Degraded { .. }),
            "trust-mc can find bugs but not prove termination: {result:?}"
        );
    }

    #[test]
    fn test_validate_ty_for_liveness_is_valid() {
        let result = validate_dispatch(PropertyKind::Liveness, "ty");
        assert_eq!(result, DispatchValidity::Valid);
    }

    // -------------------------------------------------------------------
    // Integration: classify + validate roundtrip
    // -------------------------------------------------------------------

    #[test]
    fn test_non_termination_vc_rejected_by_all_safety_solvers() {
        let vc = make_vc(VcKind::NonTermination {
            context: "while loop".to_string(),
            measure: "n".to_string(),
        });
        let property = classify_property(&vc);
        assert_eq!(property, PropertyKind::Termination);

        let safety_solvers = ["pdr", "ic3", "k-induction", "bmc", "ay-chc"];
        for solver in safety_solvers {
            let validity = validate_dispatch(property, solver);
            assert!(
                validity.is_invalid(),
                "{solver} should be invalid for termination but got: {validity:?}"
            );
        }
    }

    #[test]
    fn test_safety_vc_accepted_by_all_solvers() {
        let vc = make_vc(VcKind::DivisionByZero);
        let property = classify_property(&vc);
        assert_eq!(property, PropertyKind::Safety);

        let all_solvers =
            ["pdr", "ic3", "k-induction", "bmc", "ay", "clean", "trust-mc", "trust-wp", "ty"];
        for solver in all_solvers {
            let validity = validate_dispatch(property, solver);
            assert_eq!(
                validity,
                DispatchValidity::Valid,
                "{solver} should be valid for safety but got: {validity:?}"
            );
        }
    }
}
