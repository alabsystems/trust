// Trust: Counterexample-guided spec refinement loop
//
// When verification fails with a counterexample, this module analyzes the witness
// values, identifies the weakness in the current specification, and proposes
// Formula-level refinements. The RefinementLoop orchestrates iterative refinement
// until convergence or a maximum iteration count is reached.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, Sort, VcKind, VerificationCondition};

// Trust: The analysis result from examining a counterexample against a failing VC.
/// Structured analysis of a counterexample produced by a failed verification attempt.
///
/// Captures the failing VC, the concrete witness values, and the identified
/// weakness in the current specification. Used by [`suggest_refinement`] to
/// produce actionable [`CexRefinementSuggestion`] values.
#[derive(Debug, Clone)]
#[must_use]
#[non_exhaustive]
pub struct CounterexampleAnalysis {
    /// The verification condition that failed.
    pub failing_vc: VerificationCondition,
    /// Concrete witness values from the solver (variable name -> value).
    pub witness_values: Vec<(String, i128)>,
    /// Identified weakness in the current specification.
    pub identified_weakness: SpecWeakness,
    /// Variables that appear to be inputs (from function parameters).
    pub input_variables: Vec<String>,
    /// Variables that appear to be derived (intermediates or outputs).
    pub derived_variables: Vec<String>,
}

// Trust: Classification of what is wrong with the current specification.
/// What kind of weakness the counterexample reveals in the specification.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum SpecWeakness {
    /// Precondition is too weak -- admits inputs that cause the property to fail.
    WeakPrecondition {
        /// Which variables need tighter constraints.
        variables: Vec<String>,
    },
    /// Postcondition is too strong -- claims a property that doesn't hold for all inputs.
    StrongPostcondition {
        /// The property clause that is violated.
        violated_clause: String,
    },
    /// Missing loop invariant that would be needed to prove the property.
    MissingInvariant {
        /// Description of the invariant gap.
        description: String,
    },
    /// Missing guard condition for a branch or operation.
    MissingGuard {
        /// The operation that needs guarding.
        operation: String,
    },
    /// The weakness could not be classified.
    Unknown,
}

// Trust: Formula-level refinement suggestions for the spec.
/// A suggested refinement to a specification, expressed as a [`Formula`].
///
/// Each variant corresponds to a different kind of spec change. The
/// [`Formula`] payload is a logical constraint that can be directly
/// integrated into the VC pipeline.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum CexRefinementSuggestion {
    /// Add a precondition constraint to exclude the failing input region.
    StrengthenPrecondition(Formula),
    /// Relax the postcondition to accommodate the counterexample behavior.
    WeakenPostcondition(Formula),
    /// Add a loop invariant that is needed for inductive reasoning.
    AddInvariant(Formula),
    /// Add a guard condition before a potentially-failing operation.
    AddGuard(Formula),
}

impl CexRefinementSuggestion {
    /// Extract the inner formula from any variant.
    #[must_use]
    pub fn formula(&self) -> &Formula {
        match self {
            Self::StrengthenPrecondition(f)
            | Self::WeakenPostcondition(f)
            | Self::AddInvariant(f)
            | Self::AddGuard(f) => f,
        }
    }

    /// Human-readable description of the refinement kind.
    #[must_use]
    pub fn kind_name(&self) -> &'static str {
        match self {
            Self::StrengthenPrecondition(_) => "StrengthenPrecondition",
            Self::WeakenPostcondition(_) => "WeakenPostcondition",
            Self::AddInvariant(_) => "AddInvariant",
            Self::AddGuard(_) => "AddGuard",
        }
    }
}

// Trust: Analyze a counterexample to identify the specification weakness.
/// Analyze a counterexample from a failed VC to produce a structured analysis.
///
/// Examines the witness values against the VC kind to determine what kind
/// of specification weakness the counterexample reveals.
///
/// # Arguments
/// * `vc` - The verification condition that failed
/// * `witness` - Concrete variable assignments from the solver counterexample
///
/// # Returns
/// A [`CounterexampleAnalysis`] describing the failure and its root cause.
pub fn analyze_counterexample(
    vc: &VerificationCondition,
    witness: &[(String, i128)],
) -> CounterexampleAnalysis {
    let (input_variables, derived_variables) = classify_variables(witness);
    let identified_weakness = identify_weakness(&vc.kind, witness, &input_variables);

    CounterexampleAnalysis {
        failing_vc: vc.clone(),
        witness_values: witness.to_vec(),
        identified_weakness,
        input_variables,
        derived_variables,
    }
}

// Trust: Suggest Formula-level refinements based on the analysis.
/// Produce refinement suggestions from a counterexample analysis.
///
/// Uses the identified weakness and witness values to generate one or more
/// [`CexRefinementSuggestion`] values, each containing a [`Formula`] that
/// addresses the weakness.
///
/// Suggestions are returned in priority order (most targeted first).
#[must_use]
pub fn suggest_refinement(analysis: &CounterexampleAnalysis) -> Vec<CexRefinementSuggestion> {
    let mut suggestions = Vec::new();

    match &analysis.identified_weakness {
        SpecWeakness::WeakPrecondition { variables } => {
            // Trust: Build precondition constraints from witness values
            for var in variables {
                if let Some(value) = find_witness_value(&analysis.witness_values, var) {
                    let constraint =
                        build_exclusion_constraint(var, value, &analysis.failing_vc.kind);
                    suggestions.push(CexRefinementSuggestion::StrengthenPrecondition(constraint));
                }
            }
            // Trust: If we found no specific constraints, add a generic exclusion
            if suggestions.is_empty() {
                let generic = build_generic_precondition(&analysis.witness_values);
                suggestions.push(CexRefinementSuggestion::StrengthenPrecondition(generic));
            }
        }
        SpecWeakness::StrongPostcondition { violated_clause } => {
            // Trust: Weaken by adding a guard to the postcondition
            let guard = build_postcondition_guard(&analysis.witness_values, violated_clause);
            suggestions.push(CexRefinementSuggestion::WeakenPostcondition(guard));
        }
        SpecWeakness::MissingInvariant { description: _ } => {
            // Trust: Suggest a candidate invariant from witness pattern
            let invariant = build_invariant_candidate(&analysis.witness_values);
            suggestions.push(CexRefinementSuggestion::AddInvariant(invariant));
        }
        SpecWeakness::MissingGuard { operation: _ } => {
            // Trust: Build a guard from the failing VC kind
            let guard = build_guard_from_vc(&analysis.failing_vc.kind, &analysis.witness_values);
            suggestions.push(CexRefinementSuggestion::AddGuard(guard));
        }
        SpecWeakness::Unknown => {
            // Trust: Fall back to excluding the exact witness point
            let exclusion = build_generic_precondition(&analysis.witness_values);
            suggestions.push(CexRefinementSuggestion::StrengthenPrecondition(exclusion));
        }
    }

    suggestions
}

// Trust: Outcome of a single refinement loop iteration.
/// Result of one iteration of the refinement loop.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum IterationResult {
    /// Verification succeeded -- no further refinement needed.
    Converged {
        /// Number of iterations it took.
        iterations: usize,
    },
    /// Refinement was applied and another iteration is needed.
    Refined {
        /// The analysis from this iteration.
        analysis: CounterexampleAnalysis,
        /// The suggestions produced.
        suggestions: Vec<CexRefinementSuggestion>,
    },
    /// Maximum iterations reached without convergence.
    MaxIterationsReached {
        /// Total iterations attempted.
        iterations: usize,
        /// The last analysis before giving up.
        last_analysis: CounterexampleAnalysis,
    },
    /// An error prevented further progress.
    Error {
        /// Description of what went wrong.
        message: String,
    },
}

// Trust: Trait for pluggable verification backends in the refinement loop.
/// Verification oracle for the refinement loop.
///
/// Implementations check whether a set of formulas (the current spec)
/// make a VC provable, and return either success or a counterexample.
pub trait RefineVerifier: Send + Sync {
    /// Attempt to verify the VC with the given additional preconditions.
    ///
    /// Returns `Ok(None)` if verification succeeds (no counterexample),
    /// or `Ok(Some(witness))` if a counterexample was found.
    /// Returns `Err` on infrastructure failure.
    fn verify_with_preconditions(
        &self,
        vc: &VerificationCondition,
        preconditions: &[Formula],
    ) -> Result<Option<Vec<(String, i128)>>, String>;
}

// Trust: The main refinement loop orchestrator.
/// Orchestrates iterative counterexample-guided spec refinement.
///
/// Given an initial failing VC and a verification oracle, the loop:
/// 1. Analyzes the counterexample
/// 2. Suggests refinements
/// 3. Applies them as additional preconditions
/// 4. Re-verifies
/// 5. Repeats until convergence or `max_iterations`
///
/// Tracks convergence by checking whether new counterexamples differ
/// from previous ones. If the same witness repeats, the loop detects
/// a cycle and stops.
#[derive(Debug)]
#[must_use]
pub struct RefinementLoop {
    /// Maximum number of refinement iterations before giving up.
    pub max_iterations: usize,
    /// Accumulated preconditions from all iterations.
    accumulated_preconditions: Vec<Formula>,
    /// History of witness values for cycle detection.
    witness_history: Vec<Vec<(String, i128)>>,
    /// Number of iterations completed so far.
    iterations_completed: usize,
}

impl RefinementLoop {
    /// Create a new refinement loop with the given iteration limit.
    pub fn new(max_iterations: usize) -> Self {
        Self {
            max_iterations,
            accumulated_preconditions: Vec::new(),
            witness_history: Vec::new(),
            iterations_completed: 0,
        }
    }

    /// Run the full refinement loop to convergence or exhaustion.
    ///
    /// # Arguments
    /// * `vc` - The verification condition to refine
    /// * `initial_witness` - The initial counterexample witness
    /// * `verifier` - The verification oracle
    ///
    /// # Returns
    /// An [`IterationResult`] describing the outcome.
    pub fn run(
        &mut self,
        vc: &VerificationCondition,
        initial_witness: &[(String, i128)],
        verifier: &dyn RefineVerifier,
    ) -> IterationResult {
        let mut current_witness = initial_witness.to_vec();

        for _iter in 0..self.max_iterations {
            self.iterations_completed += 1;

            // Trust: Check for cycles in witness history
            if self.is_cycle(&current_witness) {
                return IterationResult::MaxIterationsReached {
                    iterations: self.iterations_completed,
                    last_analysis: analyze_counterexample(vc, &current_witness),
                };
            }
            self.witness_history.push(current_witness.clone());

            // Trust: Analyze the counterexample
            let analysis = analyze_counterexample(vc, &current_witness);

            // Trust: Suggest refinements
            let suggestions = suggest_refinement(&analysis);
            if suggestions.is_empty() {
                return IterationResult::Error {
                    message: "No refinement suggestions produced".to_string(),
                };
            }

            // Trust: Apply suggestions as preconditions
            for suggestion in &suggestions {
                self.accumulated_preconditions.push(suggestion.formula().clone());
            }

            // Trust: Re-verify with accumulated preconditions
            match verifier.verify_with_preconditions(vc, &self.accumulated_preconditions) {
                Ok(None) => {
                    // Verification succeeded
                    return IterationResult::Converged { iterations: self.iterations_completed };
                }
                Ok(Some(new_witness)) => {
                    // New counterexample -- continue the loop
                    let result = IterationResult::Refined { analysis, suggestions };
                    current_witness = new_witness;
                    // Trust: Continue to next iteration (result is for logging)
                    let _ = result;
                }
                Err(msg) => {
                    return IterationResult::Error { message: msg };
                }
            }
        }

        IterationResult::MaxIterationsReached {
            iterations: self.iterations_completed,
            last_analysis: analyze_counterexample(vc, &current_witness),
        }
    }

    /// Get the accumulated preconditions from all iterations.
    #[must_use]
    pub fn preconditions(&self) -> &[Formula] {
        &self.accumulated_preconditions
    }

    /// Get the number of completed iterations.
    #[must_use]
    pub fn iterations_completed(&self) -> usize {
        self.iterations_completed
    }

    /// Reset the loop state for reuse.
    pub fn reset(&mut self) {
        self.accumulated_preconditions.clear();
        self.witness_history.clear();
        self.iterations_completed = 0;
    }

    // Trust: Cycle detection -- check if this witness has been seen before.
    fn is_cycle(&self, witness: &[(String, i128)]) -> bool {
        self.witness_history.iter().any(|prev| {
            prev.len() == witness.len() && prev.iter().zip(witness.iter()).all(|(a, b)| a == b)
        })
    }
}

impl Default for RefinementLoop {
    fn default() -> Self {
        Self::new(10)
    }
}

// ---------------------------------------------------------------------------
// Trust: Internal helpers
// ---------------------------------------------------------------------------

/// Classify variables as inputs or derived based on naming heuristics.
fn classify_variables(witness: &[(String, i128)]) -> (Vec<String>, Vec<String>) {
    let mut inputs = Vec::new();
    let mut derived = Vec::new();

    for (name, _) in witness {
        // Trust: Variables with common parameter-like names are inputs
        if is_input_variable(name) {
            inputs.push(name.clone());
        } else {
            derived.push(name.clone());
        }
    }

    (inputs, derived)
}

/// Heuristic: names that look like function parameters.
fn is_input_variable(name: &str) -> bool {
    // Trust: Single-letter variables, or common parameter names
    let lower = name.to_lowercase();
    name.len() <= 2
        || lower.starts_with("arg")
        || lower.starts_with("param")
        || lower == "n"
        || lower == "x"
        || lower == "y"
        || lower == "a"
        || lower == "b"
        || lower == "divisor"
        || lower == "index"
        || lower == "len"
        || lower == "size"
        || lower == "shift"
        || lower == "lhs"
        || lower == "rhs"
}

/// Find a witness value by variable name.
fn find_witness_value(witness: &[(String, i128)], var: &str) -> Option<i128> {
    witness.iter().find(|(name, _)| name == var).map(|(_, v)| *v)
}

/// Identify the specification weakness from the VC kind and witness.
fn identify_weakness(
    vc_kind: &VcKind,
    witness: &[(String, i128)],
    input_vars: &[String],
) -> SpecWeakness {
    match vc_kind {
        VcKind::ArithmeticOverflow { .. } => {
            // Trust: Overflow means inputs are too large -- weak precondition
            SpecWeakness::WeakPrecondition { variables: input_vars.to_vec() }
        }
        VcKind::DivisionByZero | VcKind::RemainderByZero => {
            // Trust: Division by zero means divisor needs a guard
            let divisor_var = witness.iter().find(|(_, v)| *v == 0).map(|(name, _)| name.clone());
            if let Some(var) = divisor_var {
                SpecWeakness::MissingGuard { operation: format!("division by {var}") }
            } else {
                SpecWeakness::WeakPrecondition { variables: input_vars.to_vec() }
            }
        }
        VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => {
            // Trust: OOB means index needs bounds constraint
            SpecWeakness::WeakPrecondition { variables: input_vars.to_vec() }
        }
        VcKind::Postcondition => {
            SpecWeakness::StrongPostcondition { violated_clause: "postcondition".to_string() }
        }
        // Trust: Assertions with "invariant" in the message suggest loop invariant issues
        VcKind::Assertion { message } if message.contains("invariant") => {
            SpecWeakness::MissingInvariant {
                description: format!("assertion invariant not preserved: {message}"),
            }
        }
        _ => {
            if !input_vars.is_empty() {
                SpecWeakness::WeakPrecondition { variables: input_vars.to_vec() }
            } else {
                SpecWeakness::Unknown
            }
        }
    }
}

/// Build a Formula constraint that excludes the region around the witness value.
fn build_exclusion_constraint(var: &str, value: i128, vc_kind: &VcKind) -> Formula {
    let var_formula = Formula::Var(var.to_string(), Sort::Int);

    match vc_kind {
        VcKind::ArithmeticOverflow { .. } => {
            // Trust: Constrain the variable to be less than the overflow boundary
            // If the witness is at or near MAX, constrain < MAX
            Formula::Lt(Box::new(var_formula), Box::new(Formula::Int(value)))
        }
        VcKind::DivisionByZero | VcKind::RemainderByZero => {
            // Trust: The divisor must be non-zero
            Formula::Not(Box::new(Formula::Eq(Box::new(var_formula), Box::new(Formula::Int(0)))))
        }
        VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => {
            // Trust: Index must be non-negative and less than length
            Formula::And(vec![
                Formula::Ge(
                    Box::new(Formula::Var(var.to_string(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
                Formula::Lt(
                    Box::new(Formula::Var(var.to_string(), Sort::Int)),
                    Box::new(Formula::Int(value)),
                ),
            ])
        }
        _ => {
            // Trust: Generic exclusion: var != witness_value
            Formula::Not(Box::new(Formula::Eq(
                Box::new(var_formula),
                Box::new(Formula::Int(value)),
            )))
        }
    }
}

/// Build a generic precondition excluding the exact witness point.
fn build_generic_precondition(witness: &[(String, i128)]) -> Formula {
    let exclusions: Vec<Formula> = witness
        .iter()
        .map(|(name, value)| {
            Formula::Not(Box::new(Formula::Eq(
                Box::new(Formula::Var(name.clone(), Sort::Int)),
                Box::new(Formula::Int(*value)),
            )))
        })
        .collect();

    if exclusions.len() == 1 {
        exclusions.into_iter().next().expect("invariant: len == 1")
    } else if exclusions.is_empty() {
        Formula::Bool(true)
    } else {
        Formula::And(exclusions)
    }
}

/// Build a guard that conditions the postcondition.
fn build_postcondition_guard(witness: &[(String, i128)], _violated_clause: &str) -> Formula {
    // Trust: Guard the postcondition by excluding the witness region
    // The weakened postcondition is: (NOT witness_condition) => original_post
    let witness_condition = build_witness_condition(witness);
    Formula::Implies(
        Box::new(Formula::Not(Box::new(witness_condition))),
        Box::new(Formula::Bool(true)), // placeholder for original postcondition
    )
}

/// Build a candidate invariant from the witness values.
fn build_invariant_candidate(witness: &[(String, i128)]) -> Formula {
    // Trust: Infer bounds from the witness values as a candidate invariant
    let mut bounds = Vec::new();
    for (name, value) in witness {
        if *value >= 0 {
            // Trust: Non-negative value suggests >= 0 invariant
            bounds.push(Formula::Ge(
                Box::new(Formula::Var(name.clone(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ));
        }
    }
    if bounds.is_empty() { Formula::Bool(true) } else { Formula::And(bounds) }
}

/// Build a guard formula from the VC kind and witness.
fn build_guard_from_vc(vc_kind: &VcKind, witness: &[(String, i128)]) -> Formula {
    match vc_kind {
        VcKind::DivisionByZero | VcKind::RemainderByZero => {
            // Trust: Guard: divisor != 0
            if let Some((name, _)) = witness.iter().find(|(_, v)| *v == 0) {
                Formula::Not(Box::new(Formula::Eq(
                    Box::new(Formula::Var(name.clone(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                )))
            } else {
                Formula::Bool(true)
            }
        }
        _ => build_generic_precondition(witness),
    }
}

/// Build a formula representing the exact witness point.
fn build_witness_condition(witness: &[(String, i128)]) -> Formula {
    let equalities: Vec<Formula> = witness
        .iter()
        .map(|(name, value)| {
            Formula::Eq(
                Box::new(Formula::Var(name.clone(), Sort::Int)),
                Box::new(Formula::Int(*value)),
            )
        })
        .collect();

    if equalities.len() == 1 {
        equalities.into_iter().next().expect("invariant: len == 1")
    } else if equalities.is_empty() {
        Formula::Bool(false)
    } else {
        Formula::And(equalities)
    }
}

// ---------------------------------------------------------------------------
// Trust: Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::{BinOp, Formula, SourceSpan, Ty, VcKind, VerificationCondition};

    use super::*;

    /// Helper to build a test VC.
    fn make_vc(kind: VcKind, function: &str) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: function.into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        }
    }

    // --- Test 1: analyze_counterexample identifies overflow weakness ---

    #[test]
    fn test_analyze_overflow_identifies_weak_precondition() {
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
        let witness = vec![("a".to_string(), i64::MAX as i128), ("b".to_string(), 1)];

        let analysis = analyze_counterexample(&vc, &witness);

        assert!(matches!(analysis.identified_weakness, SpecWeakness::WeakPrecondition { .. }));
        assert!(!analysis.input_variables.is_empty());
        assert_eq!(analysis.witness_values.len(), 2);
    }

    // --- Test 2: analyze_counterexample identifies division-by-zero guard ---

    #[test]
    fn test_analyze_div_zero_identifies_missing_guard() {
        let vc = make_vc(VcKind::DivisionByZero, "math::safe_divide");
        let witness = vec![("x".to_string(), 42), ("divisor".to_string(), 0)];

        let analysis = analyze_counterexample(&vc, &witness);

        assert!(matches!(analysis.identified_weakness, SpecWeakness::MissingGuard { .. }));
    }

    // --- Test 3: suggest_refinement produces precondition for overflow ---

    #[test]
    fn test_suggest_refinement_overflow_produces_precondition() {
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
        let witness = vec![("a".to_string(), i64::MAX as i128), ("b".to_string(), 1)];

        let analysis = analyze_counterexample(&vc, &witness);
        let suggestions = suggest_refinement(&analysis);

        assert!(!suggestions.is_empty());
        assert!(matches!(&suggestions[0], CexRefinementSuggestion::StrengthenPrecondition(_)));
        assert_eq!(suggestions[0].kind_name(), "StrengthenPrecondition");
    }

    // --- Test 4: suggest_refinement produces guard for division-by-zero ---

    #[test]
    fn test_suggest_refinement_div_zero_produces_guard() {
        let vc = make_vc(VcKind::DivisionByZero, "math::safe_divide");
        let witness = vec![("x".to_string(), 42), ("divisor".to_string(), 0)];

        let analysis = analyze_counterexample(&vc, &witness);
        let suggestions = suggest_refinement(&analysis);

        assert!(!suggestions.is_empty());
        assert!(matches!(&suggestions[0], CexRefinementSuggestion::AddGuard(_)));

        // Trust: The guard formula should be `divisor != 0`
        let formula = suggestions[0].formula();
        assert!(matches!(formula, Formula::Not(_)));
    }

    // --- Test 5: suggest_refinement for postcondition produces weakening ---

    #[test]
    fn test_suggest_refinement_postcondition_produces_weakening() {
        let vc = make_vc(VcKind::Postcondition, "math::compute");
        let witness = vec![("result".to_string(), -1)];

        let analysis = analyze_counterexample(&vc, &witness);
        let suggestions = suggest_refinement(&analysis);

        assert!(!suggestions.is_empty());
        assert!(matches!(&suggestions[0], CexRefinementSuggestion::WeakenPostcondition(_)));
    }

    // --- Test 6: RefinementLoop converges on first try ---

    #[test]
    fn test_refinement_loop_converges_immediately() {
        struct PassVerifier;
        impl RefineVerifier for PassVerifier {
            fn verify_with_preconditions(
                &self,
                _vc: &VerificationCondition,
                _preconditions: &[Formula],
            ) -> Result<Option<Vec<(String, i128)>>, String> {
                Ok(None) // Always passes
            }
        }

        let vc = make_vc(VcKind::DivisionByZero, "f");
        let witness = vec![("d".to_string(), 0)];

        let mut refinement_loop = RefinementLoop::new(5);
        let result = refinement_loop.run(&vc, &witness, &PassVerifier);

        assert!(matches!(result, IterationResult::Converged { iterations: 1 }));
        assert_eq!(refinement_loop.iterations_completed(), 1);
        assert!(!refinement_loop.preconditions().is_empty());
    }

    // --- Test 7: RefinementLoop converges after two iterations ---

    #[test]
    fn test_refinement_loop_converges_after_two_iterations() {
        struct FailThenPassVerifier {
            call_count: std::sync::atomic::AtomicUsize,
        }
        impl RefineVerifier for FailThenPassVerifier {
            fn verify_with_preconditions(
                &self,
                _vc: &VerificationCondition,
                _preconditions: &[Formula],
            ) -> Result<Option<Vec<(String, i128)>>, String> {
                let count = self.call_count.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                if count == 0 {
                    // First call: return a different counterexample
                    Ok(Some(vec![("d".to_string(), 0), ("extra".to_string(), 5)]))
                } else {
                    Ok(None) // Pass on second call
                }
            }
        }

        let vc = make_vc(VcKind::DivisionByZero, "f");
        let witness = vec![("d".to_string(), 0)];

        let verifier = FailThenPassVerifier { call_count: std::sync::atomic::AtomicUsize::new(0) };

        let mut refinement_loop = RefinementLoop::new(5);
        let result = refinement_loop.run(&vc, &witness, &verifier);

        assert!(matches!(result, IterationResult::Converged { iterations: 2 }));
        assert_eq!(refinement_loop.iterations_completed(), 2);
    }

    // --- Test 8: RefinementLoop stops at max iterations ---

    #[test]
    fn test_refinement_loop_max_iterations() {
        struct AlwaysFailVerifier {
            call_count: std::sync::atomic::AtomicUsize,
        }
        impl RefineVerifier for AlwaysFailVerifier {
            fn verify_with_preconditions(
                &self,
                _vc: &VerificationCondition,
                _preconditions: &[Formula],
            ) -> Result<Option<Vec<(String, i128)>>, String> {
                let count = self.call_count.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                // Return different counterexamples each time
                Ok(Some(vec![("x".to_string(), count as i128 + 1)]))
            }
        }

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
        let witness = vec![("x".to_string(), 100)];

        let verifier = AlwaysFailVerifier { call_count: std::sync::atomic::AtomicUsize::new(0) };

        let mut refinement_loop = RefinementLoop::new(3);
        let result = refinement_loop.run(&vc, &witness, &verifier);

        assert!(matches!(result, IterationResult::MaxIterationsReached { iterations: 3, .. }));
    }

    // --- Test 9: RefinementLoop detects cycles ---

    #[test]
    fn test_refinement_loop_detects_cycle() {
        struct CyclingVerifier;
        impl RefineVerifier for CyclingVerifier {
            fn verify_with_preconditions(
                &self,
                _vc: &VerificationCondition,
                _preconditions: &[Formula],
            ) -> Result<Option<Vec<(String, i128)>>, String> {
                // Always return the same counterexample -> cycle
                Ok(Some(vec![("x".to_string(), 42)]))
            }
        }

        let vc = make_vc(VcKind::DivisionByZero, "f");
        let witness = vec![("x".to_string(), 42)];

        let mut refinement_loop = RefinementLoop::new(10);
        let result = refinement_loop.run(&vc, &witness, &CyclingVerifier);

        // Trust: The first witness is added to history, then the verifier
        // returns the same witness, which triggers cycle detection on iteration 2.
        assert!(matches!(result, IterationResult::MaxIterationsReached { .. }));
        // Should stop early due to cycle, not reach max_iterations
        assert!(refinement_loop.iterations_completed() < 10);
    }

    // --- Test 10: RefinementLoop handles verifier errors ---

    #[test]
    fn test_refinement_loop_handles_verifier_error() {
        struct ErrorVerifier;
        impl RefineVerifier for ErrorVerifier {
            fn verify_with_preconditions(
                &self,
                _vc: &VerificationCondition,
                _preconditions: &[Formula],
            ) -> Result<Option<Vec<(String, i128)>>, String> {
                Err("solver timeout".to_string())
            }
        }

        let vc = make_vc(VcKind::DivisionByZero, "f");
        let witness = vec![("d".to_string(), 0)];

        let mut refinement_loop = RefinementLoop::new(5);
        let result = refinement_loop.run(&vc, &witness, &ErrorVerifier);

        assert!(matches!(result, IterationResult::Error { .. }));
        if let IterationResult::Error { message } = result {
            assert_eq!(message, "solver timeout");
        }
    }

    // --- Test 11: CexRefinementSuggestion formula() accessor ---

    #[test]
    fn test_refinement_suggestion_formula_accessor() {
        let formula = Formula::Bool(true);
        let suggestion = CexRefinementSuggestion::StrengthenPrecondition(formula.clone());

        assert_eq!(*suggestion.formula(), formula);
        assert_eq!(suggestion.kind_name(), "StrengthenPrecondition");

        let guard = CexRefinementSuggestion::AddGuard(Formula::Int(42));
        assert_eq!(*guard.formula(), Formula::Int(42));
        assert_eq!(guard.kind_name(), "AddGuard");
    }

    // --- Test 12: Variable classification works for common names ---

    #[test]
    fn test_variable_classification() {
        let witness = vec![
            ("a".to_string(), 1),
            ("b".to_string(), 2),
            ("_tmp_3".to_string(), 3),
            ("index".to_string(), 4),
            ("result_intermediate".to_string(), 5),
        ];

        let (inputs, derived) = classify_variables(&witness);

        // "a", "b", "index" should be classified as inputs
        assert!(inputs.contains(&"a".to_string()));
        assert!(inputs.contains(&"b".to_string()));
        assert!(inputs.contains(&"index".to_string()));

        // "_tmp_3" and "result_intermediate" should be derived
        assert!(derived.contains(&"_tmp_3".to_string()));
        assert!(derived.contains(&"result_intermediate".to_string()));
    }

    // --- Test 13: RefinementLoop reset clears state ---

    #[test]
    fn test_refinement_loop_reset() {
        let mut refinement_loop = RefinementLoop::new(5);
        refinement_loop.accumulated_preconditions.push(Formula::Bool(true));
        refinement_loop.witness_history.push(vec![("x".to_string(), 1)]);
        refinement_loop.iterations_completed = 3;

        refinement_loop.reset();

        assert!(refinement_loop.preconditions().is_empty());
        assert_eq!(refinement_loop.iterations_completed(), 0);
    }

    // --- Test 14: build_exclusion_constraint for various VC kinds ---

    #[test]
    fn test_build_exclusion_constraint_overflow() {
        let constraint = build_exclusion_constraint(
            "x",
            i64::MAX as i128,
            &VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (
                    Ty::Int { width: 64, signed: false },
                    Ty::Int { width: 64, signed: false },
                ),
            },
        );

        // Should produce x < MAX
        assert!(matches!(constraint, Formula::Lt(_, _)));
    }

    #[test]
    fn test_build_exclusion_constraint_div_zero() {
        let constraint = build_exclusion_constraint("divisor", 0, &VcKind::DivisionByZero);

        // Should produce NOT(divisor == 0)
        assert!(matches!(constraint, Formula::Not(_)));
    }

    // --- Test 15: Postcondition weakness produces Implies formula ---

    #[test]
    fn test_postcondition_guard_produces_implies() {
        let guard = build_postcondition_guard(&[("result".to_string(), -1)], "result > 0");

        assert!(matches!(guard, Formula::Implies(_, _)));
    }
}
