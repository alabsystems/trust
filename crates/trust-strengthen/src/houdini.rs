// Trust: Houdini conjunctive refinement for invariant inference
//
// Implements the Houdini algorithm: start with the conjunction of ALL candidate
// invariants, check each against counterexamples from the solver, remove any
// invariant that is violated, and repeat until a fixed point is reached.
//
// The result is the maximal consistent conjunction of candidates.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::Formula;
use trust_types::fx::FxHashMap;

// ---------------------------------------------------------------------------
// Counterexample representation
// ---------------------------------------------------------------------------

/// A counterexample: concrete variable assignments that witness a violation.
#[derive(Debug, Clone)]
pub struct Counterexample {
    /// Variable name to concrete value mappings.
    pub assignments: Vec<(String, i128)>,
}

// ---------------------------------------------------------------------------
// Houdini verifier trait
// ---------------------------------------------------------------------------

/// Oracle that checks whether a conjunction of candidate formulas is valid.
///
/// Returns `Ok(None)` when the conjunction holds (no counterexample found),
/// or `Ok(Some(cex))` when a counterexample falsifies at least one candidate.
pub trait HoudiniVerifier: Send + Sync {
    /// Check the conjunction of the given candidate formulas.
    ///
    /// The verifier should check whether the conjunction of all `candidates`
    /// is consistent with the program semantics. If not, it returns a
    /// counterexample that falsifies at least one candidate.
    fn check_conjunction(
        &self,
        candidates: &[Formula],
    ) -> Result<Option<Counterexample>, HoudiniError>;
}

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors that can occur during Houdini refinement.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum HoudiniError {
    /// The solver returned an error.
    #[error("solver error: {0}")]
    SolverError(String),
    /// Maximum iterations reached without convergence.
    #[error("max iterations ({0}) reached without convergence")]
    MaxIterations(usize),
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for the Houdini refinement loop.
#[derive(Debug, Clone)]
pub struct HoudiniConfig {
    /// Maximum number of refinement iterations before giving up.
    pub max_iterations: usize,
}

impl Default for HoudiniConfig {
    fn default() -> Self {
        Self { max_iterations: 100 }
    }
}

// ---------------------------------------------------------------------------
// Refinement result
// ---------------------------------------------------------------------------

/// Result of running the Houdini refinement algorithm.
#[derive(Debug, Clone)]
pub struct HoudiniResult {
    /// The surviving candidate formulas (maximal consistent conjunction).
    pub surviving: Vec<Formula>,
    /// Indices of candidates that were removed (into the original input slice).
    pub removed_indices: Vec<usize>,
    /// Number of refinement iterations performed.
    pub iterations: usize,
    /// Whether the algorithm reached a true fixed point (vs. hitting max iterations).
    pub converged: bool,
}

// ---------------------------------------------------------------------------
// HoudiniRefiner
// ---------------------------------------------------------------------------

/// Houdini conjunctive refinement engine.
///
/// Given a set of candidate invariants (as [`Formula`] values), iteratively
/// removes candidates that are falsified by solver counterexamples until
/// the remaining conjunction is consistent (fixed point) or the candidate
/// set is empty.
///
/// # Algorithm
///
/// 1. Start with `alive = {0, 1, ..., n-1}` (all candidate indices).
/// 2. Ask the verifier to check the conjunction of alive candidates.
/// 3. If no counterexample: **converged** -- return alive candidates.
/// 4. If counterexample `cex`: evaluate each alive candidate against `cex`,
///    remove any candidate that `cex` falsifies.
/// 5. If nothing was removed (cex doesn't falsify any individual candidate):
///    treat as convergence failure and stop.
/// 6. Repeat from step 2 until convergence or `max_iterations`.
#[derive(Debug, Clone)]
pub struct HoudiniRefiner {
    config: HoudiniConfig,
}

impl HoudiniRefiner {
    /// Create a new refiner with the given configuration.
    #[must_use]
    pub fn new(config: HoudiniConfig) -> Self {
        Self { config }
    }

    /// Create a refiner with default configuration.
    #[must_use]
    pub fn with_defaults() -> Self {
        Self { config: HoudiniConfig::default() }
    }

    /// Run the Houdini refinement loop.
    ///
    /// # Arguments
    /// * `candidates` - The initial set of candidate invariant formulas.
    /// * `verifier` - The verification oracle that checks conjunctions and
    ///   returns counterexamples.
    ///
    /// # Returns
    /// A [`HoudiniResult`] containing the maximal consistent conjunction.
    pub fn refine(
        &self,
        candidates: &[Formula],
        verifier: &dyn HoudiniVerifier,
    ) -> Result<HoudiniResult, HoudiniError> {
        if candidates.is_empty() {
            return Ok(HoudiniResult {
                surviving: Vec::new(),
                removed_indices: Vec::new(),
                iterations: 0,
                converged: true,
            });
        }

        // Track which candidates are still alive by index.
        let mut alive: Vec<bool> = vec![true; candidates.len()];
        let mut removed_indices: Vec<usize> = Vec::new();
        let mut iterations = 0;

        #[allow(clippy::explicit_counter_loop)]
        for _ in 0..self.config.max_iterations {
            // Collect alive candidate formulas.
            let alive_formulas: Vec<Formula> = alive
                .iter()
                .enumerate()
                .filter_map(
                    |(i, &is_alive)| {
                        if is_alive { Some(candidates[i].clone()) } else { None }
                    },
                )
                .collect();

            if alive_formulas.is_empty() {
                // All candidates removed -- trivially converged.
                return Ok(HoudiniResult {
                    surviving: Vec::new(),
                    removed_indices,
                    iterations,
                    converged: true,
                });
            }

            iterations += 1;

            // Ask verifier to check the conjunction.
            let check_result = verifier.check_conjunction(&alive_formulas)?;

            match check_result {
                None => {
                    // No counterexample: conjunction is valid -- fixed point reached.
                    return Ok(HoudiniResult {
                        surviving: alive_formulas,
                        removed_indices,
                        iterations,
                        converged: true,
                    });
                }
                Some(cex) => {
                    // Counterexample found: remove falsified candidates.
                    let falsified: Vec<usize> = (0..alive.len())
                        .filter(|&i| alive[i] && is_falsified_by(&candidates[i], &cex))
                        .collect();
                    for &i in &falsified {
                        alive[i] = false;
                        removed_indices.push(i);
                    }
                    let any_removed = !falsified.is_empty();

                    if !any_removed {
                        // Counterexample doesn't falsify any individual candidate.
                        // This means the conjunction is inconsistent in a way that
                        // can't be resolved by removing individual conjuncts.
                        // Return current state as best effort.
                        return Ok(HoudiniResult {
                            surviving: alive_formulas,
                            removed_indices,
                            iterations,
                            converged: false,
                        });
                    }
                }
            }
        }

        Err(HoudiniError::MaxIterations(self.config.max_iterations))
    }
}

// ---------------------------------------------------------------------------
// Formula evaluation against counterexamples
// ---------------------------------------------------------------------------

/// Check whether a formula is falsified by a counterexample.
///
/// Evaluates the formula under the concrete variable assignments in the
/// counterexample. Returns `true` if the formula evaluates to `false`
/// (i.e., the counterexample violates this candidate invariant).
///
/// Builds a `HashMap` from the counterexample assignments for O(1) variable
/// lookup instead of the previous O(n) linear scan per variable reference.
#[must_use]
pub(crate) fn is_falsified_by(formula: &Formula, cex: &Counterexample) -> bool {
    let assignments: FxHashMap<&str, i128> =
        cex.assignments.iter().map(|(name, val)| (name.as_str(), *val)).collect();
    match eval_formula(formula, &assignments) {
        Some(false) => true, // Definitely false -> falsified.
        _ => false,          // True or unknown -> not falsified.
    }
}

/// Evaluate a formula under concrete variable assignments.
///
/// Returns `Some(true)` / `Some(false)` when the formula can be fully
/// evaluated, or `None` when a variable is missing from the assignments.
fn eval_formula(formula: &Formula, assignments: &FxHashMap<&str, i128>) -> Option<bool> {
    match formula {
        Formula::Bool(b) => Some(*b),

        // Variable lookup -- treat as an integer value, truthy if non-zero.
        Formula::Var(name, _) => assignments.get(name.as_str()).map(|v| *v != 0),

        // Boolean connectives
        Formula::Not(inner) => eval_formula(inner, assignments).map(|b| !b),
        Formula::And(conjuncts) => {
            let mut result = true;
            for c in conjuncts {
                match eval_formula(c, assignments) {
                    Some(false) => return Some(false),
                    Some(true) => {}
                    None => result = true, // Optimistic: unknown conjuncts don't falsify.
                }
            }
            Some(result)
        }
        Formula::Or(disjuncts) => {
            let mut all_known = true;
            for d in disjuncts {
                match eval_formula(d, assignments) {
                    Some(true) => return Some(true),
                    Some(false) => {}
                    None => all_known = false,
                }
            }
            if all_known { Some(false) } else { None }
        }
        Formula::Implies(lhs, rhs) => {
            match (eval_formula(lhs, assignments), eval_formula(rhs, assignments)) {
                (Some(false), _) => Some(true),
                (_, Some(true)) => Some(true),
                (Some(true), Some(false)) => Some(false),
                _ => None,
            }
        }

        // Comparisons
        Formula::Eq(a, b) => {
            let (va, vb) = (eval_int(a, assignments)?, eval_int(b, assignments)?);
            Some(va == vb)
        }
        Formula::Lt(a, b) => {
            let (va, vb) = (eval_int(a, assignments)?, eval_int(b, assignments)?);
            Some(va < vb)
        }
        Formula::Le(a, b) => {
            let (va, vb) = (eval_int(a, assignments)?, eval_int(b, assignments)?);
            Some(va <= vb)
        }
        Formula::Gt(a, b) => {
            let (va, vb) = (eval_int(a, assignments)?, eval_int(b, assignments)?);
            Some(va > vb)
        }
        Formula::Ge(a, b) => {
            let (va, vb) = (eval_int(a, assignments)?, eval_int(b, assignments)?);
            Some(va >= vb)
        }

        // For formulas we can't evaluate (arithmetic, bitvectors, quantifiers, etc.),
        // conservatively return None (unknown).
        _ => None,
    }
}

/// Evaluate a formula as an integer value under concrete assignments.
fn eval_int(formula: &Formula, assignments: &FxHashMap<&str, i128>) -> Option<i128> {
    match formula {
        Formula::Int(v) => Some(*v),
        Formula::UInt(v) => Some(*v as i128),
        Formula::Var(name, _) => assignments.get(name.as_str()).copied(),
        Formula::Add(a, b) => Some(eval_int(a, assignments)? + eval_int(b, assignments)?),
        Formula::Sub(a, b) => Some(eval_int(a, assignments)? - eval_int(b, assignments)?),
        Formula::Mul(a, b) => Some(eval_int(a, assignments)? * eval_int(b, assignments)?),
        Formula::Neg(a) => eval_int(a, assignments).map(|v| -v),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::Sort;

    use super::*;

    /// A test verifier that returns counterexamples from a pre-configured list.
    struct MockVerifier {
        /// Each call to `check_conjunction` pops the next response.
        responses: std::sync::Mutex<Vec<Option<Counterexample>>>,
    }

    impl MockVerifier {
        fn new(responses: Vec<Option<Counterexample>>) -> Self {
            Self { responses: std::sync::Mutex::new(responses) }
        }
    }

    impl HoudiniVerifier for MockVerifier {
        fn check_conjunction(
            &self,
            _candidates: &[Formula],
        ) -> Result<Option<Counterexample>, HoudiniError> {
            let mut responses = self.responses.lock().unwrap();
            if responses.is_empty() {
                // No more counterexamples -- conjunction is valid.
                Ok(None)
            } else {
                Ok(responses.remove(0))
            }
        }
    }

    fn var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }

    /// Helper: build `x >= 0`.
    fn x_ge_0() -> Formula {
        Formula::Ge(Box::new(var("x")), Box::new(Formula::Int(0)))
    }

    /// Helper: build `x < 100`.
    fn x_lt_100() -> Formula {
        Formula::Lt(Box::new(var("x")), Box::new(Formula::Int(100)))
    }

    /// Helper: build `y > 0`.
    fn y_gt_0() -> Formula {
        Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(0)))
    }

    // -----------------------------------------------------------------------
    // Scenario 1: All candidates are valid (no counterexample on first check)
    // -----------------------------------------------------------------------

    #[test]
    fn test_all_valid() {
        let candidates = vec![x_ge_0(), x_lt_100(), y_gt_0()];
        let verifier = MockVerifier::new(vec![
            None, // First check: no counterexample -> all valid.
        ]);

        let refiner = HoudiniRefiner::with_defaults();
        let result = refiner.refine(&candidates, &verifier).expect("should succeed");

        assert!(result.converged);
        assert_eq!(result.surviving.len(), 3);
        assert!(result.removed_indices.is_empty());
        assert_eq!(result.iterations, 1);
    }

    // -----------------------------------------------------------------------
    // Scenario 2: All candidates falsified in one iteration
    // -----------------------------------------------------------------------

    #[test]
    fn test_all_falsified() {
        let candidates = vec![x_ge_0(), x_lt_100(), y_gt_0()];
        // Counterexample: x = -5, y = -1 falsifies x >= 0 and y > 0.
        // Then x < 100 remains, but next cex x = 200 falsifies it.
        let verifier = MockVerifier::new(vec![
            Some(Counterexample {
                assignments: vec![("x".to_string(), -5), ("y".to_string(), -1)],
            }),
            Some(Counterexample {
                assignments: vec![("x".to_string(), 200), ("y".to_string(), 5)],
            }),
        ]);

        let refiner = HoudiniRefiner::with_defaults();
        let result = refiner.refine(&candidates, &verifier).expect("should succeed");

        assert!(result.converged);
        assert!(result.surviving.is_empty());
        assert_eq!(result.removed_indices.len(), 3);
        assert_eq!(result.iterations, 2);
    }

    // -----------------------------------------------------------------------
    // Scenario 3: Partial refinement -- some survive, some are removed
    // -----------------------------------------------------------------------

    #[test]
    fn test_partial_refinement() {
        let candidates = vec![x_ge_0(), x_lt_100(), y_gt_0()];
        // Counterexample: x = -1, y = 5 falsifies x >= 0 only.
        // After removing x >= 0, the remaining conjunction is valid.
        let verifier = MockVerifier::new(vec![
            Some(Counterexample { assignments: vec![("x".to_string(), -1), ("y".to_string(), 5)] }),
            None, // Second check: remaining candidates are valid.
        ]);

        let refiner = HoudiniRefiner::with_defaults();
        let result = refiner.refine(&candidates, &verifier).expect("should succeed");

        assert!(result.converged);
        assert_eq!(result.surviving.len(), 2);
        assert_eq!(result.removed_indices, vec![0]); // x >= 0 removed.
        assert_eq!(result.iterations, 2);
    }

    // -----------------------------------------------------------------------
    // Scenario 4: Empty candidate set
    // -----------------------------------------------------------------------

    #[test]
    fn test_empty_candidates() {
        let candidates: Vec<Formula> = vec![];
        let verifier = MockVerifier::new(vec![]);

        let refiner = HoudiniRefiner::with_defaults();
        let result = refiner.refine(&candidates, &verifier).expect("should succeed");

        assert!(result.converged);
        assert!(result.surviving.is_empty());
        assert_eq!(result.iterations, 0);
    }

    // -----------------------------------------------------------------------
    // Scenario 5: Fixed-point with multiple iterations
    // -----------------------------------------------------------------------

    #[test]
    fn test_multi_iteration_convergence() {
        // 3 candidates; remove one per iteration over 3 rounds, then converge.
        let candidates = vec![x_ge_0(), x_lt_100(), y_gt_0()];

        let verifier = MockVerifier::new(vec![
            // Iter 1: falsifies y > 0
            Some(Counterexample {
                assignments: vec![("x".to_string(), 50), ("y".to_string(), -1)],
            }),
            // Iter 2: falsifies x < 100
            Some(Counterexample {
                assignments: vec![("x".to_string(), 200), ("y".to_string(), 10)],
            }),
            // Iter 3: x >= 0 is valid
            None,
        ]);

        let refiner = HoudiniRefiner::with_defaults();
        let result = refiner.refine(&candidates, &verifier).expect("should succeed");

        assert!(result.converged);
        assert_eq!(result.surviving.len(), 1);
        // y > 0 (index 2) removed first, then x < 100 (index 1).
        assert!(result.removed_indices.contains(&2));
        assert!(result.removed_indices.contains(&1));
        assert_eq!(result.iterations, 3);
    }

    // -----------------------------------------------------------------------
    // Scenario 6: Max iterations reached
    // -----------------------------------------------------------------------

    #[test]
    fn test_max_iterations() {
        let candidates = vec![x_ge_0()];
        // Verifier always returns a cex that doesn't falsify the candidate
        // (variable not in formula => unknown => not falsified).
        let verifier = MockVerifier::new(vec![
            Some(Counterexample { assignments: vec![("z".to_string(), -1)] }),
            Some(Counterexample { assignments: vec![("z".to_string(), -2)] }),
            Some(Counterexample { assignments: vec![("z".to_string(), -3)] }),
        ]);

        let config = HoudiniConfig { max_iterations: 3 };
        let refiner = HoudiniRefiner::new(config);
        let result = refiner.refine(&candidates, &verifier);

        // The first cex doesn't falsify x>=0 (z is irrelevant), so converged=false
        // is returned immediately on first iteration.
        match result {
            Ok(r) => {
                assert!(!r.converged);
                assert_eq!(r.surviving.len(), 1);
            }
            Err(HoudiniError::MaxIterations(_)) => {
                // Also acceptable.
            }
            Err(e) => panic!("unexpected error: {e}"),
        }
    }

    // -----------------------------------------------------------------------
    // Scenario 7: Solver error propagation
    // -----------------------------------------------------------------------

    #[test]
    fn test_solver_error() {
        struct FailVerifier;
        impl HoudiniVerifier for FailVerifier {
            fn check_conjunction(
                &self,
                _: &[Formula],
            ) -> Result<Option<Counterexample>, HoudiniError> {
                Err(HoudiniError::SolverError("timeout".to_string()))
            }
        }

        let candidates = vec![x_ge_0()];
        let refiner = HoudiniRefiner::with_defaults();
        let result = refiner.refine(&candidates, &FailVerifier);

        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), HoudiniError::SolverError(_)));
    }

    // -----------------------------------------------------------------------
    // Formula evaluation unit tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_eval_ge_true() {
        let f = x_ge_0();
        let cex = Counterexample { assignments: vec![("x".to_string(), 5)] };
        assert!(!is_falsified_by(&f, &cex));
    }

    #[test]
    fn test_eval_ge_false() {
        let f = x_ge_0();
        let cex = Counterexample { assignments: vec![("x".to_string(), -1)] };
        assert!(is_falsified_by(&f, &cex));
    }

    #[test]
    fn test_eval_and_partial_false() {
        let f = Formula::And(vec![x_ge_0(), y_gt_0()]);
        let cex = Counterexample { assignments: vec![("x".to_string(), 5), ("y".to_string(), -1)] };
        assert!(is_falsified_by(&f, &cex));
    }

    #[test]
    fn test_eval_implies_false() {
        // x >= 0 => x < 100. Falsified when x = 200.
        let f = Formula::Implies(Box::new(x_ge_0()), Box::new(x_lt_100()));
        let cex = Counterexample { assignments: vec![("x".to_string(), 200)] };
        assert!(is_falsified_by(&f, &cex));
    }

    #[test]
    fn test_eval_unknown_variable() {
        let f = x_ge_0();
        let cex = Counterexample {
            assignments: vec![("z".to_string(), -1)], // x not in assignments
        };
        // Unknown -> not falsified (conservative).
        assert!(!is_falsified_by(&f, &cex));
    }
}
