// Trust: ICE (Implication CounterExample) guided learning for invariant inference
//
// Implements the ICE learning algorithm from Garg et al. (2014) "ICE: A Robust
// Framework for Learning Invariants". Maintains three kinds of counterexamples:
//   - Positive: states that must satisfy the invariant (reachable safe states)
//   - Negative: states that must NOT satisfy the invariant (error states)
//   - Implication: state pairs (s, s') where if s satisfies the invariant,
//     s' must also satisfy it (consecutive loop iterations)
//
// Uses a decision-tree-style classifier to separate positive from negative
// while respecting implication constraints, then converts the classifier
// into a Formula.
//
// Reference: trust-vc-core invariant_inference.rs (ICE section)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;

use trust_types::{Formula, Sort};

use crate::houdini::Counterexample;

// ---------------------------------------------------------------------------
// Example types
// ---------------------------------------------------------------------------

/// A concrete program state: variable name to integer value.
#[derive(Debug, Clone, PartialEq)]
pub struct ConcreteState {
    /// Variable assignments in this state.
    pub assignments: Vec<(String, i128)>,
}

impl ConcreteState {
    /// Create a new concrete state from variable assignments.
    #[must_use]
    pub fn new(assignments: Vec<(String, i128)>) -> Self {
        Self { assignments }
    }

    /// Look up a variable value.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<i128> {
        self.assignments.iter().find(|(n, _)| n == name).map(|(_, v)| *v)
    }
}

/// An implication example: if the invariant holds at `pre`, it must hold at `post`.
#[derive(Debug, Clone)]
pub struct ImplicationExample {
    /// The pre-transition state.
    pub pre: ConcreteState,
    /// The post-transition state.
    pub post: ConcreteState,
}

// ---------------------------------------------------------------------------
// Feature (split predicate)
// ---------------------------------------------------------------------------

/// A split predicate used in the decision tree: `var <= threshold`.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct SplitPredicate {
    /// Variable name.
    pub(crate) var: String,
    /// Threshold value for the split.
    pub(crate) threshold: i128,
}

impl SplitPredicate {
    /// Evaluate this predicate on a state.
    #[must_use]
    pub(crate) fn evaluate(&self, state: &ConcreteState) -> Option<bool> {
        state.get(&self.var).map(|v| v <= self.threshold)
    }

    /// Convert the true branch (var <= threshold) to a Formula.
    #[must_use]
    pub(crate) fn to_le_formula(&self) -> Formula {
        Formula::Le(
            Box::new(Formula::Var(self.var.clone(), Sort::Int)),
            Box::new(Formula::Int(self.threshold)),
        )
    }

    /// Convert the false branch (var > threshold) to a Formula.
    #[must_use]
    pub(crate) fn to_gt_formula(&self) -> Formula {
        Formula::Gt(
            Box::new(Formula::Var(self.var.clone(), Sort::Int)),
            Box::new(Formula::Int(self.threshold)),
        )
    }
}

// ---------------------------------------------------------------------------
// ICE error type
// ---------------------------------------------------------------------------

/// Errors that can occur during ICE learning.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum IceError {
    /// No positive examples provided -- cannot learn an invariant.
    #[error("no positive examples provided")]
    NoPositiveExamples,
    /// No negative examples provided -- invariant is trivially true.
    #[error("no negative examples provided")]
    NoNegativeExamples,
    /// Failed to find a consistent classifier within the iteration limit.
    #[error("max iterations ({0}) reached without convergence")]
    MaxIterations(usize),
    /// No variables found in the example states.
    #[error("no variables found in example states")]
    NoVariables,
    /// The solver returned an error during verification.
    #[error("solver error: {0}")]
    SolverError(String),
}

// ---------------------------------------------------------------------------
// ICE verifier trait
// ---------------------------------------------------------------------------

/// Oracle for the ICE learning loop.
///
/// Checks a candidate invariant and returns a counterexample classified as
/// positive, negative, or implication.
pub trait IceVerifier: Send + Sync {
    /// Check the candidate invariant against the program.
    ///
    /// Returns:
    /// - `Ok(None)` if the invariant is sufficient (inductive + safe).
    /// - `Ok(Some(IceCounterexample))` if the invariant is insufficient.
    /// - `Err(IceError)` on solver failure.
    fn check_invariant(&self, candidate: &Formula) -> Result<Option<IceCounterexample>, IceError>;
}

/// A counterexample returned by the ICE verifier, classified by kind.
#[derive(Debug, Clone)]
pub enum IceCounterexample {
    /// A reachable state that must satisfy the invariant but doesn't.
    Positive(ConcreteState),
    /// An error state that must not satisfy the invariant but does.
    Negative(ConcreteState),
    /// A transition pair: if the invariant holds at pre, it must hold at post.
    Implication(ImplicationExample),
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for the ICE learner.
#[derive(Debug, Clone)]
pub struct IceConfig {
    /// Maximum number of learning iterations.
    pub max_iterations: usize,
    /// Maximum depth of the decision tree classifier.
    pub max_tree_depth: usize,
}

impl Default for IceConfig {
    fn default() -> Self {
        Self { max_iterations: 50, max_tree_depth: 4 }
    }
}

// ---------------------------------------------------------------------------
// ICE learning result
// ---------------------------------------------------------------------------

/// Result of ICE learning.
#[derive(Debug, Clone)]
pub struct IceResult {
    /// The synthesized invariant formula.
    pub invariant: Formula,
    /// Number of learning iterations performed.
    pub iterations: usize,
    /// Whether the learner converged (verifier confirmed the invariant).
    pub converged: bool,
    /// Number of positive examples used.
    pub positive_count: usize,
    /// Number of negative examples used.
    pub negative_count: usize,
    /// Number of implication examples used.
    pub implication_count: usize,
}

// ---------------------------------------------------------------------------
// IceLearner
// ---------------------------------------------------------------------------

/// ICE (Implication CounterExample) guided invariant learner.
///
/// Maintains sets of positive, negative, and implication examples, and uses
/// a decision-tree classifier to synthesize an invariant formula that:
/// - Accepts all positive examples
/// - Rejects all negative examples
/// - Respects all implication examples (if pre accepted, post must be accepted)
#[derive(Debug, Clone)]
pub struct IceLearner {
    /// Configuration.
    config: IceConfig,
    /// Positive examples: states that must satisfy the invariant.
    positive: Vec<ConcreteState>,
    /// Negative examples: states that must not satisfy the invariant.
    negative: Vec<ConcreteState>,
    /// Implication examples: transition pairs.
    implications: Vec<ImplicationExample>,
}

impl IceLearner {
    /// Create a new ICE learner with the given configuration.
    #[must_use]
    pub fn new(config: IceConfig) -> Self {
        Self { config, positive: Vec::new(), negative: Vec::new(), implications: Vec::new() }
    }

    /// Create a learner with default configuration.
    #[must_use]
    pub fn with_defaults() -> Self {
        Self::new(IceConfig::default())
    }

    /// Add a positive example (state that must satisfy the invariant).
    pub fn add_positive(&mut self, state: ConcreteState) {
        self.positive.push(state);
    }

    /// Add a negative example (state that must not satisfy the invariant).
    pub fn add_negative(&mut self, state: ConcreteState) {
        self.negative.push(state);
    }

    /// Add an implication example (transition pair).
    pub fn add_implication(&mut self, example: ImplicationExample) {
        self.implications.push(example);
    }

    /// Add a counterexample from the ICE verifier.
    pub fn add_counterexample(&mut self, cex: IceCounterexample) {
        match cex {
            IceCounterexample::Positive(s) => self.add_positive(s),
            IceCounterexample::Negative(s) => self.add_negative(s),
            IceCounterexample::Implication(imp) => self.add_implication(imp),
        }
    }

    /// Number of positive examples.
    #[must_use]
    pub fn positive_count(&self) -> usize {
        self.positive.len()
    }

    /// Number of negative examples.
    #[must_use]
    pub fn negative_count(&self) -> usize {
        self.negative.len()
    }

    /// Number of implication examples.
    #[must_use]
    pub fn implication_count(&self) -> usize {
        self.implications.len()
    }

    /// Synthesize an invariant formula from the current example sets.
    ///
    /// Uses a decision-tree classifier to separate positive from negative
    /// examples while respecting implication constraints. Returns a
    /// `Formula` encoding the classifier.
    ///
    /// # Errors
    /// Returns `IceError` if no positive/negative examples exist or if
    /// the classifier cannot separate the examples.
    pub fn synthesize_invariant(&self) -> Result<Formula, IceError> {
        if self.positive.is_empty() {
            return Err(IceError::NoPositiveExamples);
        }
        if self.negative.is_empty() {
            return Err(IceError::NoNegativeExamples);
        }

        // Collect all variable names from examples.
        let vars = self.collect_variables();
        if vars.is_empty() {
            return Err(IceError::NoVariables);
        }

        // Build a decision tree that classifies positive vs negative.
        let tree = self.build_tree(&vars, &self.positive, &self.negative, 0);
        Ok(tree_to_formula(&tree))
    }

    /// Run the full ICE learning loop with a verifier.
    ///
    /// Iteratively: synthesize a candidate, check with verifier, add
    /// counterexample, repeat until convergence or iteration limit.
    ///
    /// # Errors
    /// Returns `IceError::MaxIterations` if the learner does not converge
    /// within `config.max_iterations`. Callers that want the best-effort
    /// (non-converged) candidate should use [`Self::learn_best_effort`] instead.
    pub fn learn(&mut self, verifier: &dyn IceVerifier) -> Result<IceResult, IceError> {
        let result = self.learn_best_effort(verifier)?;
        if result.converged { Ok(result) } else { Err(IceError::MaxIterations(result.iterations)) }
    }

    /// Run the ICE learning loop, returning the best candidate even if
    /// the learner does not converge within the iteration limit.
    ///
    /// Unlike [`Self::learn`], this method returns `Ok` with `converged: false`
    /// when max iterations are reached. Use this when you want to inspect
    /// or use the partial result (e.g., for diagnostics or as a seed for
    /// another round of learning).
    pub fn learn_best_effort(&mut self, verifier: &dyn IceVerifier) -> Result<IceResult, IceError> {
        let mut iterations = 0;

        for _ in 0..self.config.max_iterations {
            iterations += 1;

            // Synthesize candidate from current examples.
            let candidate = self.synthesize_invariant()?;

            // Check with verifier.
            match verifier.check_invariant(&candidate)? {
                None => {
                    // Invariant confirmed -- converged.
                    return Ok(IceResult {
                        invariant: candidate,
                        iterations,
                        converged: true,
                        positive_count: self.positive.len(),
                        negative_count: self.negative.len(),
                        implication_count: self.implications.len(),
                    });
                }
                Some(cex) => {
                    // Add counterexample and continue.
                    self.add_counterexample(cex);
                }
            }
        }

        // Return best effort with converged: false.
        let candidate = self.synthesize_invariant()?;
        Ok(IceResult {
            invariant: candidate,
            iterations,
            converged: false,
            positive_count: self.positive.len(),
            negative_count: self.negative.len(),
            implication_count: self.implications.len(),
        })
    }

    /// Convert a Houdini-style counterexample to an ICE positive example.
    ///
    /// Bridge for integration with the existing CEGIS pipeline: Houdini
    /// counterexamples that violate candidate invariants become positive
    /// examples (states that should satisfy the true invariant).
    #[must_use]
    pub fn houdini_cex_to_positive(cex: &Counterexample) -> ConcreteState {
        ConcreteState::new(cex.assignments.clone())
    }

    // -----------------------------------------------------------------------
    // Internal: variable collection
    // -----------------------------------------------------------------------

    /// Collect all variable names from all example sets.
    fn collect_variables(&self) -> Vec<String> {
        let mut vars = BTreeSet::<String>::new();
        for state in &self.positive {
            for (name, _) in &state.assignments {
                vars.insert(name.clone());
            }
        }
        for state in &self.negative {
            for (name, _) in &state.assignments {
                vars.insert(name.clone());
            }
        }
        for imp in &self.implications {
            for (name, _) in &imp.pre.assignments {
                vars.insert(name.clone());
            }
            for (name, _) in &imp.post.assignments {
                vars.insert(name.clone());
            }
        }
        vars.into_iter().collect()
    }

    // -----------------------------------------------------------------------
    // Internal: decision tree construction
    // -----------------------------------------------------------------------

    /// Build a decision tree to separate positive from negative examples.
    ///
    /// Uses information-gain-style splitting on `var <= threshold` predicates.
    /// Respects implication constraints: if splitting would put a pre-state
    /// and post-state on different sides, penalize that split.
    fn build_tree(
        &self,
        vars: &[String],
        pos: &[ConcreteState],
        neg: &[ConcreteState],
        depth: usize,
    ) -> DecisionTree {
        // Base cases:
        if neg.is_empty() {
            return DecisionTree::Leaf(true); // All positive -> accept
        }
        if pos.is_empty() {
            return DecisionTree::Leaf(false); // All negative -> reject
        }
        if depth >= self.config.max_tree_depth {
            // Majority vote at max depth.
            return DecisionTree::Leaf(pos.len() >= neg.len());
        }

        // Find the best split.
        let best = self.find_best_split(vars, pos, neg);
        match best {
            None => {
                // No useful split found -- majority vote.
                DecisionTree::Leaf(pos.len() >= neg.len())
            }
            Some(predicate) => {
                // Partition examples by the split predicate.
                let (pos_true, pos_false) = partition(pos, &predicate);
                let (neg_true, neg_false) = partition(neg, &predicate);

                let left = self.build_tree(vars, &pos_true, &neg_true, depth + 1);
                let right = self.build_tree(vars, &pos_false, &neg_false, depth + 1);

                DecisionTree::Split { predicate, left: Box::new(left), right: Box::new(right) }
            }
        }
    }

    /// Find the best split predicate for the given examples.
    ///
    /// Tries all `var <= threshold` where threshold is a midpoint between
    /// consecutive distinct values observed in the examples. Picks the split
    /// that maximizes information gain (reduction in impurity) while
    /// penalizing implication violations.
    fn find_best_split(
        &self,
        vars: &[String],
        pos: &[ConcreteState],
        neg: &[ConcreteState],
    ) -> Option<SplitPredicate> {
        let total = pos.len() + neg.len();
        if total == 0 {
            return None;
        }
        let parent_impurity = gini(pos.len(), neg.len());

        let mut best_predicate: Option<SplitPredicate> = None;
        let mut best_gain: f64 = 0.0;

        for var in vars {
            // Collect all distinct values for this variable.
            let mut values: Vec<i128> = Vec::new();
            for state in pos.iter().chain(neg.iter()) {
                if let Some(v) = state.get(var) {
                    values.push(v);
                }
            }
            values.sort_unstable();
            values.dedup();

            if values.len() < 2 {
                continue;
            }

            // Try midpoints between consecutive values.
            for window in values.windows(2) {
                let threshold = window[0] + (window[1] - window[0]) / 2;
                let predicate = SplitPredicate { var: var.clone(), threshold };

                let (pos_true, pos_false) = partition(pos, &predicate);
                let (neg_true, neg_false) = partition(neg, &predicate);

                let left_total = pos_true.len() + neg_true.len();
                let right_total = pos_false.len() + neg_false.len();

                if left_total == 0 || right_total == 0 {
                    continue;
                }

                let left_impurity = gini(pos_true.len(), neg_true.len());
                let right_impurity = gini(pos_false.len(), neg_false.len());

                let weighted_impurity = (left_total as f64 * left_impurity
                    + right_total as f64 * right_impurity)
                    / total as f64;
                let mut gain = parent_impurity - weighted_impurity;

                // Penalize implication violations: if pre is on one side
                // and post is on the other, this split breaks inductiveness.
                let violations = self.count_implication_violations(&predicate);
                gain -= violations as f64 * 0.1;

                if gain > best_gain {
                    best_gain = gain;
                    best_predicate = Some(predicate);
                }
            }
        }

        best_predicate
    }

    /// Count how many implication examples are violated by a split.
    ///
    /// A violation occurs when the pre-state and post-state are classified
    /// differently by the predicate (pre satisfies, post doesn't, or vice
    /// versa when considering the invariant semantics).
    fn count_implication_violations(&self, predicate: &SplitPredicate) -> usize {
        self.implications
            .iter()
            .filter(|imp| {
                let pre_eval = predicate.evaluate(&imp.pre);
                let post_eval = predicate.evaluate(&imp.post);
                // Violation: pre and post go to different sides.
                match (pre_eval, post_eval) {
                    (Some(a), Some(b)) => a != b,
                    _ => false,
                }
            })
            .count()
    }
}

// ---------------------------------------------------------------------------
// Decision tree internal representation
// ---------------------------------------------------------------------------

/// A binary decision tree for classifying states.
#[derive(Debug, Clone)]
enum DecisionTree {
    /// Terminal: accept (true) or reject (false).
    Leaf(bool),
    /// Split on a predicate: left = predicate true, right = predicate false.
    Split { predicate: SplitPredicate, left: Box<DecisionTree>, right: Box<DecisionTree> },
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Convert a decision tree to a Formula.
fn tree_to_formula(tree: &DecisionTree) -> Formula {
    match tree {
        DecisionTree::Leaf(accept) => Formula::Bool(*accept),
        DecisionTree::Split { predicate, left, right } => {
            let left_formula = tree_to_formula(left);
            let right_formula = tree_to_formula(right);

            // (var <= threshold AND left) OR (var > threshold AND right)
            let left_branch = Formula::And(vec![predicate.to_le_formula(), left_formula]);
            let right_branch = Formula::And(vec![predicate.to_gt_formula(), right_formula]);
            Formula::Or(vec![left_branch, right_branch])
        }
    }
}

/// Partition states by a split predicate.
///
/// States where the predicate evaluates to `true` go to `true_set`,
/// states where it evaluates to `false` go to `false_set`. States
/// with unknown evaluation (missing variable) go to `true_set`
/// (optimistic for positive examples).
fn partition(
    states: &[ConcreteState],
    predicate: &SplitPredicate,
) -> (Vec<ConcreteState>, Vec<ConcreteState>) {
    let mut true_set = Vec::new();
    let mut false_set = Vec::new();
    for state in states {
        match predicate.evaluate(state) {
            Some(true) | None => true_set.push(state.clone()),
            Some(false) => false_set.push(state.clone()),
        }
    }
    (true_set, false_set)
}

/// Gini impurity for a binary classification.
fn gini(pos: usize, neg: usize) -> f64 {
    let total = pos + neg;
    if total == 0 {
        return 0.0;
    }
    let p_pos = pos as f64 / total as f64;
    let p_neg = neg as f64 / total as f64;
    1.0 - p_pos * p_pos - p_neg * p_neg
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::houdini;

    // -----------------------------------------------------------------------
    // Helper constructors
    // -----------------------------------------------------------------------

    fn state(pairs: &[(&str, i128)]) -> ConcreteState {
        ConcreteState::new(pairs.iter().map(|(n, v)| (n.to_string(), *v)).collect())
    }

    // -----------------------------------------------------------------------
    // Scenario 1: Simple separation (x >= 0 invariant)
    // -----------------------------------------------------------------------

    #[test]
    fn test_simple_separation() {
        let mut learner = IceLearner::with_defaults();

        // Positive: x = 0, 5, 10 (x >= 0)
        learner.add_positive(state(&[("x", 0)]));
        learner.add_positive(state(&[("x", 5)]));
        learner.add_positive(state(&[("x", 10)]));

        // Negative: x = -1, -5, -10 (x < 0)
        learner.add_negative(state(&[("x", -1)]));
        learner.add_negative(state(&[("x", -5)]));
        learner.add_negative(state(&[("x", -10)]));

        let result = learner.synthesize_invariant();
        assert!(result.is_ok(), "should synthesize an invariant");

        let formula = result.unwrap();
        // The formula should accept positive and reject negative examples.
        for pos in &learner.positive {
            assert!(
                eval_bool(&formula, &pos.assignments).unwrap_or(true),
                "positive example {pos:?} should satisfy invariant"
            );
        }
        for neg in &learner.negative {
            assert!(
                !eval_bool(&formula, &neg.assignments).unwrap_or(false),
                "negative example {neg:?} should not satisfy invariant"
            );
        }
    }

    // -----------------------------------------------------------------------
    // Scenario 2: Two-variable separation
    // -----------------------------------------------------------------------

    #[test]
    fn test_two_variable_separation() {
        let mut learner = IceLearner::with_defaults();

        // Positive: x >= 0 AND y >= 0
        learner.add_positive(state(&[("x", 1), ("y", 1)]));
        learner.add_positive(state(&[("x", 5), ("y", 3)]));
        learner.add_positive(state(&[("x", 0), ("y", 0)]));

        // Negative: x < 0 or y < 0
        learner.add_negative(state(&[("x", -1), ("y", 1)]));
        learner.add_negative(state(&[("x", 1), ("y", -2)]));
        learner.add_negative(state(&[("x", -3), ("y", -1)]));

        let result = learner.synthesize_invariant();
        assert!(result.is_ok());

        let formula = result.unwrap();
        for pos in &learner.positive {
            assert!(eval_bool(&formula, &pos.assignments).unwrap_or(true));
        }
        for neg in &learner.negative {
            assert!(!eval_bool(&formula, &neg.assignments).unwrap_or(false));
        }
    }

    // -----------------------------------------------------------------------
    // Scenario 3: With implication examples
    // -----------------------------------------------------------------------

    #[test]
    fn test_with_implications() {
        let mut learner = IceLearner::with_defaults();

        // Loop: i increments from 0 to n
        // Positive: i = 0, 1, 5 (loop entry states)
        learner.add_positive(state(&[("i", 0)]));
        learner.add_positive(state(&[("i", 1)]));
        learner.add_positive(state(&[("i", 5)]));

        // Negative: i = -1, -3 (error states)
        learner.add_negative(state(&[("i", -1)]));
        learner.add_negative(state(&[("i", -3)]));

        // Implication: (i=0) -> (i=1), (i=1) -> (i=2)
        learner.add_implication(ImplicationExample {
            pre: state(&[("i", 0)]),
            post: state(&[("i", 1)]),
        });
        learner.add_implication(ImplicationExample {
            pre: state(&[("i", 1)]),
            post: state(&[("i", 2)]),
        });

        let result = learner.synthesize_invariant();
        assert!(result.is_ok());

        let formula = result.unwrap();
        // All positive examples should satisfy the invariant.
        for pos in &learner.positive {
            assert!(eval_bool(&formula, &pos.assignments).unwrap_or(true));
        }
        // All negative examples should not satisfy.
        for neg in &learner.negative {
            assert!(!eval_bool(&formula, &neg.assignments).unwrap_or(false));
        }
    }

    // -----------------------------------------------------------------------
    // Scenario 4: No positive examples -> error
    // -----------------------------------------------------------------------

    #[test]
    fn test_no_positive_examples_error() {
        let mut learner = IceLearner::with_defaults();
        learner.add_negative(state(&[("x", -1)]));
        let result = learner.synthesize_invariant();
        assert!(matches!(result, Err(IceError::NoPositiveExamples)));
    }

    // -----------------------------------------------------------------------
    // Scenario 5: No negative examples -> error
    // -----------------------------------------------------------------------

    #[test]
    fn test_no_negative_examples_error() {
        let mut learner = IceLearner::with_defaults();
        learner.add_positive(state(&[("x", 1)]));
        let result = learner.synthesize_invariant();
        assert!(matches!(result, Err(IceError::NoNegativeExamples)));
    }

    // -----------------------------------------------------------------------
    // Scenario 6: ICE learning loop with mock verifier
    // -----------------------------------------------------------------------

    #[test]
    fn test_ice_learning_loop_converges() {
        struct MockIceVerifier {
            responses: std::sync::Mutex<Vec<Option<IceCounterexample>>>,
        }

        impl IceVerifier for MockIceVerifier {
            fn check_invariant(
                &self,
                _candidate: &Formula,
            ) -> Result<Option<IceCounterexample>, IceError> {
                let mut responses = self.responses.lock().unwrap();
                if responses.is_empty() { Ok(None) } else { Ok(responses.remove(0)) }
            }
        }

        let mut learner = IceLearner::with_defaults();
        // Seed with initial examples.
        learner.add_positive(state(&[("x", 0)]));
        learner.add_positive(state(&[("x", 5)]));
        learner.add_negative(state(&[("x", -1)]));

        let verifier = MockIceVerifier {
            responses: std::sync::Mutex::new(vec![
                // First check: returns a new negative example.
                Some(IceCounterexample::Negative(state(&[("x", -10)]))),
                // Second check: returns a positive example.
                Some(IceCounterexample::Positive(state(&[("x", 20)]))),
                // Third check: converged.
                None,
            ]),
        };

        let result = learner.learn(&verifier);
        assert!(result.is_ok());
        let ice_result = result.unwrap();
        assert!(ice_result.converged);
        assert_eq!(ice_result.iterations, 3);
        assert_eq!(ice_result.positive_count, 3); // 2 initial + 1 from verifier
        assert_eq!(ice_result.negative_count, 2); // 1 initial + 1 from verifier
    }

    // -----------------------------------------------------------------------
    // Scenario 6b: Non-convergence returns MaxIterations error
    // -----------------------------------------------------------------------

    #[test]
    fn test_ice_learning_loop_non_convergence_returns_error() {
        // Verifier that always returns a counterexample (never converges).
        struct NeverConvergesVerifier;

        impl IceVerifier for NeverConvergesVerifier {
            fn check_invariant(
                &self,
                _candidate: &Formula,
            ) -> Result<Option<IceCounterexample>, IceError> {
                // Always return a new positive counterexample.
                Ok(Some(IceCounterexample::Positive(state(&[("x", 99)]))))
            }
        }

        let mut learner = IceLearner::new(IceConfig { max_iterations: 3, max_tree_depth: 4 });
        learner.add_positive(state(&[("x", 0)]));
        learner.add_negative(state(&[("x", -1)]));

        // learn() should return Err(MaxIterations) when not converged.
        let result = learner.learn(&NeverConvergesVerifier);
        assert!(
            matches!(result, Err(IceError::MaxIterations(3))),
            "expected MaxIterations(3), got {result:?}"
        );
    }

    // -----------------------------------------------------------------------
    // Scenario 6c: Best-effort learning returns Ok even without convergence
    // -----------------------------------------------------------------------

    #[test]
    fn test_ice_learning_best_effort_returns_ok_without_convergence() {
        struct NeverConvergesVerifier;

        impl IceVerifier for NeverConvergesVerifier {
            fn check_invariant(
                &self,
                _candidate: &Formula,
            ) -> Result<Option<IceCounterexample>, IceError> {
                Ok(Some(IceCounterexample::Positive(state(&[("x", 99)]))))
            }
        }

        let mut learner = IceLearner::new(IceConfig { max_iterations: 3, max_tree_depth: 4 });
        learner.add_positive(state(&[("x", 0)]));
        learner.add_negative(state(&[("x", -1)]));

        // learn_best_effort() should return Ok with converged: false.
        let result = learner.learn_best_effort(&NeverConvergesVerifier);
        assert!(result.is_ok(), "learn_best_effort should return Ok");
        let ice_result = result.unwrap();
        assert!(!ice_result.converged, "should not be converged");
        assert_eq!(ice_result.iterations, 3);
    }

    // -----------------------------------------------------------------------
    // Scenario 7: Houdini counterexample bridge
    // -----------------------------------------------------------------------

    #[test]
    fn test_houdini_cex_bridge() {
        let cex =
            Counterexample { assignments: vec![("x".to_string(), 42), ("y".to_string(), -7)] };
        let state = IceLearner::houdini_cex_to_positive(&cex);
        assert_eq!(state.get("x"), Some(42));
        assert_eq!(state.get("y"), Some(-7));
    }

    // -----------------------------------------------------------------------
    // Scenario 8: Example counts
    // -----------------------------------------------------------------------

    #[test]
    fn test_example_counts() {
        let mut learner = IceLearner::with_defaults();
        assert_eq!(learner.positive_count(), 0);
        assert_eq!(learner.negative_count(), 0);
        assert_eq!(learner.implication_count(), 0);

        learner.add_positive(state(&[("x", 1)]));
        learner.add_negative(state(&[("x", -1)]));
        learner.add_implication(ImplicationExample {
            pre: state(&[("x", 0)]),
            post: state(&[("x", 1)]),
        });

        assert_eq!(learner.positive_count(), 1);
        assert_eq!(learner.negative_count(), 1);
        assert_eq!(learner.implication_count(), 1);
    }

    // -----------------------------------------------------------------------
    // Scenario 9: Add counterexamples of each kind
    // -----------------------------------------------------------------------

    #[test]
    fn test_add_counterexample_dispatch() {
        let mut learner = IceLearner::with_defaults();

        learner.add_counterexample(IceCounterexample::Positive(state(&[("x", 1)])));
        learner.add_counterexample(IceCounterexample::Negative(state(&[("x", -1)])));
        learner.add_counterexample(IceCounterexample::Implication(ImplicationExample {
            pre: state(&[("x", 0)]),
            post: state(&[("x", 1)]),
        }));

        assert_eq!(learner.positive_count(), 1);
        assert_eq!(learner.negative_count(), 1);
        assert_eq!(learner.implication_count(), 1);
    }

    // -----------------------------------------------------------------------
    // Scenario 10: SplitPredicate formula conversion
    // -----------------------------------------------------------------------

    #[test]
    fn test_split_predicate_formulas() {
        let pred = SplitPredicate { var: "x".to_string(), threshold: 5 };

        let le = pred.to_le_formula();
        assert!(matches!(le, Formula::Le(_, _)));

        let gt = pred.to_gt_formula();
        assert!(matches!(gt, Formula::Gt(_, _)));
    }

    // -----------------------------------------------------------------------
    // Formula evaluation helper for tests
    // -----------------------------------------------------------------------

    /// Evaluate a formula under concrete assignments. Reuses the houdini
    /// evaluator logic pattern for consistency.
    fn eval_bool(formula: &Formula, assignments: &[(String, i128)]) -> Option<bool> {
        let cex = Counterexample { assignments: assignments.to_vec() };
        // If is_falsified_by returns true, the formula evaluates to false.
        // If it returns false, the formula evaluates to true or unknown.
        if houdini::is_falsified_by(formula, &cex) {
            Some(false)
        } else {
            // Check if definitely true by checking if NOT(formula) is falsified.
            // A simpler approach: just check the formula directly.
            match formula {
                Formula::Bool(b) => Some(*b),
                Formula::Or(parts) => {
                    // If any part is definitely true, the whole is true.
                    for part in parts {
                        if eval_bool(part, assignments) == Some(true) {
                            return Some(true);
                        }
                    }
                    // If all parts are definitely false, the whole is false.
                    let all_false = parts.iter().all(|p| eval_bool(p, assignments) == Some(false));
                    if all_false { Some(false) } else { None }
                }
                Formula::And(parts) => {
                    for part in parts {
                        if eval_bool(part, assignments) == Some(false) {
                            return Some(false);
                        }
                    }
                    let all_true = parts.iter().all(|p| eval_bool(p, assignments) == Some(true));
                    if all_true { Some(true) } else { None }
                }
                Formula::Le(a, b) => {
                    let va = eval_int(a, assignments)?;
                    let vb = eval_int(b, assignments)?;
                    Some(va <= vb)
                }
                Formula::Gt(a, b) => {
                    let va = eval_int(a, assignments)?;
                    let vb = eval_int(b, assignments)?;
                    Some(va > vb)
                }
                Formula::Ge(a, b) => {
                    let va = eval_int(a, assignments)?;
                    let vb = eval_int(b, assignments)?;
                    Some(va >= vb)
                }
                Formula::Lt(a, b) => {
                    let va = eval_int(a, assignments)?;
                    let vb = eval_int(b, assignments)?;
                    Some(va < vb)
                }
                _ => None,
            }
        }
    }

    fn eval_int(formula: &Formula, assignments: &[(String, i128)]) -> Option<i128> {
        match formula {
            Formula::Int(v) => Some(*v),
            Formula::Var(name, _) => assignments.iter().find(|(n, _)| n == name).map(|(_, v)| *v),
            Formula::Add(a, b) => Some(eval_int(a, assignments)? + eval_int(b, assignments)?),
            Formula::Sub(a, b) => Some(eval_int(a, assignments)? - eval_int(b, assignments)?),
            _ => None,
        }
    }
}
