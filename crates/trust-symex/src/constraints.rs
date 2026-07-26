// trust-symex constraint collection (DART/SAGE style)
//
// Collect path constraints during concolic execution and produce
// new input vectors by negating individual constraints. Implements
// the core constraint-negation exploration strategy from DART
// (Godefroid et al., 2005) and generational search from SAGE
// (Godefroid et al., 2008).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};
use trust_types::Formula;

use crate::concrete::SymbolicBranchPoint;
use crate::path::symbolic_to_formula;
use crate::state::SymbolicValue;

/// A negated path prefix: the path constraint up to (and including) a
/// negated decision at position `negated_index`, ready for solver dispatch.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct NegatedPrefix {
    /// Index of the decision that was negated.
    pub negated_index: usize,
    /// The formula representing all constraints on this prefix
    /// (conjunction of decisions 0..negated_index-1 with decision
    /// `negated_index` negated).
    pub formula: Formula,
    /// The block ID at the negated branch point (for coverage guidance).
    pub branch_block: usize,
}

/// Strategy for choosing which constraint to negate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
#[derive(Default)]
pub enum NegationStrategy {
    /// DART style: negate the last constraint first, working backwards.
    LastFirst,
    /// SAGE generational: negate each constraint independently to
    /// produce one new input per branch point.
    #[default]
    Generational,
    /// Coverage-directed: negate constraints at branches whose
    /// alternative direction has not been covered.
    CoverageDirected,
}

/// Collector that accumulates branch decisions from a concolic run and
/// produces negated prefixes for the solver.
#[derive(Debug, Clone, Default)]
pub(crate) struct ConstraintCollector {
    /// Branch decisions in execution order.
    decisions: Vec<CollectedDecision>,
    /// Indices of decisions already negated (to avoid re-exploration).
    negated_set: BTreeSet<usize>,
}

/// A single branch decision recorded during concolic execution.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct CollectedDecision {
    /// The symbolic condition at the branch.
    pub condition: SymbolicValue,
    /// The direction actually taken.
    pub taken: bool,
    /// The block containing the branch.
    pub block_id: usize,
}

impl ConstraintCollector {
    /// Create a new empty collector.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Import branch points from a completed concolic execution run.
    pub(crate) fn import_branches(&mut self, branches: &[SymbolicBranchPoint]) {
        self.decisions.clear();
        for bp in branches {
            self.decisions.push(CollectedDecision {
                condition: bp.condition.clone(),
                taken: bp.taken,
                block_id: bp.block_id,
            });
        }
    }

    /// Produce negated prefixes according to the chosen strategy.
    ///
    /// Each returned `NegatedPrefix` represents a path prefix whose
    /// last decision has been flipped. Solving the resulting formula
    /// yields an input that drives execution down the alternative branch.
    #[must_use]
    pub(crate) fn negate(&mut self, strategy: NegationStrategy) -> Vec<NegatedPrefix> {
        match strategy {
            NegationStrategy::LastFirst => self.negate_last_first(),
            NegationStrategy::Generational => self.negate_generational(),
            NegationStrategy::CoverageDirected => {
                // Falls back to generational for now; coverage feedback
                // is handled by the concolic engine's exploration loop.
                self.negate_generational()
            }
        }
    }

    /// DART-style: negate only the last un-negated decision.
    fn negate_last_first(&mut self) -> Vec<NegatedPrefix> {
        for i in (0..self.decisions.len()).rev() {
            if self.negated_set.contains(&i) {
                continue;
            }
            self.negated_set.insert(i);
            if let Some(prefix) = self.build_negated_prefix(i) {
                return vec![prefix];
            }
        }
        vec![]
    }

    /// SAGE generational: negate each un-negated decision independently.
    fn negate_generational(&mut self) -> Vec<NegatedPrefix> {
        let mut prefixes = Vec::new();
        for i in 0..self.decisions.len() {
            if self.negated_set.contains(&i) {
                continue;
            }
            self.negated_set.insert(i);
            if let Some(prefix) = self.build_negated_prefix(i) {
                prefixes.push(prefix);
            }
        }
        prefixes
    }

    /// Build a negated prefix formula: decisions[0..i-1] as-is, decisions[i] flipped.
    fn build_negated_prefix(&self, negated_index: usize) -> Option<NegatedPrefix> {
        if negated_index >= self.decisions.len() {
            return None;
        }

        let mut clauses: Vec<Formula> = Vec::with_capacity(negated_index + 1);

        // Keep all decisions before the negated one.
        for d in &self.decisions[..negated_index] {
            let f = symbolic_to_formula(&d.condition);
            if d.taken {
                clauses.push(f);
            } else {
                clauses.push(Formula::Not(Box::new(f)));
            }
        }

        // Negate the decision at negated_index.
        let negated_d = &self.decisions[negated_index];
        let f = symbolic_to_formula(&negated_d.condition);
        // Flip: if it was taken, assert NOT; if it was not taken, assert it.
        if negated_d.taken {
            clauses.push(Formula::Not(Box::new(f)));
        } else {
            clauses.push(f);
        }

        let formula = match clauses.len() {
            0 => Formula::Bool(true),
            // SAFETY: match arm guarantees len == 1, so .next() returns Some.
            1 => clauses
                .into_iter()
                .next()
                .unwrap_or_else(|| unreachable!("empty iter despite len == 1")),
            _ => Formula::And(clauses),
        };

        Some(NegatedPrefix { negated_index, formula, branch_block: negated_d.block_id })
    }
}

#[cfg(test)]
mod tests {
    use trust_types::BinOp;

    use super::*;
    use crate::concrete::SymbolicBranchPoint;
    fn sym(name: &str) -> SymbolicValue {
        SymbolicValue::Symbol(name.into())
    }

    fn lt_cond(name: &str, val: i128) -> SymbolicValue {
        SymbolicValue::bin_op(sym(name), BinOp::Lt, SymbolicValue::Concrete(val))
    }

    #[test]
    fn test_constraints_collector_empty() {
        let collector = ConstraintCollector::new();
        assert!(collector.decisions.is_empty());
        assert!(collector.negated_set.is_empty());
    }

    #[test]
    fn test_constraints_import_branches() {
        let mut collector = ConstraintCollector::new();
        let branches = vec![
            SymbolicBranchPoint {
                block_id: 0,
                condition: lt_cond("x", 10),
                taken: true,
                decision_index: 0,
            },
            SymbolicBranchPoint {
                block_id: 2,
                condition: lt_cond("y", 5),
                taken: false,
                decision_index: 1,
            },
        ];
        collector.import_branches(&branches);
        assert_eq!(collector.decisions.len(), 2);
        assert!(collector.negated_set.is_empty());
    }

    #[test]
    fn test_constraints_negate_last_first() {
        let mut collector = ConstraintCollector::new();
        let branches = vec![
            SymbolicBranchPoint {
                block_id: 0,
                condition: lt_cond("x", 10),
                taken: true,
                decision_index: 0,
            },
            SymbolicBranchPoint {
                block_id: 2,
                condition: lt_cond("y", 5),
                taken: true,
                decision_index: 1,
            },
        ];
        collector.import_branches(&branches);

        let prefixes = collector.negate(NegationStrategy::LastFirst);
        assert_eq!(prefixes.len(), 1);
        assert_eq!(prefixes[0].negated_index, 1);
        // The formula should be: (x < 10) AND NOT(y < 5)
        match &prefixes[0].formula {
            Formula::And(clauses) => assert_eq!(clauses.len(), 2),
            other => panic!("expected And, got {other:?}"),
        }

        // Second call should negate index 0.
        let prefixes2 = collector.negate(NegationStrategy::LastFirst);
        assert_eq!(prefixes2.len(), 1);
        assert_eq!(prefixes2[0].negated_index, 0);
    }

    #[test]
    fn test_constraints_negate_generational() {
        let mut collector = ConstraintCollector::new();
        let branches = vec![
            SymbolicBranchPoint {
                block_id: 0,
                condition: lt_cond("x", 10),
                taken: true,
                decision_index: 0,
            },
            SymbolicBranchPoint {
                block_id: 2,
                condition: lt_cond("y", 5),
                taken: true,
                decision_index: 1,
            },
            SymbolicBranchPoint {
                block_id: 4,
                condition: lt_cond("z", 3),
                taken: false,
                decision_index: 2,
            },
        ];
        collector.import_branches(&branches);

        let prefixes = collector.negate(NegationStrategy::Generational);
        // Generational produces one prefix per decision.
        assert_eq!(prefixes.len(), 3);
        assert_eq!(prefixes[0].negated_index, 0);
        assert_eq!(prefixes[1].negated_index, 1);
        assert_eq!(prefixes[2].negated_index, 2);

        // All should now be marked negated.
        assert_eq!(collector.negated_set.len(), collector.decisions.len());
    }

    #[test]
    fn test_constraints_mark_negated_skips() {
        let mut collector = ConstraintCollector::new();
        let branches = vec![
            SymbolicBranchPoint {
                block_id: 0,
                condition: lt_cond("x", 10),
                taken: true,
                decision_index: 0,
            },
            SymbolicBranchPoint {
                block_id: 2,
                condition: lt_cond("y", 5),
                taken: true,
                decision_index: 1,
            },
        ];
        collector.import_branches(&branches);
        collector.negated_set.insert(0);

        let prefixes = collector.negate(NegationStrategy::Generational);
        assert_eq!(prefixes.len(), 1);
        assert_eq!(prefixes[0].negated_index, 1);
    }

    #[test]
    fn test_constraints_negate_single_decision() {
        let mut collector = ConstraintCollector::new();
        let branches = vec![SymbolicBranchPoint {
            block_id: 0,
            condition: lt_cond("x", 10),
            taken: true,
            decision_index: 0,
        }];
        collector.import_branches(&branches);

        let prefixes = collector.negate(NegationStrategy::LastFirst);
        assert_eq!(prefixes.len(), 1);
        // With a single decision, negating it should produce NOT(x < 10).
        match &prefixes[0].formula {
            Formula::Not(_) => {}
            other => panic!("expected Not, got {other:?}"),
        }
    }

    #[test]
    fn test_constraints_exhausted_returns_empty() {
        let mut collector = ConstraintCollector::new();
        let branches = vec![SymbolicBranchPoint {
            block_id: 0,
            condition: sym("x"),
            taken: true,
            decision_index: 0,
        }];
        collector.import_branches(&branches);
        let _ = collector.negate(NegationStrategy::Generational);

        // All negated; second call returns empty.
        let prefixes = collector.negate(NegationStrategy::Generational);
        assert!(prefixes.is_empty());
    }

    #[test]
    fn test_constraints_negated_prefix_formula_correctness() {
        let mut collector = ConstraintCollector::new();
        // Three branches: taken, taken, not-taken
        let branches = vec![
            SymbolicBranchPoint {
                block_id: 0,
                condition: sym("a"),
                taken: true,
                decision_index: 0,
            },
            SymbolicBranchPoint {
                block_id: 1,
                condition: sym("b"),
                taken: true,
                decision_index: 1,
            },
            SymbolicBranchPoint {
                block_id: 2,
                condition: sym("c"),
                taken: false,
                decision_index: 2,
            },
        ];
        collector.import_branches(&branches);

        let prefixes = collector.negate(NegationStrategy::Generational);

        // Prefix for negating index 1:
        // decisions[0] as-is (a taken) AND NOT(b) [negated]
        let p1 = &prefixes[1];
        assert_eq!(p1.negated_index, 1);
        match &p1.formula {
            Formula::And(clauses) => {
                assert_eq!(clauses.len(), 2);
                // First clause: Var("a", Int) [taken as-is]
                match &clauses[0] {
                    Formula::Var(name, _) => assert_eq!(name, "a"),
                    other => panic!("expected Var(a), got {other:?}"),
                }
                // Second clause: Not(Var("b", Int)) [negated]
                match &clauses[1] {
                    Formula::Not(inner) => match inner.as_ref() {
                        Formula::Var(name, _) => assert_eq!(name, "b"),
                        other => panic!("expected Var(b), got {other:?}"),
                    },
                    other => panic!("expected Not, got {other:?}"),
                }
            }
            other => panic!("expected And, got {other:?}"),
        }
    }
}
