// trust-types/formula/temporal: Temporal logic operators and liveness properties
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

/// Trust: Temporal operator for liveness properties.
///
/// Models the standard temporal operators from LTL/CTL used in ty:
/// - Eventually: <>P ("P holds at some future state")
/// - Always: []P ("P holds at all future states")
/// - AlwaysEventually: []<>P ("P holds infinitely often")
/// - LeadsTo: P ~> Q ("[](P => <>Q)")
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TemporalOperator {
    /// <>P: P holds at some future state.
    Eventually,
    /// []P: P holds at all future states.
    Always,
    /// []<>P: P holds infinitely often.
    AlwaysEventually,
    /// P ~> Q: whenever P holds, Q eventually holds.
    LeadsTo,
}

impl TemporalOperator {
    /// TLA+ notation for this operator.
    pub fn tla_notation(&self) -> &str {
        match self {
            TemporalOperator::Eventually => "<>",
            TemporalOperator::Always => "[]",
            TemporalOperator::AlwaysEventually => "[]<>",
            TemporalOperator::LeadsTo => "~>",
        }
    }
}

/// Trust: A liveness property to verify.
///
/// Liveness = "something good eventually happens." Verified via ty's
/// Buchi automaton construction and Tarjan SCC detection for accepting cycles.
///
/// Examples:
/// - Eventually(P): <>P — system eventually reaches state P
/// - LeadsTo(P, Q): P ~> Q — every P-state eventually reaches Q
/// - InfinitelyOften(P): []<>P — P recurs forever
/// - StarvationFreedom(entity): forall t: []<>Progress(t)
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LivenessProperty {
    /// Name of the property for diagnostics.
    pub name: String,
    /// The temporal operator governing this property.
    pub operator: TemporalOperator,
    /// State predicate P (the "good thing").
    pub predicate: String,
    /// Optional second predicate Q for binary operators like LeadsTo.
    pub consequent: Option<String>,
    /// Fairness constraints required for this property to hold.
    pub fairness: Vec<FairnessConstraint>,
}

impl LivenessProperty {
    /// Human-readable description of this liveness property.
    pub fn description(&self) -> String {
        let op = self.operator.tla_notation();
        match &self.consequent {
            Some(q) => format!("{}: {} {} {}", self.name, self.predicate, op, q),
            None => format!("{}: {}{}", self.name, op, self.predicate),
        }
    }

    /// TLA+ formula representation.
    pub fn to_tla(&self) -> String {
        match self.operator {
            TemporalOperator::Eventually => format!("<>({})", self.predicate),
            TemporalOperator::Always => format!("[]({})", self.predicate),
            TemporalOperator::AlwaysEventually => format!("[]<>({})", self.predicate),
            TemporalOperator::LeadsTo => {
                let q = self.consequent.as_deref().unwrap_or("TRUE");
                format!("({}) ~> ({})", self.predicate, q)
            }
        }
    }
}

/// Trust: Fairness constraint for temporal verification.
///
/// Fairness = "if enabled infinitely often, executed infinitely often."
/// Maps to TLA+'s WF_vars(Action) and SF_vars(Action).
///
/// - Weak fairness (WF): if an action is continuously enabled, it eventually executes.
///   Maps to tokio::spawn tasks, standard async scheduling.
/// - Strong fairness (SF): if an action is enabled infinitely often (not necessarily
///   continuously), it eventually executes. Needed for priority queues, reentrant locks.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum FairnessConstraint {
    /// WF_vars(Action): weak fairness — continuously enabled implies eventually taken.
    Weak {
        /// The action (e.g., "task_schedule", "send_message").
        action: String,
        /// State variables the action operates on.
        vars: Vec<String>,
    },
    /// SF_vars(Action): strong fairness — infinitely often enabled implies infinitely often taken.
    Strong {
        /// The action (e.g., "priority_dequeue", "lock_acquire").
        action: String,
        /// State variables the action operates on.
        vars: Vec<String>,
    },
}

impl FairnessConstraint {
    /// Human-readable description.
    pub fn description(&self) -> String {
        match self {
            FairnessConstraint::Weak { action, vars } => {
                format!("WF_{{{}}}({})", vars.join(", "), action)
            }
            FairnessConstraint::Strong { action, vars } => {
                format!("SF_{{{}}}({})", vars.join(", "), action)
            }
        }
    }

    /// TLA+ formula representation.
    pub fn to_tla(&self) -> String {
        match self {
            FairnessConstraint::Weak { action, vars } => {
                format!("WF_<<{}>>({action})", vars.join(", "))
            }
            FairnessConstraint::Strong { action, vars } => {
                format!("SF_<<{}>>({action})", vars.join(", "))
            }
        }
    }

    /// Returns true if this is a strong fairness constraint.
    pub fn is_strong(&self) -> bool {
        matches!(self, FairnessConstraint::Strong { .. })
    }

    /// Returns the action name.
    pub fn action(&self) -> &str {
        match self {
            FairnessConstraint::Weak { action, .. } | FairnessConstraint::Strong { action, .. } => {
                action
            }
        }
    }
}

/// Trust: Counterexample trace for liveness violations.
///
/// A liveness violation manifests as an infinite cycle where the desired
/// property never holds. The counterexample shows:
///  1. A prefix of states leading to the cycle
///  2. The cycle itself (the lasso)
///
/// This follows the standard Buchi automaton counterexample format.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LivenessCounterexample {
    /// States leading to the cycle (may be empty if initial state is in the cycle).
    pub prefix: Vec<LivenessState>,
    /// The cycle of states where the liveness property is never satisfied.
    /// Must be non-empty for a valid counterexample.
    pub cycle: Vec<LivenessState>,
}

impl LivenessCounterexample {
    /// Returns the total number of states in the counterexample trace.
    pub fn trace_len(&self) -> usize {
        self.prefix.len() + self.cycle.len()
    }
}

impl std::fmt::Display for LivenessCounterexample {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.prefix.is_empty() {
            writeln!(f, "Prefix ({} states):", self.prefix.len())?;
            for (i, state) in self.prefix.iter().enumerate() {
                writeln!(f, "  [{i}] {}", state.label)?;
            }
        }
        writeln!(f, "Cycle ({} states):", self.cycle.len())?;
        for (i, state) in self.cycle.iter().enumerate() {
            writeln!(f, "  [{i}] {}", state.label)?;
        }
        write!(f, "  -> back to cycle start")
    }
}

/// A single state in a liveness counterexample trace.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LivenessState {
    /// Human-readable label for this state.
    pub label: String,
    /// Variable assignments in this state.
    pub assignments: Vec<(String, String)>,
}
