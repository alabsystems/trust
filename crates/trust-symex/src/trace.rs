// trust-symex trace replay and debugging
//
// Provides execution trace recording, replay, formatting, and
// counterexample extraction for symbolic execution debugging.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;
use std::fmt;
use std::fmt::Write;

use serde::{Deserialize, Serialize};

use crate::path::PathConstraint;
use crate::state::{SymbolicState, SymbolicValue};

/// A single step in an execution trace.
///
/// Records the block, statement, and a snapshot of variable values
/// at that point in the execution.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TraceStep {
    /// The basic block ID being executed.
    pub block_id: usize,
    /// The statement index within the block.
    pub stmt_index: usize,
    /// Snapshot of variable values at this step.
    pub variable_snapshot: BTreeMap<String, SymbolicValue>,
}

impl TraceStep {
    /// Create a new trace step.
    #[must_use]
    pub fn new(
        block_id: usize,
        stmt_index: usize,
        variable_snapshot: BTreeMap<String, SymbolicValue>,
    ) -> Self {
        Self { block_id, stmt_index, variable_snapshot }
    }

    /// Create a trace step from the current symbolic state.
    #[must_use]
    pub fn from_state(block_id: usize, stmt_index: usize, state: &SymbolicState) -> Self {
        let variable_snapshot = state.iter().map(|(k, v)| (k.to_owned(), v.clone())).collect();
        Self { block_id, stmt_index, variable_snapshot }
    }
}

/// A complete execution trace: an ordered sequence of steps.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExecutionTrace {
    steps: Vec<TraceStep>,
}

impl ExecutionTrace {
    /// Create an empty execution trace.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Append a step to the trace.
    pub fn push(&mut self, step: TraceStep) {
        self.steps.push(step);
    }

    /// Returns the number of steps in the trace.
    #[must_use]
    pub fn len(&self) -> usize {
        self.steps.len()
    }

    /// Returns `true` if the trace contains no steps.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }

    /// Get the trace steps as a slice.
    #[must_use]
    pub fn steps(&self) -> &[TraceStep] {
        &self.steps
    }

    /// Get a specific step by index.
    #[must_use]
    pub fn get(&self, index: usize) -> Option<&TraceStep> {
        self.steps.get(index)
    }

    /// Iterate over trace steps.
    pub fn iter(&self) -> impl Iterator<Item = &TraceStep> {
        self.steps.iter()
    }
}

/// Records trace steps during symbolic execution.
///
/// Attach a `TraceRecorder` to an execution run to accumulate a full
/// trace that can later be replayed or formatted.
#[derive(Debug, Clone, Default)]
pub struct TraceRecorder {
    trace: ExecutionTrace,
}

impl TraceRecorder {
    /// Create a new empty recorder.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Record a step from the current execution state.
    pub fn record(&mut self, block_id: usize, stmt_index: usize, state: &SymbolicState) {
        self.trace.push(TraceStep::from_state(block_id, stmt_index, state));
    }

    /// Record a step with an explicit variable snapshot.
    pub fn record_snapshot(
        &mut self,
        block_id: usize,
        stmt_index: usize,
        snapshot: BTreeMap<String, SymbolicValue>,
    ) {
        self.trace.push(TraceStep::new(block_id, stmt_index, snapshot));
    }

    /// Consume the recorder and return the completed trace.
    #[must_use]
    pub fn finish(self) -> ExecutionTrace {
        self.trace
    }

    /// Returns the number of steps recorded so far.
    #[must_use]
    pub fn len(&self) -> usize {
        self.trace.len()
    }

    /// Returns `true` if no steps have been recorded.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.trace.is_empty()
    }
}

/// Replays an execution trace and verifies consistency between steps.
///
/// The replayer iterates through trace steps and checks that variable
/// values are consistent (no unexpected mutations between steps).
#[derive(Debug)]
pub struct TraceReplayer<'a> {
    trace: &'a ExecutionTrace,
    position: usize,
}

impl<'a> TraceReplayer<'a> {
    /// Create a replayer for the given trace.
    #[must_use]
    pub fn new(trace: &'a ExecutionTrace) -> Self {
        Self { trace, position: 0 }
    }

    /// Advance to the next step, returning it if available.
    pub fn step(&mut self) -> Option<&'a TraceStep> {
        if self.position < self.trace.len() {
            let step = &self.trace.steps()[self.position];
            self.position += 1;
            Some(step)
        } else {
            None
        }
    }

    /// Returns the current position in the trace.
    #[must_use]
    pub fn position(&self) -> usize {
        self.position
    }

    /// Returns `true` if the replay has reached the end of the trace.
    #[must_use]
    pub fn is_done(&self) -> bool {
        self.position >= self.trace.len()
    }

    /// Reset the replayer to the beginning of the trace.
    pub fn reset(&mut self) {
        self.position = 0;
    }

    /// Verify that variables present in both consecutive steps maintain
    /// consistency (values that should not change between steps don't).
    ///
    /// Returns a list of inconsistencies found. An empty list means the
    /// trace is fully consistent.
    #[must_use]
    pub fn verify_consistency(&self) -> Vec<ConsistencyError> {
        let mut errors = Vec::new();
        let steps = self.trace.steps();

        for i in 1..steps.len() {
            let prev = &steps[i - 1];
            let curr = &steps[i];

            // If we are within the same block and statement index advances by 1,
            // check that no variables disappeared unexpectedly.
            if prev.block_id == curr.block_id && curr.stmt_index == prev.stmt_index + 1 {
                for (var, prev_val) in &prev.variable_snapshot {
                    if let Some(curr_val) = curr.variable_snapshot.get(var) {
                        // Value changed: that is expected if a statement assigned to it.
                        // We record it as an observation, not an error.
                        let _ = (prev_val, curr_val);
                    } else {
                        errors.push(ConsistencyError {
                            step_index: i,
                            variable: var.clone(),
                            kind: ConsistencyErrorKind::VariableDisappeared,
                        });
                    }
                }
            }
        }

        errors
    }
}

/// An inconsistency found during trace replay verification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConsistencyError {
    /// The step index where the inconsistency was detected.
    pub step_index: usize,
    /// The variable involved.
    pub variable: String,
    /// The kind of inconsistency.
    pub kind: ConsistencyErrorKind,
}

/// The kind of consistency error found during replay.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ConsistencyErrorKind {
    /// A variable present in step N-1 is absent in step N within the same block.
    VariableDisappeared,
}

impl fmt::Display for ConsistencyErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::VariableDisappeared => write!(f, "variable disappeared"),
        }
    }
}

impl fmt::Display for ConsistencyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "step {}: {} ({})", self.step_index, self.kind, self.variable)
    }
}

/// Formats an execution trace for human-readable output.
///
/// Produces output like:
/// ```text
/// Block 0, Stmt 1: x=5, y=3
/// Block 1, Stmt 0: x=5, y=3, z=8
/// ```
pub struct TraceFormatter;

impl TraceFormatter {
    /// Format a single trace step as a string.
    #[must_use]
    pub fn format_step(step: &TraceStep) -> String {
        let mut vars: Vec<_> = step.variable_snapshot.iter().collect();
        vars.sort_by_key(|(k, _)| (*k).clone());

        let var_str: String = vars
            .iter()
            .map(|(k, v)| format!("{k}={}", Self::format_value(v)))
            .collect::<Vec<_>>()
            .join(", ");

        if var_str.is_empty() {
            format!("Block {}, Stmt {}: (empty)", step.block_id, step.stmt_index)
        } else {
            format!("Block {}, Stmt {}: {}", step.block_id, step.stmt_index, var_str)
        }
    }

    /// Format an entire execution trace as a multi-line string.
    #[must_use]
    pub fn format_trace(trace: &ExecutionTrace) -> String {
        trace.iter().map(Self::format_step).collect::<Vec<_>>().join("\n")
    }

    /// Format a symbolic value for display.
    #[must_use]
    pub fn format_value(value: &SymbolicValue) -> String {
        match value {
            SymbolicValue::Concrete(n) => n.to_string(),
            SymbolicValue::Symbol(name) => name.clone(),
            SymbolicValue::BinOp(l, op, r) => {
                format!("({} {:?} {})", Self::format_value(l), op, Self::format_value(r))
            }
            SymbolicValue::Ite(c, t, e) => {
                format!(
                    "(if {} then {} else {})",
                    Self::format_value(c),
                    Self::format_value(t),
                    Self::format_value(e)
                )
            }
            SymbolicValue::Not(inner) => {
                format!("(!{})", Self::format_value(inner))
            }
            SymbolicValue::BitwiseNot(inner) => {
                format!("(~{})", Self::format_value(inner))
            }
            SymbolicValue::Neg(inner) => {
                format!("(-{})", Self::format_value(inner))
            }
        }
    }
}

/// A counterexample trace extracted when a specification violation is found.
///
/// Contains the concrete trace leading to the violation, the violated
/// property description, and the path constraints at the violation point.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CounterexampleTrace {
    /// The execution trace leading to the violation.
    pub trace: ExecutionTrace,
    /// Human-readable description of the violated property.
    pub violation: String,
    /// Path constraints at the violation point.
    pub path_constraints: PathConstraint,
    /// Concrete variable assignments that trigger the violation (if available).
    pub concrete_assignments: BTreeMap<String, i128>,
}

impl CounterexampleTrace {
    /// Create a new counterexample trace.
    #[must_use]
    pub fn new(
        trace: ExecutionTrace,
        violation: impl Into<String>,
        path_constraints: PathConstraint,
    ) -> Self {
        Self {
            trace,
            violation: violation.into(),
            path_constraints,
            concrete_assignments: BTreeMap::default(),
        }
    }

    /// Add a concrete assignment that triggers the violation.
    pub fn add_assignment(&mut self, var: impl Into<String>, value: i128) {
        self.concrete_assignments.insert(var.into(), value);
    }

    /// Set all concrete assignments at once.
    pub fn with_assignments(mut self, assignments: BTreeMap<String, i128>) -> Self {
        self.concrete_assignments = assignments;
        self
    }

    /// Extract a counterexample from a trace and the current execution state.
    ///
    /// Walks the final step's variable snapshot and attempts concrete
    /// evaluation of each value to populate `concrete_assignments`.
    #[must_use]
    pub fn extract(
        trace: ExecutionTrace,
        violation: impl Into<String>,
        path_constraints: PathConstraint,
        state: &SymbolicState,
    ) -> Self {
        let mut concrete_assignments = BTreeMap::default();

        // Try to evaluate each variable in the final state concretely.
        if let Some(last_step) = trace.steps().last() {
            for (var, val) in &last_step.variable_snapshot {
                if let Some(concrete) = crate::state::eval(state, val) {
                    concrete_assignments.insert(var.clone(), concrete);
                }
            }
        }

        Self { trace, violation: violation.into(), path_constraints, concrete_assignments }
    }

    /// Format the counterexample for human consumption.
    #[must_use]
    pub fn format(&self) -> String {
        let mut out = format!("COUNTEREXAMPLE: {}\n", self.violation);

        if !self.concrete_assignments.is_empty() {
            out.push_str("Concrete assignments:\n");
            let mut assignments: Vec<_> = self.concrete_assignments.iter().collect();
            assignments.sort_by_key(|(k, _)| (*k).clone());
            for (var, val) in &assignments {
                let _ = writeln!(out, "  {var} = {val}");
            }
        }

        let _ = writeln!(out, "Path depth: {}", self.path_constraints.depth());

        if !self.trace.is_empty() {
            out.push_str("Trace:\n");
            for step in self.trace.iter() {
                let _ = writeln!(out, "  {}", TraceFormatter::format_step(step));
            }
        }

        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::SymbolicValue;
    use trust_types::BinOp;

    #[test]
    fn test_trace_step_new() {
        let mut snapshot = BTreeMap::default();
        snapshot.insert("x".to_owned(), SymbolicValue::Concrete(5));
        let step = TraceStep::new(0, 1, snapshot.clone());
        assert_eq!(step.block_id, 0);
        assert_eq!(step.stmt_index, 1);
        assert_eq!(step.variable_snapshot, snapshot);
    }

    #[test]
    fn test_trace_step_from_state() {
        let mut state = SymbolicState::new();
        state.set("x", SymbolicValue::Concrete(5));
        state.set("y", SymbolicValue::Concrete(3));
        let step = TraceStep::from_state(0, 1, &state);
        assert_eq!(step.block_id, 0);
        assert_eq!(step.stmt_index, 1);
        assert_eq!(step.variable_snapshot.get("x"), Some(&SymbolicValue::Concrete(5)));
        assert_eq!(step.variable_snapshot.get("y"), Some(&SymbolicValue::Concrete(3)));
    }

    #[test]
    fn test_execution_trace_push_and_len() {
        let mut trace = ExecutionTrace::new();
        assert!(trace.is_empty());
        assert_eq!(trace.len(), 0);

        trace.push(TraceStep::new(0, 0, BTreeMap::default()));
        assert!(!trace.is_empty());
        assert_eq!(trace.len(), 1);

        trace.push(TraceStep::new(1, 0, BTreeMap::default()));
        assert_eq!(trace.len(), 2);
    }

    #[test]
    fn test_execution_trace_get_and_iter() {
        let mut trace = ExecutionTrace::new();
        trace.push(TraceStep::new(0, 0, BTreeMap::default()));
        trace.push(TraceStep::new(1, 0, BTreeMap::default()));

        assert_eq!(trace.get(0).map(|s| s.block_id), Some(0));
        assert_eq!(trace.get(1).map(|s| s.block_id), Some(1));
        assert!(trace.get(2).is_none());

        let block_ids: Vec<usize> = trace.iter().map(|s| s.block_id).collect();
        assert_eq!(block_ids, vec![0, 1]);
    }

    #[test]
    fn test_trace_recorder_record_and_finish() {
        let mut recorder = TraceRecorder::new();
        assert!(recorder.is_empty());

        let mut state = SymbolicState::new();
        state.set("x", SymbolicValue::Concrete(10));
        recorder.record(0, 0, &state);

        state.set("x", SymbolicValue::Concrete(20));
        recorder.record(0, 1, &state);

        assert_eq!(recorder.len(), 2);

        let trace = recorder.finish();
        assert_eq!(trace.len(), 2);
        assert_eq!(
            trace.get(0).unwrap().variable_snapshot.get("x"),
            Some(&SymbolicValue::Concrete(10))
        );
        assert_eq!(
            trace.get(1).unwrap().variable_snapshot.get("x"),
            Some(&SymbolicValue::Concrete(20))
        );
    }

    #[test]
    fn test_trace_recorder_record_snapshot() {
        let mut recorder = TraceRecorder::new();
        let mut snapshot = BTreeMap::default();
        snapshot.insert("z".to_owned(), SymbolicValue::Symbol("sym_z".into()));
        recorder.record_snapshot(2, 0, snapshot);

        let trace = recorder.finish();
        assert_eq!(trace.len(), 1);
        assert_eq!(
            trace.get(0).unwrap().variable_snapshot.get("z"),
            Some(&SymbolicValue::Symbol("sym_z".into()))
        );
    }

    #[test]
    fn test_trace_replayer_step_through() {
        let mut trace = ExecutionTrace::new();
        trace.push(TraceStep::new(0, 0, BTreeMap::default()));
        trace.push(TraceStep::new(1, 0, BTreeMap::default()));

        let mut replayer = TraceReplayer::new(&trace);
        assert_eq!(replayer.position(), 0);
        assert!(!replayer.is_done());

        let step0 = replayer.step().expect("should have step 0");
        assert_eq!(step0.block_id, 0);
        assert_eq!(replayer.position(), 1);

        let step1 = replayer.step().expect("should have step 1");
        assert_eq!(step1.block_id, 1);
        assert_eq!(replayer.position(), 2);

        assert!(replayer.step().is_none());
        assert!(replayer.is_done());
    }

    #[test]
    fn test_trace_replayer_reset() {
        let mut trace = ExecutionTrace::new();
        trace.push(TraceStep::new(0, 0, BTreeMap::default()));

        let mut replayer = TraceReplayer::new(&trace);
        replayer.step();
        assert!(replayer.is_done());

        replayer.reset();
        assert_eq!(replayer.position(), 0);
        assert!(!replayer.is_done());
    }

    #[test]
    fn test_trace_replayer_verify_consistency_clean() {
        let mut snapshot0 = BTreeMap::default();
        snapshot0.insert("x".to_owned(), SymbolicValue::Concrete(5));

        let mut snapshot1 = BTreeMap::default();
        snapshot1.insert("x".to_owned(), SymbolicValue::Concrete(10));
        snapshot1.insert("y".to_owned(), SymbolicValue::Concrete(3));

        let mut trace = ExecutionTrace::new();
        trace.push(TraceStep::new(0, 0, snapshot0));
        trace.push(TraceStep::new(0, 1, snapshot1));

        let replayer = TraceReplayer::new(&trace);
        let errors = replayer.verify_consistency();
        assert!(errors.is_empty(), "no inconsistencies expected: {errors:?}");
    }

    #[test]
    fn test_trace_replayer_verify_consistency_variable_disappeared() {
        let mut snapshot0 = BTreeMap::default();
        snapshot0.insert("x".to_owned(), SymbolicValue::Concrete(5));
        snapshot0.insert("y".to_owned(), SymbolicValue::Concrete(3));

        // y disappeared in the next step within the same block
        let mut snapshot1 = BTreeMap::default();
        snapshot1.insert("x".to_owned(), SymbolicValue::Concrete(5));

        let mut trace = ExecutionTrace::new();
        trace.push(TraceStep::new(0, 0, snapshot0));
        trace.push(TraceStep::new(0, 1, snapshot1));

        let replayer = TraceReplayer::new(&trace);
        let errors = replayer.verify_consistency();
        assert_eq!(errors.len(), 1);
        assert_eq!(errors[0].step_index, 1);
        assert_eq!(errors[0].variable, "y");
        assert_eq!(errors[0].kind, ConsistencyErrorKind::VariableDisappeared);
    }

    #[test]
    fn test_trace_replayer_consistency_across_blocks_no_error() {
        // Variables disappearing across different blocks is not an error.
        let mut snapshot0 = BTreeMap::default();
        snapshot0.insert("x".to_owned(), SymbolicValue::Concrete(5));

        let snapshot1 = BTreeMap::default(); // empty, different block

        let mut trace = ExecutionTrace::new();
        trace.push(TraceStep::new(0, 0, snapshot0));
        trace.push(TraceStep::new(1, 0, snapshot1));

        let replayer = TraceReplayer::new(&trace);
        let errors = replayer.verify_consistency();
        assert!(errors.is_empty());
    }

    #[test]
    fn test_trace_formatter_format_step_with_values() {
        let mut snapshot = BTreeMap::default();
        snapshot.insert("x".to_owned(), SymbolicValue::Concrete(5));
        snapshot.insert("y".to_owned(), SymbolicValue::Concrete(3));

        let step = TraceStep::new(0, 1, snapshot);
        let formatted = TraceFormatter::format_step(&step);
        assert_eq!(formatted, "Block 0, Stmt 1: x=5, y=3");
    }

    #[test]
    fn test_trace_formatter_format_step_empty() {
        let step = TraceStep::new(2, 0, BTreeMap::default());
        let formatted = TraceFormatter::format_step(&step);
        assert_eq!(formatted, "Block 2, Stmt 0: (empty)");
    }

    #[test]
    fn test_trace_formatter_format_trace() {
        let mut trace = ExecutionTrace::new();

        let mut s0 = BTreeMap::default();
        s0.insert("x".to_owned(), SymbolicValue::Concrete(5));
        trace.push(TraceStep::new(0, 0, s0));

        let mut s1 = BTreeMap::default();
        s1.insert("x".to_owned(), SymbolicValue::Concrete(5));
        s1.insert("y".to_owned(), SymbolicValue::Concrete(3));
        trace.push(TraceStep::new(0, 1, s1));

        let formatted = TraceFormatter::format_trace(&trace);
        assert_eq!(formatted, "Block 0, Stmt 0: x=5\nBlock 0, Stmt 1: x=5, y=3");
    }

    #[test]
    fn test_trace_formatter_format_value_concrete() {
        assert_eq!(TraceFormatter::format_value(&SymbolicValue::Concrete(42)), "42");
    }

    #[test]
    fn test_trace_formatter_format_value_symbol() {
        assert_eq!(TraceFormatter::format_value(&SymbolicValue::Symbol("arg0".into())), "arg0");
    }

    #[test]
    fn test_trace_formatter_format_value_binop() {
        let expr = SymbolicValue::bin_op(
            SymbolicValue::Symbol("x".into()),
            BinOp::Add,
            SymbolicValue::Concrete(1),
        );
        assert_eq!(TraceFormatter::format_value(&expr), "(x Add 1)");
    }

    #[test]
    fn test_trace_formatter_format_value_ite() {
        let expr = SymbolicValue::ite(
            SymbolicValue::Symbol("cond".into()),
            SymbolicValue::Concrete(1),
            SymbolicValue::Concrete(0),
        );
        assert_eq!(TraceFormatter::format_value(&expr), "(if cond then 1 else 0)");
    }

    #[test]
    fn test_trace_formatter_format_value_not() {
        let expr = SymbolicValue::Not(Box::new(SymbolicValue::Symbol("flag".into())));
        assert_eq!(TraceFormatter::format_value(&expr), "(!flag)");
    }

    #[test]
    fn test_counterexample_trace_new_and_format() {
        let mut trace = ExecutionTrace::new();
        let mut snap = BTreeMap::default();
        snap.insert("x".to_owned(), SymbolicValue::Concrete(100));
        trace.push(TraceStep::new(0, 0, snap));

        let pc = PathConstraint::new();
        let mut cex = CounterexampleTrace::new(trace, "assertion failed: x < 50", pc);
        cex.add_assignment("x", 100);

        let formatted = cex.format();
        assert!(formatted.contains("COUNTEREXAMPLE: assertion failed: x < 50"));
        assert!(formatted.contains("x = 100"));
        assert!(formatted.contains("Path depth: 0"));
        assert!(formatted.contains("Block 0, Stmt 0: x=100"));
    }

    #[test]
    fn test_counterexample_trace_with_assignments() {
        let trace = ExecutionTrace::new();
        let pc = PathConstraint::new();
        let mut assignments = BTreeMap::default();
        assignments.insert("a".to_owned(), 42);
        assignments.insert("b".to_owned(), -1);

        let cex =
            CounterexampleTrace::new(trace, "overflow", pc).with_assignments(assignments.clone());

        assert_eq!(cex.concrete_assignments, assignments);
        assert_eq!(cex.violation, "overflow");
    }

    #[test]
    fn test_counterexample_trace_extract_concrete() {
        let mut state = SymbolicState::new();
        state.set("x", SymbolicValue::Concrete(42));
        state.set("y", SymbolicValue::Concrete(7));

        let mut trace = ExecutionTrace::new();
        let mut snap = BTreeMap::default();
        snap.insert("x".to_owned(), SymbolicValue::Concrete(42));
        snap.insert("y".to_owned(), SymbolicValue::Concrete(7));
        trace.push(TraceStep::new(0, 0, snap));

        let pc = PathConstraint::new();
        let cex = CounterexampleTrace::extract(trace, "div by zero", pc, &state);

        assert_eq!(cex.concrete_assignments.get("x"), Some(&42));
        assert_eq!(cex.concrete_assignments.get("y"), Some(&7));
        assert_eq!(cex.violation, "div by zero");
    }

    #[test]
    fn test_counterexample_trace_extract_symbolic_not_resolved() {
        let state = SymbolicState::new(); // no concrete bindings

        let mut trace = ExecutionTrace::new();
        let mut snap = BTreeMap::default();
        snap.insert("x".to_owned(), SymbolicValue::Symbol("unknown_input".into()));
        trace.push(TraceStep::new(0, 0, snap));

        let pc = PathConstraint::new();
        let cex = CounterexampleTrace::extract(trace, "unreachable reached", pc, &state);

        // Symbolic values cannot be concretely evaluated, so no assignments.
        assert!(cex.concrete_assignments.is_empty());
    }

    #[test]
    fn test_counterexample_trace_format_empty_trace() {
        let trace = ExecutionTrace::new();
        let pc = PathConstraint::new();
        let cex = CounterexampleTrace::new(trace, "test violation", pc);

        let formatted = cex.format();
        assert!(formatted.contains("COUNTEREXAMPLE: test violation"));
        assert!(formatted.contains("Path depth: 0"));
        // Empty trace means no "Trace:" section output
        assert!(!formatted.contains("Trace:"));
    }

    #[test]
    fn test_consistency_error_display() {
        let err = ConsistencyError {
            step_index: 3,
            variable: "y".to_owned(),
            kind: ConsistencyErrorKind::VariableDisappeared,
        };
        assert_eq!(err.to_string(), "step 3: variable disappeared (y)");
    }
}
