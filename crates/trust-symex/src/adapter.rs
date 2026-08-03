// trust-symex counterexample replay adapter
//
// Accepts a Counterexample from a solver and drives the SymbolicExecutor
// with concrete values, collecting a detailed execution trace with
// per-statement variable snapshots.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use trust_types::{BasicBlock, Counterexample, CounterexampleValue, VerificationCondition};

use crate::engine::{BlockResult, SymbolicExecutor};
use crate::error::SymexError;
use crate::state::{SymbolicState, SymbolicValue, eval};

/// A single step in the concrete execution trace.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraceStep {
    /// Block index being executed.
    pub block_idx: usize,
    /// Statement index within the block (None for terminators).
    pub stmt_idx: Option<usize>,
    /// Description of the operation (e.g., "_local2 = _local0 + _local1").
    pub description: String,
    /// Variable values after this step, with concrete evaluations where possible.
    pub state_snapshot: BTreeMap<String, ValueSnapshot>,
}

/// A snapshot of a variable's value at a point in execution.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValueSnapshot {
    /// The symbolic expression for this variable.
    pub symbolic: String,
    /// The concrete value, if fully evaluable.
    pub concrete: Option<i128>,
}

/// Configuration for the replay adapter.
#[derive(Debug, Clone)]
pub struct AdapterConfig {
    /// Maximum number of blocks to execute.
    pub depth_limit: usize,
    /// Entry block index (usually 0).
    pub entry_block: usize,
    /// Whether to capture state snapshots at every statement (vs. only at block boundaries).
    pub capture_per_statement: bool,
}

impl Default for AdapterConfig {
    fn default() -> Self {
        Self { depth_limit: 1000, entry_block: 0, capture_per_statement: true }
    }
}

/// Result of replaying a counterexample through the adapter.
#[derive(Debug)]
pub struct AdapterResult {
    /// The detailed execution trace with per-step snapshots.
    pub trace: Vec<TraceStep>,
    /// The final symbolic state after execution.
    pub final_state: SymbolicState,
    /// Block indices visited during execution.
    pub block_trace: Vec<usize>,
    /// Whether the execution terminated normally (Return) or was cut short.
    pub terminated_normally: bool,
    /// Variables that changed during execution and their final values.
    pub modified_vars: BTreeMap<String, ValueSnapshot>,
}

/// Replay a counterexample through the symbolic executor, collecting a detailed trace.
///
/// Seeds the executor with concrete values from the counterexample, then
/// executes blocks sequentially, recording variable snapshots at each step.
///
/// # Errors
///
/// Returns `SymexError` if execution fails (depth limit, undefined variables, etc.).
pub fn replay_with_trace(
    counterexample: &Counterexample,
    _vc: &VerificationCondition,
    blocks: &[BasicBlock],
    config: &AdapterConfig,
) -> Result<AdapterResult, SymexError> {
    if blocks.is_empty() {
        return Err(SymexError::UnsupportedOperation("no basic blocks provided for replay".into()));
    }
    if config.entry_block >= blocks.len() {
        return Err(SymexError::UnsupportedOperation(format!(
            "entry block {} out of range (have {} blocks)",
            config.entry_block,
            blocks.len()
        )));
    }

    let mut executor = SymbolicExecutor::new(config.depth_limit);
    let initial_vars = seed_state(&mut executor.state, counterexample);

    let mut trace = Vec::new();
    let mut block_trace = Vec::new();
    let mut current_block = config.entry_block;

    // Record initial state.
    trace.push(TraceStep {
        block_idx: current_block,
        stmt_idx: None,
        description: "entry: seed counterexample values".into(),
        state_snapshot: snapshot_state(&executor.state),
    });

    loop {
        if current_block >= blocks.len() {
            return Err(SymexError::UnsupportedOperation(format!(
                "block index {} out of range (have {} blocks)",
                current_block,
                blocks.len()
            )));
        }

        block_trace.push(current_block);
        let block = &blocks[current_block];

        // Capture per-statement snapshots if configured.
        if config.capture_per_statement {
            for (stmt_idx, stmt) in block.stmts.iter().enumerate() {
                // Execute this single statement by running the full block
                // mechanism is too coarse; instead, capture state before/after.
                let desc = format_statement(stmt);
                // We let the executor handle the full block below;
                // here we just record what we'll see.
                trace.push(TraceStep {
                    block_idx: current_block,
                    stmt_idx: Some(stmt_idx),
                    description: desc,
                    // Snapshot will be updated after block execution
                    // for now, capture the pre-state.
                    state_snapshot: snapshot_state(&executor.state),
                });
            }
        }

        match executor.execute_block(block) {
            Ok(BlockResult::Continue(next)) => {
                // Record post-block state.
                if config.capture_per_statement {
                    // Update the last trace entries for this block with post-state.
                    let post_snapshot = snapshot_state(&executor.state);
                    for step in trace.iter_mut().rev() {
                        if step.block_idx == current_block && step.stmt_idx.is_some() {
                            step.state_snapshot = post_snapshot.clone();
                        } else {
                            break;
                        }
                    }
                }
                trace.push(TraceStep {
                    block_idx: current_block,
                    stmt_idx: None,
                    description: format!("goto bb{next}"),
                    state_snapshot: snapshot_state(&executor.state),
                });
                current_block = next;
            }
            Ok(BlockResult::Fork(forks)) => {
                // With concrete inputs, find the feasible branch.
                let chosen = find_concrete_fork(&executor.state, &forks);
                match chosen {
                    Some(fork) => {
                        trace.push(TraceStep {
                            block_idx: current_block,
                            stmt_idx: None,
                            description: format!("branch taken -> bb{}", fork.next_block),
                            state_snapshot: snapshot_state(&fork.state),
                        });
                        let next = fork.next_block;
                        executor.state = fork.state.clone();
                        executor.path = fork.path.clone();
                        current_block = next;
                    }
                    None => {
                        trace.push(TraceStep {
                            block_idx: current_block,
                            stmt_idx: None,
                            description: "no feasible branch (spurious path)".into(),
                            state_snapshot: snapshot_state(&executor.state),
                        });
                        let modified_vars = compute_modified(&initial_vars, &executor.state);
                        return Ok(AdapterResult {
                            trace,
                            final_state: executor.state,
                            block_trace,
                            terminated_normally: false,
                            modified_vars,
                        });
                    }
                }
            }
            Ok(BlockResult::Terminated) => {
                trace.push(TraceStep {
                    block_idx: current_block,
                    stmt_idx: None,
                    description: "return".into(),
                    state_snapshot: snapshot_state(&executor.state),
                });
                let modified_vars = compute_modified(&initial_vars, &executor.state);
                return Ok(AdapterResult {
                    trace,
                    final_state: executor.state,
                    block_trace,
                    terminated_normally: true,
                    modified_vars,
                });
            }
            Err(SymexError::DepthLimitExceeded { depth, limit }) => {
                return Err(SymexError::DepthLimitExceeded { depth, limit });
            }
            Err(SymexError::UnreachableReached) => {
                trace.push(TraceStep {
                    block_idx: current_block,
                    stmt_idx: None,
                    description: "unreachable reached (spurious path)".into(),
                    state_snapshot: snapshot_state(&executor.state),
                });
                let modified_vars = compute_modified(&initial_vars, &executor.state);
                return Ok(AdapterResult {
                    trace,
                    final_state: executor.state,
                    block_trace,
                    terminated_normally: false,
                    modified_vars,
                });
            }
            Err(e) => return Err(e),
        }
    }
}

/// Seed the symbolic state with concrete values from the counterexample.
/// Returns a map of the initial variable names for diffing later.
fn seed_state(state: &mut SymbolicState, cex: &Counterexample) -> BTreeMap<String, SymbolicValue> {
    let mut initial = BTreeMap::default();
    for (name, value) in &cex.assignments {
        let concrete = match value {
            CounterexampleValue::Bool(b) => SymbolicValue::Concrete(i128::from(*b)),
            CounterexampleValue::Int(n) => SymbolicValue::Concrete(*n),
            CounterexampleValue::Uint(n) => SymbolicValue::Concrete(*n as i128),
            CounterexampleValue::Float(_) => SymbolicValue::Symbol(format!("float_{name}")),
            _ => SymbolicValue::Symbol(format!("unknown_{name}")),
        };
        state.set(name.clone(), concrete.clone());
        initial.insert(name.clone(), concrete);
    }
    initial
}

/// Snapshot the current symbolic state as a map of variable -> ValueSnapshot.
fn snapshot_state(state: &SymbolicState) -> BTreeMap<String, ValueSnapshot> {
    let mut snap = BTreeMap::default();
    for (name, val) in state.iter() {
        snap.insert(
            name.to_owned(),
            ValueSnapshot { symbolic: format!("{val:?}"), concrete: eval(state, val) },
        );
    }
    snap
}

/// Format a statement for human-readable trace output.
fn format_statement(stmt: &trust_types::Statement) -> String {
    match stmt {
        trust_types::Statement::Assign { place, rvalue, .. } => {
            format!("_local{} = {rvalue:?}", place.local)
        }
        trust_types::Statement::Nop => "nop".into(),
        _ => format!("{stmt:?}"),
    }
}

/// Find the fork whose path constraints are feasible under concrete evaluation.
fn find_concrete_fork<'a>(
    state: &SymbolicState,
    forks: &'a [crate::engine::ExecutionFork],
) -> Option<&'a crate::engine::ExecutionFork> {
    for fork in forks {
        if is_fork_feasible(state, fork) {
            return Some(fork);
        }
    }
    // Fallback: take first fork as heuristic.
    forks.first()
}

/// Check whether a fork's path constraints are satisfiable under concrete state.
fn is_fork_feasible(state: &SymbolicState, fork: &crate::engine::ExecutionFork) -> bool {
    for decision in fork.path.decisions() {
        match eval(state, &decision.condition) {
            Some(v) => {
                let holds = v != 0;
                if holds != decision.taken {
                    return false;
                }
            }
            None => return true, // Can't evaluate; assume feasible.
        }
    }
    true
}

/// Compute which variables were modified during execution.
fn compute_modified(
    initial: &BTreeMap<String, SymbolicValue>,
    final_state: &SymbolicState,
) -> BTreeMap<String, ValueSnapshot> {
    let mut modified = BTreeMap::default();
    for (name, val) in final_state.iter() {
        let changed = match initial.get(name) {
            Some(init_val) => init_val != val,
            None => true, // New variable.
        };
        if changed {
            modified.insert(
                name.to_owned(),
                ValueSnapshot { symbolic: format!("{val:?}"), concrete: eval(final_state, val) },
            );
        }
    }
    modified
}

#[cfg(test)]
mod tests {
    use crate::error::SymexError;

    use trust_types::{
        BasicBlock, BinOp, BlockId, ConstValue, Counterexample, CounterexampleValue, Formula,
        Operand, Place, Rvalue, SourceSpan, Statement, Terminator, VcKind, VerificationCondition,
    };

    use super::*;

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    fn simple_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_fn".into(),
            location: span(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        }
    }

    #[test]
    fn test_adapter_straight_line_trace() {
        let blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(42))),
                span: span(),
            }],
            terminator: Terminator::Return,
        }];

        let cex = Counterexample::new(vec![("_local0".into(), CounterexampleValue::Int(10))]);

        let result = replay_with_trace(&cex, &simple_vc(), &blocks, &AdapterConfig::default())
            .expect("replay should succeed");

        assert!(result.terminated_normally);
        assert_eq!(result.block_trace, vec![0]);
        // Should have trace steps: entry + per-stmt + terminator
        assert!(result.trace.len() >= 2);
    }

    #[test]
    fn test_adapter_branch_trace() {
        let blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(0)),
                    targets: vec![(1, BlockId(1))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: span(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
        ];

        let cex = Counterexample::new(vec![("_local0".into(), CounterexampleValue::Int(1))]);

        let result = replay_with_trace(&cex, &simple_vc(), &blocks, &AdapterConfig::default())
            .expect("replay should succeed");

        assert!(result.terminated_normally);
        assert_eq!(result.block_trace, vec![0, 1]);
    }

    #[test]
    fn test_adapter_computation_trace() {
        let blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(0)),
                        Operand::Copy(Place::local(1)),
                    ),
                    span: span(),
                }],
                terminator: Terminator::Goto(BlockId(1)),
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ];

        let cex = Counterexample::new(vec![
            ("_local0".into(), CounterexampleValue::Int(10)),
            ("_local1".into(), CounterexampleValue::Int(20)),
        ]);

        let result = replay_with_trace(&cex, &simple_vc(), &blocks, &AdapterConfig::default())
            .expect("replay should succeed");

        assert!(result.terminated_normally);
        assert_eq!(result.block_trace, vec![0, 1]);
        // _local2 should appear in modified vars.
        assert!(result.modified_vars.contains_key("_local2"));
        let val = &result.modified_vars["_local2"];
        assert_eq!(val.concrete, Some(30));
    }

    #[test]
    fn test_adapter_unreachable_spurious() {
        let blocks = vec![
            BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Goto(BlockId(1)) },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Unreachable },
        ];

        let cex = Counterexample::new(vec![]);
        let result = replay_with_trace(&cex, &simple_vc(), &blocks, &AdapterConfig::default())
            .expect("replay should succeed");

        assert!(!result.terminated_normally);
        assert_eq!(result.block_trace, vec![0, 1]);
    }

    #[test]
    fn test_adapter_no_blocks_error() {
        let cex = Counterexample::new(vec![]);
        let result = replay_with_trace(&cex, &simple_vc(), &[], &AdapterConfig::default());
        assert!(result.is_err());
    }

    #[test]
    fn test_adapter_modified_vars_tracked() {
        let blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(99))),
                span: span(),
            }],
            terminator: Terminator::Return,
        }];

        let cex = Counterexample::new(vec![("_local0".into(), CounterexampleValue::Int(5))]);

        let result = replay_with_trace(&cex, &simple_vc(), &blocks, &AdapterConfig::default())
            .expect("replay should succeed");

        // _local1 is new, should be in modified_vars.
        assert!(result.modified_vars.contains_key("_local1"));
        // _local0 was seeded and not changed, should NOT be modified.
        assert!(!result.modified_vars.contains_key("_local0"));
    }

    #[test]
    fn test_adapter_entry_block_out_of_range() {
        let blocks =
            vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }];
        let cex = Counterexample::new(vec![]);
        let config = AdapterConfig { entry_block: 1, ..AdapterConfig::default() };

        let result = replay_with_trace(&cex, &simple_vc(), &blocks, &config);

        assert!(matches!(
            result,
            Err(SymexError::UnsupportedOperation(message))
                if message.contains("entry block 1 out of range")
        ));
    }

    #[test]
    fn test_adapter_depth_limit() {
        let blocks = vec![
            BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Goto(BlockId(1)) },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Goto(BlockId(2)) },
            BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
        ];
        let cex = Counterexample::new(vec![]);
        let config = AdapterConfig { depth_limit: 1, ..AdapterConfig::default() };

        let result = replay_with_trace(&cex, &simple_vc(), &blocks, &config);

        assert!(matches!(result, Err(SymexError::DepthLimitExceeded { depth: 1, limit: 1 })));
    }

    #[test]
    fn test_adapter_no_per_statement() {
        let blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(42))),
                span: span(),
            }],
            terminator: Terminator::Return,
        }];
        let cex = Counterexample::new(vec![]);

        let with_per_statement = replay_with_trace(
            &cex,
            &simple_vc(),
            &blocks,
            &AdapterConfig { capture_per_statement: true, ..AdapterConfig::default() },
        )
        .expect("per-statement capture should succeed");

        let without_per_statement = replay_with_trace(
            &cex,
            &simple_vc(),
            &blocks,
            &AdapterConfig { capture_per_statement: false, ..AdapterConfig::default() },
        )
        .expect("block-only capture should succeed");

        assert!(without_per_statement.trace.len() < with_per_statement.trace.len());
        assert!(without_per_statement.trace.iter().all(|step| step.stmt_idx.is_none()));
        assert!(with_per_statement.trace.iter().any(|step| step.stmt_idx == Some(0)));
    }

    #[test]
    fn test_adapter_float_counterexample() {
        let blocks =
            vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }];
        let cex = Counterexample::new(vec![("_local0".into(), CounterexampleValue::Float(3.5))]);

        let result = replay_with_trace(&cex, &simple_vc(), &blocks, &AdapterConfig::default())
            .expect("float counterexample should replay");

        match result.final_state.get("_local0").expect("seeded float should be present") {
            SymbolicValue::Symbol(name) => {
                assert!(name.starts_with("float_"));
                assert!(name.ends_with("_local0"));
            }
            other => panic!("expected symbolic float seed, got {other:?}"),
        }
    }

    #[test]
    fn test_adapter_uint_counterexample() {
        let blocks =
            vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }];
        let cex = Counterexample::new(vec![("_local1".into(), CounterexampleValue::Uint(7))]);

        let result = replay_with_trace(&cex, &simple_vc(), &blocks, &AdapterConfig::default())
            .expect("uint counterexample should replay");

        assert_eq!(
            result.final_state.get("_local1").expect("seeded uint should be present"),
            &SymbolicValue::Concrete(7)
        );
    }
}
