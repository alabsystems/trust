// trust-symex concolic execution engine
//
// Main concolic (concrete + symbolic) execution loop. Drives the
// concrete executor with concrete inputs, collects symbolic path
// constraints, negates constraints to explore new paths, and
// accumulates counterexamples. Implements the DART/SAGE exploration
// strategy (Godefroid et al., 2005/2008).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use trust_types::{
    BasicBlock, BinOp, ConstValue, Counterexample, Formula, Operand, Place, Rvalue, Statement,
    Terminator, Ty, UnOp, VcKind, VerificationCondition,
};

use crate::concrete::{ConcolicValue, ConcreteExecutor, run_concrete};
use crate::constraints::{ConstraintCollector, NegationStrategy};
use crate::coverage::CoverageMap;
use crate::engine::place_to_name;
use crate::error::SymexError;
use crate::state::SymbolicValue;

/// Configuration for the concolic exploration engine.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConcolicConfig {
    /// Maximum number of exploration iterations (paths to try).
    pub max_iterations: usize,
    /// Maximum number of basic blocks per concrete execution run.
    pub step_limit: usize,
    /// Constraint negation strategy.
    pub strategy: NegationStrategy,
    /// Whether to collect coverage information.
    pub track_coverage: bool,
}

impl Default for ConcolicConfig {
    fn default() -> Self {
        Self {
            max_iterations: 100,
            step_limit: 1000,
            strategy: NegationStrategy::Generational,
            track_coverage: true,
        }
    }
}

/// Result of a single concolic exploration run.
#[derive(Debug, Clone)]
pub struct ExplorationResult {
    /// Counterexamples found (inputs that violate a verification condition).
    pub counterexamples: Vec<Counterexample>,
    /// Number of paths explored.
    pub paths_explored: usize,
    /// Number of solver queries issued.
    pub solver_queries: usize,
    /// Coverage information (if tracking was enabled).
    pub coverage: CoverageMap,
}

/// Trait for solving constraint formulas. Implementors connect to an
/// actual SMT solver (e.g., ay). The concolic engine uses this to
/// find new inputs satisfying negated path constraints.
pub trait ConstraintSolver {
    /// Solve a formula. Returns `Some(assignments)` if satisfiable,
    /// `None` if unsatisfiable or the solver times out.
    fn solve(&mut self, formula: &Formula) -> Option<Vec<(String, i128)>>;
}

/// A simple mock solver for testing that accepts all formulas and
/// returns default values.
#[derive(Debug, Default)]
pub struct MockSolver {
    /// Number of queries received.
    pub query_count: usize,
    /// Canned responses: index -> assignments. If no entry, returns default.
    pub responses: BTreeMap<usize, Option<Vec<(String, i128)>>>,
}

impl ConstraintSolver for MockSolver {
    fn solve(&mut self, _formula: &Formula) -> Option<Vec<(String, i128)>> {
        let idx = self.query_count;
        self.query_count += 1;
        if let Some(response) = self.responses.get(&idx) {
            response.clone()
        } else {
            // Default: return a simple model with value 0 for common variable names.
            Some(vec![("x".to_string(), 0), ("y".to_string(), 0), ("_local0".to_string(), 0)])
        }
    }
}

/// The concolic execution engine.
///
/// Orchestrates the loop:
/// 1. Run the program concretely with current inputs.
/// 2. Collect symbolic path constraints from the run.
/// 3. Check if any verification condition was violated.
/// 4. Negate constraints to produce new inputs.
/// 5. Repeat until coverage is complete or the iteration budget is exhausted.
pub struct ConcolicEngine<S: ConstraintSolver> {
    /// The MIR basic blocks to execute.
    blocks: Vec<BasicBlock>,
    /// Verification conditions to check.
    vcs: Vec<VerificationCondition>,
    /// The solver for constraint queries.
    solver: S,
    /// Configuration.
    config: ConcolicConfig,
    /// Worklist of input vectors to try.
    worklist: Vec<BTreeMap<String, ConcolicValue>>,
    /// Coverage map.
    coverage: CoverageMap,
    /// Found counterexamples.
    counterexamples: Vec<Counterexample>,
    /// Total paths explored.
    paths_explored: usize,
    /// Total solver queries.
    solver_queries: usize,
}

impl<S: ConstraintSolver> ConcolicEngine<S> {
    /// Create a new concolic engine.
    pub fn new(
        blocks: Vec<BasicBlock>,
        vcs: Vec<VerificationCondition>,
        solver: S,
        config: ConcolicConfig,
    ) -> Self {
        Self {
            blocks,
            vcs,
            solver,
            config,
            worklist: Vec::new(),
            coverage: CoverageMap::new(),
            counterexamples: Vec::new(),
            paths_explored: 0,
            solver_queries: 0,
        }
    }

    /// Add an initial input vector to the worklist.
    pub fn add_initial_input(&mut self, inputs: BTreeMap<String, ConcolicValue>) {
        self.worklist.push(inputs);
    }

    /// Add a symbolic input seed: zero concrete values for all named symbols.
    pub fn add_symbolic_seeds(&mut self, names: &[&str]) {
        let mut inputs = BTreeMap::default();
        for name in names {
            inputs.insert(
                name.to_string(),
                ConcolicValue::with_shadow(0, SymbolicValue::Symbol(name.to_string())),
            );
        }
        self.worklist.push(inputs);
    }

    /// Run the concolic exploration loop.
    ///
    /// Returns an `ExplorationResult` containing any counterexamples found,
    /// coverage information, and exploration statistics.
    pub fn explore(&mut self) -> Result<ExplorationResult, SymexError> {
        // Ensure we have at least one input to start with.
        if self.worklist.is_empty() {
            self.worklist.push(BTreeMap::default());
        }

        while self.paths_explored < self.config.max_iterations {
            let inputs = match self.worklist.pop() {
                Some(i) => i,
                None => break, // No more inputs to try.
            };

            validate_concolic_execution(&self.blocks, &inputs, self.config.step_limit)?;
            let executor = run_concrete(&self.blocks, &inputs, self.config.step_limit)?;

            self.paths_explored += 1;

            // Record coverage.
            if self.config.track_coverage {
                let branch_decisions: Vec<(usize, bool)> =
                    executor.symbolic_branches.iter().map(|b| (b.block_id, b.taken)).collect();
                self.coverage.record_path(&branch_decisions, executor.path.depth());
            }

            // Check VCs against the current path.
            self.check_vcs(&executor, &inputs);

            // Collect and negate constraints.
            let mut collector = ConstraintCollector::new();
            collector.import_branches(&executor.symbolic_branches);
            let prefixes = collector.negate(self.config.strategy);

            // For each negated prefix, ask the solver for a new input.
            for prefix in &prefixes {
                self.solver_queries += 1;
                if let Some(assignments) = self.solver.solve(&prefix.formula) {
                    let new_inputs = assignments_to_inputs(&assignments);
                    self.worklist.push(new_inputs);
                }
            }
        }

        Ok(ExplorationResult {
            counterexamples: self.counterexamples.clone(),
            paths_explored: self.paths_explored,
            solver_queries: self.solver_queries,
            coverage: self.coverage.clone(),
        })
    }

    /// Check verification conditions against a concrete execution.
    fn check_vcs(&mut self, executor: &ConcreteExecutor, inputs: &BTreeMap<String, ConcolicValue>) {
        for vc in &self.vcs {
            // Simple check: evaluate the VC formula concretely.
            // If it evaluates to false, we have a counterexample.
            if let Some(violated) = check_vc_concrete(vc, executor, inputs) {
                self.counterexamples.push(violated);
            }
        }
    }
}

/// Check a single VC against concrete execution state.
/// Returns a Counterexample if the VC is violated.
fn check_vc_concrete(
    _vc: &VerificationCondition,
    _executor: &ConcreteExecutor,
    inputs: &BTreeMap<String, ConcolicValue>,
) -> Option<Counterexample> {
    // In a full implementation, we would evaluate the VC formula against
    // the executor's state. For now, we only produce counterexamples when
    // an explicit assertion failure occurs (handled by the executor hitting
    // UnreachableReached). This function is a hook for future VC evaluation.
    let _ = inputs;
    None
}

/// Convert solver assignments to a concolic input map.
fn assignments_to_inputs(assignments: &[(String, i128)]) -> BTreeMap<String, ConcolicValue> {
    let mut inputs = BTreeMap::default();
    for (name, value) in assignments {
        inputs.insert(
            name.clone(),
            ConcolicValue::with_shadow(*value, SymbolicValue::Symbol(name.clone())),
        );
    }
    inputs
}

fn validate_concolic_execution(
    blocks: &[BasicBlock],
    inputs: &BTreeMap<String, ConcolicValue>,
    step_limit: usize,
) -> Result<(), SymexError> {
    let mut values: BTreeMap<String, i128> =
        inputs.iter().map(|(name, value)| (name.clone(), value.concrete)).collect();

    let mut current_block = 0usize;
    let mut steps = 0usize;

    loop {
        if steps >= step_limit {
            return Err(SymexError::DepthLimitExceeded { depth: steps, limit: step_limit });
        }
        steps += 1;

        let block = blocks.get(current_block).ok_or_else(|| {
            SymexError::UnsupportedOperation(format!("block {current_block} out of range"))
        })?;

        for stmt in &block.stmts {
            validate_statement(stmt, &mut values)?;
        }

        match validate_terminator(&block.terminator, &values)? {
            Some(next) => current_block = next,
            None => return Ok(()),
        }
    }
}

fn validate_statement(
    stmt: &Statement,
    values: &mut BTreeMap<String, i128>,
) -> Result<(), SymexError> {
    match stmt {
        Statement::Assign { place, rvalue, .. } => {
            let value = eval_mir_rvalue(rvalue, values)?;
            values.insert(place_to_name(place), value);
            Ok(())
        }
        Statement::StorageLive(_)
        | Statement::StorageDead(_)
        | Statement::PlaceMention(_)
        | Statement::Coverage
        | Statement::ConstEvalCounter
        | Statement::Nop => Ok(()),
        other => Err(SymexError::UnsupportedOperation(format!(
            "unsupported concolic statement: {other:?}"
        ))),
    }
}

fn validate_terminator(
    term: &Terminator,
    values: &BTreeMap<String, i128>,
) -> Result<Option<usize>, SymexError> {
    match term {
        Terminator::Goto(target) => Ok(Some(target.0)),
        Terminator::Return => Ok(None),
        Terminator::Unreachable => Err(SymexError::UnreachableReached),
        Terminator::SwitchInt { discr, targets, otherwise, .. } => {
            let discr_value = eval_mir_operand(discr, values)?;
            for (value, target) in targets {
                if discr_value == *value as i128 {
                    return Ok(Some(target.0));
                }
            }
            Ok(Some(otherwise.0))
        }
        Terminator::Assert { cond, expected, target, .. } => {
            let actual = eval_mir_operand(cond, values)? != 0;
            if actual != *expected {
                return Err(SymexError::AssertionFailed { expected: *expected, actual });
            }
            Ok(Some(target.0))
        }
        Terminator::Drop { place, .. } => Err(SymexError::UnsupportedOperation(format!(
            "unsupported concolic drop terminator: {}",
            place_to_name(place)
        ))),
        Terminator::Call { .. } | Terminator::Opaque { .. } => Err(
            SymexError::UnsupportedOperation(format!("unsupported concolic terminator: {term:?}")),
        ),
        other => Err(SymexError::UnsupportedOperation(format!(
            "unsupported concolic terminator: {other:?}"
        ))),
    }
}

fn eval_mir_rvalue(rvalue: &Rvalue, values: &BTreeMap<String, i128>) -> Result<i128, SymexError> {
    match rvalue {
        Rvalue::Use(op) => eval_mir_operand(op, values),
        Rvalue::BinaryOp(op, lhs, rhs) | Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
            let l = eval_mir_operand(lhs, values)?;
            let r = eval_mir_operand(rhs, values)?;
            eval_mir_binop(l, *op, r)
        }
        Rvalue::UnaryOp(UnOp::Neg, op) => Ok(eval_mir_operand(op, values)?.wrapping_neg()),
        Rvalue::UnaryOp(UnOp::Not, op) => Ok(!eval_mir_operand(op, values)?),
        Rvalue::UnaryOp(UnOp::PtrMetadata, _) => Err(SymexError::UnsupportedOperation(
            "unsupported concolic unary operation: PtrMetadata".into(),
        )),
        Rvalue::UnaryOp(other, _) => Err(SymexError::UnsupportedOperation(format!(
            "unsupported concolic unary operation: {other:?}"
        ))),
        Rvalue::CopyForDeref(place) => eval_mir_place(place, values),
        Rvalue::Cast(op, dest_ty) => {
            let value = eval_mir_operand(op, values)?;
            apply_mir_int_cast(value, dest_ty)
        }
        Rvalue::Ref { .. }
        | Rvalue::Aggregate(_, _)
        | Rvalue::Discriminant(_)
        | Rvalue::Len(_)
        | Rvalue::Repeat(_, _)
        | Rvalue::AddressOf(_, _)
        | Rvalue::Unsupported { .. } => Err(SymexError::UnsupportedOperation(format!(
            "unsupported concolic rvalue: {rvalue:?}"
        ))),
        other => {
            Err(SymexError::UnsupportedOperation(format!("unsupported concolic rvalue: {other:?}")))
        }
    }
}

fn eval_mir_operand(
    operand: &Operand,
    values: &BTreeMap<String, i128>,
) -> Result<i128, SymexError> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => eval_mir_place(place, values),
        Operand::Constant(value) => eval_mir_const(value),
        Operand::Symbolic(_) | Operand::Unsupported { .. } => Err(
            SymexError::UnsupportedOperation(format!("unsupported concolic operand: {operand:?}")),
        ),
        other => Err(SymexError::UnsupportedOperation(format!(
            "unsupported concolic operand: {other:?}"
        ))),
    }
}

fn eval_mir_place(place: &Place, values: &BTreeMap<String, i128>) -> Result<i128, SymexError> {
    let name = place_to_name(place);
    values.get(&name).copied().ok_or(SymexError::UndefinedVariable(name))
}

fn eval_mir_const(value: &ConstValue) -> Result<i128, SymexError> {
    match value {
        ConstValue::Bool(value) => Ok(i128::from(*value)),
        ConstValue::Int(value) => Ok(*value),
        ConstValue::Uint(value, _) => Ok(*value as i128),
        ConstValue::Unit => Ok(0),
        ConstValue::CallableItem { .. } => Err(SymexError::UnsupportedOperation(
            "callable-item constants require identity-aware concolic semantics".to_string(),
        )),
        ConstValue::Float(_) | ConstValue::FloatBits { .. } => Err(
            SymexError::UnsupportedOperation(format!("unsupported concolic constant: {value:?}")),
        ),
        other => Err(SymexError::UnsupportedOperation(format!(
            "unsupported concolic constant: {other:?}"
        ))),
    }
}

fn eval_mir_binop(l: i128, op: BinOp, r: i128) -> Result<i128, SymexError> {
    match op {
        BinOp::Add => Ok(l.wrapping_add(r)),
        BinOp::Sub => Ok(l.wrapping_sub(r)),
        BinOp::Mul => Ok(l.wrapping_mul(r)),
        BinOp::Div => {
            if r == 0 {
                Err(SymexError::UnsupportedOperation("division by zero".into()))
            } else {
                Ok(l.wrapping_div(r))
            }
        }
        BinOp::Rem => {
            if r == 0 {
                Err(SymexError::UnsupportedOperation("remainder by zero".into()))
            } else {
                Ok(l.wrapping_rem(r))
            }
        }
        BinOp::Eq => Ok(i128::from(l == r)),
        BinOp::Ne => Ok(i128::from(l != r)),
        BinOp::Lt => Ok(i128::from(l < r)),
        BinOp::Le => Ok(i128::from(l <= r)),
        BinOp::Gt => Ok(i128::from(l > r)),
        BinOp::Ge => Ok(i128::from(l >= r)),
        BinOp::BitAnd => Ok(l & r),
        BinOp::BitOr => Ok(l | r),
        BinOp::BitXor => Ok(l ^ r),
        BinOp::Shl => Ok(l.wrapping_shl(u32::try_from(r).unwrap_or(128).min(127))),
        BinOp::Shr => Ok(l.wrapping_shr(u32::try_from(r).unwrap_or(128).min(127))),
        BinOp::Cmp => Ok(if l < r {
            -1
        } else if l == r {
            0
        } else {
            1
        }),
        other => Err(SymexError::UnsupportedOperation(format!(
            "unsupported concolic binary operation: {other:?}"
        ))),
    }
}

fn apply_mir_int_cast(value: i128, dest_ty: &Ty) -> Result<i128, SymexError> {
    let Ty::Int { width, signed } = dest_ty else {
        return Err(SymexError::UnsupportedOperation(format!(
            "unsupported concolic cast target: {dest_ty:?}"
        )));
    };
    if *width == 0 {
        return Err(SymexError::UnsupportedOperation("zero-width integer cast".into()));
    }
    if *width >= 128 {
        return Ok(value);
    }
    let mask = (1i128 << *width) - 1;
    let truncated = value & mask;
    if *signed {
        let sign_bit = 1i128 << (*width - 1);
        Ok(if truncated & sign_bit != 0 { truncated | !mask } else { truncated })
    } else {
        Ok(truncated)
    }
}

/// Top-level exploration API.
///
/// Runs concolic execution over the given basic blocks, checking the
/// provided verification conditions, and returns any counterexamples found.
///
/// This is the main entry point for external callers.
pub fn explore(
    blocks: &[BasicBlock],
    vcs: &[VerificationCondition],
    config: &ConcolicConfig,
) -> Result<Vec<Counterexample>, SymexError> {
    let mut engine =
        ConcolicEngine::new(blocks.to_vec(), vcs.to_vec(), MockSolver::default(), config.clone());

    // Seed with default symbolic inputs for function arguments.
    // In a real integration, the caller provides input names from the function signature.
    engine.add_symbolic_seeds(&[]);
    engine.worklist.push(BTreeMap::default());

    let result = engine.explore()?;
    Ok(result.counterexamples)
}

/// Explore with a custom solver.
pub fn explore_with_solver<S: ConstraintSolver>(
    blocks: &[BasicBlock],
    vcs: &[VerificationCondition],
    config: &ConcolicConfig,
    solver: S,
    input_names: &[&str],
) -> Result<ExplorationResult, SymexError> {
    let mut engine = ConcolicEngine::new(blocks.to_vec(), vcs.to_vec(), solver, config.clone());
    engine.add_symbolic_seeds(input_names);
    engine.explore()
}

// ---------------------------------------------------------------------------
// Fast bug-finding lane: ConcolicState + ConcolicResult + standalone helpers
// ---------------------------------------------------------------------------

/// Combined concrete + symbolic state for a single execution path.
///
/// Each explored path carries concrete values (used to drive execution
/// deterministically) together with the symbolic constraints collected
/// along the path (used to generate new inputs via constraint negation).
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ConcolicState {
    /// Concrete values for all variables known on this path.
    pub concrete_values: BTreeMap<String, i128>,
    /// Symbolic constraints accumulated along this path.
    /// The conjunction of these constraints characterises the inputs
    /// that follow this path.
    pub symbolic_constraints: Vec<Formula>,
}

impl ConcolicState {
    /// Create a new empty state.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a state seeded with initial concrete values.
    #[must_use]
    pub fn with_values(concrete_values: BTreeMap<String, i128>) -> Self {
        Self { concrete_values, symbolic_constraints: Vec::new() }
    }

    /// Add a symbolic constraint to this path.
    pub fn add_constraint(&mut self, formula: Formula) {
        self.symbolic_constraints.push(formula);
    }

    /// Returns the number of branch constraints on this path.
    #[must_use]
    pub fn depth(&self) -> usize {
        self.symbolic_constraints.len()
    }
}

/// Result of a concolic search run.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum ConcolicResult {
    /// A bug was found: a concrete counterexample that violates the VC.
    FoundBug {
        /// The counterexample inputs.
        counterexample: BTreeMap<String, i128>,
        /// The iteration on which the bug was discovered.
        iteration: usize,
    },
    /// All reachable paths were explored without finding a bug.
    Exhausted {
        /// Total number of iterations completed.
        iterations: usize,
    },
    /// The iteration budget was reached before exhausting paths.
    ResourceLimit,
}

/// Evaluate a `Formula` concretely under the given variable assignment.
///
/// Returns `true` when the formula evaluates to a non-zero (truthy) value
/// and `false` otherwise.
#[must_use]
pub fn execute_concrete(formula: &Formula, inputs: &BTreeMap<String, i128>) -> bool {
    execute_concrete_checked(formula, inputs)
        .expect("concrete formula evaluation encountered unsupported or undefined behavior")
}

/// Fallible concrete evaluation for formulas.
///
/// Unlike the legacy bool-returning wrapper, this returns `SymexError` for
/// missing variables, division by zero, or unsupported formula constructs.
pub(crate) fn execute_concrete_checked(
    formula: &Formula,
    inputs: &BTreeMap<String, i128>,
) -> Result<bool, SymexError> {
    Ok(eval_formula(formula, inputs)? != 0)
}

/// Negate the branch constraint at `branch_idx` to explore a new path.
///
/// Constructs a formula that keeps all constraints before `branch_idx`
/// intact and flips the constraint at `branch_idx`. Returns `None` when
/// `branch_idx` is out of range.
#[must_use]
pub fn negate_branch(state: &ConcolicState, branch_idx: usize) -> Option<Formula> {
    if branch_idx >= state.symbolic_constraints.len() {
        return None;
    }

    let mut clauses: Vec<Formula> = Vec::with_capacity(branch_idx + 1);

    // Keep all constraints before the negated one.
    for c in &state.symbolic_constraints[..branch_idx] {
        clauses.push(c.clone());
    }

    // Negate the constraint at branch_idx.
    clauses.push(Formula::Not(Box::new(state.symbolic_constraints[branch_idx].clone())));

    match clauses.len() {
        0 => Some(Formula::Bool(true)),
        // SAFETY: match arm guarantees len == 1, so .next() returns Some.
        1 => Some(
            clauses
                .into_iter()
                .next()
                .unwrap_or_else(|| unreachable!("empty iter despite len == 1")),
        ),
        _ => Some(Formula::And(clauses)),
    }
}

/// Attempt to solve a conjunction of constraints and produce a concrete
/// input assignment.
///
/// This is a lightweight local solver suitable for simple linear
/// constraints. It extracts variable-equality patterns of the form
/// `Var == Int` and `Int == Var` directly, then falls back to zero
/// for remaining free variables.
///
/// Returns `None` if the constraints are trivially unsatisfiable
/// (e.g., `Bool(false)`).
#[must_use]
pub fn generate_test_input(constraints: &[Formula]) -> Option<BTreeMap<String, i128>> {
    generate_test_input_checked(constraints)
        .expect("test input generation encountered unsupported or undefined behavior")
}

/// Fallible variant of `generate_test_input`.
///
/// Returns `Err` for unsupported formulas, missing variables during
/// validation, or undefined concrete arithmetic such as division by zero.
pub(crate) fn generate_test_input_checked(
    constraints: &[Formula],
) -> Result<Option<BTreeMap<String, i128>>, SymexError> {
    let mut assignments: BTreeMap<String, i128> = BTreeMap::default();

    for c in constraints {
        // Check for trivially unsatisfiable constraint.
        if let Formula::Bool(false) = c {
            return Ok(None);
        }
        // Extract direct equality assignments.
        extract_equalities(c, &mut assignments);
    }

    // Collect all free variables across all constraints and default them to 0.
    for c in constraints {
        for var in sorted_free_variables(c) {
            assignments.entry(var).or_insert(0);
        }
    }

    // Verify that the assignment satisfies all constraints, attempting
    // lightweight repairs when a constraint fails. After any repair,
    // re-check all constraints from the beginning since the fix may
    // have broken a previously-satisfied constraint.
    let max_repair_rounds = constraints.len() + 1;
    for _ in 0..max_repair_rounds {
        let mut all_sat = true;
        for c in constraints {
            if eval_formula(c, &assignments)? == 0 {
                if !try_fix_assignment(c, &mut assignments)? {
                    return Ok(None);
                }
                all_sat = false;
                break; // Restart the constraint check after the repair.
            }
        }
        if all_sat {
            return Ok(Some(assignments));
        }
    }

    // Exceeded repair budget -- give up.
    Ok(None)
}

/// Run the concolic search loop over a verification condition.
///
/// Starting from default (zero) inputs, the search:
/// 1. Evaluates the VC formula concretely.
/// 2. If the formula is satisfied (truthy), reports `FoundBug`.
/// 3. Collects symbolic constraints from the current path.
/// 4. Negates each branch constraint to generate new inputs.
/// 5. Repeats until the iteration budget is reached or paths are exhausted.
pub fn concolic_search(
    vc: &VerificationCondition,
    max_iterations: usize,
) -> Result<ConcolicResult, SymexError> {
    if let VcKind::UnsupportedMir { kind, detail } = &vc.kind {
        return Err(SymexError::UnsupportedOperation(format!(
            "UnsupportedMir cannot be converted into a concrete bug search: {kind}: {detail}"
        )));
    }

    // Collect free variables from the VC formula.
    let vars = sorted_free_variables(&vc.formula);

    // Initialise the worklist with a zero-seeded state.
    let mut worklist: Vec<ConcolicState> = Vec::new();
    let initial_values: BTreeMap<String, i128> = vars.iter().map(|v| (v.clone(), 0i128)).collect();
    worklist.push(ConcolicState::with_values(initial_values));

    // Also try to directly satisfy the VC formula: if we can extract
    // concrete values that make the formula true, that is a candidate
    // counterexample. This catches simple equality bugs immediately.
    let vc_constraints = match &vc.formula {
        Formula::And(cs) => cs.clone(),
        other => vec![other.clone()],
    };
    if let Some(direct_inputs) = generate_test_input_checked(&vc_constraints)? {
        worklist.push(ConcolicState::with_values(direct_inputs));
    }

    // Track explored path signatures to avoid re-exploration.
    let mut explored: BTreeSet<Vec<i128>> = BTreeSet::default();

    for iteration in 0..max_iterations {
        let state = match worklist.pop() {
            Some(s) => s,
            None => {
                return Ok(ConcolicResult::Exhausted { iterations: iteration });
            }
        };

        // Build a path signature from concrete values for dedup.
        let sig: Vec<i128> = vars
            .iter()
            .map(|v| {
                state
                    .concrete_values
                    .get(v)
                    .copied()
                    .ok_or_else(|| SymexError::UndefinedVariable(v.clone()))
            })
            .collect::<Result<_, _>>()?;
        if !explored.insert(sig) {
            continue; // Already tried this input combination.
        }

        // Step 1: evaluate VC concretely.
        // VC convention: the formula represents the *negation* of the property.
        // If it evaluates to true (non-zero) under concrete inputs, the
        // property is violated and we have a counterexample.
        if execute_concrete_checked(&vc.formula, &state.concrete_values)? {
            return Ok(ConcolicResult::FoundBug {
                counterexample: state.concrete_values,
                iteration,
            });
        }

        // Step 2: build symbolic constraints from the VC sub-formulas.
        let new_state = build_path_constraints(&vc.formula, &state.concrete_values);

        // Step 3: negate each branch constraint to produce new inputs.
        for idx in 0..new_state.symbolic_constraints.len() {
            if let Some(negated_formula) = negate_branch(&new_state, idx) {
                let constraints = match &negated_formula {
                    Formula::And(cs) => cs.clone(),
                    other => vec![other.clone()],
                };
                if let Some(new_inputs) = generate_test_input_checked(&constraints)? {
                    let mut child_state = ConcolicState::with_values(new_inputs);
                    child_state.symbolic_constraints = constraints;
                    worklist.push(child_state);
                }
            }
        }
    }

    Ok(ConcolicResult::ResourceLimit)
}

// ---------------------------------------------------------------------------
// Private helpers for the fast bug-finding lane
// ---------------------------------------------------------------------------

pub(crate) fn sorted_free_variables(formula: &Formula) -> Vec<String> {
    let mut free = BTreeSet::default();
    collect_free_variables(formula, &mut free, &BTreeSet::default());
    free.into_iter().collect()
}

fn collect_free_variables(
    formula: &Formula,
    free: &mut BTreeSet<String>,
    bound: &BTreeSet<String>,
) {
    match formula {
        Formula::Var(name, _) => {
            if !bound.contains(name) {
                free.insert(name.clone());
            }
        }
        Formula::SymVar(sym, _) => {
            let name = sym.as_str().to_string();
            if !bound.contains(&name) {
                free.insert(name);
            }
        }
        Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
            let mut new_bound = bound.clone();
            for (sym, _) in bindings {
                new_bound.insert(sym.as_str().to_string());
            }
            collect_free_variables(body, free, &new_bound);
        }
        _ => {
            for child in formula.children() {
                collect_free_variables(child, free, bound);
            }
        }
    }
}

/// Evaluate a Formula to a concrete i128 value under the given assignment.
/// Boolean results: true=1, false=0.
fn eval_formula(formula: &Formula, inputs: &BTreeMap<String, i128>) -> Result<i128, SymexError> {
    match formula {
        Formula::Bool(b) => Ok(i128::from(*b)),
        Formula::Int(n) => Ok(*n),
        Formula::UInt(n) => Ok(*n as i128),
        Formula::BitVec { value, .. } => Ok(*value),

        Formula::Var(name, _) => {
            inputs.get(name).copied().ok_or_else(|| SymexError::UndefinedVariable(name.clone()))
        }
        Formula::SymVar(sym, _) => Err(SymexError::UndefinedVariable(format!("{sym:?}"))),

        Formula::Not(inner) => {
            let v = eval_formula(inner, inputs)?;
            Ok(i128::from(v == 0))
        }
        Formula::And(clauses) => {
            let mut all_true = true;
            for c in clauses {
                all_true &= eval_formula(c, inputs)? != 0;
            }
            Ok(i128::from(all_true))
        }
        Formula::Or(clauses) => {
            let mut any_true = false;
            for c in clauses {
                any_true |= eval_formula(c, inputs)? != 0;
            }
            Ok(i128::from(any_true))
        }
        Formula::Implies(lhs, rhs) => {
            let l = eval_formula(lhs, inputs)?;
            let r = eval_formula(rhs, inputs)?;
            Ok(i128::from(l == 0 || r != 0))
        }

        Formula::Eq(l, r) => Ok(i128::from(eval_formula(l, inputs)? == eval_formula(r, inputs)?)),
        Formula::Lt(l, r) => Ok(i128::from(eval_formula(l, inputs)? < eval_formula(r, inputs)?)),
        Formula::Le(l, r) => Ok(i128::from(eval_formula(l, inputs)? <= eval_formula(r, inputs)?)),
        Formula::Gt(l, r) => Ok(i128::from(eval_formula(l, inputs)? > eval_formula(r, inputs)?)),
        Formula::Ge(l, r) => Ok(i128::from(eval_formula(l, inputs)? >= eval_formula(r, inputs)?)),

        Formula::Add(l, r) => Ok(eval_formula(l, inputs)?.wrapping_add(eval_formula(r, inputs)?)),
        Formula::Sub(l, r) => Ok(eval_formula(l, inputs)?.wrapping_sub(eval_formula(r, inputs)?)),
        Formula::Mul(l, r) => Ok(eval_formula(l, inputs)?.wrapping_mul(eval_formula(r, inputs)?)),
        Formula::Div(l, r) => {
            let rv = eval_formula(r, inputs)?;
            if rv == 0 {
                Err(SymexError::UnsupportedOperation("division by zero".into()))
            } else {
                Ok(eval_formula(l, inputs)?.wrapping_div(rv))
            }
        }
        Formula::Rem(l, r) => {
            let rv = eval_formula(r, inputs)?;
            if rv == 0 {
                Err(SymexError::UnsupportedOperation("remainder by zero".into()))
            } else {
                Ok(eval_formula(l, inputs)?.wrapping_rem(rv))
            }
        }
        Formula::Neg(inner) => Ok(eval_formula(inner, inputs)?.wrapping_neg()),

        Formula::Ite(cond, then_val, else_val) => {
            if eval_formula(cond, inputs)? != 0 {
                eval_formula(then_val, inputs)
            } else {
                eval_formula(else_val, inputs)
            }
        }

        Formula::BvAdd(..)
        | Formula::BvSub(..)
        | Formula::BvMul(..)
        | Formula::BvUDiv(..)
        | Formula::BvSDiv(..)
        | Formula::BvURem(..)
        | Formula::BvSRem(..)
        | Formula::BvAnd(..)
        | Formula::BvOr(..)
        | Formula::BvXor(..)
        | Formula::BvNot(..)
        | Formula::BvShl(..)
        | Formula::BvLShr(..)
        | Formula::BvAShr(..)
        | Formula::BvULt(..)
        | Formula::BvULe(..)
        | Formula::BvSLt(..)
        | Formula::BvSLe(..)
        | Formula::BvToInt(..)
        | Formula::IntToBv(..)
        | Formula::BvExtract { .. }
        | Formula::BvConcat(..)
        | Formula::BvZeroExt(..)
        | Formula::BvSignExt(..)
        | Formula::Forall(..)
        | Formula::Exists(..)
        | Formula::Select(..)
        | Formula::Store(..) => Err(SymexError::UnsupportedOperation(format!(
            "unsupported formula in concolic concrete evaluation: {formula:?}"
        ))),
        other => Err(SymexError::UnsupportedOperation(format!(
            "unsupported formula in concolic concrete evaluation: {other:?}"
        ))),
    }
}

/// Extract `Var == Int` and `Int == Var` patterns from a formula.
fn extract_equalities(formula: &Formula, assignments: &mut BTreeMap<String, i128>) {
    match formula {
        Formula::Eq(l, r) => match (l.as_ref(), r.as_ref()) {
            (Formula::Var(name, _), Formula::Int(n)) => {
                assignments.insert(name.clone(), *n);
            }
            (Formula::Int(n), Formula::Var(name, _)) => {
                assignments.insert(name.clone(), *n);
            }
            _ => {}
        },
        Formula::And(clauses) => {
            for c in clauses {
                extract_equalities(c, assignments);
            }
        }
        _ => {}
    }
}

/// Try simple fixes for unsatisfied constraints: e.g. for `Var < N`, try N-1.
fn try_fix_assignment(
    formula: &Formula,
    assignments: &mut BTreeMap<String, i128>,
) -> Result<bool, SymexError> {
    match formula {
        Formula::Lt(l, r) => {
            if let (Formula::Var(name, _), Formula::Int(n)) = (l.as_ref(), r.as_ref()) {
                assignments.insert(name.clone(), n - 1);
                return Ok(eval_formula(formula, assignments)? != 0);
            }
        }
        Formula::Gt(l, r) => {
            if let (Formula::Var(name, _), Formula::Int(n)) = (l.as_ref(), r.as_ref()) {
                assignments.insert(name.clone(), n + 1);
                return Ok(eval_formula(formula, assignments)? != 0);
            }
        }
        Formula::Le(l, r) => {
            if let (Formula::Var(name, _), Formula::Int(n)) = (l.as_ref(), r.as_ref()) {
                assignments.insert(name.clone(), *n);
                return Ok(eval_formula(formula, assignments)? != 0);
            }
        }
        Formula::Ge(l, r) => {
            if let (Formula::Var(name, _), Formula::Int(n)) = (l.as_ref(), r.as_ref()) {
                assignments.insert(name.clone(), *n);
                return Ok(eval_formula(formula, assignments)? != 0);
            }
        }
        Formula::Not(inner) => {
            // Not(Eq(Var, Int)): try value + 1
            if let Formula::Eq(l, r) = inner.as_ref()
                && let (Formula::Var(name, _), Formula::Int(n)) = (l.as_ref(), r.as_ref())
            {
                assignments.insert(name.clone(), n + 1);
                return Ok(eval_formula(formula, assignments)? != 0);
            }
        }
        _ => {}
    }
    Ok(false)
}

/// Build path constraints by decomposing the VC formula into branch-like
/// sub-formulas that can be individually negated.
fn build_path_constraints(formula: &Formula, inputs: &BTreeMap<String, i128>) -> ConcolicState {
    let mut state = ConcolicState::with_values(inputs.clone());

    match formula {
        Formula::And(clauses) => {
            for c in clauses {
                state.add_constraint(c.clone());
            }
        }
        Formula::Or(clauses) => {
            // For OR, each clause is a branch alternative.
            for c in clauses {
                state.add_constraint(c.clone());
            }
        }
        Formula::Implies(lhs, rhs) => {
            // P => Q  <==>  NOT P OR Q
            state.add_constraint(Formula::Not(Box::new(*lhs.clone())));
            state.add_constraint(*rhs.clone());
        }
        other => {
            // Single atomic constraint.
            state.add_constraint(other.clone());
        }
    }

    state
}

#[cfg(test)]
mod tests {
    use trust_types::UnwindEdge;
    use trust_types::{
        BasicBlock, BinOp, BlockId, ConstValue, Operand, Place, Rvalue, Sort, SourceSpan,
        Statement, Terminator, VcKind,
    };

    use super::*;

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    #[test]
    fn callable_constants_fail_closed_in_concolic_execution() {
        let value = ConstValue::CallableItem {
            def_path: "fixture::callback".to_string(),
            kind: trust_types::CallableKind::Closure,
            def_path_hash: trust_types::CallableDefPathHash::new(1, 1),
        };
        let error = eval_mir_const(&value).expect_err("concolic values cannot encode callables");
        assert!(matches!(
            error,
            SymexError::UnsupportedOperation(message)
                if message.contains("callable-item constants")
        ));
    }

    fn simple_blocks() -> Vec<BasicBlock> {
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(0)),
                        Operand::Constant(ConstValue::Int(1)),
                    ),
                    span: span(),
                }],
                terminator: Terminator::Goto(BlockId(1)),
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ]
    }

    fn branching_blocks() -> Vec<BasicBlock> {
        vec![
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
            BasicBlock {
                id: BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(100))),
                    span: span(),
                }],
                terminator: Terminator::Return,
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(200))),
                    span: span(),
                }],
                terminator: Terminator::Return,
            },
        ]
    }

    fn local0_input(value: i128) -> BTreeMap<String, ConcolicValue> {
        let mut inputs = BTreeMap::default();
        inputs.insert(
            "_local0".to_string(),
            ConcolicValue::with_shadow(value, SymbolicValue::Symbol("_local0".into())),
        );
        inputs
    }

    #[test]
    fn test_concolic_engine_simple_exploration() {
        let blocks = simple_blocks();
        let config = ConcolicConfig {
            max_iterations: 10,
            step_limit: 100,
            strategy: NegationStrategy::Generational,
            track_coverage: true,
        };
        let mut engine = ConcolicEngine::new(blocks, vec![], MockSolver::default(), config);
        engine.add_initial_input(local0_input(1));
        let result = engine.explore().expect("supported path should execute");
        assert!(result.counterexamples.is_empty());
        assert!(result.paths_explored >= 1);
    }

    #[test]
    fn test_concolic_engine_branching_explores_both() {
        let blocks = branching_blocks();
        let config = ConcolicConfig {
            max_iterations: 20,
            step_limit: 100,
            strategy: NegationStrategy::Generational,
            track_coverage: true,
        };

        let mut solver = MockSolver::default();
        // First query returns x=1 (take true branch).
        solver.responses.insert(0, Some(vec![("_local0".to_string(), 1)]));
        // Second query returns x=0 (take otherwise branch).
        solver.responses.insert(1, Some(vec![("_local0".to_string(), 0)]));

        let mut engine = ConcolicEngine::new(blocks, vec![], solver, config);
        // Seed with symbolic input.
        engine.add_initial_input(local0_input(1));

        let result = engine.explore().expect("supported branch should execute");
        assert!(result.paths_explored >= 2);
        // Should have recorded coverage at the branch point.
        assert!(result.coverage.branch_count() >= 1);
    }

    #[test]
    fn test_concolic_engine_respects_iteration_limit() {
        let blocks = branching_blocks();
        let config = ConcolicConfig {
            max_iterations: 1,
            step_limit: 100,
            strategy: NegationStrategy::Generational,
            track_coverage: false,
        };
        let mut engine = ConcolicEngine::new(blocks, vec![], MockSolver::default(), config);
        engine.add_initial_input(local0_input(0));
        let result = engine.explore().expect("supported branch should execute");
        assert_eq!(result.paths_explored, 1);
    }

    #[test]
    fn test_concolic_engine_missing_default_input_errors() {
        let blocks = simple_blocks();
        let config = ConcolicConfig {
            max_iterations: 100,
            step_limit: 100,
            strategy: NegationStrategy::Generational,
            track_coverage: false,
        };
        let mut engine = ConcolicEngine::new(blocks, vec![], MockSolver::default(), config);
        // Don't add any inputs.
        // explore() adds a default empty input, which must not fabricate locals.
        let err = engine.explore().expect_err("missing _local0 should fail closed");
        assert!(matches!(err, SymexError::UndefinedVariable(name) if name == "_local0"));
    }

    #[test]
    fn test_concolic_config_default() {
        let config = ConcolicConfig::default();
        assert_eq!(config.max_iterations, 100);
        assert_eq!(config.step_limit, 1000);
        assert_eq!(config.strategy, NegationStrategy::Generational);
        assert!(config.track_coverage);
    }

    #[test]
    fn test_concolic_explore_api() {
        let blocks = simple_blocks();
        let config = ConcolicConfig::default();
        let err = explore(&blocks, &[], &config).expect_err("missing input should fail closed");
        assert!(matches!(err, SymexError::UndefinedVariable(name) if name == "_local0"));
        let cexs = {
            let mut engine =
                ConcolicEngine::new(blocks, vec![], MockSolver::default(), config.clone());
            engine.add_initial_input(local0_input(0));
            engine.explore().expect("seeded exploration should succeed").counterexamples
        };
        assert!(cexs.is_empty());
    }

    #[test]
    fn test_concolic_explore_with_solver() {
        let blocks = simple_blocks();
        let config =
            ConcolicConfig { max_iterations: 5, step_limit: 100, ..ConcolicConfig::default() };
        let result =
            explore_with_solver(&blocks, &[], &config, MockSolver::default(), &["_local0"])
                .expect("symbolic seed should bind _local0");
        assert!(result.counterexamples.is_empty());
        assert!(result.paths_explored >= 1);
    }

    #[test]
    fn test_concolic_mock_solver_counts_queries() {
        let mut solver = MockSolver::default();
        let f = Formula::Bool(true);
        solver.solve(&f);
        solver.solve(&f);
        assert_eq!(solver.query_count, 2);
    }

    #[test]
    fn test_concolic_mock_solver_canned_response() {
        let mut solver = MockSolver::default();
        solver.responses.insert(0, None); // First query: UNSAT
        solver.responses.insert(1, Some(vec![("z".into(), 42)])); // Second: SAT

        let f = Formula::Bool(true);
        assert!(solver.solve(&f).is_none());
        let result = solver.solve(&f).expect("should be SAT");
        assert_eq!(result, vec![("z".into(), 42)]);
    }

    #[test]
    fn test_concolic_assignments_to_inputs() {
        let assignments = vec![("x".to_string(), 5), ("y".to_string(), -3)];
        let inputs = assignments_to_inputs(&assignments);
        assert_eq!(inputs.len(), 2);
        assert_eq!(inputs["x"].concrete, 5);
        assert!(inputs["x"].is_symbolic());
        assert_eq!(inputs["y"].concrete, -3);
    }

    #[test]
    fn test_concolic_engine_solver_unsat_prunes() {
        let blocks = branching_blocks();
        let config = ConcolicConfig {
            max_iterations: 10,
            step_limit: 100,
            strategy: NegationStrategy::Generational,
            track_coverage: true,
        };

        let mut solver = MockSolver::default();
        // All queries return UNSAT — no new inputs discovered.
        for i in 0..10 {
            solver.responses.insert(i, None);
        }

        let mut engine = ConcolicEngine::new(blocks, vec![], solver, config);
        engine.add_initial_input(local0_input(1));

        let result = engine.explore().expect("supported branch should execute");
        // Only the initial path is explored since solver returns UNSAT.
        assert_eq!(result.paths_explored, 1);
        assert!(result.solver_queries >= 1);
    }

    #[test]
    fn test_concolic_engine_step_limit_skip() {
        // Block that loops forever.
        let blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Goto(BlockId(0)),
        }];
        let config = ConcolicConfig {
            max_iterations: 5,
            step_limit: 3,
            strategy: NegationStrategy::Generational,
            track_coverage: false,
        };
        let mut engine = ConcolicEngine::new(blocks, vec![], MockSolver::default(), config);
        engine.worklist.push(BTreeMap::default());
        let err = engine.explore().expect_err("step limit should fail closed");
        assert!(matches!(err, SymexError::DepthLimitExceeded { depth: 3, limit: 3 }));
    }

    #[test]
    fn test_concolic_engine_div_by_zero_errors() {
        let blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Div,
                    Operand::Copy(Place::local(0)),
                    Operand::Constant(ConstValue::Int(0)),
                ),
                span: span(),
            }],
            terminator: Terminator::Return,
        }];
        let config = ConcolicConfig::default();
        let mut engine = ConcolicEngine::new(blocks, vec![], MockSolver::default(), config);
        engine.add_initial_input(local0_input(10));

        let err = engine.explore().expect_err("division by zero must fail closed");
        assert!(
            matches!(err, SymexError::UnsupportedOperation(msg) if msg.contains("division by zero"))
        );
    }

    #[test]
    fn test_concolic_engine_opaque_terminator_errors() {
        let blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Opaque {
                kind: "test-opaque".into(),
                targets: vec![BlockId(1)],
                span: span(),
            },
        }];
        let config = ConcolicConfig::default();
        let mut engine = ConcolicEngine::new(blocks, vec![], MockSolver::default(), config);
        engine.worklist.push(BTreeMap::default());

        let err = engine.explore().expect_err("opaque terminator must fail closed");
        assert!(matches!(err, SymexError::UnsupportedOperation(msg) if msg.contains("Opaque")));
    }

    #[test]
    fn test_concolic_engine_call_terminator_errors() {
        let blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                func: "opaque_call".into(),
                args: vec![],
                dest: Place::local(1),
                target: Some(BlockId(1)),
                span: span(),
                atomic: None,
            },
        }];
        let config = ConcolicConfig::default();
        let mut engine = ConcolicEngine::new(blocks, vec![], MockSolver::default(), config);
        engine.worklist.push(BTreeMap::default());

        let err = engine.explore().expect_err("call result must not become a fresh symbol");
        assert!(matches!(err, SymexError::UnsupportedOperation(msg) if msg.contains("Call")));
    }

    // -----------------------------------------------------------------------
    // Tests for the fast bug-finding lane
    // -----------------------------------------------------------------------

    fn make_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test".into(),
            location: span(),
            formula,
            contract_metadata: None,
        }
    }

    #[test]
    fn test_concolic_state_new_empty() {
        let state = ConcolicState::new();
        assert!(state.concrete_values.is_empty());
        assert!(state.symbolic_constraints.is_empty());
        assert_eq!(state.depth(), 0);
    }

    #[test]
    fn test_concolic_state_with_values() {
        let mut values = BTreeMap::default();
        values.insert("x".into(), 42);
        let state = ConcolicState::with_values(values);
        assert_eq!(state.concrete_values["x"], 42);
        assert_eq!(state.depth(), 0);
    }

    #[test]
    fn test_concolic_state_add_constraint() {
        let mut state = ConcolicState::new();
        state.add_constraint(Formula::Bool(true));
        state.add_constraint(Formula::Lt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(10)),
        ));
        assert_eq!(state.depth(), 2);
    }

    #[test]
    fn test_execute_concrete_true_literal() {
        let inputs = BTreeMap::default();
        assert!(execute_concrete(&Formula::Bool(true), &inputs));
    }

    #[test]
    fn test_execute_concrete_false_literal() {
        let inputs = BTreeMap::default();
        assert!(!execute_concrete(&Formula::Bool(false), &inputs));
    }

    #[test]
    fn test_execute_concrete_var_lookup() {
        let mut inputs = BTreeMap::default();
        inputs.insert("x".into(), 5);
        assert!(execute_concrete(
            &Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(3)),),
            &inputs,
        ));
    }

    #[test]
    fn test_execute_concrete_missing_var_errors() {
        let inputs = BTreeMap::default();
        let err = execute_concrete_checked(
            &Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(10))),
            &inputs,
        )
        .expect_err("missing variables must not default to zero");
        assert!(matches!(err, SymexError::UndefinedVariable(name) if name == "x"));
    }

    #[test]
    fn test_execute_concrete_arithmetic() {
        let mut inputs = BTreeMap::default();
        inputs.insert("x".into(), 3);
        inputs.insert("y".into(), 4);
        // x + y == 7
        let formula = Formula::Eq(
            Box::new(Formula::Add(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Var("y".into(), Sort::Int)),
            )),
            Box::new(Formula::Int(7)),
        );
        assert!(execute_concrete(&formula, &inputs));
    }

    #[test]
    fn test_execute_concrete_and() {
        let mut inputs = BTreeMap::default();
        inputs.insert("x".into(), 5);
        let formula = Formula::And(vec![
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(10))),
        ]);
        assert!(execute_concrete(&formula, &inputs));
    }

    #[test]
    fn test_execute_concrete_or() {
        let mut inputs = BTreeMap::default();
        inputs.insert("x".into(), 15);
        let formula = Formula::Or(vec![
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0))),
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(10))),
        ]);
        assert!(execute_concrete(&formula, &inputs));
    }

    #[test]
    fn test_execute_concrete_implies() {
        let inputs = BTreeMap::default();
        // false => anything is true
        let formula =
            Formula::Implies(Box::new(Formula::Bool(false)), Box::new(Formula::Bool(false)));
        assert!(execute_concrete(&formula, &inputs));
    }

    #[test]
    fn test_execute_concrete_ite() {
        let mut inputs = BTreeMap::default();
        inputs.insert("cond".into(), 1);
        let formula = Formula::Ite(
            Box::new(Formula::Var("cond".into(), Sort::Int)),
            Box::new(Formula::Int(42)),
            Box::new(Formula::Int(0)),
        );
        assert!(execute_concrete(&formula, &inputs));
    }

    #[test]
    fn test_execute_concrete_div_by_zero_errors() {
        let inputs = BTreeMap::default();
        let formula = Formula::Div(Box::new(Formula::Int(10)), Box::new(Formula::Int(0)));
        let err = execute_concrete_checked(&formula, &inputs)
            .expect_err("division by zero must fail closed");
        assert!(
            matches!(err, SymexError::UnsupportedOperation(msg) if msg.contains("division by zero"))
        );
    }

    #[test]
    fn test_negate_branch_single_constraint() {
        let mut state = ConcolicState::new();
        state.add_constraint(Formula::Lt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(10)),
        ));
        let negated = negate_branch(&state, 0).expect("should produce negated formula");
        // Should be NOT(x < 10).
        match negated {
            Formula::Not(inner) => match *inner {
                Formula::Lt(_, _) => {}
                other => panic!("expected Lt inside Not, got {other:?}"),
            },
            other => panic!("expected Not, got {other:?}"),
        }
    }

    #[test]
    fn test_negate_branch_multiple_constraints() {
        let mut state = ConcolicState::new();
        state.add_constraint(Formula::Var("a".into(), Sort::Bool));
        state.add_constraint(Formula::Var("b".into(), Sort::Bool));
        state.add_constraint(Formula::Var("c".into(), Sort::Bool));

        // Negate index 1: keep a, negate b.
        let negated = negate_branch(&state, 1).expect("should produce negated formula");
        match negated {
            Formula::And(clauses) => {
                assert_eq!(clauses.len(), 2);
                // First: a (kept).
                match &clauses[0] {
                    Formula::Var(name, _) => assert_eq!(name, "a"),
                    other => panic!("expected Var(a), got {other:?}"),
                }
                // Second: NOT(b) (negated).
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

    #[test]
    fn test_negate_branch_out_of_range() {
        let state = ConcolicState::new();
        assert!(negate_branch(&state, 0).is_none());
    }

    #[test]
    fn test_negate_branch_first_constraint() {
        let mut state = ConcolicState::new();
        state.add_constraint(Formula::Bool(true));
        state.add_constraint(Formula::Bool(false));

        // Negate index 0: produces NOT(true) = false, with no prefix.
        let negated = negate_branch(&state, 0).expect("should succeed");
        match negated {
            Formula::Not(inner) => assert_eq!(*inner, Formula::Bool(true)),
            other => panic!("expected Not(Bool(true)), got {other:?}"),
        }
    }

    #[test]
    fn test_generate_test_input_equality() {
        let constraints = vec![Formula::Eq(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(42)),
        )];
        let inputs = generate_test_input(&constraints).expect("should find assignment");
        assert_eq!(inputs["x"], 42);
    }

    #[test]
    fn test_generate_test_input_unsatisfiable() {
        let constraints = vec![Formula::Bool(false)];
        assert!(generate_test_input(&constraints).is_none());
    }

    #[test]
    fn test_generate_test_input_defaults_free_vars() {
        let constraints = vec![Formula::Lt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(10)),
        )];
        let inputs = generate_test_input(&constraints).expect("should find assignment");
        // x defaults to 0, which satisfies x < 10.
        assert!(inputs.contains_key("x"));
        assert!(inputs["x"] < 10);
    }

    #[test]
    fn test_generate_test_input_multiple_constraints() {
        let constraints = vec![
            Formula::Eq(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(5))),
            Formula::Eq(Box::new(Formula::Var("y".into(), Sort::Int)), Box::new(Formula::Int(10))),
        ];
        let inputs = generate_test_input(&constraints).expect("should find assignment");
        assert_eq!(inputs["x"], 5);
        assert_eq!(inputs["y"], 10);
    }

    #[test]
    fn test_generate_test_input_lt_fix() {
        // x < 5 and x == 10 are contradictory via equality, but the
        // light solver tries to fix: x=10 fails x<5, so it tries x=4.
        // However x=4 != 10 so the Eq fails. Should return None.
        let constraints = vec![
            Formula::Eq(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(10))),
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(5))),
        ];
        assert!(generate_test_input(&constraints).is_none());
    }

    #[test]
    fn test_concolic_search_finds_bug() {
        // VC: x == 42 (property violation when x=42).
        // concolic_search starts with x=0 (not a bug), then negates
        // to try x != 0 and through equality extraction finds x=42.
        let formula =
            Formula::Eq(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(42)));
        let vc = make_vc(formula);
        let result = concolic_search(&vc, 100).expect("supported VC should execute");
        match result {
            ConcolicResult::FoundBug { counterexample, .. } => {
                assert_eq!(counterexample["x"], 42);
            }
            other => panic!("expected FoundBug, got {other:?}"),
        }
    }

    #[test]
    fn test_concolic_search_no_bug_exhausted() {
        // VC: Bool(false) -- never violated.
        let vc = make_vc(Formula::Bool(false));
        let result = concolic_search(&vc, 50).expect("supported VC should execute");
        match result {
            ConcolicResult::Exhausted { .. } => {}
            other => panic!("expected Exhausted, got {other:?}"),
        }
    }

    #[test]
    fn test_concolic_search_resource_limit() {
        // VC that the light solver genuinely cannot satisfy: a conjunction
        // with contradictory requirements that pass trivial extraction.
        // AND(x > y, y > x) is unsatisfiable; the solver should exhaust.
        let formula = Formula::And(vec![
            Formula::Gt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Var("y".into(), Sort::Int)),
            ),
            Formula::Gt(
                Box::new(Formula::Var("y".into(), Sort::Int)),
                Box::new(Formula::Var("x".into(), Sort::Int)),
            ),
        ]);
        let vc = make_vc(formula);
        let result = concolic_search(&vc, 10).expect("supported VC should execute");
        // Should hit Exhausted or ResourceLimit (not FoundBug).
        match result {
            ConcolicResult::ResourceLimit | ConcolicResult::Exhausted { .. } => {}
            ConcolicResult::FoundBug { counterexample, .. } => {
                panic!("unexpected bug found with {counterexample:?}");
            }
        }
    }

    #[test]
    fn test_concolic_search_finds_lt_bug() {
        // VC: x < 0 -- the direct-satisfaction seed tries x=-1 which
        // satisfies x < 0, so the engine finds a bug immediately.
        let formula =
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)));
        let vc = make_vc(formula);
        let result = concolic_search(&vc, 50).expect("supported VC should execute");
        match result {
            ConcolicResult::FoundBug { counterexample, .. } => {
                assert!(counterexample["x"] < 0);
            }
            other => panic!("expected FoundBug for x < 0, got {other:?}"),
        }
    }

    #[test]
    fn test_concolic_search_finds_gt_bug() {
        // VC: x > 1000000 -- the direct-satisfaction seed solves to x=1000001.
        let formula = Formula::Gt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(1_000_000)),
        );
        let vc = make_vc(formula);
        let result = concolic_search(&vc, 10).expect("supported VC should execute");
        match result {
            ConcolicResult::FoundBug { counterexample, .. } => {
                assert!(counterexample["x"] > 1_000_000);
            }
            other => panic!("expected FoundBug for x > 1000000, got {other:?}"),
        }
    }

    #[test]
    fn test_concolic_result_enum_variants() {
        // Ensure all variants are constructible.
        let _found = ConcolicResult::FoundBug { counterexample: BTreeMap::default(), iteration: 0 };
        let _exhausted = ConcolicResult::Exhausted { iterations: 5 };
        let _limit = ConcolicResult::ResourceLimit;
    }

    #[test]
    fn test_eval_formula_neg() {
        let inputs = BTreeMap::default();
        let formula = Formula::Neg(Box::new(Formula::Int(5)));
        assert_eq!(eval_formula(&formula, &inputs).expect("supported formula"), -5);
    }

    #[test]
    fn test_eval_formula_rem() {
        let inputs = BTreeMap::default();
        let formula = Formula::Rem(Box::new(Formula::Int(10)), Box::new(Formula::Int(3)));
        assert_eq!(eval_formula(&formula, &inputs).expect("supported formula"), 1);
    }

    #[test]
    fn test_eval_formula_mul() {
        let inputs = BTreeMap::default();
        let formula = Formula::Mul(Box::new(Formula::Int(6)), Box::new(Formula::Int(7)));
        assert_eq!(eval_formula(&formula, &inputs).expect("supported formula"), 42);
    }

    #[test]
    fn test_eval_formula_sub() {
        let inputs = BTreeMap::default();
        let formula = Formula::Sub(Box::new(Formula::Int(10)), Box::new(Formula::Int(3)));
        assert_eq!(eval_formula(&formula, &inputs).expect("supported formula"), 7);
    }

    #[test]
    fn test_eval_formula_not() {
        let inputs = BTreeMap::default();
        assert_eq!(
            eval_formula(&Formula::Not(Box::new(Formula::Int(0))), &inputs)
                .expect("supported formula"),
            1
        );
        assert_eq!(
            eval_formula(&Formula::Not(Box::new(Formula::Int(1))), &inputs)
                .expect("supported formula"),
            0
        );
        assert_eq!(
            eval_formula(&Formula::Not(Box::new(Formula::Int(42))), &inputs)
                .expect("supported formula"),
            0
        );
    }

    #[test]
    fn test_build_path_constraints_and() {
        let formula = Formula::And(vec![
            Formula::Var("a".into(), Sort::Bool),
            Formula::Var("b".into(), Sort::Bool),
        ]);
        let inputs = BTreeMap::default();
        let state = build_path_constraints(&formula, &inputs);
        assert_eq!(state.depth(), 2);
    }

    #[test]
    fn test_build_path_constraints_implies() {
        let formula = Formula::Implies(
            Box::new(Formula::Var("p".into(), Sort::Bool)),
            Box::new(Formula::Var("q".into(), Sort::Bool)),
        );
        let inputs = BTreeMap::default();
        let state = build_path_constraints(&formula, &inputs);
        assert_eq!(state.depth(), 2);
        // First constraint should be NOT(p).
        match &state.symbolic_constraints[0] {
            Formula::Not(_) => {}
            other => panic!("expected Not, got {other:?}"),
        }
    }

    #[test]
    fn test_build_path_constraints_atomic() {
        let formula =
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(5)));
        let inputs = BTreeMap::default();
        let state = build_path_constraints(&formula, &inputs);
        assert_eq!(state.depth(), 1);
    }
}
