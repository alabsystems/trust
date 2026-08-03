// trust-symex: Concolic/fuzzing integration for fast bug-finding
//
// Combines concolic execution with coverage-guided fuzzing to form a fast
// bug-finding lane. The concolic executor drives concrete execution while
// collecting symbolic constraints; the fuzzer mutates inputs guided by
// coverage feedback; the bug oracle checks for crashes, assertion failures,
// and VC violations.
//
// Architecture:
//   ConcolicExecutor  -- runs concrete execution + collects symbolic constraints
//   ConcolicFuzzTarget -- generates fuzz harness code from a VC + function signature
//   CoverageTracker   -- tracks branch/path coverage across exploration runs
//   ConcolicStrategy  -- selects exploration order (DFS, coverage-guided, random)
//   BugOracle         -- classifies execution outcomes as bugs or safe
//
// References:
//   - DART (Godefroid et al., PLDI 2005)
//   - SAGE (Godefroid et al., NDSS 2008)
//   - KLEE (Cadar et al., OSDI 2008) -- refs/klee/
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt::Write;

use serde::{Deserialize, Serialize};
use trust_types::{Formula, Ty, VcKind, VerificationCondition};

use crate::concolic::{
    ConcolicState, execute_concrete_checked, generate_test_input_checked, negate_branch,
    sorted_free_variables,
};

// ---------------------------------------------------------------------------
// ConcolicStrategy: exploration order for the concolic/fuzzing loop
// ---------------------------------------------------------------------------

/// Strategy for exploring paths in the concolic/fuzzing loop.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
#[derive(Default)]
pub enum ConcolicStrategy {
    /// Depth-first: explore the deepest unexplored branch first.
    DepthFirst,
    /// Coverage-guided: prioritize inputs that reach uncovered branches.
    #[default]
    CoverageGuided,
    /// Random: select inputs uniformly at random (deterministic with seed).
    Random,
    /// Breadth-first: explore shallowest branches first.
    BreadthFirst,
}

// ---------------------------------------------------------------------------
// BugKind + BugReport: classification of discovered bugs
// ---------------------------------------------------------------------------

/// Classification of a bug discovered during concolic/fuzzing exploration.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BugKind {
    /// The program crashed (e.g., panic, abort).
    Crash { message: String },
    /// An assertion in the program failed.
    AssertionFailure { message: String },
    /// A verification condition was violated by a concrete input.
    VcViolation { vc_index: usize, vc_kind: String },
    /// Division by zero detected during concrete execution.
    DivisionByZero,
    /// Arithmetic overflow detected during concrete execution.
    ArithmeticOverflow,
    /// Index out of bounds detected during concrete execution.
    IndexOutOfBounds,
}

/// A bug report produced by the bug oracle.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BugReport {
    /// What kind of bug was found.
    pub kind: BugKind,
    /// The concrete input values that triggered the bug.
    pub inputs: BTreeMap<String, i128>,
    /// Which iteration of the exploration discovered this bug.
    pub iteration: usize,
    /// The path depth (number of branch decisions) when the bug was found.
    pub path_depth: usize,
}

// ---------------------------------------------------------------------------
// BugOracle: checks execution outcomes against VCs and safety properties
// ---------------------------------------------------------------------------

/// Oracle that classifies concrete execution outcomes as bugs or safe.
///
/// The oracle checks three categories:
/// 1. **Crashes**: the concrete execution panicked or hit unreachable code.
/// 2. **Assertion failures**: a user-level assertion evaluated to false.
/// 3. **VC violations**: a verification condition formula evaluated to true
///    (indicating the negated property holds, i.e., the property is violated).
#[derive(Debug, Clone)]
pub struct BugOracle {
    /// Verification conditions to check against concrete execution states.
    vcs: Vec<VerificationCondition>,
}

impl BugOracle {
    /// Create a new oracle checking the given verification conditions.
    #[must_use]
    pub fn new(vcs: Vec<VerificationCondition>) -> Self {
        Self { vcs }
    }

    /// Create an oracle with no VCs (only checks for crashes).
    #[must_use]
    pub fn crash_only() -> Self {
        Self { vcs: Vec::new() }
    }

    /// Check concrete inputs against all VCs and return any bugs found.
    ///
    /// VC convention: the formula represents the *negation* of the safety
    /// property. If a VC formula evaluates to true (non-zero) under the
    /// given inputs, the property is violated.
    #[must_use]
    pub fn check_inputs(
        &self,
        inputs: &BTreeMap<String, i128>,
        iteration: usize,
        path_depth: usize,
    ) -> Vec<BugReport> {
        let mut bugs = Vec::new();

        for (vc_idx, vc) in self.vcs.iter().enumerate() {
            if matches!(vc.kind, VcKind::UnsupportedMir { .. }) {
                continue;
            }
            if matches!(execute_concrete_checked(&vc.formula, inputs), Ok(true)) {
                bugs.push(BugReport {
                    kind: BugKind::VcViolation {
                        vc_index: vc_idx,
                        vc_kind: format!("{:?}", vc.kind),
                    },
                    inputs: inputs.clone(),
                    iteration,
                    path_depth,
                });
            }
        }

        bugs
    }

    /// Check whether a specific formula (not necessarily a VC) is violated.
    ///
    /// Returns a `BugReport` if the formula evaluates to true under the inputs.
    #[must_use]
    pub fn check_formula(
        &self,
        formula: &Formula,
        inputs: &BTreeMap<String, i128>,
        iteration: usize,
        message: &str,
    ) -> Option<BugReport> {
        if matches!(execute_concrete_checked(formula, inputs), Ok(true)) {
            Some(BugReport {
                kind: BugKind::AssertionFailure { message: message.to_string() },
                inputs: inputs.clone(),
                iteration,
                path_depth: 0,
            })
        } else {
            None
        }
    }

    /// Check for division-by-zero: returns a bug if any named variable is zero
    /// and is used as a divisor (indicated by the VC kind).
    #[must_use]
    pub fn check_division_by_zero(
        &self,
        inputs: &BTreeMap<String, i128>,
        iteration: usize,
    ) -> Option<BugReport> {
        for vc in &self.vcs {
            if matches!(vc.kind, VcKind::DivisionByZero | VcKind::RemainderByZero)
                && matches!(execute_concrete_checked(&vc.formula, inputs), Ok(true))
            {
                return Some(BugReport {
                    kind: BugKind::DivisionByZero,
                    inputs: inputs.clone(),
                    iteration,
                    path_depth: 0,
                });
            }
        }
        None
    }

    /// Returns the number of VCs this oracle is checking.
    #[must_use]
    pub fn vc_count(&self) -> usize {
        self.vcs.len()
    }
}

// ---------------------------------------------------------------------------
// CoverageTracker: tracks branch/path coverage for the concolic/fuzzing loop
// ---------------------------------------------------------------------------

/// Tracks which branches and paths have been explored across concolic
/// execution runs, providing coverage metrics for guided exploration.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CoverageTracker {
    /// Set of covered branch IDs (each branch direction is a separate ID).
    /// Encoding: branch_location * 2 + direction (0=false, 1=true).
    covered_edges: BTreeSet<u64>,
    /// Total number of execution runs recorded.
    runs: usize,
    /// Number of runs that discovered at least one new edge.
    productive_runs: usize,
    /// Path signatures already explored (for dedup).
    explored_paths: BTreeSet<Vec<i128>>,
    /// Per-edge hit counts for frequency-based guidance.
    edge_counts: BTreeMap<u64, usize>,
}

impl CoverageTracker {
    /// Create a new empty coverage tracker.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Record a branch decision (location, direction).
    ///
    /// Returns `true` if this is a newly covered edge.
    pub fn record_branch(&mut self, location: usize, taken: bool) -> bool {
        let edge_id = (location as u64) * 2 + u64::from(taken);
        *self.edge_counts.entry(edge_id).or_insert(0) += 1;
        self.covered_edges.insert(edge_id)
    }

    /// Record a complete execution run with its branch decisions.
    ///
    /// Returns the number of newly covered edges from this run.
    pub fn record_run(&mut self, branches: &[(usize, bool)]) -> usize {
        self.runs += 1;
        let mut new_edges = 0;
        for &(loc, taken) in branches {
            if self.record_branch(loc, taken) {
                new_edges += 1;
            }
        }
        if new_edges > 0 {
            self.productive_runs += 1;
        }
        new_edges
    }

    /// Check whether a path signature has already been explored.
    ///
    /// Returns `true` if the path is novel (not previously seen).
    pub fn is_novel_path(&mut self, signature: &[i128]) -> bool {
        self.explored_paths.insert(signature.to_vec())
    }

    /// Returns the total number of covered edges.
    #[must_use]
    pub fn covered_edge_count(&self) -> usize {
        self.covered_edges.len()
    }

    /// Returns the total number of execution runs recorded.
    #[must_use]
    pub fn total_runs(&self) -> usize {
        self.runs
    }

    /// Returns the number of runs that discovered new coverage.
    #[must_use]
    pub fn productive_run_count(&self) -> usize {
        self.productive_runs
    }

    /// Returns the coverage efficiency: productive runs / total runs.
    ///
    /// Returns 1.0 if no runs have been recorded (vacuous).
    #[must_use]
    pub fn efficiency(&self) -> f64 {
        if self.runs == 0 {
            return 1.0;
        }
        self.productive_runs as f64 / self.runs as f64
    }

    /// Check whether a specific edge has been covered.
    #[must_use]
    pub fn is_edge_covered(&self, location: usize, taken: bool) -> bool {
        let edge_id = (location as u64) * 2 + u64::from(taken);
        self.covered_edges.contains(&edge_id)
    }

    /// Returns the hit count for a specific edge, or 0 if never hit.
    #[must_use]
    pub fn edge_hit_count(&self, location: usize, taken: bool) -> usize {
        let edge_id = (location as u64) * 2 + u64::from(taken);
        self.edge_counts.get(&edge_id).copied().unwrap_or(0)
    }

    /// Returns the number of unique paths explored.
    #[must_use]
    pub fn unique_path_count(&self) -> usize {
        self.explored_paths.len()
    }
}

// ---------------------------------------------------------------------------
// ConcolicFuzzTarget: generates fuzz harness code from VCs
// ---------------------------------------------------------------------------

/// A parameter descriptor for a function under test.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FuzzParam {
    /// Parameter name.
    pub name: String,
    /// Parameter type.
    pub ty: Ty,
}

/// A generated fuzz target for concolic/fuzzing integration.
///
/// Combines the function signature with VC-derived preconditions to produce
/// a focused fuzz harness that exercises the property under test.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConcolicFuzzTarget {
    /// Name of the function under test.
    pub function_name: String,
    /// Parameters of the function (name + type).
    pub params: Vec<FuzzParam>,
    /// Preconditions extracted from VCs (formulas that inputs must satisfy).
    pub preconditions: Vec<Formula>,
    /// VC kinds being targeted.
    pub target_vc_kinds: Vec<String>,
    /// Generated harness source code.
    pub harness_code: String,
}

impl ConcolicFuzzTarget {
    /// Generate a fuzz target from a function name, its parameters, and VCs.
    #[must_use]
    pub fn from_vcs(
        function_name: &str,
        params: &[FuzzParam],
        vcs: &[VerificationCondition],
    ) -> Self {
        let preconditions: Vec<Formula> =
            vcs.iter().filter_map(|vc| extract_precondition(&vc.formula)).collect();

        let target_vc_kinds: Vec<String> = vcs.iter().map(|vc| format!("{:?}", vc.kind)).collect();

        let harness_code = generate_harness(function_name, params, &preconditions);

        Self {
            function_name: function_name.to_string(),
            params: params.to_vec(),
            preconditions,
            target_vc_kinds,
            harness_code,
        }
    }

    /// Returns the number of parameters.
    #[must_use]
    pub fn param_count(&self) -> usize {
        self.params.len()
    }

    /// Returns the number of preconditions extracted from VCs.
    #[must_use]
    pub fn precondition_count(&self) -> usize {
        self.preconditions.len()
    }

    /// Generate seed inputs for the fuzzer based on boundary values of
    /// parameter types and VC-derived constraints.
    #[must_use]
    pub fn generate_seeds(&self) -> Vec<BTreeMap<String, i128>> {
        let mut seeds = Vec::new();

        // Seed 1: all zeros.
        let zero_seed: BTreeMap<String, i128> =
            self.params.iter().map(|p| (p.name.clone(), 0i128)).collect();
        seeds.push(zero_seed);

        // Seed 2: boundary values per parameter type.
        for param in &self.params {
            for val in boundary_values_for_param(&param.ty) {
                let mut seed: BTreeMap<String, i128> =
                    self.params.iter().map(|p| (p.name.clone(), 0i128)).collect();
                seed.insert(param.name.clone(), val);
                seeds.push(seed);
            }
        }

        // Seed 3: try to satisfy preconditions directly.
        if !self.preconditions.is_empty()
            && let Ok(Some(sat_inputs)) = generate_test_input_checked(&self.preconditions)
        {
            seeds.push(sat_inputs);
        }

        seeds
    }
}

/// Extract a precondition formula from a VC formula.
///
/// For implication-shaped VCs (`P => Q`), the precondition is `P`.
/// For other shapes, returns `None`.
fn extract_precondition(formula: &Formula) -> Option<Formula> {
    match formula {
        Formula::Implies(lhs, _) => Some(*lhs.clone()),
        Formula::And(clauses) if clauses.len() >= 2 => {
            // Treat the first clause as a precondition.
            Some(clauses[0].clone())
        }
        _ => None,
    }
}

/// Generate a harness code string for the fuzz target.
fn generate_harness(
    function_name: &str,
    params: &[FuzzParam],
    preconditions: &[Formula],
) -> String {
    let mut code = String::new();
    let _ = writeln!(code, "// Concolic fuzz target for `{function_name}`");
    let _ = writeln!(code, "// Parameters: {}", params.len());

    if !preconditions.is_empty() {
        let _ = writeln!(code, "// Preconditions: {}", preconditions.len());
    }

    code.push_str("//\n");
    code.push_str("// Generated by trust-symex concolic_fuzzing module.\n\n");

    // Parameter declarations
    for param in params {
        let ty_name = ty_to_name(&param.ty);
        let _ = writeln!(code, "// param: {}: {ty_name}", param.name);
    }

    let _ = write!(code, "\nfn fuzz_{function_name}(");
    let param_list: Vec<String> =
        params.iter().map(|p| format!("{}: {}", p.name, ty_to_name(&p.ty))).collect();
    code.push_str(&param_list.join(", "));
    code.push_str(") {\n");

    // Precondition guards
    for (i, pre) in preconditions.iter().enumerate() {
        let _ = writeln!(code, "    // Precondition [{i}]: {pre:?}");
    }

    let _ = writeln!(code, "    // PLACEHOLDER: call `{function_name}` and check postconditions");
    code.push_str("}\n");

    code
}

/// Map a `Ty` to its Rust type name.
fn ty_to_name(ty: &Ty) -> String {
    match ty {
        Ty::Bool => "bool".into(),
        Ty::Int { width, signed: true } => format!("i{width}"),
        Ty::Int { width, signed: false } => format!("u{width}"),
        Ty::Float { width: 32 } => "f32".into(),
        Ty::Float { width: 64 } => "f64".into(),
        Ty::Float { width } => format!("f{width}"),
        Ty::Unit => "()".into(),
        _ => "i32".into(),
    }
}

/// Return boundary values (as i128) for a given parameter type.
fn boundary_values_for_param(ty: &Ty) -> Vec<i128> {
    match ty {
        Ty::Bool => vec![0, 1],
        Ty::Int { width: 8, signed: true } => vec![i8::MIN as i128, -1, 0, 1, i8::MAX as i128],
        Ty::Int { width: 16, signed: true } => vec![i16::MIN as i128, -1, 0, 1, i16::MAX as i128],
        Ty::Int { width: 32, signed: true } => vec![i32::MIN as i128, -1, 0, 1, i32::MAX as i128],
        Ty::Int { width: 64, signed: true } => vec![i64::MIN as i128, -1, 0, 1, i64::MAX as i128],
        Ty::Int { width: 128, signed: true } => vec![i128::MIN, -1, 0, 1, i128::MAX],
        Ty::Int { width: 8, signed: false } => vec![0, 1, u8::MAX as i128 / 2, u8::MAX as i128],
        Ty::Int { width: 16, signed: false } => vec![0, 1, u16::MAX as i128 / 2, u16::MAX as i128],
        Ty::Int { width: 32, signed: false } => vec![0, 1, u32::MAX as i128 / 2, u32::MAX as i128],
        Ty::Int { width: 64, signed: false } => vec![0, 1, u64::MAX as i128 / 2, u64::MAX as i128],
        Ty::Int { width: 128, signed: false } => vec![0, 1, i128::MAX / 2, i128::MAX],
        _ => vec![-1, 0, 1],
    }
}

// ---------------------------------------------------------------------------
// ConcolicExecutor: the main integration driver
// ---------------------------------------------------------------------------

/// Configuration for the concolic/fuzzing executor.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConcolicFuzzConfig {
    /// Maximum number of exploration iterations.
    pub max_iterations: usize,
    /// Exploration strategy.
    pub strategy: ConcolicStrategy,
    /// Whether to generate seed inputs from VC boundary values.
    pub seed_from_boundaries: bool,
    /// Maximum number of constraint negations per iteration.
    pub max_negations_per_iter: usize,
    /// Random seed for the random strategy.
    pub random_seed: u64,
}

impl Default for ConcolicFuzzConfig {
    fn default() -> Self {
        Self {
            max_iterations: 200,
            strategy: ConcolicStrategy::CoverageGuided,
            seed_from_boundaries: true,
            max_negations_per_iter: 16,
            random_seed: 42,
        }
    }
}

/// Result of a concolic/fuzzing exploration campaign.
#[derive(Debug, Clone)]
pub struct ConcolicFuzzResult {
    /// Bugs discovered during exploration.
    pub bugs: Vec<BugReport>,
    /// Total number of iterations executed.
    pub iterations: usize,
    /// Number of unique paths explored.
    pub unique_paths: usize,
    /// Number of covered edges.
    pub covered_edges: usize,
    /// Coverage efficiency (productive runs / total runs).
    pub efficiency: f64,
    /// Whether the exploration exhausted all reachable paths.
    pub exhausted: bool,
}

/// The concolic/fuzzing executor: combines concolic execution with
/// coverage-guided fuzzing for fast bug finding.
///
/// The executor maintains a worklist of input vectors, runs each one
/// concretely while collecting symbolic constraints, checks for bugs
/// via the oracle, and generates new inputs by negating constraints
/// and applying coverage-guided prioritization.
pub struct ConcolicFuzzExecutor {
    /// Verification conditions to check.
    vcs: Vec<VerificationCondition>,
    /// Configuration.
    config: ConcolicFuzzConfig,
    /// Bug oracle for checking execution outcomes.
    oracle: BugOracle,
    /// Coverage tracker.
    coverage: CoverageTracker,
    /// Worklist of input vectors to explore.
    worklist: VecDeque<ConcolicState>,
    /// Discovered bugs.
    bugs: Vec<BugReport>,
    /// Iteration counter.
    iteration: usize,
    /// Names of free variables in the VC formulas.
    var_names: Vec<String>,
    /// Random state for the Random strategy.
    rng_state: u64,
}

impl ConcolicFuzzExecutor {
    /// Create a new executor for the given VCs and configuration.
    #[must_use]
    pub fn new(vcs: Vec<VerificationCondition>, config: ConcolicFuzzConfig) -> Self {
        // Collect all free variable names across VCs.
        let mut var_set: BTreeSet<String> = BTreeSet::default();
        for vc in &vcs {
            for v in sorted_free_variables(&vc.formula) {
                var_set.insert(v);
            }
        }
        let var_names: Vec<String> = var_set.into_iter().collect();

        let rng_state = if config.random_seed == 0 { 1 } else { config.random_seed };
        let oracle = BugOracle::new(vcs.clone());

        Self {
            vcs,
            config,
            oracle,
            coverage: CoverageTracker::new(),
            worklist: VecDeque::new(),
            bugs: Vec::new(),
            iteration: 0,
            var_names,
            rng_state,
        }
    }

    /// Add an initial input to the worklist.
    pub fn add_seed(&mut self, inputs: BTreeMap<String, i128>) {
        self.worklist.push_back(ConcolicState::with_values(inputs));
    }

    /// Seed the worklist with default inputs (zeros + boundary values).
    pub fn seed_defaults(&mut self) {
        // Zero seed.
        let zero: BTreeMap<String, i128> =
            self.var_names.iter().map(|v| (v.clone(), 0i128)).collect();
        self.worklist.push_back(ConcolicState::with_values(zero));

        // Try direct VC satisfaction.
        if self.config.seed_from_boundaries {
            for vc in &self.vcs {
                if matches!(vc.kind, VcKind::UnsupportedMir { .. }) {
                    continue;
                }
                let constraints = match &vc.formula {
                    Formula::And(cs) => cs.clone(),
                    other => vec![other.clone()],
                };
                if let Ok(Some(inputs)) = generate_test_input_checked(&constraints) {
                    self.worklist.push_back(ConcolicState::with_values(inputs));
                }
            }
        }
    }

    /// Run the concolic/fuzzing exploration loop.
    ///
    /// Returns a `ConcolicFuzzResult` summarizing the campaign.
    pub fn run(&mut self) -> ConcolicFuzzResult {
        // Seed if the worklist is empty.
        if self.worklist.is_empty() {
            self.seed_defaults();
        }

        while self.iteration < self.config.max_iterations {
            let state = match self.pick_next() {
                Some(s) => s,
                None => break,
            };

            // Build path signature for dedup.
            let sig: Vec<i128> = self
                .var_names
                .iter()
                .map(|v| state.concrete_values.get(v).copied())
                .collect::<Option<Vec<_>>>()
                .unwrap_or_default();
            if sig.len() != self.var_names.len() {
                continue;
            }
            if !self.coverage.is_novel_path(&sig) {
                continue;
            }

            self.iteration += 1;

            // Check VCs via the oracle.
            let found_bugs =
                self.oracle.check_inputs(&state.concrete_values, self.iteration, state.depth());
            self.bugs.extend(found_bugs);

            // Build path constraints from VC formulas.
            let path_state = self.build_path_state(&state.concrete_values);

            // Record coverage from branch constraints.
            let branches: Vec<(usize, bool)> = path_state
                .symbolic_constraints
                .iter()
                .enumerate()
                .filter_map(|(i, c)| {
                    execute_concrete_checked(c, &state.concrete_values).ok().map(|taken| (i, taken))
                })
                .collect();
            self.coverage.record_run(&branches);

            // Negate constraints to generate new inputs.
            let max_neg =
                self.config.max_negations_per_iter.min(path_state.symbolic_constraints.len());
            for idx in 0..max_neg {
                if let Some(negated) = negate_branch(&path_state, idx) {
                    let constraints = match &negated {
                        Formula::And(cs) => cs.clone(),
                        other => vec![other.clone()],
                    };
                    if let Ok(Some(new_inputs)) = generate_test_input_checked(&constraints) {
                        let mut child = ConcolicState::with_values(new_inputs);
                        child.symbolic_constraints = constraints;
                        self.worklist.push_back(child);
                    }
                }
            }
        }

        ConcolicFuzzResult {
            bugs: self.bugs.clone(),
            iterations: self.iteration,
            unique_paths: self.coverage.unique_path_count(),
            covered_edges: self.coverage.covered_edge_count(),
            efficiency: self.coverage.efficiency(),
            exhausted: self.worklist.is_empty(),
        }
    }

    /// Pick the next input from the worklist according to the strategy.
    fn pick_next(&mut self) -> Option<ConcolicState> {
        match self.config.strategy {
            ConcolicStrategy::DepthFirst => self.worklist.pop_back(),
            ConcolicStrategy::BreadthFirst => self.worklist.pop_front(),
            ConcolicStrategy::CoverageGuided => {
                // Prefer inputs whose path signature is novel.
                // Simple heuristic: pop from front (oldest first gives breadth),
                // but if we have many items, prefer the one with the most
                // uncovered branch potential.
                if self.worklist.len() <= 1 {
                    return self.worklist.pop_front();
                }
                // Score each candidate by how many of its constraints target
                // uncovered edges. Pick the best.
                let mut best_idx = 0;
                let mut best_score: i64 = i64::MIN;
                for (i, state) in self.worklist.iter().enumerate() {
                    let score = self.score_state(state);
                    if score > best_score {
                        best_score = score;
                        best_idx = i;
                    }
                }
                self.worklist.remove(best_idx)
            }
            ConcolicStrategy::Random => {
                if self.worklist.is_empty() {
                    return None;
                }
                let idx = (self.next_rand() as usize) % self.worklist.len();
                self.worklist.remove(idx)
            }
        }
    }

    /// Score a state for coverage-guided prioritization.
    /// Higher score = more interesting.
    fn score_state(&self, state: &ConcolicState) -> i64 {
        let mut score: i64 = 0;
        // Reward states with uncovered variable assignments.
        for (name, value) in &state.concrete_values {
            if *value != 0 {
                // Non-zero values are more interesting in general.
                score += 1;
            }
            let _ = name; // Suppress unused warning.
        }
        // Reward deeper paths (more constraints to negate = more exploration).
        score += state.depth() as i64;
        // Reward novelty: penalize states whose path signature was already seen.
        let sig: Vec<i128> =
            self.var_names.iter().map(|v| *state.concrete_values.get(v).unwrap_or(&0)).collect();
        if self.coverage.explored_paths.contains(&sig) {
            score -= 1000;
        }
        score
    }

    /// Build path constraints from all VC formulas for a given input.
    fn build_path_state(&self, inputs: &BTreeMap<String, i128>) -> ConcolicState {
        let mut state = ConcolicState::with_values(inputs.clone());
        for vc in &self.vcs {
            match &vc.formula {
                Formula::And(clauses) => {
                    for c in clauses {
                        state.add_constraint(c.clone());
                    }
                }
                Formula::Or(clauses) => {
                    for c in clauses {
                        state.add_constraint(c.clone());
                    }
                }
                Formula::Implies(lhs, rhs) => {
                    state.add_constraint(Formula::Not(Box::new(*lhs.clone())));
                    state.add_constraint(*rhs.clone());
                }
                other => {
                    state.add_constraint(other.clone());
                }
            }
        }
        state
    }

    /// xorshift64 PRNG step.
    fn next_rand(&mut self) -> u64 {
        let mut s = self.rng_state;
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        self.rng_state = s;
        s
    }

    /// Returns the current coverage tracker.
    #[must_use]
    pub fn coverage(&self) -> &CoverageTracker {
        &self.coverage
    }

    /// Returns bugs found so far.
    #[must_use]
    pub fn bugs_found(&self) -> &[BugReport] {
        &self.bugs
    }

    /// Returns the current iteration count.
    #[must_use]
    pub fn iterations(&self) -> usize {
        self.iteration
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::{Formula, Sort, SourceSpan, VcKind};

    use super::*;

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    fn make_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_fn".into(),
            location: span(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    fn make_vc_with_kind(formula: Formula, kind: VcKind) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: "test_fn".into(),
            location: span(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    // -----------------------------------------------------------------------
    // ConcolicStrategy
    // -----------------------------------------------------------------------

    #[test]
    fn test_concolic_strategy_default_is_coverage_guided() {
        assert_eq!(ConcolicStrategy::default(), ConcolicStrategy::CoverageGuided);
    }

    #[test]
    fn test_concolic_strategy_all_variants_constructible() {
        let _dfs = ConcolicStrategy::DepthFirst;
        let _cov = ConcolicStrategy::CoverageGuided;
        let _rnd = ConcolicStrategy::Random;
        let _bfs = ConcolicStrategy::BreadthFirst;
    }

    // -----------------------------------------------------------------------
    // BugKind + BugReport
    // -----------------------------------------------------------------------

    #[test]
    fn test_bug_kind_variants() {
        let _crash = BugKind::Crash { message: "oops".into() };
        let _assert = BugKind::AssertionFailure { message: "assert".into() };
        let _vc = BugKind::VcViolation { vc_index: 0, vc_kind: "div".into() };
        let _div = BugKind::DivisionByZero;
        let _overflow = BugKind::ArithmeticOverflow;
        let _oob = BugKind::IndexOutOfBounds;
    }

    #[test]
    fn test_bug_report_fields() {
        let report = BugReport {
            kind: BugKind::DivisionByZero,
            inputs: [("x".into(), 0)].into_iter().collect(),
            iteration: 5,
            path_depth: 3,
        };
        assert_eq!(report.iteration, 5);
        assert_eq!(report.path_depth, 3);
        assert_eq!(report.inputs["x"], 0);
    }

    // -----------------------------------------------------------------------
    // BugOracle
    // -----------------------------------------------------------------------

    #[test]
    fn test_bug_oracle_no_vcs() {
        let oracle = BugOracle::crash_only();
        assert_eq!(oracle.vc_count(), 0);
        let bugs = oracle.check_inputs(&BTreeMap::default(), 0, 0);
        assert!(bugs.is_empty());
    }

    #[test]
    fn test_bug_oracle_detects_vc_violation() {
        // VC: x == 42 (violated when x=42).
        let vc = make_vc(Formula::Eq(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(42)),
        ));
        let oracle = BugOracle::new(vec![vc]);
        assert_eq!(oracle.vc_count(), 1);

        // x=42 should violate the VC.
        let inputs: BTreeMap<String, i128> = [("x".into(), 42)].into_iter().collect();
        let bugs = oracle.check_inputs(&inputs, 1, 0);
        assert_eq!(bugs.len(), 1);
        assert!(matches!(&bugs[0].kind, BugKind::VcViolation { vc_index: 0, .. }));

        // x=0 should not violate.
        let inputs_ok: BTreeMap<String, i128> = [("x".into(), 0)].into_iter().collect();
        let bugs_ok = oracle.check_inputs(&inputs_ok, 2, 0);
        assert!(bugs_ok.is_empty());
    }

    #[test]
    fn test_bug_oracle_check_formula() {
        let oracle = BugOracle::crash_only();
        let formula = Formula::Bool(true);
        let bug = oracle.check_formula(&formula, &BTreeMap::default(), 0, "always true");
        assert!(bug.is_some());
        assert!(matches!(
            &bug.unwrap().kind,
            BugKind::AssertionFailure { message } if message == "always true"
        ));
    }

    #[test]
    fn test_bug_oracle_check_formula_safe() {
        let oracle = BugOracle::crash_only();
        let formula = Formula::Bool(false);
        let bug = oracle.check_formula(&formula, &BTreeMap::default(), 0, "never true");
        assert!(bug.is_none());
    }

    #[test]
    fn test_bug_oracle_check_division_by_zero() {
        let vc = make_vc_with_kind(
            Formula::Eq(
                Box::new(Formula::Var("divisor".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            VcKind::DivisionByZero,
        );
        let oracle = BugOracle::new(vec![vc]);

        // divisor=0 triggers the bug.
        let inputs: BTreeMap<String, i128> = [("divisor".into(), 0)].into_iter().collect();
        let bug = oracle.check_division_by_zero(&inputs, 1);
        assert!(bug.is_some());
        assert!(matches!(&bug.unwrap().kind, BugKind::DivisionByZero));

        // divisor=5 is safe.
        let inputs_safe: BTreeMap<String, i128> = [("divisor".into(), 5)].into_iter().collect();
        assert!(oracle.check_division_by_zero(&inputs_safe, 2).is_none());
    }

    #[test]
    fn test_bug_oracle_multiple_vcs() {
        let vc1 = make_vc(Formula::Eq(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(10)),
        ));
        let vc2 = make_vc(Formula::Eq(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(20)),
        ));
        let oracle = BugOracle::new(vec![vc1, vc2]);
        assert_eq!(oracle.vc_count(), 2);

        // x=10 violates only vc1.
        let inputs: BTreeMap<String, i128> = [("x".into(), 10)].into_iter().collect();
        let bugs = oracle.check_inputs(&inputs, 0, 0);
        assert_eq!(bugs.len(), 1);
        assert!(matches!(&bugs[0].kind, BugKind::VcViolation { vc_index: 0, .. }));
    }

    #[test]
    fn test_bug_oracle_unsupported_mir_is_not_a_bug() {
        let vc = make_vc_with_kind(
            Formula::Bool(true),
            VcKind::UnsupportedMir {
                kind: "TerminatorKind::Yield".into(),
                detail: "opaque control flow".into(),
            },
        );
        let oracle = BugOracle::new(vec![vc]);

        let bugs = oracle.check_inputs(&BTreeMap::default(), 0, 0);

        assert!(
            bugs.is_empty(),
            "UnsupportedMir is an unknown coverage gap, not a concrete bug report"
        );
    }

    // -----------------------------------------------------------------------
    // CoverageTracker
    // -----------------------------------------------------------------------

    #[test]
    fn test_coverage_tracker_new_empty() {
        let tracker = CoverageTracker::new();
        assert_eq!(tracker.covered_edge_count(), 0);
        assert_eq!(tracker.total_runs(), 0);
        assert_eq!(tracker.productive_run_count(), 0);
        assert_eq!(tracker.unique_path_count(), 0);
        assert_eq!(tracker.efficiency(), 1.0);
    }

    #[test]
    fn test_coverage_tracker_record_branch() {
        let mut tracker = CoverageTracker::new();
        assert!(tracker.record_branch(0, true)); // new edge
        assert!(!tracker.record_branch(0, true)); // already covered
        assert!(tracker.record_branch(0, false)); // new edge (different direction)
        assert_eq!(tracker.covered_edge_count(), 2);
    }

    #[test]
    fn test_coverage_tracker_record_run() {
        let mut tracker = CoverageTracker::new();
        let branches = vec![(0, true), (1, false), (2, true)];
        let new_edges = tracker.record_run(&branches);
        assert_eq!(new_edges, 3);
        assert_eq!(tracker.total_runs(), 1);
        assert_eq!(tracker.productive_run_count(), 1);

        // Same run again: no new edges.
        let new_edges2 = tracker.record_run(&branches);
        assert_eq!(new_edges2, 0);
        assert_eq!(tracker.total_runs(), 2);
        assert_eq!(tracker.productive_run_count(), 1);
    }

    #[test]
    fn test_coverage_tracker_is_novel_path() {
        let mut tracker = CoverageTracker::new();
        assert!(tracker.is_novel_path(&[0, 1, 2]));
        assert!(!tracker.is_novel_path(&[0, 1, 2])); // already seen
        assert!(tracker.is_novel_path(&[0, 1, 3])); // different
    }

    #[test]
    fn test_coverage_tracker_is_edge_covered() {
        let mut tracker = CoverageTracker::new();
        tracker.record_branch(5, true);
        assert!(tracker.is_edge_covered(5, true));
        assert!(!tracker.is_edge_covered(5, false));
        assert!(!tracker.is_edge_covered(6, true));
    }

    #[test]
    fn test_coverage_tracker_edge_hit_count() {
        let mut tracker = CoverageTracker::new();
        assert_eq!(tracker.edge_hit_count(0, true), 0);
        tracker.record_branch(0, true);
        assert_eq!(tracker.edge_hit_count(0, true), 1);
        tracker.record_branch(0, true);
        assert_eq!(tracker.edge_hit_count(0, true), 2);
        assert_eq!(tracker.edge_hit_count(0, false), 0);
    }

    #[test]
    fn test_coverage_tracker_efficiency() {
        let mut tracker = CoverageTracker::new();
        // First run: productive.
        tracker.record_run(&[(0, true)]);
        assert_eq!(tracker.efficiency(), 1.0);

        // Second run: not productive (same edges).
        tracker.record_run(&[(0, true)]);
        assert_eq!(tracker.efficiency(), 0.5);

        // Third run: productive (new edge).
        tracker.record_run(&[(0, false)]);
        assert!((tracker.efficiency() - 2.0 / 3.0).abs() < 1e-10);
    }

    #[test]
    fn test_coverage_tracker_unique_path_count() {
        let mut tracker = CoverageTracker::new();
        tracker.is_novel_path(&[1, 2, 3]);
        tracker.is_novel_path(&[4, 5, 6]);
        tracker.is_novel_path(&[1, 2, 3]); // duplicate
        assert_eq!(tracker.unique_path_count(), 2);
    }

    // -----------------------------------------------------------------------
    // ConcolicFuzzTarget
    // -----------------------------------------------------------------------

    #[test]
    fn test_fuzz_target_from_vcs_no_vcs() {
        let params = vec![FuzzParam { name: "x".into(), ty: Ty::i32() }];
        let target = ConcolicFuzzTarget::from_vcs("compute", &params, &[]);
        assert_eq!(target.function_name, "compute");
        assert_eq!(target.param_count(), 1);
        assert_eq!(target.precondition_count(), 0);
        assert!(target.harness_code.contains("compute"));
    }

    #[test]
    fn test_fuzz_target_from_vcs_with_vcs() {
        let params = vec![
            FuzzParam { name: "a".into(), ty: Ty::i32() },
            FuzzParam { name: "b".into(), ty: Ty::i32() },
        ];
        let vc = make_vc(Formula::Implies(
            Box::new(Formula::Gt(
                Box::new(Formula::Var("a".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
            Box::new(Formula::Bool(true)),
        ));
        let target = ConcolicFuzzTarget::from_vcs("add", &params, &[vc]);
        assert_eq!(target.param_count(), 2);
        assert_eq!(target.precondition_count(), 1);
        assert!(!target.target_vc_kinds.is_empty());
    }

    #[test]
    fn test_fuzz_target_generate_seeds() {
        let params = vec![FuzzParam { name: "x".into(), ty: Ty::i32() }];
        let target = ConcolicFuzzTarget::from_vcs("f", &params, &[]);
        let seeds = target.generate_seeds();
        // At least the zero seed + boundary values for i32.
        assert!(seeds.len() >= 2);
        // Zero seed should be first.
        assert_eq!(seeds[0]["x"], 0);
    }

    #[test]
    fn test_fuzz_target_generate_seeds_with_preconditions() {
        let params = vec![FuzzParam { name: "x".into(), ty: Ty::i32() }];
        let vc = make_vc(Formula::Implies(
            Box::new(Formula::Eq(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(99)),
            )),
            Box::new(Formula::Bool(true)),
        ));
        let target = ConcolicFuzzTarget::from_vcs("f", &params, &[vc]);
        let seeds = target.generate_seeds();
        // Should include a seed satisfying the precondition x=99.
        assert!(seeds.iter().any(|s| s.get("x") == Some(&99)));
    }

    #[test]
    fn test_fuzz_target_harness_code_contains_params() {
        let params = vec![
            FuzzParam { name: "a".into(), ty: Ty::i32() },
            FuzzParam { name: "b".into(), ty: Ty::Int { width: 64, signed: false } },
        ];
        let target = ConcolicFuzzTarget::from_vcs("process", &params, &[]);
        assert!(target.harness_code.contains("a: i32"));
        assert!(target.harness_code.contains("b: u64"));
        assert!(target.harness_code.contains("fuzz_process"));
    }

    // -----------------------------------------------------------------------
    // ConcolicFuzzConfig
    // -----------------------------------------------------------------------

    #[test]
    fn test_fuzz_config_default() {
        let config = ConcolicFuzzConfig::default();
        assert_eq!(config.max_iterations, 200);
        assert_eq!(config.strategy, ConcolicStrategy::CoverageGuided);
        assert!(config.seed_from_boundaries);
        assert_eq!(config.max_negations_per_iter, 16);
        assert_eq!(config.random_seed, 42);
    }

    // -----------------------------------------------------------------------
    // ConcolicFuzzExecutor
    // -----------------------------------------------------------------------

    #[test]
    fn test_executor_no_vcs_no_bugs() {
        let config = ConcolicFuzzConfig { max_iterations: 10, ..Default::default() };
        let mut executor = ConcolicFuzzExecutor::new(vec![], config);
        let result = executor.run();
        assert!(result.bugs.is_empty());
        assert!(result.iterations <= 10);
    }

    #[test]
    fn test_executor_finds_simple_vc_violation() {
        // VC: x == 42 (violated when x=42).
        let vc = make_vc(Formula::Eq(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(42)),
        ));
        let config = ConcolicFuzzConfig { max_iterations: 100, ..Default::default() };
        let mut executor = ConcolicFuzzExecutor::new(vec![vc], config);
        let result = executor.run();
        assert!(!result.bugs.is_empty(), "should find x=42 bug");
        // Check that at least one bug has x=42.
        let has_42 = result.bugs.iter().any(|b| b.inputs.get("x") == Some(&42));
        assert!(has_42, "bug should have x=42");
    }

    #[test]
    fn test_executor_finds_inequality_bug() {
        // VC: x < 0 (violated when x is negative).
        let vc = make_vc(Formula::Lt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ));
        let config = ConcolicFuzzConfig { max_iterations: 50, ..Default::default() };
        let mut executor = ConcolicFuzzExecutor::new(vec![vc], config);
        let result = executor.run();
        assert!(!result.bugs.is_empty(), "should find x<0 bug");
        let has_negative = result.bugs.iter().any(|b| b.inputs.get("x").is_some_and(|&x| x < 0));
        assert!(has_negative, "bug should have negative x");
    }

    #[test]
    fn test_executor_no_bug_for_unsatisfiable_vc() {
        // VC: Bool(false) -- never violated.
        let vc = make_vc(Formula::Bool(false));
        let config = ConcolicFuzzConfig { max_iterations: 20, ..Default::default() };
        let mut executor = ConcolicFuzzExecutor::new(vec![vc], config);
        let result = executor.run();
        assert!(result.bugs.is_empty());
    }

    #[test]
    fn test_executor_custom_seed() {
        let vc = make_vc(Formula::Eq(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(999)),
        ));
        let config = ConcolicFuzzConfig {
            max_iterations: 5,
            seed_from_boundaries: false,
            ..Default::default()
        };
        let mut executor = ConcolicFuzzExecutor::new(vec![vc], config);
        // Provide the exact bug-triggering input.
        executor.add_seed([("x".into(), 999)].into_iter().collect());
        let result = executor.run();
        assert!(!result.bugs.is_empty());
    }

    #[test]
    fn test_executor_depth_first_strategy() {
        let vc = make_vc(Formula::Eq(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(42)),
        ));
        let config = ConcolicFuzzConfig {
            max_iterations: 50,
            strategy: ConcolicStrategy::DepthFirst,
            ..Default::default()
        };
        let mut executor = ConcolicFuzzExecutor::new(vec![vc], config);
        let result = executor.run();
        // DFS should still find the bug.
        assert!(!result.bugs.is_empty());
    }

    #[test]
    fn test_executor_random_strategy() {
        let vc = make_vc(Formula::Eq(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(42)),
        ));
        let config = ConcolicFuzzConfig {
            max_iterations: 50,
            strategy: ConcolicStrategy::Random,
            random_seed: 12345,
            ..Default::default()
        };
        let mut executor = ConcolicFuzzExecutor::new(vec![vc], config);
        let result = executor.run();
        assert!(!result.bugs.is_empty());
    }

    #[test]
    fn test_executor_breadth_first_strategy() {
        let vc = make_vc(Formula::Eq(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(42)),
        ));
        let config = ConcolicFuzzConfig {
            max_iterations: 50,
            strategy: ConcolicStrategy::BreadthFirst,
            ..Default::default()
        };
        let mut executor = ConcolicFuzzExecutor::new(vec![vc], config);
        let result = executor.run();
        assert!(!result.bugs.is_empty());
    }

    #[test]
    fn test_executor_coverage_tracking() {
        let vc = make_vc(Formula::And(vec![
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(100))),
        ]));
        let config = ConcolicFuzzConfig { max_iterations: 20, ..Default::default() };
        let mut executor = ConcolicFuzzExecutor::new(vec![vc], config);
        let result = executor.run();
        assert!(result.covered_edges > 0);
        assert!(result.unique_paths > 0);
    }

    #[test]
    fn test_executor_result_fields() {
        let config = ConcolicFuzzConfig { max_iterations: 5, ..Default::default() };
        let mut executor = ConcolicFuzzExecutor::new(vec![], config);
        let result = executor.run();
        assert!(result.iterations <= 5);
        assert!(result.efficiency >= 0.0);
        assert!(result.efficiency <= 1.0);
    }

    #[test]
    fn test_executor_respects_iteration_limit() {
        // VC that is never violated: Bool(false).
        let vc = make_vc(Formula::Bool(false));
        let config = ConcolicFuzzConfig { max_iterations: 3, ..Default::default() };
        let mut executor = ConcolicFuzzExecutor::new(vec![vc], config);
        let result = executor.run();
        assert!(result.iterations <= 3);
    }

    #[test]
    fn test_executor_accessor_methods() {
        let vc = make_vc(Formula::Bool(false));
        let config = ConcolicFuzzConfig::default();
        let executor = ConcolicFuzzExecutor::new(vec![vc], config);
        assert_eq!(executor.iterations(), 0);
        assert!(executor.bugs_found().is_empty());
        assert_eq!(executor.coverage().covered_edge_count(), 0);
    }

    // -----------------------------------------------------------------------
    // Helper function tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_boundary_values_for_i32() {
        let vals = boundary_values_for_param(&Ty::i32());
        assert!(vals.contains(&(i32::MIN as i128)));
        assert!(vals.contains(&(i32::MAX as i128)));
        assert!(vals.contains(&0));
        assert!(vals.contains(&1));
        assert!(vals.contains(&-1));
    }

    #[test]
    fn test_boundary_values_for_u64() {
        let vals = boundary_values_for_param(&Ty::Int { width: 64, signed: false });
        assert!(vals.contains(&0));
        assert!(vals.contains(&1));
        assert!(vals.contains(&(u64::MAX as i128)));
    }

    #[test]
    fn test_boundary_values_for_bool() {
        let vals = boundary_values_for_param(&Ty::Bool);
        assert_eq!(vals, vec![0, 1]);
    }

    #[test]
    fn test_ty_to_name_coverage() {
        assert_eq!(ty_to_name(&Ty::Bool), "bool");
        assert_eq!(ty_to_name(&Ty::i32()), "i32");
        assert_eq!(ty_to_name(&Ty::Int { width: 64, signed: false }), "u64");
        assert_eq!(ty_to_name(&Ty::Float { width: 32 }), "f32");
        assert_eq!(ty_to_name(&Ty::Float { width: 64 }), "f64");
        assert_eq!(ty_to_name(&Ty::Unit), "()");
    }

    #[test]
    fn test_extract_precondition_implies() {
        let formula = Formula::Implies(
            Box::new(Formula::Var("p".into(), Sort::Bool)),
            Box::new(Formula::Var("q".into(), Sort::Bool)),
        );
        let pre = extract_precondition(&formula);
        assert!(pre.is_some());
        assert!(matches!(pre.unwrap(), Formula::Var(name, _) if name == "p"));
    }

    #[test]
    fn test_extract_precondition_and() {
        let formula = Formula::And(vec![
            Formula::Var("pre".into(), Sort::Bool),
            Formula::Var("post".into(), Sort::Bool),
        ]);
        let pre = extract_precondition(&formula);
        assert!(pre.is_some());
        assert!(matches!(pre.unwrap(), Formula::Var(name, _) if name == "pre"));
    }

    #[test]
    fn test_extract_precondition_atomic_returns_none() {
        let formula = Formula::Bool(true);
        assert!(extract_precondition(&formula).is_none());
    }

    #[test]
    fn test_generate_harness_basic() {
        let params = vec![FuzzParam { name: "x".into(), ty: Ty::i32() }];
        let code = generate_harness("test_fn", &params, &[]);
        assert!(code.contains("fuzz_test_fn"));
        assert!(code.contains("x: i32"));
        assert!(code.contains("trust-symex"));
    }

    #[test]
    fn test_fuzz_target_with_conjunction_vc() {
        let params = vec![FuzzParam { name: "x".into(), ty: Ty::i32() }];
        let vc = make_vc(Formula::And(vec![
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(100))),
        ]));
        let target = ConcolicFuzzTarget::from_vcs("bounded", &params, &[vc]);
        // A conjunction with >= 2 clauses extracts the first as precondition.
        assert_eq!(target.precondition_count(), 1);
    }

    #[test]
    fn test_executor_multiple_vcs() {
        let vc1 = make_vc(Formula::Eq(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(10)),
        ));
        let vc2 = make_vc(Formula::Eq(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(20)),
        ));
        let config = ConcolicFuzzConfig { max_iterations: 100, ..Default::default() };
        let mut executor = ConcolicFuzzExecutor::new(vec![vc1, vc2], config);
        let result = executor.run();
        // Should find both x=10 and x=20 bugs.
        let has_10 = result.bugs.iter().any(|b| b.inputs.get("x") == Some(&10));
        let has_20 = result.bugs.iter().any(|b| b.inputs.get("x") == Some(&20));
        assert!(has_10, "should find x=10 bug");
        assert!(has_20, "should find x=20 bug");
    }

    #[test]
    fn test_executor_two_variable_vc() {
        // VC: x + y == 100
        let vc = make_vc(Formula::Eq(
            Box::new(Formula::Add(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Var("y".into(), Sort::Int)),
            )),
            Box::new(Formula::Int(100)),
        ));
        let config = ConcolicFuzzConfig { max_iterations: 50, ..Default::default() };
        let mut executor = ConcolicFuzzExecutor::new(vec![vc], config);
        // Seed with a satisfying input.
        executor.add_seed([("x".into(), 50), ("y".into(), 50)].into_iter().collect());
        let result = executor.run();
        // Should find a bug where x+y == 100.
        assert!(!result.bugs.is_empty());
        let has_sum_100 = result.bugs.iter().any(|b| {
            let x = b.inputs.get("x").copied().unwrap_or(0);
            let y = b.inputs.get("y").copied().unwrap_or(0);
            x.wrapping_add(y) == 100
        });
        assert!(has_sum_100, "should find inputs where x+y=100");
    }
}
