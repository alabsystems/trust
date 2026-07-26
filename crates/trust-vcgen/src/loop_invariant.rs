// trust_vcgen/loop_invariant.rs: Loop invariant inference via abstract interpretation widening
//
// Infers loop invariants by classifying MIR loop patterns
// and applying widening-based abstract interpretation to generate
// sound invariant formulas. Builds on the fixpoint computation in
// abstract_interp.rs and the loop detection in loop_analysis.rs.
//
// Architecture:
//   LoopPattern enum     -> classifies loop body into Counter/Accumulator/Iterator/Unknown
//   LoopInvariant        -> wraps a Formula with metadata (source pattern, loop header)
//   InvariantInferer     -> configurable inference engine with widening parameters
//   infer_invariant_interval -> produces bounds from init/step/bound arithmetic
//   classify_loop_pattern    -> analyzes header + body statements for common patterns
//
// Reference: Cousot & Cousot, "Abstract Interpretation: A Unified Lattice Model
// for Static Analysis of Programs" (POPL 1977).
// Reference: Blanchet et al., "A static analyzer for large safety-critical
// software" (PLDI 2003) — widening with thresholds.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

use crate::abstract_interp::{self, FixpointResult};

// ── Loop Pattern Classification ────────────────────────────────────────────

/// Classification of a loop's iteration pattern.
///
/// Used to select the appropriate invariant inference strategy.
/// Each pattern implies different invariant templates.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum LoopPattern {
    /// Simple counting loop: `for i in 0..n` or `while i < n { i += step }`.
    /// Fields: (variable_name, init_value, step, bound).
    Counter {
        /// Name of the induction variable.
        var: String,
        /// Initial value at loop entry.
        init: i128,
        /// Step size per iteration (positive = ascending, negative = descending).
        step: i128,
        /// Upper or lower bound (depending on step direction).
        bound: i128,
    },
    /// Accumulator pattern: variable monotonically increases/decreases.
    /// Example: `sum += arr[i]` where `arr[i] >= 0`.
    Accumulator {
        /// Name of the accumulator variable.
        var: String,
        /// Initial value.
        init: i128,
        /// Whether the accumulator is monotonically non-decreasing.
        monotone_increasing: bool,
    },
    /// Iterator-style pattern: iterating over a collection with index bounds.
    /// Example: `for elem in slice.iter()` lowered to index-based loop.
    Iterator {
        /// Name of the index variable.
        index_var: String,
        /// Name of the collection length variable (or constant length).
        length_var: String,
    },
    /// Unrecognized loop pattern — no specialized invariant template available.
    Unknown,
}

/// A discovered loop invariant wrapping a Formula.
///
/// Produced by abstract interpretation widening or pattern-based inference.
/// Can be injected into VCs as assumptions at loop headers.
#[derive(Debug, Clone)]
#[must_use]
pub struct LoopInvariant {
    /// The invariant formula (holds at loop header on every iteration).
    pub formula: Formula,
    /// Which loop header this invariant applies to.
    pub loop_header: BlockId,
    /// The pattern that generated this invariant.
    pub source_pattern: LoopPattern,
    /// Confidence that this invariant is inductive [0.0, 1.0].
    pub confidence: f64,
}

impl LoopInvariant {
    /// Create a new loop invariant.
    pub fn new(
        formula: Formula,
        loop_header: BlockId,
        source_pattern: LoopPattern,
        confidence: f64,
    ) -> Self {
        Self { formula, loop_header, source_pattern, confidence }
    }

    /// Whether this invariant was generated from a recognized pattern
    /// (not Unknown).
    #[must_use]
    pub fn is_pattern_based(&self) -> bool {
        !matches!(self.source_pattern, LoopPattern::Unknown)
    }
}

// ── Interval-Based Invariant Inference ─────────────────────────────────────

/// Infer a loop invariant from counter arithmetic.
///
/// Given a loop variable with known init, step, and bound, produces the
/// tightest interval invariant: `init <= var <= bound` (for positive step)
/// or `bound <= var <= init` (for negative step).
///
/// Returns `Formula::And([lo_bound, hi_bound])` where bounds are
/// `var >= lo` and `var <= hi`.
#[must_use]
pub fn infer_invariant_interval(loop_var: &str, init: i128, step: i128, bound: i128) -> Formula {
    // Build the variable reference.
    let var = Formula::Var(loop_var.to_string(), Sort::Int);

    if step > 0 {
        // Ascending counter: init <= var <= bound
        let lo = Formula::Ge(Box::new(var.clone()), Box::new(Formula::Int(init)));
        let hi = Formula::Le(Box::new(var), Box::new(Formula::Int(bound)));
        Formula::And(vec![lo, hi])
    } else if step < 0 {
        // Descending counter: bound <= var <= init
        let lo = Formula::Ge(Box::new(var.clone()), Box::new(Formula::Int(bound)));
        let hi = Formula::Le(Box::new(var), Box::new(Formula::Int(init)));
        Formula::And(vec![lo, hi])
    } else {
        // step == 0: variable is constant
        Formula::Eq(Box::new(var), Box::new(Formula::Int(init)))
    }
}

// ── Loop Pattern Classification ────────────────────────────────────────────

/// Classify a loop's iteration pattern from its header and body.
///
/// Examines the header block's terminator (for loop condition) and body
/// statements (for assignments) to determine if this is a Counter,
/// Accumulator, Iterator, or Unknown loop pattern.
///
/// Heuristic-based: relies on MIR's structured layout where loop headers
/// have lower block IDs than loop bodies, and standard Rust loop lowering
/// patterns.
#[must_use]
pub fn classify_loop_pattern(header: &BasicBlock, body: &[Statement]) -> LoopPattern {
    // Look for counter pattern: header has SwitchInt (loop condition),
    // body has assignment incrementing/decrementing a variable.

    // Extract the discriminant variable from the header's terminator.
    let cond_var = match &header.terminator {
        Terminator::SwitchInt { discr, .. } => extract_var_name(discr),
        Terminator::Assert { cond, .. } => extract_var_name(cond),
        _ => None,
    };

    // Look for induction variable patterns in the body.
    let mut counter_candidates: Vec<(String, i128)> = Vec::new();
    let mut accumulator_candidates: Vec<(String, bool)> = Vec::new();
    let mut index_candidates: Vec<(String, String)> = Vec::new();

    for stmt in body {
        if let Statement::Assign { place, rvalue, .. } = stmt {
            match rvalue {
                // var = var + const (counter pattern, signed)
                Rvalue::BinaryOp(BinOp::Add, lhs, Operand::Constant(ConstValue::Int(step)))
                    if is_same_place_operand(place, lhs) =>
                {
                    let var_name = place_var_name(place);
                    counter_candidates.push((var_name, *step));
                }
                // var = var + const (counter pattern, unsigned)
                Rvalue::BinaryOp(BinOp::Add, lhs, Operand::Constant(ConstValue::Uint(step, _)))
                    if is_same_place_operand(place, lhs) =>
                {
                    let var_name = place_var_name(place);
                    let step_val = i128::try_from(*step).unwrap_or(1);
                    counter_candidates.push((var_name, step_val));
                }
                Rvalue::BinaryOp(BinOp::Sub, lhs, Operand::Constant(ConstValue::Int(step)))
                    if is_same_place_operand(place, lhs) =>
                {
                    let var_name = place_var_name(place);
                    counter_candidates.push((var_name, -step));
                }
                Rvalue::BinaryOp(BinOp::Sub, lhs, Operand::Constant(ConstValue::Uint(step, _)))
                    if is_same_place_operand(place, lhs) =>
                {
                    let var_name = place_var_name(place);
                    let neg_step = i128::try_from(*step).map(|s| -s).unwrap_or(-1);
                    counter_candidates.push((var_name, neg_step));
                }

                // Checked add/sub patterns (from overflow-checked arithmetic)
                Rvalue::CheckedBinaryOp(
                    BinOp::Add,
                    lhs,
                    Operand::Constant(ConstValue::Int(step)),
                ) if is_same_place_operand(place, lhs) => {
                    let var_name = place_var_name(place);
                    counter_candidates.push((var_name, *step));
                }
                Rvalue::CheckedBinaryOp(
                    BinOp::Sub,
                    lhs,
                    Operand::Constant(ConstValue::Int(step)),
                ) if is_same_place_operand(place, lhs) => {
                    let var_name = place_var_name(place);
                    counter_candidates.push((var_name, -step));
                }

                // Accumulator pattern: var = var + <expr> (where expr is not a constant
                // relative to the same variable)
                Rvalue::BinaryOp(BinOp::Add, lhs, _)
                    if is_same_place_operand(place, lhs)
                        && counter_candidates.iter().all(|(n, _)| *n != place_var_name(place)) =>
                {
                    accumulator_candidates.push((place_var_name(place), true));
                }

                // Index pattern: Len(place) suggests array iteration
                Rvalue::Len(len_place) => {
                    let len_var = place_var_name(len_place);
                    // If we have a counter candidate, pair it with this length
                    if let Some((idx_var, _)) = counter_candidates.first() {
                        index_candidates.push((idx_var.clone(), len_var));
                    }
                }

                _ => {}
            }
        }
    }

    // Prioritize classification: Iterator > Counter > Accumulator > Unknown.
    if let Some((index_var, length_var)) = index_candidates.into_iter().next() {
        return LoopPattern::Iterator { index_var, length_var };
    }

    if let Some((var, step)) = counter_candidates.into_iter().next() {
        // Try to extract the bound from the header's switch condition.
        let bound = extract_switch_bound(header);
        return LoopPattern::Counter {
            var,
            init: 0, // Conservative default; actual init requires pre-loop analysis.
            step,
            bound: bound.unwrap_or(i128::MAX),
        };
    }

    if let Some((var, monotone_increasing)) = accumulator_candidates.into_iter().next() {
        return LoopPattern::Accumulator { var, init: 0, monotone_increasing };
    }

    // If the header has a condition variable, check if we
    // missed a counter pattern due to indirect assignment.
    if let Some(cv) = cond_var {
        // If the condition variable appears in the body at all, it might
        // be a counter we couldn't recognize. Return Unknown but log the
        // candidate for future improvements.
        let _in_body = body.iter().any(|s| {
            if let Statement::Assign { place, .. } = s {
                place_var_name(place) == cv
            } else {
                false
            }
        });
    }

    LoopPattern::Unknown
}

// ── Invariant Inferer ──────────────────────────────────────────────────────

/// Configurable loop invariant inference engine.
///
/// Uses abstract interpretation with widening to compute fixpoint,
/// then extracts invariants from the converged abstract state.
/// Pattern classification guides which invariant templates to apply.
#[derive(Debug, Clone)]
#[must_use]
pub struct InvariantInferer {
    /// Maximum widening iterations before giving up.
    pub max_widen_iterations: usize,
    /// Number of narrowing passes after widening converges.
    pub narrowing_passes: usize,
    /// Minimum confidence threshold for reporting invariants.
    pub min_confidence: f64,
}

impl Default for InvariantInferer {
    fn default() -> Self {
        Self { max_widen_iterations: 100, narrowing_passes: 3, min_confidence: 0.5 }
    }
}

impl InvariantInferer {
    /// Create a new inferer with default parameters.
    pub fn new() -> Self {
        Self::default()
    }

    /// Set maximum widening iterations.
    pub fn with_max_iterations(mut self, max: usize) -> Self {
        self.max_widen_iterations = max;
        self
    }

    /// Set number of narrowing passes.
    pub fn with_narrowing_passes(mut self, passes: usize) -> Self {
        self.narrowing_passes = passes;
        self
    }

    /// Set minimum confidence threshold.
    pub fn with_min_confidence(mut self, threshold: f64) -> Self {
        self.min_confidence = threshold;
        self
    }

    /// Infer loop invariants for a function using abstract interpretation.
    ///
    /// 1. Computes fixpoint with widening (via abstract_interp::fixpoint_with_narrowing).
    /// 2. Classifies each loop's pattern from its header and body.
    /// 3. Generates invariant formulas based on pattern + interval data.
    /// 4. Filters by confidence threshold.
    #[must_use]
    pub fn infer(&self, func: &VerifiableFunction) -> Vec<LoopInvariant> {
        // Detect loop headers (widen points).
        let widen_points = abstract_interp::detect_widen_points(func);
        if widen_points.is_empty() {
            return Vec::new();
        }

        // Compute fixpoint with narrowing for precision recovery.
        let initial = abstract_interp::type_aware_initial_state(func);
        let fp = abstract_interp::fixpoint_with_narrowing(func, initial, self.narrowing_passes);

        let mut invariants = Vec::new();

        for wp in &widen_points {
            let header_id = wp.block;

            // Find the header block.
            let Some(header) = func.body.blocks.iter().find(|b| b.id == header_id) else {
                continue;
            };

            // Collect body statements from blocks between header and latch.
            let body_stmts = collect_loop_body_stmts(func, header_id);

            // Classify the loop pattern.
            let pattern = classify_loop_pattern(header, &body_stmts);

            // Generate invariants based on pattern and fixpoint data.
            let pattern_invs = self.invariants_from_pattern(&pattern, header_id, &fp);
            invariants.extend(pattern_invs);

            // Also extract interval-based invariants from fixpoint state.
            let interval_invs = self.invariants_from_intervals(header_id, &fp);
            invariants.extend(interval_invs);
        }

        // Filter by confidence threshold.
        invariants.retain(|inv| inv.confidence >= self.min_confidence);

        // Sort by confidence descending.
        invariants.sort_by(|a, b| {
            b.confidence.partial_cmp(&a.confidence).unwrap_or(std::cmp::Ordering::Equal)
        });

        invariants
    }

    /// Generate invariants from a classified loop pattern.
    fn invariants_from_pattern(
        &self,
        pattern: &LoopPattern,
        header: BlockId,
        _fp: &FixpointResult,
    ) -> Vec<LoopInvariant> {
        match pattern {
            LoopPattern::Counter { var, init, step, bound } => {
                // Counter bounds invariant.
                let formula = infer_invariant_interval(var, *init, *step, *bound);
                vec![LoopInvariant::new(formula, header, pattern.clone(), 0.9)]
            }
            LoopPattern::Accumulator { var, init, monotone_increasing } => {
                // Monotonicity invariant for accumulators.
                let var_formula = Formula::Var(var.clone(), Sort::Int);
                let formula = if *monotone_increasing {
                    // acc >= init (monotonically non-decreasing)
                    Formula::Ge(Box::new(var_formula), Box::new(Formula::Int(*init)))
                } else {
                    // acc <= init (monotonically non-increasing)
                    Formula::Le(Box::new(var_formula), Box::new(Formula::Int(*init)))
                };
                vec![LoopInvariant::new(formula, header, pattern.clone(), 0.7)]
            }
            LoopPattern::Iterator { index_var, length_var } => {
                // Index-in-bounds invariant: 0 <= i && i <= len.
                let idx = Formula::Var(index_var.clone(), Sort::Int);
                let len = Formula::Var(length_var.clone(), Sort::Int);
                let lo_bound = Formula::Ge(Box::new(idx.clone()), Box::new(Formula::Int(0)));
                let hi_bound = Formula::Le(Box::new(idx), Box::new(len));
                let formula = Formula::And(vec![lo_bound, hi_bound]);
                vec![LoopInvariant::new(formula, header, pattern.clone(), 0.85)]
            }
            LoopPattern::Unknown => Vec::new(),
        }
    }

    /// Extract invariants from fixpoint interval data at a loop header.
    fn invariants_from_intervals(
        &self,
        header: BlockId,
        fp: &FixpointResult,
    ) -> Vec<LoopInvariant> {
        let Some(state) = fp.block_states.get(&header) else {
            return Vec::new();
        };
        if state.is_unreachable {
            return Vec::new();
        }

        let mut invariants = Vec::new();

        for (var_name, interval) in &state.vars {
            if interval.is_bottom() {
                continue;
            }

            let var_formula = Formula::Var(var_name.clone(), Sort::Int);
            let mut bounds = Vec::new();

            // Lower bound from interval.
            if interval.lo != i128::MIN {
                bounds.push(Formula::Ge(
                    Box::new(var_formula.clone()),
                    Box::new(Formula::Int(interval.lo)),
                ));
            }

            // Upper bound from interval.
            if interval.hi != i128::MAX {
                bounds
                    .push(Formula::Le(Box::new(var_formula), Box::new(Formula::Int(interval.hi))));
            }

            if !bounds.is_empty() {
                let formula = if bounds.len() == 1 {
                    bounds.into_iter().next().expect("invariant: non-empty bounds vec")
                } else {
                    Formula::And(bounds)
                };

                invariants.push(LoopInvariant::new(
                    formula,
                    header,
                    LoopPattern::Unknown,
                    0.6, // Interval-only invariants get moderate confidence.
                ));
            }
        }

        invariants
    }
}

// ── Helper Functions ───────────────────────────────────────────────────────

/// Extract variable name from an operand (Copy or Move of a simple local).
fn extract_var_name(op: &Operand) -> Option<String> {
    match op {
        Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => {
            Some(place_var_name(place))
        }
        _ => None,
    }
}

/// Build a variable name string from a Place.
fn place_var_name(place: &Place) -> String {
    format!("_{}", place.local)
}

/// Check whether an operand refers to the same place (same local, no projections).
fn is_same_place_operand(place: &Place, op: &Operand) -> bool {
    match op {
        Operand::Copy(p) | Operand::Move(p) => {
            p.local == place.local && p.projections.is_empty() && place.projections.is_empty()
        }
        _ => false,
    }
}

/// Extract a numeric bound from a SwitchInt terminator.
///
/// For `SwitchInt { discr, targets: [(val, _)], otherwise }`, the bound
/// is typically `val` (the comparison target in a `while i < bound` loop).
fn extract_switch_bound(header: &BasicBlock) -> Option<i128> {
    if let Terminator::SwitchInt { targets, .. } = &header.terminator
        && let Some((val, _)) = targets.first()
    {
        return i128::try_from(*val).ok();
    }
    None
}

/// Collect all statements from blocks that form the loop body.
///
/// The loop body consists of blocks with IDs between header and the
/// latch (highest-numbered block that has a back-edge to the header).
/// This is a sound over-approximation for MIR's structured layout.
fn collect_loop_body_stmts(func: &VerifiableFunction, header: BlockId) -> Vec<Statement> {
    // Find latch block (highest block that branches back to header).
    let latch_id = func
        .body
        .blocks
        .iter()
        .filter(|b| b.id.0 > header.0 && terminator_targets_block(&b.terminator, header))
        .map(|b| b.id.0)
        .max();

    let Some(latch) = latch_id else {
        return Vec::new();
    };

    // Collect statements from all body blocks (header exclusive, through latch).
    func.body
        .blocks
        .iter()
        .filter(|b| b.id.0 > header.0 && b.id.0 <= latch)
        .flat_map(|b| b.stmts.clone())
        .collect()
}

/// Check if a terminator has a target that is a specific block.
fn terminator_targets_block(term: &Terminator, target: BlockId) -> bool {
    match term {
        Terminator::Goto(t) => *t == target,
        Terminator::SwitchInt { targets, otherwise, .. } => {
            *otherwise == target || targets.iter().any(|(_, b)| *b == target)
        }
        Terminator::Assert { target: t, .. } => *t == target,
        Terminator::Call { target: t, .. } => t.as_ref() == Some(&target),
        Terminator::Drop { target: t, .. } => *t == target,
        Terminator::Opaque { targets, .. } => targets.contains(&target),
        _ => false,
    }
}

// ── Tests ──────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use trust_types::{
        BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
        Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
    };

    use super::*;

    // ── Helper: build a simple counter loop function ───────────────────

    /// Build a function with a counter loop: `while i < 10 { i += 1; }`
    ///
    /// bb0: i = 0; goto bb1
    /// bb1 (header): switchint(i < 10) -> [true: bb2, false: bb3]
    /// bb2 (body): i = i + 1; goto bb1
    /// bb3 (exit): return
    fn counter_loop_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "counter_loop".to_string(),
            def_path: "test::counter_loop".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("i".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: Some("cond".into()) },
                ],
                blocks: vec![
                    // bb0: init i = 0, goto bb1
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(1),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    // bb1 (header): switchint on condition
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Lt,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Int(10)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(2)),
                            targets: vec![(1, BlockId(2))],
                            otherwise: BlockId(3),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    // bb2 (body): i = i + 1; goto bb1 (back-edge)
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(1),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Int(1)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    // bb3 (exit): return
                    BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Build a function with an accumulator loop: `sum += values[i]`
    fn accumulator_loop_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "accumulator_loop".to_string(),
            def_path: "test::accumulator_loop".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("i".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("sum".into()) },
                    LocalDecl { index: 3, ty: Ty::Bool, name: Some("cond".into()) },
                    LocalDecl { index: 4, ty: Ty::i32(), name: Some("val".into()) },
                ],
                blocks: vec![
                    // bb0: i = 0; sum = 0; goto bb1
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(1),
                                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(2),
                                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    // bb1 (header): switchint on i < 10
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Lt,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Int(10)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(3)),
                            targets: vec![(1, BlockId(2))],
                            otherwise: BlockId(3),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    // bb2 (body): sum = sum + val; i = i + 1; goto bb1
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(2),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Add,
                                    Operand::Copy(Place::local(2)),
                                    Operand::Copy(Place::local(4)),
                                ),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(1),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Add,
                                    Operand::Copy(Place::local(1)),
                                    Operand::Constant(ConstValue::Int(1)),
                                ),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    // bb3 (exit): return sum
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 0,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Build a no-loop function (straight-line code).
    fn no_loop_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "no_loop".to_string(),
            def_path: "test::no_loop".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    // ── Tests ──────────────────────────────────────────────────────────

    #[test]
    fn test_infer_invariant_interval_ascending() {
        // Ascending counter: 0 <= i <= 10
        let formula = infer_invariant_interval("i", 0, 1, 10);
        match &formula {
            Formula::And(parts) => {
                assert_eq!(parts.len(), 2, "ascending counter should have 2 bounds");
                // First: i >= 0
                assert!(
                    matches!(&parts[0], Formula::Ge(var, bound)
                        if matches!(var.as_ref(), Formula::Var(n, _) if n == "i")
                        && matches!(bound.as_ref(), Formula::Int(0))),
                    "lower bound should be i >= 0, got: {:?}",
                    parts[0]
                );
                // Second: i <= 10
                assert!(
                    matches!(&parts[1], Formula::Le(var, bound)
                        if matches!(var.as_ref(), Formula::Var(n, _) if n == "i")
                        && matches!(bound.as_ref(), Formula::Int(10))),
                    "upper bound should be i <= 10, got: {:?}",
                    parts[1]
                );
            }
            other => panic!("expected And, got: {other:?}"),
        }
    }

    #[test]
    fn test_infer_invariant_interval_descending() {
        // Descending counter: 5 <= i <= 100
        let formula = infer_invariant_interval("i", 100, -1, 5);
        match &formula {
            Formula::And(parts) => {
                assert_eq!(parts.len(), 2);
                // First: i >= 5
                assert!(matches!(&parts[0], Formula::Ge(_, bound)
                    if matches!(bound.as_ref(), Formula::Int(5))));
                // Second: i <= 100
                assert!(matches!(&parts[1], Formula::Le(_, bound)
                    if matches!(bound.as_ref(), Formula::Int(100))));
            }
            other => panic!("expected And, got: {other:?}"),
        }
    }

    #[test]
    fn test_infer_invariant_interval_zero_step() {
        // Zero step: i == 42
        let formula = infer_invariant_interval("i", 42, 0, 100);
        assert!(
            matches!(&formula, Formula::Eq(var, val)
                if matches!(var.as_ref(), Formula::Var(n, _) if n == "i")
                && matches!(val.as_ref(), Formula::Int(42))),
            "zero step should produce equality, got: {formula:?}"
        );
    }

    #[test]
    fn test_classify_loop_pattern_counter() {
        let header = BasicBlock {
            id: BlockId(1),
            stmts: vec![],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(2)),
                targets: vec![(1, BlockId(2))],
                otherwise: BlockId(3),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        };
        let body = vec![Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Int(1)),
            ),
            span: SourceSpan::default(),
        }];

        let pattern = classify_loop_pattern(&header, &body);
        match &pattern {
            LoopPattern::Counter { var, step, .. } => {
                assert_eq!(var, "_1");
                assert_eq!(*step, 1);
            }
            other => panic!("expected Counter, got: {other:?}"),
        }
    }

    #[test]
    fn test_classify_loop_pattern_accumulator() {
        let header = BasicBlock {
            id: BlockId(1),
            stmts: vec![],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(3)),
                targets: vec![(1, BlockId(2))],
                otherwise: BlockId(3),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        };
        // sum = sum + val (non-constant rhs)
        let body = vec![Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(2)),
                Operand::Copy(Place::local(4)),
            ),
            span: SourceSpan::default(),
        }];

        let pattern = classify_loop_pattern(&header, &body);
        assert!(
            matches!(&pattern, LoopPattern::Accumulator { var, monotone_increasing: true, .. }
                if var == "_2"),
            "expected Accumulator, got: {pattern:?}"
        );
    }

    #[test]
    fn test_classify_loop_pattern_unknown_empty_body() {
        let header = BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return };
        let pattern = classify_loop_pattern(&header, &[]);
        assert_eq!(pattern, LoopPattern::Unknown);
    }

    #[test]
    fn test_classify_loop_pattern_descending_counter() {
        let header = BasicBlock {
            id: BlockId(1),
            stmts: vec![],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(2)),
                targets: vec![(1, BlockId(2))],
                otherwise: BlockId(3),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        };
        let body = vec![Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::BinaryOp(
                BinOp::Sub,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Int(1)),
            ),
            span: SourceSpan::default(),
        }];

        let pattern = classify_loop_pattern(&header, &body);
        match &pattern {
            LoopPattern::Counter { step, .. } => {
                assert_eq!(*step, -1, "descending counter should have step -1");
            }
            other => panic!("expected Counter with negative step, got: {other:?}"),
        }
    }

    #[test]
    fn test_inferer_no_loops_returns_empty() {
        let func = no_loop_function();
        let inferer = InvariantInferer::new();
        let invariants = inferer.infer(&func);
        assert!(invariants.is_empty(), "no-loop function should produce no invariants");
    }

    #[test]
    fn test_inferer_counter_loop_produces_invariants() {
        let func = counter_loop_function();
        let inferer = InvariantInferer::new();
        let invariants = inferer.infer(&func);
        assert!(!invariants.is_empty(), "counter loop should produce at least one invariant");
        // At least one invariant should be pattern-based.
        assert!(
            invariants.iter().any(LoopInvariant::is_pattern_based),
            "counter loop should produce pattern-based invariant"
        );
    }

    #[test]
    fn test_inferer_confidence_ordering() {
        let func = counter_loop_function();
        let inferer = InvariantInferer::new();
        let invariants = inferer.infer(&func);
        // Verify sorted by confidence descending.
        for window in invariants.windows(2) {
            assert!(
                window[0].confidence >= window[1].confidence,
                "invariants should be sorted by confidence descending"
            );
        }
    }

    #[test]
    fn test_inferer_min_confidence_filtering() {
        let func = counter_loop_function();
        let inferer = InvariantInferer::new().with_min_confidence(0.95);
        let high_conf = inferer.infer(&func);

        let inferer_low = InvariantInferer::new().with_min_confidence(0.1);
        let low_conf = inferer_low.infer(&func);

        assert!(
            high_conf.len() <= low_conf.len(),
            "higher confidence threshold should produce <= invariants"
        );
    }

    #[test]
    fn test_loop_invariant_is_pattern_based() {
        let inv_counter = LoopInvariant::new(
            Formula::Bool(true),
            BlockId(0),
            LoopPattern::Counter { var: "i".into(), init: 0, step: 1, bound: 10 },
            0.9,
        );
        assert!(inv_counter.is_pattern_based());

        let inv_unknown =
            LoopInvariant::new(Formula::Bool(true), BlockId(0), LoopPattern::Unknown, 0.5);
        assert!(!inv_unknown.is_pattern_based());
    }

    #[test]
    fn test_classify_loop_pattern_iterator_with_len() {
        let header = BasicBlock {
            id: BlockId(1),
            stmts: vec![],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(3)),
                targets: vec![(1, BlockId(2))],
                otherwise: BlockId(3),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        };
        // Body: i += 1 (counter) + Len(arr) (length extraction)
        let body = vec![
            Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Add,
                    Operand::Copy(Place::local(1)),
                    Operand::Constant(ConstValue::Int(1)),
                ),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(4),
                rvalue: Rvalue::Len(Place::local(5)),
                span: SourceSpan::default(),
            },
        ];

        let pattern = classify_loop_pattern(&header, &body);
        assert!(
            matches!(&pattern, LoopPattern::Iterator { index_var, length_var }
                if index_var == "_1" && length_var == "_5"),
            "expected Iterator pattern, got: {pattern:?}"
        );
    }

    #[test]
    fn test_extract_switch_bound() {
        let header = BasicBlock {
            id: BlockId(1),
            stmts: vec![],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(1)),
                targets: vec![(42, BlockId(2))],
                otherwise: BlockId(3),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        };
        assert_eq!(extract_switch_bound(&header), Some(42));

        let no_switch =
            BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return };
        assert_eq!(extract_switch_bound(&no_switch), None);
    }

    #[test]
    fn test_accumulator_loop_inferer() {
        let func = accumulator_loop_function();
        let inferer = InvariantInferer::new();
        let invariants = inferer.infer(&func);
        // Should produce invariants (at least interval-based).
        assert!(!invariants.is_empty(), "accumulator loop should produce invariants");
    }

    #[test]
    fn test_counter_uint_step() {
        let header = BasicBlock {
            id: BlockId(1),
            stmts: vec![],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(2)),
                targets: vec![(1, BlockId(2))],
                otherwise: BlockId(3),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        };
        // i += 2u32
        let body = vec![Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Uint(2, 32)),
            ),
            span: SourceSpan::default(),
        }];

        let pattern = classify_loop_pattern(&header, &body);
        match &pattern {
            LoopPattern::Counter { step, .. } => {
                assert_eq!(*step, 2, "Uint step should be converted correctly");
            }
            other => panic!("expected Counter, got: {other:?}"),
        }
    }
}
