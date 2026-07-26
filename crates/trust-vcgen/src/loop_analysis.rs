// trust_vcgen/loop_analysis.rs: Structured loop analysis from MIR CFG
//
// Builds on the basic back-edge detection in termination.rs with richer
// loop information: exit blocks, induction variables with init/step/bound,
// and natural loop membership via dominator-free heuristics on MIR's
// structured block layout.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;
use trust_types::*;

/// Direction an induction variable moves on each iteration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StepDirection {
    Ascending,
    Descending,
}

/// An induction variable detected inside a loop.
#[derive(Debug, Clone)]
#[allow(dead_code)] // Fields read in tests; struct populated by detect_loops
pub(crate) struct InductionVar {
    /// Local variable index in the function body.
    pub(crate) local_idx: usize,
    /// Human-readable variable name.
    pub(crate) name: String,
    /// Initial value formula (assigned before the loop or at loop entry).
    pub(crate) init: Option<Formula>,
    /// Step size per iteration (positive = ascending, negative = descending).
    pub(crate) step: i128,
    /// Direction of change.
    pub(crate) direction: StepDirection,
    /// Upper or lower bound from the loop condition, if detected.
    pub(crate) bound: Option<Formula>,
}

/// Rich loop information extracted from the MIR CFG.
#[derive(Debug, Clone)]
pub struct LoopInfo {
    /// Block ID of the loop header (target of the back-edge).
    pub(crate) header: BlockId,
    /// Block ID of the latch (source of the back-edge).
    pub(crate) _latch: BlockId,
    /// All blocks in the loop body (header through latch, inclusive).
    pub(crate) body_blocks: Vec<BlockId>,
    /// Blocks that exit the loop (successors of body blocks that are outside the loop).
    pub(crate) _exit_blocks: Vec<BlockId>,
    /// Induction variables detected in this loop (populated by `find_induction_variables`).
    pub(crate) induction_vars: Vec<InductionVar>,
}

impl LoopInfo {
    /// Block that heads the natural loop.
    #[must_use]
    pub fn header(&self) -> BlockId {
        self.header
    }

    /// Block whose back-edge closes the natural loop.
    #[must_use]
    pub fn latch(&self) -> BlockId {
        self._latch
    }

    /// Blocks belonging to the natural loop, including its header and latch.
    #[must_use]
    pub fn body_blocks(&self) -> &[BlockId] {
        &self.body_blocks
    }

    /// Successor blocks outside the natural loop.
    #[must_use]
    pub fn exit_blocks(&self) -> &[BlockId] {
        &self._exit_blocks
    }
}

/// Detect natural loops in the CFG by finding back-edges.
///
/// A back-edge is a CFG edge where the target block ID <= the source block ID.
/// This heuristic works for MIR's structured control flow where loop headers
/// always have lower block IDs than their latches.
///
/// For each detected loop, also computes exit blocks: successors of body blocks
/// that fall outside the loop body.
#[must_use]
pub fn detect_loops(func: &VerifiableFunction) -> Vec<LoopInfo> {
    let mut loops = Vec::new();

    for block in &func.body.blocks {
        let successors = block_successors(&block.terminator);
        for succ in successors {
            if succ.0 <= block.id.0 {
                let header = succ;
                let latch = block.id;

                let body_set: FxHashSet<usize> = func
                    .body
                    .blocks
                    .iter()
                    .filter(|bb| bb.id.0 >= header.0 && bb.id.0 <= latch.0)
                    .map(|bb| bb.id.0)
                    .collect();

                let body_blocks: Vec<BlockId> = body_set.iter().map(|&id| BlockId(id)).collect();

                // Exit blocks: successors of body blocks that are NOT in the body
                let mut exit_blocks = Vec::new();
                for &body_id in &body_set {
                    if let Some(bb) = func.body.blocks.get(body_id) {
                        for s in block_successors(&bb.terminator) {
                            if !body_set.contains(&s.0) && !exit_blocks.contains(&s) {
                                exit_blocks.push(s);
                            }
                        }
                    }
                }

                loops.push(LoopInfo {
                    header,
                    _latch: latch,
                    body_blocks,
                    _exit_blocks: exit_blocks,
                    induction_vars: Vec::new(),
                });
            }
        }
    }

    // Populate induction variables for each loop
    for loop_info in &mut loops {
        loop_info.induction_vars = find_induction_variables(loop_info, func);
    }

    loops
}

/// Find induction variables in a loop.
///
/// An induction variable is a local that:
/// 1. Is assigned as `var = var +/- constant` in the loop body
/// 2. Has an integer type
///
/// We also attempt to find the initial value (from assignments before the loop)
/// and the loop bound (from comparisons in the header block).
#[must_use]
pub(crate) fn find_induction_variables(
    loop_info: &LoopInfo,
    func: &VerifiableFunction,
) -> Vec<InductionVar> {
    let body_set: FxHashSet<usize> = loop_info.body_blocks.iter().map(|b| b.0).collect();
    let mut vars = Vec::new();

    for &body_id in &body_set {
        let Some(block) = func.body.blocks.get(body_id) else {
            continue;
        };
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt {
                if !place.projections.is_empty() {
                    continue;
                }
                let local_idx = place.local;
                let Some(decl) = func.body.locals.get(local_idx) else {
                    continue;
                };
                if !decl.ty.is_integer() {
                    continue;
                }
                // Already found this variable?
                if vars.iter().any(|v: &InductionVar| v.local_idx == local_idx) {
                    continue;
                }

                let step = detect_step(rvalue, local_idx);
                if let Some(step_val) = step {
                    let name = decl.name.clone().unwrap_or_else(|| format!("_{local_idx}"));
                    let direction = if step_val > 0 {
                        StepDirection::Ascending
                    } else {
                        StepDirection::Descending
                    };
                    let init = find_init_value(func, loop_info, local_idx);
                    let bound = find_loop_bound(func, loop_info, local_idx);

                    vars.push(InductionVar {
                        local_idx,
                        name,
                        init,
                        step: step_val,
                        direction,
                        bound,
                    });
                }
            }
        }
    }

    vars
}

/// Detect if an rvalue is `local = local +/- constant`, returning the step.
fn detect_step(rvalue: &Rvalue, local_idx: usize) -> Option<i128> {
    match rvalue {
        Rvalue::BinaryOp(BinOp::Add, Operand::Copy(src), Operand::Constant(cv))
        | Rvalue::BinaryOp(BinOp::Add, Operand::Constant(cv), Operand::Copy(src))
            if src.local == local_idx && src.projections.is_empty() =>
        {
            const_to_i128(cv)
        }
        Rvalue::BinaryOp(BinOp::Sub, Operand::Copy(src), Operand::Constant(cv))
            if src.local == local_idx && src.projections.is_empty() =>
        {
            const_to_i128(cv).map(|v| -v)
        }
        // CheckedBinaryOp variants
        Rvalue::CheckedBinaryOp(BinOp::Add, Operand::Copy(src), Operand::Constant(cv))
        | Rvalue::CheckedBinaryOp(BinOp::Add, Operand::Constant(cv), Operand::Copy(src))
            if src.local == local_idx && src.projections.is_empty() =>
        {
            const_to_i128(cv)
        }
        Rvalue::CheckedBinaryOp(BinOp::Sub, Operand::Copy(src), Operand::Constant(cv))
            if src.local == local_idx && src.projections.is_empty() =>
        {
            const_to_i128(cv).map(|v| -v)
        }
        _ => None,
    }
}

/// Find the initial value of an induction variable.
///
/// Looks in blocks BEFORE the loop header for a `local = constant` assignment.
fn find_init_value(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
    local_idx: usize,
) -> Option<Formula> {
    for block in &func.body.blocks {
        // Only look in blocks before the loop header
        if block.id.0 >= loop_info.header.0 {
            break;
        }
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt
                && place.local == local_idx
                && place.projections.is_empty()
                && let Rvalue::Use(op) = rvalue
            {
                return Some(crate::operand_to_formula(func, op));
            }
        }
    }
    None
}

/// Find the loop bound from the header block's comparison involving the given local.
fn find_loop_bound(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
    local_idx: usize,
) -> Option<Formula> {
    let header_block = func.body.blocks.get(loop_info.header.0)?;

    for stmt in &header_block.stmts {
        if let Statement::Assign { rvalue, .. } = stmt {
            match rvalue {
                // i < bound or i <= bound
                Rvalue::BinaryOp(BinOp::Lt | BinOp::Le, Operand::Copy(lhs), rhs)
                    if lhs.local == local_idx && lhs.projections.is_empty() =>
                {
                    return Some(crate::operand_to_formula(func, rhs));
                }
                // bound > i or bound >= i
                Rvalue::BinaryOp(BinOp::Gt | BinOp::Ge, rhs, Operand::Copy(lhs))
                    if lhs.local == local_idx && lhs.projections.is_empty() =>
                {
                    return Some(crate::operand_to_formula(func, rhs));
                }
                // i > bound (descending loop)
                Rvalue::BinaryOp(BinOp::Gt | BinOp::Ge, Operand::Copy(lhs), rhs)
                    if lhs.local == local_idx && lhs.projections.is_empty() =>
                {
                    return Some(crate::operand_to_formula(func, rhs));
                }
                _ => {}
            }
        }
    }

    None
}

/// Get all successor block IDs from a terminator.
fn block_successors(term: &Terminator) -> Vec<BlockId> {
    match term {
        Terminator::Goto(target) => vec![*target],
        Terminator::SwitchInt { targets, otherwise, .. } => {
            let mut succs: Vec<BlockId> = targets.iter().map(|(_, t)| *t).collect();
            succs.push(*otherwise);
            succs
        }
        Terminator::Return | Terminator::Unreachable => vec![],
        Terminator::Call { target, .. } => target.iter().copied().collect(),
        Terminator::Assert { target, .. } => vec![*target],
        Terminator::Drop { target, .. } => vec![*target],
        Terminator::Opaque { targets, .. } => targets.clone(),
        _ => vec![],
    }
}

fn const_to_i128(cv: &ConstValue) -> Option<i128> {
    match cv {
        ConstValue::Int(n) => Some(*n),
        ConstValue::Uint(n, _) => Some(*n as i128),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a counted loop: while i < n { sum += i; i += 1; }
    fn sum_loop_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "sum_to_n".to_string(),
            def_path: "test::sum_to_n".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("i".into()) },
                    LocalDecl { index: 3, ty: Ty::u32(), name: Some("sum".into()) },
                    LocalDecl { index: 4, ty: Ty::Bool, name: Some("cond".into()) },
                ],
                blocks: vec![
                    // bb0: i = 0; sum = 0; goto bb1
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(2),
                                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(3),
                                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    // bb1 (header): cond = i < n; SwitchInt -> [1: bb2, else: bb3]
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Lt,
                                Operand::Copy(Place::local(2)),
                                Operand::Copy(Place::local(1)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(4)),
                            targets: vec![(1, BlockId(2))],
                            otherwise: BlockId(3),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    // bb2 (body): sum += i; i += 1; goto bb1
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(3),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Add,
                                    Operand::Copy(Place::local(3)),
                                    Operand::Copy(Place::local(2)),
                                ),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(2),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Add,
                                    Operand::Copy(Place::local(2)),
                                    Operand::Constant(ConstValue::Uint(1, 64)),
                                ),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    // bb3 (exit): _0 = sum; return
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Build a countdown loop: while n > 0 { n -= 1; }
    fn countdown_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "countdown".to_string(),
            def_path: "test::countdown".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: Some("cond".into()) },
                ],
                blocks: vec![
                    // bb0 (header): cond = n > 0; SwitchInt -> [1: bb1, else: bb2]
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Gt,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(0, 64)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(2)),
                            targets: vec![(1, BlockId(1))],
                            otherwise: BlockId(2),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    // bb1 (body): n -= 1; goto bb0
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(1),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Sub,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(1, 64)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Goto(BlockId(0)),
                    },
                    // bb2 (exit): return
                    BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Build a binary search loop
    fn binary_search_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "binary_search".to_string(),
            def_path: "test::binary_search".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Bool, name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Ref {
                            mutable: false,
                            inner: Box::new(Ty::Slice { elem: Box::new(Ty::u32()) }),
                        },
                        name: Some("arr".into()),
                    },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("target".into()) },
                    LocalDecl { index: 3, ty: Ty::usize(), name: Some("low".into()) },
                    LocalDecl { index: 4, ty: Ty::usize(), name: Some("high".into()) },
                    LocalDecl { index: 5, ty: Ty::usize(), name: Some("mid".into()) },
                    LocalDecl { index: 6, ty: Ty::Bool, name: Some("cond".into()) },
                    LocalDecl { index: 7, ty: Ty::usize(), name: Some("len".into()) },
                ],
                blocks: vec![
                    // bb0: len = arr.len(); low = 0; high = len; goto bb1
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(7),
                                rvalue: Rvalue::Len(Place::local(1)),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(3),
                                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(4),
                                rvalue: Rvalue::Use(Operand::Copy(Place::local(7))),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    // bb1 (header): cond = low < high; SwitchInt -> [1: bb2, else: bb3]
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(6),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Lt,
                                Operand::Copy(Place::local(3)),
                                Operand::Copy(Place::local(4)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(6)),
                            targets: vec![(1, BlockId(2))],
                            otherwise: BlockId(3),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    // bb2 (body): mid = (low + high) / 2; low = mid + 1; goto bb1
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(5),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Div,
                                    Operand::Copy(Place::local(3)),
                                    Operand::Constant(ConstValue::Uint(2, 64)),
                                ),
                                span: SourceSpan::default(),
                            },
                            Statement::Assign {
                                place: Place::local(3),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Add,
                                    Operand::Copy(Place::local(5)),
                                    Operand::Constant(ConstValue::Uint(1, 64)),
                                ),
                                span: SourceSpan::default(),
                            },
                        ],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    // bb3 (exit): return false
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(false))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 2,
                return_ty: Ty::Bool,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// No-loop function for negative test.
    fn no_loop_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "identity".to_string(),
            def_path: "test::identity".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
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
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_detect_loops_counted() {
        let func = sum_loop_function();
        let loops = detect_loops(&func);
        assert_eq!(loops.len(), 1, "sum loop has exactly one loop");
        assert_eq!(loops[0].header, BlockId(1));
        assert_eq!(loops[0]._latch, BlockId(2));
        assert!(loops[0].body_blocks.contains(&BlockId(1)));
        assert!(loops[0].body_blocks.contains(&BlockId(2)));
    }

    #[test]
    fn test_detect_loops_exit_blocks() {
        let func = sum_loop_function();
        let loops = detect_loops(&func);
        assert_eq!(loops.len(), 1);
        // bb3 is the exit block (otherwise target of SwitchInt in bb1)
        assert!(
            loops[0]._exit_blocks.contains(&BlockId(3)),
            "bb3 should be an exit block, got: {:?}",
            loops[0]._exit_blocks
        );
    }

    #[test]
    fn test_detect_loops_countdown_descending() {
        let func = countdown_function();
        let loops = detect_loops(&func);
        assert_eq!(loops.len(), 1);
        assert_eq!(loops[0].header, BlockId(0));
        assert_eq!(loops[0]._latch, BlockId(1));
    }

    #[test]
    fn test_no_loops_detected_for_straight_line() {
        let func = no_loop_function();
        let loops = detect_loops(&func);
        assert!(loops.is_empty(), "no loops in identity function");
    }

    #[test]
    fn test_induction_var_ascending() {
        let func = sum_loop_function();
        let loops = detect_loops(&func);
        assert_eq!(loops.len(), 1);

        let ivars = &loops[0].induction_vars;
        // `i` (local 2) is incremented by 1
        let i_var = ivars.iter().find(|v| v.name == "i");
        assert!(i_var.is_some(), "should detect `i` as induction variable");
        let i_var = i_var.unwrap();
        assert_eq!(i_var.step, 1);
        assert_eq!(i_var.direction, StepDirection::Ascending);
        assert!(i_var.init.is_some(), "should find init value for i");
        assert!(
            matches!(&i_var.init, Some(Formula::Int(0))),
            "init should be 0, got: {:?}",
            i_var.init
        );
        assert!(i_var.bound.is_some(), "should find bound for i");
    }

    #[test]
    fn test_induction_var_descending() {
        let func = countdown_function();
        let loops = detect_loops(&func);
        assert_eq!(loops.len(), 1);

        let ivars = &loops[0].induction_vars;
        let n_var = ivars.iter().find(|v| v.name == "n");
        assert!(n_var.is_some(), "should detect `n` as induction variable");
        let n_var = n_var.unwrap();
        assert_eq!(n_var.step, -1);
        assert_eq!(n_var.direction, StepDirection::Descending);
    }

    #[test]
    fn test_induction_var_bound_detection() {
        let func = sum_loop_function();
        let loops = detect_loops(&func);
        let ivars = &loops[0].induction_vars;
        let i_var = ivars.iter().find(|v| v.name == "i").unwrap();
        // Bound should reference variable `n`
        assert!(
            matches!(&i_var.bound, Some(Formula::Var(name, Sort::Int)) if name == "n"),
            "bound should be variable n, got: {:?}",
            i_var.bound
        );
    }

    #[test]
    fn test_binary_search_loop_detected() {
        let func = binary_search_function();
        let loops = detect_loops(&func);
        assert_eq!(loops.len(), 1, "binary search has exactly one loop");
        assert_eq!(loops[0].header, BlockId(1));

        // In a binary search, `low = mid + 1` does NOT match the `var = var + const`
        // induction variable pattern. This is correct: binary search convergence is
        // proved via the `high - low` measure decreasing, not via a simple step.
        // The binary search invariant (`low <= high`) is detected by the
        // invariant_inference::infer_binary_search pattern instead.
        let ivars = &loops[0].induction_vars;
        // No simple induction variables expected in binary search
        assert!(
            ivars.is_empty() || !ivars.iter().any(|v| v.name == "low"),
            "low should not be a simple induction var (low = mid + 1, not low = low + 1)"
        );
    }

    #[test]
    fn test_binary_search_has_exit_block() {
        let func = binary_search_function();
        let loops = detect_loops(&func);
        assert!(loops[0]._exit_blocks.contains(&BlockId(3)), "bb3 should be exit block");
    }

    #[test]
    fn test_find_induction_variables_standalone() {
        let func = sum_loop_function();
        let loops = detect_loops(&func);
        let ivars = find_induction_variables(&loops[0], &func);
        assert!(!ivars.is_empty(), "should find at least one induction variable");
        assert!(ivars.iter().any(|v| v.name == "i"), "should find `i` as induction variable");
    }

    #[test]
    fn test_detect_step_add() {
        let rvalue = Rvalue::BinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local(2)),
            Operand::Constant(ConstValue::Uint(1, 64)),
        );
        assert_eq!(detect_step(&rvalue, 2), Some(1));
    }

    #[test]
    fn test_detect_step_sub() {
        let rvalue = Rvalue::BinaryOp(
            BinOp::Sub,
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Uint(1, 64)),
        );
        assert_eq!(detect_step(&rvalue, 1), Some(-1));
    }

    #[test]
    fn test_detect_step_non_matching() {
        let rvalue = Rvalue::BinaryOp(
            BinOp::Mul,
            Operand::Copy(Place::local(2)),
            Operand::Constant(ConstValue::Uint(2, 64)),
        );
        assert_eq!(detect_step(&rvalue, 2), None);
    }

    #[test]
    fn test_detect_step_wrong_local() {
        let rvalue = Rvalue::BinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local(5)),
            Operand::Constant(ConstValue::Uint(1, 64)),
        );
        assert_eq!(detect_step(&rvalue, 2), None, "step detection should not match wrong local");
    }
}
