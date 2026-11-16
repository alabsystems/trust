// trust_vcgen/loop_analysis.rs: Structured loop analysis from MIR CFG
//
// Builds on the basic back-edge detection in termination.rs with richer
// loop information: exit blocks, induction variables with their initial value,
// and natural loop membership via dominator-free heuristics on MIR's
// structured block layout.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;
use trust_types::*;

/// An induction variable detected inside a loop.
///
/// Carries exactly what production reads: `chc::build_init_args` matches
/// `local_idx` and inlines `init` as the invariant's initial state.
#[derive(Debug, Clone)]
pub(crate) struct InductionVar {
    /// Local variable index in the function body.
    pub(crate) local_idx: usize,
    /// Initial value formula (assigned before the loop or at loop entry).
    pub(crate) init: Option<Formula>,
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

/// True iff any block in `func.body.blocks` has a CFG back-edge (`succ.0 <= block.id.0`).
#[must_use]
pub(crate) fn has_back_edge(func: &VerifiableFunction) -> bool {
    if let Some(tp) = crate::generate::cached_terminator_presence_for_body(&func.body) {
        return tp.has_back_edge;
    }
    for block in &func.body.blocks {
        let mut found = false;
        for_each_successor(&block.terminator, |succ| {
            if succ.0 <= block.id.0 {
                found = true;
            }
        });
        if found {
            return true;
        }
    }
    false
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
    if crate::generate::cached_terminator_presence_for_body(&func.body)
        .is_some_and(|tp| !tp.has_back_edge)
    {
        return Vec::new();
    }
    let mut loops = Vec::new();
    let mut dense_blocks: Option<bool> = None;

    for block in &func.body.blocks {
        for_each_successor(&block.terminator, |succ| {
            if succ.0 <= block.id.0 {
                let header = succ;
                let latch = block.id;
                let is_dense = *dense_blocks.get_or_insert_with(|| {
                    func.body.blocks.iter().enumerate().all(|(i, bb)| bb.id.0 == i)
                });

                let cap = latch.0.saturating_sub(header.0).saturating_add(1);
                let mut exit_blocks = Vec::new();
                let body_blocks: Vec<BlockId> = if is_dense {
                    let body_blocks: Vec<BlockId> = (header.0..=latch.0).map(BlockId).collect();
                    if let Some(slice) = func.body.blocks.get(header.0..=latch.0) {
                        for bb in slice {
                            for_each_successor(&bb.terminator, |s| {
                                if (s.0 < header.0 || s.0 > latch.0) && !exit_blocks.contains(&s) {
                                    exit_blocks.push(s);
                                }
                            });
                        }
                    }
                    body_blocks
                } else {
                    let mut body_set: FxHashSet<usize> =
                        FxHashSet::with_capacity_and_hasher(cap, Default::default());
                    let mut body_blocks: Vec<BlockId> = Vec::with_capacity(cap);
                    for bb in &func.body.blocks {
                        if bb.id.0 >= header.0 && bb.id.0 <= latch.0 && body_set.insert(bb.id.0) {
                            body_blocks.push(bb.id);
                        }
                    }
                    // Exit blocks: successors of body blocks that are NOT in the body
                    for &body_id in &body_blocks {
                        if let Some(bb) = func.body.blocks.get(body_id.0) {
                            for_each_successor(&bb.terminator, |s| {
                                if !body_set.contains(&s.0) && !exit_blocks.contains(&s) {
                                    exit_blocks.push(s);
                                }
                            });
                        }
                    }
                    body_blocks
                };

                loops.push(LoopInfo {
                    header,
                    _latch: latch,
                    body_blocks,
                    _exit_blocks: exit_blocks,
                    induction_vars: Vec::new(),
                });
            }
        });
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
/// We also attempt to find the initial value (from assignments before the loop).
#[must_use]
pub(crate) fn find_induction_variables(
    loop_info: &LoopInfo,
    func: &VerifiableFunction,
) -> Vec<InductionVar> {
    let mut vars = Vec::new();

    for &BlockId(body_id) in &loop_info.body_blocks {
        let Some(block) = func.body.blocks.get(body_id) else {
            continue;
        };
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt {
                if !place.projections.is_empty() {
                    continue;
                }
                let local_idx = place.local;
                // Already found this variable?
                if vars.iter().any(|v: &InductionVar| v.local_idx == local_idx) {
                    continue;
                }
                if detect_step(rvalue, local_idx).is_none() {
                    continue;
                }
                let Some(decl) = func.body.locals.get(local_idx) else {
                    continue;
                };
                if !decl.ty.is_integer() {
                    continue;
                }

                let init = find_init_value(func, loop_info, local_idx);
                vars.push(InductionVar { local_idx, init });
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
///
/// A PARAMETER is initialized at ENTRY and `body.blocks` never carries that
/// definition, so a pre-header `p = c` is not what `p` holds on a path that skips it
/// (`if c { i = 0; } while i < n { … }`). The answer here is INLINED as the CHC
/// invariant's INITIAL state (`chc::build_init_args`), so a wrong one narrows the
/// initial state and the invariant can be proved of executions that never happen.
/// Declining leaves `build_init_args`' `init_<name>` fallback — an unconstrained
/// initial value, which only makes the invariant harder to prove.
fn find_init_value(
    func: &VerifiableFunction,
    loop_info: &LoopInfo,
    local_idx: usize,
) -> Option<Formula> {
    if crate::local_defs::is_parameter(func, local_idx) {
        return None;
    }
    crate::find_local_write_stmt(func, &func.body.blocks, local_idx, |block, stmt| {
        // Only look in blocks before the loop header
        if block.id.0 >= loop_info.header.0 {
            return Some(None);
        }
        if let Statement::Assign { place, rvalue, .. } = stmt
            && place.local == local_idx
            && place.projections.is_empty()
            && let Rvalue::Use(op) = rvalue
        {
            return Some(Some(crate::operand_to_formula(func, op)));
        }
        None
    })
    .flatten()
}

/// Visit all successor block IDs from a terminator without allocating a `Vec`.
pub(crate) fn for_each_successor(term: &Terminator, mut f: impl FnMut(BlockId)) {
    match term {
        Terminator::Goto(target)
        | Terminator::Assert { target, .. }
        | Terminator::Drop { target, .. } => f(*target),
        Terminator::SwitchInt { targets, otherwise, .. } => {
            for &(_, t) in targets {
                f(t);
            }
            f(*otherwise);
        }
        Terminator::Return | Terminator::TailCall { .. } | Terminator::Unreachable => {}
        Terminator::Call { target, .. } => {
            if let Some(t) = *target {
                f(t);
            }
        }
        Terminator::Opaque { targets, .. } => {
            for &t in targets {
                f(t);
            }
        }
        _ => {}
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
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
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
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
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
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
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
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
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
        let i_var = ivars.iter().find(|v| v.local_idx == 2);
        assert!(i_var.is_some(), "should detect `i` as induction variable");
        let i_var = i_var.unwrap();
        assert!(
            matches!(&i_var.init, Some(Formula::Int(0))),
            "init should be 0, got: {:?}",
            i_var.init
        );
    }

    #[test]
    fn test_induction_var_descending() {
        let func = countdown_function();
        let loops = detect_loops(&func);
        assert_eq!(loops.len(), 1);

        let ivars = &loops[0].induction_vars;
        // `n` (local 1) is decremented by 1
        assert!(ivars.iter().any(|v| v.local_idx == 1), "should detect `n` as induction variable");
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
            ivars.is_empty() || !ivars.iter().any(|v| v.local_idx == 3),
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
        assert!(ivars.iter().any(|v| v.local_idx == 2), "should find `i` as induction variable");
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
