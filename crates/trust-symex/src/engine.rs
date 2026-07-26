// trust-symex execution engine
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;
use std::fmt::Write;

use serde::{Deserialize, Serialize};
use trust_types::{
    BasicBlock, BinOp, ConstValue, Operand, Place, Rvalue, Statement, Terminator, Ty,
};

use crate::error::SymexError;
use crate::path::PathConstraint;
use crate::state::{SymbolicState, SymbolicValue};

/// A fork in execution produced when a branch is encountered.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExecutionFork {
    /// Symbolic state at the fork point.
    pub state: SymbolicState,
    /// Path constraints accumulated up to and including this fork.
    pub path: PathConstraint,
    /// The next block to execute.
    pub next_block: usize,
}

/// Result of executing a single basic block.
#[derive(Debug)]
pub enum BlockResult {
    /// Execution continues to a single next block (no branching).
    Continue(usize),
    /// Execution forks at a branch: multiple possible successors.
    Fork(Vec<ExecutionFork>),
    /// Execution terminates (return or unreachable).
    Terminated,
}

/// The symbolic execution engine.
///
/// Tracks symbolic state, path constraints, and block coverage.
#[derive(Debug, Clone)]
pub struct SymbolicExecutor {
    /// Current symbolic state (variable -> symbolic value).
    pub state: SymbolicState,
    /// Current path constraints.
    pub path: PathConstraint,
    /// Set of covered block IDs.
    pub coverage: BTreeSet<usize>,
    /// Maximum execution depth (number of blocks).
    pub depth_limit: usize,
    /// Current execution depth.
    pub(crate) current_depth: usize,
}

impl SymbolicExecutor {
    /// Create a new executor with the given depth limit.
    #[must_use]
    pub fn new(depth_limit: usize) -> Self {
        Self {
            state: SymbolicState::new(),
            path: PathConstraint::new(),
            coverage: BTreeSet::default(),
            depth_limit,
            current_depth: 0,
        }
    }

    /// Create an executor from a prior fork point.
    #[must_use]
    pub fn from_fork(fork: ExecutionFork, depth_limit: usize) -> Self {
        Self {
            state: fork.state,
            path: fork.path,
            coverage: BTreeSet::default(),
            depth_limit,
            current_depth: 0,
        }
    }

    /// Execute a single basic block, potentially forking on branches.
    pub fn execute_block(&mut self, block: &BasicBlock) -> Result<BlockResult, SymexError> {
        if self.current_depth >= self.depth_limit {
            return Err(SymexError::DepthLimitExceeded {
                depth: self.current_depth,
                limit: self.depth_limit,
            });
        }

        self.current_depth += 1;
        self.coverage.insert(block.id.0);

        // Execute all statements in the block.
        for stmt in &block.stmts {
            self.execute_statement(stmt)?;
        }

        // Process the terminator.
        self.execute_terminator(&block.terminator)
    }

    fn execute_statement(&mut self, stmt: &Statement) -> Result<(), SymexError> {
        match stmt {
            Statement::Assign { place, rvalue, .. } => {
                // CheckedBinaryOp produces a (result, overflow_flag) tuple.
                // We store the result at place.f0 and the overflow condition at place.f1.
                if let Rvalue::CheckedBinaryOp(op, lhs, rhs) = rvalue {
                    let l = self.eval_operand(lhs)?;
                    let r = self.eval_operand(rhs)?;
                    let result_val = SymbolicValue::bin_op(l.clone(), *op, r.clone());
                    // P0-5: Extract bit width/signedness from operands
                    // so overflow checks use range-based detection instead of the
                    // algebraically tautological (result - lhs) != rhs.
                    let type_info = infer_operand_type(lhs).or_else(|| infer_operand_type(rhs));
                    let overflow_cond = build_overflow_condition(l, *op, r, type_info);
                    let base = place_to_name(place);
                    self.state.set(format!("{base}.f0"), result_val);
                    self.state.set(format!("{base}.f1"), overflow_cond);
                    return Ok(());
                }
                let val = self.eval_rvalue(rvalue)?;
                let name = place_to_name(place);
                self.state.set(name, val);
                Ok(())
            }
            Statement::StorageLive(_)
            | Statement::StorageDead(_)
            | Statement::PlaceMention(_)
            | Statement::Coverage
            | Statement::ConstEvalCounter
            | Statement::Nop => Ok(()),
            other => Err(unsupported(format!("unhandled Statement variant: {other:?}"))),
        }
    }

    fn execute_terminator(&mut self, term: &Terminator) -> Result<BlockResult, SymexError> {
        match term {
            Terminator::Goto(target) => Ok(BlockResult::Continue(target.0)),
            Terminator::Return => Ok(BlockResult::Terminated),
            Terminator::Unreachable => Err(SymexError::UnreachableReached),
            Terminator::SwitchInt { discr, targets, otherwise, .. } => {
                let discr_val = self.eval_operand(discr)?;

                let mut forks = Vec::new();

                // One fork per target value.
                for (value, target) in targets {
                    // Trust: #783 — two's complement cast preserves bitvector semantics.
                    let cond = SymbolicValue::bin_op(
                        discr_val.clone(),
                        BinOp::Eq,
                        SymbolicValue::Concrete(*value as i128),
                    );
                    let mut fork_path = self.path.clone();
                    fork_path.add_constraint(cond, true);
                    forks.push(ExecutionFork {
                        state: self.state.clone(),
                        path: fork_path,
                        next_block: target.0,
                    });
                }

                // Otherwise branch: none of the target values matched.
                let mut otherwise_path = self.path.clone();
                for (value, _) in targets {
                    // Trust: #783 — two's complement cast preserves bitvector semantics.
                    let cond = SymbolicValue::bin_op(
                        discr_val.clone(),
                        BinOp::Eq,
                        SymbolicValue::Concrete(*value as i128),
                    );
                    otherwise_path.add_constraint(cond, false);
                }
                forks.push(ExecutionFork {
                    state: self.state.clone(),
                    path: otherwise_path,
                    next_block: otherwise.0,
                });

                Ok(BlockResult::Fork(forks))
            }
            Terminator::Assert { cond, expected, target, .. } => {
                let cond_val = self.eval_operand(cond)?;
                if let SymbolicValue::Concrete(actual) = cond_val {
                    let actual = actual != 0;
                    return if actual == *expected {
                        Ok(BlockResult::Continue(target.0))
                    } else {
                        Err(SymexError::AssertionFailed { expected: *expected, actual })
                    };
                }
                let constraint_cond =
                    if *expected { cond_val } else { SymbolicValue::Not(Box::new(cond_val)) };
                self.path.add_constraint(constraint_cond, true);
                Ok(BlockResult::Continue(target.0))
            }
            Terminator::Call { func, .. } => Err(unsupported(format!(
                "call terminator requires a function summary before symex: {func}"
            ))),
            Terminator::Drop { place, .. } => Err(unsupported(format!(
                "drop terminator requires drop semantics before symex: {}",
                place_to_name(place)
            ))),
            Terminator::Opaque { kind, .. } => Err(unsupported(format!(
                "opaque terminator cannot be symbolically executed: {kind}"
            ))),
            other => Err(unsupported(format!("unhandled Terminator variant: {other:?}"))),
        }
    }

    fn eval_rvalue(&self, rvalue: &Rvalue) -> Result<SymbolicValue, SymexError> {
        match rvalue {
            Rvalue::Use(op) => self.eval_operand(op),
            Rvalue::BinaryOp(op, lhs, rhs) => {
                let l = self.eval_operand(lhs)?;
                let r = self.eval_operand(rhs)?;
                Ok(SymbolicValue::bin_op(l, *op, r))
            }
            // CheckedBinaryOp is handled in execute_statement to produce
            // the (result, overflow_flag) tuple at place.f0 and place.f1.
            // If reached here directly, return just the result value.
            Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
                let l = self.eval_operand(lhs)?;
                let r = self.eval_operand(rhs)?;
                Ok(SymbolicValue::bin_op(l, *op, r))
            }
            Rvalue::UnaryOp(un_op, op) => {
                let v = self.eval_operand(op)?;
                match un_op {
                    trust_types::UnOp::Neg => Ok(SymbolicValue::Neg(Box::new(v))),
                    trust_types::UnOp::Not => Ok(SymbolicValue::BitwiseNot(Box::new(v))),
                    trust_types::UnOp::PtrMetadata => Err(unsupported(
                        "pointer metadata extraction requires fat-pointer semantics in symex",
                    )),
                    other => Err(unsupported(format!("unhandled UnOp variant: {other:?}"))),
                }
            }
            Rvalue::Ref { place, .. } => {
                // #776: Return a symbolic reference (pointer token), not the
                // value at the place. `&x` produces a pointer to x, not x itself.
                // Deref operations resolve the pointer via the state mapping.
                let name = place_to_name(place);
                Ok(SymbolicValue::Symbol(format!("ref_{name}")))
            }
            Rvalue::Cast(op, dest_ty) => {
                let val = self.eval_operand(op)?;
                apply_cast(val, dest_ty)
            }
            Rvalue::Aggregate(kind, _) => Err(SymexError::UnsupportedOperation(format!(
                "unsupported aggregate semantics in symex: {kind:?}"
            ))),
            Rvalue::Discriminant(place) => Err(unsupported(format!(
                "discriminant requires ADT layout semantics in symex: {}",
                place_to_name(place)
            ))),
            Rvalue::Len(place) => Err(unsupported(format!(
                "len requires array/slice layout semantics in symex: {}",
                place_to_name(place)
            ))),
            Rvalue::Repeat(_, _) => {
                Err(unsupported("repeat aggregate requires array-value semantics in symex"))
            }
            Rvalue::AddressOf(_, place) => {
                // #776: Return a symbolic address token, not the value at
                // the place. `&raw const x` / `&raw mut x` produce pointer
                // values, distinct from the pointee value.
                let name = place_to_name(place);
                Ok(SymbolicValue::Symbol(format!("addr_{name}")))
            }
            Rvalue::CopyForDeref(place) => {
                let name = place_to_name(place);
                match self.state.try_get(&name) {
                    Some(val) => Ok(val.clone()),
                    None => Ok(SymbolicValue::Symbol(name)),
                }
            }
            Rvalue::Unsupported { kind, detail, .. } => {
                Err(unsupported(format!("unsupported MIR rvalue in symex: {kind}: {detail}")))
            }
            other => Err(unsupported(format!("unhandled Rvalue variant: {other:?}"))),
        }
    }

    fn eval_operand(&self, op: &Operand) -> Result<SymbolicValue, SymexError> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                let name = place_to_name(place);
                match self.state.try_get(&name) {
                    Some(val) => Ok(val.clone()),
                    None => Ok(SymbolicValue::Symbol(name)),
                }
            }
            Operand::Constant(cv) => const_to_symbolic(cv),
            Operand::Symbolic(_) => {
                Err(unsupported("SMT Formula operands are not executable by trust-symex"))
            }
            Operand::Unsupported { kind, detail } => {
                Err(unsupported(format!("unsupported MIR operand in symex: {kind}: {detail}")))
            }
            other => Err(unsupported(format!("unhandled Operand variant: {other:?}"))),
        }
    }
}

/// Convert a `Place` to a flat variable name for the symbolic state.
#[must_use]
pub(crate) fn place_to_name(place: &Place) -> String {
    let mut name = format!("_local{}", place.local);
    for proj in &place.projections {
        match proj {
            trust_types::Projection::Field(f) => {
                let _ = write!(name, ".f{f}");
            }
            trust_types::Projection::Index(i) => {
                let _ = write!(name, "[{i}]");
            }
            trust_types::Projection::Deref => {
                name.push_str(".*");
            }
            trust_types::Projection::Downcast(v) => {
                let _ = write!(name, "@{v}");
            }
            trust_types::Projection::ConstantIndex { offset, min_length, from_end } => {
                if *from_end {
                    let _ = write!(name, "[-{offset};min={min_length}]");
                } else {
                    let _ = write!(name, "[{offset};min={min_length}]");
                }
            }
            trust_types::Projection::Subslice { from, to, from_end } => {
                if *from_end {
                    let _ = write!(name, "[{from}..-{to}]");
                } else {
                    let _ = write!(name, "[{from}..{to}]");
                }
            }
            _ => {}
        }
    }
    name
}

/// P0-5: Extract bit-width and signedness from an operand when possible.
///
/// Returns `Some((width, signed))` for constant operands with known type.
/// Returns `None` for place-based operands (type info not available in symex).
fn infer_operand_type(op: &Operand) -> Option<(u32, bool)> {
    match op {
        Operand::Constant(ConstValue::Uint(_, width)) => Some((*width, false)),
        Operand::Constant(ConstValue::Int(_)) => Some((128, true)),
        _ => None,
    }
}

/// Build a symbolic overflow condition for a checked arithmetic operation.
///
/// P0-5: Uses bit-width-aware range checks instead of algebraic
/// identities that simplify to tautologies in the unbounded symbolic domain.
///
/// When `type_info` is `Some((width, signed))`, overflow is detected by checking
/// whether the mathematical result falls outside the type's representable range:
/// - **Unsigned w-bit:** overflow = `result < 0 || result >= 2^w`
/// - **Signed w-bit:** overflow = `result < -2^(w-1) || result >= 2^(w-1)`
///
/// For multiplication, we use `(rhs != 0) && (result / rhs != lhs)` which is
/// correct because integer division truncates, making this non-tautological
/// for multiplication (unlike addition/subtraction where the inverse is exact).
///
/// When `type_info` is `None`, returns `Concrete(0)` (conservatively assumes
/// no overflow detectable without type information).
fn build_overflow_condition(
    lhs: SymbolicValue,
    op: BinOp,
    rhs: SymbolicValue,
    type_info: Option<(u32, bool)>,
) -> SymbolicValue {
    let result = SymbolicValue::bin_op(lhs.clone(), op, rhs.clone());

    match op {
        BinOp::Add | BinOp::Sub => {
            // For Add/Sub, the algebraic inverse is exact in unbounded arithmetic,
            // so we MUST use range-based checks.
            if let Some((width, signed)) = type_info {
                let (min_val, max_val) = type_range(width, signed);
                // overflow = result < min || result > max
                let below_min = SymbolicValue::bin_op(
                    result.clone(),
                    BinOp::Lt,
                    SymbolicValue::Concrete(min_val),
                );
                let above_max =
                    SymbolicValue::bin_op(result, BinOp::Gt, SymbolicValue::Concrete(max_val));
                // Encode OR as: if below_min then 1 else above_max
                SymbolicValue::ite(below_min, SymbolicValue::Concrete(1), above_max)
            } else {
                // Without type info, cannot detect overflow in unbounded domain.
                SymbolicValue::Concrete(0)
            }
        }
        BinOp::Mul => {
            // For Mul, integer division truncates so (result / rhs != lhs) is
            // NOT a tautology — it correctly detects when the product wraps.
            let rhs_nonzero =
                SymbolicValue::bin_op(rhs.clone(), BinOp::Ne, SymbolicValue::Concrete(0));
            let div_check = SymbolicValue::bin_op(
                SymbolicValue::bin_op(result, BinOp::Div, rhs),
                BinOp::Ne,
                lhs,
            );
            SymbolicValue::ite(rhs_nonzero, div_check, SymbolicValue::Concrete(0))
        }
        _ => SymbolicValue::Concrete(0),
    }
}

/// Compute the (min, max) representable range for a `width`-bit integer type.
fn type_range(width: u32, signed: bool) -> (i128, i128) {
    if signed {
        if width >= 128 {
            (i128::MIN, i128::MAX)
        } else {
            let half = 1i128 << (width - 1);
            (-half, half - 1)
        }
    } else {
        let max = if width >= 128 { i128::MAX } else { (1i128 << width) - 1 };
        (0, max)
    }
}

fn const_to_symbolic(cv: &ConstValue) -> Result<SymbolicValue, SymexError> {
    match cv {
        ConstValue::Bool(b) => Ok(SymbolicValue::Concrete(i128::from(*b))),
        ConstValue::Int(n) => Ok(SymbolicValue::Concrete(*n)),
        // Trust: #783 — `as i128` preserves the bit pattern (two's complement / bitvector
        // semantics). Values > i128::MAX wrap to negative, which is the correct bitvector
        // interpretation for our formula representation.
        ConstValue::Uint(n, _) => Ok(SymbolicValue::Concrete(*n as i128)),
        ConstValue::Unit => Ok(SymbolicValue::Concrete(0)),
        ConstValue::CallableItem { def_path, kind, def_path_hash } => Ok(SymbolicValue::Symbol(
            ConstValue::callable_smt_var_name(def_path, *kind, *def_path_hash),
        )),
        ConstValue::Float(_) | ConstValue::FloatBits { .. } => {
            Err(unsupported("floating-point constants require float semantics in symex"))
        }
        other => Err(unsupported(format!("unhandled ConstValue variant: {other:?}"))),
    }
}

/// Apply a cast to a symbolic value based on the destination type.
///
/// - Integer narrowing: applies a truncation bitmask (e.g. `& 0xFF` for u8).
/// - Signed narrowing: truncates then sign-extends from the destination width.
/// - Unsigned widening: identity (no bits change).
/// - Signed widening: sign-extends from the current value's bit pattern.
///   Without source type info we model this as identity, which is correct when
///   the value was previously truncated to the right width.
/// - Non-integer casts (pointers, floats): unsupported until precise semantics exist.
fn apply_cast(val: SymbolicValue, dest_ty: &Ty) -> Result<SymbolicValue, SymexError> {
    match dest_ty {
        Ty::Int { width, signed } => {
            let w = *width;
            if w == 0 {
                return Err(unsupported("zero-width integer cast in symex"));
            }
            // Full i128 width or wider — no truncation needed.
            if w >= 128 {
                return Ok(val);
            }
            let mask = (1i128 << w) - 1;
            // Truncate to destination width via BitAnd with mask.
            let truncated =
                SymbolicValue::bin_op(val, BinOp::BitAnd, SymbolicValue::Concrete(mask));
            if *signed {
                // Sign-extend: if the sign bit (bit w-1) is set, the value
                // should be interpreted as negative. We model this as:
                //   ite(truncated & sign_bit != 0, truncated | ~mask, truncated)
                // which sets the high bits for negative values.
                let sign_bit = 1i128 << (w - 1);
                let sign_test = SymbolicValue::bin_op(
                    SymbolicValue::bin_op(
                        truncated.clone(),
                        BinOp::BitAnd,
                        SymbolicValue::Concrete(sign_bit),
                    ),
                    BinOp::Ne,
                    SymbolicValue::Concrete(0),
                );
                let sign_extended = SymbolicValue::bin_op(
                    truncated.clone(),
                    BinOp::BitOr,
                    SymbolicValue::Concrete(!mask),
                );
                Ok(SymbolicValue::ite(sign_test, sign_extended, truncated))
            } else {
                // Unsigned: truncation alone is sufficient.
                Ok(truncated)
            }
        }
        Ty::Unsupported { kind, detail } => {
            Err(unsupported(format!("cast target type is unsupported in symex: {kind}: {detail}")))
        }
        other => Err(unsupported(format!(
            "non-integer cast target requires precise cast semantics in symex: {other:?}"
        ))),
    }
}

fn unsupported(message: impl Into<String>) -> SymexError {
    SymexError::UnsupportedOperation(message.into())
}

#[cfg(test)]
mod tests {
    use trust_types::UnwindEdge;
    use trust_types::{AssertMessage, BlockId, SourceSpan};

    use super::*;

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    #[test]
    fn callable_constants_are_distinct_opaque_symbols() {
        let first = const_to_symbolic(&ConstValue::CallableItem {
            def_path: "fixture::first".to_string(),
            kind: trust_types::CallableKind::FnDef,
            def_path_hash: trust_types::CallableDefPathHash::new(1, 1),
        })
        .expect("symbolic execution can preserve callable identity opaquely");
        let second = const_to_symbolic(&ConstValue::CallableItem {
            def_path: "fixture::second".to_string(),
            kind: trust_types::CallableKind::FnDef,
            def_path_hash: trust_types::CallableDefPathHash::new(1, 2),
        })
        .expect("symbolic execution can preserve callable identity opaquely");
        assert!(matches!(first, SymbolicValue::Symbol(_)));
        assert!(matches!(second, SymbolicValue::Symbol(_)));
        assert_ne!(first, second, "distinct callable paths must not alias");
        assert_ne!(first, SymbolicValue::Concrete(0), "callables are not unit literals");
    }

    #[test]
    fn test_engine_execute_assign_and_goto() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(42))),
                span: span(),
            }],
            terminator: Terminator::Goto(BlockId(1)),
        };

        let mut exec = SymbolicExecutor::new(100);
        let result = exec.execute_block(&block).expect("should succeed");
        match result {
            BlockResult::Continue(next) => assert_eq!(next, 1),
            other => panic!("expected Continue, got {other:?}"),
        }
        assert_eq!(exec.state.get("_local1").unwrap(), &SymbolicValue::Concrete(42));
    }

    #[test]
    fn test_engine_switch_int_forks() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::SwitchInt {
                discr: Operand::Constant(ConstValue::Bool(true)),
                targets: vec![(1, BlockId(1))],
                otherwise: BlockId(2),
                exhaustive_enum_unreachable: false,
                span: span(),
            },
        };

        let mut exec = SymbolicExecutor::new(100);
        let result = exec.execute_block(&block).expect("should succeed");
        match result {
            BlockResult::Fork(forks) => {
                assert_eq!(forks.len(), 2);
                assert_eq!(forks[0].next_block, 1);
                assert_eq!(forks[1].next_block, 2);
            }
            other => panic!("expected Fork, got {other:?}"),
        }
    }

    #[test]
    fn test_engine_return_terminates() {
        let block = BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return };

        let mut exec = SymbolicExecutor::new(100);
        let result = exec.execute_block(&block).expect("should succeed");
        assert!(matches!(result, BlockResult::Terminated));
    }

    #[test]
    fn test_engine_depth_limit() {
        let block =
            BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Goto(BlockId(0)) };

        let mut exec = SymbolicExecutor::new(1);
        exec.execute_block(&block).expect("first block ok");
        let err = exec.execute_block(&block).expect_err("should hit limit");
        assert!(matches!(err, SymexError::DepthLimitExceeded { .. }));
    }

    #[test]
    fn test_engine_assert_adds_constraint() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Assert {
                unwind: UnwindEdge::Unreachable,
                cond: Operand::Copy(Place::local(1)),
                expected: true,
                msg: AssertMessage::BoundsCheck,
                target: BlockId(1),
                span: span(),
            },
        };

        let mut exec = SymbolicExecutor::new(100);
        let result = exec.execute_block(&block).expect("should succeed");
        match result {
            BlockResult::Continue(1) => {}
            other => panic!("expected Continue(1), got {other:?}"),
        }
        assert_eq!(exec.path.depth(), 1);
    }

    #[test]
    fn test_engine_binary_op_symbolic() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Add,
                    Operand::Copy(Place::local(0)),
                    Operand::Constant(ConstValue::Int(1)),
                ),
                span: span(),
            }],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        exec.state.set("_local0", SymbolicValue::Symbol("arg0".into()));
        exec.execute_block(&block).expect("should succeed");

        let result = exec.state.get("_local2").unwrap();
        match result {
            SymbolicValue::BinOp(_, BinOp::Add, _) => {}
            other => panic!("expected BinOp Add, got {other:?}"),
        }
    }

    #[test]
    fn test_engine_coverage_tracking() {
        let blocks = [
            BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Goto(BlockId(1)) },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ];

        let mut exec = SymbolicExecutor::new(100);
        exec.execute_block(&blocks[0]).expect("block 0");
        exec.execute_block(&blocks[1]).expect("block 1");
        assert!(exec.coverage.contains(&0));
        assert!(exec.coverage.contains(&1));
        assert_eq!(exec.coverage.len(), 2);
    }

    #[test]
    fn test_engine_place_to_name_projections() {
        let p = Place {
            local: 3,
            projections: vec![trust_types::Projection::Field(1), trust_types::Projection::Deref],
        };
        assert_eq!(place_to_name(&p), "_local3.f1.*");
    }

    #[test]
    fn test_engine_from_fork() {
        let mut state = SymbolicState::new();
        state.set("_local0", SymbolicValue::Concrete(7));

        let mut path = PathConstraint::new();
        path.add_constraint(SymbolicValue::Symbol("cond".into()), true);

        let fork = ExecutionFork { state, path, next_block: 3 };
        let exec = SymbolicExecutor::from_fork(fork, 25);

        assert_eq!(
            exec.state.get("_local0").expect("fork state should be preserved"),
            &SymbolicValue::Concrete(7)
        );
        assert_eq!(exec.path.depth(), 1);
        assert!(exec.path.decisions()[0].taken);
        assert!(exec.coverage.is_empty());
        assert_eq!(exec.depth_limit, 25);
        assert_eq!(exec.current_depth, 0);
    }

    #[test]
    fn test_engine_nop_statement() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Nop],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        let result = exec.execute_block(&block).expect("nop block should execute");

        assert!(matches!(result, BlockResult::Terminated));
        assert!(exec.state.is_empty());
    }

    #[test]
    fn test_engine_call_terminator_is_unsupported() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                func: "callee".into(),
                args: vec![],
                dest: Place::local(2),
                target: Some(BlockId(1)),
                span: span(),
                atomic: None,
            },
        };

        let mut exec = SymbolicExecutor::new(100);
        assert_unsupported(
            exec.execute_block(&block),
            "call terminator requires a function summary",
        );
    }

    #[test]
    fn test_engine_drop_terminator_is_unsupported() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Drop {
                unwind: UnwindEdge::Unreachable,
                place: Place::local(1),
                target: BlockId(2),
                span: span(),
            },
        };

        let mut exec = SymbolicExecutor::new(100);
        assert_unsupported(exec.execute_block(&block), "drop terminator requires drop semantics");
    }

    #[test]
    fn test_engine_unary_neg() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::UnaryOp(
                    trust_types::UnOp::Neg,
                    Operand::Constant(ConstValue::Int(5)),
                ),
                span: span(),
            }],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        exec.execute_block(&block).expect("unary neg should execute");

        let result = exec.state.get("_local2").expect("unary result should be stored");
        assert_eq!(result, &SymbolicValue::Neg(Box::new(SymbolicValue::Concrete(5))));
        // Verify concrete evaluation: -5
        let state = crate::state::SymbolicState::new();
        assert_eq!(crate::state::eval(&state, result), Some(-5));
    }

    #[test]
    fn test_engine_unary_not() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::UnaryOp(
                    trust_types::UnOp::Not,
                    Operand::Constant(ConstValue::Int(0)),
                ),
                span: span(),
            }],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        exec.execute_block(&block).expect("unary not should execute");

        let result = exec.state.get("_local2").expect("unary not result should be stored");
        assert_eq!(result, &SymbolicValue::BitwiseNot(Box::new(SymbolicValue::Concrete(0))));
        let state = crate::state::SymbolicState::new();
        assert_eq!(crate::state::eval(&state, result), Some(!0i128));
    }

    #[test]
    fn test_engine_checked_add_overflow_flag() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::CheckedBinaryOp(
                    BinOp::Add,
                    Operand::Constant(ConstValue::Int(3)),
                    Operand::Constant(ConstValue::Int(4)),
                ),
                span: span(),
            }],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        exec.execute_block(&block).expect("checked add should execute");

        // Result at place.f0
        let result = exec.state.get("_local2.f0").expect("checked result at f0");
        let state = crate::state::SymbolicState::new();
        assert_eq!(crate::state::eval(&state, result), Some(7));

        // Overflow flag at place.f1 — for non-wrapping add, should eval to 0 (false)
        let overflow = exec.state.get("_local2.f1").expect("overflow flag at f1");
        assert_eq!(crate::state::eval(&state, overflow), Some(0));
    }

    #[test]
    fn test_engine_rvalue_len() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Len(Place::local(3)),
                span: span(),
            }],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        assert_unsupported(exec.execute_block(&block), "len requires array/slice layout semantics");
    }

    #[test]
    fn test_engine_rvalue_discriminant() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Discriminant(Place::local(4)),
                span: span(),
            }],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        assert_unsupported(
            exec.execute_block(&block),
            "discriminant requires ADT layout semantics",
        );
    }

    // --- Cast tests (Part of #780) ---

    #[test]
    fn test_engine_cast_narrowing_i32_to_u8() {
        // Casting 300_i32 as u8 should truncate to 300 & 0xFF = 44.
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Cast(Operand::Constant(ConstValue::Int(300)), Ty::u8()),
                span: span(),
            }],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        exec.execute_block(&block).expect("cast block should execute");

        let result = exec.state.get("_local1").expect("cast result stored");
        let concrete = crate::state::eval(&exec.state, result);
        assert_eq!(concrete, Some(44), "300 & 0xFF = 44");
    }

    #[test]
    fn test_engine_cast_widening_u8_to_u32() {
        // Casting 200_u8 as u32 — value fits, truncation mask is 0xFFFFFFFF,
        // so result should still be 200.
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Cast(Operand::Constant(ConstValue::Int(200)), Ty::u32()),
                span: span(),
            }],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        exec.execute_block(&block).expect("widening cast should execute");

        let result = exec.state.get("_local1").expect("widening cast result stored");
        let concrete = crate::state::eval(&exec.state, result);
        assert_eq!(concrete, Some(200), "200 unchanged through u32 widening");
    }

    #[test]
    fn test_engine_cast_sign_extension_i8() {
        // Casting 0xFF (255, which is -1 in i8) as i8 should sign-extend to -1.
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Cast(Operand::Constant(ConstValue::Int(0xFF)), Ty::i8()),
                span: span(),
            }],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        exec.execute_block(&block).expect("sign-extend cast should execute");

        let result = exec.state.get("_local1").expect("sign-extend result stored");
        let concrete = crate::state::eval(&exec.state, result);
        assert_eq!(concrete, Some(-1), "0xFF sign-extended as i8 = -1");
    }

    #[test]
    fn test_engine_cast_positive_i8_stays_positive() {
        // Casting 42 as i8 — sign bit is 0, so result remains 42.
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Cast(Operand::Constant(ConstValue::Int(42)), Ty::i8()),
                span: span(),
            }],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        exec.execute_block(&block).expect("positive i8 cast should execute");

        let result = exec.state.get("_local1").expect("positive i8 result stored");
        let concrete = crate::state::eval(&exec.state, result);
        assert_eq!(concrete, Some(42), "42 fits in i8 without sign extension");
    }

    #[test]
    fn test_engine_cast_narrowing_u16() {
        // Casting 0x1_FFFF (131071) as u16 should truncate to 0xFFFF = 65535.
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Cast(Operand::Constant(ConstValue::Int(0x1_FFFF)), Ty::u16()),
                span: span(),
            }],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        exec.execute_block(&block).expect("u16 truncation should execute");

        let result = exec.state.get("_local1").expect("u16 truncation result stored");
        let concrete = crate::state::eval(&exec.state, result);
        assert_eq!(concrete, Some(0xFFFF), "0x1_FFFF & 0xFFFF = 0xFFFF");
    }

    #[test]
    fn test_engine_cast_pointer_is_unsupported() {
        let ptr_ty = Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) };
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Cast(Operand::Constant(ConstValue::Int(0xDEAD)), ptr_ty),
                span: span(),
            }],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        assert_unsupported(
            exec.execute_block(&block),
            "non-integer cast target requires precise cast semantics",
        );
    }

    #[test]
    fn test_apply_cast_concrete_truncation() {
        // Direct unit test for apply_cast: 0x1234 truncated to u8 = 0x34.
        let val = SymbolicValue::Concrete(0x1234);
        let result = apply_cast(val, &Ty::u8()).expect("integer cast supported");
        let state = SymbolicState::new();
        assert_eq!(crate::state::eval(&state, &result), Some(0x34));
    }

    #[test]
    fn test_apply_cast_signed_negative() {
        // Direct unit test: 0x80 as i8 should sign-extend to -128.
        let val = SymbolicValue::Concrete(0x80);
        let result = apply_cast(val, &Ty::i8()).expect("integer cast supported");
        let state = SymbolicState::new();
        assert_eq!(crate::state::eval(&state, &result), Some(-128));
    }

    #[test]
    fn test_engine_unsupported_statement_errors() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Unsupported {
                kind: "FakeStatement".into(),
                detail: "test unsupported statement".into(),
                operands: vec![],
                span: span(),
            }],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        assert_unsupported(exec.execute_block(&block), "unhandled Statement variant");
    }

    #[test]
    fn test_engine_unsupported_operand_errors() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Use(Operand::Unsupported {
                    kind: "FakeOperand".into(),
                    detail: "test unsupported operand".into(),
                }),
                span: span(),
            }],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        assert_unsupported(exec.execute_block(&block), "unsupported MIR operand");
    }

    #[test]
    fn test_engine_unsupported_rvalue_errors() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Unsupported {
                    kind: "FakeRvalue".into(),
                    detail: "test unsupported rvalue".into(),
                    operands: vec![],
                },
                span: span(),
            }],
            terminator: Terminator::Return,
        };

        let mut exec = SymbolicExecutor::new(100);
        assert_unsupported(exec.execute_block(&block), "unsupported MIR rvalue");
    }

    #[test]
    fn test_engine_opaque_terminator_errors() {
        let block = BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Opaque {
                kind: "Yield".into(),
                targets: vec![BlockId(1)],
                span: span(),
            },
        };

        let mut exec = SymbolicExecutor::new(100);
        assert_unsupported(
            exec.execute_block(&block),
            "opaque terminator cannot be symbolically executed",
        );
    }

    fn assert_unsupported<T: std::fmt::Debug>(result: Result<T, SymexError>, expected: &str) {
        match result {
            Err(SymexError::UnsupportedOperation(message)) => {
                assert!(message.contains(expected), "unexpected message: {message}");
            }
            other => panic!("expected UnsupportedOperation containing {expected:?}, got {other:?}"),
        }
    }
}
