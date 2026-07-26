// trust-symex concrete executor
//
// Execute MIR statements concretely while tracking which values are symbolic.
// When a symbolic value affects control flow, record the branch point for
// the concolic engine to explore alternative paths.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use trust_types::{BasicBlock, BinOp, BlockId, ConstValue, Operand, Rvalue, Terminator, Ty};

use crate::engine::place_to_name;
use crate::error::SymexError;
use crate::path::PathConstraint;
use crate::state::SymbolicValue;

/// A concrete value paired with its symbolic shadow.
///
/// During concolic execution every value has both a concrete component
/// (used to drive execution deterministically) and a symbolic component
/// (used to build path constraints for the solver).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConcolicValue {
    /// The concrete integer value used for execution.
    pub concrete: i128,
    /// The symbolic expression shadowing this value. `None` when the value
    /// is purely concrete (no input dependency).
    pub symbolic: Option<SymbolicValue>,
}

impl ConcolicValue {
    /// Create a purely concrete value with no symbolic shadow.
    #[must_use]
    pub(crate) fn concrete(value: i128) -> Self {
        Self { concrete: value, symbolic: None }
    }

    /// Create a concolic value with both concrete and symbolic components.
    #[must_use]
    pub(crate) fn with_shadow(concrete: i128, symbolic: SymbolicValue) -> Self {
        Self { concrete, symbolic: Some(symbolic) }
    }

    /// Returns `true` if this value has a symbolic shadow.
    #[must_use]
    pub(crate) fn is_symbolic(&self) -> bool {
        self.symbolic.is_some()
    }

    /// Get the symbolic expression, falling back to a concrete literal.
    #[must_use]
    pub(crate) fn to_symbolic(&self) -> SymbolicValue {
        self.symbolic.clone().unwrap_or(SymbolicValue::Concrete(self.concrete))
    }
}

/// A branch point detected during concrete execution where a symbolic
/// value influenced control flow.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct SymbolicBranchPoint {
    /// The block in which the branch occurs.
    pub block_id: usize,
    /// The symbolic condition at the branch.
    pub condition: SymbolicValue,
    /// The direction taken during concrete execution.
    pub taken: bool,
    /// Index of this decision within the path.
    pub decision_index: usize,
}

/// The concrete executor: runs MIR blocks using concrete values while
/// maintaining symbolic shadows for constraint collection.
#[derive(Debug, Clone)]
pub(crate) struct ConcreteExecutor {
    /// Mapping from variable names to concolic values.
    vars: BTreeMap<String, ConcolicValue>,
    /// Path constraints accumulated during execution.
    pub(crate) path: PathConstraint,
    /// Branch points where symbolic values affected control flow.
    pub(crate) symbolic_branches: Vec<SymbolicBranchPoint>,
    /// Maximum number of blocks to execute before aborting.
    pub(crate) step_limit: usize,
    /// Current step count.
    pub(crate) steps: usize,
}

impl ConcreteExecutor {
    /// Create a new concrete executor.
    #[must_use]
    pub(crate) fn new(step_limit: usize) -> Self {
        Self {
            vars: BTreeMap::default(),
            path: PathConstraint::new(),
            symbolic_branches: Vec::new(),
            step_limit,
            steps: 0,
        }
    }

    /// Bind a variable to a concolic value.
    pub(crate) fn set_input(&mut self, name: impl Into<String>, value: ConcolicValue) {
        self.vars.insert(name.into(), value);
    }

    /// Get the concolic value of a variable.
    pub(crate) fn get(&self, name: &str) -> Result<ConcolicValue, SymexError> {
        self.vars.get(name).cloned().ok_or_else(|| SymexError::UndefinedVariable(name.to_owned()))
    }

    /// Execute a single basic block concretely.
    ///
    /// Returns the ID of the next block to execute, or `None` if the block
    /// terminates (return / unreachable).
    pub(crate) fn execute_block(
        &mut self,
        block: &BasicBlock,
    ) -> Result<Option<usize>, SymexError> {
        if self.steps >= self.step_limit {
            return Err(SymexError::DepthLimitExceeded {
                depth: self.steps,
                limit: self.step_limit,
            });
        }
        self.steps += 1;

        // Execute statements.
        for stmt in &block.stmts {
            self.execute_statement(stmt)?;
        }

        // Process terminator.
        self.execute_terminator(block.id, &block.terminator)
    }

    fn execute_statement(&mut self, stmt: &trust_types::Statement) -> Result<(), SymexError> {
        match stmt {
            trust_types::Statement::Assign { place, rvalue, .. } => {
                let val = self.eval_rvalue(rvalue)?;
                let name = place_to_name(place);
                self.vars.insert(name, val);
                Ok(())
            }
            trust_types::Statement::Nop => Ok(()),
            other => Err(SymexError::UnsupportedOperation(format!(
                "unhandled Statement variant: {other:?}"
            ))),
        }
    }

    fn execute_terminator(
        &mut self,
        block_id: BlockId,
        term: &Terminator,
    ) -> Result<Option<usize>, SymexError> {
        match term {
            Terminator::Goto(target) => Ok(Some(target.0)),
            Terminator::Return => Ok(None),
            Terminator::Unreachable => Err(SymexError::UnreachableReached),
            Terminator::SwitchInt { discr, targets, otherwise, .. } => {
                let discr_val = self.eval_operand(discr)?;
                let concrete_discr = discr_val.concrete;

                // Record symbolic branch if the discriminant has a symbolic shadow.
                if discr_val.is_symbolic() {
                    // Record constraints for each target comparison.
                    let mut matched_target = None;
                    for (value, target) in targets {
                        let cond = SymbolicValue::bin_op(
                            discr_val.to_symbolic(),
                            BinOp::Eq,
                            SymbolicValue::Concrete(*value as i128),
                        );
                        let taken = concrete_discr == *value as i128;
                        let decision_index = self.symbolic_branches.len();
                        self.symbolic_branches.push(SymbolicBranchPoint {
                            block_id: block_id.0,
                            condition: cond.clone(),
                            taken,
                            decision_index,
                        });
                        self.path.add_constraint(cond, taken);
                        if taken {
                            matched_target = Some(target.0);
                        }
                    }
                    return Ok(Some(matched_target.unwrap_or(otherwise.0)));
                }

                // Pure concrete dispatch.
                for (value, target) in targets {
                    if concrete_discr == *value as i128 {
                        return Ok(Some(target.0));
                    }
                }
                Ok(Some(otherwise.0))
            }
            Terminator::Assert { cond, expected, target, .. } => {
                let cond_val = self.eval_operand(cond)?;
                let actual = cond_val.concrete != 0;
                if actual != *expected {
                    return Err(SymexError::AssertionFailed { expected: *expected, actual });
                }
                if cond_val.is_symbolic() {
                    let sym_cond = if *expected {
                        cond_val.to_symbolic()
                    } else {
                        SymbolicValue::Not(Box::new(cond_val.to_symbolic()))
                    };
                    self.path.add_constraint(sym_cond, true);
                }
                Ok(Some(target.0))
            }
            Terminator::Call { func, .. } => Err(unsupported(format!(
                "call terminator requires a function summary before concrete symex: {func}"
            ))),
            Terminator::Drop { place, .. } => Err(unsupported(format!(
                "drop terminator requires drop semantics before concrete symex: {}",
                place_to_name(place)
            ))),
            Terminator::Opaque { kind, .. } => {
                Err(unsupported(format!("opaque terminator cannot be concretely executed: {kind}")))
            }
            other => Err(SymexError::UnsupportedOperation(format!(
                "unhandled Terminator variant: {other:?}"
            ))),
        }
    }

    fn eval_rvalue(&self, rvalue: &Rvalue) -> Result<ConcolicValue, SymexError> {
        match rvalue {
            Rvalue::Use(op) => self.eval_operand(op),
            Rvalue::BinaryOp(op, lhs, rhs) | Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
                let l = self.eval_operand(lhs)?;
                let r = self.eval_operand(rhs)?;
                let concrete = eval_concrete_binop(l.concrete, *op, r.concrete)?;
                let symbolic = if l.is_symbolic() || r.is_symbolic() {
                    Some(SymbolicValue::bin_op(l.to_symbolic(), *op, r.to_symbolic()))
                } else {
                    None
                };
                Ok(ConcolicValue { concrete, symbolic })
            }
            Rvalue::UnaryOp(un_op, op) => {
                let v = self.eval_operand(op)?;
                match un_op {
                    trust_types::UnOp::Neg => {
                        let concrete = -v.concrete;
                        let symbolic = v.symbolic.map(|s| SymbolicValue::Neg(Box::new(s)));
                        Ok(ConcolicValue { concrete, symbolic })
                    }
                    trust_types::UnOp::Not => {
                        let concrete = !v.concrete;
                        let symbolic = v.symbolic.map(|s| SymbolicValue::BitwiseNot(Box::new(s)));
                        Ok(ConcolicValue { concrete, symbolic })
                    }
                    trust_types::UnOp::PtrMetadata => Err(unsupported(
                        "pointer metadata extraction requires fat-pointer semantics in concrete symex",
                    )),
                    other => Err(unsupported(format!("unhandled UnOp variant: {other:?}"))),
                }
            }
            Rvalue::Ref { place, .. } => Err(unsupported(format!(
                "references require memory/provenance semantics in concrete symex: {}",
                place_to_name(place)
            ))),
            Rvalue::Cast(op, dest_ty) => {
                let value = self.eval_operand(op)?;
                apply_cast(value, dest_ty)
            }
            Rvalue::Aggregate(kind, _) => Err(SymexError::UnsupportedOperation(format!(
                "unsupported aggregate semantics in concrete symex: {kind:?}"
            ))),
            Rvalue::Discriminant(place) => Err(unsupported(format!(
                "discriminant requires ADT layout semantics in concrete symex: {}",
                place_to_name(place)
            ))),
            Rvalue::Len(place) => Err(unsupported(format!(
                "len requires array/slice layout semantics in concrete symex: {}",
                place_to_name(place)
            ))),
            Rvalue::Repeat(_, _) => Err(unsupported(
                "repeat aggregate requires array-value semantics in concrete symex",
            )),
            Rvalue::AddressOf(_, place) => Err(unsupported(format!(
                "raw address creation requires memory/provenance semantics in concrete symex: {}",
                place_to_name(place)
            ))),
            Rvalue::CopyForDeref(place) => {
                let name = place_to_name(place);
                self.get(&name)
            }
            Rvalue::Unsupported { kind, detail, .. } => Err(unsupported(format!(
                "unsupported MIR rvalue in concrete symex: {kind}: {detail}"
            ))),
            other => Err(SymexError::UnsupportedOperation(format!(
                "unhandled Rvalue variant: {other:?}"
            ))),
        }
    }

    fn eval_operand(&self, op: &Operand) -> Result<ConcolicValue, SymexError> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                let name = place_to_name(place);
                self.get(&name)
            }
            Operand::Constant(cv) => const_to_concolic(cv),
            Operand::Symbolic(_) => {
                Err(unsupported("SMT Formula operands are not executable by concrete symex"))
            }
            Operand::Unsupported { kind, detail } => Err(unsupported(format!(
                "unsupported MIR operand in concrete symex: {kind}: {detail}"
            ))),
            other => Err(SymexError::UnsupportedOperation(format!(
                "unhandled Operand variant: {other:?}"
            ))),
        }
    }
}

/// Evaluate a binary operation on concrete values.
fn eval_concrete_binop(l: i128, op: BinOp, r: i128) -> Result<i128, SymexError> {
    match op {
        BinOp::Add => Ok(l.wrapping_add(r)),
        BinOp::Sub => Ok(l.wrapping_sub(r)),
        BinOp::Mul => Ok(l.wrapping_mul(r)),
        BinOp::Div => {
            if r == 0 {
                Err(unsupported("division by zero in concrete symex"))
            } else {
                Ok(l.wrapping_div(r))
            }
        }
        BinOp::Rem => {
            if r == 0 {
                Err(unsupported("remainder by zero in concrete symex"))
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
        // Clamp shift to valid range; large shifts produce 0.
        BinOp::Shl => Ok(l.wrapping_shl(u32::try_from(r).unwrap_or(128).min(127))),
        BinOp::Shr => Ok(l.wrapping_shr(u32::try_from(r).unwrap_or(128).min(127))),
        // Three-way comparison returns -1 (Less), 0 (Equal), or 1 (Greater).
        BinOp::Cmp => Ok(if l < r {
            -1
        } else if l == r {
            0
        } else {
            1
        }),
        other => {
            Err(SymexError::UnsupportedOperation(format!("unhandled BinOp variant: {other:?}")))
        }
    }
}

fn const_to_concolic(cv: &ConstValue) -> Result<ConcolicValue, SymexError> {
    match cv {
        ConstValue::Bool(b) => Ok(ConcolicValue::concrete(i128::from(*b))),
        ConstValue::Int(n) => Ok(ConcolicValue::concrete(*n)),
        // Trust: #783 — two's complement cast preserves bitvector semantics.
        ConstValue::Uint(n, _) => Ok(ConcolicValue::concrete(*n as i128)),
        ConstValue::Unit => Ok(ConcolicValue::concrete(0)),
        ConstValue::CallableItem { .. } => Err(unsupported(
            "callable-item constants require identity-aware concrete semantics",
        )),
        ConstValue::Float(_) | ConstValue::FloatBits { .. } => {
            Err(unsupported("floating-point constants require float semantics in concrete symex"))
        }
        other => Err(SymexError::UnsupportedOperation(format!(
            "unhandled ConstValue variant: {other:?}"
        ))),
    }
}

fn apply_cast(value: ConcolicValue, dest_ty: &Ty) -> Result<ConcolicValue, SymexError> {
    let Ty::Int { width, signed } = dest_ty else {
        return Err(unsupported(format!(
            "non-integer cast target requires precise cast semantics in concrete symex: {dest_ty:?}"
        )));
    };
    if *width == 0 {
        return Err(unsupported("zero-width integer cast in concrete symex"));
    }

    let concrete = apply_int_cast(value.concrete, *width, *signed);
    let symbolic =
        value.symbolic.map(|sym| apply_symbolic_int_cast(sym, *width, *signed)).transpose()?;
    Ok(ConcolicValue { concrete, symbolic })
}

fn apply_int_cast(value: i128, width: u32, signed: bool) -> i128 {
    if width >= 128 {
        return value;
    }
    let mask = (1i128 << width) - 1;
    let truncated = value & mask;
    if signed {
        let sign_bit = 1i128 << (width - 1);
        if truncated & sign_bit != 0 { truncated | !mask } else { truncated }
    } else {
        truncated
    }
}

fn apply_symbolic_int_cast(
    value: SymbolicValue,
    width: u32,
    signed: bool,
) -> Result<SymbolicValue, SymexError> {
    if width >= 128 {
        return Ok(value);
    }
    let mask = (1i128 << width) - 1;
    let truncated = SymbolicValue::bin_op(value, BinOp::BitAnd, SymbolicValue::Concrete(mask));
    if signed {
        let sign_bit = 1i128 << (width - 1);
        let sign_test = SymbolicValue::bin_op(
            SymbolicValue::bin_op(
                truncated.clone(),
                BinOp::BitAnd,
                SymbolicValue::Concrete(sign_bit),
            ),
            BinOp::Ne,
            SymbolicValue::Concrete(0),
        );
        let sign_extended =
            SymbolicValue::bin_op(truncated.clone(), BinOp::BitOr, SymbolicValue::Concrete(!mask));
        Ok(SymbolicValue::ite(sign_test, sign_extended, truncated))
    } else {
        Ok(truncated)
    }
}

fn unsupported(message: impl Into<String>) -> SymexError {
    SymexError::UnsupportedOperation(message.into())
}

/// Run blocks concretely from an entry point to termination.
///
/// Returns the executor after execution completes (or hits the step limit).
pub(crate) fn run_concrete(
    blocks: &[BasicBlock],
    inputs: &BTreeMap<String, ConcolicValue>,
    step_limit: usize,
) -> Result<ConcreteExecutor, SymexError> {
    let mut executor = ConcreteExecutor::new(step_limit);
    for (name, val) in inputs {
        executor.set_input(name.clone(), val.clone());
    }

    let mut current_block = 0usize;
    loop {
        let block = blocks.get(current_block).ok_or_else(|| {
            SymexError::UnsupportedOperation(format!("block {current_block} out of range"))
        })?;
        match executor.execute_block(block)? {
            Some(next) => current_block = next,
            None => break,
        }
    }

    Ok(executor)
}

#[cfg(test)]
mod tests {
    use trust_types::UnwindEdge;
    use trust_types::{BlockId, Place, SourceSpan, Statement};

    use super::*;

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    #[test]
    fn callable_constants_fail_closed_in_concrete_execution() {
        let value = ConstValue::CallableItem {
            def_path: "fixture::callback".to_string(),
            kind: trust_types::CallableKind::FnDef,
            def_path_hash: trust_types::CallableDefPathHash::new(1, 1),
        };
        let error =
            const_to_concolic(&value).expect_err("concrete values cannot encode callables");
        assert!(matches!(
            error,
            SymexError::UnsupportedOperation(message)
                if message.contains("callable-item constants")
        ));
    }

    #[test]
    fn test_concrete_pure_concrete_execution() {
        let blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(42))),
                span: span(),
            }],
            terminator: Terminator::Return,
        }];
        let inputs = BTreeMap::default();
        let exec = run_concrete(&blocks, &inputs, 100).expect("should succeed");
        let val = exec.get("_local1").expect("_local1 initialized");
        assert_eq!(val.concrete, 42);
        assert!(!val.is_symbolic());
    }

    #[test]
    fn test_concrete_symbolic_input_tracking() {
        let mut executor = ConcreteExecutor::new(100);
        executor.set_input("x", ConcolicValue::with_shadow(5, SymbolicValue::Symbol("x".into())));
        let val = executor.get("x").expect("x initialized");
        assert_eq!(val.concrete, 5);
        assert!(val.is_symbolic());
        match val.to_symbolic() {
            SymbolicValue::Symbol(name) => assert_eq!(name, "x"),
            other => panic!("expected Symbol, got {other:?}"),
        }
    }

    #[test]
    fn test_concrete_binary_op_symbolic_propagation() {
        let blocks = vec![BasicBlock {
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
        }];

        let mut inputs = BTreeMap::default();
        inputs.insert(
            "_local0".to_string(),
            ConcolicValue::with_shadow(10, SymbolicValue::Symbol("arg0".into())),
        );

        let exec = run_concrete(&blocks, &inputs, 100).expect("should succeed");
        let result = exec.get("_local2").expect("_local2 initialized");
        assert_eq!(result.concrete, 11); // 10 + 1
        assert!(result.is_symbolic());
    }

    #[test]
    fn test_concrete_switch_records_symbolic_branch() {
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

        let mut inputs = BTreeMap::default();
        inputs.insert(
            "_local0".to_string(),
            ConcolicValue::with_shadow(1, SymbolicValue::Symbol("input".into())),
        );

        let exec = run_concrete(&blocks, &inputs, 100).expect("should succeed");
        assert!(!exec.symbolic_branches.is_empty());
        // With concrete value 1, should take the first target (value == 1).
        assert!(exec.symbolic_branches[0].taken);
    }

    #[test]
    fn test_concrete_step_limit() {
        let blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Goto(BlockId(0)),
        }];
        let inputs = BTreeMap::default();
        let result = run_concrete(&blocks, &inputs, 3);
        assert!(result.is_err());
    }

    #[test]
    fn test_concolic_value_pure_concrete() {
        let v = ConcolicValue::concrete(42);
        assert!(!v.is_symbolic());
        assert_eq!(v.concrete, 42);
        assert_eq!(v.to_symbolic(), SymbolicValue::Concrete(42));
    }

    #[test]
    fn test_concolic_value_with_shadow() {
        let v = ConcolicValue::with_shadow(5, SymbolicValue::Symbol("x".into()));
        assert!(v.is_symbolic());
        assert_eq!(v.concrete, 5);
        match v.to_symbolic() {
            SymbolicValue::Symbol(name) => assert_eq!(name, "x"),
            other => panic!("expected Symbol, got {other:?}"),
        }
    }

    #[test]
    fn test_concrete_goto_chain() {
        let blocks = vec![
            BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Goto(BlockId(1)) },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(99))),
                    span: span(),
                }],
                terminator: Terminator::Return,
            },
        ];
        let exec = run_concrete(&blocks, &BTreeMap::default(), 100).expect("should succeed");
        assert_eq!(exec.get("_local1").expect("_local1 initialized").concrete, 99);
        assert_eq!(exec.steps, 2);
    }

    #[test]
    fn test_eval_concrete_binop_div_by_zero() {
        assert_unsupported(eval_concrete_binop(10, BinOp::Div, 0), "division by zero");
        assert_unsupported(eval_concrete_binop(10, BinOp::Rem, 0), "remainder by zero");
    }

    #[test]
    fn test_eval_concrete_binop_comparisons() {
        assert_eq!(eval_concrete_binop(3, BinOp::Lt, 5).unwrap(), 1);
        assert_eq!(eval_concrete_binop(5, BinOp::Lt, 3).unwrap(), 0);
        assert_eq!(eval_concrete_binop(3, BinOp::Eq, 3).unwrap(), 1);
        assert_eq!(eval_concrete_binop(3, BinOp::Ne, 3).unwrap(), 0);
    }

    #[test]
    fn test_concrete_missing_variable_errors() {
        let blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(0))),
                span: span(),
            }],
            terminator: Terminator::Return,
        }];

        let err = run_concrete(&blocks, &BTreeMap::default(), 100)
            .expect_err("missing variables must not default to zero");
        assert!(matches!(err, SymexError::UndefinedVariable(name) if name == "_local0"));
    }

    #[test]
    fn test_concrete_false_assert_errors() {
        let blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Assert {
                unwind: UnwindEdge::Unreachable,
                cond: Operand::Constant(ConstValue::Bool(false)),
                expected: true,
                msg: trust_types::AssertMessage::BoundsCheck,
                target: BlockId(1),
                span: span(),
            },
        }];

        let err = run_concrete(&blocks, &BTreeMap::default(), 100)
            .expect_err("false assertion must fail closed");
        assert!(matches!(err, SymexError::AssertionFailed { expected: true, actual: false }));
    }

    #[test]
    fn test_concrete_opaque_terminator_errors() {
        let blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Opaque {
                kind: "Yield".into(),
                targets: vec![BlockId(1)],
                span: span(),
            },
        }];

        let err = run_concrete(&blocks, &BTreeMap::default(), 100)
            .expect_err("opaque terminator must fail closed");
        assert!(
            matches!(err, SymexError::UnsupportedOperation(msg) if msg.contains("opaque terminator"))
        );
    }

    #[test]
    fn test_concrete_pointer_cast_errors() {
        let ptr_ty = Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) };
        let blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(1),
                rvalue: Rvalue::Cast(Operand::Constant(ConstValue::Int(0xDEAD)), ptr_ty),
                span: span(),
            }],
            terminator: Terminator::Return,
        }];

        let err = run_concrete(&blocks, &BTreeMap::default(), 100)
            .expect_err("pointer casts must not be identity");
        assert!(
            matches!(err, SymexError::UnsupportedOperation(msg) if msg.contains("non-integer cast target"))
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
