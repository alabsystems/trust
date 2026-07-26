// trust_vcgen/binary_analysis/lifter.rs: Binary lifting into trust-types MIR
//
// Defines a small abstract instruction layer and lowers lifted binaries into
// `VerifiableFunction` bodies built from `BasicBlock`, `Statement`, and
// `Terminator` values.
//
// Part of #148: Binary analysis pipeline
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use trust_types::*;

use super::cfg_reconstruct::reconstruct_cfg;
use super::lowering::{
    build_locals, build_lowering_context, collect_register_ids, infer_formula_ty,
    lower_cfg_to_blocks, ty_for_register_width,
};

/// An abstract operand used by lifted binary instructions.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AbstractValue {
    /// A machine register identified by its abstract register ID.
    Register(u16),
    /// A symbolic or literal formula value.
    Formula(Formula),
}

/// A symbolic memory access used by abstract load/store instructions.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum MemoryAccess {
    /// Read `size` bytes from `addr`.
    Read { addr: Formula, size: u32 },
    /// Write `value` to `addr` over `size` bytes.
    Write { addr: Formula, size: u32, value: Formula },
}

/// An abstract instruction operation produced by the binary lifter front-end.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AbstractOp {
    /// `dst = *addr`
    Load { dst: u16, access: MemoryAccess },
    /// `*addr = value`
    Store { access: MemoryAccess },
    /// `dst = lhs <op> rhs`
    BinArith { dst: u16, op: BinOp, lhs: AbstractValue, rhs: AbstractValue },
    /// `dst = <op> operand`
    UnaryOp { dst: u16, op: UnOp, operand: AbstractValue },
    /// Unconditional control transfer.
    Branch { target: u64 },
    /// Conditional control transfer.
    CondBranch { cond: AbstractValue, true_target: u64, false_target: u64 },
    /// Call a named procedure, optionally storing the result.
    Call { func: String, args: Vec<AbstractValue>, dest: Option<u16>, next: Option<u64> },
    /// Return from the current function.
    Return { value: Option<AbstractValue> },
    /// Simple register-to-register copy / sign-extend / zero-extend.
    Assign { dst: u16, src: AbstractValue },
    /// Compare two values and store the boolean result.
    Compare { dst: u16, op: BinOp, lhs: AbstractValue, rhs: AbstractValue },
    /// Indirect branch through a register (unresolved target).
    IndirectBranch { target: AbstractValue },
    /// No-op or ignored instruction.
    Nop,
}

/// One lifted instruction in address order.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AbstractInsn {
    /// Concrete address in the original binary.
    pub address: u64,
    /// The abstracted operation semantics.
    pub op: AbstractOp,
    /// Encoded instruction size in bytes.
    pub size: u8,
}

/// A machine register exposed to the lifting layer.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AbstractRegister {
    /// Stable register ID used in abstract instructions.
    pub id: u16,
    /// Human-readable register name.
    pub name: String,
    /// Bit width of the register value.
    pub width: u32,
}

/// A fully lifted binary program ready for MIR lowering.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LiftedProgram {
    /// Instructions in ascending address order.
    pub instructions: Vec<AbstractInsn>,
    /// Binary entry-point address.
    pub entry_point: u64,
    /// Register file visible at function entry.
    pub registers: Vec<AbstractRegister>,
}

/// Errors that can arise while converting lifted instructions into MIR.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum LiftError {
    /// The program declared the same register ID more than once.
    #[error("duplicate abstract register r{id}")]
    DuplicateRegister { id: u16 },

    /// The entry point does not correspond to any lifted instruction.
    #[error("entry point 0x{entry_point:x} is not present in the instruction stream")]
    MissingEntryPoint { entry_point: u64 },

    /// An instruction used a register absent from `LiftedProgram::registers`.
    #[error("instruction at 0x{address:x} references undeclared register r{id}")]
    UnknownRegister { address: u64, id: u16 },

    /// A load instruction was paired with the wrong memory access shape.
    #[error("instruction at 0x{address:x} uses a non-read memory access for Load")]
    InvalidLoadAccess { address: u64 },

    /// A store instruction was paired with the wrong memory access shape.
    #[error("instruction at 0x{address:x} uses a non-write memory access for Store")]
    InvalidStoreAccess { address: u64 },

    /// A control-flow target does not correspond to any lifted instruction.
    #[error("instruction at 0x{address:x} targets missing address 0x{target:x}")]
    MissingTarget { address: u64, target: u64 },

    /// An indirect branch target cannot be represented in strict lifted MIR.
    #[error("instruction at 0x{address:x} has unresolved indirect branch target")]
    UnresolvedIndirectBranch { address: u64 },

    /// Return instructions disagreed on the synthesized return type.
    #[error("inconsistent return types: expected {expected:?}, found {found:?}")]
    InconsistentReturnType { expected: Ty, found: Ty },
}

/// Convert a lifted binary program into a verifiable MIR body.
pub fn lift_to_mir(program: &LiftedProgram) -> Result<VerifiableFunction, LiftError> {
    validate_program(program)?;

    let return_ty = infer_return_ty(program)?;
    if program.instructions.is_empty() {
        return Ok(VerifiableFunction {
            name: format!("lifted_{:x}", program.entry_point),
            def_path: format!("binary::0x{:x}", program.entry_point),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: return_ty.clone(), name: None }],
                blocks: vec![],
                arg_count: program.registers.len(),
                return_ty,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        });
    }

    let mut cfg = reconstruct_cfg(&program.instructions);
    normalize_cfg_entry(&mut cfg, program.entry_point);

    let context = build_lowering_context(&cfg, &program.registers);
    let blocks = lower_cfg_to_blocks(&cfg, &context);
    let locals = build_locals(return_ty.clone(), &context);

    Ok(VerifiableFunction {
        name: format!("lifted_{:x}", program.entry_point),
        def_path: format!("binary::0x{:x}", program.entry_point),
        span: SourceSpan::binary_address(program.entry_point),
        body: VerifiableBody { locals, blocks, arg_count: program.registers.len(), return_ty },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    })
}

fn normalize_cfg_entry(cfg: &mut super::cfg_reconstruct::ReconstructedCfg, entry_point: u64) {
    cfg.entry = entry_point;
    cfg.nodes.sort_by_key(|node| (node.address != entry_point, node.address));

    for (index, node) in cfg.nodes.iter_mut().enumerate() {
        node.block_id = BlockId(index);
    }
}

fn validate_program(program: &LiftedProgram) -> Result<(), LiftError> {
    let mut seen_registers = BTreeSet::new();
    for register in &program.registers {
        if !seen_registers.insert(register.id) {
            return Err(LiftError::DuplicateRegister { id: register.id });
        }
    }

    if !program.instructions.is_empty()
        && !program.instructions.iter().any(|insn| insn.address == program.entry_point)
    {
        return Err(LiftError::MissingEntryPoint { entry_point: program.entry_point });
    }

    let cfg = reconstruct_cfg(&program.instructions);
    let declared_registers: BTreeMap<u16, &AbstractRegister> =
        program.registers.iter().map(|register| (register.id, register)).collect();
    let used_registers = collect_register_ids(&cfg);

    for register in used_registers {
        if !declared_registers.contains_key(&register) {
            let address = instruction_address_using_register(&program.instructions, register);
            return Err(LiftError::UnknownRegister { address, id: register });
        }
    }

    let valid_targets: BTreeSet<u64> =
        program.instructions.iter().map(|insn| insn.address).collect();
    for insn in &program.instructions {
        match &insn.op {
            AbstractOp::Load { access: MemoryAccess::Read { .. }, .. }
            | AbstractOp::Store { access: MemoryAccess::Write { .. } }
            | AbstractOp::BinArith { .. }
            | AbstractOp::UnaryOp { .. }
            | AbstractOp::Assign { .. }
            | AbstractOp::Compare { .. }
            | AbstractOp::Return { .. }
            | AbstractOp::Branch { .. }
            | AbstractOp::CondBranch { .. }
            | AbstractOp::Call { .. }
            | AbstractOp::Nop => {}
            AbstractOp::Load { .. } => {
                return Err(LiftError::InvalidLoadAccess { address: insn.address });
            }
            AbstractOp::Store { .. } => {
                return Err(LiftError::InvalidStoreAccess { address: insn.address });
            }
            AbstractOp::IndirectBranch { .. } => {
                return Err(LiftError::UnresolvedIndirectBranch { address: insn.address });
            }
        }

        match &insn.op {
            AbstractOp::Branch { target } => {
                validate_target(insn.address, *target, &valid_targets)?;
            }
            AbstractOp::CondBranch { true_target, false_target, .. } => {
                validate_target(insn.address, *true_target, &valid_targets)?;
                validate_target(insn.address, *false_target, &valid_targets)?;
            }
            AbstractOp::Call { next: Some(target), .. } => {
                validate_target(insn.address, *target, &valid_targets)?;
            }
            _ => {}
        }
    }

    Ok(())
}

fn validate_target(
    address: u64,
    target: u64,
    valid_targets: &BTreeSet<u64>,
) -> Result<(), LiftError> {
    if valid_targets.contains(&target) {
        Ok(())
    } else {
        Err(LiftError::MissingTarget { address, target })
    }
}

fn infer_return_ty(program: &LiftedProgram) -> Result<Ty, LiftError> {
    let register_types: BTreeMap<u16, Ty> = program
        .registers
        .iter()
        .map(|register| (register.id, ty_for_register_width(register.width)))
        .collect();

    let mut return_ty = Ty::Unit;
    for insn in &program.instructions {
        if let AbstractOp::Return { value: Some(value) } = &insn.op {
            let current = abstract_value_ty(value, &register_types);
            if return_ty == Ty::Unit {
                return_ty = current;
            } else if return_ty != current {
                return Err(LiftError::InconsistentReturnType {
                    expected: return_ty,
                    found: current,
                });
            }
        }
    }

    Ok(return_ty)
}

fn abstract_value_ty(value: &AbstractValue, register_types: &BTreeMap<u16, Ty>) -> Ty {
    match value {
        AbstractValue::Register(id) => {
            register_types.get(id).cloned().unwrap_or(Ty::Int { width: 64, signed: false })
        }
        AbstractValue::Formula(formula) => infer_formula_ty(formula),
    }
}

fn instruction_address_using_register(instructions: &[AbstractInsn], register: u16) -> u64 {
    instructions
        .iter()
        .find(|insn| instruction_mentions_register(insn, register))
        .map_or(0, |insn| insn.address)
}

fn instruction_mentions_register(insn: &AbstractInsn, register: u16) -> bool {
    match &insn.op {
        AbstractOp::Load { dst, .. } => *dst == register,
        AbstractOp::Store { .. } | AbstractOp::Branch { .. } | AbstractOp::Nop => false,
        AbstractOp::BinArith { dst, lhs, rhs, .. } | AbstractOp::Compare { dst, lhs, rhs, .. } => {
            *dst == register
                || abstract_value_mentions_register(lhs, register)
                || abstract_value_mentions_register(rhs, register)
        }
        AbstractOp::UnaryOp { dst, operand, .. } => {
            *dst == register || abstract_value_mentions_register(operand, register)
        }
        AbstractOp::Assign { dst, src } => {
            *dst == register || abstract_value_mentions_register(src, register)
        }
        AbstractOp::CondBranch { cond, .. } => abstract_value_mentions_register(cond, register),
        AbstractOp::IndirectBranch { target } => abstract_value_mentions_register(target, register),
        AbstractOp::Call { args, dest, .. } => {
            dest.is_some_and(|dest| dest == register)
                || args.iter().any(|arg| abstract_value_mentions_register(arg, register))
        }
        AbstractOp::Return { value } => {
            value.as_ref().is_some_and(|value| abstract_value_mentions_register(value, register))
        }
    }
}

fn abstract_value_mentions_register(value: &AbstractValue, register: u16) -> bool {
    matches!(value, AbstractValue::Register(id) if *id == register)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn reg(id: u16, width: u32) -> AbstractRegister {
        AbstractRegister { id, name: format!("r{id}"), width }
    }

    fn insn(address: u64, op: AbstractOp) -> AbstractInsn {
        AbstractInsn { address, op, size: 4 }
    }

    #[test]
    fn test_lift_empty_program() {
        let program = LiftedProgram { instructions: vec![], entry_point: 0, registers: vec![] };

        let function = lift_to_mir(&program).expect("empty program should lift");
        assert!(function.body.blocks.is_empty());
        assert_eq!(function.body.locals.len(), 1);
        assert_eq!(function.body.return_ty, Ty::Unit);
    }

    #[test]
    fn test_lift_simple_arithmetic() {
        let program = LiftedProgram {
            instructions: vec![
                insn(
                    0x100,
                    AbstractOp::BinArith {
                        dst: 2,
                        op: BinOp::Add,
                        lhs: AbstractValue::Register(0),
                        rhs: AbstractValue::Register(1),
                    },
                ),
                insn(0x104, AbstractOp::Return { value: Some(AbstractValue::Register(2)) }),
            ],
            entry_point: 0x100,
            registers: vec![reg(0, 64), reg(1, 64), reg(2, 64)],
        };

        let function = lift_to_mir(&program).expect("arithmetic program should lift");
        assert_eq!(function.span, SourceSpan::binary_address(0x100));
        assert_eq!(function.body.blocks.len(), 1);
        assert_eq!(function.body.return_ty, Ty::Int { width: 64, signed: false });

        let block = &function.body.blocks[0];
        assert_eq!(block.id, BlockId(0));
        assert!(matches!(
            block.stmts[0],
            Statement::Assign { rvalue: Rvalue::BinaryOp(BinOp::Add, ..), .. }
        ));
        assert!(matches!(
            &block.stmts[0],
            Statement::Assign { span, .. } if span == &SourceSpan::binary_address(0x100)
        ));
        assert!(matches!(
            &block.stmts[1],
            Statement::Assign { span, .. } if span == &SourceSpan::binary_address(0x104)
        ));
        assert!(matches!(block.terminator, Terminator::Return));
    }

    #[test]
    fn test_lift_branch_program() {
        let program = LiftedProgram {
            instructions: vec![
                insn(
                    0x100,
                    AbstractOp::CondBranch {
                        cond: AbstractValue::Register(0),
                        true_target: 0x110,
                        false_target: 0x120,
                    },
                ),
                insn(
                    0x110,
                    AbstractOp::Return { value: Some(AbstractValue::Formula(Formula::Int(1))) },
                ),
                insn(
                    0x120,
                    AbstractOp::Return { value: Some(AbstractValue::Formula(Formula::Int(0))) },
                ),
            ],
            entry_point: 0x100,
            registers: vec![reg(0, 1)],
        };

        let function = lift_to_mir(&program).expect("branch program should lift");
        assert_eq!(function.body.blocks.len(), 3);
        assert!(matches!(
            &function.body.blocks[0].terminator,
            Terminator::SwitchInt { span, .. } if span == &SourceSpan::binary_address(0x100)
        ));
    }

    #[test]
    fn test_lift_call_program() {
        let program = LiftedProgram {
            instructions: vec![
                insn(
                    0x100,
                    AbstractOp::Call {
                        func: "puts".to_string(),
                        args: vec![AbstractValue::Register(0)],
                        dest: Some(1),
                        next: Some(0x108),
                    },
                ),
                insn(0x108, AbstractOp::Return { value: Some(AbstractValue::Register(1)) }),
            ],
            entry_point: 0x100,
            registers: vec![reg(0, 64), reg(1, 64)],
        };

        let function = lift_to_mir(&program).expect("call program should lift");
        assert_eq!(function.body.blocks.len(), 2);
        assert!(matches!(
            &function.body.blocks[0].terminator,
            Terminator::Call { target: Some(BlockId(1)), span, .. }
                if span == &SourceSpan::binary_address(0x100)
        ));
        assert!(matches!(function.body.blocks[1].terminator, Terminator::Return));
    }

    #[test]
    fn test_lift_load_store_program() {
        let pointer = Formula::Var("ptr".into(), Sort::Int);
        let program = LiftedProgram {
            instructions: vec![
                insn(
                    0x100,
                    AbstractOp::Load {
                        dst: 0,
                        access: MemoryAccess::Read { addr: pointer.clone(), size: 4 },
                    },
                ),
                insn(
                    0x104,
                    AbstractOp::Store {
                        access: MemoryAccess::Write {
                            addr: pointer,
                            size: 4,
                            value: Formula::Int(7),
                        },
                    },
                ),
                insn(0x108, AbstractOp::Return { value: Some(AbstractValue::Register(0)) }),
            ],
            entry_point: 0x100,
            registers: vec![reg(0, 32)],
        };

        let function = lift_to_mir(&program).expect("memory program should lift");
        let block = &function.body.blocks[0];
        assert_eq!(block.stmts.len(), 3);

        assert!(matches!(
            &block.stmts[0],
            Statement::Assign {
                rvalue: Rvalue::Use(Operand::Copy(Place { projections, .. })),
                ..
            } if projections == &vec![Projection::Deref]
        ));
        assert!(matches!(
            &block.stmts[1],
            Statement::Assign {
                place: Place { projections, .. },
                ..
            } if projections == &vec![Projection::Deref]
        ));
    }

    #[test]
    fn test_lift_indirect_branch_fails_closed() {
        let program = LiftedProgram {
            instructions: vec![insn(
                0x100,
                AbstractOp::IndirectBranch { target: AbstractValue::Register(0) },
            )],
            entry_point: 0x100,
            registers: vec![reg(0, 64)],
        };

        let err = lift_to_mir(&program).expect_err("indirect targets must fail closed");
        assert!(matches!(err, LiftError::UnresolvedIndirectBranch { address: 0x100 }));
    }

    #[test]
    fn test_lifted_program_roundtrip() {
        let program = LiftedProgram {
            instructions: vec![
                insn(
                    0x100,
                    AbstractOp::UnaryOp {
                        dst: 1,
                        op: UnOp::Not,
                        operand: AbstractValue::Register(0),
                    },
                ),
                insn(0x104, AbstractOp::Return { value: Some(AbstractValue::Register(1)) }),
            ],
            entry_point: 0x100,
            registers: vec![reg(0, 1), reg(1, 1)],
        };

        let json = serde_json::to_string(&program).expect("serialize");
        let roundtrip: LiftedProgram = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip, program);

        let function = lift_to_mir(&roundtrip).expect("round-tripped program should lift");
        assert_eq!(function.body.blocks.len(), 1);
        assert!(matches!(function.body.blocks[0].terminator, Terminator::Return));
    }
}
