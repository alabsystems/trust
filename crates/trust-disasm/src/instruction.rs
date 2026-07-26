// trust-disasm instruction representation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::opcode::Opcode;
use crate::operand::{Operand, Register};

/// Maximum number of operands per instruction.
pub(crate) const MAX_OPERANDS: usize = 5;

/// Control flow classification of an instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ControlFlow {
    /// Falls through to the next instruction.
    Fallthrough,
    /// Unconditional branch (B, BR).
    Branch,
    /// Conditional branch (B.cond, CBZ, CBNZ, TBZ, TBNZ).
    ConditionalBranch,
    /// Function call (BL, BLR).
    Call,
    /// Return from function (RET).
    Return,
    /// System call / exception (SVC, HVC, SMC, BRK, HLT).
    Exception,
}

/// A decoded instruction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Instruction {
    /// Virtual address of this instruction.
    pub address: u64,
    /// Instruction size in bytes (always 4 for AArch64).
    pub size: u8,
    /// Legacy raw encoding field.
    pub encoding: u32,
    /// Original instruction bytes as they appeared in the input stream.
    pub bytes: Vec<u8>,
    /// Decoded opcode.
    pub opcode: Opcode,
    /// Operands (up to MAX_OPERANDS, unused slots are None).
    operands: [Option<Operand>; MAX_OPERANDS],
    /// Number of valid operands.
    operand_count: u8,
    /// Control flow classification.
    pub flow: ControlFlow,
}

impl Instruction {
    /// Create a new instruction with the given base fields and no operands.
    /// Default size is 4 (AArch64). Use `with_size` for variable-length ISAs.
    #[must_use]
    pub(crate) fn new(address: u64, encoding: u32, opcode: Opcode, flow: ControlFlow) -> Self {
        Self {
            address,
            size: 4,
            encoding,
            bytes: encoding.to_le_bytes().to_vec(),
            opcode,
            operands: [None; MAX_OPERANDS],
            operand_count: 0,
            flow,
        }
    }

    /// Create a new instruction with an explicit size (for variable-length ISAs like x86-64).
    /// The `encoding` field preserves the legacy compact encoding value.
    #[must_use]
    pub(crate) fn with_size(
        address: u64,
        size: u8,
        encoding: u32,
        opcode: Opcode,
        flow: ControlFlow,
    ) -> Self {
        Self {
            address,
            size,
            encoding,
            bytes: encoding.to_le_bytes()[..usize::from(size).min(4)].to_vec(),
            opcode,
            operands: [None; MAX_OPERANDS],
            operand_count: 0,
            flow,
        }
    }

    /// Append an operand. Panics if more than MAX_OPERANDS are added.
    pub(crate) fn push_operand(&mut self, op: Operand) {
        let idx = self.operand_count as usize;
        assert!(idx < MAX_OPERANDS, "too many operands");
        self.operands[idx] = Some(op);
        self.operand_count += 1;
    }

    /// Number of operands.
    #[must_use]
    pub fn operand_count(&self) -> usize {
        self.operand_count as usize
    }

    /// Get operand by index.
    #[must_use]
    pub fn operand(&self, index: usize) -> Option<&Operand> {
        if index < self.operand_count as usize { self.operands[index].as_ref() } else { None }
    }

    /// Iterate over operands.
    pub fn operands(&self) -> impl Iterator<Item = &Operand> {
        self.operands[..self.operand_count as usize].iter().filter_map(|o| o.as_ref())
    }

    /// Returns true if this instruction reads the given register.
    #[must_use]
    pub fn reads_register(&self, reg: &Register) -> bool {
        // Source operands are typically operands 1+ for most instructions.
        // Memory operands' base/index registers are reads.
        for op in self.operands() {
            match op {
                Operand::Reg(r)
                | Operand::ShiftedReg { reg: r, .. }
                | Operand::ExtendedReg { reg: r, .. }
                    if r == reg =>
                {
                    return true;
                }
                Operand::Mem(mem) if mem_reads_register(mem, reg) => {
                    return true;
                }
                _ => {}
            }
        }
        false
    }

    /// Returns true if this instruction writes the given register.
    #[must_use]
    pub fn writes_register(&self, reg: &Register) -> bool {
        // The first operand is typically the destination for data processing.
        // Stores don't write their first operand (it's the source).
        if self.is_store() {
            return false;
        }
        if let Some(Operand::Reg(r)) = self.operand(0) {
            return r == reg;
        }
        false
    }

    /// Is this a load instruction?
    #[must_use]
    pub fn is_load(&self) -> bool {
        matches!(
            self.opcode,
            Opcode::Ldr
                | Opcode::Ldrb
                | Opcode::Ldrh
                | Opcode::Ldrsb
                | Opcode::Ldrsh
                | Opcode::Ldrsw
                | Opcode::Ldp
                | Opcode::Ldxr
                | Opcode::Ldar
                | Opcode::Ldaxr
                | Opcode::LdrLiteral
        )
    }

    /// Is this a store instruction?
    #[must_use]
    pub fn is_store(&self) -> bool {
        matches!(
            self.opcode,
            Opcode::Str
                | Opcode::Strb
                | Opcode::Strh
                | Opcode::Stp
                | Opcode::Stxr
                | Opcode::Stlr
                | Opcode::Stlxr
        )
    }

    /// Is this a branch/jump instruction?
    #[must_use]
    pub fn is_branch(&self) -> bool {
        matches!(
            self.flow,
            ControlFlow::Branch
                | ControlFlow::ConditionalBranch
                | ControlFlow::Call
                | ControlFlow::Return
        )
    }

    /// Branch target address, if this is a direct branch.
    #[must_use]
    pub fn branch_target(&self) -> Option<u64> {
        for op in self.operands() {
            if let Operand::PcRelAddr(addr) = op {
                return Some(*addr);
            }
        }
        None
    }
}

/// Check if a memory operand reads a specific register.
fn mem_reads_register(mem: &crate::operand::MemoryOperand, reg: &Register) -> bool {
    use crate::operand::MemoryOperand;
    match mem {
        MemoryOperand::Base { base } => base == reg,
        MemoryOperand::BaseOffset { base, .. } => base == reg,
        MemoryOperand::BaseRegister { base, index, .. } => base == reg || index == reg,
        MemoryOperand::PreIndex { base, .. } => base == reg,
        MemoryOperand::PostIndex { base, .. } => base == reg,
        MemoryOperand::PcRelative { .. } => false,
    }
}
