// trust-machine-sem error types
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_disasm::Opcode;

/// Errors produced during instruction semantics evaluation.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum SemError {
    /// The instruction opcode is not yet modeled.
    #[error("unsupported opcode: {0}")]
    UnsupportedOpcode(Opcode),

    /// Atomic or exclusive semantics require ordering/monitor state not yet modeled.
    #[error("unsupported atomic/exclusive opcode {opcode}: {detail}")]
    UnsupportedAtomic { opcode: Opcode, detail: String },

    /// AArch64 opcode is recognized but blocked from proof-grade semantics by
    /// a typed missing semantic witness category.
    #[error("unsupported AArch64 {category} proof blocker opcode {opcode}: {detail}")]
    UnsupportedAarch64ProofBlocker { opcode: Opcode, category: &'static str, detail: String },

    /// An operand was missing or had unexpected form.
    #[error("invalid operand at index {index} for {opcode}: {detail}")]
    InvalidOperand { opcode: Opcode, index: usize, detail: String },

    /// Register width mismatch in an operation.
    #[error("width mismatch: expected {expected}-bit, got {actual}-bit")]
    WidthMismatch { expected: u32, actual: u32 },
}
