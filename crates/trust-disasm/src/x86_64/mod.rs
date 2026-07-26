// trust-disasm x86-64 (AMD64) decoder
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
// Reference: Intel 64 and IA-32 Architectures Software Developer's Manual,
// Volume 2 (Instruction Set Reference). AMD64 Architecture Programmer's
// Manual, Volume 3 (General-Purpose and System Instructions).
//
// x86-64 instructions are variable-length (1-15 bytes), little-endian.
// Decoding order: legacy prefixes -> REX prefix -> opcode -> ModR/M -> SIB
// -> displacement -> immediate.

pub(crate) mod decoder;
pub(crate) mod modrm;
pub(crate) mod prefix;

#[cfg(test)]
mod tests;

use crate::arch::{Arch, Decoder};
use crate::error::DisasmError;
use crate::instruction::Instruction;

/// x86-64 instruction decoder.
#[derive(Debug, Clone, Default)]
pub struct X86_64Decoder;

impl X86_64Decoder {
    /// Create a new x86-64 decoder.
    #[must_use]
    pub fn new() -> Self {
        Self
    }
}

impl Arch for X86_64Decoder {
    fn name(&self) -> &'static str {
        "x86-64"
    }

    fn min_insn_size(&self) -> usize {
        1
    }

    fn max_insn_size(&self) -> usize {
        15
    }

    fn alignment(&self) -> usize {
        1 // No alignment requirement
    }

    fn gpr_count(&self) -> usize {
        16 // RAX-R15
    }

    fn stack_pointer(&self) -> Option<u8> {
        Some(4) // RSP
    }

    fn link_register(&self) -> Option<u8> {
        None // x86-64 uses the stack for return addresses
    }

    fn program_counter(&self) -> Option<u8> {
        None // RIP not accessible as a GPR
    }
}

impl Decoder for X86_64Decoder {
    fn decode(&self, bytes: &[u8], address: u64) -> Result<Instruction, DisasmError> {
        if bytes.is_empty() {
            return Err(DisasmError::InsufficientBytes { needed: 1, available: 0 });
        }
        decoder::decode_instruction(bytes, address)
    }
}
