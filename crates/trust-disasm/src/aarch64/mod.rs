// trust-disasm AArch64 (A64) decoder
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
// Reference: ARM Architecture Reference Manual for A-profile architecture
// (DDI 0487). All encoding tables referenced below follow the ARMv8-A spec.
// AArch64 instructions are fixed 32-bit width, little-endian.

mod decode;

#[cfg(test)]
mod tests;

use crate::arch::{Arch, Decoder};
use crate::error::DisasmError;
use crate::instruction::Instruction;

/// AArch64 instruction decoder.
#[derive(Debug, Clone, Default)]
pub struct Aarch64Decoder;

impl Aarch64Decoder {
    /// Create a new AArch64 decoder.
    #[must_use]
    pub fn new() -> Self {
        Self
    }
}

impl Arch for Aarch64Decoder {
    fn name(&self) -> &'static str {
        "AArch64"
    }

    fn min_insn_size(&self) -> usize {
        4
    }

    fn max_insn_size(&self) -> usize {
        4
    }

    fn alignment(&self) -> usize {
        4
    }

    fn gpr_count(&self) -> usize {
        31 // X0-X30
    }

    fn stack_pointer(&self) -> Option<u8> {
        Some(31)
    }

    fn link_register(&self) -> Option<u8> {
        Some(30)
    }

    fn program_counter(&self) -> Option<u8> {
        None // PC not accessible as GPR in AArch64
    }
}

impl Decoder for Aarch64Decoder {
    fn decode(&self, bytes: &[u8], address: u64) -> Result<Instruction, DisasmError> {
        if bytes.len() < 4 {
            return Err(DisasmError::InsufficientBytes { needed: 4, available: bytes.len() });
        }
        // AArch64 is always little-endian for instruction fetch.
        let encoding = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
        let mut instruction = decode::decode_instruction(encoding, address)?;
        instruction.bytes = bytes[..4].to_vec();
        Ok(instruction)
    }
}
