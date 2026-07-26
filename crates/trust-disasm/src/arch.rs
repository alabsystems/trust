// trust-disasm architecture trait
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::error::DisasmError;
use crate::instruction::Instruction;

/// Architecture-specific instruction decoder trait.
///
/// Each ISA (AArch64, x86-64, RISC-V, etc.) implements this trait.
/// The decoder is stateless -- all context comes from the byte stream and address.
pub trait Arch {
    /// Human-readable name of the architecture (e.g., "AArch64").
    fn name(&self) -> &'static str;

    /// Minimum instruction size in bytes (4 for AArch64, 1 for x86-64).
    fn min_insn_size(&self) -> usize;

    /// Maximum instruction size in bytes (4 for AArch64, 15 for x86-64).
    fn max_insn_size(&self) -> usize;

    /// Instruction alignment requirement in bytes (4 for AArch64, 1 for x86-64).
    fn alignment(&self) -> usize;

    /// Number of general-purpose registers.
    fn gpr_count(&self) -> usize;

    /// Stack pointer register index, if the architecture has one.
    fn stack_pointer(&self) -> Option<u8>;

    /// Link register index, if the architecture has one.
    fn link_register(&self) -> Option<u8>;

    /// Program counter register index, if exposed as a GPR.
    fn program_counter(&self) -> Option<u8>;
}

/// Stateless instruction decoder.
///
/// Implementations decode raw bytes into structured [`Instruction`] values.
pub trait Decoder: Arch {
    /// Decode one instruction starting at `bytes[0]` with the given virtual address.
    ///
    /// Returns the decoded instruction (which includes its size) or an error.
    /// The caller advances by `instruction.size` bytes for the next decode.
    fn decode(&self, bytes: &[u8], address: u64) -> Result<Instruction, DisasmError>;

    /// Decode a sequence of instructions from a byte slice.
    ///
    /// Stops at the first error or when the byte slice is exhausted.
    fn decode_all(&self, bytes: &[u8], base_address: u64) -> Vec<Result<Instruction, DisasmError>> {
        let mut results = Vec::new();
        let mut offset = 0usize;
        while offset < bytes.len() {
            let addr = base_address.wrapping_add(offset as u64);
            match self.decode(&bytes[offset..], addr) {
                Ok(insn) => {
                    let size = insn.size as usize;
                    results.push(Ok(insn));
                    offset += size;
                }
                Err(e) => {
                    results.push(Err(e));
                    // Advance by minimum instruction size to try to resync.
                    offset += self.min_insn_size();
                }
            }
        }
        results
    }
}
