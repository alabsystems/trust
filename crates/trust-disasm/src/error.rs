// trust-disasm error types
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

/// Errors that can occur during instruction decoding.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum DisasmError {
    /// Not enough bytes to decode an instruction.
    #[error("insufficient bytes: need {needed}, have {available}")]
    InsufficientBytes { needed: usize, available: usize },

    /// The encoding does not match any known instruction.
    #[error("unknown instruction encoding: 0x{encoding:08x} at 0x{address:x}")]
    UnknownEncoding { encoding: u32, address: u64 },

    /// A reserved or unallocated encoding was encountered.
    #[error("unallocated encoding: 0x{encoding:08x} at 0x{address:x}")]
    UnallocatedEncoding { encoding: u32, address: u64 },

    /// AArch64 barrier option is architectural but outside the proof-grade
    /// named barrier boundary modeled by this decoder.
    #[error(
        "unsupported AArch64 barrier option 0x{option:x}: encoding 0x{encoding:08x} at 0x{address:x}; proof-grade barrier decode supports only named DMB/DSB LD/ST/full options and ISB SY"
    )]
    UnsupportedAarch64BarrierOption { encoding: u32, address: u64, option: u8 },
}
