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

    /// An encoding that IS architecturally allocated and names a real
    /// instruction, but whose distinguishing semantics this decoder declines to
    /// model.
    ///
    /// Kept DISTINCT from [`Self::UnallocatedEncoding`], which means "no
    /// instruction has this encoding". Conflating the two would make the
    /// diagnostic claim the CPU would reject a word the CPU executes happily,
    /// and would hide the real reason a function was refused. Same spirit as
    /// [`Self::UnsupportedAarch64BarrierOption`]: architectural, but outside the
    /// proof-grade boundary.
    ///
    /// Refusing is the point. Each instruction in this class has a near
    /// neighbour the decoder DOES model, and the difference between them is not
    /// representable here — so decoding it as the neighbour would present a
    /// distinct instruction to the gate under the neighbour's semantics.
    #[error(
        "unmodeled AArch64 instruction {mnemonic}: encoding 0x{encoding:08x} at 0x{address:x}; {reason}"
    )]
    UnmodeledAarch64Instruction {
        encoding: u32,
        address: u64,
        mnemonic: &'static str,
        reason: &'static str,
    },

    /// An encoding whose FIELDS are all architecturally valid but whose OPERANDS
    /// name a register combination the architecture declares CONSTRAINED
    /// UNPREDICTABLE.
    ///
    /// Kept DISTINCT from every other variant here, because it is a distinct
    /// claim. [`Self::UnallocatedEncoding`] says "no instruction has this
    /// encoding" — false, the encoding is allocated and objdump names it.
    /// [`Self::UnmodeledAarch64Instruction`] says "a real instruction this
    /// decoder declines to model" — also not it, because there is no single
    /// instruction here to model: the architecture permits the implementation
    /// to choose from `{UNDEF, NOP, UNKNOWN result, writeback suppressed}`, so
    /// no definite result exists to be right about.
    ///
    /// This is the shape a FIELD check cannot catch. Every bit pattern is legal;
    /// it is the coincidence of two register NUMBERS that puts the word out of
    /// bounds. The decoders validate fields; this validates operand constraints.
    ///
    /// The evidence for each rule is recorded in
    /// `aarch64::constrained_unpredictable_tests`: the assembler refuses to
    /// encode the source form, and native execution answers SIGILL for the
    /// load/store families.
    #[error(
        "CONSTRAINED UNPREDICTABLE operands in {mnemonic}: encoding 0x{encoding:08x} at 0x{address:x}; {constraint}"
    )]
    ConstrainedUnpredictableOperands {
        encoding: u32,
        address: u64,
        mnemonic: &'static str,
        constraint: &'static str,
    },
}
