// trust-lift error types
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt;

use thiserror::Error;

/// Proof-mode context for structured lifting errors.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LiftProofMode {
    /// Semantic lifting proof mode.
    SemanticLift,
    /// CFG recovery proof mode.
    Cfg,
}

impl fmt::Display for LiftProofMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SemanticLift => f.write_str("semantic lift proof mode"),
            Self::Cfg => f.write_str("CFG proof mode"),
        }
    }
}

/// Errors that can occur during binary lifting.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum LiftError {
    /// Binary parsing support was not compiled into this crate.
    #[error("binary parser support is not enabled; enable the `elf` or `macho` feature")]
    BinaryParserUnavailable,

    /// Binary parsing failed (requires `macho` or `elf` feature).
    #[cfg(any(feature = "macho", feature = "elf"))]
    #[error("binary parse error: {0}")]
    Parse(#[from] trust_binary_parse::ParseError),

    /// Binary parsing failed (generic message without binary-parse features).
    #[cfg(not(any(feature = "macho", feature = "elf")))]
    #[error("binary parse error: {0}")]
    Parse(String),

    /// Unsupported ELF machine type for lifting.
    #[error("unsupported ELF machine type: 0x{0:x}")]
    UnsupportedMachine(u16),

    /// Unsupported binary format for lifting.
    #[error("unsupported binary format for lifting: {format} ({reason})")]
    UnsupportedBinaryFormat {
        /// Binary format name.
        format: &'static str,
        /// Why the format is not supported by this lifter.
        reason: &'static str,
    },

    /// Instruction decoding failed at the given address.
    #[error("disassembly error at 0x{address:x}: {source}")]
    Disasm { address: u64, source: trust_disasm::DisasmError },

    /// No text section found in the binary.
    #[error("no text section found in binary")]
    NoTextSection,

    /// The requested entry point is outside the text section.
    #[error("entry point 0x{entry:x} is outside text section [0x{text_start:x}..0x{text_end:x})")]
    EntryOutOfBounds { entry: u64, text_start: u64, text_end: u64 },

    /// The parsed binary did not report an entry point.
    #[error("binary has no entry point; choose functions by address, name, or all functions")]
    NoBinaryEntryPoint,

    /// Function selection resolved to no candidate functions.
    #[error("no functions selected for binary lifting")]
    NoFunctionsSelected,

    /// No function found at the given address.
    #[error("no function found at address 0x{0:x}")]
    NoFunctionAtAddress(u64),

    /// No function symbol found with the requested name.
    #[error("no function symbol named `{0}`")]
    NoFunctionNamed(String),

    /// SSA construction failed.
    #[error("SSA construction error: {0}")]
    Ssa(String),

    /// Instruction semantics were unsupported or unavailable.
    #[error("SSA construction error: {mode}: {message}")]
    UnsupportedSemantics { mode: LiftProofMode, message: String },

    /// A semantic effect cannot be represented in the current TrustIr layout.
    #[error("SSA construction error: {mode}: {message}")]
    UnsupportedEffect { mode: LiftProofMode, message: String },

    /// Recovered or semantic control flow could not be resolved.
    #[error("SSA construction error: {mode}: {message}")]
    UnresolvedControlFlow { mode: LiftProofMode, message: String },

    /// A referenced CFG successor is missing from the recovered CFG.
    #[error("SSA construction error: {mode}: {message}")]
    MissingSuccessor { mode: LiftProofMode, message: String },

    /// The recovered CFG shape cannot be represented by the current lifting IR.
    #[error("SSA construction error: {mode}: {message}")]
    UnrepresentableCfg { mode: LiftProofMode, message: String },

    /// Block contained no instructions after decoding.
    #[error("empty block at address 0x{address:x}")]
    EmptyBlock { address: u64 },
}
