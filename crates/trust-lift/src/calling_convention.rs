// trust-lift: Calling convention and recovered signature types
//
// Shared data types for recovered calling convention and signature metadata.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_disasm::operand::Register;
use trust_types::Ty;

/// Detected calling convention.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CallingConvention {
    /// AArch64 Procedure Call Standard (ARM 64-bit).
    Aapcs64,
    /// System V AMD64 ABI (x86-64 Linux/macOS).
    SysV64,
    /// Microsoft x64 calling convention (x86-64 Windows).
    Win64,
    /// Could not determine calling convention.
    Unknown,
}

/// Recovered function signature combining arg_count, return type,
/// calling convention, frame size, and callee-saved register info.
#[derive(Debug, Clone)]
pub struct FunctionSignature {
    /// Detected calling convention.
    pub convention: CallingConvention,
    /// Number of arguments (from register usage analysis).
    pub arg_count: usize,
    /// Return type (from return value analysis).
    pub return_ty: Ty,
    /// Stack frame size in bytes (from SP modifications in prologue).
    pub frame_size: u64,
    /// Whether this is a leaf function (no outgoing calls).
    pub is_leaf: bool,
    /// Callee-saved registers spilled in the prologue.
    pub callee_saved: Vec<Register>,
    /// Default ABI return register name, recorded as metadata only.
    pub return_register: Option<String>,
    /// Default ABI argument register names for this architecture/convention.
    pub argument_registers: Vec<String>,
    /// ABI argument registers read before local definition in the entry block.
    pub observed_argument_registers: Vec<String>,
    /// Human-readable provenance for recovered signature facts.
    pub provenance: Vec<String>,
}
