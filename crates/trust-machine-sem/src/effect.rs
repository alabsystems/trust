// trust-machine-sem: Instruction effects
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_disasm::operand::Condition;
use trust_types::Formula;

/// AArch64 synchronization-boundary instruction class.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum Aarch64SyncBoundaryKind {
    /// Data Memory Barrier.
    DataMemoryBarrier,
    /// Data Synchronization Barrier.
    DataSynchronizationBarrier,
    /// Instruction Synchronization Barrier.
    InstructionSynchronizationBarrier,
    /// Clear local exclusive monitor.
    ClearExclusiveMonitor,
}

/// AArch64 shareability or locality scope for a synchronization boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum Aarch64SyncScope {
    OuterShareable,
    NonShareable,
    InnerShareable,
    FullSystem,
    Local,
}

/// Access class ordered by an AArch64 synchronization boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum Aarch64SyncOrdering {
    Loads,
    Stores,
    LoadsAndStores,
    InstructionStream,
    None,
}

/// AArch64 atomic memory access class.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum Aarch64AtomicAccessKind {
    Load,
    Store,
}

/// AArch64 per-access memory ordering.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum Aarch64AtomicOrdering {
    Acquire,
    Release,
}

/// A single semantic effect produced by an instruction.
///
/// An instruction's semantics is a sequence of `Effect` values that, when
/// applied in order, transform the pre-state into the post-state.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum Effect {
    /// Write a value to a general-purpose register (index 0-30).
    /// Writes to index 31 (ZR) are silently discarded.
    RegWrite {
        /// Register index (0-30).
        index: u8,
        /// Width in bits (32 or 64).
        width: u32,
        /// The new value (a Formula of sort `BitVec(width)`).
        value: Formula,
    },

    /// Write a value to the stack pointer.
    SpWrite {
        /// The new SP value (64-bit bitvector).
        value: Formula,
    },

    /// Write a value to memory at a symbolic address.
    MemWrite {
        /// Address (64-bit bitvector).
        address: Formula,
        /// Value to store.
        value: Formula,
        /// Width of the store in bytes (1, 2, 4, or 8).
        width_bytes: u32,
    },

    /// Read a value from memory at a symbolic address (load into register
    /// is modeled as MemRead + RegWrite, but the read itself is an effect
    /// for memory-ordering purposes).
    MemRead {
        /// Address (64-bit bitvector).
        address: Formula,
        /// Width of the load in bytes.
        width_bytes: u32,
    },

    /// Update the NZCV condition flags.
    FlagUpdate { n: Formula, z: Formula, c: Formula, v: Formula },

    /// Unconditional branch to a target address.
    Branch {
        /// Target address (64-bit bitvector).
        target: Formula,
    },

    /// Conditional branch: taken if `condition` holds in the current flags.
    ConditionalBranch {
        /// The condition to evaluate.
        condition: Condition,
        /// Target if condition is true.
        target: Formula,
        /// Fallthrough address if condition is false.
        fallthrough: Formula,
    },

    /// Function call (BL/BLR): branch + link register write.
    Call {
        /// Target address.
        target: Formula,
        /// Return address written to X30.
        return_addr: Formula,
    },

    /// Return (branch to X30).
    Return {
        /// Target address (typically the value of X30).
        target: Formula,
    },

    /// Write a value to a SIMD/FP register (V0-V31).
    /// The width indicates the active portion (32 for S, 64 for D, 128 for Q).
    /// Upper bits beyond width are zeroed (AArch64 semantics).
    FpRegWrite {
        /// FP register index (0-31).
        index: u8,
        /// Width in bits (32, 64, or 128).
        width: u32,
        /// The new value.
        value: Formula,
    },

    /// AArch64 barrier/synchronization boundary.
    ///
    /// This is an ordering/monitor effect, not a proof that adjacent memory
    /// operations synchronize correctly. Atomic/exclusive load-store
    /// instructions still require separate monitor/status proof consumption.
    Aarch64SyncBoundary {
        kind: Aarch64SyncBoundaryKind,
        scope: Aarch64SyncScope,
        ordering: Aarch64SyncOrdering,
        clears_exclusive_monitor: bool,
        raw_option: Option<u8>,
    },

    /// AArch64 per-access atomic ordering metadata.
    ///
    /// This carries the acquire/release fact for a single memory access. It
    /// does not by itself mutate scalar data state; LDAR/STLR also emit the
    /// ordinary MemRead/RegWrite or MemWrite effects for their data plane.
    /// Exclusive forms remain unsupported until monitor/status semantics are
    /// modeled and proof-consumed.
    Aarch64AtomicAccess {
        kind: Aarch64AtomicAccessKind,
        ordering: Aarch64AtomicOrdering,
        address: Formula,
        width_bytes: u32,
        exclusive: bool,
    },

    /// Update the program counter.
    PcUpdate {
        /// New PC value.
        value: Formula,
    },
}
