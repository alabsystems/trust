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

/// Emits the whole `Effect` variant census — [`Effect::VARIANT_NAMES`] and
/// [`Effect::variant_name`] — from ONE list of variant identifiers.
///
/// SINGLE-SOURCED, NOT ASSERTED. The name table and the match that produces
/// those names are expanded from the same tokens, so "the table says one thing
/// and the code says another" is not a mistake that can be written down. This
/// replaces a `const` assertion against `core::mem::variant_count::<Effect>()`,
/// which only DETECTED that drift after the fact and cost the crate an unstable
/// `#![feature(variant_count)]` — an unstable feature this crate cannot afford,
/// because it is reachable from `rustc_codegen_trust_cg` and therefore sits in
/// the compiler's own build graph.
///
/// The generated `match` is an ordinary exhaustive match with NO wildcard arm,
/// written in the crate that DEFINES `Effect` (where `#[non_exhaustive]` is
/// inert), so it keeps exactly the property the hand-written match had: a
/// fourteenth variant that is not censused is `cargo build` error E0004 in the
/// library itself, not merely in a test, and never a silent default. The
/// converse mistake — a name in this list that the enum does not have — is
/// E0599 pointing at the offending line of the list. Both directions are
/// MEASURED, not asserted; see [`Effect::VARIANT_NAMES`].
macro_rules! declare_effect_census {
    ($($variant:ident),+ $(,)?) => {
        impl Effect {
            /// EVERY `Effect` variant name, in declaration order.
            ///
            /// This is the CENSUS every consumer of the effect surface is
            /// measured against. A consumer that handles some variants ITSELF
            /// (rather than forwarding them to a fail-closed threader) is
            /// protected only by enumerating them correctly, so each such
            /// consumer carries a test that walks this list and requires a
            /// declared, MEASURED disposition for every entry — see
            /// `effect_variant_census` in this crate's tests and
            /// `f_every_effect_variant_has_a_measured_gate_disposition` in
            /// `trust-cg-bridge`.
            ///
            /// The list cannot drift from the enum, and the enforcement is a
            /// chain in which every link is a hard failure:
            ///
            /// 1. This list and [`Effect::variant_name`]'s match are expanded
            ///    from ONE token list by `declare_effect_census!`, so a name
            ///    here that no arm produces — or an arm producing a name that
            ///    is not here — is UNREPRESENTABLE rather than merely
            ///    detected. Nothing checkable-only-by-sampling guards the
            ///    count, and nothing unstable is required to hold it.
            /// 2. That match is EXHAUSTIVE with no wildcard arm, in the crate
            ///    that DEFINES `Effect`, so a fourteenth variant is `cargo
            ///    build` error E0004 in the library itself. There is exactly
            ///    one OTHER way to silence that E0004 — pasting rustc's own
            ///    `help:` arm into the macro body rather than extending the
            ///    list — and `deny(unreachable_patterns)` on the generated
            ///    match makes that a hard error too, because such an arm is
            ///    expanded once per census entry. So the only way through is to
            ///    add the variant to the census list, which extends this table
            ///    in the same edit, by construction.
            /// 3. `effect_variant_census` (tests) then requires the sample set
            ///    to cover this list exactly, so extending the list without
            ///    MEASURING the new variant's disposition in each consumer
            ///    fails the test.
            ///
            /// Step 1 is not decoration. It is what makes the "hurried author"
            /// path safe: the edit that resolves E0004 is the same edit that
            /// censuses the variant, so the earlier failure mode — E0004
            /// resolved, name table left short, census silently passing with an
            /// uncensused variant present — no longer has a spelling.
            ///
            /// MEASURED, 2026-08-10, by injecting a fourteenth variant:
            /// `cargo build -p trust-machine-sem --lib` reported THREE E0004s —
            /// this match, `ConcreteState::apply_effect`, and
            /// `ConcreteState::apply_effect_with_eval_state`. Adding the
            /// identifier to the census list (the laziest resolution this
            /// construction admits) cleared this one and extended
            /// `VARIANT_NAMES` in the same edit; giving the concrete oracle
            /// fail-closed arms then built the library clean, and
            /// `effect_variant_census` failed on coverage naming the injected
            /// variant — link 3 doing its job. Removing the census entry while
            /// leaving the enum variant out is E0599 on the census line.
            ///
            /// The bypass in step 2 is MEASURED too, and it is why the `deny` is
            /// there. Injecting the fourteenth variant AND pasting rustc's
            /// suggested arm inside the macro repetition — which silenced the
            /// census with only a warning before the `deny` — now reports
            /// `error: unreachable pattern` alongside the remaining E0004s.
            /// Duplicating an entry in the census list is likewise
            /// `error: unreachable pattern` rather than the runtime test
            /// failure it used to be.
            pub const VARIANT_NAMES: &'static [&'static str] =
                &[$(stringify!($variant)),+];

            /// The name of this effect's variant, for diagnostics.
            ///
            /// EXHAUSTIVE BY CONSTRUCTION — there is deliberately no wildcard
            /// arm and no fallback string. A fourteenth `Effect` variant does
            /// not silently report itself under a generic label; it fails to
            /// compile. The returned name is an element of
            /// [`Effect::VARIANT_NAMES`] by construction, not by test: both
            /// come from the same list.
            //
            // `deny(unreachable_patterns)` is LOAD-BEARING, not hygiene. It
            // closes the one bypass the single-source list would otherwise
            // leave: rustc's own `help:` for the E0004 below prints an arm to
            // paste in, and pasting it INSIDE this repetition silences the
            // error while leaving the census list — and therefore
            // `VARIANT_NAMES` — short. Expanded 13 times, such an arm is
            // unreachable after the first, so denying the lint turns that
            // paste into a hard error instead of a warning. It also makes a
            // DUPLICATED entry in the census list a compile error rather than
            // a runtime test failure.
            #[deny(unreachable_patterns)]
            #[must_use]
            pub fn variant_name(&self) -> &'static str {
                match self {
                    $( Effect::$variant { .. } => stringify!($variant), )+
                }
            }
        }
    };
}

// THE CENSUS. One list, in declaration order. Adding an `Effect` variant
// without adding it here is E0004 in the generated `variant_name`; adding it
// here without adding it to the enum is E0599 on that line. Once it compiles,
// add a row to
// `effect_variant_census` (trust-machine-sem tests) and to the gate-disposition
// table (`f_every_effect_variant_has_a_measured_gate_disposition`,
// trust-cg-bridge) declaring what each consumer does with it.
declare_effect_census! {
    RegWrite,
    SpWrite,
    MemWrite,
    MemRead,
    FlagUpdate,
    Branch,
    ConditionalBranch,
    Call,
    Return,
    FpRegWrite,
    Aarch64SyncBoundary,
    Aarch64AtomicAccess,
    PcUpdate,
}
