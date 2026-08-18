// dead_code audit: crate-level suppression removed
//! trust-disasm: Multi-architecture instruction decoder
//!
//! # BEFORE YOU CHANGE THE AARCH64 DECODER
//!
//! ```text
//! crates/trust-disasm/harness/gate.sh --fast     # ~30 s, before every commit
//! crates/trust-disasm/harness/gate.sh            # ~40 min, before landing
//! ```
//!
//! Widening what this decoder accepts widens what the output gate can reach
//! Proven on. Four soundness families have been found here one at a time, each
//! after the previous was declared closed — a `1u64 << 64` overflow in the
//! bitmask decoder, unvalidated reserved fields, CONSTRAINED UNPREDICTABLE
//! operand aliasing, a discarded `Effect::PcUpdate` — and every one was a word
//! this decoder ACCEPTED and the CPU REFUSES. A mnemonic-level differential
//! cannot see that class: it compares NAMES, and both aliasing and
//! reserved-field words can carry correct names.
//!
//! `harness/native-invariant` executes all 2^32 words and holds the recorded
//! result (0 violations, exhaustive). `harness/native-semantic` then asks the
//! harder question — whether the word DOES what was certified. Newly decoding a
//! form with no correct semantics behind it turns a refusal into a wrong
//! answer, which is strictly worse; the differential is what catches it.
//! `harness/README.md` is the operating note.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

pub mod aarch64;
pub mod arch;
pub(crate) mod error;
pub mod instruction;
pub mod opcode;
pub mod operand;
pub mod x86_64;

pub use arch::{Arch, Decoder};
pub use error::DisasmError;
pub use instruction::{ControlFlow, Instruction};
pub use opcode::Opcode;
pub use operand::{Condition, Operand, Register, ShiftType};

/// Convenience: decode a single AArch64 instruction from bytes at a given address.
pub fn decode_aarch64(bytes: &[u8], address: u64) -> Result<Instruction, DisasmError> {
    let decoder = aarch64::Aarch64Decoder::new();
    decoder.decode(bytes, address)
}

/// Convenience: decode a single x86-64 instruction from bytes at a given address.
pub fn decode_x86_64(bytes: &[u8], address: u64) -> Result<Instruction, DisasmError> {
    let decoder = x86_64::X86_64Decoder::new();
    decoder.decode(bytes, address)
}
