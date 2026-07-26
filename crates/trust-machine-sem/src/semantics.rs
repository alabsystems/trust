// trust-machine-sem: Semantics trait
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_disasm::Instruction;

use crate::effect::Effect;
use crate::error::SemError;
use crate::state::MachineState;

/// Maps a decoded instruction to its logical effects on machine state.
///
/// Implementations are ISA-specific (one per architecture). The trait
/// takes a pre-state and an instruction and returns the list of effects
/// that the instruction produces.
pub trait Semantics {
    /// Compute the semantic effects of `insn` given `state`.
    ///
    /// The returned effects, applied in order, transform `state` into the
    /// post-state.
    ///
    /// # Errors
    ///
    /// Returns `SemError` if the instruction uses an unsupported opcode or
    /// has an unexpected operand structure.
    fn effects(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError>;
}
