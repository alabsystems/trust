// Reassigned-parameter SOUNDNESS regression — real trustc MIR.
// `SemOperand::Var(idx)` = ENTRY-TIME param, so a NON-LOOP recognizer that consumes a
// REASSIGNED param would read the wrong value. These pin the fail-closed guard.
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
pub fn reassign_id(mut x: u64) -> u64 { x = x + 1; x }   // MUST DECLINE (returns x+1, not entry x)
pub fn clean_id(x: u64) -> u64 { x }                     // positive control: certifies
