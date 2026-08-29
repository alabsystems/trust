// dead_code audit: crate-level suppression removed
// `contracts_internals` is an internal compiler feature used by the
// `contract_requires { ... }` syntax in concrete.rs. The
// `internal_features` lint is suppressed because this is precisely
// the use case (verification IR using compiler-internal contracts).
#![allow(internal_features)]
#![feature(contracts_internals)]
#![feature(register_tool)]
// The effect-surface census (effect.rs) needs NO unstable feature. It used to
// spend `#![feature(variant_count)]` on a const assertion that
// `Effect::VARIANT_NAMES` was as long as the enum; that list and
// `Effect::variant_name`'s wildcard-free match are now expanded from a single
// token list by `declare_effect_census!`, so drift is unrepresentable instead of
// asserted. That removed the only entry this crate needed on
// `CARGO_TRUST_ALLOW_FEATURES` for its own census — it does NOT make the crate
// feature-free: `contracts_internals` and `register_tool` above are still spent,
// and both are already on that list for other reasons.
#![register_tool(trust)]
//! trust-machine-sem: ISA semantics formalization
//!
//! Maps decoded instructions to their logical effects on machine state.
//! Used by translation validation to verify compiled output matches source
//! semantics.
//!
//! # BEFORE YOU CHANGE THIS CRATE
//!
//! ```text
//! crates/trust-disasm/harness/gate.sh --fast     # ~30 s, before every commit
//! crates/trust-disasm/harness/gate.sh            # ~40 min, before landing
//! ```
//!
//! The output gate does not merely require that an emitted word RUNS — it
//! re-derives the object's meaning from `Aarch64Semantics::effects` and proves a
//! theorem about THAT. A wrong effect list is a false Proven exactly as much as
//! an unexecutable word, and it is the quieter of the two: nothing faults,
//! nothing is refused, the answer is simply about a different instruction. Unit
//! tests cannot find that class; only executing the instruction on the hardware
//! and comparing the whole post-state can, and three live families were found
//! the day such a harness first existed.
//!
//! `crates/trust-disasm/harness/README.md` is the operating note: what to run,
//! what each failure means, and what the harnesses cannot see. The standing
//! rule when a divergence is found: **fix the semantics or REFUSE the form.**
//! Approximating onto a neighbouring value is never acceptable; refusing always
//! is.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

pub(crate) mod aarch64;
pub mod concrete;
pub(crate) mod effect;
pub(crate) mod error;
pub(crate) mod semantics;
pub(crate) mod state;
pub(crate) mod x86_64;

pub use aarch64::Aarch64Semantics;
// Trust: #564 — re-export condition_to_formula for semantic_lift branch wiring.
pub use aarch64::condition_to_formula;
pub use concrete::{ConcreteError, ConcreteFlags, ConcreteState, eval_condition};
pub use effect::{
    Aarch64AtomicAccessKind, Aarch64AtomicOrdering, Aarch64SyncBoundaryKind, Aarch64SyncOrdering,
    Aarch64SyncScope, Effect,
};
pub use error::SemError;
pub use semantics::Semantics;
pub use state::{Flags, MachineState};
pub use x86_64::X86_64Semantics;

#[cfg(test)]
mod tests;

pub fn trigger_trust_verifier_overflow(x: u64, y: u64) -> u64 {
    x + y
}
