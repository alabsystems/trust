// dead_code audit: crate-level suppression removed
// `contracts_internals` is an internal compiler feature used by the
// `contract_requires { ... }` syntax in concrete.rs. The
// `internal_features` lint is suppressed because this is precisely
// the use case (verification IR using compiler-internal contracts).
#![allow(internal_features)]
#![feature(contracts_internals)]
#![feature(register_tool)]
#![register_tool(trust)]
//! trust-machine-sem: ISA semantics formalization
//!
//! Maps decoded instructions to their logical effects on machine state.
//! Used by translation validation to verify compiled output matches source
//! semantics.
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
pub use x86_64::X86_64Semantics;
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

#[cfg(test)]
mod tests;

pub fn trigger_trust_verifier_overflow(x: u64, y: u64) -> u64 {
    x + y
}
