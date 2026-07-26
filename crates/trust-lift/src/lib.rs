//! trust-lift: Proof-producing binary lifter
//!
//! Lifts binary code into TrustIr functions with CFG recovery and SSA construction.
//! Pipeline: binary bytes -> disassembly -> basic block recovery -> CFG ->
//! SSA construction -> TrustIr functions.
//!
//! Each lifted TrustIr statement links back to its binary offset for proof annotation.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]
// dead_code audit: crate-level suppression removed

pub mod binary;
pub(crate) mod boundary;
pub(crate) mod calling_convention;
pub mod cfg;
pub(crate) mod cfg_builder;
pub(crate) mod error;
pub(crate) mod lifter;
pub mod semantic_lift;
pub(crate) mod ssa;
#[cfg(feature = "ay-verify")]
pub mod validation;

pub use binary::{
    BinaryFunctionSelection, BinaryLiftOptions, ExactReplayInstructionAttestation,
    ExactReplayInstructionWitness, ExactReplaySelectedImage, ExactReplaySliceAttestation,
    LiftedBinary, LiftedFunctionFailure, LiftedFunctionSeed, LiftedFunctionSeedSource,
    LiftedSourceMapping, LiftedSourceProvenance, LiftedSourceProvenanceStatus, lift_binary_to_trust_ir,
};
pub use boundary::FunctionBoundary;
pub use calling_convention::{CallingConvention, FunctionSignature};
pub use cfg::LiftedFunction;
pub use error::{LiftError, LiftProofMode};
pub use lifter::{LiftArch, Lifter, summarize_function_signature};
pub use semantic_lift::LocalLayout;
