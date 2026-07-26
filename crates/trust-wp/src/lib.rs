// dead_code audit: crate-level suppression removed
// trust-wp: tRustc integration boundary for trust_wp deductive verifier
//
// Target contract architecture:
// designs/2026-04-25-trust-contracts-first-class-target.md.
// Exposes trust-wp's deductive verification as a library API that Trust can call
// directly instead of shelling out to the CLI binary.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! # trust_wp
//!
//! Integration boundary for the trust_wp deductive verifier. This crate provides:
//!
//! - **Types**: `ContractSet`, `TrustWpResult`, `LoopInvariant` (standalone by default)
//! - **Trait**: `TrustWpBackend` for pluggable verification backends
//! - **CLI backend**: `CliBackend` compatibility bridge for non-tRustc runs
//! - **Native backend**: typed in-process trust_wp IR obligations with `trust-build`
//! - **Configuration**: `TrustWpConfig`, `DiagConfig` for controlling verification
//! - **Results**: `TrustWpResult`, `Verdict`, `FunctionVerdict` for structured output
//!
//! ## Architecture
//!
//! ```text
//! Trust compiler pass (TyCtxt, DefId)
//!          |
//!          v
//!   trust_wp  (this crate)
//!          |
//!          +--[trust-build]---> trust_wp in-process over TrustContractBundle
//!          |
//!          +--[default]-------> compatibility subprocess bridge
//!          |
//!          v
//!     TrustWpResult { verdict, function_verdicts, loop_invariants }
//! ```
//!
//! ## Feature Flags
//!
//! - `trust-build`: Enables direct tRustc `TyCtxt` integration. Target builds
//!   must use this path for first-class Trust contracts.
//!
//! ## Why standalone types?
//!
//! By default this crate defines standalone compatibility types without linking
//! trust_wp internals. With `trust-build`, it also links `trust-wp-core`/`trust-wp-ay`
//! and verifies typed `PureExpr` obligations in-process.

mod backend;
mod cli;
mod config;
mod contract;
mod error;
mod native;
mod result;
mod verifier_api;

pub use backend::TrustWpBackend;
pub use cli::CliBackend;
pub use config::{DiagConfig, TrustWpConfig};
pub use contract::{Contract, ContractKind, ContractSet};
pub use error::TrustWpLibError;
pub use native::{
    NativeContract, NativeContractBundle, NativeFunctionTarget, NativeLoopContract,
    NativeLoopContractRole, NativeResultBinding, NativeSnapshot, NativeSummaryRef,
    NativeTrustWpRequest, NativeTrustWpResult, NativeTrustWpStatus, NativeUnsupportedFeature,
    NativeUnsupportedKind, verify_native,
};
#[cfg(feature = "trust-build")]
pub use native::{NativePureBody, NativeTrustWpExpr, NativeTrustWpMir};
pub use result::{
    DiagLevel, DiagnosticMessage, FunctionVerdict, LoopInvariant, TrustWpResult, Verdict,
    VerificationCounts,
};
#[cfg(feature = "trust-build")]
pub use verifier_api::trust_wp_native_replay_metadata_entries_from_trust_ir_bundle;
pub use verifier_api::{
    TRUST_WP_ENGINE_NAME, TRUST_WP_NATIVE_NOT_WIRED, TrustWpVerificationEngine,
    TRUST_TRUST_WP_CLAIM_DIGEST_METADATA_KEY, TRUST_TRUST_WP_NATIVE_ORIGIN_METADATA_KEY,
    TRUST_TRUST_WP_NATIVE_REPLAY_METADATA_KEY, TRUST_TRUST_WP_NATIVE_REPLAY_REQUIRED_METADATA_KEYS,
    TRUST_TRUST_WP_NATIVE_SOLVER_METADATA_KEY, TRUST_TRUST_WP_NATIVE_SUMMARY_FACT_METADATA_KEY,
    TRUST_TRUST_WP_NATIVE_VERIFIER_METADATA_KEY, TRUST_TRUST_WP_PROOF_CONTEXT_METADATA_KEY,
    TRUST_TRUST_WP_TRUST_IR_OBLIGATION_SOURCE_METADATA_KEY, TRUST_TRUST_WP_TRUST_IR_SOURCE_SPAN_METADATA_KEY,
    is_trust_wp_owned_obligation_kind, trust_wp_owned_obligation_kinds,
};

/// Verify a function's contracts using trust-wp's deductive verification.
///
/// This is the high-level entry point matching the Pipeline v2 design:
/// ```text
/// let result = trust_wp::verify_with_contracts(
///     function_name, contracts, config,
/// );
/// ```
///
/// In compatibility builds, this delegates to the CLI backend. Target tRustc
/// builds must call trust-wp's verification context directly in-process with
/// `TyCtxt`, `DefId`, MIR, and `TrustContractBundle`.
///
/// # Arguments
///
/// * `function_name` - The fully qualified function name to verify
/// * `contracts` - The contract set (requires/ensures/invariants)
/// * `config` - Verification configuration (timeout, diagnostics)
///
/// # Errors
///
/// Returns `TrustWpLibError` if the subprocess fails or produces
/// unparseable output.
pub fn verify_with_contracts(
    function_name: &str,
    contracts: &ContractSet,
    config: &TrustWpConfig,
) -> Result<TrustWpResult, TrustWpLibError> {
    let backend = CliBackend::new(config);
    backend.verify(function_name, contracts)
}

/// Infer loop invariants for a function using trust_wp.
///
/// This is the lower-level API from the Pipeline v2 design. Returns
/// candidate loop invariants discovered by trust-wp's abstract interpretation.
///
/// In compatibility builds, this invokes trust_wp with `--infer-invariants` and
/// parses the output. Target tRustc builds call trust-wp's invariant inference
/// directly over MIR.
///
/// # Arguments
///
/// * `function_name` - The fully qualified function name
/// * `config` - Verification configuration
///
/// # Errors
///
/// Returns `TrustWpLibError` if invariant inference fails.
pub fn infer_loop_invariants(
    function_name: &str,
    config: &TrustWpConfig,
) -> Result<Vec<LoopInvariant>, TrustWpLibError> {
    let backend = CliBackend::new(config);
    backend.infer_invariants(function_name)
}
