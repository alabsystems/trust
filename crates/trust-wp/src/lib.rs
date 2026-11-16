// dead_code audit: crate-level suppression removed
// trust-wp: standalone compatibility boundary for the trust_wp deductive verifier
//
// Target contract architecture:
// designs/2026-04-25-trust-contracts-first-class-target.md.
// Preserves standalone TrustWP compatibility APIs and historical wire readers.
// This legacy facade grants no proof authority. The full verifier's native
// body-WP alternative uses first-party trust-wp-lib directly.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! # trust_wp
//!
//! Integration boundary for the trust_wp deductive verifier. This crate provides:
//!
//! - **Types**: `ContractSet`, `TrustWpResult`, `LoopInvariant` (standalone by default)
//! - **Trait**: `TrustWpBackend` for pluggable verification backends
//! - **CLI backend**: `CliBackend` for explicit standalone compatibility runs
//! - **Historical inspector**: typed TrustWP IR decoding with `trust-build`
//! - **Configuration**: `TrustWpConfig`, `DiagConfig` for controlling verification
//! - **Results**: `TrustWpResult`, `Verdict`, `FunctionVerdict` for structured output
//!
//! ## Architecture
//!
//! ```text
//! Explicit compatibility caller
//!          |
//!          +--[trust-build]---> historical typed replay inspector
//!          |
//!          +--[explicit API]--> standalone compatibility subprocess bridge
//!
//! This facade: no compiler/full-verifier route; always Unsupported
//! Native body-WP: first-party trust-wp-lib via trust-router
//! ```
//!
//! ## Feature Flags
//!
//! - `trust-build`: Enables historical typed replay inspection. It does not
//!   enable a compiler/full-verifier authority route.
//!
//! ## Why standalone types?
//!
//! By default this crate defines standalone compatibility types without linking
//! trust_wp internals. With `trust-build`, it also links `trust-wp-core`
//! and retains historical typed replay inspection. The full-verification engine
//! advertises zero TrustWP-owned kinds: the formula-less RustHorn `&mut`
//! give-back record is not a dischargeable proof obligation.
//! Consequently neither this CLI compatibility API nor historical replay
//! artifacts are compiler/full-verifier proof authority.

mod backend;
mod cli;
mod config;
mod contract;
mod error;
mod result;
mod verifier_api;

pub use backend::TrustWpBackend;
pub use cli::CliBackend;
pub use config::{DiagConfig, TrustWpConfig};
pub use contract::{Contract, ContractKind, ContractSet};
pub use error::TrustWpLibError;
pub use result::{
    DiagLevel, DiagnosticMessage, FunctionVerdict, LoopInvariant, TrustWpResult, Verdict,
    VerificationCounts,
};
pub use verifier_api::{
    TRUST_TRUST_WP_CLAIM_DIGEST_METADATA_KEY, TRUST_TRUST_WP_NATIVE_ORIGIN_METADATA_KEY,
    TRUST_TRUST_WP_NATIVE_REPLAY_METADATA_KEY, TRUST_TRUST_WP_NATIVE_REPLAY_REQUIRED_METADATA_KEYS,
    TRUST_TRUST_WP_NATIVE_SOLVER_METADATA_KEY, TRUST_TRUST_WP_NATIVE_SUMMARY_FACT_METADATA_KEY,
    TRUST_TRUST_WP_NATIVE_VERIFIER_METADATA_KEY, TRUST_TRUST_WP_PROOF_CONTEXT_METADATA_KEY,
    TRUST_TRUST_WP_TRUST_IR_OBLIGATION_SOURCE_METADATA_KEY,
    TRUST_TRUST_WP_TRUST_IR_SOURCE_SPAN_METADATA_KEY, TRUST_WP_ENGINE_NAME,
    TRUST_WP_NATIVE_NOT_WIRED, TrustWpVerificationEngine, is_trust_wp_owned_obligation_kind,
    trust_wp_owned_obligation_kinds,
};
#[cfg(feature = "trust-build")]
pub use verifier_api::{
    trust_wp_native_formula_from_trust_spec,
    trust_wp_native_replay_metadata_entries_from_trust_ir_bundle,
};

/// Run the standalone trust-wp CLI compatibility protocol.
///
/// This is the high-level entry point matching the Pipeline v2 design:
/// ```text
/// let result = trust_wp::verify_with_contracts(
///     function_name, contracts, config,
/// );
/// ```
///
/// **Standalone callers only — the compiler route must not use this.** It
/// delegates to the subprocess `CliBackend` and derives a verdict from the
/// parsed `TRUST_WP_RESULT:v1` text protocol. The R4 flip (2026-08-20) retired
/// this lane from every compiler-reachable verdict path: trustc's per-VC
/// router uses its canonical constant evaluator for formula-only requests;
/// body-aware WP uses the independent typed TrustIR engine in the full verifier.
/// A trust-router test pins that its per-VC route is invariant to `TRUST_WP_PATH`.
/// This API is not registered as a compiler or full-verifier backend. It may be
/// used by explicit compatibility tooling, but its parsed subprocess verdict is
/// never proof authority. Compiler/full-verifier paths do not call this API;
/// the public TrustWP adapter reports no capability. This API contains no
/// latent or pending compiler capability grant.
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
/// This explicit compatibility API invokes trust_wp with `--infer-invariants`
/// and parses the output. The target compiler does not use it as verdict
/// authority.
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
