// trust-bmc configuration types
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Configuration for trust_mc library verification.
//!
//! `TrustMcConfig` controls BMC depth, timeout, and solver behavior.
//! `DiagConfig` controls how trust_mc diagnostics are emitted during verification.

use serde::{Deserialize, Serialize};

use crate::result::TrustMcProofMode;

/// Configuration for trust_mc verification.
///
/// Controls BMC depth, timeout, solver path, and diagnostic behavior.
///
/// The current struct still carries the legacy BMC-depth field because the
/// compatibility subprocess bridge is SMT-LIB/BMC-shaped. The proof mode that
/// produced a result is carried by `TrustMcResult::proof_mode`.
/// Matches the `TrustMcConfig` signature from the Pipeline v2 design.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrustMcConfig {
    /// BMC unrolling depth. Higher values explore more execution paths
    /// but increase solving time. Default: 100.
    pub bmc_depth: u32,

    /// Timeout in milliseconds for the solver. Default: 30,000 (30s).
    pub timeout_ms: u64,

    /// Path to the trust_mc binary for subprocess mode.
    /// If `None`, probes `TRUST_MC_PATH` env var then `PATH`.
    pub solver_path: Option<String>,

    /// Extra arguments passed to the trust_mc solver.
    pub solver_args: Vec<String>,

    /// Diagnostic configuration controlling how trust_mc messages are handled.
    pub diagnostics: DiagConfig,

    /// Whether to request proof certificates from the solver.
    pub produce_proofs: bool,

    /// Whether to request counterexample models on SAT results.
    pub produce_models: bool,

    /// Whether to use adaptive BMC depth based on formula complexity.
    pub adaptive_depth: bool,

    /// Proof mode requested from trust_mc.
    ///
    /// SMT-LIB compatibility input currently supports ordinary BMC and
    /// finite-acyclic BMC. CHC/PDR requests fail closed until native artifacts
    /// for those modes are available.
    #[serde(default)]
    pub proof_mode: TrustMcProofMode,
}

impl Default for TrustMcConfig {
    fn default() -> Self {
        Self {
            bmc_depth: 100,
            timeout_ms: 30_000,
            solver_path: None,
            solver_args: vec!["-smt2".to_string(), "-in".to_string()],
            diagnostics: DiagConfig::default(),
            produce_proofs: false,
            produce_models: true,
            adaptive_depth: false,
            proof_mode: TrustMcProofMode::Bmc,
        }
    }
}

impl TrustMcConfig {
    /// Create a new config with default settings.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Set the BMC unrolling depth.
    #[must_use]
    pub fn with_bmc_depth(mut self, depth: u32) -> Self {
        self.bmc_depth = depth;
        self
    }

    /// Set the timeout in milliseconds.
    #[must_use]
    pub fn with_timeout(mut self, timeout_ms: u64) -> Self {
        self.timeout_ms = timeout_ms;
        self
    }

    /// Set an explicit solver path.
    #[must_use]
    pub fn with_solver_path(mut self, path: impl Into<String>) -> Self {
        self.solver_path = Some(path.into());
        self
    }

    /// Set the diagnostic configuration.
    #[must_use]
    pub fn with_diagnostics(mut self, diagnostics: DiagConfig) -> Self {
        self.diagnostics = diagnostics;
        self
    }

    /// Enable or disable proof certificate production.
    #[must_use]
    pub fn with_proofs(mut self, produce: bool) -> Self {
        self.produce_proofs = produce;
        self
    }

    /// Enable or disable adaptive BMC depth.
    #[must_use]
    pub fn with_adaptive_depth(mut self, enabled: bool) -> Self {
        self.adaptive_depth = enabled;
        self
    }

    /// Set the requested trust_mc proof mode.
    #[must_use]
    pub fn with_proof_mode(mut self, proof_mode: TrustMcProofMode) -> Self {
        self.proof_mode = proof_mode;
        self
    }
}

/// Controls how trust_mc diagnostic messages are handled during verification.
///
/// In subprocess mode, diagnostics come from stderr. In direct mode (Phase 2),
/// diagnostics are intercepted from `span_err` / `span_warn` calls.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[derive(Default)]
pub enum DiagConfig {
    /// Suppress all diagnostic output (default for library use).
    #[default]
    Silent,

    /// Capture diagnostics into the `TrustMcResult::diagnostics` vector
    /// for programmatic consumption.
    Capture,

    /// Pass diagnostics through to stderr (useful for debugging).
    Passthrough,
}
