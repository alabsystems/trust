// trust_wp configuration types
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Configuration for trust_wp library verification.
//!
//! `TrustWpConfig` controls timeout, solver behavior, and diagnostics.
//! `DiagConfig` controls how trust_wp diagnostics are emitted during verification.

use serde::{Deserialize, Serialize};

/// Configuration for trust_wp deductive verification.
///
/// Controls timeout, solver path, diagnostic behavior, and proof options.
/// Matches the `TrustWpConfig` signature from the Pipeline v2 design.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrustWpConfig {
    /// Timeout in milliseconds for the verification. Default: 60,000 (60s).
    pub timeout_ms: u64,

    /// Path to the trust_wp binary for subprocess mode.
    /// If `None`, only an explicitly-configured `TRUST_WP_PATH` env var is
    /// honored; `$PATH` discovery is deliberately disabled (fail-closed).
    pub solver_path: Option<String>,

    /// Extra arguments passed to the trust_wp CLI.
    pub solver_args: Vec<String>,

    /// Diagnostic configuration controlling how trust_wp messages are handled.
    pub diagnostics: DiagConfig,

    /// Whether to request proof certificates from the verifier.
    pub produce_proofs: bool,

    /// Memory tracking precision level.
    /// Maps to trust-wp-core's `TrackLevel`: "auto", "reg", "ptr", "mem".
    pub track_level: String,

    /// Whether to enable the structured result protocol (TRUST_WP_RESULT_PROTOCOL=1).
    pub structured_results: bool,

    /// Whether to attempt loop invariant inference.
    pub infer_invariants: bool,
}

impl Default for TrustWpConfig {
    fn default() -> Self {
        Self {
            timeout_ms: 60_000,
            solver_path: None,
            solver_args: Vec::new(),
            diagnostics: DiagConfig::default(),
            produce_proofs: false,
            track_level: "auto".to_string(),
            structured_results: true,
            infer_invariants: false,
        }
    }
}

impl TrustWpConfig {
    /// Create a new config with default settings.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
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

    /// Set the memory tracking precision level.
    #[must_use]
    pub fn with_track_level(mut self, level: impl Into<String>) -> Self {
        self.track_level = level.into();
        self
    }

    /// Enable or disable loop invariant inference.
    #[must_use]
    pub fn with_infer_invariants(mut self, enabled: bool) -> Self {
        self.infer_invariants = enabled;
        self
    }
}

/// Controls how trust_wp diagnostic messages are handled during verification.
///
/// In subprocess mode, diagnostics come from stderr. In direct mode (Phase 2),
/// diagnostics are intercepted from rustc's diagnostic system.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[derive(Default)]
pub enum DiagConfig {
    /// Suppress all diagnostic output (default for library use).
    #[default]
    Silent,

    /// Capture diagnostics into the `TrustWpResult::diagnostics` vector
    /// for programmatic consumption.
    Capture,

    /// Pass diagnostics through to stderr (useful for debugging).
    Passthrough,
}
