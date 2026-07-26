// trust-bmc error types
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Error types for the trust_mc tRustc integration boundary.

/// Errors from the trust_mc library integration.
#[derive(Debug, thiserror::Error)]
pub enum TrustMcLibError {
    /// The trust_mc binary was not found at the configured path or on PATH.
    #[error("trust-mc binary not found: {reason}")]
    BinaryNotFound {
        /// Details about where we looked.
        reason: String,
    },

    /// Failed to spawn the trust_mc subprocess.
    #[error("failed to spawn trust_mc subprocess: {0}")]
    SpawnFailed(#[from] std::io::Error),

    /// Failed to write to the solver's stdin.
    #[error("failed to write SMT-LIB2 script to trust_mc stdin: {reason}")]
    InputError {
        /// Details about the write failure.
        reason: String,
    },

    /// The solver produced output that could not be parsed.
    #[error("failed to parse trust_mc output: {reason}")]
    ParseError {
        /// Details about what was unexpected.
        reason: String,
    },

    /// The solver timed out.
    #[error("trust-mc timed out after {timeout_ms}ms")]
    Timeout {
        /// The configured timeout that was exceeded.
        timeout_ms: u64,
    },

    /// An encoding error occurred (e.g., unsupported MIR construct).
    #[error("encoding error: {reason}")]
    EncodingError {
        /// Details about what failed to encode.
        reason: String,
    },

    /// Configuration error.
    #[error("configuration error: {reason}")]
    ConfigError {
        /// Details about the invalid configuration.
        reason: String,
    },
}
