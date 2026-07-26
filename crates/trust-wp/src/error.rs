// trust_wp error types
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Error types for the trust_wp tRustc integration boundary.

/// Errors from the trust_wp library integration.
#[derive(Debug, thiserror::Error)]
pub enum TrustWpLibError {
    /// The trust_wp binary was not found at the configured path or on PATH.
    #[error("trust-wp binary not found: {reason}")]
    BinaryNotFound {
        /// Details about where we looked.
        reason: String,
    },

    /// Failed to spawn the trust_wp subprocess.
    #[error("failed to spawn trust_wp subprocess: {0}")]
    SpawnFailed(#[from] std::io::Error),

    /// The subprocess exited with a non-zero code that indicates an internal error.
    #[error("trust-wp subprocess failed with exit code {code}: {stderr}")]
    SubprocessFailed {
        /// Exit code from the subprocess.
        code: i32,
        /// Captured stderr output.
        stderr: String,
    },

    /// Failed to parse trust-wp's output.
    #[error("failed to parse trust_wp output: {reason}")]
    ParseError {
        /// Details about what was unexpected.
        reason: String,
    },

    /// The verification timed out.
    #[error("trust-wp timed out after {timeout_ms}ms")]
    Timeout {
        /// The configured timeout that was exceeded.
        timeout_ms: u64,
    },

    /// Contract serialization error.
    #[error("contract serialization error: {reason}")]
    ContractError {
        /// Details about what failed.
        reason: String,
    },

    /// Configuration error.
    #[error("configuration error: {reason}")]
    ConfigError {
        /// Details about the invalid configuration.
        reason: String,
    },
}
