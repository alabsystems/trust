// trust-router/error.rs: errors shared across the crate's solver lanes.
//
// A variant here records the structured cause instead of a formatted string,
// so a caller can attribute a failure to a solver and a phase without parsing
// prose. An error only one module raises stays in that module.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use thiserror::Error;

/// Trust: Error type for solver subprocess invocation (smtlib, trust-mc, trust-vc,
/// trust-wp, clean backends).
///
/// Each variant captures the structured cause rather than a format!() string.
/// The solver name is included in every variant so callers can attribute errors
/// without carrying additional context.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum SolverProcessError {
    /// The solver binary was not found on disk or PATH.
    #[error("{solver} binary not found: {hint}")]
    BinaryNotFound { solver: &'static str, hint: String },

    /// Failed to spawn the solver subprocess.
    #[error("failed to spawn {solver} at {path}: {source}")]
    SpawnFailed { solver: &'static str, path: String, source: std::io::Error },

    /// Failed to write to the solver's stdin.
    #[error("failed to write to {solver} stdin: {source}")]
    StdinWriteFailed { solver: &'static str, source: std::io::Error },

    /// Failed to read the solver's output (stdout/stderr).
    #[error("failed to read {solver} output: {source}")]
    OutputReadFailed { solver: &'static str, source: std::io::Error },

    /// The solver wrote diagnostic output to stderr, indicating an error.
    #[error("{solver} stderr: {stderr}")]
    SolverStderr { solver: &'static str, stderr: String },

    /// The solver process crashed (closed stdout unexpectedly).
    #[error("{solver} process crashed: {detail}")]
    ProcessCrashed { solver: &'static str, detail: String },

    /// The solver timed out waiting for a response.
    #[error("{solver} timeout: {detail}")]
    Timeout { solver: &'static str, detail: String },

    /// The solver reader thread disconnected (thread panicked or was killed).
    #[error("{solver} disconnected: {detail}")]
    Disconnected { solver: &'static str, detail: String },

    /// The solver's model output exceeded the size limit.
    #[error("{solver} model output too large: {bytes} bytes exceeds {limit} byte limit")]
    ModelOutputTooLarge { solver: &'static str, bytes: usize, limit: usize },
}
