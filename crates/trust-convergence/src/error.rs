// trust-convergence: Top-level errors for live convergence tracking APIs.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

/// Top-level error type for the trust-convergence crate.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum ConvergenceError {
    /// Invalid configuration (e.g., zero thresholds, contradictory limits).
    #[error("invalid configuration: {0}")]
    InvalidConfig(String),

    /// The convergence tracker has no observations to report on.
    #[error("no observations recorded")]
    NoObservations,

    /// A stagnation threshold was violated.
    #[error(
        "stagnation detected: {consecutive_stale} consecutive stale iterations (threshold: {threshold})"
    )]
    Stagnation { consecutive_stale: usize, threshold: usize },
}
