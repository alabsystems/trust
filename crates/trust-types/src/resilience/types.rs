// trust-types/resilience/types: Resilience analysis type definitions
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::{BinOp, BlockId, SourceSpan};

// ---------------------------------------------------------------------------
// Existing types: FailureMode, ExternalDependency, FailureModel, etc.
// ---------------------------------------------------------------------------

/// How an external dependency can fail.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum FailureMode {
    /// Network/service timeout.
    Timeout,
    /// Explicit error response (HTTP 5xx, DB error, etc.).
    Error,
    /// Service unreachable (connection refused, DNS failure).
    Unavailable,
    /// Partial failure (e.g., partial write, partial read).
    Partial,
    /// Custom failure mode from user annotation.
    Custom(String),
}

impl std::fmt::Display for FailureMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FailureMode::Timeout => write!(f, "timeout"),
            FailureMode::Error => write!(f, "error"),
            FailureMode::Unavailable => write!(f, "unavailable"),
            FailureMode::Partial => write!(f, "partial"),
            FailureMode::Custom(s) => write!(f, "{s}"),
        }
    }
}

/// An external dependency detected in MIR (network call, file I/O, DB query).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExternalDependency {
    /// Name of the external service or resource (e.g., "redis", "postgres", "s3").
    pub name: String,
    /// Failure modes this dependency can exhibit.
    pub failure_modes: Vec<FailureMode>,
    /// MIR block where the external call occurs.
    pub block: BlockId,
    /// Source location of the call.
    pub span: SourceSpan,
    /// The function call path that was matched.
    pub call_path: String,
}

/// A failure model describing which dependencies can fail and how.
///
/// This is the input for resilience verification: for each combination of
/// failure states, verify the code handles it without panicking.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct FailureModel {
    /// External dependencies detected in the function.
    pub dependencies: Vec<ExternalDependency>,
    /// Function this model was extracted from.
    pub function: String,
}

impl FailureModel {
    /// Create an empty failure model for a function.
    pub fn new(function: impl Into<String>) -> Self {
        Self { dependencies: Vec::new(), function: function.into() }
    }

    /// Returns true if no external dependencies were detected.
    pub fn is_empty(&self) -> bool {
        self.dependencies.is_empty()
    }

    /// Total number of failure combinations to check.
    ///
    /// Each dependency can be in one of (1 + failure_modes.len()) states:
    /// healthy, or any of its failure modes.
    pub fn failure_combination_count(&self) -> usize {
        self.dependencies.iter().map(|dep| 1 + dep.failure_modes.len()).product()
    }

    /// Generate all failure scenarios as a list of `(dep_index, Option<FailureMode>)` tuples.
    ///
    /// Each scenario is a Vec where entry `i` is `None` (healthy) or
    /// `Some(mode)` (failing with that mode) for dependency `i`.
    pub fn failure_scenarios(&self) -> Vec<Vec<Option<FailureMode>>> {
        if self.dependencies.is_empty() {
            return vec![vec![]];
        }

        let mut scenarios = vec![vec![]];
        for dep in &self.dependencies {
            let mut next_scenarios = Vec::new();
            let mut modes: Vec<Option<FailureMode>> = vec![None]; // healthy
            modes.extend(dep.failure_modes.iter().map(|m| Some(m.clone())));

            for existing in &scenarios {
                for mode in &modes {
                    let mut scenario = existing.clone();
                    scenario.push(mode.clone());
                    next_scenarios.push(scenario);
                }
            }
            scenarios = next_scenarios;
        }
        scenarios
    }
}

/// Result of checking a single failure scenario for resilience.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResilienceCheckResult {
    /// The failure scenario that was checked (per-dependency failure mode).
    pub scenario: Vec<(String, Option<FailureMode>)>,
    /// Whether the code handles this scenario without panicking.
    pub is_resilient: bool,
    /// If not resilient, describes the problem (e.g., "unwrap on error path").
    pub violation: Option<String>,
    /// Block where the violation occurs (if any).
    pub violation_block: Option<BlockId>,
}

// ---------------------------------------------------------------------------
// ResilienceLevel, RecoveryStrategy, FaultAssumptions
// ---------------------------------------------------------------------------

/// The resilience level of a function or module.
///
/// Ordered from least resilient to most resilient. This classification
/// drives verification depth: higher levels require more proof obligations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ResilienceLevel {
    /// Function panics or aborts on any unexpected input or failure.
    /// No error handling; any fault is fatal.
    Fragile,
    /// Function handles some errors gracefully (returns Result/Option)
    /// but may still panic on edge cases (e.g., unchecked arithmetic).
    Tolerant,
    /// Function handles all anticipated failure modes, propagates errors,
    /// and has no panic paths. Suitable for production services.
    Hardened,
    /// Function tolerates arbitrary faults including Byzantine failures
    /// (non-deterministic, adversarial). Requires formal proof of
    /// correctness under fault injection.
    ByzantineFault,
}

impl std::fmt::Display for ResilienceLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ResilienceLevel::Fragile => write!(f, "fragile"),
            ResilienceLevel::Tolerant => write!(f, "tolerant"),
            ResilienceLevel::Hardened => write!(f, "hardened"),
            ResilienceLevel::ByzantineFault => write!(f, "byzantine-fault"),
        }
    }
}

/// Strategy for recovering from a detected fault.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum RecoveryStrategy {
    /// No recovery: propagate error to caller.
    Propagate,
    /// Retry the operation up to `max_retries` times.
    Retry { max_retries: u32 },
    /// Fall back to a default or cached value.
    Fallback,
    /// Use a circuit breaker: stop calling the dependency after
    /// `threshold` consecutive failures, reopen after `reset_timeout_ms`.
    CircuitBreaker { threshold: u32, reset_timeout_ms: u64 },
    /// Gracefully degrade by disabling the dependent feature.
    GracefulDegradation,
    /// Compensating transaction: undo partial side effects.
    Compensate,
}

impl std::fmt::Display for RecoveryStrategy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RecoveryStrategy::Propagate => write!(f, "propagate"),
            RecoveryStrategy::Retry { max_retries } => write!(f, "retry({})", max_retries),
            RecoveryStrategy::Fallback => write!(f, "fallback"),
            RecoveryStrategy::CircuitBreaker { threshold, reset_timeout_ms } => {
                write!(f, "circuit-breaker({}, {}ms)", threshold, reset_timeout_ms)
            }
            RecoveryStrategy::GracefulDegradation => write!(f, "graceful-degradation"),
            RecoveryStrategy::Compensate => write!(f, "compensate"),
        }
    }
}

/// Fault assumptions for a function: what faults it expects and how it recovers.
///
/// This is attached to a function during analysis and drives the verification
/// engine to inject the appropriate fault scenarios.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FaultAssumptions {
    /// The resilience level this function is designed to meet.
    pub target_level: ResilienceLevel,
    /// Which failure modes are tolerated (subset of all possible modes).
    pub tolerated_failures: Vec<FailureMode>,
    /// Recovery strategies for each tolerated failure mode.
    pub recovery_strategies: Vec<(FailureMode, RecoveryStrategy)>,
    /// Maximum acceptable latency increase under fault (in milliseconds).
    /// `None` means no latency constraint.
    pub max_latency_ms: Option<u64>,
    /// Whether the function must remain idempotent under fault recovery
    /// (e.g., retries must not cause duplicate side effects).
    pub idempotency_required: bool,
}

impl Default for FaultAssumptions {
    fn default() -> Self {
        Self {
            target_level: ResilienceLevel::Tolerant,
            tolerated_failures: Vec::new(),
            recovery_strategies: Vec::new(),
            max_latency_ms: None,
            idempotency_required: false,
        }
    }
}

impl FaultAssumptions {
    /// Create fault assumptions targeting a specific resilience level.
    pub fn with_level(level: ResilienceLevel) -> Self {
        Self { target_level: level, ..Default::default() }
    }

    /// Add a tolerated failure mode with its recovery strategy.
    pub fn tolerate(&mut self, mode: FailureMode, strategy: RecoveryStrategy) {
        self.tolerated_failures.push(mode.clone());
        self.recovery_strategies.push((mode, strategy));
    }

    /// Returns true if a given failure mode is tolerated.
    pub fn tolerates(&self, mode: &FailureMode) -> bool {
        self.tolerated_failures.contains(mode)
    }

    /// Get the recovery strategy for a specific failure mode.
    pub fn recovery_for(&self, mode: &FailureMode) -> Option<&RecoveryStrategy> {
        self.recovery_strategies.iter().find(|(m, _)| m == mode).map(|(_, s)| s)
    }

    /// Classify the actual resilience level based on the analysis report.
    ///
    /// Compares the function's actual behavior (from `ResilienceReport`) against
    /// the target level and returns the achieved level.
    pub fn classify_achieved_level(report: &ResilienceReport) -> ResilienceLevel {
        if !report.panic_paths.is_empty() {
            return ResilienceLevel::Fragile;
        }
        if !report.unchecked_arithmetic.is_empty() {
            return ResilienceLevel::Tolerant;
        }
        let has_swallowing = report
            .error_handling
            .iter()
            .any(|e| matches!(e, ErrorHandlingPattern::Swallowing { .. }));
        if has_swallowing {
            return ResilienceLevel::Tolerant;
        }
        if report.failure_model.is_empty() {
            return ResilienceLevel::Hardened;
        }
        ResilienceLevel::Hardened
    }
}

// ---------------------------------------------------------------------------
// FaultModel, ResilienceProperty, ErrorHandlingPattern, PanicPath, etc.
// ---------------------------------------------------------------------------

/// How a function responds to faults at the system level.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum FaultModel {
    /// Function panics on any error (unwrap, expect, panic!, assert!).
    PanicOnError,
    /// Function returns an error type (Result::Err, Option::None).
    ReturnError,
    /// Function silently ignores errors (swallows Result, uses unwrap_or_default).
    SilentCorruption,
    /// Function exhibits non-deterministic behavior under faults (e.g., races, unsafe).
    ByzantineFault,
}

impl std::fmt::Display for FaultModel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FaultModel::PanicOnError => write!(f, "panic-on-error"),
            FaultModel::ReturnError => write!(f, "return-error"),
            FaultModel::SilentCorruption => write!(f, "silent-corruption"),
            FaultModel::ByzantineFault => write!(f, "byzantine-fault"),
        }
    }
}

/// Algebraic properties of a function that affect resilience.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ResilienceProperty {
    /// Calling the function twice with the same input produces the same result.
    Idempotent,
    /// Order of arguments does not matter (e.g., set union, addition).
    Commutative,
    /// The function preserves a partial order (output >= input in some measure).
    Monotonic,
    /// After a crash, the function leaves the system in a consistent state.
    CrashConsistent,
}

impl std::fmt::Display for ResilienceProperty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ResilienceProperty::Idempotent => write!(f, "idempotent"),
            ResilienceProperty::Commutative => write!(f, "commutative"),
            ResilienceProperty::Monotonic => write!(f, "monotonic"),
            ResilienceProperty::CrashConsistent => write!(f, "crash-consistent"),
        }
    }
}

/// How a function handles errors from callees.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ErrorHandlingPattern {
    /// Error is propagated to the caller (using `?` or explicit match + return).
    Propagation { call_path: String, block: BlockId },
    /// Error is swallowed (result discarded, unwrap_or_default, map_err to unit).
    Swallowing { call_path: String, block: BlockId },
    /// Error is transformed into a different error type.
    Transforming { call_path: String, block: BlockId },
    /// Error triggers a panic (unwrap, expect, panic!).
    Panicking { call_path: String, block: BlockId },
}

/// A detected panic path in the function.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PanicPath {
    /// Block containing the panic-inducing terminator or call.
    pub block: BlockId,
    /// Source location.
    pub span: SourceSpan,
    /// Human-readable description (e.g., "unwrap call", "assert failure", "overflow check").
    pub description: String,
    /// The kind of panic.
    pub kind: PanicKind,
}

/// What kind of panic was detected.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum PanicKind {
    /// Explicit unwrap() call.
    Unwrap,
    /// Explicit expect() call.
    Expect,
    /// Overflow assert from checked arithmetic.
    Overflow,
    /// Bounds check assert (index out of bounds).
    BoundsCheck,
    /// Division by zero.
    DivisionByZero,
    /// Explicit panic!() or unreachable!().
    ExplicitPanic,
    /// Other assert failure.
    Assert,
}

/// A detected unchecked arithmetic operation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct UncheckedArithmetic {
    /// Block containing the operation.
    pub block: BlockId,
    /// The binary operation.
    pub op: BinOp,
    /// Source location.
    pub span: SourceSpan,
    /// Description of the risk.
    pub description: String,
}

/// Full resilience analysis report for a function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResilienceReport {
    /// Function that was analyzed.
    pub function: String,
    /// Inferred fault model for the function.
    pub fault_model: FaultModel,
    /// Detected resilience properties.
    pub properties: Vec<ResilienceProperty>,
    /// Risk score from 0.0 (safe) to 1.0 (high risk).
    pub risk_score: f64,
    /// Human-readable recommendations for improving resilience.
    pub recommendations: Vec<String>,
    /// All detected panic paths.
    pub panic_paths: Vec<PanicPath>,
    /// All detected unchecked arithmetic operations.
    pub unchecked_arithmetic: Vec<UncheckedArithmetic>,
    /// Error handling patterns detected in the function.
    pub error_handling: Vec<ErrorHandlingPattern>,
    /// External dependency failure model (from existing analysis).
    pub failure_model: FailureModel,
}
