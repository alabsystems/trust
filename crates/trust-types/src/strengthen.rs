// trust-types/strengthen.rs: Spec synthesis types for strengthen phase
//
// Used by the strengthen phase of the prove-strengthen-backprop loop to record
// synthesized temporal specifications and candidate code changes that would
// help discharged failed liveness verification conditions.
//
// Part of #56
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::formula::{FairnessConstraint, LivenessProperty};

/// A suggested specification synthesized from failed verification conditions.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SpecSuggestion {
    /// Unique identifier for the synthesized spec.
    pub id: String,
    /// The temporal property being suggested.
    pub property: LivenessProperty,
    /// Confidence score in the range [0.0, 1.0].
    pub confidence: f64,
    /// Evidence explaining why the spec was suggested.
    pub evidence: Vec<String>,
    /// The recognized code pattern that motivated the suggestion.
    pub pattern: PatternKind,
    /// Candidate source change that could make the spec hold.
    pub code_fix: Option<CodeFix>,
}

impl SpecSuggestion {
    /// Construct a new spec suggestion.
    #[must_use]
    pub fn new(
        id: impl Into<String>,
        property: LivenessProperty,
        confidence: f64,
        evidence: Vec<String>,
        pattern: PatternKind,
        code_fix: Option<CodeFix>,
    ) -> Self {
        Self { id: id.into(), property, confidence, evidence, pattern, code_fix }
    }
}

/// Recognized program patterns that imply common liveness obligations.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum PatternKind {
    /// Connection pool with idle, active, and drained states.
    ConnectionPool,
    /// Retry loop with attempt, backoff, and terminal states.
    RetryLoop,
    /// Producer-consumer pipeline with buffered work.
    ProducerConsumer,
    /// Request-response workflow with pending requests.
    RequestResponse,
    /// Circuit breaker with closed, open, and half-open states.
    CircuitBreaker,
    /// User-defined pattern name.
    Custom { name: String },
}

impl PatternKind {
    /// Construct the canonical connection-pool pattern.
    #[must_use]
    pub fn connection_pool() -> Self {
        Self::ConnectionPool
    }

    /// Construct the canonical retry-loop pattern.
    #[must_use]
    pub fn retry_loop() -> Self {
        Self::RetryLoop
    }

    /// Construct the canonical producer-consumer pattern.
    #[must_use]
    pub fn producer_consumer() -> Self {
        Self::ProducerConsumer
    }

    /// Construct the canonical request-response pattern.
    #[must_use]
    pub fn request_response() -> Self {
        Self::RequestResponse
    }

    /// Construct the canonical circuit-breaker pattern.
    #[must_use]
    pub fn circuit_breaker() -> Self {
        Self::CircuitBreaker
    }

    /// Construct a custom pattern with a user-defined name.
    #[must_use]
    pub fn custom(name: impl Into<String>) -> Self {
        Self::Custom { name: name.into() }
    }

    /// Human-readable explanation of this pattern and its expected liveness.
    #[must_use]
    pub fn description(&self) -> String {
        match self {
            PatternKind::ConnectionPool => {
                "connection pool: idle/active/drained states; should eventually return to idle"
                    .to_string()
            }
            PatternKind::RetryLoop => {
                "retry loop: attempt/backoff/success-failure states; attempts should lead to success"
                    .to_string()
            }
            PatternKind::ProducerConsumer => {
                "producer-consumer: producing/buffered/consuming states; consume usually needs strong fairness"
                    .to_string()
            }
            PatternKind::RequestResponse => {
                "request-response: request/processing/response states; requests should lead to responses"
                    .to_string()
            }
            PatternKind::CircuitBreaker => {
                "circuit breaker: closed/open/half_open states; should eventually return to closed"
                    .to_string()
            }
            PatternKind::Custom { name } => format!("custom pattern: {name}"),
        }
    }
}

/// A suggested code modification that could help satisfy a synthesized spec.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CodeFix {
    /// Human-readable explanation of the change.
    pub description: String,
    /// Structured representation of the proposed change.
    pub fix_kind: FixKind,
    /// State or transition to adjust.
    pub target_state: String,
    /// Confidence score in the range [0.0, 1.0].
    pub confidence: f64,
}

impl CodeFix {
    /// Construct a new code-fix suggestion.
    #[must_use]
    pub fn new(
        description: impl Into<String>,
        fix_kind: FixKind,
        target_state: impl Into<String>,
        confidence: f64,
    ) -> Self {
        Self {
            description: description.into(),
            fix_kind,
            target_state: target_state.into(),
            confidence,
        }
    }
}

/// A structured kind of code change synthesized by strengthen.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum FixKind {
    /// Add a timeout to a waiting or blocked state.
    AddTimeout { timeout_ms: u64 },
    /// Add bounded retry with exponential or linear backoff.
    AddRetryWithBackoff { max_retries: u32, initial_delay_ms: u64 },
    /// Add a circuit breaker to prevent cascading failures.
    AddCircuitBreaker { failure_threshold: u32, recovery_timeout_ms: u64 },
    /// Strengthen the model with an explicit fairness requirement.
    AddFairnessAnnotation { constraint: FairnessConstraint },
    /// User-defined structured fix.
    Custom { description: String },
}

impl FixKind {
    /// Construct an `AddTimeout` fix.
    #[must_use]
    pub fn add_timeout(timeout_ms: u64) -> Self {
        Self::AddTimeout { timeout_ms }
    }

    /// Construct an `AddRetryWithBackoff` fix.
    #[must_use]
    pub fn add_retry_with_backoff(max_retries: u32, initial_delay_ms: u64) -> Self {
        Self::AddRetryWithBackoff { max_retries, initial_delay_ms }
    }

    /// Construct an `AddCircuitBreaker` fix.
    #[must_use]
    pub fn add_circuit_breaker(failure_threshold: u32, recovery_timeout_ms: u64) -> Self {
        Self::AddCircuitBreaker { failure_threshold, recovery_timeout_ms }
    }

    /// Construct an `AddFairnessAnnotation` fix.
    #[must_use]
    pub fn add_fairness_annotation(constraint: FairnessConstraint) -> Self {
        Self::AddFairnessAnnotation { constraint }
    }

    /// Construct a custom fix description.
    #[must_use]
    pub fn custom(description: impl Into<String>) -> Self {
        Self::Custom { description: description.into() }
    }
}

/// Output from one strengthen iteration over failed verification conditions.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct StrengthenResult {
    /// New spec suggestions produced in this iteration.
    pub suggestions: Vec<SpecSuggestion>,
    /// Whether strengthen produced no new information.
    pub converged: bool,
    /// Monotonic strengthen iteration count.
    pub iteration: u32,
}

impl StrengthenResult {
    /// Construct a strengthen result and infer convergence from the suggestion set.
    #[must_use]
    pub fn new(suggestions: Vec<SpecSuggestion>, iteration: u32) -> Self {
        let converged = suggestions.is_empty();
        Self { suggestions, converged, iteration }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn request_response_property() -> LivenessProperty {
        LivenessProperty {
            name: "request_eventually_responds".into(),
            operator: crate::TemporalOperator::LeadsTo,
            predicate: "request".into(),
            consequent: Some("response".into()),
            fairness: vec![FairnessConstraint::Weak {
                action: "process_request".into(),
                vars: vec!["requests".into(), "responses".into()],
            }],
        }
    }

    #[test]
    fn test_spec_suggestion_construction_and_serialization_roundtrip() {
        let fix = CodeFix::new(
            "add timeout to unblock stuck request processing",
            FixKind::add_timeout(500),
            "processing",
            0.8,
        );
        let suggestion = SpecSuggestion::new(
            "request_eventually_responds",
            request_response_property(),
            0.92,
            vec![
                "observed request state without terminal response".into(),
                "matched request/response control-flow pattern".into(),
            ],
            PatternKind::request_response(),
            Some(fix),
        );

        let json = serde_json::to_string(&suggestion).expect("serialize suggestion");
        let roundtrip: SpecSuggestion =
            serde_json::from_str(&json).expect("deserialize suggestion");

        assert_eq!(roundtrip, suggestion);
    }

    #[test]
    fn test_pattern_kind_description() {
        assert_eq!(
            PatternKind::connection_pool().description(),
            "connection pool: idle/active/drained states; should eventually return to idle"
        );
        assert_eq!(
            PatternKind::retry_loop().description(),
            "retry loop: attempt/backoff/success-failure states; attempts should lead to success"
        );
        assert_eq!(
            PatternKind::producer_consumer().description(),
            "producer-consumer: producing/buffered/consuming states; consume usually needs strong fairness"
        );
        assert_eq!(
            PatternKind::request_response().description(),
            "request-response: request/processing/response states; requests should lead to responses"
        );
        assert_eq!(
            PatternKind::circuit_breaker().description(),
            "circuit breaker: closed/open/half_open states; should eventually return to closed"
        );
        assert_eq!(PatternKind::custom("timer wheel").description(), "custom pattern: timer wheel");
    }

    #[test]
    fn test_strengthen_result_converged_detection() {
        let converged = StrengthenResult::new(Vec::new(), 3);
        assert!(converged.converged);
        assert!(converged.suggestions.is_empty());

        let suggestion = SpecSuggestion::new(
            "conn_pool_eventually_idle",
            LivenessProperty {
                name: "conn_pool_eventually_idle".into(),
                operator: crate::TemporalOperator::Eventually,
                predicate: "idle".into(),
                consequent: None,
                fairness: vec![],
            },
            0.87,
            vec!["matched connection-pool state machine".into()],
            PatternKind::connection_pool(),
            None,
        );
        let not_converged = StrengthenResult::new(vec![suggestion], 4);

        assert!(!not_converged.converged);
        assert_eq!(not_converged.iteration, 4);
        assert_eq!(not_converged.suggestions.len(), 1);
    }

    #[test]
    fn test_code_fix_construction() {
        let fairness =
            FairnessConstraint::Strong { action: "consume".into(), vars: vec!["buffer".into()] };
        let fix = CodeFix::new(
            "require strong fairness on consume to avoid starvation",
            FixKind::add_fairness_annotation(fairness.clone()),
            "consuming",
            0.76,
        );

        assert_eq!(
            fix,
            CodeFix {
                description: "require strong fairness on consume to avoid starvation".into(),
                fix_kind: FixKind::AddFairnessAnnotation { constraint: fairness },
                target_state: "consuming".into(),
                confidence: 0.76,
            }
        );
    }
}
