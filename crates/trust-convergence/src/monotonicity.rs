// trust-convergence/monotonicity.rs: Monotonicity policy enforcement.
//
// Defines policies for when proof frontier regressions should trigger rollback
// versus being tolerated (e.g., if net improvement is positive).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::{FrontierDelta, ProofFrontier};

/// Policy for enforcing monotonic improvement in the proof frontier.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
#[derive(Default)]
pub enum MonotonicityPolicy {
    /// Any regression in static proofs or increase in failures triggers rollback.
    #[default]
    Strict,
    /// Net improvement is acceptable: more static proofs gained than lost,
    /// and total failures did not increase.
    Relaxed,
}

/// Result of a monotonicity check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MonotonicityResult {
    /// Whether the frontier satisfies the policy.
    pub is_monotonic: bool,
    /// The policy that was applied.
    pub policy: MonotonicityPolicy,
    /// The delta that was evaluated.
    pub delta: FrontierDelta,
    /// Human-readable reason if monotonicity was violated.
    pub violation_reason: Option<String>,
}

impl MonotonicityResult {
    /// True if rollback should be triggered.
    #[must_use]
    pub fn should_rollback(&self) -> bool {
        !self.is_monotonic
    }
}

/// Check whether transitioning from `previous` to `current` satisfies the given policy.
#[must_use]
pub fn check_monotonicity(
    previous: &ProofFrontier,
    current: &ProofFrontier,
    policy: MonotonicityPolicy,
) -> MonotonicityResult {
    let delta = current.delta_from(previous);

    match policy {
        MonotonicityPolicy::Strict => check_strict(&delta),
        MonotonicityPolicy::Relaxed => check_relaxed(&delta),
    }
}

fn check_strict(delta: &FrontierDelta) -> MonotonicityResult {
    let policy = MonotonicityPolicy::Strict;

    if delta.statically_proved_delta() < 0 {
        return MonotonicityResult {
            is_monotonic: false,
            policy,
            delta: *delta,
            violation_reason: Some(format!(
                "static proofs decreased by {}",
                -delta.statically_proved_delta()
            )),
        };
    }

    if delta.failed > 0 {
        return MonotonicityResult {
            is_monotonic: false,
            policy,
            delta: *delta,
            violation_reason: Some(format!("failures increased by {}", delta.failed)),
        };
    }

    if delta.unresolved_delta() > 0 {
        return MonotonicityResult {
            is_monotonic: false,
            policy,
            delta: *delta,
            violation_reason: Some(format!(
                "unresolved obligations increased by {}",
                delta.unresolved_delta()
            )),
        };
    }

    MonotonicityResult { is_monotonic: true, policy, delta: *delta, violation_reason: None }
}

fn check_relaxed(delta: &FrontierDelta) -> MonotonicityResult {
    let policy = MonotonicityPolicy::Relaxed;

    // Under relaxed policy, we allow local regressions as long as:
    // 1. Net static proofs did not decrease
    // 2. Total failures did not increase
    let net_proved = delta.statically_proved_delta();
    let failures_increased = delta.failed > 0;

    if net_proved < 0 {
        return MonotonicityResult {
            is_monotonic: false,
            policy,
            delta: *delta,
            violation_reason: Some(format!("net static proofs decreased by {}", -net_proved)),
        };
    }

    if failures_increased {
        return MonotonicityResult {
            is_monotonic: false,
            policy,
            delta: *delta,
            violation_reason: Some(format!("failures increased by {}", delta.failed)),
        };
    }

    MonotonicityResult { is_monotonic: true, policy, delta: *delta, violation_reason: None }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn frontier(
        trusted: u32,
        certified: u32,
        runtime_checked: u32,
        failed: u32,
        unknown: u32,
    ) -> ProofFrontier {
        ProofFrontier { trusted, certified, runtime_checked, failed, unknown }
    }

    // -- Strict policy tests --

    #[test]
    fn test_strict_improvement_is_monotonic() {
        let prev = frontier(3, 0, 1, 1, 0);
        let curr = frontier(4, 0, 0, 1, 0);
        let result = check_monotonicity(&prev, &curr, MonotonicityPolicy::Strict);
        assert!(result.is_monotonic);
        assert!(!result.should_rollback());
        assert!(result.violation_reason.is_none());
    }

    #[test]
    fn test_strict_stable_is_monotonic() {
        let prev = frontier(3, 1, 0, 0, 1);
        let curr = frontier(3, 1, 0, 0, 1);
        let result = check_monotonicity(&prev, &curr, MonotonicityPolicy::Strict);
        assert!(result.is_monotonic);
        assert!(!result.should_rollback());
    }

    #[test]
    fn test_strict_fewer_proofs_triggers_rollback() {
        let prev = frontier(5, 0, 0, 0, 0);
        let curr = frontier(4, 0, 0, 0, 1);
        let result = check_monotonicity(&prev, &curr, MonotonicityPolicy::Strict);
        assert!(!result.is_monotonic);
        assert!(result.should_rollback());
        assert!(result.violation_reason.expect("reason").contains("static proofs decreased"));
    }

    #[test]
    fn test_strict_more_failures_triggers_rollback() {
        let prev = frontier(3, 0, 0, 0, 2);
        let curr = frontier(3, 0, 0, 1, 1);
        let result = check_monotonicity(&prev, &curr, MonotonicityPolicy::Strict);
        assert!(!result.is_monotonic);
        assert!(result.should_rollback());
        assert!(result.violation_reason.expect("reason").contains("failures increased"));
    }

    #[test]
    fn test_strict_more_unresolved_triggers_rollback() {
        let prev = frontier(3, 0, 0, 0, 1);
        let curr = frontier(3, 0, 1, 0, 1);
        let result = check_monotonicity(&prev, &curr, MonotonicityPolicy::Strict);
        assert!(!result.is_monotonic);
        assert!(result.should_rollback());
        assert!(result.violation_reason.expect("reason").contains("unresolved"));
    }

    // -- Relaxed policy tests --

    #[test]
    fn test_relaxed_net_improvement_is_monotonic() {
        // Trusted went down 1, but certified went up 2 => net +1 static proofs.
        // Unknown increased by 1 but failures didn't increase.
        let prev = frontier(5, 0, 0, 1, 0);
        let curr = frontier(4, 2, 1, 1, 0);
        let result = check_monotonicity(&prev, &curr, MonotonicityPolicy::Relaxed);
        assert!(result.is_monotonic);
        assert!(!result.should_rollback());
    }

    #[test]
    fn test_relaxed_net_decrease_triggers_rollback() {
        let prev = frontier(5, 1, 0, 0, 0);
        let curr = frontier(3, 1, 0, 0, 2);
        let result = check_monotonicity(&prev, &curr, MonotonicityPolicy::Relaxed);
        assert!(!result.is_monotonic);
        assert!(result.should_rollback());
        assert!(result.violation_reason.expect("reason").contains("net static proofs decreased"));
    }

    #[test]
    fn test_relaxed_more_failures_triggers_rollback() {
        let prev = frontier(3, 0, 0, 0, 2);
        let curr = frontier(4, 0, 0, 1, 0);
        let result = check_monotonicity(&prev, &curr, MonotonicityPolicy::Relaxed);
        assert!(!result.is_monotonic);
        assert!(result.should_rollback());
        assert!(result.violation_reason.expect("reason").contains("failures increased"));
    }

    #[test]
    fn test_relaxed_stable_is_monotonic() {
        let prev = frontier(3, 1, 0, 0, 1);
        let curr = frontier(3, 1, 0, 0, 1);
        let result = check_monotonicity(&prev, &curr, MonotonicityPolicy::Relaxed);
        assert!(result.is_monotonic);
    }

    #[test]
    fn test_relaxed_unresolved_increase_ok_if_no_failure_increase() {
        // Under relaxed, unresolved can increase if proofs are stable and failures aren't up.
        let prev = frontier(3, 0, 0, 0, 1);
        let curr = frontier(3, 0, 1, 0, 1);
        let result = check_monotonicity(&prev, &curr, MonotonicityPolicy::Relaxed);
        assert!(result.is_monotonic);
    }

    // -- Default --

    #[test]
    fn test_default_policy_is_strict() {
        assert_eq!(MonotonicityPolicy::default(), MonotonicityPolicy::Strict);
    }

    // -- Result accessors --

    #[test]
    fn test_monotonicity_result_delta_preserved() {
        let prev = frontier(5, 0, 0, 0, 0);
        let curr = frontier(3, 0, 0, 0, 2);
        let result = check_monotonicity(&prev, &curr, MonotonicityPolicy::Strict);
        assert_eq!(result.delta.trusted, -2);
        assert_eq!(result.delta.unknown, 2);
        assert_eq!(result.policy, MonotonicityPolicy::Strict);
    }
}
