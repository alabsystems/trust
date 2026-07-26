// Convergence tracking for the rewrite loop.
//
// The decision rule — when has the proof frontier converged, stalled, or gone
// backwards — is `trust-convergence`'s, not a second one written here. A loop
// that stops on a different rule than the crate that exists to define that rule
// is a loop whose reported "CONVERGED" means something the rest of the system
// does not agree with.
//
// What stays local is the shape the rewrite loop reports: this frontier is
// serialized into the loop's iteration record, and its three buckets are the
// vocabulary of `targo trust --rewrite` output.

use serde::Serialize;
use trust_convergence::{
    ConvergenceDecision, ConvergenceTracker as FrontierTracker, IterationSnapshot,
    ProofFrontier as TrackedFrontier, RegressionReason, StepVerdict,
};

use crate::types::{VerificationOutcome, VerificationResult};

/// How many consecutive identical frontiers mean the loop has converged.
const STABLE_ROUND_LIMIT: usize = 2;

/// Proof frontier snapshot for one iteration.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct ProofFrontier {
    pub(crate) proved: usize,
    pub(crate) failed: usize,
    pub(crate) unknown: usize,
}

impl ProofFrontier {
    pub(crate) fn from_results(results: &[VerificationResult]) -> Self {
        let proved = results.iter().filter(|r| r.outcome == VerificationOutcome::Proved).count();
        let failed = results.iter().filter(|r| r.outcome == VerificationOutcome::Failed).count();
        let unknown = results
            .iter()
            .filter(|r| r.outcome.is_inconclusive() || r.outcome.is_runtime_checked())
            .count();
        Self { proved, failed, unknown }
    }

    pub(crate) fn total(&self) -> usize {
        self.proved + self.failed + self.unknown
    }

    /// Project onto the tracker's five-bucket frontier.
    ///
    /// The rewrite loop only ever observes a compiler verdict, which cannot
    /// distinguish a kernel-certified row from a trusted one, so everything
    /// proved lands in one bucket; runtime-checked rows are already folded into
    /// `unknown` by `from_results` because the rewrite loop treats them as work
    /// still to do. Saturating conversion keeps a pathological count from
    /// wrapping into an apparent improvement.
    fn tracked(&self) -> TrackedFrontier {
        TrackedFrontier {
            trusted: 0,
            certified: u32::try_from(self.proved).unwrap_or(u32::MAX),
            runtime_checked: 0,
            failed: u32::try_from(self.failed).unwrap_or(u32::MAX),
            unknown: u32::try_from(self.unknown).unwrap_or(u32::MAX),
        }
    }
}

/// Decision after comparing two frontiers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum LoopDecision {
    /// Keep iterating, with a description of what happened.
    Continue { verdict: &'static str },
    /// Proof frontier converged (same results for `stable_rounds` iterations).
    Converged { stable_rounds: usize },
    /// Proof frontier regressed (more failures or fewer proofs).
    Regressed { reason: &'static str },
    /// Hit the iteration limit.
    IterationLimitReached,
}

/// Convergence tracker for the rewrite loop.
pub(crate) struct ConvergenceTracker {
    inner: FrontierTracker,
    observed: usize,
}

impl ConvergenceTracker {
    pub(crate) fn new(max_iterations: usize) -> Self {
        Self {
            inner: FrontierTracker::new(
                STABLE_ROUND_LIMIT,
                u32::try_from(max_iterations).unwrap_or(u32::MAX).max(1),
            ),
            observed: 0,
        }
    }

    /// Record a new frontier and return the convergence decision.
    pub(crate) fn observe(&mut self, frontier: ProofFrontier) -> LoopDecision {
        self.observed += 1;
        let iteration = u32::try_from(self.observed).unwrap_or(u32::MAX);
        let decision = self.inner.observe(IterationSnapshot::new(iteration, frontier.tracked()));
        match decision {
            ConvergenceDecision::Continue { verdict } if self.observed < 2 => {
                let _ = verdict;
                LoopDecision::Continue { verdict: "first iteration" }
            }
            ConvergenceDecision::Continue { verdict } => LoopDecision::Continue {
                verdict: match verdict {
                    StepVerdict::Improved => "improved",
                    StepVerdict::Stable => "stable (no change)",
                    StepVerdict::Regressed => "regressed",
                },
            },
            ConvergenceDecision::Converged { stable_rounds, .. } => {
                LoopDecision::Converged { stable_rounds }
            }
            ConvergenceDecision::Regressed { reason } => LoopDecision::Regressed {
                reason: match reason {
                    RegressionReason::FewerStaticProofs => "fewer proofs than previous iteration",
                    RegressionReason::MoreFailures => "more failures than previous iteration",
                    RegressionReason::MoreUnresolvedObligations => {
                        "more unresolved obligations than previous iteration"
                    }
                },
            },
            ConvergenceDecision::IterationLimitReached { .. } => {
                LoopDecision::IterationLimitReached
            }
        }
    }

    pub(crate) fn iteration_count(&self) -> usize {
        self.observed
    }
}
