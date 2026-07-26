// trust-loop/scheduling.rs: Loop scheduling and resource management
//
// Provides scheduling policies and resource budgets for the verification loop,
// controlling which functions to verify next and when to pause based on resource limits.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BinaryHeap;
use std::time::{Duration, Instant};

/// Scheduling policy for verification loop iterations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum SchedulingPolicy {
    /// Verify functions in round-robin order, cycling through all candidates equally.
    RoundRobin,
    /// Verify functions based on static priority (difficulty estimate, past failures).
    PriorityBased,
    /// Like PriorityBased but also considers remaining resource budget.
    ResourceAware,
    /// Dynamically switches between policies based on observed progress.
    Adaptive,
}

/// Resource budget for a verification session.
#[derive(Debug, Clone, PartialEq)]
pub struct IterationBudget {
    /// Maximum wall-clock time for the entire session.
    pub max_time: Duration,
    /// Maximum memory in bytes (advisory; checked via `should_pause`).
    pub max_memory: u64,
    /// Maximum number of solver calls across all iterations.
    pub max_solver_calls: u32,
}

impl Default for IterationBudget {
    fn default() -> Self {
        Self {
            max_time: Duration::from_secs(300),
            max_memory: 4 * 1024 * 1024 * 1024, // 4 GiB
            max_solver_calls: 10_000,
        }
    }
}

/// A function candidate for verification, with priority metadata.
#[derive(Debug, Clone, PartialEq)]
pub struct VerificationCandidate {
    /// Fully-qualified function name (e.g. `crate::module::func`).
    pub function: String,
    /// Estimated difficulty in [0.0, 1.0]. Higher means harder to prove.
    pub difficulty_estimate: f64,
    /// Number of past verification failures for this function.
    pub past_failures: u32,
    /// Number of VCs associated with this function.
    pub vc_count: u32,
}

impl Eq for VerificationCandidate {}

/// Priority wrapper for the binary heap. Higher priority = dequeued first.
#[derive(Debug, Clone, PartialEq)]
struct PrioritizedCandidate {
    priority: f64,
    candidate: VerificationCandidate,
}

impl Eq for PrioritizedCandidate {}

impl PartialOrd for PrioritizedCandidate {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PrioritizedCandidate {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Higher priority first. Use total_cmp for deterministic f64 ordering.
        self.priority.total_cmp(&other.priority)
    }
}

/// Tracks resource usage and scheduling state across iterations.
#[derive(Debug)]
pub struct SchedulerState {
    policy: SchedulingPolicy,
    budget: IterationBudget,
    start_time: Instant,
    solver_calls_used: u32,
    memory_used: u64,
    iterations_completed: u32,
    round_robin_index: usize,
    candidates: Vec<VerificationCandidate>,
    priority_queue: BinaryHeap<PrioritizedCandidate>,
}

impl SchedulerState {
    /// Create a new scheduler with the given policy, budget, and initial candidates.
    #[must_use]
    pub fn new(
        policy: SchedulingPolicy,
        budget: IterationBudget,
        candidates: Vec<VerificationCandidate>,
    ) -> Self {
        let mut state = Self {
            policy,
            budget,
            start_time: Instant::now(),
            solver_calls_used: 0,
            memory_used: 0,
            iterations_completed: 0,
            round_robin_index: 0,
            candidates: candidates.clone(),
            priority_queue: BinaryHeap::new(),
        };
        state.rebuild_priority_queue(&candidates);
        state
    }

    /// Record solver calls consumed by the latest iteration.
    pub fn record_solver_calls(&mut self, calls: u32) {
        self.solver_calls_used = self.solver_calls_used.saturating_add(calls);
    }

    /// Record current memory usage (advisory, set by the caller).
    pub fn record_memory_usage(&mut self, bytes: u64) {
        self.memory_used = bytes;
    }

    /// Record that an iteration completed.
    pub fn record_iteration(&mut self) {
        self.iterations_completed += 1;
    }

    /// Number of solver calls used so far.
    #[must_use]
    pub fn solver_calls_used(&self) -> u32 {
        self.solver_calls_used
    }

    /// Number of iterations completed so far.
    #[must_use]
    pub fn iterations_completed(&self) -> u32 {
        self.iterations_completed
    }

    /// Elapsed time since the scheduler was created.
    #[must_use]
    pub fn elapsed(&self) -> Duration {
        self.start_time.elapsed()
    }

    /// The active scheduling policy.
    #[must_use]
    pub fn policy(&self) -> SchedulingPolicy {
        self.policy
    }

    /// Pick the next function to verify based on the active policy.
    ///
    /// Returns `None` if no candidates remain or resources are exhausted.
    #[must_use]
    pub fn schedule_next(&mut self) -> Option<VerificationCandidate> {
        if self.candidates.is_empty() {
            return None;
        }

        match self.policy {
            SchedulingPolicy::RoundRobin => self.schedule_round_robin(),
            SchedulingPolicy::PriorityBased => self.schedule_priority(),
            SchedulingPolicy::ResourceAware => self.schedule_resource_aware(),
            SchedulingPolicy::Adaptive => self.schedule_adaptive(),
        }
    }

    /// Check whether the loop should pause due to resource limits.
    ///
    /// Returns a `PauseReason` if any limit is exceeded, or `None` to continue.
    #[must_use]
    pub fn should_pause(&self) -> Option<PauseReason> {
        if self.start_time.elapsed() >= self.budget.max_time {
            return Some(PauseReason::TimeExceeded {
                elapsed: self.start_time.elapsed(),
                limit: self.budget.max_time,
            });
        }
        if self.memory_used >= self.budget.max_memory {
            return Some(PauseReason::MemoryExceeded {
                used: self.memory_used,
                limit: self.budget.max_memory,
            });
        }
        if self.solver_calls_used >= self.budget.max_solver_calls {
            return Some(PauseReason::SolverCallsExceeded {
                used: self.solver_calls_used,
                limit: self.budget.max_solver_calls,
            });
        }
        None
    }

    // -- Private scheduling strategies --

    fn schedule_round_robin(&mut self) -> Option<VerificationCandidate> {
        if self.candidates.is_empty() {
            return None;
        }
        let idx = self.round_robin_index % self.candidates.len();
        self.round_robin_index = idx + 1;
        Some(self.candidates[idx].clone())
    }

    fn schedule_priority(&mut self) -> Option<VerificationCandidate> {
        self.priority_queue.pop().map(|pc| pc.candidate)
    }

    fn schedule_resource_aware(&mut self) -> Option<VerificationCandidate> {
        // Like priority, but skip candidates whose estimated cost exceeds remaining budget.
        let remaining_calls = self.budget.max_solver_calls.saturating_sub(self.solver_calls_used);

        while let Some(pc) = self.priority_queue.pop() {
            // Estimate solver calls as vc_count * (1 + past_failures).
            let estimated_cost =
                pc.candidate.vc_count.saturating_mul(1 + pc.candidate.past_failures);
            if estimated_cost <= remaining_calls {
                return Some(pc.candidate);
            }
            // Skip this candidate -- too expensive for remaining budget.
        }
        None
    }

    fn schedule_adaptive(&mut self) -> Option<VerificationCandidate> {
        // Switch strategy based on progress: use priority for first half of budget,
        // then switch to resource-aware to conserve resources.
        let budget_fraction =
            self.solver_calls_used as f64 / self.budget.max_solver_calls.max(1) as f64;

        if budget_fraction < 0.5 {
            self.schedule_priority()
        } else {
            self.schedule_resource_aware()
        }
    }

    fn rebuild_priority_queue(&mut self, candidates: &[VerificationCandidate]) {
        self.priority_queue.clear();
        for c in candidates {
            let priority = compute_priority(c);
            self.priority_queue.push(PrioritizedCandidate { priority, candidate: c.clone() });
        }
    }
}

/// Compute priority score for a candidate. Higher = scheduled sooner.
///
/// Prioritizes functions with more past failures (likely regressions or hard cases)
/// and higher difficulty estimates.
fn compute_priority(candidate: &VerificationCandidate) -> f64 {
    // Weight: 60% past failures, 30% difficulty, 10% VC count (more VCs = more value).
    let failure_score = candidate.past_failures as f64;
    let difficulty_score = candidate.difficulty_estimate;
    let vc_score = (candidate.vc_count as f64).ln_1p(); // log scale for VC count

    0.6 * failure_score + 0.3 * difficulty_score + 0.1 * vc_score
}

/// Reason for pausing the verification loop.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum PauseReason {
    /// Wall-clock time limit exceeded.
    TimeExceeded { elapsed: Duration, limit: Duration },
    /// Memory usage limit exceeded.
    MemoryExceeded { used: u64, limit: u64 },
    /// Solver call limit exceeded.
    SolverCallsExceeded { used: u32, limit: u32 },
}

impl std::fmt::Display for PauseReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TimeExceeded { elapsed, limit } => {
                write!(f, "time exceeded: {elapsed:?} >= {limit:?}")
            }
            Self::MemoryExceeded { used, limit } => {
                write!(f, "memory exceeded: {used} >= {limit} bytes")
            }
            Self::SolverCallsExceeded { used, limit } => {
                write!(f, "solver calls exceeded: {used} >= {limit}")
            }
        }
    }
}

/// Scheduling error type.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum SchedulingError {
    /// No candidates available for scheduling.
    #[error("no verification candidates available")]
    NoCandidates,
    /// Resource budget exhausted before scheduling could complete.
    #[error("resource budget exhausted: {reason}")]
    BudgetExhausted { reason: PauseReason },
}

#[cfg(test)]
mod tests {
    use super::*;

    fn candidate(name: &str, difficulty: f64, failures: u32, vcs: u32) -> VerificationCandidate {
        VerificationCandidate {
            function: name.into(),
            difficulty_estimate: difficulty,
            past_failures: failures,
            vc_count: vcs,
        }
    }

    #[test]
    fn test_round_robin_cycles_through_candidates() {
        let candidates = vec![
            candidate("crate::a", 0.1, 0, 1),
            candidate("crate::b", 0.5, 1, 2),
            candidate("crate::c", 0.9, 3, 4),
        ];
        let budget = IterationBudget::default();
        let mut state = SchedulerState::new(SchedulingPolicy::RoundRobin, budget, candidates);

        let first = state.schedule_next().expect("should return candidate");
        assert_eq!(first.function, "crate::a");
        let second = state.schedule_next().expect("should return candidate");
        assert_eq!(second.function, "crate::b");
        let third = state.schedule_next().expect("should return candidate");
        assert_eq!(third.function, "crate::c");
        // Wraps around
        let fourth = state.schedule_next().expect("should return candidate");
        assert_eq!(fourth.function, "crate::a");
    }

    #[test]
    fn test_priority_based_orders_by_score() {
        let candidates = vec![
            candidate("crate::easy", 0.1, 0, 1),   // low priority
            candidate("crate::hard", 0.9, 5, 10),  // high priority
            candidate("crate::medium", 0.5, 2, 3), // medium
        ];
        let budget = IterationBudget::default();
        let mut state = SchedulerState::new(SchedulingPolicy::PriorityBased, budget, candidates);

        let first = state.schedule_next().expect("should return candidate");
        assert_eq!(first.function, "crate::hard");
        let second = state.schedule_next().expect("should return candidate");
        assert_eq!(second.function, "crate::medium");
        let third = state.schedule_next().expect("should return candidate");
        assert_eq!(third.function, "crate::easy");
    }

    #[test]
    fn test_priority_queue_empty_returns_none() {
        let candidates = vec![candidate("crate::solo", 0.5, 1, 2)];
        let budget = IterationBudget::default();
        let mut state = SchedulerState::new(SchedulingPolicy::PriorityBased, budget, candidates);

        let first = state.schedule_next();
        assert!(first.is_some());
        let second = state.schedule_next();
        assert!(second.is_none());
    }

    #[test]
    fn test_resource_aware_skips_expensive_candidates() {
        let candidates = vec![
            candidate("crate::cheap", 0.1, 0, 1),      // cost: 1*(1+0) = 1
            candidate("crate::expensive", 0.9, 10, 5), // cost: 5*(1+10) = 55
        ];
        let budget = IterationBudget {
            max_solver_calls: 10, // only 10 calls total
            ..IterationBudget::default()
        };
        let mut state = SchedulerState::new(SchedulingPolicy::ResourceAware, budget, candidates);

        // Expensive candidate has higher priority but costs 55 > 10 remaining.
        // Cheap candidate costs 1 <= 10 remaining.
        let first = state.schedule_next().expect("should return cheap candidate");
        assert_eq!(first.function, "crate::cheap");
        // No more candidates fit
        let second = state.schedule_next();
        assert!(second.is_none());
    }

    #[test]
    fn test_should_pause_solver_calls() {
        let candidates = vec![candidate("crate::f", 0.5, 0, 1)];
        let budget = IterationBudget { max_solver_calls: 100, ..IterationBudget::default() };
        let mut state = SchedulerState::new(SchedulingPolicy::RoundRobin, budget, candidates);

        assert!(state.should_pause().is_none());
        state.record_solver_calls(100);
        let reason = state.should_pause().expect("should pause");
        match reason {
            PauseReason::SolverCallsExceeded { used, limit } => {
                assert_eq!(used, 100);
                assert_eq!(limit, 100);
            }
            _ => panic!("expected SolverCallsExceeded"),
        }
    }

    #[test]
    fn test_should_pause_memory() {
        let candidates = vec![candidate("crate::f", 0.5, 0, 1)];
        let budget = IterationBudget { max_memory: 1024, ..IterationBudget::default() };
        let mut state = SchedulerState::new(SchedulingPolicy::RoundRobin, budget, candidates);

        assert!(state.should_pause().is_none());
        state.record_memory_usage(2048);
        let reason = state.should_pause().expect("should pause");
        match reason {
            PauseReason::MemoryExceeded { used, limit } => {
                assert_eq!(used, 2048);
                assert_eq!(limit, 1024);
            }
            _ => panic!("expected MemoryExceeded"),
        }
    }

    #[test]
    fn test_should_pause_time() {
        let candidates = vec![candidate("crate::f", 0.5, 0, 1)];
        let budget =
            IterationBudget { max_time: Duration::from_millis(0), ..IterationBudget::default() };
        let state = SchedulerState::new(SchedulingPolicy::RoundRobin, budget, candidates);

        // With a 0ms budget, should_pause triggers immediately.
        let reason = state.should_pause().expect("should pause for time");
        assert!(matches!(reason, PauseReason::TimeExceeded { .. }));
    }

    #[test]
    fn test_record_iteration_increments() {
        let candidates = vec![candidate("crate::f", 0.5, 0, 1)];
        let budget = IterationBudget::default();
        let mut state = SchedulerState::new(SchedulingPolicy::RoundRobin, budget, candidates);

        assert_eq!(state.iterations_completed(), 0);
        state.record_iteration();
        assert_eq!(state.iterations_completed(), 1);
        state.record_iteration();
        state.record_iteration();
        assert_eq!(state.iterations_completed(), 3);
    }

    #[test]
    fn test_empty_candidates_returns_none() {
        let budget = IterationBudget::default();
        let mut state = SchedulerState::new(SchedulingPolicy::RoundRobin, budget, Vec::new());

        assert!(state.schedule_next().is_none());
    }

    #[test]
    fn test_adaptive_switches_strategy() {
        let candidates = vec![
            candidate("crate::cheap", 0.1, 0, 1), // cost 1, low priority
            candidate("crate::expensive", 0.9, 5, 20), // cost 20*6=120, high priority
        ];
        let budget = IterationBudget { max_solver_calls: 200, ..IterationBudget::default() };
        let mut state = SchedulerState::new(SchedulingPolicy::Adaptive, budget, candidates.clone());

        // First half of budget (0 used / 200 max = 0%): uses priority-based.
        // "expensive" has higher priority, so it comes first.
        let first = state.schedule_next().expect("should return candidate");
        assert_eq!(first.function, "crate::expensive");

        // Simulate using >50% of budget.
        state.record_solver_calls(150);
        // Rebuild the priority queue for a fresh round of adaptive scheduling.
        state.rebuild_priority_queue(&candidates);

        // Now at 75% budget usage: switches to resource-aware.
        // "expensive" costs 120 but only 50 calls remain, so it's skipped.
        // "cheap" costs 1 <= 50, so it's returned.
        let second = state.schedule_next().expect("should return cheap");
        assert_eq!(second.function, "crate::cheap");
    }

    #[test]
    fn test_compute_priority_ordering() {
        let low = candidate("low", 0.0, 0, 1);
        let mid = candidate("mid", 0.5, 2, 5);
        let high = candidate("high", 1.0, 10, 20);

        let p_low = compute_priority(&low);
        let p_mid = compute_priority(&mid);
        let p_high = compute_priority(&high);

        assert!(p_low < p_mid, "low ({p_low}) should be < mid ({p_mid})");
        assert!(p_mid < p_high, "mid ({p_mid}) should be < high ({p_high})");
    }

    #[test]
    fn test_iteration_budget_default() {
        let budget = IterationBudget::default();
        assert_eq!(budget.max_time, Duration::from_secs(300));
        assert_eq!(budget.max_memory, 4 * 1024 * 1024 * 1024);
        assert_eq!(budget.max_solver_calls, 10_000);
    }

    #[test]
    fn test_scheduling_error_display() {
        let err = SchedulingError::NoCandidates;
        assert_eq!(err.to_string(), "no verification candidates available");

        let err2 = SchedulingError::BudgetExhausted {
            reason: PauseReason::SolverCallsExceeded { used: 100, limit: 50 },
        };
        assert!(err2.to_string().contains("solver calls exceeded"));
    }

    #[test]
    fn test_solver_calls_saturating_add() {
        let candidates = vec![candidate("crate::f", 0.5, 0, 1)];
        let budget = IterationBudget::default();
        let mut state = SchedulerState::new(SchedulingPolicy::RoundRobin, budget, candidates);

        state.record_solver_calls(u32::MAX);
        state.record_solver_calls(1);
        assert_eq!(state.solver_calls_used(), u32::MAX);
    }
}
