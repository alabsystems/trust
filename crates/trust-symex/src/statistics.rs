// trust-symex execution statistics
//
// Collects and reports statistics from symbolic execution runs:
// path counts, solver performance, timing data.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::time::Duration;

use serde::{Deserialize, Serialize};

/// Statistics collected from a symbolic execution run.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ExecutionStats {
    /// Total number of feasible paths discovered.
    pub total_paths: usize,
    /// Number of paths fully explored to termination.
    pub explored_paths: usize,
    /// Number of paths pruned (infeasible constraints).
    pub pruned_paths: usize,
    /// Number of paths merged (state merging).
    pub merged_paths: usize,
    /// Number of paths that hit the timeout.
    pub timeouts: usize,

    /// Average path length (number of blocks traversed).
    pub avg_path_length: f64,
    /// Maximum path length observed.
    pub max_path_length: usize,
    /// Average constraint count per path.
    pub avg_constraint_count: f64,

    /// Total number of solver calls.
    pub solver_calls: usize,
    /// Number of solver cache hits.
    pub cache_hits: usize,
    /// Total solver time in milliseconds.
    pub total_solver_time_ms: u64,
}

impl Default for ExecutionStats {
    fn default() -> Self {
        Self {
            total_paths: 0,
            explored_paths: 0,
            pruned_paths: 0,
            merged_paths: 0,
            timeouts: 0,
            avg_path_length: 0.0,
            max_path_length: 0,
            avg_constraint_count: 0.0,
            solver_calls: 0,
            cache_hits: 0,
            total_solver_time_ms: 0,
        }
    }
}

impl ExecutionStats {
    /// Solver cache hit rate as a percentage (0.0-100.0).
    ///
    /// Returns 0.0 if no solver calls have been made.
    #[must_use]
    pub fn cache_hit_rate(&self) -> f64 {
        if self.solver_calls == 0 {
            return 0.0;
        }
        (self.cache_hits as f64 / self.solver_calls as f64) * 100.0
    }

    /// Average solver time per call in milliseconds.
    ///
    /// Returns 0.0 if no solver calls have been made.
    #[must_use]
    pub fn avg_solver_time_ms(&self) -> f64 {
        if self.solver_calls == 0 {
            return 0.0;
        }
        self.total_solver_time_ms as f64 / self.solver_calls as f64
    }
}

/// Accumulates statistics during a symbolic execution run.
///
/// Call the `record_*` methods as execution progresses, then call
/// `finish()` to produce the final `ExecutionStats`.
#[derive(Debug, Clone, Default)]
pub struct StatsCollector {
    total_paths: usize,
    explored_paths: usize,
    pruned_paths: usize,
    merged_paths: usize,
    timeouts: usize,

    path_lengths: Vec<usize>,
    constraint_counts: Vec<usize>,

    solver_calls: usize,
    cache_hits: usize,
    solver_time: Duration,
}

impl StatsCollector {
    /// Create a new, empty stats collector.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Record discovery of a new path.
    pub fn record_path(&mut self, length: usize, constraint_count: usize) {
        self.total_paths += 1;
        self.path_lengths.push(length);
        self.constraint_counts.push(constraint_count);
    }

    /// Record that a path was fully explored.
    pub fn record_explored(&mut self) {
        self.explored_paths += 1;
    }

    /// Record that a path was pruned (infeasible).
    pub fn record_pruned(&mut self) {
        self.pruned_paths += 1;
    }

    /// Record that paths were merged.
    pub fn record_merged(&mut self, count: usize) {
        self.merged_paths += count;
    }

    /// Record that a path hit the timeout.
    pub fn record_timeout(&mut self) {
        self.timeouts += 1;
    }

    /// Record a solver call with its duration and whether it was a cache hit.
    pub fn record_solver_call(&mut self, duration: Duration, cache_hit: bool) {
        self.solver_calls += 1;
        self.solver_time += duration;
        if cache_hit {
            self.cache_hits += 1;
        }
    }

    /// Finalize and produce the `ExecutionStats`.
    #[must_use]
    pub fn finish(&self) -> ExecutionStats {
        let avg_path_length = if self.path_lengths.is_empty() {
            0.0
        } else {
            self.path_lengths.iter().sum::<usize>() as f64 / self.path_lengths.len() as f64
        };

        let max_path_length = self.path_lengths.iter().copied().max().unwrap_or(0);

        let avg_constraint_count = if self.constraint_counts.is_empty() {
            0.0
        } else {
            self.constraint_counts.iter().sum::<usize>() as f64
                / self.constraint_counts.len() as f64
        };

        ExecutionStats {
            total_paths: self.total_paths,
            explored_paths: self.explored_paths,
            pruned_paths: self.pruned_paths,
            merged_paths: self.merged_paths,
            timeouts: self.timeouts,
            avg_path_length,
            max_path_length,
            avg_constraint_count,
            solver_calls: self.solver_calls,
            cache_hits: self.cache_hits,
            total_solver_time_ms: self.solver_time.as_millis() as u64,
        }
    }
}

/// Format an `ExecutionStats` into a human-readable summary report.
#[must_use]
pub fn format_stats_report(stats: &ExecutionStats) -> String {
    let mut lines = Vec::new();

    lines.push("=== Symbolic Execution Statistics ===".to_owned());
    lines.push(String::new());

    // Path summary.
    lines.push("Paths:".to_owned());
    lines.push(format!("  Total discovered:  {}", stats.total_paths));
    lines.push(format!("  Fully explored:    {}", stats.explored_paths));
    lines.push(format!("  Pruned:            {}", stats.pruned_paths));
    lines.push(format!("  Merged:            {}", stats.merged_paths));
    lines.push(format!("  Timeouts:          {}", stats.timeouts));
    lines.push(String::new());

    // Path metrics.
    lines.push("Path metrics:".to_owned());
    lines.push(format!("  Avg length:        {:.1}", stats.avg_path_length));
    lines.push(format!("  Max length:        {}", stats.max_path_length));
    lines.push(format!("  Avg constraints:   {:.1}", stats.avg_constraint_count));
    lines.push(String::new());

    // Solver performance.
    lines.push("Solver:".to_owned());
    lines.push(format!("  Calls:             {}", stats.solver_calls));
    lines.push(format!("  Cache hits:        {}", stats.cache_hits));
    lines.push(format!("  Cache hit rate:    {:.1}%", stats.cache_hit_rate()));
    lines.push(format!("  Total time:        {} ms", stats.total_solver_time_ms));
    lines.push(format!("  Avg time/call:     {:.1} ms", stats.avg_solver_time_ms()));

    lines.join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_stats_default_zeroed() {
        let stats = ExecutionStats::default();
        assert_eq!(stats.total_paths, 0);
        assert_eq!(stats.explored_paths, 0);
        assert_eq!(stats.pruned_paths, 0);
        assert_eq!(stats.merged_paths, 0);
        assert_eq!(stats.timeouts, 0);
        assert_eq!(stats.avg_path_length, 0.0);
        assert_eq!(stats.max_path_length, 0);
        assert_eq!(stats.avg_constraint_count, 0.0);
        assert_eq!(stats.solver_calls, 0);
        assert_eq!(stats.cache_hits, 0);
        assert_eq!(stats.total_solver_time_ms, 0);
    }

    #[test]
    fn test_stats_cache_hit_rate_no_calls() {
        let stats = ExecutionStats::default();
        assert_eq!(stats.cache_hit_rate(), 0.0);
    }

    #[test]
    fn test_stats_cache_hit_rate_with_hits() {
        let stats = ExecutionStats { solver_calls: 10, cache_hits: 3, ..Default::default() };
        assert!((stats.cache_hit_rate() - 30.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_stats_avg_solver_time_no_calls() {
        let stats = ExecutionStats::default();
        assert_eq!(stats.avg_solver_time_ms(), 0.0);
    }

    #[test]
    fn test_stats_avg_solver_time_with_calls() {
        let stats =
            ExecutionStats { solver_calls: 4, total_solver_time_ms: 100, ..Default::default() };
        assert!((stats.avg_solver_time_ms() - 25.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_stats_collector_empty_finish() {
        let collector = StatsCollector::new();
        let stats = collector.finish();
        assert_eq!(stats.total_paths, 0);
        assert_eq!(stats.max_path_length, 0);
        assert_eq!(stats.avg_path_length, 0.0);
        assert_eq!(stats.avg_constraint_count, 0.0);
    }

    #[test]
    fn test_stats_collector_record_paths() {
        let mut c = StatsCollector::new();
        c.record_path(5, 3);
        c.record_path(10, 7);
        c.record_path(15, 5);

        let stats = c.finish();
        assert_eq!(stats.total_paths, 3);
        assert_eq!(stats.max_path_length, 15);
        assert!((stats.avg_path_length - 10.0).abs() < f64::EPSILON);
        assert!((stats.avg_constraint_count - 5.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_stats_collector_record_explored_pruned() {
        let mut c = StatsCollector::new();
        c.record_explored();
        c.record_explored();
        c.record_pruned();

        let stats = c.finish();
        assert_eq!(stats.explored_paths, 2);
        assert_eq!(stats.pruned_paths, 1);
    }

    #[test]
    fn test_stats_collector_record_merged() {
        let mut c = StatsCollector::new();
        c.record_merged(3);
        c.record_merged(2);

        let stats = c.finish();
        assert_eq!(stats.merged_paths, 5);
    }

    #[test]
    fn test_stats_collector_record_timeout() {
        let mut c = StatsCollector::new();
        c.record_timeout();
        c.record_timeout();

        let stats = c.finish();
        assert_eq!(stats.timeouts, 2);
    }

    #[test]
    fn test_stats_collector_record_solver_calls() {
        let mut c = StatsCollector::new();
        c.record_solver_call(Duration::from_millis(10), false);
        c.record_solver_call(Duration::from_millis(20), true);
        c.record_solver_call(Duration::from_millis(30), true);

        let stats = c.finish();
        assert_eq!(stats.solver_calls, 3);
        assert_eq!(stats.cache_hits, 2);
        assert_eq!(stats.total_solver_time_ms, 60);
    }

    #[test]
    fn test_stats_format_report_contains_sections() {
        let stats = ExecutionStats {
            total_paths: 42,
            explored_paths: 30,
            pruned_paths: 8,
            merged_paths: 4,
            timeouts: 0,
            avg_path_length: 7.5,
            max_path_length: 20,
            avg_constraint_count: 4.2,
            solver_calls: 100,
            cache_hits: 60,
            total_solver_time_ms: 500,
        };

        let report = format_stats_report(&stats);
        assert!(report.contains("Symbolic Execution Statistics"));
        assert!(report.contains("Total discovered:  42"));
        assert!(report.contains("Fully explored:    30"));
        assert!(report.contains("Pruned:            8"));
        assert!(report.contains("Merged:            4"));
        assert!(report.contains("Timeouts:          0"));
        assert!(report.contains("Avg length:        7.5"));
        assert!(report.contains("Max length:        20"));
        assert!(report.contains("Avg constraints:   4.2"));
        assert!(report.contains("Calls:             100"));
        assert!(report.contains("Cache hits:        60"));
        assert!(report.contains("Cache hit rate:    60.0%"));
        assert!(report.contains("Total time:        500 ms"));
        assert!(report.contains("Avg time/call:     5.0 ms"));
    }

    #[test]
    fn test_stats_format_report_zero_stats() {
        let stats = ExecutionStats::default();
        let report = format_stats_report(&stats);
        assert!(report.contains("Total discovered:  0"));
        assert!(report.contains("Cache hit rate:    0.0%"));
        assert!(report.contains("Avg time/call:     0.0 ms"));
    }

    #[test]
    fn test_stats_collector_full_workflow() {
        let mut c = StatsCollector::new();

        // Simulate 3 paths explored.
        c.record_path(4, 2);
        c.record_explored();

        c.record_path(8, 6);
        c.record_explored();

        c.record_path(3, 1);
        c.record_pruned();

        // 2 solver calls.
        c.record_solver_call(Duration::from_millis(5), false);
        c.record_solver_call(Duration::from_millis(15), true);

        let stats = c.finish();
        assert_eq!(stats.total_paths, 3);
        assert_eq!(stats.explored_paths, 2);
        assert_eq!(stats.pruned_paths, 1);
        assert_eq!(stats.max_path_length, 8);
        assert!((stats.avg_path_length - 5.0).abs() < f64::EPSILON);
        assert!((stats.avg_constraint_count - 3.0).abs() < f64::EPSILON);
        assert_eq!(stats.solver_calls, 2);
        assert_eq!(stats.cache_hits, 1);
        assert_eq!(stats.total_solver_time_ms, 20);
    }
}
