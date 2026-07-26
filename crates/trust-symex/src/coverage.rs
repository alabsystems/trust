// trust-symex coverage tracking
//
// Tracks which branches and paths symbolic execution has explored,
// computes coverage metrics, and suggests unexplored paths.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

/// A branch point in the program under analysis.
///
/// Each branch point represents a location where execution can diverge
/// (e.g., an `if` condition, a `match` arm). Tracks whether each direction
/// has been explored by at least one symbolic execution path.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BranchPoint {
    /// Unique identifier for this branch location (typically a block ID).
    pub location: usize,
    /// Human-readable description of the branch condition.
    pub condition: String,
    /// Whether the true (taken) direction has been explored.
    pub true_explored: bool,
    /// Whether the false (not-taken) direction has been explored.
    pub false_explored: bool,
}

impl BranchPoint {
    /// Create a new unexplored branch point.
    #[must_use]
    pub fn new(location: usize, condition: impl Into<String>) -> Self {
        Self { location, condition: condition.into(), true_explored: false, false_explored: false }
    }

    /// Returns `true` if both directions have been explored.
    #[must_use]
    pub fn is_fully_covered(&self) -> bool {
        self.true_explored && self.false_explored
    }

    /// Returns the number of explored directions (0, 1, or 2).
    #[must_use]
    pub fn explored_count(&self) -> usize {
        usize::from(self.true_explored) + usize::from(self.false_explored)
    }
}

/// Coverage information for a single execution path.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PathCoverage {
    /// Unique identifier for this path.
    pub path_id: usize,
    /// Sequence of branch decisions (true = taken, false = not-taken).
    pub branches_taken: Vec<(usize, bool)>,
    /// Number of constraints on this path.
    pub constraint_count: usize,
}

/// Aggregate coverage map across all explored symbolic execution paths.
///
/// Collects branch-level coverage and path metadata to support coverage
/// reporting and guided exploration.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CoverageMap {
    /// Branch points indexed by location.
    branches: BTreeMap<usize, BranchPoint>,
    /// Per-path coverage records.
    paths: Vec<PathCoverage>,
    /// Total number of branches registered (both directions counted).
    total_branch_directions: usize,
    /// Counter for assigning path IDs.
    next_path_id: usize,
}

impl CoverageMap {
    /// Create an empty coverage map.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a branch point. If the location already exists, this is a no-op.
    pub fn register_branch(&mut self, location: usize, condition: impl Into<String>) {
        self.branches.entry(location).or_insert_with(|| {
            self.total_branch_directions += 2;
            BranchPoint::new(location, condition)
        });
    }

    /// Record that a branch direction was explored.
    ///
    /// If the branch location is not yet registered, it is created with an
    /// empty condition string.
    pub fn record_branch(&mut self, location: usize, taken: bool) {
        let bp = self.branches.entry(location).or_insert_with(|| {
            self.total_branch_directions += 2;
            BranchPoint::new(location, "")
        });
        if taken {
            bp.true_explored = true;
        } else {
            bp.false_explored = true;
        }
    }

    /// Record a complete path's coverage.
    ///
    /// `branches` is the sequence of `(location, taken)` decisions along the path.
    /// Returns the assigned path ID.
    pub fn record_path(&mut self, branches: &[(usize, bool)], constraint_count: usize) -> usize {
        let path_id = self.next_path_id;
        self.next_path_id += 1;

        for &(loc, taken) in branches {
            self.record_branch(loc, taken);
        }

        self.paths.push(PathCoverage {
            path_id,
            branches_taken: branches.to_vec(),
            constraint_count,
        });

        path_id
    }

    /// Returns the number of registered branch points.
    #[must_use]
    pub fn branch_count(&self) -> usize {
        self.branches.len()
    }

    /// Returns the number of recorded paths.
    #[must_use]
    pub fn path_count(&self) -> usize {
        self.paths.len()
    }

    /// Returns a reference to all branch points.
    #[must_use]
    pub fn branches(&self) -> &BTreeMap<usize, BranchPoint> {
        &self.branches
    }

    /// Returns a reference to all path records.
    #[must_use]
    pub fn paths(&self) -> &[PathCoverage] {
        &self.paths
    }
}

/// Compute the overall branch coverage percentage.
///
/// Coverage is defined as the fraction of branch directions (true/false per
/// branch point) that have been explored. Returns 100.0 if there are no
/// branch points (vacuously covered).
#[must_use]
pub fn coverage_percentage(map: &CoverageMap) -> f64 {
    if map.total_branch_directions == 0 {
        return 100.0;
    }

    let explored: usize = map.branches.values().map(|bp| bp.explored_count()).sum();

    (explored as f64 / map.total_branch_directions as f64) * 100.0
}

/// Return all branch points that have at least one unexplored direction.
#[must_use]
pub fn uncovered_branches(map: &CoverageMap) -> Vec<BranchPoint> {
    let mut result: Vec<BranchPoint> =
        map.branches.values().filter(|bp| !bp.is_fully_covered()).cloned().collect();
    // Sort by location for deterministic output.
    result.sort_by_key(|bp| bp.location);
    result
}

/// Suggest a sequence of branch decisions that would maximize coverage.
///
/// Returns `None` if all branches are fully covered. Otherwise, returns
/// a sequence of `bool` decisions (one per registered branch in location
/// order) that targets the first unexplored direction at each branch.
#[must_use]
pub fn suggest_next_path(map: &CoverageMap) -> Option<Vec<bool>> {
    let uncovered = uncovered_branches(map);
    if uncovered.is_empty() {
        return None;
    }

    // Build a suggested path: for each branch (sorted by location),
    // pick the unexplored direction. If both are explored, default to true.
    let mut locations: Vec<usize> = map.branches.keys().copied().collect();
    locations.sort_unstable();

    let decisions: Vec<bool> = locations
        .iter()
        .map(|loc| {
            let bp = &map.branches[loc];
            if !bp.true_explored {
                true
            } else if !bp.false_explored {
                false
            } else {
                // Both explored; default to true.
                true
            }
        })
        .collect();

    Some(decisions)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_coverage_branch_point_new_unexplored() {
        let bp = BranchPoint::new(0, "x < 10");
        assert_eq!(bp.location, 0);
        assert_eq!(bp.condition, "x < 10");
        assert!(!bp.true_explored);
        assert!(!bp.false_explored);
        assert!(!bp.is_fully_covered());
        assert_eq!(bp.explored_count(), 0);
    }

    #[test]
    fn test_coverage_branch_point_partial() {
        let mut bp = BranchPoint::new(1, "y > 0");
        bp.true_explored = true;
        assert!(!bp.is_fully_covered());
        assert_eq!(bp.explored_count(), 1);
    }

    #[test]
    fn test_coverage_branch_point_fully_covered() {
        let mut bp = BranchPoint::new(2, "z == 0");
        bp.true_explored = true;
        bp.false_explored = true;
        assert!(bp.is_fully_covered());
        assert_eq!(bp.explored_count(), 2);
    }

    #[test]
    fn test_coverage_map_empty() {
        let map = CoverageMap::new();
        assert_eq!(map.branch_count(), 0);
        assert_eq!(map.path_count(), 0);
        assert_eq!(coverage_percentage(&map), 100.0);
        assert!(uncovered_branches(&map).is_empty());
        assert!(suggest_next_path(&map).is_none());
    }

    #[test]
    fn test_coverage_map_register_and_record() {
        let mut map = CoverageMap::new();
        map.register_branch(0, "x < 10");
        map.register_branch(1, "y > 0");
        assert_eq!(map.branch_count(), 2);

        map.record_branch(0, true);
        assert_eq!(coverage_percentage(&map), 25.0); // 1 of 4 directions

        map.record_branch(0, false);
        assert_eq!(coverage_percentage(&map), 50.0); // 2 of 4 directions
    }

    #[test]
    fn test_coverage_map_record_path() {
        let mut map = CoverageMap::new();
        map.register_branch(0, "a");
        map.register_branch(1, "b");

        let pid = map.record_path(&[(0, true), (1, false)], 2);
        assert_eq!(pid, 0);
        assert_eq!(map.path_count(), 1);

        let paths = map.paths();
        assert_eq!(paths[0].path_id, 0);
        assert_eq!(paths[0].branches_taken, vec![(0, true), (1, false)]);
        assert_eq!(paths[0].constraint_count, 2);
    }

    #[test]
    fn test_coverage_percentage_full() {
        let mut map = CoverageMap::new();
        map.register_branch(0, "cond");
        map.record_branch(0, true);
        map.record_branch(0, false);
        assert_eq!(coverage_percentage(&map), 100.0);
    }

    #[test]
    fn test_coverage_uncovered_branches() {
        let mut map = CoverageMap::new();
        map.register_branch(0, "a");
        map.register_branch(1, "b");
        map.register_branch(2, "c");

        // Fully cover branch 1.
        map.record_branch(1, true);
        map.record_branch(1, false);
        // Partially cover branch 0.
        map.record_branch(0, true);
        // Leave branch 2 untouched.

        let uncov = uncovered_branches(&map);
        assert_eq!(uncov.len(), 2);
        assert_eq!(uncov[0].location, 0); // partial
        assert_eq!(uncov[1].location, 2); // untouched
    }

    #[test]
    fn test_coverage_suggest_next_path_targets_unexplored() {
        let mut map = CoverageMap::new();
        map.register_branch(0, "a");
        map.register_branch(1, "b");

        // Explore true for both.
        map.record_branch(0, true);
        map.record_branch(1, true);

        let suggestion = suggest_next_path(&map).expect("should suggest");
        // Should suggest false for both (the unexplored directions).
        assert_eq!(suggestion, vec![false, false]);
    }

    #[test]
    fn test_coverage_suggest_next_path_none_when_covered() {
        let mut map = CoverageMap::new();
        map.register_branch(0, "a");
        map.record_branch(0, true);
        map.record_branch(0, false);
        assert!(suggest_next_path(&map).is_none());
    }

    #[test]
    fn test_coverage_record_branch_auto_registers() {
        let mut map = CoverageMap::new();
        // Recording without registering first should auto-register.
        map.record_branch(5, true);
        assert_eq!(map.branch_count(), 1);
        assert!(map.branches().contains_key(&5));
    }

    #[test]
    fn test_coverage_multiple_paths_accumulate() {
        let mut map = CoverageMap::new();
        map.register_branch(0, "x");
        map.register_branch(1, "y");

        let p0 = map.record_path(&[(0, true), (1, true)], 2);
        let p1 = map.record_path(&[(0, false), (1, false)], 2);
        assert_eq!(p0, 0);
        assert_eq!(p1, 1);
        assert_eq!(map.path_count(), 2);
        assert_eq!(coverage_percentage(&map), 100.0);
    }

    #[test]
    fn test_coverage_register_branch_idempotent() {
        let mut map = CoverageMap::new();
        map.register_branch(0, "first");
        map.register_branch(0, "second");
        assert_eq!(map.branch_count(), 1);
        // First registration wins.
        assert_eq!(map.branches()[&0].condition, "first");
    }

    #[test]
    fn test_coverage_path_coverage_fields() {
        let pc = PathCoverage {
            path_id: 7,
            branches_taken: vec![(0, true), (1, false), (2, true)],
            constraint_count: 5,
        };
        assert_eq!(pc.path_id, 7);
        assert_eq!(pc.branches_taken.len(), 3);
        assert_eq!(pc.constraint_count, 5);
    }
}
