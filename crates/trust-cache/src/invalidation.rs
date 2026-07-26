// trust-cache/invalidation.rs: Dependency-aware cache invalidation
//
// Tracks function dependencies (caller -> callees) and computes minimal
// invalidation plans when specs change. Uses transitive closure over the
// reverse call graph to find all affected callers.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;
use trust_types::fx::{FxHashMap, FxHashSet};

/// Tracks function dependencies: which functions depend on which callees.
///
/// This is the reverse perspective from a call graph: given a callee that
/// changed, we need to find all transitive callers whose cached results
/// are now stale.
#[derive(Debug, Clone, Default)]
pub(crate) struct DependencyTracker {
    /// Forward edges: function -> set of functions it depends on (callees).
    dependencies: FxHashMap<String, FxHashSet<String>>,
    /// Reverse edges: function -> set of functions that depend on it (callers).
    /// Maintained in sync with `dependencies` for efficient invalidation.
    reverse_deps: FxHashMap<String, FxHashSet<String>>,
}

impl DependencyTracker {
    /// Create an empty dependency tracker.
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Register that `function` depends on `dependency` (i.e., calls it).
    pub(crate) fn add_dependency(&mut self, function: &str, dependency: &str) {
        self.dependencies.entry(function.to_string()).or_default().insert(dependency.to_string());
        self.reverse_deps.entry(dependency.to_string()).or_default().insert(function.to_string());
    }

    /// Register multiple dependencies at once.
    pub(crate) fn add_dependencies(&mut self, function: &str, dependencies: &[&str]) {
        for dep in dependencies {
            self.add_dependency(function, dep);
        }
    }

    /// Get the direct dependencies of a function (its callees).
    #[must_use]
    pub(crate) fn direct_dependencies(&self, function: &str) -> FxHashSet<String> {
        self.dependencies.get(function).cloned().unwrap_or_default()
    }

    /// Get the direct dependents of a function (its callers).
    #[must_use]
    #[cfg(test)]
    pub(crate) fn direct_dependents(&self, function: &str) -> FxHashSet<String> {
        self.reverse_deps.get(function).cloned().unwrap_or_default()
    }

    /// Compute all transitive dependents of a function.
    ///
    /// If C changes and B calls C and A calls B, returns {B, A}.
    /// Does NOT include the changed function itself.
    #[must_use]
    pub(crate) fn transitive_dependents(&self, function: &str) -> FxHashSet<String> {
        let mut visited = FxHashSet::default();
        let mut queue = VecDeque::new();

        // Seed with direct dependents
        if let Some(direct) = self.reverse_deps.get(function) {
            for dep in direct {
                if visited.insert(dep.clone()) {
                    queue.push_back(dep.clone());
                }
            }
        }

        // BFS through reverse dependency edges
        while let Some(current) = queue.pop_front() {
            if let Some(dependents) = self.reverse_deps.get(&current) {
                for dep in dependents {
                    if visited.insert(dep.clone()) {
                        queue.push_back(dep.clone());
                    }
                }
            }
        }

        visited
    }

    /// Number of tracked functions (those with at least one dependency or dependent).
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        let mut all: FxHashSet<&str> = FxHashSet::default();
        for (k, vs) in &self.dependencies {
            all.insert(k.as_str());
            for v in vs {
                all.insert(v.as_str());
            }
        }
        all.len()
    }

    /// Whether the tracker has no entries.
    #[must_use]
    #[cfg(test)]
    pub(crate) fn is_empty(&self) -> bool {
        self.dependencies.is_empty() && self.reverse_deps.is_empty()
    }

    /// Remove all tracked dependencies.
    #[cfg(test)]
    pub(crate) fn clear(&mut self) {
        self.dependencies.clear();
        self.reverse_deps.clear();
    }
}

/// Why a function's cached result was invalidated.
#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct InvalidationReason {
    /// The function whose cached result is being invalidated.
    pub function: String,
    /// The changed function that caused this invalidation.
    pub changed_root: String,
    /// The dependency chain from root to this function (shortest path).
    /// For direct dependents this is [root, function].
    /// For transitive: [root, intermediate..., function].
    pub chain: Vec<String>,
}

/// An ordered list of functions to re-verify after spec changes.
#[derive(Debug, Clone, Default)]
pub(crate) struct InvalidationPlan {
    /// Functions to re-verify, ordered callee-first (leaves before callers).
    pub(crate) functions: Vec<String>,
    /// Invalidation reasons for diagnostics.
    #[cfg(test)]
    pub(crate) reasons: Vec<InvalidationReason>,
}

// Trust: test-only convenience methods on InvalidationPlan.
// Production code accesses `.functions` directly.
#[cfg(test)]
impl InvalidationPlan {
    /// Number of functions that need re-verification.
    #[must_use]
    pub fn len(&self) -> usize {
        self.functions.len()
    }

    /// Whether no functions need re-verification.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.functions.is_empty()
    }

    /// Get the invalidation reason for a specific function, if present.
    #[must_use]
    pub fn reason_for(&self, function: &str) -> Option<&InvalidationReason> {
        self.reasons.iter().find(|r| r.function == function)
    }
}

/// Compute a minimal invalidation plan given a set of changed functions.
///
/// For each changed function, finds all transitive dependents via the
/// dependency tracker and produces an ordered list of functions to
/// re-verify. The order is callee-first: if A calls B and B changed,
/// B appears before A in the plan.
///
/// The changed functions themselves are included in the plan (they need
/// re-verification too, since their spec changed).
#[must_use]
pub(crate) fn plan_invalidation(changed: &[String], deps: &DependencyTracker) -> InvalidationPlan {
    let mut all_affected: FxHashSet<String> = FxHashSet::default();
    #[cfg(test)]
    let mut reasons: Vec<InvalidationReason> = Vec::new();

    for changed_fn in changed {
        // The changed function itself needs re-verification
        all_affected.insert(changed_fn.clone());
        #[cfg(test)]
        reasons.push(InvalidationReason {
            function: changed_fn.clone(),
            changed_root: changed_fn.clone(),
            chain: vec![changed_fn.clone()],
        });

        // Find all transitive dependents
        let dependents = deps.transitive_dependents(changed_fn);
        for dep in &dependents {
            all_affected.insert(dep.clone());
            #[cfg(test)]
            {
                let chain = find_shortest_chain(deps, changed_fn, dep);
                reasons.push(InvalidationReason {
                    function: dep.clone(),
                    changed_root: changed_fn.clone(),
                    chain,
                });
            }
        }
    }

    // Order: callee-first using topological sort of the dependency subgraph.
    // Functions with fewer transitive dependents come first (leaves).
    let ordered = topological_sort_affected(&all_affected, deps);

    InvalidationPlan {
        functions: ordered,
        #[cfg(test)]
        reasons,
    }
}

/// Find the shortest dependency chain from `root` to `target` through reverse deps.
#[cfg(test)]
fn find_shortest_chain(deps: &DependencyTracker, root: &str, target: &str) -> Vec<String> {
    // BFS from root through reverse_deps to find target
    let mut visited: FxHashMap<String, String> = FxHashMap::default(); // node -> predecessor
    let mut queue = VecDeque::new();
    queue.push_back(root.to_string());
    visited.insert(root.to_string(), String::new());

    while let Some(current) = queue.pop_front() {
        if current == target {
            // Reconstruct path
            let mut path = vec![target.to_string()];
            let mut node = target.to_string();
            while let Some(pred) = visited.get(&node) {
                if pred.is_empty() {
                    break;
                }
                path.push(pred.clone());
                node = pred.clone();
            }
            path.reverse();
            return path;
        }

        if let Some(dependents) = deps.reverse_deps.get(&current) {
            let mut sorted: Vec<&String> = dependents.iter().collect();
            sorted.sort(); // deterministic traversal
            for dep in sorted {
                if !visited.contains_key(dep.as_str()) {
                    visited.insert(dep.clone(), current.clone());
                    queue.push_back(dep.clone());
                }
            }
        }
    }

    // Fallback: just return [root, target]
    vec![root.to_string(), target.to_string()]
}

/// Topological sort of affected functions: callees before callers.
///
/// Within the affected set, a function that is depended upon by others
/// in the set should come first (re-verify it before its callers).
fn topological_sort_affected(
    affected: &FxHashSet<String>,
    deps: &DependencyTracker,
) -> Vec<String> {
    // Collect affected dependency info into owned structures to avoid lifetime issues.
    // For each affected function, compute its direct dependencies that are also affected.
    let mut out_degree: FxHashMap<String, usize> = FxHashMap::default();
    let mut reverse: FxHashMap<String, Vec<String>> = FxHashMap::default();

    for func in affected {
        reverse.entry(func.clone()).or_default();
        let affected_deps: Vec<String> =
            deps.direct_dependencies(func).into_iter().filter(|d| affected.contains(d)).collect();
        out_degree.insert(func.clone(), affected_deps.len());

        for dep in affected_deps {
            reverse.entry(dep).or_default().push(func.clone());
        }
    }

    // Kahn's algorithm: start with functions that have no affected dependencies
    let mut queue: VecDeque<String> = VecDeque::new();
    let mut initial: Vec<String> =
        out_degree.iter().filter(|(_, deg)| **deg == 0).map(|(name, _)| name.clone()).collect();
    initial.sort(); // deterministic
    queue.extend(initial);

    let mut result = Vec::with_capacity(affected.len());

    while let Some(node) = queue.pop_front() {
        if let Some(callers) = reverse.get(&node) {
            let mut callers_sorted = callers.clone();
            callers_sorted.sort();
            for caller in callers_sorted {
                if let Some(deg) = out_degree.get_mut(&caller) {
                    *deg = deg.saturating_sub(1);
                    if *deg == 0 {
                        queue.push_back(caller);
                    }
                }
            }
        }
        result.push(node);
    }

    // Append cycle members in sorted order
    let in_result: FxHashSet<&str> = result.iter().map(String::as_str).collect();
    let mut remaining: Vec<String> =
        affected.iter().filter(|f| !in_result.contains(f.as_str())).cloned().collect();
    remaining.sort();
    result.extend(remaining);

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tracker_with_chain() -> DependencyTracker {
        // A calls B, B calls C: A -> B -> C
        let mut tracker = DependencyTracker::new();
        tracker.add_dependency("A", "B");
        tracker.add_dependency("B", "C");
        tracker
    }

    fn tracker_with_diamond() -> DependencyTracker {
        //   A
        //  / \
        // B   C
        //  \ /
        //   D
        let mut tracker = DependencyTracker::new();
        tracker.add_dependency("A", "B");
        tracker.add_dependency("A", "C");
        tracker.add_dependency("B", "D");
        tracker.add_dependency("C", "D");
        tracker
    }

    // -- DependencyTracker tests --

    #[test]
    fn test_tracker_new_is_empty() {
        let tracker = DependencyTracker::new();
        assert!(tracker.is_empty());
    }

    #[test]
    fn test_tracker_add_dependency() {
        let mut tracker = DependencyTracker::new();
        tracker.add_dependency("caller", "callee");

        assert!(tracker.direct_dependencies("caller").contains("callee"));
        assert!(tracker.direct_dependents("callee").contains("caller"));
    }

    #[test]
    fn test_tracker_add_dependencies_batch() {
        let mut tracker = DependencyTracker::new();
        tracker.add_dependencies("main", &["foo", "bar", "baz"]);

        let deps = tracker.direct_dependencies("main");
        assert_eq!(deps.len(), 3);
        assert!(deps.contains("foo"));
        assert!(deps.contains("bar"));
        assert!(deps.contains("baz"));
    }

    #[test]
    fn test_tracker_direct_dependencies_unknown() {
        let tracker = DependencyTracker::new();
        assert!(tracker.direct_dependencies("unknown").is_empty());
    }

    #[test]
    fn test_tracker_direct_dependents_unknown() {
        let tracker = DependencyTracker::new();
        assert!(tracker.direct_dependents("unknown").is_empty());
    }

    #[test]
    fn test_tracker_transitive_chain() {
        let tracker = tracker_with_chain();
        // C changes -> B and A should be affected
        let affected = tracker.transitive_dependents("C");
        assert_eq!(affected.len(), 2);
        assert!(affected.contains("B"));
        assert!(affected.contains("A"));
    }

    #[test]
    fn test_tracker_transitive_middle() {
        let tracker = tracker_with_chain();
        // B changes -> only A is affected (C is not a dependent of B)
        let affected = tracker.transitive_dependents("B");
        assert_eq!(affected.len(), 1);
        assert!(affected.contains("A"));
    }

    #[test]
    fn test_tracker_transitive_leaf() {
        let tracker = tracker_with_chain();
        // A changes -> nobody depends on A
        let affected = tracker.transitive_dependents("A");
        assert!(affected.is_empty());
    }

    #[test]
    fn test_tracker_transitive_diamond() {
        let tracker = tracker_with_diamond();
        // D changes -> B, C, A are all affected
        let affected = tracker.transitive_dependents("D");
        assert_eq!(affected.len(), 3);
        assert!(affected.contains("B"));
        assert!(affected.contains("C"));
        assert!(affected.contains("A"));
    }

    #[test]
    fn test_tracker_len() {
        let tracker = tracker_with_chain();
        assert_eq!(tracker.len(), 3); // A, B, C
    }

    #[test]
    fn test_tracker_clear() {
        let mut tracker = tracker_with_chain();
        tracker.clear();
        assert!(tracker.is_empty());
        assert!(tracker.direct_dependencies("A").is_empty());
    }

    // -- InvalidationPlan tests --

    #[test]
    fn test_plan_empty_changed() {
        let tracker = tracker_with_chain();
        let plan = plan_invalidation(&[], &tracker);
        assert!(plan.is_empty());
        assert_eq!(plan.len(), 0);
    }

    #[test]
    fn test_plan_leaf_change() {
        let tracker = tracker_with_chain();
        // C changes -> C, B, A all need re-verification
        let plan = plan_invalidation(&["C".to_string()], &tracker);
        assert_eq!(plan.len(), 3);
        assert!(plan.functions.contains(&"A".to_string()));
        assert!(plan.functions.contains(&"B".to_string()));
        assert!(plan.functions.contains(&"C".to_string()));
    }

    #[test]
    fn test_plan_callee_first_ordering() {
        let tracker = tracker_with_chain();
        let plan = plan_invalidation(&["C".to_string()], &tracker);

        let pos = |name: &str| plan.functions.iter().position(|n| n == name).unwrap();
        assert!(pos("C") < pos("B"), "C before B: {:?}", plan.functions);
        assert!(pos("B") < pos("A"), "B before A: {:?}", plan.functions);
    }

    #[test]
    fn test_plan_diamond_ordering() {
        let tracker = tracker_with_diamond();
        let plan = plan_invalidation(&["D".to_string()], &tracker);

        assert_eq!(plan.len(), 4); // D, B, C, A

        let pos = |name: &str| plan.functions.iter().position(|n| n == name).unwrap();
        assert!(pos("D") < pos("B"), "D before B: {:?}", plan.functions);
        assert!(pos("D") < pos("C"), "D before C: {:?}", plan.functions);
        assert!(pos("B") < pos("A"), "B before A: {:?}", plan.functions);
        assert!(pos("C") < pos("A"), "C before A: {:?}", plan.functions);
    }

    #[test]
    fn test_plan_middle_change_minimal() {
        let tracker = tracker_with_chain();
        // B changes -> only B and A are affected, not C
        let plan = plan_invalidation(&["B".to_string()], &tracker);
        assert_eq!(plan.len(), 2);
        assert!(plan.functions.contains(&"A".to_string()));
        assert!(plan.functions.contains(&"B".to_string()));
        assert!(!plan.functions.contains(&"C".to_string()));
    }

    #[test]
    fn test_plan_root_change_only_self() {
        let tracker = tracker_with_chain();
        // A changes -> only A (nobody depends on A)
        let plan = plan_invalidation(&["A".to_string()], &tracker);
        assert_eq!(plan.len(), 1);
        assert_eq!(plan.functions[0], "A");
    }

    #[test]
    fn test_plan_multiple_changes_deduped() {
        let tracker = tracker_with_chain();
        // Both B and C change -> A, B, C all affected but no duplicates
        let plan = plan_invalidation(&["B".to_string(), "C".to_string()], &tracker);
        assert_eq!(plan.len(), 3);
    }

    #[test]
    fn test_plan_reasons_present() {
        let tracker = tracker_with_chain();
        let plan = plan_invalidation(&["C".to_string()], &tracker);

        let reason_b = plan.reason_for("B").expect("should have reason for B");
        assert_eq!(reason_b.changed_root, "C");
        assert_eq!(reason_b.chain, vec!["C", "B"]);

        let reason_a = plan.reason_for("A").expect("should have reason for A");
        assert_eq!(reason_a.changed_root, "C");
        assert_eq!(reason_a.chain, vec!["C", "B", "A"]);
    }

    #[test]
    fn test_plan_reason_for_self() {
        let tracker = tracker_with_chain();
        let plan = plan_invalidation(&["C".to_string()], &tracker);

        let reason_c = plan.reason_for("C").expect("should have reason for C");
        assert_eq!(reason_c.changed_root, "C");
        assert_eq!(reason_c.chain, vec!["C"]);
    }

    #[test]
    fn test_plan_unknown_function() {
        let tracker = tracker_with_chain();
        // Unknown function has no dependents -> only itself
        let plan = plan_invalidation(&["unknown".to_string()], &tracker);
        assert_eq!(plan.len(), 1);
        assert_eq!(plan.functions[0], "unknown");
    }

    #[test]
    fn test_plan_no_reason_for_missing() {
        let tracker = tracker_with_chain();
        let plan = plan_invalidation(&["C".to_string()], &tracker);
        assert!(plan.reason_for("nonexistent").is_none());
    }

    // -- Cycle handling --

    #[test]
    fn test_tracker_transitive_with_cycle() {
        // A -> B -> C -> A (cycle)
        let mut tracker = DependencyTracker::new();
        tracker.add_dependency("A", "B");
        tracker.add_dependency("B", "C");
        tracker.add_dependency("C", "A");

        // C changes -> A and B are transitive dependents
        let affected = tracker.transitive_dependents("C");
        assert!(affected.contains("A"));
        assert!(affected.contains("B"));
    }

    #[test]
    fn test_plan_with_cycle() {
        let mut tracker = DependencyTracker::new();
        tracker.add_dependency("A", "B");
        tracker.add_dependency("B", "A");

        let plan = plan_invalidation(&["A".to_string()], &tracker);
        assert_eq!(plan.len(), 2);
        assert!(plan.functions.contains(&"A".to_string()));
        assert!(plan.functions.contains(&"B".to_string()));
    }

    // -- Duplicate dependency registration --

    #[test]
    fn test_tracker_duplicate_dependency_idempotent() {
        let mut tracker = DependencyTracker::new();
        tracker.add_dependency("A", "B");
        tracker.add_dependency("A", "B"); // duplicate

        assert_eq!(tracker.direct_dependencies("A").len(), 1);
        assert_eq!(tracker.direct_dependents("B").len(), 1);
    }
}
