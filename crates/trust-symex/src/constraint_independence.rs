// trust-symex/constraint_independence.rs: Constraint independence optimization
//
// KLEE-style constraint independence optimization — partitions path constraints
// into independent subsets based on shared variables. Constraints that share no
// variables are placed in separate partitions, enabling parallel/smaller solver
// invocations. Inspired by KLEE's constraint independence optimization
// (refs/klee/lib/Solver/).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for the constraint partitioner.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PartitionConfig {
    /// Maximum number of constraints allowed in a single partition.
    /// Partitions exceeding this are not split further — they represent
    /// genuinely coupled constraint sets.
    pub max_partition_size: usize,
    /// Whether to merge partitions smaller than `min_partition_size`.
    pub merge_small_partitions: bool,
    /// Minimum partition size; partitions below this are merged with the
    /// smallest compatible neighbor when `merge_small_partitions` is true.
    pub min_partition_size: usize,
}

impl Default for PartitionConfig {
    fn default() -> Self {
        Self { max_partition_size: 1024, merge_small_partitions: false, min_partition_size: 2 }
    }
}

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// A single partition: a group of constraints and the variables they reference.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstraintPartition {
    /// The constraints in this partition (as strings).
    pub partitions: Vec<Vec<String>>,
    /// The variables referenced by each constraint group.
    pub variable_groups: Vec<Vec<String>>,
}

/// A graph encoding variable-sharing dependencies between constraints.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IndependenceGraph {
    /// Constraint labels (one per node).
    pub nodes: Vec<String>,
    /// Edges: `(i, j)` means constraint `i` and constraint `j` share a variable.
    pub edges: Vec<(usize, usize)>,
}

/// Result of partitioning a constraint set.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PartitionResult {
    /// The independent partitions, each containing its constraints and variables.
    pub partitions: Vec<ConstraintPartition>,
    /// Total number of input constraints processed.
    pub total_constraints: usize,
    /// Number of resulting partitions.
    pub num_partitions: usize,
    /// Size of the largest partition.
    pub max_partition_size: usize,
}

// ---------------------------------------------------------------------------
// Partitioner
// ---------------------------------------------------------------------------

/// Partitions a set of string-encoded constraints into independent subsets
/// based on shared variable names. Two constraints are *dependent* when they
/// mention at least one common variable; transitively dependent constraints
/// end up in the same partition.
pub struct ConstraintPartitioner {
    config: PartitionConfig,
}

impl ConstraintPartitioner {
    /// Create a new partitioner with the given configuration.
    #[must_use]
    pub fn new(config: PartitionConfig) -> Self {
        Self { config }
    }

    /// Partition `constraints` into independent subsets.
    #[must_use]
    pub fn partition_constraints(&self, constraints: &[&str]) -> PartitionResult {
        if constraints.is_empty() {
            return PartitionResult {
                partitions: Vec::new(),
                total_constraints: 0,
                num_partitions: 0,
                max_partition_size: 0,
            };
        }

        let graph = self.build_dependency_graph(constraints);
        let components = self.connected_components(&graph);

        let mut raw_partitions: Vec<Vec<String>> = components
            .iter()
            .map(|comp| comp.iter().map(|&i| constraints[i].to_string()).collect())
            .collect();

        if self.config.merge_small_partitions {
            raw_partitions = self.merge_small(raw_partitions);
        }

        let result_partitions: Vec<ConstraintPartition> = raw_partitions
            .iter()
            .map(|group| {
                let vars: Vec<Vec<String>> =
                    group.iter().map(|c| self.extract_variables(c)).collect();
                ConstraintPartition { partitions: vec![group.clone()], variable_groups: vars }
            })
            .collect();

        let max_size = result_partitions
            .iter()
            .map(|p| p.partitions.iter().map(Vec::len).sum::<usize>())
            .max()
            .unwrap_or(0);

        PartitionResult {
            num_partitions: result_partitions.len(),
            total_constraints: constraints.len(),
            max_partition_size: max_size,
            partitions: result_partitions,
        }
    }

    /// Check whether two constraints are independent (share no variables).
    #[must_use]
    pub fn are_independent(&self, a: &str, b: &str) -> bool {
        let vars_a: BTreeSet<String> = self.extract_variables(a).into_iter().collect();
        let vars_b: BTreeSet<String> = self.extract_variables(b).into_iter().collect();
        vars_a.is_disjoint(&vars_b)
    }

    /// Build a dependency graph where nodes are constraints and edges connect
    /// constraints that share at least one variable.
    #[must_use]
    pub fn build_dependency_graph(&self, constraints: &[&str]) -> IndependenceGraph {
        let per_constraint_vars: Vec<BTreeSet<String>> =
            constraints.iter().map(|c| self.extract_variables(c).into_iter().collect()).collect();

        // Map variable -> set of constraint indices that mention it.
        let mut var_to_constraints: BTreeMap<&str, Vec<usize>> = BTreeMap::default();
        for (idx, vars) in per_constraint_vars.iter().enumerate() {
            for v in vars {
                var_to_constraints.entry(v.as_str()).or_default().push(idx);
            }
        }

        // Collect edges (deduplicated via BTreeSet of ordered pairs).
        let mut edge_set: BTreeSet<(usize, usize)> = BTreeSet::new();
        for indices in var_to_constraints.values() {
            for i in 0..indices.len() {
                for j in (i + 1)..indices.len() {
                    let a = indices[i].min(indices[j]);
                    let b = indices[i].max(indices[j]);
                    edge_set.insert((a, b));
                }
            }
        }

        IndependenceGraph {
            nodes: constraints.iter().map(|c| c.to_string()).collect(),
            edges: edge_set.into_iter().collect(),
        }
    }

    /// Extract variable names from a constraint string.
    ///
    /// Variables are identified as sequences of alphanumeric characters or
    /// underscores that start with a letter or underscore (standard identifier
    /// rules). Keywords and numeric literals are excluded.
    #[must_use]
    pub fn extract_variables(&self, constraint: &str) -> Vec<String> {
        let keywords: BTreeSet<&str> = [
            "and", "or", "not", "true", "false", "ite", "let", "forall", "exists", "assert",
            "check", "sat", "unsat", "define", "declare", "bvadd", "bvsub", "bvmul", "bvand",
            "bvor", "bvxor", "bvshl", "bvlshr", "bvashr", "bvnot", "bvneg", "bvult", "bvslt",
            "bvugt", "bvsgt", "bvule", "bvsle", "bvuge", "bvsge", "concat", "extract", "select",
            "store", "iff", "xor", "implies", "distinct", "if", "then", "else",
        ]
        .into_iter()
        .collect();

        let mut vars = BTreeSet::new();
        let chars: Vec<char> = constraint.chars().collect();
        let mut i = 0;

        while i < chars.len() {
            if chars[i].is_alphabetic() || chars[i] == '_' {
                let start = i;
                while i < chars.len() && (chars[i].is_alphanumeric() || chars[i] == '_') {
                    i += 1;
                }
                let token: String = chars[start..i].iter().collect();
                if !keywords.contains(token.as_str()) {
                    vars.insert(token);
                }
            } else {
                i += 1;
            }
        }

        vars.into_iter().collect()
    }

    /// Compute connected components of the independence graph via union-find.
    #[must_use]
    pub fn connected_components(&self, graph: &IndependenceGraph) -> Vec<Vec<usize>> {
        let n = graph.nodes.len();
        if n == 0 {
            return Vec::new();
        }

        // Union-Find
        let mut parent: Vec<usize> = (0..n).collect();
        let mut rank: Vec<usize> = vec![0; n];

        fn find(parent: &mut [usize], x: usize) -> usize {
            if parent[x] != x {
                parent[x] = find(parent, parent[x]);
            }
            parent[x]
        }

        fn union(parent: &mut [usize], rank: &mut [usize], a: usize, b: usize) {
            let ra = find(parent, a);
            let rb = find(parent, b);
            if ra == rb {
                return;
            }
            if rank[ra] < rank[rb] {
                parent[ra] = rb;
            } else if rank[ra] > rank[rb] {
                parent[rb] = ra;
            } else {
                parent[rb] = ra;
                rank[ra] += 1;
            }
        }

        for &(a, b) in &graph.edges {
            union(&mut parent, &mut rank, a, b);
        }

        // Group by root.
        let mut groups: BTreeMap<usize, Vec<usize>> = BTreeMap::default();
        for i in 0..n {
            let root = find(&mut parent, i);
            groups.entry(root).or_default().push(i);
        }

        // Return in deterministic order (sorted by smallest index in each group).
        let mut result: Vec<Vec<usize>> = groups.into_values().collect();
        result.sort_by_key(|g| g[0]);
        result
    }

    /// Merge partitions smaller than `min_partition_size` into the smallest
    /// existing partition to reduce overhead from very small solver calls.
    #[must_use]
    pub fn merge_small(&self, partitions: Vec<Vec<String>>) -> Vec<Vec<String>> {
        if partitions.is_empty() {
            return partitions;
        }

        let mut large: Vec<Vec<String>> = Vec::new();
        let mut small: Vec<String> = Vec::new();

        for p in partitions {
            if p.len() < self.config.min_partition_size {
                small.extend(p);
            } else {
                large.push(p);
            }
        }

        if small.is_empty() {
            return large;
        }

        if large.is_empty() {
            // Everything was small — just return as one partition.
            return vec![small];
        }

        // Merge small constraints into the smallest large partition.
        let min_idx = large
            .iter()
            .enumerate()
            .min_by_key(|(_, p)| p.len())
            .map(|(i, _)| i)
            // SAFETY: We checked large.is_empty() above and returned early.
            .unwrap_or_else(|| unreachable!("large empty after non-empty check"));
        large[min_idx].extend(small);
        large
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn default_partitioner() -> ConstraintPartitioner {
        ConstraintPartitioner::new(PartitionConfig::default())
    }

    #[test]
    fn test_extract_variables_simple() {
        let p = default_partitioner();
        let vars = p.extract_variables("x + y > 0");
        assert!(vars.contains(&"x".to_string()));
        assert!(vars.contains(&"y".to_string()));
        assert_eq!(vars.len(), 2);
    }

    #[test]
    fn test_extract_variables_keywords_excluded() {
        let p = default_partitioner();
        let vars = p.extract_variables("and or not x");
        assert_eq!(vars, vec!["x".to_string()]);
    }

    #[test]
    fn test_extract_variables_underscored() {
        let p = default_partitioner();
        let vars = p.extract_variables("_tmp_0 + var_1");
        assert!(vars.contains(&"_tmp_0".to_string()));
        assert!(vars.contains(&"var_1".to_string()));
        assert_eq!(vars.len(), 2);
    }

    #[test]
    fn test_extract_variables_empty() {
        let p = default_partitioner();
        let vars = p.extract_variables("42 + 7 > 10");
        assert!(vars.is_empty());
    }

    #[test]
    fn test_are_independent_true() {
        let p = default_partitioner();
        assert!(p.are_independent("x > 0", "y < 10"));
    }

    #[test]
    fn test_are_independent_false() {
        let p = default_partitioner();
        assert!(!p.are_independent("x > 0", "x < 10"));
    }

    #[test]
    fn test_are_independent_no_vars() {
        let p = default_partitioner();
        assert!(p.are_independent("42 > 0", "7 < 10"));
    }

    #[test]
    fn test_build_dependency_graph_no_edges() {
        let p = default_partitioner();
        let graph = p.build_dependency_graph(&["x > 0", "y < 5"]);
        assert_eq!(graph.nodes.len(), 2);
        assert!(graph.edges.is_empty());
    }

    #[test]
    fn test_build_dependency_graph_with_edges() {
        let p = default_partitioner();
        let graph = p.build_dependency_graph(&["x > 0", "x + y < 10", "z == 3"]);
        assert_eq!(graph.nodes.len(), 3);
        // x shared between 0 and 1
        assert!(graph.edges.contains(&(0, 1)));
        // z is separate — no edge to 0 or 1 (unless y connects, which it doesn't to 0)
        // Actually constraint 1 has y, constraint 2 has z — no overlap
        let has_edge_to_2 = graph.edges.iter().any(|(a, b)| *a == 2 || *b == 2);
        assert!(!has_edge_to_2);
    }

    #[test]
    fn test_connected_components_singleton() {
        let p = default_partitioner();
        let graph = IndependenceGraph { nodes: vec!["a".into()], edges: vec![] };
        let comps = p.connected_components(&graph);
        assert_eq!(comps.len(), 1);
        assert_eq!(comps[0], vec![0]);
    }

    #[test]
    fn test_connected_components_two_groups() {
        let p = default_partitioner();
        let graph = IndependenceGraph {
            nodes: vec!["a".into(), "b".into(), "c".into(), "d".into()],
            edges: vec![(0, 1), (2, 3)],
        };
        let comps = p.connected_components(&graph);
        assert_eq!(comps.len(), 2);
        assert!(comps.iter().any(|c| c == &[0, 1]));
        assert!(comps.iter().any(|c| c == &[2, 3]));
    }

    #[test]
    fn test_connected_components_all_connected() {
        let p = default_partitioner();
        let graph = IndependenceGraph {
            nodes: vec!["a".into(), "b".into(), "c".into()],
            edges: vec![(0, 1), (1, 2)],
        };
        let comps = p.connected_components(&graph);
        assert_eq!(comps.len(), 1);
        assert_eq!(comps[0], vec![0, 1, 2]);
    }

    #[test]
    fn test_connected_components_empty() {
        let p = default_partitioner();
        let graph = IndependenceGraph { nodes: vec![], edges: vec![] };
        let comps = p.connected_components(&graph);
        assert!(comps.is_empty());
    }

    #[test]
    fn test_partition_constraints_empty() {
        let p = default_partitioner();
        let result = p.partition_constraints(&[]);
        assert_eq!(result.total_constraints, 0);
        assert_eq!(result.num_partitions, 0);
        assert!(result.partitions.is_empty());
    }

    #[test]
    fn test_partition_constraints_all_independent() {
        let p = default_partitioner();
        let result = p.partition_constraints(&["x > 0", "y < 5", "z == 3"]);
        assert_eq!(result.total_constraints, 3);
        assert_eq!(result.num_partitions, 3);
        assert_eq!(result.max_partition_size, 1);
    }

    #[test]
    fn test_partition_constraints_all_dependent() {
        let p = default_partitioner();
        let result = p.partition_constraints(&["x > 0", "x + y < 10", "y > 1"]);
        assert_eq!(result.total_constraints, 3);
        assert_eq!(result.num_partitions, 1);
        assert_eq!(result.max_partition_size, 3);
    }

    #[test]
    fn test_partition_constraints_mixed() {
        let p = default_partitioner();
        let result = p.partition_constraints(&["x > 0", "x < 10", "y > 5", "z + w == 3", "w < 7"]);
        assert_eq!(result.total_constraints, 5);
        // x-group: {x > 0, x < 10}, y-group: {y > 5}, zw-group: {z+w==3, w<7}
        assert_eq!(result.num_partitions, 3);
    }

    #[test]
    fn test_merge_small_no_small() {
        let p = ConstraintPartitioner::new(PartitionConfig {
            merge_small_partitions: true,
            min_partition_size: 2,
            ..Default::default()
        });
        let parts = vec![vec!["a".into(), "b".into()], vec!["c".into(), "d".into()]];
        let merged = p.merge_small(parts.clone());
        assert_eq!(merged, parts);
    }

    #[test]
    fn test_merge_small_merges_singleton() {
        let p = ConstraintPartitioner::new(PartitionConfig {
            merge_small_partitions: true,
            min_partition_size: 2,
            ..Default::default()
        });
        let parts = vec![vec!["a".into(), "b".into()], vec!["c".into()]];
        let merged = p.merge_small(parts);
        assert_eq!(merged.len(), 1);
        assert_eq!(merged[0].len(), 3);
    }

    #[test]
    fn test_merge_small_all_small() {
        let p = ConstraintPartitioner::new(PartitionConfig {
            merge_small_partitions: true,
            min_partition_size: 3,
            ..Default::default()
        });
        let parts = vec![vec!["a".into()], vec!["b".into()]];
        let merged = p.merge_small(parts);
        assert_eq!(merged.len(), 1);
        assert_eq!(merged[0].len(), 2);
    }

    #[test]
    fn test_partition_with_merge_small() {
        let p = ConstraintPartitioner::new(PartitionConfig {
            merge_small_partitions: true,
            min_partition_size: 2,
            ..Default::default()
        });
        // x > 0, y > 5 are independent singletons, should be merged
        let result = p.partition_constraints(&["x > 0", "y > 5"]);
        assert_eq!(result.total_constraints, 2);
        // Both are singletons (size 1) < min_partition_size (2), so merged
        assert_eq!(result.num_partitions, 1);
    }

    #[test]
    fn test_partition_config_default() {
        let cfg = PartitionConfig::default();
        assert_eq!(cfg.max_partition_size, 1024);
        assert!(!cfg.merge_small_partitions);
        assert_eq!(cfg.min_partition_size, 2);
    }

    #[test]
    fn test_transitive_dependency() {
        let p = default_partitioner();
        // a shares x with b, b shares y with c => all in one partition
        let result = p.partition_constraints(&["x > 0", "x + y < 10", "y > 1"]);
        assert_eq!(result.num_partitions, 1);
    }

    #[test]
    fn test_single_constraint() {
        let p = default_partitioner();
        let result = p.partition_constraints(&["x > 0"]);
        assert_eq!(result.total_constraints, 1);
        assert_eq!(result.num_partitions, 1);
        assert_eq!(result.max_partition_size, 1);
    }

    #[test]
    fn test_merge_small_empty() {
        let p = default_partitioner();
        let merged = p.merge_small(Vec::new());
        assert!(merged.is_empty());
    }
}
