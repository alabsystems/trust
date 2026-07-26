// trust-symex alias analysis for symbolic pointers
//
// May/must alias analysis for symbolic pointers during symbolic execution.
// Maintains points-to sets and answers alias queries to enable precise
// symbolic memory modeling.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

/// Result of an alias query between two pointers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum AliasResult {
    /// Pointers definitely refer to the same location.
    MustAlias,
    /// Pointers may or may not refer to the same location.
    MayAlias,
    /// Pointers definitely refer to different locations.
    NoAlias,
}

/// A query asking whether two pointers alias.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AliasQuery {
    /// First pointer name.
    pub pointer_a: String,
    /// Second pointer name.
    pub pointer_b: String,
    /// Context (e.g., function or basic block) for the query.
    pub context: String,
}

/// A single entry in a points-to set: a pointer and its possible targets.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PointsToEntry {
    /// The pointer name.
    pub pointer: String,
    /// The set of locations this pointer may point to.
    pub targets: Vec<String>,
}

/// A collection of points-to entries representing alias information.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct AliasSet {
    /// All points-to entries in this set.
    pub entries: Vec<PointsToEntry>,
}

/// Alias analyzer maintaining points-to information for symbolic pointers.
///
/// Tracks which symbolic pointers may point to which targets, and answers
/// alias queries based on points-to set overlap.
#[derive(Debug, Clone)]
pub struct AliasAnalyzer {
    /// Map from pointer name to set of target locations.
    points_to: BTreeMap<String, BTreeSet<String>>,
    /// Map from pointer to most recently stored value.
    stores: BTreeMap<String, String>,
}

impl AliasAnalyzer {
    /// Create a new empty alias analyzer.
    #[must_use]
    pub fn new() -> Self {
        Self { points_to: BTreeMap::default(), stores: BTreeMap::default() }
    }

    /// Query whether two pointers alias.
    ///
    /// - `MustAlias` if both have exactly one target and it is the same.
    /// - `NoAlias` if their points-to sets are disjoint.
    /// - `MayAlias` otherwise (including when either pointer is unknown).
    #[must_use]
    pub fn query_alias(&self, a: &str, b: &str) -> AliasResult {
        if a == b {
            return AliasResult::MustAlias;
        }

        let targets_a = self.points_to.get(a);
        let targets_b = self.points_to.get(b);

        match (targets_a, targets_b) {
            (Some(ta), Some(tb)) => {
                let intersection: BTreeSet<_> = ta.intersection(tb).collect();
                if intersection.is_empty() {
                    AliasResult::NoAlias
                } else if ta.len() == 1 && tb.len() == 1 && ta == tb {
                    AliasResult::MustAlias
                } else {
                    AliasResult::MayAlias
                }
            }
            // Unknown pointer: conservatively assume may-alias.
            _ => AliasResult::MayAlias,
        }
    }

    /// Add a points-to edge: `pointer` may point to `target`.
    pub fn add_points_to(&mut self, pointer: &str, target: &str) {
        self.points_to.entry(pointer.to_owned()).or_default().insert(target.to_owned());
    }

    /// Compute the points-to set for a given pointer.
    #[must_use]
    pub fn compute_points_to(&self, pointer: &str) -> Vec<String> {
        self.points_to
            .get(pointer)
            .map(|targets| {
                let mut v: Vec<String> = targets.iter().cloned().collect();
                v.sort();
                v
            })
            .unwrap_or_default()
    }

    /// Merge two alias sets, taking the union of targets for each pointer.
    #[must_use]
    pub fn merge_alias_sets(&self, a: &AliasSet, b: &AliasSet) -> AliasSet {
        let mut merged: BTreeMap<String, BTreeSet<String>> = BTreeMap::default();

        for entry in a.entries.iter().chain(b.entries.iter()) {
            let set = merged.entry(entry.pointer.clone()).or_default();
            for target in &entry.targets {
                set.insert(target.clone());
            }
        }

        let mut entries: Vec<PointsToEntry> = merged
            .into_iter()
            .map(|(pointer, targets)| {
                let mut targets: Vec<String> = targets.into_iter().collect();
                targets.sort();
                PointsToEntry { pointer, targets }
            })
            .collect();
        entries.sort_by(|a, b| a.pointer.cmp(&b.pointer));

        AliasSet { entries }
    }

    /// Perform an alias-aware store: record `value` at `ptr` and return
    /// all other pointers that may alias `ptr` (and are thus affected).
    pub fn alias_aware_store(&mut self, ptr: &str, value: &str) -> Vec<String> {
        self.stores.insert(ptr.to_owned(), value.to_owned());

        let mut affected = Vec::new();
        let keys: Vec<String> = self.points_to.keys().cloned().collect();
        for key in &keys {
            if key == ptr {
                continue;
            }
            match self.query_alias(ptr, key) {
                AliasResult::MustAlias | AliasResult::MayAlias => {
                    affected.push(key.to_owned());
                }
                AliasResult::NoAlias => {}
            }
        }
        affected.sort();
        affected
    }

    /// Perform an alias-aware load: return all possible values that `ptr`
    /// could read, considering aliases.
    #[must_use]
    pub fn alias_aware_load(&self, ptr: &str) -> Vec<String> {
        let mut values = BTreeSet::default();

        // Direct store to this pointer.
        if let Some(v) = self.stores.get(ptr) {
            values.insert(v.clone());
        }

        // Stores through aliasing pointers.
        for (key, val) in &self.stores {
            if key == ptr {
                continue;
            }
            match self.query_alias(ptr, key) {
                AliasResult::MustAlias | AliasResult::MayAlias => {
                    values.insert(val.clone());
                }
                AliasResult::NoAlias => {}
            }
        }

        let mut result: Vec<String> = values.into_iter().collect();
        result.sort();
        result
    }

    /// Return all pointers that may alias the given pointer (excluding itself).
    #[must_use]
    pub fn all_aliases_of(&self, pointer: &str) -> Vec<String> {
        let mut aliases = Vec::new();
        for key in self.points_to.keys() {
            if key == pointer {
                continue;
            }
            match self.query_alias(pointer, key) {
                AliasResult::MustAlias | AliasResult::MayAlias => {
                    aliases.push(key.to_owned());
                }
                AliasResult::NoAlias => {}
            }
        }
        aliases.sort();
        aliases
    }

    /// Return the total number of pointers tracked.
    #[must_use]
    pub fn pointer_count(&self) -> usize {
        self.points_to.len()
    }
}

impl Default for AliasAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_alias_analyzer_new_empty() {
        let analyzer = AliasAnalyzer::new();
        assert_eq!(analyzer.pointer_count(), 0);
    }

    #[test]
    fn test_alias_analyzer_same_pointer_must_alias() {
        let analyzer = AliasAnalyzer::new();
        assert_eq!(analyzer.query_alias("p", "p"), AliasResult::MustAlias);
    }

    #[test]
    fn test_alias_analyzer_unknown_pointers_may_alias() {
        let analyzer = AliasAnalyzer::new();
        assert_eq!(analyzer.query_alias("p", "q"), AliasResult::MayAlias);
    }

    #[test]
    fn test_alias_analyzer_disjoint_no_alias() {
        let mut analyzer = AliasAnalyzer::new();
        analyzer.add_points_to("p", "x");
        analyzer.add_points_to("q", "y");
        assert_eq!(analyzer.query_alias("p", "q"), AliasResult::NoAlias);
    }

    #[test]
    fn test_alias_analyzer_shared_target_may_alias() {
        let mut analyzer = AliasAnalyzer::new();
        analyzer.add_points_to("p", "x");
        analyzer.add_points_to("p", "y");
        analyzer.add_points_to("q", "y");
        analyzer.add_points_to("q", "z");
        assert_eq!(analyzer.query_alias("p", "q"), AliasResult::MayAlias);
    }

    #[test]
    fn test_alias_analyzer_singleton_must_alias() {
        let mut analyzer = AliasAnalyzer::new();
        analyzer.add_points_to("p", "x");
        analyzer.add_points_to("q", "x");
        assert_eq!(analyzer.query_alias("p", "q"), AliasResult::MustAlias);
    }

    #[test]
    fn test_alias_analyzer_compute_points_to_empty() {
        let analyzer = AliasAnalyzer::new();
        assert!(analyzer.compute_points_to("p").is_empty());
    }

    #[test]
    fn test_alias_analyzer_compute_points_to_multiple() {
        let mut analyzer = AliasAnalyzer::new();
        analyzer.add_points_to("p", "b");
        analyzer.add_points_to("p", "a");
        analyzer.add_points_to("p", "c");
        assert_eq!(
            analyzer.compute_points_to("p"),
            vec!["a".to_owned(), "b".to_owned(), "c".to_owned()]
        );
    }

    #[test]
    fn test_alias_analyzer_add_duplicate_target() {
        let mut analyzer = AliasAnalyzer::new();
        analyzer.add_points_to("p", "x");
        analyzer.add_points_to("p", "x");
        assert_eq!(analyzer.compute_points_to("p"), vec!["x".to_owned()]);
    }

    #[test]
    fn test_alias_analyzer_pointer_count() {
        let mut analyzer = AliasAnalyzer::new();
        assert_eq!(analyzer.pointer_count(), 0);
        analyzer.add_points_to("p", "x");
        assert_eq!(analyzer.pointer_count(), 1);
        analyzer.add_points_to("q", "y");
        assert_eq!(analyzer.pointer_count(), 2);
        // Adding another target to existing pointer doesn't increase count.
        analyzer.add_points_to("p", "z");
        assert_eq!(analyzer.pointer_count(), 2);
    }

    #[test]
    fn test_alias_analyzer_merge_alias_sets() {
        let analyzer = AliasAnalyzer::new();
        let a = AliasSet {
            entries: vec![PointsToEntry { pointer: "p".to_owned(), targets: vec!["x".to_owned()] }],
        };
        let b = AliasSet {
            entries: vec![
                PointsToEntry { pointer: "p".to_owned(), targets: vec!["y".to_owned()] },
                PointsToEntry { pointer: "q".to_owned(), targets: vec!["z".to_owned()] },
            ],
        };
        let merged = analyzer.merge_alias_sets(&a, &b);
        assert_eq!(merged.entries.len(), 2);
        // "p" should have both "x" and "y".
        let p_entry = merged.entries.iter().find(|e| e.pointer == "p").unwrap();
        assert_eq!(p_entry.targets, vec!["x".to_owned(), "y".to_owned()]);
        // "q" should have "z".
        let q_entry = merged.entries.iter().find(|e| e.pointer == "q").unwrap();
        assert_eq!(q_entry.targets, vec!["z".to_owned()]);
    }

    #[test]
    fn test_alias_analyzer_alias_aware_store_returns_affected() {
        let mut analyzer = AliasAnalyzer::new();
        analyzer.add_points_to("p", "x");
        analyzer.add_points_to("q", "x");
        analyzer.add_points_to("r", "y");
        let affected = analyzer.alias_aware_store("p", "42");
        // q aliases p (both point to x), r does not.
        assert_eq!(affected, vec!["q".to_owned()]);
    }

    #[test]
    fn test_alias_analyzer_alias_aware_store_no_aliases() {
        let mut analyzer = AliasAnalyzer::new();
        analyzer.add_points_to("p", "x");
        analyzer.add_points_to("q", "y");
        let affected = analyzer.alias_aware_store("p", "42");
        assert!(affected.is_empty());
    }

    #[test]
    fn test_alias_analyzer_alias_aware_load_direct() {
        let mut analyzer = AliasAnalyzer::new();
        analyzer.add_points_to("p", "x");
        analyzer.alias_aware_store("p", "42");
        let values = analyzer.alias_aware_load("p");
        assert_eq!(values, vec!["42".to_owned()]);
    }

    #[test]
    fn test_alias_analyzer_alias_aware_load_through_alias() {
        let mut analyzer = AliasAnalyzer::new();
        analyzer.add_points_to("p", "x");
        analyzer.add_points_to("q", "x");
        analyzer.alias_aware_store("q", "99");
        let values = analyzer.alias_aware_load("p");
        // p can see q's store because they must-alias.
        assert_eq!(values, vec!["99".to_owned()]);
    }

    #[test]
    fn test_alias_analyzer_alias_aware_load_multiple_values() {
        let mut analyzer = AliasAnalyzer::new();
        analyzer.add_points_to("p", "x");
        analyzer.add_points_to("p", "y");
        analyzer.add_points_to("q", "y");
        analyzer.add_points_to("q", "z");
        analyzer.alias_aware_store("p", "10");
        analyzer.alias_aware_store("q", "20");
        let values = analyzer.alias_aware_load("p");
        // p sees its own store (10) and q's store (20) since p may-alias q.
        assert_eq!(values, vec!["10".to_owned(), "20".to_owned()]);
    }

    #[test]
    fn test_alias_analyzer_all_aliases_of() {
        let mut analyzer = AliasAnalyzer::new();
        analyzer.add_points_to("p", "x");
        analyzer.add_points_to("q", "x");
        analyzer.add_points_to("r", "y");
        let aliases = analyzer.all_aliases_of("p");
        assert_eq!(aliases, vec!["q".to_owned()]);
    }

    #[test]
    fn test_alias_analyzer_all_aliases_of_none() {
        let mut analyzer = AliasAnalyzer::new();
        analyzer.add_points_to("p", "x");
        analyzer.add_points_to("q", "y");
        analyzer.add_points_to("r", "z");
        let aliases = analyzer.all_aliases_of("p");
        assert!(aliases.is_empty());
    }

    #[test]
    fn test_alias_analyzer_default_impl() {
        let analyzer = AliasAnalyzer::default();
        assert_eq!(analyzer.pointer_count(), 0);
    }

    #[test]
    fn test_alias_set_default() {
        let set = AliasSet::default();
        assert!(set.entries.is_empty());
    }

    #[test]
    fn test_alias_query_struct() {
        let query = AliasQuery {
            pointer_a: "p".to_owned(),
            pointer_b: "q".to_owned(),
            context: "fn_main".to_owned(),
        };
        assert_eq!(query.pointer_a, "p");
        assert_eq!(query.pointer_b, "q");
        assert_eq!(query.context, "fn_main");
    }
}
