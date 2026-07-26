// trust-cache/spec_change_detector.rs: Detect spec changes and compute affected VCs
//
// Produces SpecFingerprint (SHA-256 of a function's requires + ensures clauses)
// and SpecChangeDetector which compares fingerprints across iterations to find
// which functions had their specs modified. Used by the invalidation pipeline
// to selectively flush stale cached results.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use sha2::{Digest, Sha256};

use crate::invalidation::{DependencyTracker, InvalidationPlan, plan_invalidation};

/// A fingerprint of a function's specification (requires + ensures + invariants).
///
/// If the fingerprint changes between iterations, the spec was modified and
/// cached verification results for this function (and its transitive callers)
/// must be invalidated.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SpecFingerprint {
    /// The function's def_path (unique identifier).
    pub def_path: String,
    /// SHA-256 hex digest of the canonical spec representation.
    pub hash: String,
}

impl SpecFingerprint {
    /// Compute a fingerprint from raw spec clause strings.
    ///
    /// The hash is computed over sorted, concatenated clause texts so that
    /// ordering changes within a clause category do not cause false positives.
    #[must_use]
    pub fn from_clauses(
        def_path: &str,
        requires: &[String],
        ensures: &[String],
        invariants: &[String],
    ) -> Self {
        let mut hasher = Sha256::new();
        hasher.update(b"requires:");
        let mut sorted_req: Vec<&str> = requires.iter().map(String::as_str).collect();
        sorted_req.sort();
        for clause in &sorted_req {
            hasher.update(clause.as_bytes());
            hasher.update(b"\n");
        }
        hasher.update(b"ensures:");
        let mut sorted_ens: Vec<&str> = ensures.iter().map(String::as_str).collect();
        sorted_ens.sort();
        for clause in &sorted_ens {
            hasher.update(clause.as_bytes());
            hasher.update(b"\n");
        }
        hasher.update(b"invariants:");
        let mut sorted_inv: Vec<&str> = invariants.iter().map(String::as_str).collect();
        sorted_inv.sort();
        for clause in &sorted_inv {
            hasher.update(clause.as_bytes());
            hasher.update(b"\n");
        }
        Self { def_path: def_path.to_string(), hash: format!("{:x}", hasher.finalize()) }
    }

    /// Compute a fingerprint from contracts (the existing pipeline type).
    #[must_use]
    pub fn from_contracts(def_path: &str, contracts: &[trust_types::Contract]) -> Self {
        use trust_types::ContractKind;
        let mut requires = Vec::new();
        let mut ensures = Vec::new();
        let mut invariants = Vec::new();
        for c in contracts {
            match c.kind {
                ContractKind::Requires => requires.push(c.body.clone()),
                ContractKind::Ensures => ensures.push(c.body.clone()),
                ContractKind::Invariant => invariants.push(c.body.clone()),
                ContractKind::Decreases => {} // not part of spec fingerprint
                _ => {}
            }
        }
        Self::from_clauses(def_path, &requires, &ensures, &invariants)
    }

    /// Fingerprint for a function with no specs.
    #[must_use]
    pub fn empty(def_path: &str) -> Self {
        Self::from_clauses(def_path, &[], &[], &[])
    }
}

/// Detects which functions' specs changed between two iterations.
///
/// Maintains a snapshot of spec fingerprints from the previous iteration
/// and compares against the current iteration to produce a changeset.
#[derive(Debug, Clone, Default)]
pub struct SpecChangeDetector {
    /// Fingerprints from the previous iteration, keyed by def_path.
    previous: FxHashMap<String, String>,
}

/// Summary of detected spec changes.
#[derive(Debug, Clone, Default)]
pub struct SpecChangeSummary {
    /// Functions whose specs were modified (hash changed).
    pub modified: Vec<String>,
    /// Functions that are new (no previous fingerprint).
    pub added: Vec<String>,
    /// Functions that were removed (had previous fingerprint, absent now).
    pub removed: Vec<String>,
}

impl SpecChangeSummary {
    /// All functions that need cache invalidation (modified + removed).
    ///
    /// Added functions are not in the cache yet, so they don't need invalidation.
    #[must_use]
    pub fn invalidation_roots(&self) -> Vec<String> {
        let mut roots = self.modified.clone();
        roots.extend(self.removed.iter().cloned());
        roots
    }

    /// Total number of changes detected.
    #[must_use]
    pub fn total_changes(&self) -> usize {
        // Diagnostic count over three live Vecs. saturating_add is exact for
        // every reachable state (three in-memory Vec<String> cannot hold
        // usize::MAX elements combined — each element occupies >= 24 bytes),
        // and even at the clamp `has_changes` stays correct: a nonzero sum
        // can never saturate DOWN to zero. Not checked_add: a diagnostic
        // count must not become a fallible operation or an abort.
        self.modified.len().saturating_add(self.added.len()).saturating_add(self.removed.len())
    }

    /// Whether any changes were detected.
    #[must_use]
    pub fn has_changes(&self) -> bool {
        self.total_changes() > 0
    }
}

impl SpecChangeDetector {
    /// Create a new detector with no previous state.
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a detector pre-loaded with previous fingerprints.
    pub fn with_previous(fingerprints: &[SpecFingerprint]) -> Self {
        let previous =
            fingerprints.iter().map(|fp| (fp.def_path.clone(), fp.hash.clone())).collect();
        Self { previous }
    }

    /// Update the previous snapshot and detect changes.
    ///
    /// After this call, `previous` is replaced with the new fingerprints.
    pub fn detect_changes(&mut self, current: &[SpecFingerprint]) -> SpecChangeSummary {
        let mut summary = SpecChangeSummary::default();

        let current_map: FxHashMap<&str, &str> =
            current.iter().map(|fp| (fp.def_path.as_str(), fp.hash.as_str())).collect();

        // Check each current function against previous
        for fp in current {
            match self.previous.get(&fp.def_path) {
                Some(prev_hash) if prev_hash != &fp.hash => {
                    summary.modified.push(fp.def_path.clone());
                }
                None => {
                    summary.added.push(fp.def_path.clone());
                }
                _ => {} // unchanged
            }
        }

        // Check for removed functions
        for prev_path in self.previous.keys() {
            if !current_map.contains_key(prev_path.as_str()) {
                summary.removed.push(prev_path.clone());
            }
        }

        // Sort for deterministic output
        summary.modified.sort();
        summary.added.sort();
        summary.removed.sort();

        // Update snapshot
        self.previous = current.iter().map(|fp| (fp.def_path.clone(), fp.hash.clone())).collect();

        summary
    }

    /// Number of tracked functions in the previous snapshot.
    #[must_use]
    pub fn tracked_count(&self) -> usize {
        self.previous.len()
    }
}

/// Compute which cached VCs need re-verification after spec changes.
///
/// Combines spec change detection with dependency tracking to produce
/// a full invalidation plan: the changed functions plus all their
/// transitive callers.
#[must_use]
pub(crate) fn affected_vcs(
    changes: &SpecChangeSummary,
    deps: &DependencyTracker,
) -> InvalidationPlan {
    let roots = changes.invalidation_roots();
    plan_invalidation(&roots, deps)
}

#[cfg(test)]
mod tests {
    use trust_types::fx::FxHashSet;
    use trust_types::{Contract, ContractKind, SourceSpan};

    use super::*;

    // Trust: test-only convenience functions moved from production code.

    /// Convenience: detect changes and compute affected VCs in one step.
    fn detect_and_plan(
        detector: &mut SpecChangeDetector,
        current_fingerprints: &[SpecFingerprint],
        deps: &DependencyTracker,
    ) -> (SpecChangeSummary, InvalidationPlan) {
        let summary = detector.detect_changes(current_fingerprints);
        let plan = affected_vcs(&summary, deps);
        (summary, plan)
    }

    /// Compute the set of all def_paths that should be invalidated in the cache
    /// given spec changes and a dependency graph.
    fn invalidation_set(
        changes: &SpecChangeSummary,
        deps: &DependencyTracker,
    ) -> FxHashSet<String> {
        let plan = affected_vcs(changes, deps);
        plan.functions.into_iter().collect()
    }

    // -----------------------------------------------------------------------
    // SpecFingerprint tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_fingerprint_deterministic() {
        let fp1 = SpecFingerprint::from_clauses(
            "crate::foo",
            &["x > 0".to_string()],
            &["result >= 0".to_string()],
            &[],
        );
        let fp2 = SpecFingerprint::from_clauses(
            "crate::foo",
            &["x > 0".to_string()],
            &["result >= 0".to_string()],
            &[],
        );
        assert_eq!(fp1.hash, fp2.hash, "same inputs must produce same hash");
    }

    #[test]
    fn test_fingerprint_is_sha256_hex() {
        let fp = SpecFingerprint::from_clauses("f", &[], &[], &[]);
        assert_eq!(fp.hash.len(), 64);
        assert!(fp.hash.chars().all(|c| c.is_ascii_hexdigit()));
    }

    #[test]
    fn test_fingerprint_changes_with_requires() {
        let fp1 = SpecFingerprint::from_clauses("f", &["x > 0".into()], &[], &[]);
        let fp2 = SpecFingerprint::from_clauses("f", &["x > 1".into()], &[], &[]);
        assert_ne!(fp1.hash, fp2.hash);
    }

    #[test]
    fn test_fingerprint_changes_with_ensures() {
        let fp1 = SpecFingerprint::from_clauses("f", &[], &["r > 0".into()], &[]);
        let fp2 = SpecFingerprint::from_clauses("f", &[], &["r > 1".into()], &[]);
        assert_ne!(fp1.hash, fp2.hash);
    }

    #[test]
    fn test_fingerprint_changes_with_invariants() {
        let fp1 = SpecFingerprint::from_clauses("f", &[], &[], &["n >= 0".into()]);
        let fp2 = SpecFingerprint::from_clauses("f", &[], &[], &["n >= 1".into()]);
        assert_ne!(fp1.hash, fp2.hash);
    }

    #[test]
    fn test_fingerprint_order_independent_within_category() {
        let fp1 = SpecFingerprint::from_clauses("f", &["a > 0".into(), "b > 0".into()], &[], &[]);
        let fp2 = SpecFingerprint::from_clauses("f", &["b > 0".into(), "a > 0".into()], &[], &[]);
        assert_eq!(fp1.hash, fp2.hash, "clause order should not matter");
    }

    #[test]
    fn test_fingerprint_empty() {
        let fp = SpecFingerprint::empty("crate::bar");
        assert_eq!(fp.def_path, "crate::bar");
        assert_eq!(fp.hash.len(), 64);
    }

    #[test]
    fn test_fingerprint_empty_vs_nonempty() {
        let fp_empty = SpecFingerprint::empty("f");
        let fp_with = SpecFingerprint::from_clauses("f", &["x > 0".into()], &[], &[]);
        assert_ne!(fp_empty.hash, fp_with.hash);
    }

    #[test]
    fn test_fingerprint_from_contracts() {
        let contracts = vec![
            Contract {
                kind: ContractKind::Requires,
                span: SourceSpan::default(),
                body: "x > 0".to_string(),
            },
            Contract {
                kind: ContractKind::Ensures,
                span: SourceSpan::default(),
                body: "result >= 0".to_string(),
            },
            Contract {
                kind: ContractKind::Decreases,
                span: SourceSpan::default(),
                body: "n".to_string(),
            },
        ];
        let fp = SpecFingerprint::from_contracts("crate::foo", &contracts);
        // Decreases should not affect fingerprint
        let fp_no_dec = SpecFingerprint::from_clauses(
            "crate::foo",
            &["x > 0".into()],
            &["result >= 0".into()],
            &[],
        );
        assert_eq!(fp.hash, fp_no_dec.hash, "decreases should not affect fingerprint");
    }

    #[test]
    fn test_fingerprint_requires_vs_ensures_differ() {
        let fp1 = SpecFingerprint::from_clauses("f", &["x > 0".into()], &[], &[]);
        let fp2 = SpecFingerprint::from_clauses("f", &[], &["x > 0".into()], &[]);
        assert_ne!(fp1.hash, fp2.hash, "requires vs ensures must differ");
    }

    #[test]
    fn test_total_changes_exact_across_all_three_buckets() {
        // total_changes is a saturating sum (hardened_panic_boundary site);
        // it must stay EXACT for all reachable states and keep has_changes
        // consistent. The saturation point itself is untestable — three live
        // Vec<String> cannot hold usize::MAX elements combined — so this
        // locks the exactness + consistency contract.
        let summary = SpecChangeSummary {
            modified: vec!["a".into(), "b".into()],
            added: vec!["c".into()],
            removed: vec!["d".into(), "e".into(), "f".into()],
        };
        assert_eq!(summary.total_changes(), 6);
        assert!(summary.has_changes());

        let empty = SpecChangeSummary::default();
        assert_eq!(empty.total_changes(), 0);
        assert!(!empty.has_changes());

        // Single-bucket cases: the sum must count each bucket.
        let only_removed = SpecChangeSummary {
            modified: vec![],
            added: vec![],
            removed: vec!["x".into()],
        };
        assert_eq!(only_removed.total_changes(), 1);
        assert!(only_removed.has_changes());
    }

    // -----------------------------------------------------------------------
    // SpecChangeDetector tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_detector_new_empty() {
        let detector = SpecChangeDetector::new();
        assert_eq!(detector.tracked_count(), 0);
    }

    #[test]
    fn test_detector_first_iteration_all_added() {
        let mut detector = SpecChangeDetector::new();
        let fps = vec![
            SpecFingerprint::from_clauses("f", &["x > 0".into()], &[], &[]),
            SpecFingerprint::from_clauses("g", &[], &["r > 0".into()], &[]),
        ];
        let summary = detector.detect_changes(&fps);
        assert_eq!(summary.added.len(), 2);
        assert!(summary.modified.is_empty());
        assert!(summary.removed.is_empty());
        assert_eq!(summary.total_changes(), 2);
    }

    #[test]
    fn test_detector_no_changes() {
        let fps = vec![SpecFingerprint::from_clauses("f", &["x > 0".into()], &[], &[])];
        let mut detector = SpecChangeDetector::with_previous(&fps);
        let summary = detector.detect_changes(&fps);
        assert!(!summary.has_changes());
        assert_eq!(summary.total_changes(), 0);
    }

    #[test]
    fn test_detector_modified_spec() {
        let fps_v1 = vec![SpecFingerprint::from_clauses("f", &["x > 0".into()], &[], &[])];
        let fps_v2 = vec![SpecFingerprint::from_clauses("f", &["x > 1".into()], &[], &[])];
        let mut detector = SpecChangeDetector::with_previous(&fps_v1);
        let summary = detector.detect_changes(&fps_v2);
        assert_eq!(summary.modified, vec!["f"]);
        assert!(summary.added.is_empty());
        assert!(summary.removed.is_empty());
    }

    #[test]
    fn test_detector_added_function() {
        let fps_v1 = vec![SpecFingerprint::from_clauses("f", &["x > 0".into()], &[], &[])];
        let fps_v2 = vec![
            SpecFingerprint::from_clauses("f", &["x > 0".into()], &[], &[]),
            SpecFingerprint::from_clauses("g", &["y > 0".into()], &[], &[]),
        ];
        let mut detector = SpecChangeDetector::with_previous(&fps_v1);
        let summary = detector.detect_changes(&fps_v2);
        assert!(summary.modified.is_empty());
        assert_eq!(summary.added, vec!["g"]);
        assert!(summary.removed.is_empty());
    }

    #[test]
    fn test_detector_removed_function() {
        let fps_v1 = vec![
            SpecFingerprint::from_clauses("f", &["x > 0".into()], &[], &[]),
            SpecFingerprint::from_clauses("g", &["y > 0".into()], &[], &[]),
        ];
        let fps_v2 = vec![SpecFingerprint::from_clauses("f", &["x > 0".into()], &[], &[])];
        let mut detector = SpecChangeDetector::with_previous(&fps_v1);
        let summary = detector.detect_changes(&fps_v2);
        assert!(summary.modified.is_empty());
        assert!(summary.added.is_empty());
        assert_eq!(summary.removed, vec!["g"]);
    }

    #[test]
    fn test_detector_mixed_changes() {
        let fps_v1 = vec![
            SpecFingerprint::from_clauses("f", &["x > 0".into()], &[], &[]),
            SpecFingerprint::from_clauses("g", &["y > 0".into()], &[], &[]),
        ];
        let fps_v2 = vec![
            SpecFingerprint::from_clauses("f", &["x > 1".into()], &[], &[]), // modified
            SpecFingerprint::from_clauses("h", &["z > 0".into()], &[], &[]), // added
                                                                             // g removed
        ];
        let mut detector = SpecChangeDetector::with_previous(&fps_v1);
        let summary = detector.detect_changes(&fps_v2);
        assert_eq!(summary.modified, vec!["f"]);
        assert_eq!(summary.added, vec!["h"]);
        assert_eq!(summary.removed, vec!["g"]);
        assert_eq!(summary.total_changes(), 3);
    }

    #[test]
    fn test_detector_updates_snapshot() {
        let fps_v1 = vec![SpecFingerprint::from_clauses("f", &["x > 0".into()], &[], &[])];
        let mut detector = SpecChangeDetector::new();
        let _ = detector.detect_changes(&fps_v1);
        assert_eq!(detector.tracked_count(), 1);

        // Second call with same data: no changes
        let summary = detector.detect_changes(&fps_v1);
        assert!(!summary.has_changes());
    }

    #[test]
    fn test_invalidation_roots_excludes_added() {
        let summary = SpecChangeSummary {
            modified: vec!["f".to_string()],
            added: vec!["new_fn".to_string()],
            removed: vec!["old_fn".to_string()],
        };
        let roots = summary.invalidation_roots();
        assert!(roots.contains(&"f".to_string()));
        assert!(roots.contains(&"old_fn".to_string()));
        assert!(!roots.contains(&"new_fn".to_string()));
    }

    // -----------------------------------------------------------------------
    // Integration: affected_vcs + detect_and_plan
    // -----------------------------------------------------------------------

    #[test]
    fn test_affected_vcs_with_deps() {
        let mut deps = DependencyTracker::new();
        deps.add_dependency("caller", "callee");
        deps.add_dependency("top", "caller");

        let summary = SpecChangeSummary {
            modified: vec!["callee".to_string()],
            added: vec![],
            removed: vec![],
        };
        let plan = affected_vcs(&summary, &deps);
        assert!(plan.functions.contains(&"callee".to_string()));
        assert!(plan.functions.contains(&"caller".to_string()));
        assert!(plan.functions.contains(&"top".to_string()));
        assert_eq!(plan.len(), 3);
    }

    #[test]
    fn test_affected_vcs_no_deps() {
        let deps = DependencyTracker::new();
        let summary = SpecChangeSummary {
            modified: vec!["standalone".to_string()],
            added: vec![],
            removed: vec![],
        };
        let plan = affected_vcs(&summary, &deps);
        assert_eq!(plan.len(), 1);
        assert_eq!(plan.functions[0], "standalone");
    }

    #[test]
    fn test_affected_vcs_no_changes() {
        let deps = DependencyTracker::new();
        let summary = SpecChangeSummary::default();
        let plan = affected_vcs(&summary, &deps);
        assert!(plan.is_empty());
    }

    #[test]
    fn test_detect_and_plan_end_to_end() {
        let fps_v1 = vec![
            SpecFingerprint::from_clauses("lib::a", &["x > 0".into()], &[], &[]),
            SpecFingerprint::from_clauses("lib::b", &[], &["r > 0".into()], &[]),
        ];
        let fps_v2 = vec![
            SpecFingerprint::from_clauses("lib::a", &["x > 0".into()], &[], &[]),
            SpecFingerprint::from_clauses("lib::b", &[], &["r > 1".into()], &[]), // changed
        ];

        let mut deps = DependencyTracker::new();
        deps.add_dependency("lib::a", "lib::b"); // a calls b

        let mut detector = SpecChangeDetector::with_previous(&fps_v1);
        let (summary, plan) = detect_and_plan(&mut detector, &fps_v2, &deps);

        assert_eq!(summary.modified, vec!["lib::b"]);
        assert!(plan.functions.contains(&"lib::b".to_string()));
        assert!(plan.functions.contains(&"lib::a".to_string()));
    }

    #[test]
    fn test_invalidation_set_membership() {
        let mut deps = DependencyTracker::new();
        deps.add_dependency("A", "B");
        deps.add_dependency("B", "C");

        let summary =
            SpecChangeSummary { modified: vec!["C".to_string()], added: vec![], removed: vec![] };
        let set = invalidation_set(&summary, &deps);
        assert!(set.contains("A"));
        assert!(set.contains("B"));
        assert!(set.contains("C"));
        assert!(!set.contains("D"));
    }

    #[test]
    fn test_detector_with_previous() {
        let fps = vec![
            SpecFingerprint::from_clauses("f", &["x > 0".into()], &[], &[]),
            SpecFingerprint::from_clauses("g", &["y > 0".into()], &[], &[]),
        ];
        let detector = SpecChangeDetector::with_previous(&fps);
        assert_eq!(detector.tracked_count(), 2);
    }

    #[test]
    fn test_fingerprint_adding_clause_changes_hash() {
        let fp1 = SpecFingerprint::from_clauses("f", &["x > 0".into()], &[], &[]);
        let fp2 = SpecFingerprint::from_clauses("f", &["x > 0".into(), "y > 0".into()], &[], &[]);
        assert_ne!(fp1.hash, fp2.hash, "adding a clause must change hash");
    }

    #[test]
    fn test_fingerprint_removing_clause_changes_hash() {
        let fp1 = SpecFingerprint::from_clauses("f", &["x > 0".into(), "y > 0".into()], &[], &[]);
        let fp2 = SpecFingerprint::from_clauses("f", &["x > 0".into()], &[], &[]);
        assert_ne!(fp1.hash, fp2.hash, "removing a clause must change hash");
    }
}
