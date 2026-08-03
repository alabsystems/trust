// VC strength comparison and subsumption ordering
//
// Provides syntactic comparison of verification condition formulas to detect
// when one VC implies another (subsumption). This enables discharging VCs
// that are logically weaker than an already-proved VC without calling the solver.
//
// Key insight: if VC_A's formula is a syntactic subset of VC_B's conjuncts,
// then B is stronger than A (B implies A). Proving B automatically proves A.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{Formula, VcKind, VerificationCondition};

// Strength comparison result between two formulas.
/// Describes the logical strength relationship between two formulas.
///
/// In verification, formula A is *stronger* than B if A implies B
/// (any model satisfying A also satisfies B). Conversely, A is *weaker*
/// than B if B implies A.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[must_use]
#[non_exhaustive]
pub enum VcStrength {
    /// A is strictly stronger than B (A implies B, but B does not imply A).
    Stronger,
    /// A is strictly weaker than B (B implies A, but A does not imply B).
    Weaker,
    /// A and B are logically equivalent (A implies B and B implies A).
    Equivalent,
    /// Neither formula implies the other.
    Incomparable,
}

// Subsumption graph for VC discharge optimization.
/// A directed graph where edge `(i, j)` means `VC[i]` subsumes `VC[j]`
/// (proving `VC[i]` automatically discharges `VC[j]`).
///
/// Built from pairwise syntactic comparison of VC formulas.
#[derive(Debug, Clone)]
#[must_use]
pub struct SubsumptionGraph {
    /// Number of VCs in the graph.
    pub(crate) vc_count: usize,
    /// Adjacency list: subsumes[i] = list of indices j where VC[i] subsumes VC[j].
    /// i.e., VC[i] is stronger than or equivalent to VC[j].
    pub(crate) subsumes: FxHashMap<usize, Vec<usize>>,
}

impl SubsumptionGraph {
    /// Returns the total number of VCs in the graph.
    #[must_use]
    pub fn vc_count(&self) -> usize {
        self.vc_count
    }

    /// Returns the indices of VCs that `VC[idx]` subsumes (is stronger than or equivalent to).
    #[must_use]
    pub fn subsumed_by(&self, idx: usize) -> &[usize] {
        self.subsumes.get(&idx).map_or(&[], |v| v.as_slice())
    }

    /// Returns the total number of subsumption edges in the graph.
    #[must_use]
    pub fn edge_count(&self) -> usize {
        self.subsumes.values().map(|v| v.len()).sum()
    }
}

// Extract conjuncts from a formula.
/// Recursively flatten nested `And` nodes into a set of conjuncts.
/// A non-And formula is treated as a single-element set.
fn collect_conjuncts(formula: &Formula) -> Vec<&Formula> {
    match formula {
        Formula::And(terms) => terms.iter().flat_map(collect_conjuncts).collect(),
        other => vec![other],
    }
}

// Syntactic formula comparison.
/// Compare two formulas for syntactic strength (implication).
///
/// Uses conjunct-subset analysis: if A's conjuncts are a superset of B's
/// conjuncts, then A is stronger (A implies B, because A requires more).
/// If they are equal sets, the formulas are equivalent.
///
/// This is a conservative (sound) approximation -- it may return
/// `Incomparable` for formulas that are semantically related but
/// syntactically different.
pub fn compare_formulas(a: &Formula, b: &Formula) -> VcStrength {
    // Fast path: structural equality.
    if a == b {
        return VcStrength::Equivalent;
    }

    // Extract conjuncts from both formulas.
    let conjuncts_a = collect_conjuncts(a);
    let conjuncts_b = collect_conjuncts(b);

    // Check subset relationships using Vec-based containment.
    // Formula implements PartialEq + Eq but not Hash, so we use linear scans.
    // This is acceptable because conjunct lists are typically small (<20).
    let a_subset_b = conjuncts_a.iter().all(|ca| conjuncts_b.iter().any(|cb| ca == cb));
    let b_subset_a = conjuncts_b.iter().all(|cb| conjuncts_a.iter().any(|ca| ca == cb));

    match (a_subset_b, b_subset_a) {
        // A's conjuncts == B's conjuncts: equivalent formulas.
        (true, true) => VcStrength::Equivalent,
        // A's conjuncts are a strict subset of B's conjuncts:
        // B has more constraints, so B is stronger (B implies A).
        // Therefore A is weaker than B.
        (true, false) => VcStrength::Weaker,
        // B's conjuncts are a strict subset of A's conjuncts:
        // A has more constraints, so A is stronger (A implies B).
        // Therefore A is stronger than B.
        (false, true) => VcStrength::Stronger,
        // Neither is a subset of the other: incomparable.
        (false, false) => VcStrength::Incomparable,
    }
}

// Build a subsumption graph from a set of VCs.
/// Construct a subsumption graph by pairwise comparing all VC formulas.
///
/// An edge `(i, j)` in the graph means proving `VC[i]` is sufficient to
/// also discharge `VC[j]` (`VC[i]`'s formula is stronger than or equivalent
/// to `VC[j]`'s formula).
///
/// Complexity: O(n^2 * m) where n is the number of VCs and m is the
/// average number of conjuncts per formula.
pub fn build_subsumption_graph(vcs: &[VerificationCondition]) -> SubsumptionGraph {
    let vc_count = vcs.len();
    let mut subsumes: FxHashMap<usize, Vec<usize>> = FxHashMap::default();

    for i in 0..vc_count {
        for j in 0..vc_count {
            if i == j {
                continue;
            }
            if matches!(vcs[i].kind, VcKind::UnsupportedMir { .. })
                || matches!(vcs[j].kind, VcKind::UnsupportedMir { .. })
            {
                continue;
            }
            let strength = compare_formulas(&vcs[i].formula, &vcs[j].formula);
            match strength {
                VcStrength::Stronger | VcStrength::Equivalent => {
                    subsumes.entry(i).or_default().push(j);
                }
                VcStrength::Weaker | VcStrength::Incomparable => {}
            }
        }
    }

    SubsumptionGraph { vc_count, subsumes }
}

// Discharge subsumed VCs given a proved index.
/// Given that `VC[proved_idx]` has been proved, return the indices of all
/// VCs that are transitively subsumed and can be discharged without
/// calling the solver.
///
/// Performs a BFS/DFS traversal from `proved_idx` in the subsumption graph
/// to find all reachable (transitively subsumed) VCs.
#[must_use]
pub fn discharge_subsumed(graph: &SubsumptionGraph, proved_idx: usize) -> Vec<usize> {
    let mut discharged = Vec::new();
    let mut visited = FxHashSet::default();
    let mut stack = vec![proved_idx];

    while let Some(current) = stack.pop() {
        for &subsumed in graph.subsumed_by(current) {
            if visited.insert(subsumed) {
                discharged.push(subsumed);
                // Transitively follow subsumption edges.
                stack.push(subsumed);
            }
        }
    }

    discharged.sort_unstable();
    discharged
}

#[cfg(test)]
mod tests {
    use trust_types::{Formula, Sort, SourceSpan, VcKind, VerificationCondition};

    use super::*;

    // Helper to build a Formula variable.
    fn var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }

    // Helper to build a simple VC with the given formula.
    fn make_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    // -----------------------------------------------------------------------
    // compare_formulas tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_compare_formulas_identical_returns_equivalent() {
        let f = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        assert_eq!(compare_formulas(&f, &f), VcStrength::Equivalent);
    }

    #[test]
    fn test_compare_formulas_same_conjuncts_different_order_returns_equivalent() {
        let a = Formula::And(vec![
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(1))),
        ]);
        let b = Formula::And(vec![
            Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(1))),
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
        ]);
        assert_eq!(compare_formulas(&a, &b), VcStrength::Equivalent);
    }

    #[test]
    fn test_compare_formulas_superset_conjuncts_returns_stronger() {
        // a = (x == 0) AND (y == 1) AND (z == 2)
        // b = (x == 0) AND (y == 1)
        // a is stronger because it has more conjuncts (implies b)
        let a = Formula::And(vec![
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(1))),
            Formula::Eq(Box::new(var("z")), Box::new(Formula::Int(2))),
        ]);
        let b = Formula::And(vec![
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(1))),
        ]);
        assert_eq!(compare_formulas(&a, &b), VcStrength::Stronger);
    }

    #[test]
    fn test_compare_formulas_subset_conjuncts_returns_weaker() {
        // a = (x == 0)
        // b = (x == 0) AND (y == 1)
        // a is weaker because b has more conjuncts
        let a = Formula::And(vec![Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)))]);
        let b = Formula::And(vec![
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(1))),
        ]);
        assert_eq!(compare_formulas(&a, &b), VcStrength::Weaker);
    }

    #[test]
    fn test_compare_formulas_disjoint_returns_incomparable() {
        let a = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let b = Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(1)));
        assert_eq!(compare_formulas(&a, &b), VcStrength::Incomparable);
    }

    #[test]
    fn test_compare_formulas_overlapping_but_not_subset_returns_incomparable() {
        // a = (x == 0) AND (y == 1)
        // b = (x == 0) AND (z == 2)
        // They share (x == 0) but neither is a subset of the other
        let a = Formula::And(vec![
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(1))),
        ]);
        let b = Formula::And(vec![
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Eq(Box::new(var("z")), Box::new(Formula::Int(2))),
        ]);
        assert_eq!(compare_formulas(&a, &b), VcStrength::Incomparable);
    }

    #[test]
    fn test_compare_formulas_bool_literals() {
        assert_eq!(
            compare_formulas(&Formula::Bool(true), &Formula::Bool(true)),
            VcStrength::Equivalent
        );
        assert_eq!(
            compare_formulas(&Formula::Bool(true), &Formula::Bool(false)),
            VcStrength::Incomparable
        );
    }

    #[test]
    fn test_compare_formulas_nested_and_flattening() {
        // a = And(And(x==0, y==1), z==2)  (3 conjuncts after flattening)
        // b = And(x==0, y==1)             (2 conjuncts)
        // a is stronger because it flattens to 3 conjuncts that include b's 2
        let x_eq_0 = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let y_eq_1 = Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(1)));
        let z_eq_2 = Formula::Eq(Box::new(var("z")), Box::new(Formula::Int(2)));
        let a = Formula::And(vec![Formula::And(vec![x_eq_0.clone(), y_eq_1.clone()]), z_eq_2]);
        let b = Formula::And(vec![x_eq_0, y_eq_1]);
        assert_eq!(compare_formulas(&a, &b), VcStrength::Stronger);
    }

    #[test]
    fn test_compare_formulas_single_vs_and_containing_it() {
        // a = (x == 0)
        // b = And((x == 0), (y == 1))
        // a is weaker (subset of b's conjuncts)
        let x_eq_0 = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let b = Formula::And(vec![
            x_eq_0.clone(),
            Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(1))),
        ]);
        assert_eq!(compare_formulas(&x_eq_0, &b), VcStrength::Weaker);
    }

    // -----------------------------------------------------------------------
    // build_subsumption_graph tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_build_subsumption_graph_empty() {
        let graph = build_subsumption_graph(&[]);
        assert_eq!(graph.vc_count(), 0);
        assert_eq!(graph.edge_count(), 0);
    }

    #[test]
    fn test_build_subsumption_graph_single_vc() {
        let vcs = vec![make_vc(Formula::Bool(true))];
        let graph = build_subsumption_graph(&vcs);
        assert_eq!(graph.vc_count(), 1);
        assert_eq!(graph.edge_count(), 0);
        assert!(graph.subsumed_by(0).is_empty());
    }

    #[test]
    fn test_build_subsumption_graph_two_equivalent_vcs() {
        let f = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let vcs = vec![make_vc(f.clone()), make_vc(f)];
        let graph = build_subsumption_graph(&vcs);
        assert_eq!(graph.vc_count(), 2);
        // VC[0] subsumes VC[1] and vice versa (equivalent)
        assert!(graph.subsumed_by(0).contains(&1));
        assert!(graph.subsumed_by(1).contains(&0));
    }

    #[test]
    fn test_build_subsumption_graph_strength_relationship() {
        // VC[0]: And(x==0, y==1, z==2) -- strongest
        // VC[1]: And(x==0, y==1)       -- middle
        // VC[2]: x==0                   -- weakest
        let x_eq_0 = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let y_eq_1 = Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(1)));
        let z_eq_2 = Formula::Eq(Box::new(var("z")), Box::new(Formula::Int(2)));

        let vcs = vec![
            make_vc(Formula::And(vec![x_eq_0.clone(), y_eq_1.clone(), z_eq_2])),
            make_vc(Formula::And(vec![x_eq_0.clone(), y_eq_1])),
            make_vc(x_eq_0),
        ];
        let graph = build_subsumption_graph(&vcs);

        // VC[0] is strongest: subsumes VC[1] and VC[2]
        let sub0 = graph.subsumed_by(0);
        assert!(sub0.contains(&1), "VC[0] should subsume VC[1]");
        assert!(sub0.contains(&2), "VC[0] should subsume VC[2]");

        // VC[1] subsumes VC[2] only
        let sub1 = graph.subsumed_by(1);
        assert!(sub1.contains(&2), "VC[1] should subsume VC[2]");
        assert!(!sub1.contains(&0), "VC[1] should NOT subsume VC[0]");

        // VC[2] subsumes nothing
        assert!(graph.subsumed_by(2).is_empty(), "VC[2] is weakest, subsumes nothing");
    }

    // -----------------------------------------------------------------------
    // discharge_subsumed tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_discharge_subsumed_empty_graph() {
        let graph = SubsumptionGraph { vc_count: 1, subsumes: FxHashMap::default() };
        let discharged = discharge_subsumed(&graph, 0);
        assert!(discharged.is_empty());
    }

    #[test]
    fn test_discharge_subsumed_direct_subsumption() {
        // VC[0] subsumes VC[1] and VC[2]
        let mut subsumes = FxHashMap::default();
        subsumes.insert(0, vec![1, 2]);
        let graph = SubsumptionGraph { vc_count: 3, subsumes };

        let discharged = discharge_subsumed(&graph, 0);
        assert_eq!(discharged, vec![1, 2]);
    }

    #[test]
    fn test_discharge_subsumed_transitive() {
        // VC[0] subsumes VC[1], VC[1] subsumes VC[2]
        // Proving VC[0] should transitively discharge VC[2]
        let mut subsumes = FxHashMap::default();
        subsumes.insert(0, vec![1]);
        subsumes.insert(1, vec![2]);
        let graph = SubsumptionGraph { vc_count: 3, subsumes };

        let discharged = discharge_subsumed(&graph, 0);
        assert_eq!(discharged, vec![1, 2]);
    }

    #[test]
    fn test_discharge_subsumed_no_duplicates() {
        // VC[0] -> VC[1], VC[0] -> VC[2], VC[1] -> VC[2]
        // VC[2] should appear only once in output
        let mut subsumes = FxHashMap::default();
        subsumes.insert(0, vec![1, 2]);
        subsumes.insert(1, vec![2]);
        let graph = SubsumptionGraph { vc_count: 3, subsumes };

        let discharged = discharge_subsumed(&graph, 0);
        assert_eq!(discharged, vec![1, 2]);
        // Check no duplicates
        let unique: FxHashSet<usize> = discharged.iter().copied().collect();
        assert_eq!(unique.len(), discharged.len(), "no duplicates in discharged list");
    }

    #[test]
    fn test_discharge_subsumed_does_not_include_proved_idx() {
        let mut subsumes = FxHashMap::default();
        subsumes.insert(0, vec![1]);
        let graph = SubsumptionGraph { vc_count: 2, subsumes };

        let discharged = discharge_subsumed(&graph, 0);
        assert!(!discharged.contains(&0), "proved_idx should not be in discharged set");
    }

    // -----------------------------------------------------------------------
    // Integration: compare_formulas + build + discharge pipeline
    // -----------------------------------------------------------------------

    #[test]
    fn test_full_pipeline_three_vcs() {
        // VC[0]: And(x > 0, y > 0, z > 0)  -- strongest
        // VC[1]: And(x > 0, y > 0)          -- medium
        // VC[2]: x > 0                       -- weakest
        let x_gt_0 = Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0)));
        let y_gt_0 = Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(0)));
        let z_gt_0 = Formula::Gt(Box::new(var("z")), Box::new(Formula::Int(0)));

        let vcs = vec![
            make_vc(Formula::And(vec![x_gt_0.clone(), y_gt_0.clone(), z_gt_0])),
            make_vc(Formula::And(vec![x_gt_0.clone(), y_gt_0])),
            make_vc(x_gt_0),
        ];

        let graph = build_subsumption_graph(&vcs);

        // Proving VC[0] (strongest) should discharge VC[1] and VC[2].
        let discharged = discharge_subsumed(&graph, 0);
        assert_eq!(discharged, vec![1, 2]);

        // Proving VC[1] should discharge VC[2] only.
        let discharged = discharge_subsumed(&graph, 1);
        assert_eq!(discharged, vec![2]);

        // Proving VC[2] (weakest) discharges nothing.
        let discharged = discharge_subsumed(&graph, 2);
        assert!(discharged.is_empty());
    }

    #[test]
    fn test_vc_strength_enum_values_distinct() {
        // Ensure all four variants are distinct
        let variants = [
            VcStrength::Stronger,
            VcStrength::Weaker,
            VcStrength::Equivalent,
            VcStrength::Incomparable,
        ];
        for i in 0..variants.len() {
            for j in (i + 1)..variants.len() {
                assert_ne!(variants[i], variants[j], "variants {i} and {j} should be distinct");
            }
        }
    }
}
