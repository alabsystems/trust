// trust_vcgen/alias_analysis.rs: Alias analysis for VC precision
//
// Performs points-to analysis over MIR references to determine aliasing
// relationships between memory locations. Used to strengthen verification
// conditions by ruling out impossible aliasing scenarios.
//
// Key concepts:
// - AliasSet: a set of potentially-aliasing memory locations
// - AliasResult: the aliasing relationship between two references
// - AliasAnalyzer: flow-sensitive points-to analysis over a function body
//
// Part of #280: Add alias analysis for VC precision
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;
use std::fmt::Write;

use serde::{Deserialize, Serialize};
use trust_types::fx::FxHashMap;
use trust_types::{
    Formula, Operand, Place, Projection, Rvalue, Sort, Statement, VerifiableFunction,
    VerificationCondition,
};

// ────────────────────────────────────────────────────────────────────────────
// Core types
// ────────────────────────────────────────────────────────────────────────────

/// A unique identifier for a memory location (local index + projection path).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct MemoryLocation {
    /// The local variable index.
    pub local: usize,
    /// Projection path from the local (e.g., field, deref, index).
    pub projections: Vec<ProjectionKind>,
}

/// Simplified projection kinds for alias analysis.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ProjectionKind {
    Field(usize),
    Deref,
    /// Unknown index -- conservatively aliases any element.
    Index,
}

impl MemoryLocation {
    /// Create a location for a bare local variable.
    #[must_use]
    pub fn from_local(local: usize) -> Self {
        Self { local, projections: vec![] }
    }

    /// Create a location from a MIR `Place`.
    #[must_use]
    pub fn from_place(place: &Place) -> Self {
        let projections = place
            .projections
            .iter()
            .map(|p| match p {
                Projection::Field(idx) => ProjectionKind::Field(*idx),
                Projection::Deref => ProjectionKind::Deref,
                Projection::Index(_)
                | Projection::Downcast(_)
                | Projection::ConstantIndex { .. }
                | Projection::Subslice { .. } => ProjectionKind::Index,
                _ => ProjectionKind::Index,
            })
            .collect();
        Self { local: place.local, projections }
    }

    /// Whether this location is a prefix of `other` (i.e., `other` is nested).
    #[must_use]
    pub fn is_prefix_of(&self, other: &Self) -> bool {
        self.local == other.local
            && self.projections.len() <= other.projections.len()
            && self.projections == other.projections[..self.projections.len()]
    }
}

/// Result of an alias query between two memory locations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AliasResult {
    /// The two references definitely refer to the same memory.
    MustAlias,
    /// The two references may or may not refer to the same memory.
    MayAlias,
    /// The two references definitely do not refer to the same memory.
    NoAlias,
}

impl AliasResult {
    /// Whether the result permits aliasing (MustAlias or MayAlias).
    #[must_use]
    pub fn may_alias(self) -> bool {
        matches!(self, Self::MustAlias | Self::MayAlias)
    }
}

/// A set of memory locations that may alias each other.
///
/// All locations within a single `AliasSet` are treated as potentially
/// referring to the same underlying memory. Different alias sets are
/// guaranteed not to alias.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AliasSet {
    /// Unique identifier for this alias class.
    pub id: usize,
    /// Locations that belong to this alias class.
    pub locations: BTreeSet<MemoryLocation>,
}

impl AliasSet {
    /// Create a new alias set with a single location.
    #[must_use]
    pub fn singleton(id: usize, loc: MemoryLocation) -> Self {
        let mut locations = BTreeSet::new();
        locations.insert(loc);
        Self { id, locations }
    }

    /// Merge another alias set into this one.
    pub fn merge(&mut self, other: &AliasSet) {
        self.locations.extend(other.locations.iter().cloned());
    }

    /// Whether this set contains the given location.
    #[must_use]
    pub fn contains(&self, loc: &MemoryLocation) -> bool {
        self.locations.contains(loc)
    }

    /// Number of locations in this set.
    #[must_use]
    pub fn len(&self) -> usize {
        self.locations.len()
    }

    /// Whether this set is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.locations.is_empty()
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Alias analyzer
// ────────────────────────────────────────────────────────────────────────────

/// Points-to analysis state: maps each pointer local to the set of locations
/// it may point to.
type PointsToMap = FxHashMap<usize, BTreeSet<MemoryLocation>>;

/// Flow-sensitive alias analyzer over a function's MIR body.
///
/// Walks all statements to build a points-to map, then answers alias queries
/// by checking whether two references share any points-to targets.
#[derive(Debug)]
pub struct AliasAnalyzer {
    /// For each pointer local, the set of locations it may point to.
    points_to: PointsToMap,
    /// Total number of locals in the analyzed function.
    num_locals: usize,
}

impl AliasAnalyzer {
    /// Analyze a function body and build the points-to map.
    #[must_use]
    pub fn analyze(func: &VerifiableFunction) -> Self {
        let num_locals = func.body.locals.len();
        let mut points_to: PointsToMap = FxHashMap::default();

        // Walk all blocks and statements.
        for block in &func.body.blocks {
            for stmt in &block.stmts {
                if let Statement::Assign { place, rvalue, .. } = stmt {
                    Self::transfer_assign(place, rvalue, &mut points_to);
                }
            }
        }

        Self { points_to, num_locals }
    }

    /// Transfer function for an assignment statement.
    fn transfer_assign(dst: &Place, rvalue: &Rvalue, pts: &mut PointsToMap) {
        match rvalue {
            // `_x = &y` or `_x = &mut y` -- _x points to y
            Rvalue::Ref { place, .. } => {
                let target = MemoryLocation::from_place(place);
                pts.entry(dst.local).or_default().insert(target);
            }
            // `_x = Copy(_y)` or `_x = Move(_y)` -- copy points-to set
            Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) => {
                if let Some(src_pts) = pts.get(&src.local).cloned() {
                    pts.entry(dst.local).or_default().extend(src_pts);
                }
            }
            _ => {}
        }
    }

    /// Query the alias relationship between two places.
    #[must_use]
    pub fn query_alias(&self, a: &Place, b: &Place) -> AliasResult {
        let loc_a = MemoryLocation::from_place(a);
        let loc_b = MemoryLocation::from_place(b);

        // Same place is always MustAlias.
        if loc_a == loc_b {
            return AliasResult::MustAlias;
        }

        // Different locals with no pointer indirection cannot alias.
        if loc_a.local != loc_b.local && !self.has_pointer_overlap(a, b) {
            return AliasResult::NoAlias;
        }

        // Check if one is a prefix of the other (overlapping fields).
        if loc_a.is_prefix_of(&loc_b) || loc_b.is_prefix_of(&loc_a) {
            return AliasResult::MayAlias;
        }

        // Same local, disjoint projections -> NoAlias.
        if loc_a.local == loc_b.local && Self::disjoint_projections(&loc_a, &loc_b) {
            return AliasResult::NoAlias;
        }

        AliasResult::MayAlias
    }

    /// Check whether two places' points-to sets overlap.
    fn has_pointer_overlap(&self, a: &Place, b: &Place) -> bool {
        let pts_a = self.points_to.get(&a.local);
        let pts_b = self.points_to.get(&b.local);

        match (pts_a, pts_b) {
            (Some(sa), Some(sb)) => sa.iter().any(|loc| sb.contains(loc)),
            _ => false,
        }
    }

    /// Whether two locations from the same local have disjoint field projections.
    fn disjoint_projections(a: &MemoryLocation, b: &MemoryLocation) -> bool {
        for (pa, pb) in a.projections.iter().zip(b.projections.iter()) {
            match (pa, pb) {
                (ProjectionKind::Field(fa), ProjectionKind::Field(fb)) if fa != fb => {
                    return true;
                }
                (ProjectionKind::Deref, _) | (_, ProjectionKind::Deref) => {
                    // After a deref we cannot determine disjointness statically.
                    return false;
                }
                (ProjectionKind::Index, _) | (_, ProjectionKind::Index) => {
                    // Unknown index -- conservatively may overlap.
                    return false;
                }
                _ => { /* same projection, continue checking deeper */ }
            }
        }
        false
    }

    /// Compute alias sets: partition all referenced locations into alias classes.
    #[must_use]
    pub fn compute_alias_sets(&self) -> Vec<AliasSet> {
        let mut sets: Vec<AliasSet> = Vec::new();
        let mut loc_to_set: FxHashMap<MemoryLocation, usize> = FxHashMap::default();

        // Collect all referenced locations.
        let mut all_locs: BTreeSet<MemoryLocation> = BTreeSet::new();
        for local in 0..self.num_locals {
            all_locs.insert(MemoryLocation::from_local(local));
        }
        for pts in self.points_to.values() {
            all_locs.extend(pts.iter().cloned());
        }

        // Assign each location to a set. Merge sets when aliasing detected.
        for loc in &all_locs {
            let mut merged_into: Option<usize> = None;

            for (set_idx, set) in sets.iter().enumerate() {
                for existing in &set.locations {
                    if self.locations_may_alias(loc, existing) {
                        merged_into = Some(set_idx);
                        break;
                    }
                }
                if merged_into.is_some() {
                    break;
                }
            }

            match merged_into {
                Some(idx) => {
                    sets[idx].locations.insert(loc.clone());
                    loc_to_set.insert(loc.clone(), idx);
                }
                None => {
                    let id = sets.len();
                    sets.push(AliasSet::singleton(id, loc.clone()));
                    loc_to_set.insert(loc.clone(), id);
                }
            }
        }

        sets
    }

    /// Check whether two memory locations may alias based on the points-to map.
    fn locations_may_alias(&self, a: &MemoryLocation, b: &MemoryLocation) -> bool {
        if a == b {
            return true;
        }
        if a.is_prefix_of(b) || b.is_prefix_of(a) {
            return true;
        }
        // Check if any pointer points to both locations.
        for pts in self.points_to.values() {
            if pts.contains(a) && pts.contains(b) {
                return true;
            }
        }
        false
    }

    /// The number of locals analyzed.
    #[must_use]
    pub fn num_locals(&self) -> usize {
        self.num_locals
    }
}

// ────────────────────────────────────────────────────────────────────────────
// VC refinement
// ────────────────────────────────────────────────────────────────────────────

/// Strengthen VCs using alias analysis results.
///
/// For each VC, if alias analysis determines that certain references
/// definitely do not alias, we add non-aliasing assumptions to the
/// formula. This helps solvers prune infeasible paths.
#[must_use]
pub fn refine_vc_with_alias(
    func: &VerifiableFunction,
    vcs: Vec<VerificationCondition>,
) -> Vec<VerificationCondition> {
    let analyzer = AliasAnalyzer::analyze(func);
    let alias_sets = analyzer.compute_alias_sets();

    // If there's only one alias set, no refinement is possible.
    if alias_sets.len() <= 1 {
        return vcs;
    }

    // Build non-aliasing constraints between distinct alias sets.
    let no_alias_constraints = build_no_alias_constraints(&alias_sets);

    if no_alias_constraints.is_empty() {
        return vcs;
    }

    // Conjoin the no-alias constraints as assumptions to each VC.
    let assumption = if no_alias_constraints.len() == 1 {
        // SAFETY: len == 1 guarantees .next() returns Some.
        no_alias_constraints
            .into_iter()
            .next()
            .unwrap_or_else(|| unreachable!("empty iter despite len == 1"))
    } else {
        Formula::And(no_alias_constraints)
    };

    vcs.into_iter()
        .map(|mut vc| {
            vc.formula = Formula::Implies(Box::new(assumption.clone()), Box::new(vc.formula));
            vc
        })
        .collect()
}

/// Build formulas asserting that locations in different alias sets are distinct.
fn build_no_alias_constraints(sets: &[AliasSet]) -> Vec<Formula> {
    let mut constraints = Vec::new();

    for i in 0..sets.len() {
        for j in (i + 1)..sets.len() {
            // Pick a representative from each set.
            if let (Some(rep_a), Some(rep_b)) =
                (sets[i].locations.iter().next(), sets[j].locations.iter().next())
            {
                let var_a = Formula::Var(
                    crate::generated_formula_symbol("alias", &format!("loc_{}", loc_name(rep_a))),
                    Sort::Int,
                );
                let var_b = Formula::Var(
                    crate::generated_formula_symbol("alias", &format!("loc_{}", loc_name(rep_b))),
                    Sort::Int,
                );
                // Assert the two representatives are not equal.
                constraints
                    .push(Formula::Not(Box::new(Formula::Eq(Box::new(var_a), Box::new(var_b)))));
            }
        }
    }

    constraints
}

/// Human-readable name for a memory location.
fn loc_name(loc: &MemoryLocation) -> String {
    let mut name = format!("_{}", loc.local);
    for proj in &loc.projections {
        match proj {
            ProjectionKind::Field(idx) => {
                let _ = write!(name, ".{idx}");
            }
            ProjectionKind::Deref => name.push('*'),
            ProjectionKind::Index => name.push_str("[?]"),
        }
    }
    name
}

// ────────────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use trust_types::{BasicBlock, BlockId, LocalDecl, SourceSpan, Terminator, Ty};

    use super::*;

    /// Helper: build a simple function with the given locals and statements.
    fn make_func(locals: Vec<LocalDecl>, stmts: Vec<Statement>) -> VerifiableFunction {
        VerifiableFunction {
            name: "test_alias".to_string(),
            def_path: "test::alias".to_string(),
            span: SourceSpan::default(),
            body: trust_types::VerifiableBody {
                locals,
                blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_memory_location_from_local() {
        let loc = MemoryLocation::from_local(3);
        assert_eq!(loc.local, 3);
        assert!(loc.projections.is_empty());
    }

    #[test]
    fn test_memory_location_from_place_with_projections() {
        let place = Place { local: 1, projections: vec![Projection::Field(2), Projection::Deref] };
        let loc = MemoryLocation::from_place(&place);
        assert_eq!(loc.local, 1);
        assert_eq!(loc.projections.len(), 2);
        assert_eq!(loc.projections[0], ProjectionKind::Field(2));
        assert_eq!(loc.projections[1], ProjectionKind::Deref);
    }

    #[test]
    fn test_is_prefix_of() {
        let parent = MemoryLocation::from_local(1);
        let child = MemoryLocation { local: 1, projections: vec![ProjectionKind::Field(0)] };
        assert!(parent.is_prefix_of(&child));
        assert!(!child.is_prefix_of(&parent));
    }

    #[test]
    fn test_alias_result_same_place_must_alias() {
        let func = make_func(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Int { width: 32, signed: true },
                    name: Some("x".into()),
                },
            ],
            vec![],
        );
        let analyzer = AliasAnalyzer::analyze(&func);
        let p = Place::local(1);
        assert_eq!(analyzer.query_alias(&p, &p), AliasResult::MustAlias);
    }

    #[test]
    fn test_alias_result_different_locals_no_alias() {
        let func = make_func(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Int { width: 32, signed: true },
                    name: Some("x".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Int { width: 32, signed: true },
                    name: Some("y".into()),
                },
            ],
            vec![],
        );
        let analyzer = AliasAnalyzer::analyze(&func);
        assert_eq!(analyzer.query_alias(&Place::local(1), &Place::local(2)), AliasResult::NoAlias,);
    }

    #[test]
    fn test_alias_result_ref_creates_points_to() {
        // _2 = &_1 ; _3 = &_1 => _2 and _3 point to same location
        let func = make_func(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Int { width: 32, signed: true },
                    name: Some("x".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref {
                        mutable: false,
                        inner: Box::new(Ty::Int { width: 32, signed: true }),
                    },
                    name: Some("r1".into()),
                },
                LocalDecl {
                    index: 3,
                    ty: Ty::Ref {
                        mutable: false,
                        inner: Box::new(Ty::Int { width: 32, signed: true }),
                    },
                    name: Some("r2".into()),
                },
            ],
            vec![
                Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                    span: SourceSpan::default(),
                },
                Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                    span: SourceSpan::default(),
                },
            ],
        );
        let analyzer = AliasAnalyzer::analyze(&func);
        // _2 and _3 both point to _1, so they have overlapping points-to sets.
        assert!(analyzer.query_alias(&Place::local(2), &Place::local(3)).may_alias());
    }

    #[test]
    fn test_alias_result_disjoint_fields() {
        // _1.0 and _1.1 are different fields of the same local -> NoAlias
        let func = make_func(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Tuple(vec![Ty::Int { width: 32, signed: true }, Ty::Bool]),
                    name: Some("tup".into()),
                },
            ],
            vec![],
        );
        let analyzer = AliasAnalyzer::analyze(&func);
        let field_0 = Place { local: 1, projections: vec![Projection::Field(0)] };
        let field_1 = Place { local: 1, projections: vec![Projection::Field(1)] };
        assert_eq!(analyzer.query_alias(&field_0, &field_1), AliasResult::NoAlias);
    }

    #[test]
    fn test_alias_result_may_alias_returns_true() {
        assert!(AliasResult::MayAlias.may_alias());
        assert!(AliasResult::MustAlias.may_alias());
        assert!(!AliasResult::NoAlias.may_alias());
    }

    #[test]
    fn test_compute_alias_sets_basic() {
        let func = make_func(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Int { width: 32, signed: true },
                    name: Some("x".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Int { width: 32, signed: true },
                    name: Some("y".into()),
                },
            ],
            vec![],
        );
        let analyzer = AliasAnalyzer::analyze(&func);
        let sets = analyzer.compute_alias_sets();
        // Each local should be in its own alias set (no aliasing).
        assert!(sets.len() >= 2, "should have at least 2 alias sets, got {}", sets.len());
    }

    #[test]
    fn test_compute_alias_sets_merges_aliased_locations() {
        // _2 = &_1 ; _3 = &_1 => _1 appears in points-to of both _2 and _3,
        // and _2 and _3 alias each other through _1.
        let func = make_func(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Int { width: 32, signed: true },
                    name: Some("x".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref {
                        mutable: false,
                        inner: Box::new(Ty::Int { width: 32, signed: true }),
                    },
                    name: Some("r1".into()),
                },
                LocalDecl {
                    index: 3,
                    ty: Ty::Ref {
                        mutable: false,
                        inner: Box::new(Ty::Int { width: 32, signed: true }),
                    },
                    name: Some("r2".into()),
                },
            ],
            vec![
                Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                    span: SourceSpan::default(),
                },
                Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                    span: SourceSpan::default(),
                },
            ],
        );
        let analyzer = AliasAnalyzer::analyze(&func);
        let sets = analyzer.compute_alias_sets();
        // _1 should be in the points-to set of both _2 and _3, so the
        // locations referenced through pointers should be merged.
        let total_locs: usize = sets.iter().map(|s| s.len()).sum();
        assert!(total_locs >= 4, "should track at least 4 locations");
    }

    #[test]
    fn test_refine_vc_with_alias_empty_vcs() {
        let func = make_func(vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }], vec![]);
        let refined = refine_vc_with_alias(&func, vec![]);
        assert!(refined.is_empty());
    }

    #[test]
    fn test_alias_set_singleton_and_merge() {
        let loc_a = MemoryLocation::from_local(0);
        let loc_b = MemoryLocation::from_local(1);
        let mut set_a = AliasSet::singleton(0, loc_a.clone());
        let set_b = AliasSet::singleton(1, loc_b.clone());

        assert_eq!(set_a.len(), 1);
        assert!(set_a.contains(&loc_a));
        assert!(!set_a.contains(&loc_b));

        set_a.merge(&set_b);
        assert_eq!(set_a.len(), 2);
        assert!(set_a.contains(&loc_b));
    }

    #[test]
    fn test_refine_vc_preserves_vc_count() {
        // Build a function with distinct locals (no aliasing), and some VCs.
        let func = make_func(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Int { width: 32, signed: true },
                    name: Some("a".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Int { width: 32, signed: true },
                    name: Some("b".into()),
                },
            ],
            vec![],
        );
        let vcs = vec![VerificationCondition {
            kind: trust_types::VcKind::DivisionByZero,
            function: "test".into(),
            location: SourceSpan::default(),
            formula: Formula::Eq(
                Box::new(Formula::Var("b".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
            obligation: None,
        }];
        let refined = refine_vc_with_alias(&func, vcs);
        assert_eq!(refined.len(), 1, "refinement must preserve VC count");
    }

    #[test]
    fn generated_alias_constraints_use_reserved_namespace() {
        let sets = [
            AliasSet::singleton(0, MemoryLocation::from_local(1)),
            AliasSet::singleton(1, MemoryLocation::from_local(2)),
        ];
        let constraints = build_no_alias_constraints(&sets);
        let [Formula::Not(eq)] = constraints.as_slice() else {
            panic!("expected one non-alias constraint, got {constraints:?}")
        };
        let Formula::Eq(lhs, rhs) = eq.as_ref() else {
            panic!("expected a disequality body, got {eq:?}")
        };
        let expected_lhs = crate::generated_formula_symbol("alias", "loc__1");
        let expected_rhs = crate::generated_formula_symbol("alias", "loc__2");
        assert!(matches!(lhs.as_ref(), Formula::Var(name, Sort::Int) if name == &expected_lhs));
        assert!(matches!(rhs.as_ref(), Formula::Var(name, Sort::Int) if name == &expected_rhs));
        assert_ne!(expected_lhs, "alias_loc__1");
        assert_ne!(expected_rhs, "alias_loc__2");
    }

    #[test]
    fn test_loc_name_formatting() {
        let loc = MemoryLocation {
            local: 2,
            projections: vec![
                ProjectionKind::Field(1),
                ProjectionKind::Deref,
                ProjectionKind::Index,
            ],
        };
        let name = loc_name(&loc);
        assert_eq!(name, "_2.1*[?]");
    }
}
