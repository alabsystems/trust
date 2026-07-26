// trust-types/lifetime_analysis.rs: Higher-level lifetime and borrow analysis
//
// Builds on the core lifetime types in lifetime.rs to provide whole-function
// lifetime analysis: computing borrow sets per program point, building
// region constraint graphs (NLL-style), checking borrow safety across
// all blocks, and generating summary reports for the verification pipeline.
//
// Part of #153
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::fx::{FxHashMap, FxHashSet};

use serde::{Deserialize, Serialize};

use crate::formula::{Formula, VcKind, VerificationCondition};
use crate::lifetime::{
    BorrowChecker, BorrowError, BorrowInfo, Lifetime, LifetimeRelation, Mutability,
    check_lifetime_constraints,
};
use crate::model::{
    BasicBlock, BlockId, Operand, Place, Rvalue, SourceSpan, Statement, Terminator, VerifiableBody,
};

// ---------------------------------------------------------------------------
// Region variables (NLL-style)
// ---------------------------------------------------------------------------

/// The kind of a lifetime region.
///
/// Distinguishes between the different lifetime categories in Rust's
/// type system. Used by the constraint solver to determine compatibility.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum RegionKind {
    /// The `'static` lifetime — lives for the entire program duration.
    Static,
    /// A named lifetime from a function signature (e.g., `'a` in `fn foo<'a>`).
    Named(String),
    /// An anonymous lifetime inferred by the compiler (e.g., elided lifetimes).
    Anonymous,
    /// An erased lifetime used after monomorphization (lifetime info discarded).
    Erased,
}

impl RegionKind {
    /// Human-readable description of this region kind.
    #[must_use]
    pub fn description(&self) -> String {
        match self {
            RegionKind::Static => "'static".to_string(),
            RegionKind::Named(name) => name.clone(),
            RegionKind::Anonymous => "'_".to_string(),
            RegionKind::Erased => "'erased".to_string(),
        }
    }

    /// Whether this region is known to outlive all other regions.
    #[must_use]
    pub fn is_static(&self) -> bool {
        matches!(self, RegionKind::Static)
    }
}

/// A region variable representing a lifetime in the NLL constraint system.
///
/// Region variables are inferred lifetimes — the solver finds the smallest
/// region (set of program points) that satisfies all constraints.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RegionVariable {
    /// Unique index for this region variable.
    pub index: usize,
    /// Optional name (for named lifetimes like `'a`; anonymous regions have None).
    pub name: Option<String>,
    /// The kind of region this variable represents.
    pub kind: RegionKind,
    /// The program points (block, statement index) where this region is live.
    pub live_points: Vec<ProgramPoint>,
}

/// A program point: a specific location in the MIR.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ProgramPoint {
    /// Block containing this point.
    pub block: BlockId,
    /// Statement index within the block (0-based; terminator = stmts.len()).
    pub statement_index: usize,
}

impl ProgramPoint {
    /// Create a new program point.
    #[must_use]
    pub fn new(block: BlockId, statement_index: usize) -> Self {
        Self { block, statement_index }
    }
}

// ---------------------------------------------------------------------------
// Lifetime constraints
// ---------------------------------------------------------------------------

/// A constraint between lifetime regions, with provenance information.
///
/// Richer than `LifetimeRelation` — includes the source location and
/// reason for the constraint, enabling better error messages.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LifetimeConstraint {
    /// The kind of constraint.
    pub kind: ConstraintKind,
    /// Where in the source this constraint arises.
    pub span: SourceSpan,
    /// Human-readable reason for this constraint.
    pub reason: String,
}

/// Kinds of lifetime constraints.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ConstraintKind {
    /// Region `a` must outlive region `b` (`'a: 'b`).
    Outlives { a: usize, b: usize },
    /// Region `a` must equal region `b`.
    Equal { a: usize, b: usize },
    /// Region `a` must be live at the given program point.
    LiveAt { region: usize, point: ProgramPoint },
}

// ---------------------------------------------------------------------------
// Borrow set
// ---------------------------------------------------------------------------

/// The set of borrows active at a specific program point.
///
/// Computed by walking the CFG and tracking borrow creation/expiration.
/// Used by trust_vcgen to generate VCs at each program point.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BorrowSet {
    /// Active borrows at this point.
    pub borrows: Vec<BorrowInfo>,
}

impl BorrowSet {
    /// Create an empty borrow set.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Number of active borrows.
    #[must_use]
    pub fn len(&self) -> usize {
        self.borrows.len()
    }

    /// Whether there are no active borrows.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.borrows.is_empty()
    }

    /// Check if any borrow in this set conflicts with a new borrow.
    #[must_use]
    pub fn conflicts_with(&self, place: &Place, mutability: Mutability) -> Option<&BorrowInfo> {
        for borrow in &self.borrows {
            if borrow.borrowed_place.local != place.local {
                continue;
            }
            match (borrow.mutability, mutability) {
                (Mutability::Mutable, _) | (_, Mutability::Mutable) => return Some(borrow),
                (Mutability::Shared, Mutability::Shared) => {}
            }
        }
        None
    }

    /// Add a borrow to the set.
    pub fn add(&mut self, info: BorrowInfo) {
        self.borrows.push(info);
    }

    /// Remove all borrows of a specific local.
    pub fn expire_local(&mut self, local: usize) {
        self.borrows.retain(|b| b.borrowed_place.local != local);
    }

    /// All locals that are currently borrowed.
    #[must_use]
    pub fn borrowed_locals(&self) -> FxHashSet<usize> {
        self.borrows.iter().map(|b| b.borrowed_place.local).collect()
    }

    /// All mutably borrowed locals.
    #[must_use]
    pub fn mutably_borrowed_locals(&self) -> FxHashSet<usize> {
        self.borrows
            .iter()
            .filter(|b| b.mutability == Mutability::Mutable)
            .map(|b| b.borrowed_place.local)
            .collect()
    }
}

// ---------------------------------------------------------------------------
// Whole-function lifetime analysis
// ---------------------------------------------------------------------------

/// Result of whole-function lifetime and borrow analysis.
///
/// Contains borrow sets per block, lifetime constraints, region variables,
/// and any borrow errors detected.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct LifetimeAnalysis {
    /// Borrow set at the entry of each block.
    pub borrow_sets: FxHashMap<usize, BorrowSet>,
    /// Region variables inferred during analysis.
    pub regions: Vec<RegionVariable>,
    /// Lifetime constraints collected from the body.
    pub constraints: Vec<LifetimeConstraint>,
    /// Borrow errors detected.
    pub errors: Vec<BorrowError>,
    /// Lifetime relations extracted (for constraint solving).
    pub relations: Vec<LifetimeRelation>,
}

impl LifetimeAnalysis {
    /// Whether the analysis found any errors.
    #[must_use]
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Number of borrow errors.
    #[must_use]
    pub fn error_count(&self) -> usize {
        self.errors.len()
    }

    /// Number of region variables.
    #[must_use]
    pub fn region_count(&self) -> usize {
        self.regions.len()
    }

    /// Number of lifetime constraints.
    #[must_use]
    pub fn constraint_count(&self) -> usize {
        self.constraints.len()
    }
}

// ---------------------------------------------------------------------------
// Analysis entry point
// ---------------------------------------------------------------------------

/// Perform whole-function borrow and lifetime analysis.
///
/// Walks all blocks in the body, tracks borrows and ownership through
/// each statement, detects violations, and collects lifetime constraints.
/// Returns a complete analysis result.
#[must_use]
pub fn check_borrow_safety(body: &VerifiableBody) -> LifetimeAnalysis {
    let mut analysis = LifetimeAnalysis::default();
    let mut checker = BorrowChecker::new();

    // Initialize all locals as owned.
    for local in &body.locals {
        checker.init_local(local.index);
    }

    // Walk blocks in order, computing borrow sets and checking safety.
    let mut current_borrow_set = BorrowSet::new();

    for block in &body.blocks {
        // Record borrow set at block entry.
        analysis.borrow_sets.insert(block.id.0, current_borrow_set.clone());

        // Process each statement in the block.
        analyze_block_borrows(block, &mut checker, &mut current_borrow_set, &mut analysis);

        // Handle terminator effects on borrows.
        analyze_terminator_borrows(&block.terminator, &mut current_borrow_set, &mut analysis);
    }

    // Check collected lifetime relations for consistency.
    if let Err(err) = check_lifetime_constraints(&analysis.relations) {
        analysis.errors.push(err);
    }

    analysis
}

/// Analyze borrows within a single basic block.
fn analyze_block_borrows(
    block: &BasicBlock,
    checker: &mut BorrowChecker,
    borrow_set: &mut BorrowSet,
    analysis: &mut LifetimeAnalysis,
) {
    for (stmt_idx, stmt) in block.stmts.iter().enumerate() {
        if let Statement::Assign { place: _, rvalue, span } = stmt {
            // Check for borrow conflicts on operands.
            check_rvalue_borrows(rvalue, checker, span, block.id, stmt_idx, analysis);

            // Track new borrows from references.
            if let Rvalue::Ref { mutable, place: borrowed } = rvalue {
                let region_idx = analysis.regions.len();
                let lifetime = Lifetime::new(format!("'_r{region_idx}"), block.id);

                let mutability = if *mutable { Mutability::Mutable } else { Mutability::Shared };

                let borrow_info = BorrowInfo {
                    borrowed_place: borrowed.clone(),
                    lifetime: lifetime.clone(),
                    mutability,
                    span: span.clone(),
                };

                // Check for conflicts before adding.
                if let Some(conflict) = borrow_set.conflicts_with(borrowed, mutability) {
                    analysis.errors.push(BorrowError::AlreadyBorrowed {
                        place: borrowed.clone(),
                        existing: conflict.mutability,
                        requested: mutability,
                        existing_span: conflict.span.clone(),
                        requested_span: span.clone(),
                    });
                }

                borrow_set.add(borrow_info.clone());
                checker.add_borrow(borrow_info);

                // Create a region variable for this borrow.
                analysis.regions.push(RegionVariable {
                    index: region_idx,
                    name: Some(lifetime.name.clone()),
                    kind: RegionKind::Anonymous,
                    live_points: vec![ProgramPoint::new(block.id, stmt_idx)],
                });

                // Add a liveness constraint.
                analysis.constraints.push(LifetimeConstraint {
                    kind: ConstraintKind::LiveAt {
                        region: region_idx,
                        point: ProgramPoint::new(block.id, stmt_idx),
                    },
                    span: span.clone(),
                    reason: format!(
                        "borrow of `_{local}` must be live at {block_id}:{stmt_idx}",
                        local = borrowed.local,
                        block_id = block.id.0
                    ),
                });
            }

            // Track ownership changes.
            checker.track_ownership(stmt);
        }
    }
}

/// Check rvalue operands for use-after-move and borrow conflicts.
fn check_rvalue_borrows(
    rvalue: &Rvalue,
    checker: &BorrowChecker,
    span: &SourceSpan,
    block: BlockId,
    _stmt_idx: usize,
    analysis: &mut LifetimeAnalysis,
) {
    // Check move/copy operands for use-after-move.
    for place in extract_operand_places(rvalue) {
        if let crate::lifetime::OwnershipState::Moved { span: move_span, .. } =
            checker.ownership_state(place.local)
        {
            analysis.errors.push(BorrowError::MovedValue {
                place: place.clone(),
                move_span: move_span.clone(),
                use_span: span.clone(),
            });
        }
    }

    // For reference creation, the checker.check_borrow handles conflicts.
    if let Rvalue::Ref { mutable, place: borrowed } = rvalue {
        let mutability = if *mutable { Mutability::Mutable } else { Mutability::Shared };
        if let Err(err) = checker.check_borrow(borrowed, mutability, span) {
            // Only add if it's a MovedValue error (AlreadyBorrowed is handled via BorrowSet).
            if matches!(err, BorrowError::MovedValue { .. }) {
                analysis.errors.push(err);
            }
        }
    }

    let _ = block; // used in constraint generation (future extension)
}

/// Extract places used as operands in an rvalue.
fn extract_operand_places(rvalue: &Rvalue) -> Vec<&Place> {
    match rvalue {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) => {
            extract_operand_place(op).into_iter().collect()
        }
        Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
            let mut places = Vec::new();
            places.extend(extract_operand_place(a));
            places.extend(extract_operand_place(b));
            places
        }
        Rvalue::Ref { place, .. } | Rvalue::AddressOf(_, place) => vec![place],
        Rvalue::Aggregate(_, ops) => ops.iter().filter_map(extract_operand_place).collect(),
        Rvalue::Repeat(op, _) => extract_operand_place(op).into_iter().collect(),
        Rvalue::Discriminant(p) | Rvalue::Len(p) | Rvalue::CopyForDeref(p) => vec![p],
        // Trust: W2 inc-0 — pointer arithmetic reads BOTH the base pointer and
        // the offset count, exactly like a `BinaryOp`.
        Rvalue::PtrOffset { ptr, count } => {
            let mut places = Vec::new();
            places.extend(extract_operand_place(ptr));
            places.extend(extract_operand_place(count));
            places
        }
        Rvalue::Unsupported { operands, .. } => {
            operands.iter().filter_map(extract_operand_place).collect()
        }
    }
}

/// Extract the place from a single operand.
fn extract_operand_place(op: &Operand) -> Option<&Place> {
    match op {
        Operand::Copy(p) | Operand::Move(p) => Some(p),
        Operand::Constant(_) | Operand::Symbolic(_) | Operand::Unsupported { .. } => None,
    }
}

/// Handle terminator effects on borrow sets.
fn analyze_terminator_borrows(
    terminator: &Terminator,
    borrow_set: &mut BorrowSet,
    analysis: &mut LifetimeAnalysis,
) {
    match terminator {
        Terminator::Drop { place, .. } => {
            // Drop expires all borrows of the dropped place.
            borrow_set.expire_local(place.local);
        }
        Terminator::Return => {
            // At return, check for dangling borrows of locals.
            for borrow in &borrow_set.borrows {
                if borrow.lifetime.name != "'static" {
                    // A local borrow surviving to return is suspicious.
                    // Add an outlives relation: the borrow's lifetime must
                    // outlive the function return.
                    analysis.relations.push(LifetimeRelation::Outlives {
                        a: borrow.lifetime.clone(),
                        b: Lifetime::static_lifetime(),
                    });
                }
            }
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Borrow set computation
// ---------------------------------------------------------------------------

/// Compute borrow sets at the entry of each block in the body.
///
/// A simpler interface than full `check_borrow_safety` — only computes
/// the borrow sets without checking for errors.
#[must_use]
pub fn compute_borrow_sets(body: &VerifiableBody) -> FxHashMap<usize, BorrowSet> {
    let mut sets: FxHashMap<usize, BorrowSet> = FxHashMap::default();
    let mut current = BorrowSet::new();

    for block in &body.blocks {
        sets.insert(block.id.0, current.clone());

        for stmt in &block.stmts {
            if let Statement::Assign {
                rvalue: Rvalue::Ref { mutable, place: borrowed },
                span,
                ..
            } = stmt
            {
                let mutability = if *mutable { Mutability::Mutable } else { Mutability::Shared };
                current.add(BorrowInfo {
                    borrowed_place: borrowed.clone(),
                    lifetime: Lifetime::new("'_auto", block.id),
                    mutability,
                    span: span.clone(),
                });
            }
        }

        if let Terminator::Drop { place, .. } = &block.terminator {
            current.expire_local(place.local);
        }
    }

    sets
}

// ---------------------------------------------------------------------------
// VC generation for lifetime analysis
// ---------------------------------------------------------------------------

/// Generate verification conditions from a lifetime analysis result.
///
/// Produces VCs for each borrow error and for non-trivial lifetime
/// constraints that require solver verification.
#[must_use]
pub fn generate_lifetime_vcs(
    analysis: &LifetimeAnalysis,
    function_name: &str,
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    // VC for each borrow error.
    for error in &analysis.errors {
        let span = match error {
            BorrowError::AlreadyBorrowed { requested_span, .. } => requested_span.clone(),
            BorrowError::MovedValue { use_span, .. } => use_span.clone(),
            BorrowError::DanglingReference { span, .. } => span.clone(),
            BorrowError::LifetimeExpired { use_span, .. } => use_span.clone(),
        };

        vcs.push(VerificationCondition {
            kind: VcKind::Assertion { message: format!("borrow safety: {error}") },
            function: function_name.into(),
            location: span,
            formula: Formula::Bool(false), // error = unsatisfiable
            contract_metadata: None,
        });
    }

    // VC for each outlives constraint.
    for constraint in &analysis.constraints {
        if let ConstraintKind::Outlives { a, b } = &constraint.kind {
            vcs.push(VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "lifetime: region r{a} must outlive region r{b} ({})",
                        constraint.reason
                    ),
                },
                function: function_name.into(),
                location: constraint.span.clone(),
                formula: Formula::Bool(true), // constraint, not violation
                contract_metadata: None,
            });
        }
    }

    vcs
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::*;

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    fn span_at(file: &str, line: u32) -> SourceSpan {
        SourceSpan {
            file: file.to_string(),
            line_start: line,
            col_start: 1,
            line_end: line,
            col_end: 40,
        }
    }

    // --- ProgramPoint tests ---

    #[test]
    fn test_program_point_new() {
        let pp = ProgramPoint::new(BlockId(2), 3);
        assert_eq!(pp.block, BlockId(2));
        assert_eq!(pp.statement_index, 3);
    }

    // --- BorrowSet tests ---

    #[test]
    fn test_borrow_set_empty() {
        let set = BorrowSet::new();
        assert!(set.is_empty());
        assert_eq!(set.len(), 0);
        assert!(set.borrowed_locals().is_empty());
    }

    #[test]
    fn test_borrow_set_add_and_query() {
        let mut set = BorrowSet::new();
        set.add(BorrowInfo {
            borrowed_place: Place::local(0),
            lifetime: Lifetime::new("'a", BlockId(0)),
            mutability: Mutability::Shared,
            span: span(),
        });

        assert_eq!(set.len(), 1);
        assert!(set.borrowed_locals().contains(&0));
        assert!(set.mutably_borrowed_locals().is_empty());
    }

    #[test]
    fn test_borrow_set_mutable_tracking() {
        let mut set = BorrowSet::new();
        set.add(BorrowInfo {
            borrowed_place: Place::local(0),
            lifetime: Lifetime::new("'a", BlockId(0)),
            mutability: Mutability::Mutable,
            span: span(),
        });

        assert!(set.mutably_borrowed_locals().contains(&0));
    }

    #[test]
    fn test_borrow_set_conflicts_shared_ok() {
        let mut set = BorrowSet::new();
        set.add(BorrowInfo {
            borrowed_place: Place::local(0),
            lifetime: Lifetime::new("'a", BlockId(0)),
            mutability: Mutability::Shared,
            span: span(),
        });

        // Shared + Shared = no conflict.
        assert!(set.conflicts_with(&Place::local(0), Mutability::Shared).is_none());
    }

    #[test]
    fn test_borrow_set_conflicts_mutable() {
        let mut set = BorrowSet::new();
        set.add(BorrowInfo {
            borrowed_place: Place::local(0),
            lifetime: Lifetime::new("'a", BlockId(0)),
            mutability: Mutability::Shared,
            span: span(),
        });

        // Shared + Mutable = conflict.
        assert!(set.conflicts_with(&Place::local(0), Mutability::Mutable).is_some());
    }

    #[test]
    fn test_borrow_set_conflicts_existing_mutable() {
        let mut set = BorrowSet::new();
        set.add(BorrowInfo {
            borrowed_place: Place::local(0),
            lifetime: Lifetime::new("'a", BlockId(0)),
            mutability: Mutability::Mutable,
            span: span(),
        });

        // Mutable + Shared = conflict.
        assert!(set.conflicts_with(&Place::local(0), Mutability::Shared).is_some());
        // Mutable + Mutable = conflict.
        assert!(set.conflicts_with(&Place::local(0), Mutability::Mutable).is_some());
    }

    #[test]
    fn test_borrow_set_no_conflict_different_local() {
        let mut set = BorrowSet::new();
        set.add(BorrowInfo {
            borrowed_place: Place::local(0),
            lifetime: Lifetime::new("'a", BlockId(0)),
            mutability: Mutability::Mutable,
            span: span(),
        });

        // Different local = no conflict.
        assert!(set.conflicts_with(&Place::local(1), Mutability::Mutable).is_none());
    }

    #[test]
    fn test_borrow_set_expire() {
        let mut set = BorrowSet::new();
        set.add(BorrowInfo {
            borrowed_place: Place::local(0),
            lifetime: Lifetime::new("'a", BlockId(0)),
            mutability: Mutability::Mutable,
            span: span(),
        });
        set.add(BorrowInfo {
            borrowed_place: Place::local(1),
            lifetime: Lifetime::new("'b", BlockId(0)),
            mutability: Mutability::Shared,
            span: span(),
        });

        set.expire_local(0);
        assert_eq!(set.len(), 1);
        assert!(!set.borrowed_locals().contains(&0));
        assert!(set.borrowed_locals().contains(&1));
    }

    // --- LifetimeConstraint tests ---

    #[test]
    fn test_lifetime_constraint_outlives() {
        let constraint = LifetimeConstraint {
            kind: ConstraintKind::Outlives { a: 0, b: 1 },
            span: span(),
            reason: "assignment".to_string(),
        };
        assert!(matches!(constraint.kind, ConstraintKind::Outlives { a: 0, b: 1 }));
    }

    #[test]
    fn test_lifetime_constraint_live_at() {
        let point = ProgramPoint::new(BlockId(2), 3);
        let constraint = LifetimeConstraint {
            kind: ConstraintKind::LiveAt { region: 0, point },
            span: span(),
            reason: "borrow use".to_string(),
        };
        assert!(matches!(constraint.kind, ConstraintKind::LiveAt { region: 0, .. }));
    }

    // --- RegionVariable tests ---

    #[test]
    fn test_region_variable_construction() {
        let region = RegionVariable {
            index: 0,
            name: Some("'a".to_string()),
            kind: RegionKind::Named("'a".to_string()),
            live_points: vec![ProgramPoint::new(BlockId(0), 0)],
        };
        assert_eq!(region.index, 0);
        assert_eq!(region.name, Some("'a".to_string()));
        assert!(matches!(region.kind, RegionKind::Named(_)));
        assert_eq!(region.live_points.len(), 1);
    }

    // --- RegionKind tests ---

    #[test]
    fn test_region_kind_static() {
        let kind = RegionKind::Static;
        assert!(kind.is_static());
        assert_eq!(kind.description(), "'static");
    }

    #[test]
    fn test_region_kind_named() {
        let kind = RegionKind::Named("'a".to_string());
        assert!(!kind.is_static());
        assert_eq!(kind.description(), "'a");
    }

    #[test]
    fn test_region_kind_anonymous() {
        let kind = RegionKind::Anonymous;
        assert!(!kind.is_static());
        assert_eq!(kind.description(), "'_");
    }

    #[test]
    fn test_region_kind_erased() {
        let kind = RegionKind::Erased;
        assert!(!kind.is_static());
        assert_eq!(kind.description(), "'erased");
    }

    #[test]
    fn test_region_kind_serialization_roundtrip() {
        let kinds = vec![
            RegionKind::Static,
            RegionKind::Named("'a".to_string()),
            RegionKind::Anonymous,
            RegionKind::Erased,
        ];
        for kind in kinds {
            let json = serde_json::to_string(&kind).expect("serialize");
            let roundtrip: RegionKind = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(roundtrip, kind);
        }
    }

    // --- check_borrow_safety tests ---

    #[test]
    fn test_check_borrow_safety_clean_body() {
        let body = VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                    span: span(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::i32(),
        };

        let analysis = check_borrow_safety(&body);
        assert!(!analysis.has_errors());
        assert_eq!(analysis.error_count(), 0);
        assert!(analysis.borrow_sets.contains_key(&0));
    }

    #[test]
    fn test_check_borrow_safety_detects_use_after_move() {
        let body = VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("y".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Move(Place::local(1))),
                        span: span_at("src/lib.rs", 5),
                    },
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: span_at("src/lib.rs", 6),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::i32(),
        };

        let analysis = check_borrow_safety(&body);
        assert!(analysis.has_errors());
        assert!(analysis.errors.iter().any(|e| matches!(e, BorrowError::MovedValue { .. })));
    }

    #[test]
    fn test_check_borrow_safety_detects_aliasing() {
        let body = VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: true, inner: Box::new(Ty::i32()) },
                    name: Some("r1".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::i32()) },
                    name: Some("r2".into()),
                },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Ref { mutable: true, place: Place::local(0) },
                        span: span_at("src/lib.rs", 10),
                    },
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Ref { mutable: false, place: Place::local(0) },
                        span: span_at("src/lib.rs", 11),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
        };

        let analysis = check_borrow_safety(&body);
        assert!(analysis.has_errors());
        assert!(analysis.errors.iter().any(|e| matches!(e, BorrowError::AlreadyBorrowed { .. })));
    }

    #[test]
    fn test_check_borrow_safety_creates_regions() {
        let body = VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::i32()) },
                    name: Some("r".into()),
                },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Ref { mutable: false, place: Place::local(0) },
                    span: span(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
        };

        let analysis = check_borrow_safety(&body);
        assert_eq!(analysis.region_count(), 1);
        assert!(analysis.regions[0].name.as_deref().unwrap().starts_with("'_r"));
    }

    #[test]
    fn test_check_borrow_safety_return_dangling() {
        // A non-static borrow surviving to return should produce a lifetime relation.
        let body = VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::i32()) },
                    name: Some("r".into()),
                },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Ref { mutable: false, place: Place::local(0) },
                    span: span(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
        };

        let analysis = check_borrow_safety(&body);
        // The analysis should detect that a local borrow at return creates
        // an outlives-static relation which will fail.
        assert!(!analysis.relations.is_empty());
        assert!(analysis.has_errors(), "dangling borrow at return should error");
    }

    // --- compute_borrow_sets tests ---

    #[test]
    fn test_compute_borrow_sets_empty() {
        let body = VerifiableBody {
            locals: vec![],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        };

        let sets = compute_borrow_sets(&body);
        assert_eq!(sets.len(), 1);
        assert!(sets[&0].is_empty());
    }

    #[test]
    fn test_compute_borrow_sets_tracks_borrows() {
        let body = VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::i32()) },
                    name: None,
                },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Ref { mutable: false, place: Place::local(0) },
                        span: span(),
                    }],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        };

        let sets = compute_borrow_sets(&body);
        // Block 0 entry: no borrows yet.
        assert!(sets[&0].is_empty());
        // Block 1 entry: borrow from block 0 should be active.
        assert_eq!(sets[&1].len(), 1);
        assert!(sets[&1].borrowed_locals().contains(&0));
    }

    #[test]
    fn test_compute_borrow_sets_drop_expires() {
        let body = VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::i32()) },
                    name: None,
                },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Ref { mutable: false, place: Place::local(0) },
                        span: span(),
                    }],
                    terminator: Terminator::Drop {
                        unwind: UnwindEdge::Unreachable,
                        place: Place::local(0),
                        target: BlockId(1),
                        span: span(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        };

        let sets = compute_borrow_sets(&body);
        // After drop of local 0, borrows of local 0 should be expired.
        assert!(sets[&1].is_empty());
    }

    // --- generate_lifetime_vcs tests ---

    #[test]
    fn test_generate_lifetime_vcs_clean() {
        let analysis = LifetimeAnalysis::default();
        let vcs = generate_lifetime_vcs(&analysis, "test_fn");
        assert!(vcs.is_empty());
    }

    #[test]
    fn test_generate_lifetime_vcs_with_errors() {
        let analysis = LifetimeAnalysis {
            errors: vec![BorrowError::MovedValue {
                place: Place::local(0),
                move_span: span(),
                use_span: span_at("src/lib.rs", 10),
            }],
            ..Default::default()
        };

        let vcs = generate_lifetime_vcs(&analysis, "test_fn");
        assert_eq!(vcs.len(), 1);
        assert_eq!(vcs[0].function, "test_fn");
        assert!(vcs[0].kind.description().contains("assertion"));
    }

    #[test]
    fn test_generate_lifetime_vcs_with_outlives() {
        let analysis = LifetimeAnalysis {
            constraints: vec![LifetimeConstraint {
                kind: ConstraintKind::Outlives { a: 0, b: 1 },
                span: span(),
                reason: "assignment".to_string(),
            }],
            ..Default::default()
        };

        let vcs = generate_lifetime_vcs(&analysis, "test_fn");
        assert_eq!(vcs.len(), 1);
        // Outlives constraints are satisfiable (not violations).
        assert_eq!(vcs[0].formula, Formula::Bool(true));
    }

    // --- LifetimeAnalysis tests ---

    #[test]
    fn test_lifetime_analysis_accessors() {
        let analysis = LifetimeAnalysis {
            regions: vec![RegionVariable {
                index: 0,
                name: Some("'a".to_string()),
                kind: RegionKind::Named("'a".to_string()),
                live_points: vec![],
            }],
            constraints: vec![
                LifetimeConstraint {
                    kind: ConstraintKind::Outlives { a: 0, b: 1 },
                    span: span(),
                    reason: "test".to_string(),
                },
                LifetimeConstraint {
                    kind: ConstraintKind::Equal { a: 0, b: 1 },
                    span: span(),
                    reason: "test".to_string(),
                },
            ],
            errors: vec![BorrowError::LifetimeExpired {
                place: Place::local(0),
                lifetime: Lifetime::new("'a", BlockId(0)),
                use_span: span(),
            }],
            ..Default::default()
        };

        assert!(analysis.has_errors());
        assert_eq!(analysis.error_count(), 1);
        assert_eq!(analysis.region_count(), 1);
        assert_eq!(analysis.constraint_count(), 2);
    }

    // --- Serialization tests ---

    #[test]
    fn test_borrow_set_serialization_roundtrip() {
        let mut set = BorrowSet::new();
        set.add(BorrowInfo {
            borrowed_place: Place::local(0),
            lifetime: Lifetime::new("'a", BlockId(0)),
            mutability: Mutability::Shared,
            span: span(),
        });

        let json = serde_json::to_string(&set).expect("serialize");
        let roundtrip: BorrowSet = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip.len(), 1);
    }

    #[test]
    fn test_lifetime_constraint_serialization_roundtrip() {
        let constraint = LifetimeConstraint {
            kind: ConstraintKind::Outlives { a: 0, b: 1 },
            span: span(),
            reason: "assignment".to_string(),
        };

        let json = serde_json::to_string(&constraint).expect("serialize");
        let roundtrip: LifetimeConstraint = serde_json::from_str(&json).expect("deserialize");
        assert!(matches!(roundtrip.kind, ConstraintKind::Outlives { a: 0, b: 1 }));
        assert_eq!(roundtrip.reason, "assignment");
    }

    #[test]
    fn test_region_variable_serialization_roundtrip() {
        let region = RegionVariable {
            index: 42,
            name: Some("'a".to_string()),
            kind: RegionKind::Named("'a".to_string()),
            live_points: vec![ProgramPoint::new(BlockId(0), 0), ProgramPoint::new(BlockId(1), 2)],
        };

        let json = serde_json::to_string(&region).expect("serialize");
        let roundtrip: RegionVariable = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip.index, 42);
        assert_eq!(roundtrip.live_points.len(), 2);
    }
}
