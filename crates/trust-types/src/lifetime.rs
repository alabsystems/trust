// trust-types/lifetime.rs: Lifetime model for ownership verification
//
// Models Rust's ownership and borrowing system for verification:
// lifetimes, borrow tracking, ownership transfers, and VC generation
// for borrow checker properties. Used by trust_vcgen to generate
// verification conditions that prove borrow safety statically.
//
// Part of #153
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
#![allow(clippy::result_large_err)]

use crate::fx::FxHashMap;

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::formula::{Formula, VcKind, VerificationCondition};
use crate::model::{
    BasicBlock, BlockId, Operand, Place, Rvalue, SourceSpan, Statement, Terminator, VerifiableBody,
};

// ---------------------------------------------------------------------------
// Lifetime types
// ---------------------------------------------------------------------------

/// A lifetime label in the verification model.
///
/// Lifetimes are identified by name and bound to a lexical scope (block ID).
/// The scope represents the block where the lifetime starts; it ends when
/// control leaves that block.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Lifetime {
    /// Lifetime name (e.g., "'a", "'static", "'_anon_0").
    pub name: String,
    /// The block where this lifetime begins.
    pub scope: BlockId,
}

impl Lifetime {
    /// The `'static` lifetime (scope block 0 by convention).
    #[must_use]
    pub fn static_lifetime() -> Self {
        Self { name: "'static".to_string(), scope: BlockId(0) }
    }

    /// Create a named lifetime bound to a scope.
    #[must_use]
    pub fn new(name: impl Into<String>, scope: BlockId) -> Self {
        Self { name: name.into(), scope }
    }
}

// ---------------------------------------------------------------------------
// Borrow tracking
// ---------------------------------------------------------------------------

/// Mutability of a borrow.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Mutability {
    Shared,
    Mutable,
}

/// Information about an active borrow.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BorrowInfo {
    /// The place being borrowed (e.g., local variable or field).
    pub borrowed_place: Place,
    /// Lifetime of the borrow.
    pub lifetime: Lifetime,
    /// Whether this is a shared or mutable borrow.
    pub mutability: Mutability,
    /// Source location where the borrow was created.
    pub span: SourceSpan,
}

/// Errors from borrow checking.
#[derive(Debug, Clone, PartialEq, Eq, Error, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BorrowError {
    /// A place is already mutably borrowed.
    #[error(
        "cannot borrow `{place:?}` as {requested:?} because it is already borrowed as {existing:?}"
    )]
    AlreadyBorrowed {
        place: Place,
        existing: Mutability,
        requested: Mutability,
        existing_span: SourceSpan,
        requested_span: SourceSpan,
    },
    /// A value was used after being moved.
    #[error("use of moved value `{place:?}`, moved at {move_span:?}")]
    MovedValue { place: Place, move_span: SourceSpan, use_span: SourceSpan },
    /// A reference outlives the data it points to.
    #[error("dangling reference to `{place:?}`: data does not live long enough")]
    DanglingReference {
        place: Place,
        borrow_lifetime: Lifetime,
        data_lifetime: Lifetime,
        span: SourceSpan,
    },
    /// A borrow was used after its lifetime expired.
    #[error("borrow of `{place:?}` has expired (lifetime {lifetime:?})")]
    LifetimeExpired { place: Place, lifetime: Lifetime, use_span: SourceSpan },
}

// ---------------------------------------------------------------------------
// Lifetime relations
// ---------------------------------------------------------------------------

/// A constraint between two lifetimes.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum LifetimeRelation {
    /// Lifetime `a` outlives lifetime `b` (`'a: 'b`).
    Outlives { a: Lifetime, b: Lifetime },
    /// Lifetimes `a` and `b` are equal.
    Equal { a: Lifetime, b: Lifetime },
}

impl LifetimeRelation {
    /// Human-readable description.
    #[must_use]
    pub fn description(&self) -> String {
        match self {
            LifetimeRelation::Outlives { a, b } => {
                format!("{}: {}", a.name, b.name)
            }
            LifetimeRelation::Equal { a, b } => {
                format!("{} == {}", a.name, b.name)
            }
        }
    }
}

/// Check a set of lifetime constraints for consistency.
///
/// Returns `Ok(())` if all constraints are satisfiable, or a `BorrowError`
/// if a constraint is violated (e.g., a short-lived reference assigned to
/// a longer-lived slot).
pub fn check_lifetime_constraints(relations: &[LifetimeRelation]) -> Result<(), BorrowError> {
    // Build an outlives graph and check for violations.
    // A violation occurs when 'a: 'b is required but 'a has a strictly
    // smaller scope than 'b.
    for rel in relations {
        if let LifetimeRelation::Outlives { a, b } = rel {
            // Static outlives everything.
            if a.name == "'static" {
                continue;
            }
            // If b is static but a is not, that is a violation.
            if b.name == "'static" && a.name != "'static" {
                return Err(BorrowError::DanglingReference {
                    place: Place::local(0),
                    borrow_lifetime: b.clone(),
                    data_lifetime: a.clone(),
                    span: SourceSpan::default(),
                });
            }
            // Scope-based check: a must start no later than b.
            if a.scope.0 > b.scope.0 {
                return Err(BorrowError::DanglingReference {
                    place: Place::local(0),
                    borrow_lifetime: b.clone(),
                    data_lifetime: a.clone(),
                    span: SourceSpan::default(),
                });
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Ownership tracking
// ---------------------------------------------------------------------------

/// An ownership transfer event (move or copy).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum OwnershipTransfer {
    /// Value was moved from `from` to `to`.
    Move { from: Place, to: Place, span: SourceSpan },
    /// Value was copied from `from` to `to`.
    Copy { from: Place, to: Place, span: SourceSpan },
}

/// The ownership state of a local variable.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum OwnershipState {
    /// The variable owns its value.
    Owned,
    /// The variable has been moved out.
    Moved { destination: Place, span: SourceSpan },
    /// The variable is borrowed (one or more borrows active).
    Borrowed { borrows: Vec<BorrowInfo> },
    /// The variable is uninitialized.
    Uninitialized,
}

// ---------------------------------------------------------------------------
// BorrowChecker
// ---------------------------------------------------------------------------

/// Tracks active borrows and ownership state for borrow checking.
///
/// This is a simplified model of Rust's borrow checker (NLL / Polonius),
/// sufficient for generating verification conditions. The full borrow
/// checker lives in rustc; this model generates VCs that prove the same
/// properties hold.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct BorrowChecker {
    /// Active borrows keyed by the borrowed place's local index.
    active_borrows: FxHashMap<usize, Vec<BorrowInfo>>,
    /// Ownership state per local variable.
    ownership: FxHashMap<usize, OwnershipState>,
    /// Ownership transfer log.
    transfers: Vec<OwnershipTransfer>,
}

impl BorrowChecker {
    /// Create a new borrow checker with all locals uninitialized.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Initialize a local variable as owned.
    pub fn init_local(&mut self, local: usize) {
        self.ownership.insert(local, OwnershipState::Owned);
    }

    /// Get the ownership state of a local.
    #[must_use]
    pub fn ownership_state(&self, local: usize) -> &OwnershipState {
        self.ownership.get(&local).unwrap_or(&OwnershipState::Uninitialized)
    }

    /// Get all active borrows for a local.
    #[must_use]
    pub fn active_borrows(&self, local: usize) -> &[BorrowInfo] {
        self.active_borrows.get(&local).map_or(&[], |v| v.as_slice())
    }

    /// Get the transfer log.
    #[must_use]
    pub fn transfers(&self) -> &[OwnershipTransfer] {
        &self.transfers
    }

    /// Check whether a new borrow of `place` with `mutability` is allowed
    /// given the current active borrows.
    pub fn check_borrow(
        &self,
        place: &Place,
        mutability: Mutability,
        span: &SourceSpan,
    ) -> Result<(), BorrowError> {
        // First check: is the value still owned (not moved)?
        match self.ownership_state(place.local) {
            OwnershipState::Moved { span: move_span, .. } => {
                return Err(BorrowError::MovedValue {
                    place: place.clone(),
                    move_span: move_span.clone(),
                    use_span: span.clone(),
                });
            }
            OwnershipState::Uninitialized => {
                return Err(BorrowError::MovedValue {
                    place: place.clone(),
                    move_span: SourceSpan::default(),
                    use_span: span.clone(),
                });
            }
            _ => {}
        }

        let active = self.active_borrows(place.local);

        match mutability {
            Mutability::Mutable => {
                // Mutable borrow: no other borrows allowed.
                if let Some(existing) = active.first() {
                    return Err(BorrowError::AlreadyBorrowed {
                        place: place.clone(),
                        existing: existing.mutability,
                        requested: Mutability::Mutable,
                        existing_span: existing.span.clone(),
                        requested_span: span.clone(),
                    });
                }
            }
            Mutability::Shared => {
                // Shared borrow: no mutable borrows allowed.
                if let Some(existing) = active.iter().find(|b| b.mutability == Mutability::Mutable)
                {
                    return Err(BorrowError::AlreadyBorrowed {
                        place: place.clone(),
                        existing: Mutability::Mutable,
                        requested: Mutability::Shared,
                        existing_span: existing.span.clone(),
                        requested_span: span.clone(),
                    });
                }
            }
        }

        Ok(())
    }

    /// Record a new borrow.
    pub fn add_borrow(&mut self, info: BorrowInfo) {
        let local = info.borrowed_place.local;
        self.active_borrows.entry(local).or_default().push(info);
    }

    /// Expire all borrows for a given local.
    pub fn expire_borrows(&mut self, local: usize) {
        self.active_borrows.remove(&local);
    }

    /// Track ownership changes from a statement.
    ///
    /// Updates the ownership map based on moves, copies, and borrows
    /// observed in the statement. Returns any ownership transfers.
    pub fn track_ownership(&mut self, stmt: &Statement) -> Vec<OwnershipTransfer> {
        let mut new_transfers = Vec::new();

        if let Statement::Assign { place, rvalue, span } = stmt {
            match rvalue {
                Rvalue::Use(Operand::Move(src)) => {
                    // Move: source becomes moved, dest becomes owned.
                    let transfer = OwnershipTransfer::Move {
                        from: src.clone(),
                        to: place.clone(),
                        span: span.clone(),
                    };
                    self.ownership.insert(
                        src.local,
                        OwnershipState::Moved { destination: place.clone(), span: span.clone() },
                    );
                    self.ownership.insert(place.local, OwnershipState::Owned);
                    self.transfers.push(transfer.clone());
                    new_transfers.push(transfer);
                }
                Rvalue::Use(Operand::Copy(src)) => {
                    // Copy: source stays owned, dest becomes owned.
                    let transfer = OwnershipTransfer::Copy {
                        from: src.clone(),
                        to: place.clone(),
                        span: span.clone(),
                    };
                    self.ownership.insert(place.local, OwnershipState::Owned);
                    self.transfers.push(transfer.clone());
                    new_transfers.push(transfer);
                }
                Rvalue::Ref { mutable, place: borrowed_place } => {
                    // Borrow: dest gets a reference, source stays owned.
                    self.ownership.insert(place.local, OwnershipState::Owned);
                    let borrow = BorrowInfo {
                        borrowed_place: borrowed_place.clone(),
                        lifetime: Lifetime::new("'_auto", BlockId(0)),
                        mutability: if *mutable { Mutability::Mutable } else { Mutability::Shared },
                        span: span.clone(),
                    };
                    self.add_borrow(borrow);
                }
                _ => {
                    // Other rvalues: dest becomes owned.
                    self.ownership.insert(place.local, OwnershipState::Owned);
                }
            }
        }

        new_transfers
    }
}

// ---------------------------------------------------------------------------
// VC generation for borrow safety
// ---------------------------------------------------------------------------

/// Generate verification conditions for borrow checker properties.
///
/// Walks the function body and generates VCs for:
/// - No use-after-move
/// - No aliasing violations (shared XOR mutable)
/// - No dangling references
///
/// Returns a list of VCs that, if proved, guarantee borrow safety.
#[must_use]
pub fn generate_borrow_vcs(body: &VerifiableBody) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();
    let mut checker = BorrowChecker::new();

    // Initialize all locals as owned.
    for local in &body.locals {
        checker.init_local(local.index);
    }

    for block in &body.blocks {
        generate_block_borrow_vcs(block, &mut checker, &mut vcs);
    }

    vcs
}

/// Generate borrow VCs for a single basic block.
fn generate_block_borrow_vcs(
    block: &BasicBlock,
    checker: &mut BorrowChecker,
    vcs: &mut Vec<VerificationCondition>,
) {
    for stmt in &block.stmts {
        if let Statement::Assign { place: _, rvalue, span } = stmt {
            // Check for use-after-move on operands.
            for operand_place in operand_places(rvalue) {
                if let OwnershipState::Moved { span: move_span, .. } =
                    checker.ownership_state(operand_place.local)
                {
                    // Generate a VC: this use-after-move should be impossible.
                    vcs.push(VerificationCondition {
                        kind: VcKind::Assertion {
                            message: format!(
                                "use of moved value `_{}` (moved at {}:{})",
                                operand_place.local, move_span.file, move_span.line_start
                            ),
                        },
                        function: crate::Symbol::intern(""),
                        location: span.clone(),
                        formula: Formula::Bool(false), // always violated
                        contract_metadata: None,
                    });
                }
            }

            // Check borrow conflicts for references.
            if let Rvalue::Ref { mutable, place: borrowed } = rvalue {
                let mutability = if *mutable { Mutability::Mutable } else { Mutability::Shared };
                if let Err(err) = checker.check_borrow(borrowed, mutability, span) {
                    vcs.push(VerificationCondition {
                        kind: VcKind::Assertion { message: format!("borrow violation: {err}") },
                        function: crate::Symbol::intern(""),
                        location: span.clone(),
                        formula: Formula::Bool(false),
                        contract_metadata: None,
                    });
                }
            }

            // Track ownership changes.
            checker.track_ownership(stmt);
        }
    }

    // Handle drop terminators: expire borrows.
    if let Terminator::Drop { place, .. } = &block.terminator {
        checker.expire_borrows(place.local);
    }
}

/// Extract places used as operands in an rvalue.
fn operand_places(rvalue: &Rvalue) -> Vec<&Place> {
    match rvalue {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) => {
            operand_place(op).into_iter().collect()
        }
        Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
            let mut places = Vec::new();
            places.extend(operand_place(a));
            places.extend(operand_place(b));
            places
        }
        Rvalue::Ref { place, .. } | Rvalue::AddressOf(_, place) => vec![place],
        Rvalue::Aggregate(_, ops) => ops.iter().filter_map(operand_place).collect(),
        Rvalue::Repeat(op, _) => operand_place(op).into_iter().collect(),
        Rvalue::Discriminant(p) | Rvalue::Len(p) | Rvalue::CopyForDeref(p) => vec![p],
        // Trust: W2 inc-0 — pointer arithmetic reads BOTH the base pointer and
        // the offset count, exactly like a `BinaryOp`.
        Rvalue::PtrOffset { ptr, count } => {
            let mut places = Vec::new();
            places.extend(operand_place(ptr));
            places.extend(operand_place(count));
            places
        }
        Rvalue::Unsupported { operands, .. } => operands.iter().filter_map(operand_place).collect(),
    }
}

/// Extract the place from a single operand, if any.
fn operand_place(op: &Operand) -> Option<&Place> {
    match op {
        Operand::Copy(p) | Operand::Move(p) => Some(p),
        Operand::Constant(_) | Operand::Symbolic(_) | Operand::Unsupported { .. } => None,
    }
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

    // --- Lifetime tests ---

    #[test]
    fn test_lifetime_static() {
        let lt = Lifetime::static_lifetime();
        assert_eq!(lt.name, "'static");
        assert_eq!(lt.scope, BlockId(0));
    }

    #[test]
    fn test_lifetime_new() {
        let lt = Lifetime::new("'a", BlockId(3));
        assert_eq!(lt.name, "'a");
        assert_eq!(lt.scope, BlockId(3));
    }

    // --- Borrow checking tests ---

    #[test]
    fn test_check_borrow_shared_ok() {
        let mut checker = BorrowChecker::new();
        checker.init_local(0);

        // First shared borrow should succeed.
        let result = checker.check_borrow(&Place::local(0), Mutability::Shared, &span());
        assert!(result.is_ok());

        // Add a shared borrow, then check another shared borrow.
        checker.add_borrow(BorrowInfo {
            borrowed_place: Place::local(0),
            lifetime: Lifetime::new("'a", BlockId(0)),
            mutability: Mutability::Shared,
            span: span(),
        });
        let result = checker.check_borrow(&Place::local(0), Mutability::Shared, &span());
        assert!(result.is_ok(), "multiple shared borrows should be allowed");
    }

    #[test]
    fn test_check_borrow_mutable_conflict() {
        let mut checker = BorrowChecker::new();
        checker.init_local(0);

        checker.add_borrow(BorrowInfo {
            borrowed_place: Place::local(0),
            lifetime: Lifetime::new("'a", BlockId(0)),
            mutability: Mutability::Shared,
            span: span_at("src/lib.rs", 10),
        });

        // Mutable borrow while shared borrow active should fail.
        let result =
            checker.check_borrow(&Place::local(0), Mutability::Mutable, &span_at("src/lib.rs", 15));
        assert!(result.is_err());
        match result.unwrap_err() {
            BorrowError::AlreadyBorrowed { existing, requested, .. } => {
                assert_eq!(existing, Mutability::Shared);
                assert_eq!(requested, Mutability::Mutable);
            }
            other => panic!("expected AlreadyBorrowed, got {other:?}"),
        }
    }

    #[test]
    fn test_check_borrow_shared_after_mutable_conflict() {
        let mut checker = BorrowChecker::new();
        checker.init_local(0);

        checker.add_borrow(BorrowInfo {
            borrowed_place: Place::local(0),
            lifetime: Lifetime::new("'a", BlockId(0)),
            mutability: Mutability::Mutable,
            span: span(),
        });

        // Shared borrow while mutable borrow active should fail.
        let result = checker.check_borrow(&Place::local(0), Mutability::Shared, &span());
        assert!(result.is_err());
        match result.unwrap_err() {
            BorrowError::AlreadyBorrowed { existing, requested, .. } => {
                assert_eq!(existing, Mutability::Mutable);
                assert_eq!(requested, Mutability::Shared);
            }
            other => panic!("expected AlreadyBorrowed, got {other:?}"),
        }
    }

    #[test]
    fn test_check_borrow_after_move_fails() {
        let mut checker = BorrowChecker::new();
        checker.init_local(0);
        checker.ownership.insert(
            0,
            OwnershipState::Moved { destination: Place::local(1), span: span_at("src/lib.rs", 5) },
        );

        let result = checker.check_borrow(&Place::local(0), Mutability::Shared, &span());
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), BorrowError::MovedValue { .. }));
    }

    #[test]
    fn test_check_borrow_uninitialized_fails() {
        let checker = BorrowChecker::new();
        let result = checker.check_borrow(&Place::local(99), Mutability::Shared, &span());
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), BorrowError::MovedValue { .. }));
    }

    #[test]
    fn test_expire_borrows() {
        let mut checker = BorrowChecker::new();
        checker.init_local(0);
        checker.add_borrow(BorrowInfo {
            borrowed_place: Place::local(0),
            lifetime: Lifetime::new("'a", BlockId(0)),
            mutability: Mutability::Mutable,
            span: span(),
        });

        // Should fail before expiration.
        assert!(checker.check_borrow(&Place::local(0), Mutability::Shared, &span()).is_err());

        // Expire and retry.
        checker.expire_borrows(0);
        assert!(checker.check_borrow(&Place::local(0), Mutability::Shared, &span()).is_ok());
    }

    // --- Ownership tracking tests ---

    #[test]
    fn test_track_ownership_move() {
        let mut checker = BorrowChecker::new();
        checker.init_local(0);
        checker.init_local(1);

        let stmt = Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Move(Place::local(0))),
            span: span_at("src/lib.rs", 10),
        };

        let transfers = checker.track_ownership(&stmt);
        assert_eq!(transfers.len(), 1);
        assert!(matches!(&transfers[0], OwnershipTransfer::Move { .. }));

        // Source should be moved.
        assert!(matches!(checker.ownership_state(0), OwnershipState::Moved { .. }));
        // Dest should be owned.
        assert_eq!(checker.ownership_state(1), &OwnershipState::Owned);
    }

    #[test]
    fn test_track_ownership_copy() {
        let mut checker = BorrowChecker::new();
        checker.init_local(0);
        checker.init_local(1);

        let stmt = Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(0))),
            span: span(),
        };

        let transfers = checker.track_ownership(&stmt);
        assert_eq!(transfers.len(), 1);
        assert!(matches!(&transfers[0], OwnershipTransfer::Copy { .. }));

        // Both should be owned after copy.
        assert_eq!(checker.ownership_state(0), &OwnershipState::Owned);
        assert_eq!(checker.ownership_state(1), &OwnershipState::Owned);
    }

    #[test]
    fn test_track_ownership_ref_creates_borrow() {
        let mut checker = BorrowChecker::new();
        checker.init_local(0);
        checker.init_local(1);

        let stmt = Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Ref { mutable: true, place: Place::local(0) },
            span: span(),
        };

        checker.track_ownership(&stmt);

        // Should have an active borrow on local 0.
        let borrows = checker.active_borrows(0);
        assert_eq!(borrows.len(), 1);
        assert_eq!(borrows[0].mutability, Mutability::Mutable);
    }

    // --- Lifetime constraint tests ---

    #[test]
    fn test_lifetime_outlives_ok() {
        let relations = vec![LifetimeRelation::Outlives {
            a: Lifetime::static_lifetime(),
            b: Lifetime::new("'a", BlockId(1)),
        }];
        assert!(check_lifetime_constraints(&relations).is_ok());
    }

    #[test]
    fn test_lifetime_outlives_scope_violation() {
        // 'a (scope 5) cannot outlive 'b (scope 2) because it starts later.
        let relations = vec![LifetimeRelation::Outlives {
            a: Lifetime::new("'a", BlockId(5)),
            b: Lifetime::new("'b", BlockId(2)),
        }];
        assert!(check_lifetime_constraints(&relations).is_err());
    }

    #[test]
    fn test_lifetime_non_static_outlives_static_fails() {
        let relations = vec![LifetimeRelation::Outlives {
            a: Lifetime::new("'a", BlockId(1)),
            b: Lifetime::static_lifetime(),
        }];
        assert!(check_lifetime_constraints(&relations).is_err());
    }

    #[test]
    fn test_lifetime_equal_ok() {
        let relations = vec![LifetimeRelation::Equal {
            a: Lifetime::new("'a", BlockId(1)),
            b: Lifetime::new("'b", BlockId(1)),
        }];
        // Equal relations don't trigger errors in our simplified model.
        assert!(check_lifetime_constraints(&relations).is_ok());
    }

    #[test]
    fn test_lifetime_relation_description() {
        let outlives = LifetimeRelation::Outlives {
            a: Lifetime::new("'a", BlockId(0)),
            b: Lifetime::new("'b", BlockId(1)),
        };
        assert_eq!(outlives.description(), "'a: 'b");

        let equal = LifetimeRelation::Equal {
            a: Lifetime::new("'a", BlockId(0)),
            b: Lifetime::new("'b", BlockId(0)),
        };
        assert_eq!(equal.description(), "'a == 'b");
    }

    // --- VC generation tests ---

    #[test]
    fn test_generate_borrow_vcs_clean_body() {
        // A simple body with no borrow issues should generate no VCs.
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

        let vcs = generate_borrow_vcs(&body);
        assert!(vcs.is_empty(), "clean body should produce no borrow VCs");
    }

    #[test]
    fn test_generate_borrow_vcs_use_after_move() {
        // Move local 1 to local 0, then try to copy local 1.
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

        let vcs = generate_borrow_vcs(&body);
        assert_eq!(vcs.len(), 1, "should detect use-after-move");
        assert!(vcs[0].kind.description().contains("assertion"));
    }

    #[test]
    fn test_generate_borrow_vcs_aliasing_violation() {
        // Create a mutable borrow, then try a shared borrow of the same place.
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

        let vcs = generate_borrow_vcs(&body);
        assert_eq!(vcs.len(), 1, "should detect aliasing violation");
        assert!(vcs[0].kind.description().contains("borrow violation"));
    }

    // --- Serialization tests ---

    #[test]
    fn test_borrow_info_serialization_roundtrip() {
        let info = BorrowInfo {
            borrowed_place: Place::local(3),
            lifetime: Lifetime::new("'a", BlockId(1)),
            mutability: Mutability::Mutable,
            span: span_at("src/lib.rs", 42),
        };

        let json = serde_json::to_string(&info).expect("serialize");
        let roundtrip: BorrowInfo = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip.borrowed_place, Place::local(3));
        assert_eq!(roundtrip.mutability, Mutability::Mutable);
        assert_eq!(roundtrip.lifetime.name, "'a");
    }

    #[test]
    fn test_borrow_error_display() {
        let err = BorrowError::AlreadyBorrowed {
            place: Place::local(0),
            existing: Mutability::Mutable,
            requested: Mutability::Shared,
            existing_span: span(),
            requested_span: span(),
        };
        let msg = format!("{err}");
        assert!(msg.contains("already borrowed"));

        let moved =
            BorrowError::MovedValue { place: Place::local(1), move_span: span(), use_span: span() };
        assert!(format!("{moved}").contains("moved value"));

        let dangling = BorrowError::DanglingReference {
            place: Place::local(2),
            borrow_lifetime: Lifetime::static_lifetime(),
            data_lifetime: Lifetime::new("'a", BlockId(1)),
            span: span(),
        };
        assert!(format!("{dangling}").contains("dangling reference"));

        let expired = BorrowError::LifetimeExpired {
            place: Place::local(3),
            lifetime: Lifetime::new("'a", BlockId(1)),
            use_span: span(),
        };
        assert!(format!("{expired}").contains("expired"));
    }

    #[test]
    fn test_checker_transfer_log() {
        let mut checker = BorrowChecker::new();
        checker.init_local(0);
        checker.init_local(1);
        checker.init_local(2);

        checker.track_ownership(&Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Move(Place::local(0))),
            span: span(),
        });
        checker.track_ownership(&Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
            span: span(),
        });

        let log = checker.transfers();
        assert_eq!(log.len(), 2);
        assert!(matches!(&log[0], OwnershipTransfer::Move { .. }));
        assert!(matches!(&log[1], OwnershipTransfer::Copy { .. }));
    }
}
