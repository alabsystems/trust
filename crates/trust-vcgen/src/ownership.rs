// trust_vcgen/ownership.rs: Ownership and borrow checking for MIR bodies
//
// Lightweight intraprocedural borrow checker that tracks active borrows per
// place (by local index) and detects:
// - Aliasing violations (mutable + any other borrow on the same local)
// - Use-after-move (read/write a moved local)
// - Dangling references (borrow outlives the referent)
//
// Complements safe_rust_model.rs (region-based) with a direct transfer-function
// approach that walks blocks sequentially.
//
// Part of #238
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use trust_types::{
    Operand, Place, Rvalue, Statement, Terminator, VerifiableBody, VerifiableFunction,
};

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// The kind of borrow held on a place.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum BorrowKind {
    /// `&T` -- multiple shared borrows are allowed.
    Shared,
    /// `&mut T` -- exclusive; no other borrows allowed.
    Mutable,
    /// Value has been moved out. Further access is invalid.
    Moved,
}

/// A single active borrow record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BorrowRecord {
    /// The local holding the reference (destination of `Ref`).
    pub borrower: usize,
    /// The kind of borrow.
    pub kind: BorrowKind,
}

/// Tracks active borrows per place (keyed by source local index).
///
/// Invariants maintained:
/// - A local with `Mutable` borrow must have no other borrows.
/// - A moved local has exactly one entry with `kind == Moved`.
#[derive(Debug, Clone, Default)]
pub struct BorrowState {
    /// Map from *source* local to the set of active borrows on it.
    borrows: FxHashMap<usize, Vec<BorrowRecord>>,
    /// Set of locals that have been moved.
    moved: FxHashMap<usize, bool>,
    /// Set of locals that have been dropped.
    dropped: FxHashMap<usize, bool>,
}

/// A borrow-safety violation detected during analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum BorrowViolation {
    /// A mutable borrow co-exists with another borrow on the same local.
    AliasingViolation { local: usize, existing: BorrowKind, attempted: BorrowKind },
    /// A local was accessed (read/write/borrow) after being moved.
    UseAfterMove { local: usize },
    /// A borrow exists on a local that has been dropped or moved.
    DanglingReference { local: usize, borrower: usize },
}

// ---------------------------------------------------------------------------
// Transfer functions
// ---------------------------------------------------------------------------

impl BorrowState {
    /// Create a new empty borrow state.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Record a new reference creation. Returns a violation if the borrow is
    /// incompatible with existing borrows on the same source local.
    pub fn create_ref(
        &mut self,
        src: usize,
        dst: usize,
        kind: BorrowKind,
    ) -> Result<(), BorrowViolation> {
        // Cannot borrow a moved local.
        if self.moved.get(&src).copied().unwrap_or(false) {
            return Err(BorrowViolation::UseAfterMove { local: src });
        }
        // Cannot borrow a dropped local.
        if self.dropped.get(&src).copied().unwrap_or(false) {
            return Err(BorrowViolation::DanglingReference { local: src, borrower: dst });
        }

        let existing = self.borrows.entry(src).or_default();

        // Check aliasing rules.
        if kind == BorrowKind::Mutable {
            // Mutable borrow requires no other borrows.
            if let Some(prev) = existing.first() {
                return Err(BorrowViolation::AliasingViolation {
                    local: src,
                    existing: prev.kind,
                    attempted: kind,
                });
            }
        } else {
            // Shared borrow is incompatible with an existing mutable borrow.
            if existing.iter().any(|b| b.kind == BorrowKind::Mutable) {
                return Err(BorrowViolation::AliasingViolation {
                    local: src,
                    existing: BorrowKind::Mutable,
                    attempted: kind,
                });
            }
        }

        existing.push(BorrowRecord { borrower: dst, kind });
        Ok(())
    }

    /// Record a dereference of a local (read through a reference).
    /// Returns a violation if the local was moved or dropped.
    pub fn deref(&self, local: usize) -> Result<(), BorrowViolation> {
        if self.moved.get(&local).copied().unwrap_or(false) {
            return Err(BorrowViolation::UseAfterMove { local });
        }
        if self.dropped.get(&local).copied().unwrap_or(false) {
            return Err(BorrowViolation::DanglingReference { local, borrower: local });
        }
        Ok(())
    }

    /// Record a move from a local. Returns a violation on double-move.
    pub fn move_place(&mut self, local: usize) -> Result<(), BorrowViolation> {
        if self.moved.get(&local).copied().unwrap_or(false) {
            return Err(BorrowViolation::UseAfterMove { local });
        }
        self.moved.insert(local, true);
        // Remove any borrows sourced from this local (they become dangling).
        self.borrows.remove(&local);
        Ok(())
    }

    /// Record a drop of a local. Returns a violation if there are live borrows
    /// on the local (they would become dangling).
    pub fn drop_place(&mut self, local: usize) -> Result<(), BorrowViolation> {
        if let Some(records) = self.borrows.get(&local)
            && let Some(first) = records.first()
        {
            return Err(BorrowViolation::DanglingReference { local, borrower: first.borrower });
        }
        self.dropped.insert(local, true);
        self.borrows.remove(&local);
        Ok(())
    }

    /// Whether a local has been moved.
    #[must_use]
    pub fn is_moved(&self, local: usize) -> bool {
        self.moved.get(&local).copied().unwrap_or(false)
    }

    /// Whether a local has been dropped.
    #[must_use]
    pub fn is_dropped(&self, local: usize) -> bool {
        self.dropped.get(&local).copied().unwrap_or(false)
    }

    /// Active borrows on a given source local.
    #[must_use]
    pub fn borrows_on(&self, local: usize) -> &[BorrowRecord] {
        self.borrows.get(&local).map_or(&[], Vec::as_slice)
    }
}

// ---------------------------------------------------------------------------
// Body scanner
// ---------------------------------------------------------------------------

/// Scan an entire function body for borrow violations.
///
/// Walks blocks in order, processing each statement and terminator through the
/// transfer functions. Returns all violations found.
#[must_use]
pub fn scan_body(func: &VerifiableFunction) -> Vec<BorrowViolation> {
    scan_body_inner(&func.body)
}

/// Inner implementation operating on `VerifiableBody`.
fn scan_body_inner(body: &VerifiableBody) -> Vec<BorrowViolation> {
    let mut state = BorrowState::new();
    let mut violations = Vec::new();

    for block in &body.blocks {
        for stmt in &block.stmts {
            scan_statement(&mut state, stmt, &mut violations);
        }
        scan_terminator(&mut state, &block.terminator, &mut violations);
    }

    violations
}

/// Process a single statement for borrow operations.
fn scan_statement(
    state: &mut BorrowState,
    stmt: &Statement,
    violations: &mut Vec<BorrowViolation>,
) {
    if let Statement::Assign { place, rvalue, .. } = stmt {
        // Check rvalue first — it may read from places.
        match rvalue {
            Rvalue::Ref { mutable, place: src } => {
                let kind = if *mutable { BorrowKind::Mutable } else { BorrowKind::Shared };
                if let Err(v) = state.create_ref(src.local, place.local, kind) {
                    violations.push(v);
                }
            }
            Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) => {
                check_operand(state, op, violations);
            }
            Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
                check_operand(state, lhs, violations);
                check_operand(state, rhs, violations);
            }
            Rvalue::Aggregate(_, ops) => {
                for op in ops {
                    check_operand(state, op, violations);
                }
            }
            Rvalue::Discriminant(_) | Rvalue::Len(_) | Rvalue::CopyForDeref(_) => {
                // These are reads but don't move or borrow.
            }
            Rvalue::AddressOf(_, _) => {
                // Raw pointer creation — similar to Ref but no borrow tracking.
            }
            Rvalue::Repeat(op, _) => {
                check_operand(state, op, violations);
            }
            _ => {}
        }
    }
}

/// Check an operand for moves or derefs.
fn check_operand(state: &mut BorrowState, op: &Operand, violations: &mut Vec<BorrowViolation>) {
    match op {
        Operand::Move(place) => {
            // Check if already moved.
            if state.is_moved(place.local) {
                violations.push(BorrowViolation::UseAfterMove { local: place.local });
            } else {
                if let Err(v) = state.move_place(place.local) {
                    violations.push(v);
                }
            }
            // Also check deref projections.
            check_deref_projections(state, place, violations);
        }
        Operand::Copy(place) => {
            // Read access -- check for use-after-move.
            if state.is_moved(place.local) {
                violations.push(BorrowViolation::UseAfterMove { local: place.local });
            }
            check_deref_projections(state, place, violations);
        }
        Operand::Constant(_) => {}
        _ => {}
    }
}

/// If a place has `Deref` projections, check that the base is valid.
fn check_deref_projections(
    state: &BorrowState,
    place: &Place,
    violations: &mut Vec<BorrowViolation>,
) {
    if place.projections.iter().any(|p| matches!(p, trust_types::Projection::Deref))
        && let Err(v) = state.deref(place.local)
    {
        violations.push(v);
    }
}

/// Process a terminator for drop operations.
fn scan_terminator(
    state: &mut BorrowState,
    terminator: &Terminator,
    violations: &mut Vec<BorrowViolation>,
) {
    if let Terminator::Drop { place, .. } = terminator
        && let Err(v) = state.drop_place(place.local)
    {
        violations.push(v);
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::UnwindEdge;
    use trust_types::{
        BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
        Terminator, Ty, VerifiableBody, VerifiableFunction,
    };

    use super::*;

    // -- BorrowState unit tests -----------------------------------------------

    #[test]
    fn test_shared_borrows_ok() {
        let mut state = BorrowState::new();
        // Two shared borrows on the same source local should succeed.
        state.create_ref(0, 1, BorrowKind::Shared).expect("first shared borrow should succeed");
        state.create_ref(0, 2, BorrowKind::Shared).expect("second shared borrow should succeed");

        assert_eq!(state.borrows_on(0).len(), 2);
    }

    #[test]
    fn test_mutable_alias_detected() {
        let mut state = BorrowState::new();
        state.create_ref(0, 1, BorrowKind::Shared).expect("shared borrow should succeed");

        let result = state.create_ref(0, 2, BorrowKind::Mutable);
        assert!(result.is_err(), "mutable borrow after shared should fail");
        match result.unwrap_err() {
            BorrowViolation::AliasingViolation { local, existing, attempted } => {
                assert_eq!(local, 0);
                assert_eq!(existing, BorrowKind::Shared);
                assert_eq!(attempted, BorrowKind::Mutable);
            }
            other => panic!("expected AliasingViolation, got {other:?}"),
        }
    }

    #[test]
    fn test_shared_after_mutable_detected() {
        let mut state = BorrowState::new();
        state.create_ref(0, 1, BorrowKind::Mutable).expect("mutable borrow should succeed");

        let result = state.create_ref(0, 2, BorrowKind::Shared);
        assert!(result.is_err(), "shared borrow after mutable should fail");
        match result.unwrap_err() {
            BorrowViolation::AliasingViolation { local, existing, attempted } => {
                assert_eq!(local, 0);
                assert_eq!(existing, BorrowKind::Mutable);
                assert_eq!(attempted, BorrowKind::Shared);
            }
            other => panic!("expected AliasingViolation, got {other:?}"),
        }
    }

    #[test]
    fn test_use_after_move_detected() {
        let mut state = BorrowState::new();
        state.move_place(0).expect("first move should succeed");

        assert!(state.is_moved(0));

        // Trying to borrow a moved local should fail.
        let result = state.create_ref(0, 1, BorrowKind::Shared);
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), BorrowViolation::UseAfterMove { local: 0 }));
    }

    #[test]
    fn test_double_move_detected() {
        let mut state = BorrowState::new();
        state.move_place(0).expect("first move should succeed");

        let result = state.move_place(0);
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), BorrowViolation::UseAfterMove { local: 0 }));
    }

    #[test]
    fn test_deref_after_move_detected() {
        let mut state = BorrowState::new();
        state.move_place(0).expect("move should succeed");

        let result = state.deref(0);
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), BorrowViolation::UseAfterMove { local: 0 }));
    }

    #[test]
    fn test_drop_with_active_borrow_detected() {
        let mut state = BorrowState::new();
        state.create_ref(0, 1, BorrowKind::Shared).expect("borrow should succeed");

        let result = state.drop_place(0);
        assert!(result.is_err());
        match result.unwrap_err() {
            BorrowViolation::DanglingReference { local, borrower } => {
                assert_eq!(local, 0);
                assert_eq!(borrower, 1);
            }
            other => panic!("expected DanglingReference, got {other:?}"),
        }
    }

    #[test]
    fn test_drop_without_borrow_ok() {
        let mut state = BorrowState::new();
        state.drop_place(0).expect("drop with no borrows should succeed");
        assert!(state.is_dropped(0));
    }

    // -- scan_body integration tests -------------------------------------------

    /// Helper: build a minimal function with given blocks.
    fn make_func(locals: Vec<LocalDecl>, blocks: Vec<BasicBlock>) -> VerifiableFunction {
        VerifiableFunction {
            name: "test_fn".to_string(),
            def_path: "test::test_fn".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody { arg_count: 0, return_ty: Ty::Unit, locals, blocks },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_scan_body_shared_borrows_ok() {
        // let x = 1; let r1 = &x; let r2 = &x;
        let func = make_func(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
                    name: Some("r1".into()),
                },
                LocalDecl {
                    index: 3,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
                    name: Some("r2".into()),
                },
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
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
                terminator: Terminator::Return,
            }],
        );

        let violations = scan_body(&func);
        assert!(violations.is_empty(), "multiple shared borrows should be allowed: {violations:?}");
    }

    #[test]
    fn test_scan_body_mutable_alias_detected() {
        // let x = 1; let r1 = &x; let r2 = &mut x;  // violation
        let func = make_func(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
                    name: Some("r1".into()),
                },
                LocalDecl {
                    index: 3,
                    ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
                    name: Some("r2".into()),
                },
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
        );

        let violations = scan_body(&func);
        assert_eq!(violations.len(), 1, "should detect mutable aliasing: {violations:?}");
        assert!(
            matches!(&violations[0], BorrowViolation::AliasingViolation { local: 1, .. }),
            "violation should be on local 1: {:?}",
            violations[0]
        );
    }

    #[test]
    fn test_scan_body_use_after_move_detected() {
        // let x = 1; let y = move x; let z = copy x;  // violation
        let func = make_func(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("y".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("z".into()) },
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Move(Place::local(1))),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
        );

        let violations = scan_body(&func);
        assert_eq!(violations.len(), 1, "should detect use-after-move: {violations:?}");
        assert!(
            matches!(&violations[0], BorrowViolation::UseAfterMove { local: 1 }),
            "violation should be UseAfterMove on local 1: {:?}",
            violations[0]
        );
    }

    #[test]
    fn test_scan_body_dangling_reference_on_drop() {
        // let x = 1; let r = &x; drop(x);  // r is dangling
        let func = make_func(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
                    name: Some("r".into()),
                },
            ],
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Drop {
                        unwind: UnwindEdge::Unreachable,
                        place: Place::local(1),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        );

        let violations = scan_body(&func);
        assert_eq!(violations.len(), 1, "should detect dangling reference: {violations:?}");
        assert!(
            matches!(&violations[0], BorrowViolation::DanglingReference { local: 1, borrower: 2 }),
            "violation should be DanglingReference: {:?}",
            violations[0]
        );
    }

    #[test]
    fn test_scan_body_no_violations_clean_function() {
        // fn f(a: u32, b: u32) -> u32 { a + b }
        let func = make_func(
            vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
        );

        let violations = scan_body(&func);
        assert!(violations.is_empty(), "clean function should have no violations: {violations:?}");
    }

    #[test]
    fn test_scan_body_move_then_borrow_detected() {
        // let x = 1; let y = move x; let r = &x;  // violation
        let func = make_func(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("y".into()) },
                LocalDecl {
                    index: 3,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
                    name: Some("r".into()),
                },
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Move(Place::local(1))),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
        );

        let violations = scan_body(&func);
        assert_eq!(violations.len(), 1, "should detect borrow of moved local: {violations:?}");
        assert!(
            matches!(&violations[0], BorrowViolation::UseAfterMove { local: 1 }),
            "violation should be UseAfterMove: {:?}",
            violations[0]
        );
    }

    #[test]
    fn test_exclusive_mutable_borrow_ok() {
        // let mut x = 1; let r = &mut x;  -- single mutable borrow is fine
        let func = make_func(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
                    name: Some("r".into()),
                },
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
        );

        let violations = scan_body(&func);
        assert!(violations.is_empty(), "single mutable borrow should be allowed: {violations:?}");
    }

    #[test]
    fn test_two_mutable_borrows_detected() {
        // let mut x = 1; let r1 = &mut x; let r2 = &mut x;  // violation
        let func = make_func(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
                    name: Some("r1".into()),
                },
                LocalDecl {
                    index: 3,
                    ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
                    name: Some("r2".into()),
                },
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
        );

        let violations = scan_body(&func);
        assert_eq!(violations.len(), 1, "should detect double mutable borrow: {violations:?}");
        assert!(
            matches!(
                &violations[0],
                BorrowViolation::AliasingViolation {
                    local: 1,
                    existing: BorrowKind::Mutable,
                    attempted: BorrowKind::Mutable,
                }
            ),
            "violation should be AliasingViolation: {:?}",
            violations[0]
        );
    }
}
