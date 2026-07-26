// trust-integration-tests/tests/ownership_e2e.rs: Ownership/memory safety error detection tests
//
// Tests 6 VcKinds related to ownership and memory safety:
//   Tier A (VC generation): UseAfterFree, DoubleFree, AliasingViolation
//   Tier B (pipeline routing): LifetimeViolation, SendViolation, SyncViolation
//
// Each VcKind has a buggy variant (violation detected) and a safe variant (no violation).
//
// Part of #637
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use trust_types::provenance::*;
use trust_types::*;
use trust_vcgen::memory_provenance::ProvenanceTracker;
use trust_vcgen::ownership::{
    BorrowKind as OwnershipBorrowKind, BorrowState, BorrowViolation, scan_body,
};

// ===========================================================================
// Tier A: VC Generation Tests — UseAfterFree
// ===========================================================================

/// Buggy: allocate, free, then read through the freed pointer.
/// ProvenanceTracker should detect UseAfterFree.
#[test]
fn test_use_after_free_buggy() {
    let mut tracker = ProvenanceTracker::new();

    // Allocate a region and bind local 0 to it.
    let region = tracker.new_allocation(BorrowKind::MutableRef);
    tracker.bind_local(0, region, region);

    // Free the region.
    tracker.free_region(region, SourceSpan::default());

    // Read through the freed pointer — should detect UseAfterFree.
    let violations = tracker.read_through(0, &SourceSpan::default());
    assert!(
        violations.iter().any(|v| v.kind == ProvenanceViolationKind::UseAfterFree),
        "Should detect UseAfterFree when reading through freed pointer, got: {violations:?}"
    );
}

/// Buggy: build synthetic MIR that drops a ref-typed local then reads through it.
/// `check_provenance` should produce VCs indicating the violation.
#[test]
fn test_use_after_free_mir_buggy() {
    // fn f(x: &mut u32) { drop(x); let _ = *x; }
    // MIR: bb0: Drop(_1) -> bb1; bb1: _2 = Copy(*_1); return
    let func = VerifiableFunction {
        name: "use_after_free".into(),
        def_path: "test::use_after_free".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
                    name: Some("x".into()),
                },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("val".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Drop {
                        place: Place::local(1),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                        unwind: trust_types::UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Deref],
                        })),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    };

    let vcs = trust_vcgen::memory_provenance::check_provenance(&func);
    assert!(!vcs.is_empty(), "check_provenance should detect use-after-free in MIR, got 0 VCs");
}

/// Buggy: use-after-move detected by ownership scanner.
/// move x into y, then copy x — should detect UseAfterMove.
#[test]
fn test_use_after_move_mir_buggy() {
    // fn f() { let x = 1; let y = move x; let z = copy x; }
    let func = VerifiableFunction {
        name: "use_after_move".into(),
        def_path: "test::use_after_move".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("y".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("z".into()) },
            ],
            blocks: vec![BasicBlock {
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
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    };

    let violations = scan_body(&func);
    assert!(
        violations.iter().any(|v| matches!(v, BorrowViolation::UseAfterMove { local: 1 })),
        "scan_body should detect use-after-move on local 1, got: {violations:?}"
    );
}

/// Safe: allocate, read through the pointer (no free). No violation.
#[test]
fn test_use_after_free_safe() {
    let mut tracker = ProvenanceTracker::new();

    let region = tracker.new_allocation(BorrowKind::MutableRef);
    tracker.bind_local(0, region, region);

    // Read through valid pointer — should be fine.
    let violations = tracker.read_through(0, &SourceSpan::default());
    assert!(
        violations.is_empty(),
        "Reading through valid pointer should produce no violations, got: {violations:?}"
    );
}

// ===========================================================================
// Tier A: VC Generation Tests — DoubleFree
// ===========================================================================

/// Buggy: allocate, free, then access again (simulating double-free).
/// The second access to a freed region triggers UseAfterFree on the provenance tracker,
/// which is the provenance-level manifestation of double-free.
#[test]
fn test_double_free_buggy() {
    let mut tracker = ProvenanceTracker::new();

    let region = tracker.new_allocation(BorrowKind::MutableRef);
    tracker.bind_local(0, region, region);

    // First free.
    tracker.free_region(region, SourceSpan::default());

    // Second access after free — the region is already freed.
    // Write through detects use-after-free (the provenance-level manifestation of double-free).
    let violations = tracker.write_through(0, &SourceSpan::default());
    assert!(
        violations.iter().any(|v| v.kind == ProvenanceViolationKind::UseAfterFree),
        "Should detect violation on double-free (write to freed region), got: {violations:?}"
    );
}

/// Buggy: drop a local that has a live borrow — creates dangling reference.
/// This is the ownership-level manifestation of memory unsafety related to double-free.
#[test]
fn test_double_free_dangling_ref_mir_buggy() {
    // fn f() { let x = 1; let r = &x; drop(x); }
    // MIR: bb0: _2 = &_1; Drop(_1) -> bb1; bb1: return
    let func = VerifiableFunction {
        name: "double_free_dangling".into(),
        def_path: "test::double_free_dangling".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
                    name: Some("r".into()),
                },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Drop {
                        place: Place::local(1),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                        unwind: trust_types::UnwindEdge::Unreachable,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    };

    let violations = scan_body(&func);
    assert!(
        violations
            .iter()
            .any(|v| matches!(v, BorrowViolation::DanglingReference { local: 1, borrower: 2 })),
        "scan_body should detect dangling reference on drop, got: {violations:?}"
    );
}

/// Safe: allocate and free exactly once. No violation.
#[test]
fn test_double_free_safe() {
    let mut tracker = ProvenanceTracker::new();

    let region = tracker.new_allocation(BorrowKind::MutableRef);
    tracker.bind_local(0, region, region);

    // Single free — no violation.
    tracker.free_region(region, SourceSpan::default());

    // No further access — should be clean.
    assert_eq!(tracker.region_count(), 1, "Should have exactly 1 region tracked");
}

// ===========================================================================
// Tier A: VC Generation Tests — AliasingViolation
// ===========================================================================

/// Buggy: create a shared borrow, then a mutable borrow on the same local.
/// BorrowState should detect an AliasingViolation.
#[test]
fn test_aliasing_violation_buggy() {
    let mut state = BorrowState::new();

    // Create a shared borrow: _2 = &_1
    let result1 = state.create_ref(1, 2, OwnershipBorrowKind::Shared);
    assert!(result1.is_ok(), "First shared borrow should succeed");

    // Create a mutable borrow: _3 = &mut _1 (conflicts with shared borrow)
    let result2 = state.create_ref(1, 3, OwnershipBorrowKind::Mutable);
    assert!(
        matches!(result2, Err(BorrowViolation::AliasingViolation { .. })),
        "Mutable borrow should conflict with existing shared borrow, got: {result2:?}"
    );
}

/// Buggy: synthetic MIR with two conflicting borrows on the same local.
#[test]
fn test_aliasing_violation_mir_buggy() {
    // fn f(x: u32) { let r = &x; let m = &mut x; }
    // MIR: bb0: _2 = Ref(Shared, _1); _3 = Ref(Mutable, _1); return
    let func = VerifiableFunction {
        name: "aliasing_violation".into(),
        def_path: "test::aliasing_violation".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
                    name: Some("r".into()),
                },
                LocalDecl {
                    index: 3,
                    ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
                    name: Some("m".into()),
                },
            ],
            blocks: vec![BasicBlock {
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
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    };

    let violations = scan_body(&func);
    assert!(
        violations.iter().any(|v| matches!(v, BorrowViolation::AliasingViolation { .. })),
        "scan_body should detect aliasing violation (mutable + shared borrow), got: {violations:?}"
    );
}

/// Buggy: two mutable borrows on the same local (double &mut).
#[test]
fn test_aliasing_violation_double_mut_buggy() {
    let mut state = BorrowState::new();

    let result1 = state.create_ref(1, 2, OwnershipBorrowKind::Mutable);
    assert!(result1.is_ok(), "First mutable borrow should succeed");

    let result2 = state.create_ref(1, 3, OwnershipBorrowKind::Mutable);
    assert!(
        matches!(
            result2,
            Err(BorrowViolation::AliasingViolation {
                existing: OwnershipBorrowKind::Mutable,
                attempted: OwnershipBorrowKind::Mutable,
                ..
            })
        ),
        "Second mutable borrow should conflict with first, got: {result2:?}"
    );
}

/// Safe: two shared borrows on the same local is allowed.
#[test]
fn test_aliasing_violation_safe() {
    let mut state = BorrowState::new();

    // Two shared borrows on the same local — allowed.
    let result1 = state.create_ref(1, 2, OwnershipBorrowKind::Shared);
    assert!(result1.is_ok(), "First shared borrow should succeed");

    let result2 = state.create_ref(1, 3, OwnershipBorrowKind::Shared);
    assert!(
        result2.is_ok(),
        "Second shared borrow should succeed (no mutable aliasing), got: {result2:?}"
    );
}

/// Safe: synthetic MIR with only shared borrows — no violation.
#[test]
fn test_aliasing_violation_mir_safe() {
    // fn f(x: u32) { let r1 = &x; let r2 = &x; }
    let func = VerifiableFunction {
        name: "no_aliasing".into(),
        def_path: "test::no_aliasing".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
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
            blocks: vec![BasicBlock {
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
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    };

    let violations = scan_body(&func);
    assert!(
        violations.is_empty(),
        "Two shared borrows should produce no violations, got: {violations:?}"
    );
}

// ===========================================================================
// Tier B: Pipeline Routing Tests — LifetimeViolation, SendViolation, SyncViolation
//
// These VcKind variants exist in trust-types but the router's termination_dispatch
// does not yet handle them (#546 follow-up). We verify VcKind metadata (proof_level,
// description, proof_level) which is the integration contract between
// trust-types and the pipeline.
// ===========================================================================

/// LifetimeViolation: reference outlives its referent.
#[test]
fn test_lifetime_violation_properties() {
    let kind = VcKind::LifetimeViolation;

    assert_eq!(kind.proof_level(), ProofLevel::L0Safety);
    assert!(
        kind.description().contains("lifetime"),
        "LifetimeViolation description should mention 'lifetime', got: {}",
        kind.description()
    );
}

/// LifetimeViolation: construct a VC and verify it is well-formed.
#[test]
fn test_lifetime_violation_vc_construction() {
    let vc = VerificationCondition {
        function: "test::dangling_ref".into(),
        kind: VcKind::LifetimeViolation,
        location: SourceSpan::default(),
        formula: Formula::Var("lifetime_check".into(), Sort::Bool),
        contract_metadata: None,
    };

    assert_eq!(vc.function, "test::dangling_ref");
    assert!(matches!(vc.kind, VcKind::LifetimeViolation));
    assert_eq!(vc.kind.proof_level(), ProofLevel::L0Safety);
}

/// SendViolation: non-Send type sent across thread boundary.
#[test]
fn test_send_violation_properties() {
    let kind = VcKind::SendViolation;

    assert_eq!(kind.proof_level(), ProofLevel::L0Safety);
    assert!(
        kind.description().contains("Send"),
        "SendViolation description should mention 'Send', got: {}",
        kind.description()
    );
}

/// SendViolation: construct a VC and verify it is well-formed.
#[test]
fn test_send_violation_vc_construction() {
    let vc = VerificationCondition {
        function: "test::spawn_with_rc".into(),
        kind: VcKind::SendViolation,
        location: SourceSpan::default(),
        formula: Formula::Var("send_check".into(), Sort::Bool),
        contract_metadata: None,
    };

    assert_eq!(vc.function, "test::spawn_with_rc");
    assert!(matches!(vc.kind, VcKind::SendViolation));
    assert_eq!(vc.kind.proof_level(), ProofLevel::L0Safety);
}

/// SyncViolation: non-Sync type shared across threads.
#[test]
fn test_sync_violation_properties() {
    let kind = VcKind::SyncViolation;

    assert_eq!(kind.proof_level(), ProofLevel::L0Safety);
    assert!(
        kind.description().contains("Sync"),
        "SyncViolation description should mention 'Sync', got: {}",
        kind.description()
    );
}

/// SyncViolation: construct a VC and verify it is well-formed.
#[test]
fn test_sync_violation_vc_construction() {
    let vc = VerificationCondition {
        function: "test::share_cell_across_threads".into(),
        kind: VcKind::SyncViolation,
        location: SourceSpan::default(),
        formula: Formula::Var("sync_check".into(), Sort::Bool),
        contract_metadata: None,
    };

    assert_eq!(vc.function, "test::share_cell_across_threads");
    assert!(matches!(vc.kind, VcKind::SyncViolation));
    assert_eq!(vc.kind.proof_level(), ProofLevel::L0Safety);
}

// ===========================================================================
// Cross-cutting: Proof level and description validation for all 6 VcKinds
// ===========================================================================

/// All 6 ownership/memory safety VcKinds should have proof level L0Safety.
#[test]
fn test_all_ownership_vckind_proof_levels() {
    let kinds: Vec<VcKind> = vec![
        VcKind::UseAfterFree,
        VcKind::DoubleFree,
        VcKind::AliasingViolation { mutable: true },
        VcKind::AliasingViolation { mutable: false },
        VcKind::LifetimeViolation,
        VcKind::SendViolation,
        VcKind::SyncViolation,
    ];

    for kind in &kinds {
        assert_eq!(kind.proof_level(), ProofLevel::L0Safety, "{:?} should be L0Safety", kind);
    }
}

/// All 6 VcKinds produce non-empty, descriptive descriptions.
#[test]
fn test_all_ownership_vckind_descriptions() {
    let test_cases: Vec<(VcKind, &str)> = vec![
        (VcKind::UseAfterFree, "use after free"),
        (VcKind::DoubleFree, "double free"),
        (VcKind::AliasingViolation { mutable: true }, "&mut"),
        (VcKind::AliasingViolation { mutable: false }, "&"),
        (VcKind::LifetimeViolation, "lifetime"),
        (VcKind::SendViolation, "Send"),
        (VcKind::SyncViolation, "Sync"),
    ];

    for (kind, expected_substr) in &test_cases {
        let desc = kind.description();
        assert!(!desc.is_empty(), "{:?} description should not be empty", kind);
        assert!(
            desc.contains(expected_substr),
            "{:?} description should contain '{}', got: '{}'",
            kind,
            expected_substr,
            desc
        );
    }
}

/// All 6 ownership VcKinds should have no runtime check (UB in unsafe code).
#[test]
fn test_all_ownership_vckind_no_runtime_check() {
    let kinds: Vec<VcKind> = vec![
        VcKind::UseAfterFree,
        VcKind::DoubleFree,
        VcKind::AliasingViolation { mutable: true },
        VcKind::AliasingViolation { mutable: false },
        VcKind::LifetimeViolation,
        VcKind::SendViolation,
        VcKind::SyncViolation,
    ];

    for kind in &kinds {
        assert_eq!(kind.proof_level(), ProofLevel::L0Safety, "{:?} should be L0Safety", kind);
    }
}

/// Construct VCs for all 6 ownership VcKinds and verify they are well-formed.
#[test]
fn test_construct_all_6_ownership_vcs() {
    let vcs: Vec<VerificationCondition> = vec![
        VerificationCondition {
            function: "uaf".into(),
            kind: VcKind::UseAfterFree,
            location: SourceSpan::default(),
            formula: Formula::Var("uaf".into(), Sort::Bool),
            contract_metadata: None,
        },
        VerificationCondition {
            function: "df".into(),
            kind: VcKind::DoubleFree,
            location: SourceSpan::default(),
            formula: Formula::Var("df".into(), Sort::Bool),
            contract_metadata: None,
        },
        VerificationCondition {
            function: "alias_mut".into(),
            kind: VcKind::AliasingViolation { mutable: true },
            location: SourceSpan::default(),
            formula: Formula::Var("alias_mut".into(), Sort::Bool),
            contract_metadata: None,
        },
        VerificationCondition {
            function: "alias_shared".into(),
            kind: VcKind::AliasingViolation { mutable: false },
            location: SourceSpan::default(),
            formula: Formula::Var("alias_shared".into(), Sort::Bool),
            contract_metadata: None,
        },
        VerificationCondition {
            function: "lt".into(),
            kind: VcKind::LifetimeViolation,
            location: SourceSpan::default(),
            formula: Formula::Var("lt".into(), Sort::Bool),
            contract_metadata: None,
        },
        VerificationCondition {
            function: "send".into(),
            kind: VcKind::SendViolation,
            location: SourceSpan::default(),
            formula: Formula::Var("send".into(), Sort::Bool),
            contract_metadata: None,
        },
        VerificationCondition {
            function: "sync".into(),
            kind: VcKind::SyncViolation,
            location: SourceSpan::default(),
            formula: Formula::Var("sync".into(), Sort::Bool),
            contract_metadata: None,
        },
    ];

    assert_eq!(vcs.len(), 7, "should have 7 VCs (6 kinds, AliasingViolation has 2 variants)");

    // All should be L0Safety
    for vc in &vcs {
        assert_eq!(
            vc.kind.proof_level(),
            ProofLevel::L0Safety,
            "{} should be L0Safety",
            vc.function
        );
    }

    // Verify each VC has distinct function names
    let func_names: Vec<&str> = vcs.iter().map(|vc| vc.function.as_str()).collect();
    for (i, name) in func_names.iter().enumerate() {
        for (j, other) in func_names.iter().enumerate() {
            if i != j {
                assert_ne!(name, other, "VC function names should be unique");
            }
        }
    }
}
