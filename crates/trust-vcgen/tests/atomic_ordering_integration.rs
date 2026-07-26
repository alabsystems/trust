// trust_vcgen/tests/atomic_ordering_integration.rs: Integration tests for atomic ordering analysis
//
// Tests the full pipeline: construct VerifiableFunction with atomic operations
// on Call terminators -> run check_operation_legality -> assert correct VCs.
//
// Part of #614.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;
use trust_vcgen::memory_ordering::MemoryModelChecker;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Build a minimal VerifiableFunction with a single Call terminator carrying
/// an atomic operation.
fn make_atomic_func(name: &str, atomic_ops: Vec<AtomicOperation>) -> VerifiableFunction {
    let mut blocks = Vec::new();

    for (i, op) in atomic_ops.iter().enumerate() {
        let target = if i + 1 < atomic_ops.len() {
            Some(BlockId(i + 1))
        } else {
            Some(BlockId(atomic_ops.len()))
        };
        blocks.push(BasicBlock {
            id: BlockId(i),
            stmts: vec![],
            terminator: Terminator::Call { unwind: trust_types::UnwindEdge::Unreachable,  is_unsafe_sig: false, is_foreign: false,
                func: format!("core::intrinsics::atomic_{}", op.op_kind),
                args: vec![Operand::Copy(Place::local(1))],
                dest: Place::local(2),
                target,
                span: op.span.clone(),
                atomic: Some(op.clone()),
            },
        });
    }

    // Final return block
    blocks.push(BasicBlock {
        id: BlockId(atomic_ops.len()),
        stmts: vec![],
        terminator: Terminator::Return,
    });

    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("integration::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("ptr".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("result".into()) },
            ],
            blocks,
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn make_op(
    op_kind: AtomicOpKind,
    ordering: AtomicOrdering,
    failure_ordering: Option<AtomicOrdering>,
) -> AtomicOperation {
    AtomicOperation {
        place: Place::local(1),
        dest: Some(Place::local(2)),
        op_kind,
        ordering,
        failure_ordering,
        span: SourceSpan::default(),
    }
}

/// Extract atomic operations from a VerifiableFunction's Call terminators.
fn extract_atomic_ops(func: &VerifiableFunction) -> Vec<AtomicOperation> {
    func.body
        .blocks
        .iter()
        .filter_map(|block| {
            if let Terminator::Call { atomic: Some(op), .. } = &block.terminator {
                Some(op.clone())
            } else {
                None
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Integration: construct function -> extract atomics -> check legality -> assert VCs
// ---------------------------------------------------------------------------

#[test]
fn test_integration_valid_load_store_no_vcs() {
    let func = make_atomic_func(
        "valid_load_store",
        vec![
            make_op(AtomicOpKind::Load, AtomicOrdering::Acquire, None),
            make_op(AtomicOpKind::Store, AtomicOrdering::Release, None),
        ],
    );

    let ops = extract_atomic_ops(&func);
    let vcs = MemoryModelChecker::check_operation_legality(&ops, &func.name);
    assert!(vcs.is_empty(), "valid load(Acquire) + store(Release) should produce no VCs");
}

#[test]
fn test_integration_l1_load_release_produces_vc() {
    let func = make_atomic_func(
        "bad_load",
        vec![make_op(AtomicOpKind::Load, AtomicOrdering::Release, None)],
    );

    let ops = extract_atomic_ops(&func);
    let vcs = MemoryModelChecker::check_operation_legality(&ops, &func.name);
    assert_eq!(vcs.len(), 1);
    assert!(matches!(&vcs[0].kind, VcKind::InsufficientOrdering { .. }));
    assert_eq!(vcs[0].function, "bad_load");
}

#[test]
fn test_integration_l2_store_acquire_produces_vc() {
    let func = make_atomic_func(
        "bad_store",
        vec![make_op(AtomicOpKind::Store, AtomicOrdering::Acquire, None)],
    );

    let ops = extract_atomic_ops(&func);
    let vcs = MemoryModelChecker::check_operation_legality(&ops, &func.name);
    assert_eq!(vcs.len(), 1);
    assert!(matches!(&vcs[0].kind, VcKind::InsufficientOrdering { .. }));
}

#[test]
fn test_integration_l3_cas_failure_release_produces_vc() {
    let func = make_atomic_func(
        "bad_cas",
        vec![make_op(
            AtomicOpKind::CompareExchange,
            AtomicOrdering::SeqCst,
            Some(AtomicOrdering::Release),
        )],
    );

    let ops = extract_atomic_ops(&func);
    let vcs = MemoryModelChecker::check_operation_legality(&ops, &func.name);
    assert!(!vcs.is_empty(), "CAS with failure=Release should produce L3 VC");
}

#[test]
fn test_integration_l4_cas_failure_stronger_than_success() {
    let func = make_atomic_func(
        "bad_cas_order",
        vec![make_op(
            AtomicOpKind::CompareExchange,
            AtomicOrdering::Relaxed,
            Some(AtomicOrdering::Acquire),
        )],
    );

    let ops = extract_atomic_ops(&func);
    let vcs = MemoryModelChecker::check_operation_legality(&ops, &func.name);
    assert!(!vcs.is_empty(), "CAS with failure > success should produce L4 VC");
}

#[test]
fn test_integration_l5_fence_relaxed_produces_vc() {
    let func = make_atomic_func(
        "bad_fence",
        vec![make_op(AtomicOpKind::Fence, AtomicOrdering::Relaxed, None)],
    );

    let ops = extract_atomic_ops(&func);
    let vcs = MemoryModelChecker::check_operation_legality(&ops, &func.name);
    assert_eq!(vcs.len(), 1, "fence(Relaxed) should produce L5 VC");
}

#[test]
fn test_integration_mixed_valid_and_invalid() {
    let func = make_atomic_func(
        "mixed_ops",
        vec![
            // Valid
            make_op(AtomicOpKind::Load, AtomicOrdering::SeqCst, None),
            // Invalid (L2)
            make_op(AtomicOpKind::Store, AtomicOrdering::AcqRel, None),
            // Valid
            make_op(AtomicOpKind::FetchAdd, AtomicOrdering::Relaxed, None),
            // Invalid (L5)
            make_op(AtomicOpKind::Fence, AtomicOrdering::Relaxed, None),
        ],
    );

    let ops = extract_atomic_ops(&func);
    let vcs = MemoryModelChecker::check_operation_legality(&ops, &func.name);
    assert_eq!(vcs.len(), 2, "should detect exactly the 2 violations");
}

#[test]
fn test_integration_all_rmw_with_acqrel_valid() {
    let rmw_kinds = vec![
        AtomicOpKind::Exchange,
        AtomicOpKind::FetchAdd,
        AtomicOpKind::FetchSub,
        AtomicOpKind::FetchAnd,
        AtomicOpKind::FetchOr,
        AtomicOpKind::FetchXor,
        AtomicOpKind::FetchNand,
        AtomicOpKind::FetchMin,
        AtomicOpKind::FetchMax,
    ];

    let ops: Vec<_> =
        rmw_kinds.into_iter().map(|kind| make_op(kind, AtomicOrdering::AcqRel, None)).collect();

    let func = make_atomic_func("all_rmw", ops);
    let extracted = extract_atomic_ops(&func);
    let vcs = MemoryModelChecker::check_operation_legality(&extracted, &func.name);
    assert!(vcs.is_empty(), "all RMW ops with AcqRel should be legal");
}

#[test]
fn test_integration_cas_with_valid_failure_ordering() {
    let func = make_atomic_func(
        "valid_cas",
        vec![
            make_op(
                AtomicOpKind::CompareExchange,
                AtomicOrdering::AcqRel,
                Some(AtomicOrdering::Acquire),
            ),
            make_op(
                AtomicOpKind::CompareExchangeWeak,
                AtomicOrdering::SeqCst,
                Some(AtomicOrdering::Relaxed),
            ),
        ],
    );

    let ops = extract_atomic_ops(&func);
    let vcs = MemoryModelChecker::check_operation_legality(&ops, &func.name);
    assert!(vcs.is_empty(), "CAS with valid failure orderings should produce no VCs");
}

#[test]
fn test_integration_compiler_fence_relaxed_violation() {
    let func = make_atomic_func(
        "bad_compiler_fence",
        vec![make_op(AtomicOpKind::CompilerFence, AtomicOrdering::Relaxed, None)],
    );

    let ops = extract_atomic_ops(&func);
    let vcs = MemoryModelChecker::check_operation_legality(&ops, &func.name);
    assert_eq!(vcs.len(), 1, "compiler_fence(Relaxed) should produce L5 VC");
}

#[test]
fn test_integration_compiler_fence_seqcst_valid() {
    let func = make_atomic_func(
        "valid_compiler_fence",
        vec![make_op(AtomicOpKind::CompilerFence, AtomicOrdering::SeqCst, None)],
    );

    let ops = extract_atomic_ops(&func);
    let vcs = MemoryModelChecker::check_operation_legality(&ops, &func.name);
    assert!(vcs.is_empty(), "compiler_fence(SeqCst) should be legal");
}

// ---------------------------------------------------------------------------
// Integration: Full pipeline with generate_vcs()
// ---------------------------------------------------------------------------

#[test]
fn test_integration_generate_vcs_does_not_crash_with_atomics() {
    // Verify that generate_vcs can handle functions with atomic terminators
    // without panicking, even though it may not produce atomic-specific VCs yet.
    let func = make_atomic_func(
        "atomic_fn",
        vec![
            make_op(AtomicOpKind::Load, AtomicOrdering::Acquire, None),
            make_op(AtomicOpKind::Store, AtomicOrdering::Release, None),
        ],
    );

    // This should not panic
    let vcs = trust_vcgen::generate_vcs(&func);
    // We don't assert specific VCs here since generate_vcs may not yet wire
    // atomic checks, but it must not crash.
    let _ = vcs;
}

// ---------------------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------------------

#[test]
fn test_integration_function_with_no_atomics() {
    let func = VerifiableFunction {
        name: "plain_fn".to_string(),
        def_path: "integration::plain_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let ops = extract_atomic_ops(&func);
    assert!(ops.is_empty());
    let vcs = MemoryModelChecker::check_operation_legality(&ops, &func.name);
    assert!(vcs.is_empty());
}

#[test]
fn test_integration_every_legality_rule_in_one_function() {
    // Build a function that violates all 5 rules at once
    let func = make_atomic_func(
        "all_violations",
        vec![
            // L1: load with Release
            make_op(AtomicOpKind::Load, AtomicOrdering::Release, None),
            // L2: store with Acquire
            make_op(AtomicOpKind::Store, AtomicOrdering::Acquire, None),
            // L3: CAS failure=AcqRel
            make_op(
                AtomicOpKind::CompareExchange,
                AtomicOrdering::SeqCst,
                Some(AtomicOrdering::AcqRel),
            ),
            // L4: CAS failure > success (Relaxed success, Acquire failure)
            make_op(
                AtomicOpKind::CompareExchangeWeak,
                AtomicOrdering::Relaxed,
                Some(AtomicOrdering::Acquire),
            ),
            // L5: fence with Relaxed
            make_op(AtomicOpKind::Fence, AtomicOrdering::Relaxed, None),
        ],
    );

    let ops = extract_atomic_ops(&func);
    let vcs = MemoryModelChecker::check_operation_legality(&ops, &func.name);
    // L1 + L2 + L3 + L4 + L5 = at least 5 VCs
    assert!(vcs.len() >= 5, "should detect at least one violation per rule, got {} VCs", vcs.len());
}

#[test]
fn test_integration_vc_kind_details() {
    let func = make_atomic_func(
        "vc_detail_check",
        vec![make_op(AtomicOpKind::Store, AtomicOrdering::AcqRel, None)],
    );

    let ops = extract_atomic_ops(&func);
    let vcs = MemoryModelChecker::check_operation_legality(&ops, &func.name);
    assert_eq!(vcs.len(), 1);

    match &vcs[0].kind {
        VcKind::InsufficientOrdering { variable, actual, required } => {
            assert!(variable.contains("1"), "variable should reference the local");
            assert_eq!(actual, "AcqRel", "actual ordering should be AcqRel");
            assert!(required.contains("L2"), "required should mention L2 rule");
        }
        other => panic!("expected InsufficientOrdering, got: {other:?}"),
    }
}
