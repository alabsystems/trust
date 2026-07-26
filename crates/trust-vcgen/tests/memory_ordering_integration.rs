// trust_vcgen/tests/memory_ordering_integration.rs: Integration tests for atomic ordering analysis
//
// Exercises the full memory ordering pipeline:
// 1. AtomicOrdering lattice properties (join, meet, is_at_least)
// 2. AccessKind classification including AtomicRmw
// 3. Data race detection: positive and negative cases
// 4. MemoryModelChecker: operation legality (L1-L5) via check_operation_legality
// 5. DataRaceDetector: end-to-end race detection with HB
//
// Part of #614: Phase 1.6-1.7 tests for atomic ordering analysis
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;
use trust_vcgen::{
    AccessKind, AtomicAccessEntry, AtomicAccessLog, DataRaceDetector, HappensBefore,
    MemoryModelChecker, MemoryOrdering, OrderingRequirement, SharedAccess,
    check_ordering_sufficient, detect_potential_races, generate_ordering_vcs, generate_race_vcs,
};

// ===========================================================================
// Part 1: AtomicOrdering lattice (trust-types) — integration verification
// ===========================================================================

/// Verify the lattice absorption law: join(a, meet(a, b)) == a.
#[test]
fn test_atomic_ordering_lattice_absorption_join_meet() {
    use AtomicOrdering::*;
    let all = [Relaxed, Acquire, Release, AcqRel, SeqCst];
    for &a in &all {
        for &b in &all {
            let meet_ab = a.meet(&b);
            let result = a.join(&meet_ab);
            assert_eq!(
                result, a,
                "absorption law: join({a}, meet({a}, {b})) = join({a}, {meet_ab}) = {result}, expected {a}"
            );
        }
    }
}

/// Verify the lattice absorption law: meet(a, join(a, b)) == a.
#[test]
fn test_atomic_ordering_lattice_absorption_meet_join() {
    use AtomicOrdering::*;
    let all = [Relaxed, Acquire, Release, AcqRel, SeqCst];
    for &a in &all {
        for &b in &all {
            let join_ab = a.join(&b);
            let result = a.meet(&join_ab);
            assert_eq!(
                result, a,
                "absorption law: meet({a}, join({a}, {b})) = meet({a}, {join_ab}) = {result}, expected {a}"
            );
        }
    }
}

/// Verify join associativity: join(join(a, b), c) == join(a, join(b, c)).
#[test]
fn test_atomic_ordering_join_associative() {
    use AtomicOrdering::*;
    let all = [Relaxed, Acquire, Release, AcqRel, SeqCst];
    for &a in &all {
        for &b in &all {
            for &c in &all {
                let lhs = a.join(&b).join(&c);
                let rhs = a.join(&b.join(&c));
                assert_eq!(
                    lhs, rhs,
                    "join associativity: join(join({a}, {b}), {c}) = {lhs} != join({a}, join({b}, {c})) = {rhs}"
                );
            }
        }
    }
}

/// Verify meet associativity: meet(meet(a, b), c) == meet(a, meet(b, c)).
#[test]
fn test_atomic_ordering_meet_associative() {
    use AtomicOrdering::*;
    let all = [Relaxed, Acquire, Release, AcqRel, SeqCst];
    for &a in &all {
        for &b in &all {
            for &c in &all {
                let lhs = a.meet(&b).meet(&c);
                let rhs = a.meet(&b.meet(&c));
                assert_eq!(
                    lhs, rhs,
                    "meet associativity: meet(meet({a}, {b}), {c}) = {lhs} != meet({a}, meet({b}, {c})) = {rhs}"
                );
            }
        }
    }
}

/// Verify is_at_least consistency with partial_cmp.
#[test]
fn test_atomic_ordering_is_at_least_consistent_with_partial_cmp() {
    use AtomicOrdering::*;
    let all = [Relaxed, Acquire, Release, AcqRel, SeqCst];
    for &a in &all {
        for &b in &all {
            let at_least = a.is_at_least(&b);
            let cmp = a.partial_cmp(&b);
            match cmp {
                Some(std::cmp::Ordering::Greater | std::cmp::Ordering::Equal) => {
                    assert!(
                        at_least,
                        "{a}.is_at_least({b}) should be true when partial_cmp says >= "
                    );
                }
                Some(std::cmp::Ordering::Less) => {
                    assert!(
                        !at_least,
                        "{a}.is_at_least({b}) should be false when partial_cmp says < "
                    );
                }
                None => {
                    // Incomparable: is_at_least should be false
                    assert!(!at_least, "{a}.is_at_least({b}) should be false when incomparable");
                }
            }
        }
    }
}

/// Verify idempotence: join(a, a) == a, meet(a, a) == a.
#[test]
fn test_atomic_ordering_idempotence() {
    use AtomicOrdering::*;
    for &a in &[Relaxed, Acquire, Release, AcqRel, SeqCst] {
        assert_eq!(a.join(&a), a, "join({a}, {a}) should be {a}");
        assert_eq!(a.meet(&a), a, "meet({a}, {a}) should be {a}");
    }
}

/// Verify lattice bounds: Relaxed is bottom, SeqCst is top.
#[test]
fn test_atomic_ordering_lattice_bounds() {
    use AtomicOrdering::*;
    for &a in &[Relaxed, Acquire, Release, AcqRel, SeqCst] {
        assert_eq!(a.join(&SeqCst), SeqCst, "join({a}, SeqCst) should be SeqCst");
        assert_eq!(a.meet(&Relaxed), Relaxed, "meet({a}, Relaxed) should be Relaxed");
        assert_eq!(a.join(&Relaxed), a, "join({a}, Relaxed) should be {a}");
        assert_eq!(a.meet(&SeqCst), a, "meet({a}, SeqCst) should be {a}");
    }
}

// ===========================================================================
// Part 2: AccessKind classification — AtomicRmw semantics
// ===========================================================================

#[test]
fn test_access_kind_atomic_rmw_is_write() {
    let rmw = AccessKind::AtomicRmw(MemoryOrdering::AcqRel, AtomicRmwOp::Add);
    assert!(rmw.is_write(), "AtomicRmw is a write");
}

#[test]
fn test_access_kind_atomic_rmw_is_read() {
    let rmw = AccessKind::AtomicRmw(MemoryOrdering::AcqRel, AtomicRmwOp::Add);
    assert!(rmw.is_read(), "AtomicRmw is also a read");
}

#[test]
fn test_access_kind_atomic_rmw_is_not_non_atomic() {
    let rmw = AccessKind::AtomicRmw(MemoryOrdering::Relaxed, AtomicRmwOp::Xchg);
    assert!(!rmw.is_non_atomic(), "AtomicRmw is atomic");
}

#[test]
fn test_access_kind_atomic_rmw_ordering() {
    let rmw = AccessKind::AtomicRmw(MemoryOrdering::Release, AtomicRmwOp::Sub);
    assert_eq!(rmw.ordering(), Some(MemoryOrdering::Release));
}

#[test]
fn test_access_kind_atomic_rmw_serialization_roundtrip() {
    let rmw = AccessKind::AtomicRmw(MemoryOrdering::SeqCst, AtomicRmwOp::Nand);
    let json = serde_json::to_string(&rmw).expect("serialize");
    let round: AccessKind = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(round, rmw);
}

#[test]
fn test_access_kind_atomic_rmw_all_ops() {
    // Verify all RmwOp variants work with AccessKind.
    let ops = [
        AtomicRmwOp::Xchg,
        AtomicRmwOp::Add,
        AtomicRmwOp::Sub,
        AtomicRmwOp::And,
        AtomicRmwOp::Or,
        AtomicRmwOp::Xor,
        AtomicRmwOp::Nand,
        AtomicRmwOp::Min,
        AtomicRmwOp::Max,
    ];
    for op in ops {
        let kind = AccessKind::AtomicRmw(MemoryOrdering::Relaxed, op);
        assert!(kind.is_write());
        assert!(kind.is_read());
        assert!(!kind.is_non_atomic());
        assert_eq!(kind.ordering(), Some(MemoryOrdering::Relaxed));
    }
}

// ===========================================================================
// Part 3: MemoryOrdering at_least semantics (from data_race module)
// ===========================================================================

#[test]
fn test_memory_ordering_at_least_full_lattice() {
    // Complete truth table for is_at_least on MemoryOrdering.
    use MemoryOrdering::*;

    // SeqCst satisfies everything
    for o in [Relaxed, Acquire, Release, AcqRel, SeqCst] {
        assert!(SeqCst.is_at_least(o));
    }

    // AcqRel satisfies everything except SeqCst
    assert!(AcqRel.is_at_least(Relaxed));
    assert!(AcqRel.is_at_least(Acquire));
    assert!(AcqRel.is_at_least(Release));
    assert!(AcqRel.is_at_least(AcqRel));
    assert!(!AcqRel.is_at_least(SeqCst));

    // Acquire and Release are incomparable
    assert!(!Acquire.is_at_least(Release));
    assert!(!Release.is_at_least(Acquire));

    // Each satisfies itself and Relaxed only
    assert!(Acquire.is_at_least(Acquire));
    assert!(Acquire.is_at_least(Relaxed));
    assert!(!Acquire.is_at_least(AcqRel));
    assert!(!Acquire.is_at_least(SeqCst));

    assert!(Release.is_at_least(Release));
    assert!(Release.is_at_least(Relaxed));
    assert!(!Release.is_at_least(AcqRel));
    assert!(!Release.is_at_least(SeqCst));

    // Relaxed only satisfies Relaxed
    assert!(Relaxed.is_at_least(Relaxed));
    assert!(!Relaxed.is_at_least(Acquire));
    assert!(!Relaxed.is_at_least(Release));
    assert!(!Relaxed.is_at_least(AcqRel));
    assert!(!Relaxed.is_at_least(SeqCst));
}

// ===========================================================================
// Part 4: Data race integration — detect_potential_races
// ===========================================================================

fn make_access(var: &str, kind: AccessKind, thread: &str, hb: Vec<usize>) -> SharedAccess {
    SharedAccess {
        variable: var.to_string(),
        access_kind: kind,
        thread_id: thread.to_string(),
        happens_before: hb,
        span: SourceSpan::default(),
    }
}

/// Integration test: detect data race between non-atomic accesses.
#[test]
fn test_integration_race_non_atomic_write_read() {
    let accesses = vec![
        make_access("shared_counter", AccessKind::Write, "writer_thread", vec![]),
        make_access("shared_counter", AccessKind::Read, "reader_thread", vec![]),
    ];

    let races = detect_potential_races(&accesses);
    assert_eq!(races.len(), 1, "non-atomic write + read should race");
    assert_eq!(races[0].variable, "shared_counter");
    assert_eq!(races[0].thread_a, "writer_thread");
    assert_eq!(races[0].thread_b, "reader_thread");

    // Generate VCs and verify structure.
    let vcs = generate_race_vcs(&races, "increment_counter", &accesses);
    assert_eq!(vcs.len(), 1);
    match &vcs[0].kind {
        VcKind::DataRace { variable, thread_a, thread_b } => {
            assert_eq!(variable, "shared_counter");
            assert_eq!(thread_a, "writer_thread");
            assert_eq!(thread_b, "reader_thread");
        }
        other => panic!("expected DataRace VC, got: {other:?}"),
    }
}

/// Integration test: no race between properly-ordered atomics with HB chain.
#[test]
fn test_integration_no_race_release_acquire_pattern() {
    // Thread 1: write data (0), release-store flag (1)
    // Thread 2: acquire-load flag (2), read data (3)
    // HB chain: 0 -> 1 -> 2 -> 3 (via program order + release-acquire sync)
    let accesses = vec![
        make_access("data", AccessKind::Write, "producer", vec![]),
        make_access("flag", AccessKind::AtomicWrite(MemoryOrdering::Release), "producer", vec![0]),
        make_access("flag", AccessKind::AtomicRead(MemoryOrdering::Acquire), "consumer", vec![1]),
        make_access("data", AccessKind::Read, "consumer", vec![2]),
    ];

    let races = detect_potential_races(&accesses);
    let data_races: Vec<_> = races.iter().filter(|r| r.variable == "data").collect();
    assert!(data_races.is_empty(), "release-acquire synchronization prevents race on data");
}

/// Integration test: race when ordering is too weak (Relaxed instead of Release).
#[test]
fn test_integration_race_when_ordering_too_weak() {
    // Thread 1: write data (0), RELAXED-store flag (1) — should be Release!
    // Thread 2: acquire-load flag (2), read data (3)
    // No sync pair established because the store is Relaxed.
    let accesses = vec![
        make_access("data", AccessKind::Write, "producer", vec![]),
        make_access("flag", AccessKind::AtomicWrite(MemoryOrdering::Relaxed), "producer", vec![0]),
        make_access("flag", AccessKind::AtomicRead(MemoryOrdering::Acquire), "consumer", vec![]),
        make_access("data", AccessKind::Read, "consumer", vec![2]),
    ];

    let races = detect_potential_races(&accesses);
    let data_races: Vec<_> = races.iter().filter(|r| r.variable == "data").collect();
    assert_eq!(
        data_races.len(),
        1,
        "weak ordering (Relaxed instead of Release) should allow race on data"
    );
}

/// Integration test: AtomicRmw does not race with other atomics.
#[test]
fn test_integration_atomic_rmw_no_race_with_atomic() {
    let accesses = vec![
        make_access(
            "counter",
            AccessKind::AtomicRmw(MemoryOrdering::Relaxed, AtomicRmwOp::Add),
            "t1",
            vec![],
        ),
        make_access("counter", AccessKind::AtomicRead(MemoryOrdering::Relaxed), "t2", vec![]),
    ];

    let races = detect_potential_races(&accesses);
    assert!(races.is_empty(), "two atomic accesses (RMW + read) do not race");
}

/// Integration test: AtomicRmw DOES race with non-atomic access.
#[test]
fn test_integration_atomic_rmw_races_with_non_atomic() {
    let accesses = vec![
        make_access(
            "counter",
            AccessKind::AtomicRmw(MemoryOrdering::SeqCst, AtomicRmwOp::Add),
            "t1",
            vec![],
        ),
        make_access("counter", AccessKind::Read, "t2", vec![]),
    ];

    let races = detect_potential_races(&accesses);
    assert_eq!(races.len(), 1, "AtomicRmw + non-atomic read is a data race");
}

/// Integration test: three threads, multiple variables, multiple races.
#[test]
fn test_integration_multi_thread_multi_variable_races() {
    let accesses = vec![
        // Thread 1 writes x and y
        make_access("x", AccessKind::Write, "t1", vec![]),
        make_access("y", AccessKind::Write, "t1", vec![]),
        // Thread 2 reads x and writes y
        make_access("x", AccessKind::Read, "t2", vec![]),
        make_access("y", AccessKind::Write, "t2", vec![]),
        // Thread 3 reads y
        make_access("y", AccessKind::Read, "t3", vec![]),
    ];

    let races = detect_potential_races(&accesses);
    let x_races: Vec<_> = races.iter().filter(|r| r.variable == "x").collect();
    let y_races: Vec<_> = races.iter().filter(|r| r.variable == "y").collect();

    assert_eq!(x_races.len(), 1, "should detect 1 race on x (t1 write vs t2 read)");
    assert!(y_races.len() >= 2, "should detect races on y (t1 vs t2, t1 vs t3, t2 vs t3)");
}

// ===========================================================================
// Part 5: DataRaceDetector end-to-end
// ===========================================================================

/// Integration test: full detector workflow with sync preventing race.
#[test]
fn test_integration_detector_release_acquire_sync() {
    let mut det = DataRaceDetector::new();

    // Producer thread: write data, then release-store flag
    let w = det.add_access("data", AccessKind::Write, "producer", SourceSpan::default());
    let rel = det.add_access(
        "flag",
        AccessKind::AtomicWrite(MemoryOrdering::Release),
        "producer",
        SourceSpan::default(),
    );
    det.add_happens_before(w, rel);

    // Consumer thread: acquire-load flag, then read data
    let acq = det.add_access(
        "flag",
        AccessKind::AtomicRead(MemoryOrdering::Acquire),
        "consumer",
        SourceSpan::default(),
    );
    let r = det.add_access("data", AccessKind::Read, "consumer", SourceSpan::default());
    det.add_happens_before(acq, r);

    // Sync pair: release -> acquire
    det.add_sync_pair(rel, acq);

    let races = det.detect_races();
    let data_races: Vec<_> = races.iter().filter(|r| r.location == "data").collect();
    assert!(data_races.is_empty(), "release-acquire sync should prevent data race");
}

/// Integration test: detector finds race when sync is missing.
#[test]
fn test_integration_detector_missing_sync_race() {
    let mut det = DataRaceDetector::new();

    let w = det.add_access("data", AccessKind::Write, "producer", SourceSpan::default());
    let _rel = det.add_access(
        "flag",
        AccessKind::AtomicWrite(MemoryOrdering::Relaxed),
        "producer",
        SourceSpan::default(),
    );
    det.add_happens_before(w, _rel);

    let _acq = det.add_access(
        "flag",
        AccessKind::AtomicRead(MemoryOrdering::Acquire),
        "consumer",
        SourceSpan::default(),
    );
    let r = det.add_access("data", AccessKind::Read, "consumer", SourceSpan::default());
    det.add_happens_before(_acq, r);

    // NO sync pair — producer used Relaxed, not Release

    let races = det.detect_races();
    let data_races: Vec<_> = races.iter().filter(|r| r.location == "data").collect();
    assert_eq!(data_races.len(), 1, "missing sync should allow data race");
}

/// Integration test: describe() output on detected race.
#[test]
fn test_integration_race_condition_describe() {
    let mut det = DataRaceDetector::new();
    det.add_access("buffer", AccessKind::Write, "writer", SourceSpan::default());
    det.add_access("buffer", AccessKind::Read, "reader", SourceSpan::default());

    let races = det.detect_races();
    assert_eq!(races.len(), 1);

    let desc = races[0].describe();
    assert!(desc.contains("buffer"), "description should mention the variable");
    assert!(desc.contains("write"), "description should mention write");
    assert!(desc.contains("read"), "description should mention read");
    assert!(desc.contains("writer"), "description should mention writer thread");
    assert!(desc.contains("reader"), "description should mention reader thread");
}

// ===========================================================================
// Part 6: MemoryModelChecker — operation legality (L1-L5) integration
// ===========================================================================

fn make_op(
    op_kind: AtomicOpKind,
    ordering: AtomicOrdering,
    failure_ordering: Option<AtomicOrdering>,
) -> AtomicOperation {
    AtomicOperation {
        place: Place::local(0),
        dest: if op_kind.is_store() || op_kind.is_fence() { None } else { Some(Place::local(1)) },
        op_kind,
        ordering,
        failure_ordering,
        span: SourceSpan::default(),
    }
}

/// Integration test: exercise full legality checker with a realistic function's atomic ops.
///
/// Simulates a function that:
/// 1. Does a valid Acquire load (OK)
/// 2. Does a valid Release store (OK)
/// 3. Does a valid AcqRel CAS with Acquire failure (OK)
/// 4. Does a valid SeqCst fence (OK)
/// 5. Does a valid FetchAdd with Relaxed (OK)
///
/// Should produce zero VCs.
#[test]
fn test_integration_legality_all_valid_operations() {
    let ops = [
        make_op(AtomicOpKind::Load, AtomicOrdering::Acquire, None),
        make_op(AtomicOpKind::Store, AtomicOrdering::Release, None),
        make_op(
            AtomicOpKind::CompareExchange,
            AtomicOrdering::AcqRel,
            Some(AtomicOrdering::Acquire),
        ),
        make_op(AtomicOpKind::Fence, AtomicOrdering::SeqCst, None),
        make_op(AtomicOpKind::FetchAdd, AtomicOrdering::Relaxed, None),
    ];

    let vcs = MemoryModelChecker::check_operation_legality(&ops, "realistic_function");
    assert!(vcs.is_empty(), "all valid operations should produce 0 VCs, got {}", vcs.len());
}

/// Integration test: function with mixed valid and invalid operations.
///
/// Simulates a buggy function that violates L1, L2, and L5.
#[test]
fn test_integration_legality_mixed_violations() {
    let ops = [
        make_op(AtomicOpKind::Load, AtomicOrdering::Release, None), // L1 violation
        make_op(AtomicOpKind::Store, AtomicOrdering::Acquire, None), // L2 violation
        make_op(AtomicOpKind::Load, AtomicOrdering::Acquire, None), // valid
        make_op(AtomicOpKind::Fence, AtomicOrdering::Relaxed, None), // L5 violation
        make_op(AtomicOpKind::Store, AtomicOrdering::Release, None), // valid
    ];

    let vcs = MemoryModelChecker::check_operation_legality(&ops, "buggy_function");
    assert_eq!(vcs.len(), 3, "should detect exactly 3 violations (L1, L2, L5)");

    // All VCs should be InsufficientOrdering
    for vc in &vcs {
        assert!(
            matches!(vc.kind, VcKind::InsufficientOrdering { .. }),
            "VC should be InsufficientOrdering"
        );
        assert_eq!(vc.function, "buggy_function");
    }
}

/// Integration test: CAS with double violation (L3 + L4).
#[test]
fn test_integration_legality_cas_double_violation() {
    // success=Relaxed, failure=Release: L3 (Release forbidden) + L4 (failure > success)
    let ops = [make_op(
        AtomicOpKind::CompareExchange,
        AtomicOrdering::Relaxed,
        Some(AtomicOrdering::Release),
    )];

    let vcs = MemoryModelChecker::check_operation_legality(&ops, "cas_double_bug");
    assert!(vcs.len() >= 2, "should fire both L3 and L4, got {} VCs", vcs.len());

    let vc_texts: Vec<String> = vcs.iter().map(|vc| vc.kind.to_string()).collect();
    assert!(vc_texts.iter().any(|t| t.contains("L3")), "should have L3 violation");
    assert!(vc_texts.iter().any(|t| t.contains("L4")), "should have L4 violation");
}

/// Integration test: CompareExchangeWeak follows the same rules.
#[test]
fn test_integration_legality_cas_weak_same_rules() {
    let ops = [make_op(
        AtomicOpKind::CompareExchangeWeak,
        AtomicOrdering::SeqCst,
        Some(AtomicOrdering::Release),
    )];

    let vcs = MemoryModelChecker::check_operation_legality(&ops, "weak_cas");
    assert!(
        vcs.iter().any(|vc| vc.kind.to_string().contains("L3")),
        "CompareExchangeWeak should also trigger L3"
    );
}

/// Integration test: RMW operations are NOT affected by L1 or L2.
#[test]
fn test_integration_legality_rmw_accepts_all_orderings() {
    let orderings = [
        AtomicOrdering::Relaxed,
        AtomicOrdering::Acquire,
        AtomicOrdering::Release,
        AtomicOrdering::AcqRel,
        AtomicOrdering::SeqCst,
    ];
    let rmw_kinds = [
        AtomicOpKind::FetchAdd,
        AtomicOpKind::FetchSub,
        AtomicOpKind::FetchAnd,
        AtomicOpKind::FetchOr,
        AtomicOpKind::FetchXor,
        AtomicOpKind::FetchNand,
        AtomicOpKind::FetchMin,
        AtomicOpKind::FetchMax,
        AtomicOpKind::Exchange,
    ];

    for kind in rmw_kinds {
        for ordering in orderings {
            let ops = [make_op(kind, ordering, None)];
            let vcs = MemoryModelChecker::check_operation_legality(&ops, "rmw_test");
            assert!(
                vcs.is_empty(),
                "RMW op {kind} with ordering {ordering} should be valid, got {} VCs",
                vcs.len()
            );
        }
    }
}

/// Integration test: compiler_fence with Relaxed violates L5.
#[test]
fn test_integration_legality_compiler_fence_relaxed() {
    let ops = [make_op(AtomicOpKind::CompilerFence, AtomicOrdering::Relaxed, None)];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "bad_cfence");
    assert_eq!(vcs.len(), 1, "compiler_fence with Relaxed should violate L5");
    assert!(vcs[0].kind.to_string().contains("L5"));
}

/// Integration test: fence with all valid orderings.
#[test]
fn test_integration_legality_fence_valid_orderings() {
    for ordering in [
        AtomicOrdering::Acquire,
        AtomicOrdering::Release,
        AtomicOrdering::AcqRel,
        AtomicOrdering::SeqCst,
    ] {
        let ops = [make_op(AtomicOpKind::Fence, ordering, None)];
        let vcs = MemoryModelChecker::check_operation_legality(&ops, "fence_test");
        assert!(vcs.is_empty(), "fence with {ordering} should be valid");
    }
}

// ===========================================================================
// Part 7: Ordering sufficiency + generate_ordering_vcs integration
// ===========================================================================

#[test]
fn test_integration_ordering_sufficiency_and_vc_generation() {
    // A function where some atomic accesses have insufficient ordering.
    let accesses = vec![
        make_access("flag", AccessKind::AtomicRead(MemoryOrdering::Relaxed), "t1", vec![]),
        make_access("counter", AccessKind::AtomicWrite(MemoryOrdering::SeqCst), "t1", vec![]),
        make_access("data", AccessKind::AtomicRead(MemoryOrdering::Acquire), "t2", vec![]),
    ];

    // Requirements: flag needs Acquire, counter needs Release (SeqCst >= Release, OK),
    // data needs SeqCst (Acquire < SeqCst, violation).
    let requirements = vec![
        (0, MemoryOrdering::Acquire), // Relaxed < Acquire => VC
        (1, MemoryOrdering::Release), // SeqCst >= Release => no VC
        (2, MemoryOrdering::SeqCst),  // Acquire < SeqCst => VC
    ];

    // Verify individual checks
    assert!(!check_ordering_sufficient(&accesses[0], MemoryOrdering::Acquire));
    assert!(check_ordering_sufficient(&accesses[1], MemoryOrdering::Release));
    assert!(!check_ordering_sufficient(&accesses[2], MemoryOrdering::SeqCst));

    // Generate VCs
    let vcs = generate_ordering_vcs(&accesses, &requirements, "mixed_fn");
    assert_eq!(vcs.len(), 2, "should generate 2 ordering VCs");

    // Both should be InsufficientOrdering
    for vc in &vcs {
        assert!(matches!(vc.kind, VcKind::InsufficientOrdering { .. }));
        assert_eq!(vc.function, "mixed_fn");
    }
}

// ===========================================================================
// Part 8: MemoryModelChecker full workflow integration
// ===========================================================================

#[test]
fn test_integration_checker_full_workflow_sound() {
    let mut log = AtomicAccessLog::new();
    log.record(AtomicAccessEntry {
        location: "ready".to_string(),
        access_kind: AccessKind::AtomicWrite(MemoryOrdering::Release),
        thread_id: "producer".to_string(),
        span: SourceSpan::default(),
    });
    log.record(AtomicAccessEntry {
        location: "ready".to_string(),
        access_kind: AccessKind::AtomicRead(MemoryOrdering::Acquire),
        thread_id: "consumer".to_string(),
        span: SourceSpan::default(),
    });

    let mut hb = HappensBefore::new(2);
    hb.add_synchronizes_with(0, 1);

    let checker = MemoryModelChecker::new(log, hb);
    let result = checker.check();

    assert!(result.is_sound, "properly-ordered atomics should be sound");
    assert!(result.races.is_empty());
    assert!(result.ordering_violations.is_empty());

    let vcs = checker.generate_vcs("producer_consumer");
    assert!(vcs.is_empty(), "sound system should generate no VCs");
}

#[test]
fn test_integration_checker_full_workflow_unsound() {
    let mut log = AtomicAccessLog::new();
    log.record(AtomicAccessEntry {
        location: "flag".to_string(),
        access_kind: AccessKind::AtomicRead(MemoryOrdering::Relaxed),
        thread_id: "spinner".to_string(),
        span: SourceSpan::default(),
    });

    let hb = HappensBefore::new(1);
    let mut checker = MemoryModelChecker::new(log, hb);
    checker.require_ordering(OrderingRequirement {
        access_index: 0,
        required: MemoryOrdering::Acquire,
        reason: "spin loop needs Acquire for visibility".to_string(),
    });

    let result = checker.check();
    assert!(!result.is_sound, "Relaxed load where Acquire needed should be unsound");
    assert_eq!(result.ordering_violations.len(), 1);
    assert_eq!(result.ordering_violations[0].actual, MemoryOrdering::Relaxed);
    assert_eq!(result.ordering_violations[0].required, MemoryOrdering::Acquire);

    let vcs = checker.generate_vcs("spin_wait");
    assert_eq!(vcs.len(), 1, "should generate 1 VC for the ordering violation");
    assert!(matches!(&vcs[0].kind, VcKind::InsufficientOrdering { .. }));
}

// ===========================================================================
// Part 9: HappensBefore graph integration
// ===========================================================================

#[test]
fn test_integration_hb_graph_diamond_pattern() {
    // Diamond pattern: 0 -> 1, 0 -> 2, 1 -> 3, 2 -> 3
    // Both 1 and 2 should HB 3. 1 and 2 are unordered.
    let mut hb = HappensBefore::new(4);
    hb.add_edge(0, 1);
    hb.add_edge(0, 2);
    hb.add_edge(1, 3);
    hb.add_edge(2, 3);

    assert!(hb.happens_before(0, 3), "0 should HB 3 via both paths");
    assert!(hb.happens_before(1, 3));
    assert!(hb.happens_before(2, 3));
    assert!(hb.are_ordered(1, 3));
    assert!(hb.are_ordered(2, 3));

    // 1 and 2 are NOT ordered relative to each other
    assert!(!hb.are_ordered(1, 2), "1 and 2 should be concurrent");
}

#[test]
fn test_integration_hb_long_chain() {
    // Linear chain: 0 -> 1 -> 2 -> ... -> 9
    let n = 10;
    let mut hb = HappensBefore::new(n);
    for i in 0..n - 1 {
        hb.add_edge(i, i + 1);
    }

    // First should HB last
    assert!(hb.happens_before(0, n - 1));
    // Last should NOT HB first
    assert!(!hb.happens_before(n - 1, 0));
    // Every earlier event should HB every later event
    for i in 0..n {
        for j in i..n {
            assert!(hb.happens_before(i, j), "event {i} should HB event {j}");
        }
    }
}
