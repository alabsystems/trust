// trust-integration-tests/tests/concurrency_e2e.rs: End-to-end concurrency verification
//
// Exercises the full concurrency verification pipeline:
//   DataRaceDetector -> MemoryModelChecker -> VC generation -> Router
// plus Send/Sync checking and HappensBeforeGraph validation.
//
// Part of #620: Phase 2.5 end-to-end concurrency verification test
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use trust_types::{BlockId, ConcurrencyPoint, HappensBeforeEdgeKind, SourceSpan, VcKind};
use trust_vcgen::data_race::{
    AccessKind, MemoryOrdering, SharedAccess, detect_potential_races, generate_race_vcs,
};
use trust_vcgen::memory_ordering::{
    AtomicAccessEntry, AtomicAccessLog, DataRaceDetector, HappensBefore, HappensBeforeGraph,
    MemoryModelChecker,
};
use trust_vcgen::send_sync::{
    MutexEvent as DiagnosticMutexEvent, SendSyncChecker, SharedAccess as DiagnosticSharedAccess,
    TypeInfo, ViolationKind, generate_thread_safety_vcs,
};

// ---------------------------------------------------------------------------
// 1. Claimed release-acquire pattern: race candidates remain
// ---------------------------------------------------------------------------

/// Simulates a producer-consumer pattern with a caller-claimed release-acquire
/// chain. The producer writes data, then release-stores a flag. The consumer
/// acquire-loads the flag, then reads data.
///
/// Expected: the authored HB list cannot suppress the data race candidate.
#[test]
fn test_claimed_release_acquire_still_produces_data_race_candidate() {
    // Build the access trace: producer writes data, release-stores flag;
    // consumer acquire-loads flag, reads data.
    let accesses = vec![
        // Producer thread
        SharedAccess {
            variable: "data".to_string(),
            access_kind: AccessKind::Write,
            thread_id: "producer".to_string(),
            happens_before: vec![],
            span: SourceSpan::default(),
        },
        SharedAccess {
            variable: "flag".to_string(),
            access_kind: AccessKind::AtomicWrite(MemoryOrdering::Release),
            thread_id: "producer".to_string(),
            happens_before: vec![0], // program order: data write -> flag store
            span: SourceSpan::default(),
        },
        // Consumer thread
        SharedAccess {
            variable: "flag".to_string(),
            access_kind: AccessKind::AtomicRead(MemoryOrdering::Acquire),
            thread_id: "consumer".to_string(),
            happens_before: vec![1], // release-acquire sync: flag store -> flag load
            span: SourceSpan::default(),
        },
        SharedAccess {
            variable: "data".to_string(),
            access_kind: AccessKind::Read,
            thread_id: "consumer".to_string(),
            happens_before: vec![2], // program order: flag load -> data read
            span: SourceSpan::default(),
        },
    ];

    // The authored path lacks runtime event identity and a read-from witness.
    let races = detect_potential_races(&accesses);
    let data_pair = races
        .iter()
        .position(|race| (race.first, race.second) == (0, 3))
        .expect("authored HB cannot hide the data write/read candidate");

    // The diagnostic VC mirrors that candidate; it is not a proof verdict.
    let vcs = generate_race_vcs(&races, "producer_consumer", &accesses);
    assert_eq!(vcs.len(), races.len());
    assert!(matches!(
        &vcs[data_pair].kind,
        VcKind::UnsupportedMir { kind, detail }
            if kind == "DataRaceCandidate"
                && detail.contains("data")
                && detail.contains("producer")
                && detail.contains("consumer")
    ));
}

// ---------------------------------------------------------------------------
// 2. Buggy relaxed-only pattern: unsupported race candidate retained
// ---------------------------------------------------------------------------

/// Simulates a broken producer-consumer where the flag uses Relaxed ordering
/// instead of Release/Acquire. The non-atomic data access is unprotected.
///
/// Expected: an unsupported data-race candidate with diagnostic labels.
#[test]
fn test_buggy_relaxed_pattern_produces_data_race_vcs() {
    let accesses = vec![
        // Producer: write data, then relaxed-store flag (BUG: should be Release)
        SharedAccess {
            variable: "data".to_string(),
            access_kind: AccessKind::Write,
            thread_id: "producer".to_string(),
            happens_before: vec![],
            span: SourceSpan::default(),
        },
        SharedAccess {
            variable: "flag".to_string(),
            access_kind: AccessKind::AtomicWrite(MemoryOrdering::Relaxed),
            thread_id: "producer".to_string(),
            happens_before: vec![0], // program order within producer
            span: SourceSpan::default(),
        },
        // Consumer: relaxed-load flag (BUG: should be Acquire), then read data
        SharedAccess {
            variable: "flag".to_string(),
            access_kind: AccessKind::AtomicRead(MemoryOrdering::Relaxed),
            thread_id: "consumer".to_string(),
            happens_before: vec![], // NO sync edge from producer -- this is the bug
            span: SourceSpan::default(),
        },
        SharedAccess {
            variable: "data".to_string(),
            access_kind: AccessKind::Read,
            thread_id: "consumer".to_string(),
            happens_before: vec![2], // program order within consumer
            span: SourceSpan::default(),
        },
    ];

    // Detect races -- the data write/read remains one of several may-alias pairs.
    let races = detect_potential_races(&accesses);
    let data_pair = races
        .iter()
        .position(|race| (race.first, race.second) == (0, 3))
        .expect("the data write/read must remain a candidate");

    // Verify diagnostic labels on the actual data pair.
    assert_eq!(races[data_pair].thread_a, "producer");
    assert_eq!(races[data_pair].thread_b, "consumer");
    assert_eq!(races[data_pair].variable, "data");

    // Generate VCs and verify this candidate's diagnostic metadata.
    let vcs = generate_race_vcs(&races, "broken_producer_consumer", &accesses);
    assert_eq!(vcs.len(), races.len());
    assert_eq!(vcs[data_pair].function, "broken_producer_consumer");

    // Verify the unsupported candidate carries the diagnostic labels.
    match &vcs[data_pair].kind {
        VcKind::UnsupportedMir { kind, detail } => {
            assert_eq!(kind, "DataRaceCandidate");
            assert!(detail.contains("data"));
            assert!(detail.contains("producer"));
            assert!(detail.contains("consumer"));
        }
        other => panic!("expected unsupported race candidate, got: {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// 3. Send/Sync bound checking on thread-spawned closures
// ---------------------------------------------------------------------------

/// Verifies that the Send/Sync checker detects violations when a type
/// claiming Send contains a !Send field (e.g., Rc<T> captured in a closure
/// sent to another thread).
#[test]
fn test_send_sync_checking_detects_violations() {
    let mut checker = SendSyncChecker::new();

    // Simulate a closure that captures Rc<i32> -- Rc is !Send, !Sync
    let rc_field = TypeInfo::new("Rc<i32>", false, false);
    let mut closure_type = TypeInfo::new("ClosureEnv", true, false);
    closure_type.fields.push(rc_field);
    checker.register_type(closure_type);

    let violations = checker.check_all();
    assert_eq!(
        violations.len(),
        1,
        "Should detect 1 violation: ClosureEnv claims Send but has !Send Rc<i32>"
    );
    assert_eq!(violations[0].kind, ViolationKind::UnsafeSend);
    assert!(violations[0].message.contains("Rc<i32>"));
    assert!(violations[0].message.contains("ClosureEnv"));

    // Generate VCs from violations
    let vcs = checker.to_vcs("spawn_with_rc");
    assert_eq!(vcs.len(), 1);
    assert_eq!(vcs[0].function, "spawn_with_rc");
}

/// Verifies that types with interior mutability and !Sync are flagged.
#[test]
fn test_send_sync_interior_mutability_requires_sync() {
    let mut checker = SendSyncChecker::new();

    // Cell<T> has interior mutability but is !Sync
    let mut cell_type = TypeInfo::new("Cell<i32>", true, false);
    cell_type.has_interior_mutability = true;
    checker.register_type(cell_type);

    let violations = checker.check_all();
    assert!(
        violations.iter().any(|v| v.kind == ViolationKind::UnprotectedInteriorMutability),
        "Should detect interior mutability without Sync"
    );
}

/// Verifies that properly Send+Sync types produce no violations.
#[test]
fn test_send_sync_safe_type_no_violations() {
    let mut checker = SendSyncChecker::new();

    // Arc<Mutex<i32>> is Send+Sync with all fields also Send+Sync
    let inner = TypeInfo::new("i32", true, true);
    let mut arc_type = TypeInfo::new("Arc<Mutex<i32>>", true, true);
    arc_type.fields.push(inner);
    checker.register_type(arc_type);

    let violations = checker.check_all();
    assert!(violations.is_empty(), "Arc<Mutex<i32>> should produce no Send/Sync violations");
}

// ---------------------------------------------------------------------------
// 4. Full pipeline: DataRaceDetector -> MemoryModelChecker -> VCs -> Router
// ---------------------------------------------------------------------------

/// End-to-end pipeline test: build a concurrent scenario, run through the
/// memory_ordering module's DataRaceDetector and MemoryModelChecker, generate
/// VCs, and route them through the Router.
#[test]
fn test_full_pipeline_detector_to_checker_to_router() {
    // Phase 1: Use DataRaceDetector for the access-level race analysis
    let mut detector = DataRaceDetector::new();

    // Producer thread: write data, then release-store flag
    let write_data =
        detector.add_access("shared_buf", AccessKind::Write, "producer", SourceSpan::default());
    let release_flag = detector.add_access(
        "ready_flag",
        AccessKind::AtomicWrite(MemoryOrdering::Release),
        "producer",
        SourceSpan::default(),
    );
    detector.add_happens_before(write_data, release_flag);

    // Consumer thread: acquire-load flag, then read data
    let acquire_flag = detector.add_access(
        "ready_flag",
        AccessKind::AtomicRead(MemoryOrdering::Acquire),
        "consumer",
        SourceSpan::default(),
    );
    let read_data =
        detector.add_access("shared_buf", AccessKind::Read, "consumer", SourceSpan::default());
    detector.add_happens_before(acquire_flag, read_data);

    // Establish release-acquire sync
    detector.add_sync_pair(release_flag, acquire_flag);

    // Check: the caller-claimed sync path does not erase the data pair.
    let races = detector.detect_races();
    assert!(
        races
            .iter()
            .any(|race| { (race.first_access, race.second_access) == (write_data, read_data) })
    );

    // Phase 2: Use MemoryModelChecker for ordering analysis
    let mut log = AtomicAccessLog::new();
    let rel_idx = log.record(AtomicAccessEntry {
        location: "ready_flag".to_string(),
        access_kind: AccessKind::AtomicWrite(MemoryOrdering::Release),
        thread_id: "producer".to_string(),
        span: SourceSpan::default(),
    });
    let acq_idx = log.record(AtomicAccessEntry {
        location: "ready_flag".to_string(),
        access_kind: AccessKind::AtomicRead(MemoryOrdering::Acquire),
        thread_id: "consumer".to_string(),
        span: SourceSpan::default(),
    });

    let mut hb = HappensBefore::new(2);
    hb.add_synchronizes_with(rel_idx, acq_idx);

    let checker = MemoryModelChecker::new(log, hb);

    // This atomic-only check does not decide the non-atomic data race candidate.
    let result = checker.check();
    assert!(result.is_sound, "the atomic-only ordering check should pass");
    assert!(result.races.is_empty());
    assert!(result.ordering_violations.is_empty());

    // This checker has no atomic ordering violation VC.
    let vcs = checker.generate_vcs("producer_consumer");
    assert!(vcs.is_empty(), "the atomic-only checker should produce no VCs");

    // Phase 3: carry the retained data candidate to the router. The emitted
    // formula is still a placeholder, so routing must not turn it into proof.
    let candidates = detect_potential_races(detector.accesses());
    let data_pair = candidates
        .iter()
        .position(|pair| (pair.first, pair.second) == (write_data, read_data))
        .expect("the claimed sync path cannot erase the data candidate");
    let race_vcs = generate_race_vcs(&candidates, "producer_consumer", detector.accesses());
    assert_eq!(race_vcs.len(), candidates.len());
    let router = trust_router::Router::new();
    let results = router.verify_all(&race_vcs);
    assert_eq!(results.len(), race_vcs.len());
    assert!(matches!(&results[data_pair].0.kind, VcKind::UnsupportedMir { .. }));
    assert!(
        matches!(&results[data_pair].1, trust_types::VerificationResult::Unknown { .. }),
        "an unmodeled data-race candidate must be Unknown"
    );
}

#[test]
fn test_send_sync_forged_labels_candidate_reaches_router_without_proof() {
    let accesses = [
        DiagnosticSharedAccess {
            location: "left".into(),
            thread: "worker".into(),
            is_write: true,
            span: SourceSpan::default(),
        },
        DiagnosticSharedAccess {
            location: "right".into(),
            thread: "worker".into(),
            is_write: false,
            span: SourceSpan::default(),
        },
    ];
    let mutex_events = [
        DiagnosticMutexEvent {
            mutex_id: "left".into(),
            thread: "worker".into(),
            is_acquire: true,
            span: SourceSpan::default(),
        },
        DiagnosticMutexEvent {
            mutex_id: "left".into(),
            thread: "worker".into(),
            is_acquire: false,
            span: SourceSpan::default(),
        },
    ];

    let vcs = generate_thread_safety_vcs("f", &accesses, &mutex_events, &[]);
    assert_eq!(vcs.len(), 1, "forged labels and lock claims cannot hide the candidate");
    let results = trust_router::Router::new().verify_all(&vcs);
    assert_eq!(results.len(), 1);
    assert!(
        matches!(&results[0].1, trust_types::VerificationResult::Unknown { .. }),
        "an unmodeled send_sync race candidate must be Unknown"
    );
}

/// End-to-end pipeline with a buggy scenario that produces VCs routed to the solver.
#[test]
fn test_full_pipeline_buggy_ordering_produces_routed_vcs() {
    // Build a checker with an ordering violation: Relaxed load where Acquire needed
    let mut log = AtomicAccessLog::new();
    log.record(AtomicAccessEntry {
        location: "flag".to_string(),
        access_kind: AccessKind::AtomicRead(MemoryOrdering::Relaxed),
        thread_id: "consumer".to_string(),
        span: SourceSpan::default(),
    });

    let hb = HappensBefore::new(1);
    let mut checker = MemoryModelChecker::new(log, hb);
    checker.require_ordering(trust_vcgen::memory_ordering::OrderingRequirement {
        access_index: 0,
        required: MemoryOrdering::Acquire,
        reason: "must synchronize with producer's release store".to_string(),
    });

    // Check should detect the violation
    let result = checker.check();
    assert!(!result.is_sound, "insufficient ordering should not be sound");
    assert_eq!(result.ordering_violations.len(), 1);

    // Generate VCs
    let vcs = checker.generate_vcs("buggy_consumer");
    assert_eq!(vcs.len(), 1);
    match &vcs[0].kind {
        VcKind::InsufficientOrdering { variable, actual, required } => {
            assert_eq!(variable, "flag");
            assert_eq!(actual, "Relaxed");
            assert_eq!(required, "Acquire");
        }
        other => panic!("expected InsufficientOrdering, got: {other:?}"),
    }

    // Route through the Router
    let router = trust_router::Router::new();
    let results = router.verify_all(&vcs);
    assert_eq!(results.len(), 1);
    // ConstantFolderBackend returns a result for the VC
    let (ref vc, ref _result) = results[0];
    assert_eq!(vc.function, "buggy_consumer");
}

// ---------------------------------------------------------------------------
// 5. HappensBeforeGraph: spawn/join edges validate concurrency ordering
// ---------------------------------------------------------------------------

/// Builds a HappensBeforeGraph with spawn and join edges, verifying that
/// transitivity correctly identifies which program points are ordered and
/// which are concurrent.
#[test]
fn test_happens_before_graph_spawn_join_concurrency() {
    let mut graph = HappensBeforeGraph::new();

    // Main thread: before_spawn -> spawn -> after_spawn -> join -> after_join
    let before_spawn = ConcurrencyPoint::new("main_fn", BlockId(0), "main");
    let spawn_site = ConcurrencyPoint::new("main_fn", BlockId(1), "main");
    let after_spawn = ConcurrencyPoint::new("main_fn", BlockId(2), "main");
    let join_site = ConcurrencyPoint::new("main_fn", BlockId(3), "main");
    let after_join = ConcurrencyPoint::new("main_fn", BlockId(4), "main");

    // Child thread: child_entry -> child_work -> child_exit
    let child_entry = ConcurrencyPoint::new("worker_fn", BlockId(0), "child");
    let child_work = ConcurrencyPoint::new("worker_fn", BlockId(1), "child");
    let child_exit = ConcurrencyPoint::new("worker_fn", BlockId(2), "child");

    // Add all nodes
    for p in [
        &before_spawn,
        &spawn_site,
        &after_spawn,
        &join_site,
        &after_join,
        &child_entry,
        &child_work,
        &child_exit,
    ] {
        graph.add_node(p.clone());
    }

    // Main thread program order
    graph.add_edge(&before_spawn, &spawn_site, HappensBeforeEdgeKind::ProgramOrder);
    graph.add_edge(&spawn_site, &after_spawn, HappensBeforeEdgeKind::ProgramOrder);
    graph.add_edge(&after_spawn, &join_site, HappensBeforeEdgeKind::ProgramOrder);
    graph.add_edge(&join_site, &after_join, HappensBeforeEdgeKind::ProgramOrder);

    // Child thread program order
    graph.add_edge(&child_entry, &child_work, HappensBeforeEdgeKind::ProgramOrder);
    graph.add_edge(&child_work, &child_exit, HappensBeforeEdgeKind::ProgramOrder);

    // Spawn edge: spawn_site -> child_entry
    graph.add_edge(&spawn_site, &child_entry, HappensBeforeEdgeKind::Spawn);

    // Join edge: child_exit -> join_site
    graph.add_edge(&child_exit, &join_site, HappensBeforeEdgeKind::Join);

    // --- Verify ordered pairs ---

    // Spawn establishes HB
    assert!(
        graph.happens_before(&spawn_site, &child_entry),
        "spawn site should happen-before child entry"
    );
    assert!(
        graph.happens_before(&before_spawn, &child_entry),
        "before_spawn should transitively HB child_entry"
    );

    // Join establishes HB
    assert!(
        graph.happens_before(&child_exit, &join_site),
        "child exit should happen-before join site"
    );
    assert!(
        graph.happens_before(&child_work, &after_join),
        "child_work should transitively HB after_join via child_exit -> join"
    );

    // Full transitive chain: before_spawn -> ... -> child_exit -> join -> after_join
    assert!(
        graph.happens_before(&before_spawn, &after_join),
        "before_spawn should transitively HB after_join"
    );

    // --- Verify concurrent pairs (NOT ordered) ---

    // Main thread work after spawn vs child thread work: concurrent
    assert!(
        !graph.are_ordered(&after_spawn, &child_work),
        "after_spawn and child_work should be concurrent (not ordered)"
    );
    assert!(
        !graph.are_ordered(&after_spawn, &child_entry),
        "after_spawn and child_entry should be concurrent"
    );

    // --- Verify edge kinds ---
    assert_eq!(graph.edge_kind(&spawn_site, &child_entry), Some(HappensBeforeEdgeKind::Spawn));
    assert_eq!(graph.edge_kind(&child_exit, &join_site), Some(HappensBeforeEdgeKind::Join));
    assert_eq!(
        graph.edge_kind(&before_spawn, &spawn_site),
        Some(HappensBeforeEdgeKind::ProgramOrder)
    );
}

/// Verifies that release-acquire synchronization edges in the HB graph
/// establish ordering between threads that are otherwise concurrent.
#[test]
fn test_happens_before_graph_release_acquire_sync() {
    let mut graph = HappensBeforeGraph::new();

    // Thread 1: write_data -> release_store
    let t1_write = ConcurrencyPoint::new("fn_a", BlockId(0), "t1");
    let t1_release = ConcurrencyPoint::new("fn_a", BlockId(1), "t1");

    // Thread 2: acquire_load -> read_data
    let t2_acquire = ConcurrencyPoint::new("fn_b", BlockId(0), "t2");
    let t2_read = ConcurrencyPoint::new("fn_b", BlockId(1), "t2");

    for p in [&t1_write, &t1_release, &t2_acquire, &t2_read] {
        graph.add_node(p.clone());
    }

    // Program order within each thread
    graph.add_edge(&t1_write, &t1_release, HappensBeforeEdgeKind::ProgramOrder);
    graph.add_edge(&t2_acquire, &t2_read, HappensBeforeEdgeKind::ProgramOrder);

    // Release-acquire sync edge
    graph.add_edge(&t1_release, &t2_acquire, HappensBeforeEdgeKind::SyncWith);

    // Transitive: t1_write -> t1_release -> t2_acquire -> t2_read
    assert!(
        graph.happens_before(&t1_write, &t2_read),
        "t1_write should HB t2_read via release-acquire sync"
    );
    assert!(graph.happens_before(&t1_release, &t2_acquire), "release should HB acquire");
    assert!(!graph.happens_before(&t2_read, &t1_write), "reverse should not hold");

    // Edge kind verification
    assert_eq!(graph.edge_kind(&t1_release, &t2_acquire), Some(HappensBeforeEdgeKind::SyncWith));
}

// ---------------------------------------------------------------------------
// 7. Pipeline integration: unsupported race candidate through Router -> Report
// ---------------------------------------------------------------------------

/// Helper to construct a VC with a given kind and function name.
fn make_concurrency_vc(kind: VcKind, function: &str) -> trust_types::VerificationCondition {
    trust_types::VerificationCondition {
        kind,
        function: function.into(),
        location: SourceSpan::default(),
        formula: trust_types::Formula::Bool(false),
        contract_metadata: None,
        obligation: None,
    }
}

/// Routes a generated potential-race candidate through every public Router
/// entrypoint and checks that the report retains an Unknown L0 row.
#[test]
fn test_data_race_candidate_is_unknown_through_router_and_report() {
    use trust_types::ProofLevel;

    let accesses = [
        SharedAccess {
            variable: "shared_counter".into(),
            access_kind: AccessKind::Write,
            thread_id: "writer".into(),
            happens_before: vec![],
            span: SourceSpan::default(),
        },
        SharedAccess {
            variable: "shared_counter".into(),
            access_kind: AccessKind::Read,
            thread_id: "reader".into(),
            happens_before: vec![],
            span: SourceSpan::default(),
        },
    ];
    let races = detect_potential_races(&accesses);
    let vcs = generate_race_vcs(&races, "concurrent_counter", &accesses);
    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];

    assert_eq!(vc.kind.proof_level(), ProofLevel::L0Safety);
    assert!(matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. } if kind == "DataRaceCandidate"));

    let desc = vc.kind.description();
    assert!(desc.contains("shared_counter"), "description should mention the variable: {desc}");
    assert!(desc.contains("writer"), "description should mention thread_a: {desc}");
    assert!(desc.contains("reader"), "description should mention thread_b: {desc}");

    let router = trust_router::Router::new();
    assert!(router.backend_plan(vc).is_empty());
    assert!(matches!(router.verify_one(vc), trust_types::VerificationResult::Unknown { .. }));
    let results = router.verify_all(&vcs);
    assert!(matches!(&results[0].1, trust_types::VerificationResult::Unknown { .. }));

    let report = trust_report::build_json_report("concurrency_crate", &results);

    assert_eq!(report.summary.functions_analyzed, 1);
    assert_eq!(report.summary.total_obligations, 1);
    assert_eq!(report.summary.total_unknown, 1);
    assert_eq!(report.functions[0].function, "concurrent_counter");

    let ob = &report.functions[0].obligations[0];
    assert!(
        ob.description.contains("shared_counter"),
        "report obligation should describe the candidate's location label"
    );
    assert_eq!(ob.proof_level, ProofLevel::L0Safety);
}

// ---------------------------------------------------------------------------
// 8. Pipeline integration: InsufficientOrdering VCs through Router -> Report
// ---------------------------------------------------------------------------

/// Routes a hand-constructed InsufficientOrdering VC through the Router and verifies:
/// - the Router refuses it as `Unknown` (v6/D2) even though its hardcoded
///   `false` formula is trivially "provable": before the 2026-09-30 gate the
///   constant folder minted `Proved` here, a green verdict about a cross-thread
///   ordering claim that no memory model backed
/// - The report contains the correct VcKind description
/// - proof_level is L1Functional
#[test]
fn test_insufficient_ordering_vc_pipeline_through_router_and_report() {
    use trust_types::ProofLevel;

    let vc = make_concurrency_vc(
        VcKind::InsufficientOrdering {
            variable: "ready_flag".to_string(),
            actual: "Relaxed".to_string(),
            required: "Acquire".to_string(),
        },
        "broken_consumer",
    );

    // Verify proof level classification
    assert_eq!(
        vc.kind.proof_level(),
        ProofLevel::L1Functional,
        "InsufficientOrdering should be L1 Functional"
    );

    // Verify description content
    let desc = vc.kind.description();
    assert!(desc.contains("ready_flag"), "description should mention the variable: {desc}");
    assert!(desc.contains("Relaxed"), "description should mention actual ordering: {desc}");
    assert!(desc.contains("Acquire"), "description should mention required ordering: {desc}");

    // Route through Router (ConstantFolderBackend): refused before dispatch.
    let router = trust_router::Router::new();
    let result = router.verify_one(&vc);
    assert!(
        matches!(&result, trust_types::VerificationResult::Unknown { reason, .. }
            if reason.contains("memory-ordering VC unsupported")),
        "an ordering VC without a memory model must fail closed, got {result:?}"
    );

    // Build report and verify structure
    let results = vec![(vc.clone(), result)];
    let report = trust_report::build_json_report("ordering_crate", &results);

    assert_eq!(report.summary.functions_analyzed, 1);
    assert_eq!(report.summary.total_obligations, 1);
    assert_eq!(report.functions[0].function, "broken_consumer");

    // Obligation description should contain the ordering details
    let ob = &report.functions[0].obligations[0];
    assert!(
        ob.description.contains("ready_flag"),
        "report obligation should describe the ordering variable"
    );
    assert!(ob.description.contains("Relaxed"), "report obligation should mention actual ordering");
    assert_eq!(
        ob.proof_level,
        ProofLevel::L1Functional,
        "report obligation should be L1 Functional"
    );
}

// ---------------------------------------------------------------------------
// 9. Proof level filtering: L0 includes race candidate, excludes InsufficientOrdering
// ---------------------------------------------------------------------------

/// Filters a generated unsupported race candidate and a separate ordering VC.
#[test]
fn test_proof_level_filtering_concurrency_vcs() {
    use trust_types::ProofLevel;

    let accesses = [
        SharedAccess {
            variable: "buf".into(),
            access_kind: AccessKind::Write,
            thread_id: "t1".into(),
            happens_before: vec![],
            span: SourceSpan::default(),
        },
        SharedAccess {
            variable: "buf".into(),
            access_kind: AccessKind::Read,
            thread_id: "t2".into(),
            happens_before: vec![],
            span: SourceSpan::default(),
        },
    ];
    let data_race_vc = generate_race_vcs(&detect_potential_races(&accesses), "race_fn", &accesses)
        .into_iter()
        .next()
        .expect("the conflicting pair must yield a candidate");

    let ordering_vc = make_concurrency_vc(
        VcKind::InsufficientOrdering {
            variable: "flag".to_string(),
            actual: "Relaxed".to_string(),
            required: "Release".to_string(),
        },
        "ordering_fn",
    );

    let all_vcs = vec![data_race_vc, ordering_vc];
    assert_eq!(all_vcs.len(), 2);

    // Filter to L0 Safety only
    let l0_vcs = trust_vcgen::filter_vcs_by_level(all_vcs.clone(), ProofLevel::L0Safety);
    assert_eq!(l0_vcs.len(), 1, "L0 filter should keep the race candidate");
    assert!(
        matches!(l0_vcs[0].kind, VcKind::UnsupportedMir { .. }),
        "the retained VC should be an unsupported race candidate"
    );
    assert_eq!(l0_vcs[0].kind.proof_level(), ProofLevel::L0Safety);

    // Filter to L1 Functional — should keep both
    let l1_vcs = trust_vcgen::filter_vcs_by_level(all_vcs.clone(), ProofLevel::L1Functional);
    assert_eq!(
        l1_vcs.len(),
        2,
        "L1 filter should keep both DataRace (L0) and InsufficientOrdering (L1)"
    );

    // Route L0-filtered VCs and verify report only has DataRace
    let router = trust_router::Router::new();
    let l0_results = router.verify_all(&l0_vcs);
    let l0_report = trust_report::build_json_report("l0_concurrency", &l0_results);

    assert_eq!(l0_report.summary.functions_analyzed, 1);
    assert!(
        l0_report.functions[0].obligations.iter().all(|o| o.proof_level == ProofLevel::L0Safety),
        "L0 report should only contain L0 obligations"
    );

    // Route all VCs and verify report has both levels
    let all_results = router.verify_all(&all_vcs);
    let full_report = trust_report::build_json_report("full_concurrency", &all_results);

    assert_eq!(full_report.summary.functions_analyzed, 2);
    assert_eq!(full_report.summary.total_obligations, 2);

    // Verify both proof levels appear
    let levels: Vec<ProofLevel> = full_report
        .functions
        .iter()
        .flat_map(|f| f.obligations.iter().map(|o| o.proof_level))
        .collect();
    assert!(
        levels.contains(&ProofLevel::L0Safety),
        "full report should contain L0 Safety obligations"
    );
    assert!(
        levels.contains(&ProofLevel::L1Functional),
        "full report should contain L1 Functional obligations"
    );
}
