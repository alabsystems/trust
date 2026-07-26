// trust_vcgen/memory_ordering/tests.rs: Tests for memory ordering verification
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::UnwindEdge;
use trust_types::{
    Aarch64AtomicSemanticFact, Aarch64ExclusiveMonitorSemantics, Aarch64SyncBoundaryKind,
    Aarch64SyncBoundarySemanticFact, Aarch64SyncOrdering, Aarch64SyncScope, AtomicOpKind,
    AtomicOperation, AtomicOrdering, AtomicRmwOp, ConcurrencyPoint, Formula, HappensBeforeEdgeKind,
    MemoryAccessKind, MemoryOrderingSemantics, Place, Sort, SourceSpan, VcKind,
};

use super::*;
use crate::data_race::{AccessKind, MemoryOrdering};

// -----------------------------------------------------------------------
// HappensBefore tests
// -----------------------------------------------------------------------

#[test]
fn test_hb_reflexive() {
    let hb = HappensBefore::new(5);
    for i in 0..5 {
        assert!(hb.happens_before(i, i), "happens-before must be reflexive");
    }
}

#[test]
fn test_hb_direct_edge() {
    let mut hb = HappensBefore::new(3);
    assert!(hb.add_edge(0, 1));
    assert!(hb.happens_before(0, 1));
    assert!(!hb.happens_before(1, 0));
}

#[test]
fn test_hb_transitive() {
    let mut hb = HappensBefore::new(4);
    hb.add_edge(0, 1);
    hb.add_edge(1, 2);
    hb.add_edge(2, 3);

    assert!(hb.happens_before(0, 3), "HB should be transitive: 0->1->2->3");
    assert!(hb.happens_before(0, 2), "HB should be transitive: 0->1->2");
    assert!(hb.happens_before(1, 3), "HB should be transitive: 1->2->3");
    assert!(!hb.happens_before(3, 0), "reverse should not hold");
}

#[test]
fn test_hb_no_edge_between_unconnected() {
    let mut hb = HappensBefore::new(4);
    hb.add_edge(0, 1);
    hb.add_edge(2, 3);

    assert!(!hb.happens_before(0, 3));
    assert!(!hb.happens_before(1, 2));
}

#[test]
fn test_hb_are_ordered() {
    let mut hb = HappensBefore::new(3);
    hb.add_edge(0, 1);

    assert!(hb.are_ordered(0, 1));
    assert!(hb.are_ordered(1, 0)); // ordered in either direction counts
    assert!(!hb.are_ordered(0, 2));
}

#[test]
fn test_hb_out_of_range() {
    let mut hb = HappensBefore::new(2);
    assert!(!hb.add_edge(0, 5)); // out of range
    assert!(!hb.happens_before(0, 10));
}

#[test]
fn test_hb_synchronizes_with() {
    let mut hb = HappensBefore::new(4);
    // Thread 1: event 0 (write), event 1 (release store)
    // Thread 2: event 2 (acquire load), event 3 (read)
    hb.add_edge(0, 1); // program order
    hb.add_synchronizes_with(1, 2); // release-acquire sync
    hb.add_edge(2, 3); // program order

    assert!(hb.happens_before(0, 3), "write should HB read via release-acquire");
}

#[test]
fn test_hb_successors() {
    let mut hb = HappensBefore::new(4);
    hb.add_edge(0, 1);
    hb.add_edge(0, 2);
    hb.add_edge(0, 3);

    let mut succs = hb.successors(0);
    succs.sort();
    assert_eq!(succs, vec![1, 2, 3]);
    assert!(hb.successors(3).is_empty());
}

#[test]
fn test_hb_edge_count() {
    let mut hb = HappensBefore::new(3);
    assert_eq!(hb.edge_count(), 0);
    hb.add_edge(0, 1);
    hb.add_edge(0, 2);
    hb.add_edge(1, 2);
    assert_eq!(hb.edge_count(), 3);
}

#[test]
fn test_hb_duplicate_edge() {
    let mut hb = HappensBefore::new(2);
    assert!(hb.add_edge(0, 1));
    assert!(!hb.add_edge(0, 1)); // duplicate
    assert_eq!(hb.edge_count(), 1);
}

#[test]
fn test_hb_query_apis_fail_closed_on_invalid_deserialized_edges() {
    let hb: HappensBefore = serde_json::from_value(serde_json::json!({
        "edges": { "0": [1, 2] },
        "event_count": 2
    }))
    .expect("deserialization can materialize malformed HB evidence");

    let mut invalid_edges = hb.validate().expect_err("out-of-range edge must be rejected");
    invalid_edges.sort();
    assert_eq!(invalid_edges, vec![(0, Some(2))]);

    assert!(
        !hb.happens_before(0, 1),
        "valid-looking edges must not leak out of an invalid HB relation"
    );
    assert!(!hb.are_ordered(0, 1));
    assert!(hb.successors(0).is_empty());
    assert_eq!(hb.edge_count(), 0);
}

// -----------------------------------------------------------------------
// RaceCondition tests
// -----------------------------------------------------------------------

#[test]
fn test_race_condition_describe() {
    let race = RaceCondition {
        first_access: 0,
        second_access: 1,
        location: "counter".to_string(),
        first_thread: "main".to_string(),
        second_thread: "worker".to_string(),
        first_kind: AccessKind::Write,
        second_kind: AccessKind::Read,
        first_span: SourceSpan::default(),
        second_span: SourceSpan::default(),
    };

    let desc = race.describe();
    assert!(desc.contains("counter"));
    assert!(desc.contains("write"));
    assert!(desc.contains("read"));
    assert!(desc.contains("main"));
    assert!(desc.contains("worker"));
}

#[test]
fn test_race_condition_write_write() {
    let race = RaceCondition {
        first_access: 0,
        second_access: 1,
        location: "x".to_string(),
        first_thread: "t1".to_string(),
        second_thread: "t2".to_string(),
        first_kind: AccessKind::Write,
        second_kind: AccessKind::Write,
        first_span: SourceSpan::default(),
        second_span: SourceSpan::default(),
    };
    assert!(race.is_write_write());
}

#[test]
fn test_race_condition_read_write_not_write_write() {
    let race = RaceCondition {
        first_access: 0,
        second_access: 1,
        location: "x".to_string(),
        first_thread: "t1".to_string(),
        second_thread: "t2".to_string(),
        first_kind: AccessKind::Read,
        second_kind: AccessKind::Write,
        first_span: SourceSpan::default(),
        second_span: SourceSpan::default(),
    };
    assert!(!race.is_write_write());
}

// -----------------------------------------------------------------------
// AtomicAccessLog tests
// -----------------------------------------------------------------------

fn make_atomic_entry(location: &str, kind: AccessKind, thread: &str) -> AtomicAccessEntry {
    AtomicAccessEntry {
        location: location.to_string(),
        access_kind: kind,
        thread_id: thread.to_string(),
        span: SourceSpan::default(),
    }
}

fn make_aarch64_atomic_fact(
    opcode: &str,
    access: MemoryAccessKind,
    ordering: MemoryOrderingSemantics,
    exclusive_monitor: Aarch64ExclusiveMonitorSemantics,
    reports_status: bool,
    missing_witnesses: &[&str],
) -> Aarch64AtomicSemanticFact {
    Aarch64AtomicSemanticFact {
        origin: None,
        opcode: opcode.to_string(),
        operand: None,
        access,
        ordering,
        exclusive_monitor,
        reports_status,
        missing_witnesses: missing_witnesses.iter().map(|witness| (*witness).to_string()).collect(),
        consumed_by_proof_model: false,
    }
}

fn make_aarch64_sync_fact(
    opcode: &str,
    kind: Aarch64SyncBoundaryKind,
    scope: Aarch64SyncScope,
    ordering: Aarch64SyncOrdering,
    clears_exclusive_monitor: bool,
    raw_option: Option<u8>,
    missing_witnesses: &[&str],
) -> Aarch64SyncBoundarySemanticFact {
    Aarch64SyncBoundarySemanticFact {
        origin: None,
        opcode: opcode.to_string(),
        operand: None,
        kind,
        scope,
        ordering,
        clears_exclusive_monitor,
        raw_option,
        missing_witnesses: missing_witnesses.iter().map(|witness| (*witness).to_string()).collect(),
        consumed_by_proof_model: false,
    }
}

const AARCH64_BARRIER_WITNESSES: &[&str] = &[
    "barrier ordering event",
    "barrier domain witness",
    "barrier effect witness",
    "barrier thread identity",
    "pre-barrier program-order edge",
    "post-barrier program-order edge",
    "barrier happens-before witness",
];

fn make_aarch64_barrier_fact(
    opcode: &str,
    domain: Aarch64BarrierDomain,
    effect: Aarch64BarrierEffect,
    ordering: MemoryOrderingSemantics,
    missing_witnesses: &[&str],
) -> Aarch64BarrierSemanticFact {
    Aarch64BarrierSemanticFact {
        opcode: opcode.to_string(),
        domain,
        effect,
        ordering,
        missing_witnesses: missing_witnesses.iter().map(|witness| (*witness).to_string()).collect(),
    }
}

#[test]
fn test_atomic_log_record_and_query() {
    let mut log = AtomicAccessLog::new();
    let idx0 = log.record(make_atomic_entry(
        "flag",
        AccessKind::AtomicWrite(MemoryOrdering::Release),
        "t1",
    ));
    let idx1 = log.record(make_atomic_entry(
        "flag",
        AccessKind::AtomicRead(MemoryOrdering::Acquire),
        "t2",
    ));
    let idx2 = log.record(make_atomic_entry(
        "counter",
        AccessKind::AtomicWrite(MemoryOrdering::Relaxed),
        "t1",
    ));

    assert_eq!(idx0, 0);
    assert_eq!(idx1, 1);
    assert_eq!(idx2, 2);
    assert_eq!(log.len(), 3);
    assert!(!log.is_empty());
}

#[test]
fn test_atomic_log_try_record_non_atomic() {
    let mut log = AtomicAccessLog::new();
    let result = log.try_record(make_atomic_entry("x", AccessKind::Write, "t1"));
    assert!(result.is_none(), "non-atomic access should be rejected by try_record");
    assert!(log.is_empty());
}

#[test]
#[should_panic(expected = "AtomicAccessLog::record requires atomic access")]
fn test_atomic_log_record_non_atomic_panics() {
    let mut log = AtomicAccessLog::new();
    log.record(make_atomic_entry("x", AccessKind::Write, "t1"));
}

#[test]
fn test_atomic_log_try_record_atomic() {
    let mut log = AtomicAccessLog::new();
    let result = log.try_record(make_atomic_entry(
        "x",
        AccessKind::AtomicWrite(MemoryOrdering::SeqCst),
        "t1",
    ));
    assert_eq!(result, Some(0));
    assert_eq!(log.len(), 1);
}

#[test]
fn test_atomic_log_validate_rejects_non_atomic_deserialized_entries() {
    let release = make_atomic_entry("flag", AccessKind::AtomicWrite(MemoryOrdering::Release), "t1");
    let non_atomic_read = make_atomic_entry("flag", AccessKind::Read, "t2");
    let acquire = make_atomic_entry("flag", AccessKind::AtomicRead(MemoryOrdering::Acquire), "t3");
    let non_atomic_write = make_atomic_entry("data", AccessKind::Write, "t4");
    let log: AtomicAccessLog = serde_json::from_value(serde_json::json!({
        "entries": [release, non_atomic_read, acquire, non_atomic_write]
    }))
    .expect("deserialization can materialize malformed logs");

    assert_eq!(log.validate(), Err(vec![1, 3]));
}

#[test]
fn test_atomic_log_accesses_to() {
    let mut log = AtomicAccessLog::new();
    log.record(make_atomic_entry("flag", AccessKind::AtomicWrite(MemoryOrdering::Release), "t1"));
    log.record(make_atomic_entry(
        "counter",
        AccessKind::AtomicWrite(MemoryOrdering::Relaxed),
        "t1",
    ));
    log.record(make_atomic_entry("flag", AccessKind::AtomicRead(MemoryOrdering::Acquire), "t2"));

    let flag_accesses = log.accesses_to("flag");
    assert_eq!(flag_accesses.len(), 2);
    assert_eq!(flag_accesses[0].0, 0);
    assert_eq!(flag_accesses[1].0, 2);
}

#[test]
fn test_atomic_log_accesses_by_thread() {
    let mut log = AtomicAccessLog::new();
    log.record(make_atomic_entry("x", AccessKind::AtomicWrite(MemoryOrdering::Release), "t1"));
    log.record(make_atomic_entry("y", AccessKind::AtomicRead(MemoryOrdering::Acquire), "t2"));
    log.record(make_atomic_entry("z", AccessKind::AtomicWrite(MemoryOrdering::SeqCst), "t1"));

    let t1_accesses = log.accesses_by_thread("t1");
    assert_eq!(t1_accesses.len(), 2);
}

#[test]
fn test_atomic_log_accesses_with_ordering() {
    let mut log = AtomicAccessLog::new();
    log.record(make_atomic_entry("a", AccessKind::AtomicWrite(MemoryOrdering::Relaxed), "t1"));
    log.record(make_atomic_entry("b", AccessKind::AtomicWrite(MemoryOrdering::SeqCst), "t1"));
    log.record(make_atomic_entry("c", AccessKind::AtomicRead(MemoryOrdering::Relaxed), "t2"));

    let relaxed = log.accesses_with_ordering(MemoryOrdering::Relaxed);
    assert_eq!(relaxed.len(), 2);
}

#[test]
fn test_atomic_log_locations_and_threads() {
    let mut log = AtomicAccessLog::new();
    log.record(make_atomic_entry("x", AccessKind::AtomicWrite(MemoryOrdering::SeqCst), "t1"));
    log.record(make_atomic_entry("y", AccessKind::AtomicRead(MemoryOrdering::SeqCst), "t2"));
    log.record(make_atomic_entry("x", AccessKind::AtomicRead(MemoryOrdering::SeqCst), "t3"));

    let locs = log.locations();
    assert_eq!(locs.len(), 2);
    assert!(locs.contains("x"));
    assert!(locs.contains("y"));

    let threads = log.threads();
    assert_eq!(threads.len(), 3);
}

#[test]
fn test_atomic_log_find_release_acquire_pairs() {
    let mut log = AtomicAccessLog::new();
    log.record(make_atomic_entry("flag", AccessKind::AtomicWrite(MemoryOrdering::Release), "t1"));
    log.record(make_atomic_entry("flag", AccessKind::AtomicRead(MemoryOrdering::Acquire), "t2"));
    log.record(make_atomic_entry("other", AccessKind::AtomicWrite(MemoryOrdering::Relaxed), "t1"));

    let pairs = log.find_release_acquire_pairs();
    assert_eq!(pairs.len(), 1);
    assert_eq!(pairs[0], (0, 1));
}

#[test]
fn test_atomic_log_release_acquire_discovery_fails_closed_on_invalid_evidence() {
    let release = make_atomic_entry("flag", AccessKind::AtomicWrite(MemoryOrdering::Release), "t1");
    let invalid_evidence = make_atomic_entry("data", AccessKind::Read, "t3");
    let acquire = make_atomic_entry("flag", AccessKind::AtomicRead(MemoryOrdering::Acquire), "t2");
    let log: AtomicAccessLog = serde_json::from_value(serde_json::json!({
        "entries": [release, invalid_evidence, acquire]
    }))
    .expect("deserialization can bypass AtomicAccessLog::record");

    assert_eq!(log.validate(), Err(vec![1]));
    assert!(
        log.find_release_acquire_pairs().is_empty(),
        "malformed logs must not contribute release/acquire ordering evidence"
    );
}

#[test]
fn test_atomic_log_query_apis_fail_closed_on_invalid_evidence() {
    let release = make_atomic_entry("flag", AccessKind::AtomicWrite(MemoryOrdering::Release), "t1");
    let invalid_evidence = make_atomic_entry("data", AccessKind::Read, "t3");
    let acquire = make_atomic_entry("flag", AccessKind::AtomicRead(MemoryOrdering::Acquire), "t2");
    let log: AtomicAccessLog = serde_json::from_value(serde_json::json!({
        "entries": [release, invalid_evidence, acquire]
    }))
    .expect("deserialization can bypass AtomicAccessLog::record");

    assert_eq!(log.validate(), Err(vec![1]));
    assert!(log.accesses_to("flag").is_empty());
    assert!(log.accesses_by_thread("t1").is_empty());
    assert!(log.accesses_with_ordering(MemoryOrdering::Release).is_empty());
    assert!(log.locations().is_empty());
    assert!(log.threads().is_empty());
}

#[test]
fn test_atomic_log_no_release_acquire_same_thread() {
    let mut log = AtomicAccessLog::new();
    log.record(make_atomic_entry("flag", AccessKind::AtomicWrite(MemoryOrdering::Release), "t1"));
    log.record(make_atomic_entry("flag", AccessKind::AtomicRead(MemoryOrdering::Acquire), "t1"));

    let pairs = log.find_release_acquire_pairs();
    assert!(pairs.is_empty(), "same-thread pairs are not cross-thread sync");
}

#[test]
fn test_atomic_log_release_acquire_seqcst_counts() {
    let mut log = AtomicAccessLog::new();
    log.record(make_atomic_entry("flag", AccessKind::AtomicWrite(MemoryOrdering::SeqCst), "t1"));
    log.record(make_atomic_entry("flag", AccessKind::AtomicRead(MemoryOrdering::SeqCst), "t2"));

    let pairs = log.find_release_acquire_pairs();
    assert_eq!(pairs.len(), 1, "SeqCst write/read should form a release-acquire pair");
}

#[test]
fn test_atomic_log_release_acquire_rmw_counts() {
    let mut log = AtomicAccessLog::new();
    log.record(make_atomic_entry(
        "counter",
        AccessKind::AtomicRmw(MemoryOrdering::Release, AtomicRmwOp::Add),
        "t1",
    ));
    log.record(make_atomic_entry("counter", AccessKind::AtomicRead(MemoryOrdering::Acquire), "t2"));
    log.record(make_atomic_entry("gate", AccessKind::AtomicWrite(MemoryOrdering::Release), "t3"));
    log.record(make_atomic_entry(
        "gate",
        AccessKind::AtomicRmw(MemoryOrdering::Acquire, AtomicRmwOp::Xchg),
        "t4",
    ));

    let pairs = log.find_release_acquire_pairs();
    assert_eq!(pairs, vec![(0, 1), (2, 3)], "RMWs must participate in sync pairs");
}

#[test]
fn test_atomic_log_empty() {
    let log = AtomicAccessLog::new();
    assert!(log.is_empty());
    assert_eq!(log.len(), 0);
    assert!(log.find_release_acquire_pairs().is_empty());
    assert!(log.locations().is_empty());
    assert!(log.threads().is_empty());
}

// -----------------------------------------------------------------------
// DataRaceDetector tests
// -----------------------------------------------------------------------

#[test]
fn test_detector_simple_race() {
    let mut det = DataRaceDetector::new();
    det.add_access("x", AccessKind::Write, "t1", SourceSpan::default());
    det.add_access("x", AccessKind::Read, "t2", SourceSpan::default());

    let races = det.detect_races();
    assert_eq!(races.len(), 1);
    assert_eq!(races[0].location, "x");
    assert_eq!(races[0].first_thread, "t1");
    assert_eq!(races[0].second_thread, "t2");
}

#[test]
fn test_detector_no_race_with_hb() {
    let mut det = DataRaceDetector::new();
    let w = det.add_access("x", AccessKind::Write, "t1", SourceSpan::default());
    let r = det.add_access("x", AccessKind::Read, "t2", SourceSpan::default());
    det.add_happens_before(w, r);

    let races = det.detect_races();
    assert!(races.is_empty(), "HB edge should prevent race");
}

#[test]
fn test_detector_no_race_same_thread() {
    let mut det = DataRaceDetector::new();
    det.add_access("x", AccessKind::Write, "t1", SourceSpan::default());
    det.add_access("x", AccessKind::Read, "t1", SourceSpan::default());

    let races = det.detect_races();
    assert!(races.is_empty(), "same-thread accesses cannot race");
}

#[test]
fn test_detector_no_race_two_reads() {
    let mut det = DataRaceDetector::new();
    det.add_access("x", AccessKind::Read, "t1", SourceSpan::default());
    det.add_access("x", AccessKind::Read, "t2", SourceSpan::default());

    let races = det.detect_races();
    assert!(races.is_empty(), "two reads cannot race");
}

#[test]
fn test_detector_no_race_both_atomic() {
    let mut det = DataRaceDetector::new();
    det.add_access(
        "x",
        AccessKind::AtomicWrite(MemoryOrdering::Relaxed),
        "t1",
        SourceSpan::default(),
    );
    det.add_access(
        "x",
        AccessKind::AtomicRead(MemoryOrdering::Relaxed),
        "t2",
        SourceSpan::default(),
    );

    let races = det.detect_races();
    assert!(races.is_empty(), "two atomic accesses do not race");
}

#[test]
fn test_detector_race_atomic_vs_non_atomic() {
    let mut det = DataRaceDetector::new();
    det.add_access(
        "x",
        AccessKind::AtomicWrite(MemoryOrdering::Relaxed),
        "t1",
        SourceSpan::default(),
    );
    det.add_access("x", AccessKind::Read, "t2", SourceSpan::default());

    let races = det.detect_races();
    assert_eq!(races.len(), 1, "atomic + non-atomic = race");
}

#[test]
fn test_detector_transitive_hb_prevents_race() {
    let mut det = DataRaceDetector::new();
    let w = det.add_access("x", AccessKind::Write, "t1", SourceSpan::default());
    let rel = det.add_access(
        "flag",
        AccessKind::AtomicWrite(MemoryOrdering::Release),
        "t1",
        SourceSpan::default(),
    );
    let acq = det.add_access(
        "flag",
        AccessKind::AtomicRead(MemoryOrdering::Acquire),
        "t2",
        SourceSpan::default(),
    );
    let r = det.add_access("x", AccessKind::Read, "t2", SourceSpan::default());

    det.add_happens_before(w, rel); // program order in t1
    det.add_sync_pair(rel, acq); // release-acquire sync
    det.add_happens_before(acq, r); // program order in t2

    let races = det.detect_races();
    // The write-read pair on "x" should be ordered via transitive HB.
    // Filter to only "x" races since flag accesses are both atomic.
    let x_races: Vec<_> = races.iter().filter(|r| r.location == "x").collect();
    assert!(x_races.is_empty(), "transitive HB via release-acquire should prevent race on x");
}

#[test]
fn test_detector_multiple_variables() {
    let mut det = DataRaceDetector::new();
    det.add_access("x", AccessKind::Write, "t1", SourceSpan::default());
    det.add_access("x", AccessKind::Read, "t2", SourceSpan::default());
    det.add_access("y", AccessKind::Write, "t1", SourceSpan::default());
    det.add_access("y", AccessKind::Write, "t2", SourceSpan::default());

    let races = det.detect_races();
    assert_eq!(races.len(), 2, "should detect races on both x and y");
}

#[test]
fn test_detector_fence_skipped() {
    let mut det = DataRaceDetector::new();
    det.add_access("x", AccessKind::Write, "t1", SourceSpan::default());
    det.add_access("fence", AccessKind::Fence(MemoryOrdering::SeqCst), "t1", SourceSpan::default());
    det.add_access("x", AccessKind::Read, "t2", SourceSpan::default());

    // Fence is skipped as a race participant but doesn't establish HB here
    let races = det.detect_races();
    assert_eq!(races.len(), 1);
    assert_eq!(races[0].location, "x");
}

#[test]
fn test_detector_access_count() {
    let mut det = DataRaceDetector::new();
    assert_eq!(det.access_count(), 0);
    det.add_access("x", AccessKind::Write, "t1", SourceSpan::default());
    assert_eq!(det.access_count(), 1);
    det.add_access("y", AccessKind::Read, "t2", SourceSpan::default());
    assert_eq!(det.access_count(), 2);
}

#[test]
fn test_detector_default() {
    let det = DataRaceDetector::default();
    assert_eq!(det.access_count(), 0);
    assert!(det.detect_races().is_empty());
}

// -----------------------------------------------------------------------
// MemoryModelChecker tests
// -----------------------------------------------------------------------

#[test]
fn test_checker_sound_when_no_issues() {
    let log = AtomicAccessLog::new();
    let hb = HappensBefore::new(0);
    let checker = MemoryModelChecker::new(log, hb);

    let result = checker.check();
    assert!(result.is_sound);
    assert!(result.races.is_empty());
    assert!(result.ordering_violations.is_empty());
    assert!(result.ordering_coverage_gaps.is_empty());
}

#[test]
fn test_checker_detects_ordering_violation() {
    let mut log = AtomicAccessLog::new();
    log.record(make_atomic_entry("flag", AccessKind::AtomicRead(MemoryOrdering::Relaxed), "t1"));

    let hb = HappensBefore::new(1);
    let mut checker = MemoryModelChecker::new(log, hb);
    checker.require_ordering(OrderingRequirement {
        access_index: 0,
        required: MemoryOrdering::Acquire,
        reason: "synchronizes with release store".to_string(),
    });

    let result = checker.check();
    assert!(!result.is_sound);
    assert_eq!(result.ordering_violations.len(), 1);
    assert!(result.ordering_coverage_gaps.is_empty());
    assert_eq!(result.ordering_violations[0].actual, MemoryOrdering::Relaxed);
    assert_eq!(result.ordering_violations[0].required, MemoryOrdering::Acquire);
}

#[test]
fn test_checker_no_violation_when_sufficient() {
    let mut log = AtomicAccessLog::new();
    log.record(make_atomic_entry("flag", AccessKind::AtomicRead(MemoryOrdering::SeqCst), "t1"));

    let hb = HappensBefore::new(1);
    let mut checker = MemoryModelChecker::new(log, hb);
    checker.require_ordering(OrderingRequirement {
        access_index: 0,
        required: MemoryOrdering::Acquire,
        reason: "synchronizes with release store".to_string(),
    });

    let result = checker.check();
    assert!(result.is_sound);
    assert!(result.ordering_coverage_gaps.is_empty());
}

#[test]
fn test_checker_missing_ordering_requirement_fails_closed() {
    let log = AtomicAccessLog::new();
    let hb = HappensBefore::new(0);
    let mut checker = MemoryModelChecker::new(log, hb);
    checker.require_ordering(OrderingRequirement {
        access_index: 3,
        required: MemoryOrdering::Acquire,
        reason: "extracted acquire witness must bind to an atomic access".to_string(),
    });

    let result = checker.check();
    assert!(!result.is_sound, "missing requirement targets must fail closed");
    assert!(result.ordering_violations.is_empty());
    assert_eq!(result.ordering_coverage_gaps.len(), 1);
    assert_eq!(result.ordering_coverage_gaps[0].access_index, 3);
    assert!(result.ordering_coverage_gaps[0].detail.contains("missing atomic access index 3"));

    let vcs = checker.generate_vcs("missing_atomic_witness");
    assert_eq!(vcs.len(), 1);
    match &vcs[0].kind {
        VcKind::UnsupportedMir { kind, detail } => {
            assert_eq!(kind, "ConcurrencyOrderingCoverageGap");
            assert!(detail.contains("required=Acquire"));
            assert!(detail.contains("extracted acquire witness"));
        }
        other => panic!("expected unsupported coverage-gap VC, got: {other:?}"),
    }
}

#[test]
fn test_checker_non_atomic_ordering_requirement_fails_closed() {
    let malformed_entry = make_atomic_entry("shared", AccessKind::Read, "t1");
    let log: AtomicAccessLog =
        serde_json::from_value(serde_json::json!({ "entries": [malformed_entry] }))
            .expect("malformed serialized log remains possible evidence");

    let hb = HappensBefore::new(1);
    let mut checker = MemoryModelChecker::new(log, hb);
    checker.require_ordering(OrderingRequirement {
        access_index: 0,
        required: MemoryOrdering::Release,
        reason: "release witness must point at an atomic store".to_string(),
    });

    let result = checker.check();
    assert!(!result.is_sound, "non-atomic requirement targets must fail closed");
    assert!(result.ordering_violations.is_empty());
    assert_eq!(result.ordering_coverage_gaps.len(), 1);
    assert!(result.ordering_coverage_gaps[0].detail.contains("non-atomic access `shared`"));

    let vcs = checker.generate_vcs("non_atomic_witness");
    assert_eq!(vcs.len(), 1);
    assert!(matches!(
        &vcs[0].kind,
        VcKind::UnsupportedMir { kind, detail }
            if kind == "ConcurrencyOrderingCoverageGap"
                && detail.contains("required=Release")
                && detail.contains("release witness")
    ));
}

#[test]
fn test_checker_invalid_atomic_log_rejects_partial_ordering_evidence() {
    let valid_but_weak =
        make_atomic_entry("flag", AccessKind::AtomicRead(MemoryOrdering::Relaxed), "consumer");
    let invalid_evidence = make_atomic_entry("data", AccessKind::Read, "observer");
    let log: AtomicAccessLog = serde_json::from_value(serde_json::json!({
        "entries": [valid_but_weak, invalid_evidence]
    }))
    .expect("malformed serialized log remains possible evidence");

    let hb = HappensBefore::new(2);
    let mut checker = MemoryModelChecker::new(log, hb);
    checker.require_ordering(OrderingRequirement {
        access_index: 0,
        required: MemoryOrdering::Acquire,
        reason: "valid-looking relaxed access must not be checked from an invalid log".to_string(),
    });

    let result = checker.check();
    assert!(!result.is_sound, "invalid atomic logs must fail closed");
    assert!(
        result.ordering_violations.is_empty(),
        "checker must not derive partial ordering violations from invalid logs"
    );
    assert_eq!(result.ordering_coverage_gaps.len(), 1);
    assert!(result.ordering_coverage_gaps[0].detail.contains("invalid atomic access log"));
    assert!(result.ordering_coverage_gaps[0].detail.contains("index 1"));

    let vcs = checker.generate_vcs("invalid_atomic_log");
    assert_eq!(vcs.len(), 1);
    assert!(matches!(
        &vcs[0].kind,
        VcKind::UnsupportedMir { kind, detail }
            if kind == "ConcurrencyOrderingCoverageGap"
                && detail.contains("invalid atomic access log")
    ));
}

#[test]
fn test_checker_invalid_happens_before_rejects_partial_ordering_evidence() {
    let hb: HappensBefore = serde_json::from_value(serde_json::json!({
        "edges": { "0": [1, 2] },
        "event_count": 2
    }))
    .expect("deserialization can materialize malformed HB evidence");

    let checker = MemoryModelChecker::new(AtomicAccessLog::new(), hb);

    assert!(
        !checker.happens_before().happens_before(0, 1),
        "valid-looking HB edges must not leak through checker query access"
    );

    let result = checker.check();
    assert!(!result.is_sound, "invalid HB evidence must fail closed");
    assert!(result.ordering_violations.is_empty());
    assert_eq!(result.ordering_coverage_gaps.len(), 1);
    assert!(result.ordering_coverage_gaps[0].detail.contains("invalid happens-before edge 0 -> 2"));

    let vcs = checker.generate_vcs("invalid_happens_before");
    assert_eq!(vcs.len(), 1);
    assert!(matches!(
        &vcs[0].kind,
        VcKind::UnsupportedMir { kind, detail }
            if kind == "ConcurrencyOrderingCoverageGap"
                && detail.contains("happens-before evidence")
    ));
}

#[test]
fn test_checker_release_acquire_consistency() {
    let mut log = AtomicAccessLog::new();
    log.record(make_atomic_entry("flag", AccessKind::AtomicWrite(MemoryOrdering::Release), "t1"));
    log.record(make_atomic_entry("flag", AccessKind::AtomicRead(MemoryOrdering::Acquire), "t2"));

    let hb = HappensBefore::new(2);
    let checker = MemoryModelChecker::new(log, hb);

    let violations = checker.check_release_acquire_consistency();
    assert!(violations.is_empty(), "proper release-acquire pair should have no violations");
}

#[test]
fn test_checker_release_acquire_inconsistency_weak_acquire() {
    let mut log = AtomicAccessLog::new();
    // Release is proper, but acquire side uses Relaxed (too weak)
    log.record(make_atomic_entry("flag", AccessKind::AtomicWrite(MemoryOrdering::Release), "t1"));
    log.record(make_atomic_entry("flag", AccessKind::AtomicRead(MemoryOrdering::Relaxed), "t2"));

    let hb = HappensBefore::new(2);
    let checker = MemoryModelChecker::new(log, hb);

    let violations = checker.check_release_acquire_consistency();
    // Relaxed read won't be found as an acquire in find_release_acquire_pairs,
    // so this returns empty (it's not a release-acquire pair at all).
    // The issue is caught by ordering requirements instead.
    assert!(violations.is_empty());
}

#[test]
fn test_checker_generate_vcs_for_violation() {
    let mut log = AtomicAccessLog::new();
    log.record(make_atomic_entry("flag", AccessKind::AtomicRead(MemoryOrdering::Relaxed), "t1"));

    let hb = HappensBefore::new(1);
    let mut checker = MemoryModelChecker::new(log, hb);
    checker.require_ordering(OrderingRequirement {
        access_index: 0,
        required: MemoryOrdering::Acquire,
        reason: "must synchronize".to_string(),
    });

    let vcs = checker.generate_vcs("spin_wait");
    assert_eq!(vcs.len(), 1);
    assert!(matches!(
        &vcs[0].kind,
        VcKind::InsufficientOrdering { variable, actual, required }
            if variable == "flag" && actual == "Relaxed" && required == "Acquire"
    ));
    assert_eq!(vcs[0].function, "spin_wait");
    assert_eq!(
        vcs[0].formula,
        Formula::Var(crate::generated_formula_symbol("memory_ordering", "reach_0"), Sort::Bool,)
    );
    assert_ne!(vcs[0].formula.var_name(), Some("reach_0"));
}

#[test]
fn test_checker_generate_no_vcs_when_sound() {
    let log = AtomicAccessLog::new();
    let hb = HappensBefore::new(0);
    let checker = MemoryModelChecker::new(log, hb);

    let vcs = checker.generate_vcs("safe_fn");
    assert!(vcs.is_empty());
}

#[test]
fn test_checker_multiple_violations() {
    let mut log = AtomicAccessLog::new();
    log.record(make_atomic_entry("a", AccessKind::AtomicRead(MemoryOrdering::Relaxed), "t1"));
    log.record(make_atomic_entry("b", AccessKind::AtomicWrite(MemoryOrdering::Relaxed), "t2"));

    let hb = HappensBefore::new(2);
    let mut checker = MemoryModelChecker::new(log, hb);
    checker.require_ordering(OrderingRequirement {
        access_index: 0,
        required: MemoryOrdering::Acquire,
        reason: "needs acquire for load".to_string(),
    });
    checker.require_ordering(OrderingRequirement {
        access_index: 1,
        required: MemoryOrdering::Release,
        reason: "needs release for store".to_string(),
    });

    let result = checker.check();
    assert_eq!(result.ordering_violations.len(), 2);
    assert!(!result.is_sound);
}

// -----------------------------------------------------------------------
// Serialization roundtrip tests
// -----------------------------------------------------------------------

#[test]
fn test_happens_before_serialization_roundtrip() {
    let mut hb = HappensBefore::new(3);
    hb.add_edge(0, 1);
    hb.add_edge(1, 2);

    let json = serde_json::to_string(&hb).expect("serialize");
    let round: HappensBefore = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(round.event_count(), 3);
    assert!(round.happens_before(0, 2));
}

#[test]
fn test_race_condition_serialization_roundtrip() {
    let race = RaceCondition {
        first_access: 0,
        second_access: 3,
        location: "shared_buf".to_string(),
        first_thread: "producer".to_string(),
        second_thread: "consumer".to_string(),
        first_kind: AccessKind::Write,
        second_kind: AccessKind::Read,
        first_span: SourceSpan::default(),
        second_span: SourceSpan::default(),
    };
    let json = serde_json::to_string(&race).expect("serialize");
    let round: RaceCondition = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(round, race);
}

#[test]
fn test_atomic_access_log_serialization_roundtrip() {
    let mut log = AtomicAccessLog::new();
    log.record(make_atomic_entry("flag", AccessKind::AtomicWrite(MemoryOrdering::Release), "t1"));
    log.record(make_atomic_entry("flag", AccessKind::AtomicRead(MemoryOrdering::Acquire), "t2"));

    let json = serde_json::to_string(&log).expect("serialize");
    let round: AtomicAccessLog = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(round.len(), 2);
}

#[test]
fn test_ordering_violation_serialization_roundtrip() {
    let violation = OrderingViolation {
        access_index: 0,
        location: "counter".to_string(),
        actual: MemoryOrdering::Relaxed,
        required: MemoryOrdering::Acquire,
        reason: "synchronizes with release".to_string(),
        span: SourceSpan::default(),
    };
    let json = serde_json::to_string(&violation).expect("serialize");
    let round: OrderingViolation = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(round, violation);
}

#[test]
fn test_memory_model_check_result_serialization_roundtrip() {
    let result = MemoryModelCheckResult {
        races: vec![],
        ordering_violations: vec![],
        ordering_coverage_gaps: vec![],
        is_sound: true,
    };
    let json = serde_json::to_string(&result).expect("serialize");
    let round: MemoryModelCheckResult = serde_json::from_str(&json).expect("deserialize");
    assert!(round.is_sound);
    assert!(round.ordering_coverage_gaps.is_empty());
}

// -----------------------------------------------------------------------
// Integration-style tests
// -----------------------------------------------------------------------

#[test]
fn test_full_workflow_spin_lock_pattern() {
    // Simulate a spin-lock pattern:
    // Thread 1: write data, release-store flag=1
    // Thread 2: acquire-load flag until 1, read data
    let mut det = DataRaceDetector::new();

    // Thread 1
    let write_data = det.add_access("data", AccessKind::Write, "t1", SourceSpan::default());
    let release_flag = det.add_access(
        "flag",
        AccessKind::AtomicWrite(MemoryOrdering::Release),
        "t1",
        SourceSpan::default(),
    );
    det.add_happens_before(write_data, release_flag); // program order

    // Thread 2
    let acquire_flag = det.add_access(
        "flag",
        AccessKind::AtomicRead(MemoryOrdering::Acquire),
        "t2",
        SourceSpan::default(),
    );
    let read_data = det.add_access("data", AccessKind::Read, "t2", SourceSpan::default());
    det.add_happens_before(acquire_flag, read_data); // program order

    // Release-acquire synchronization
    det.add_sync_pair(release_flag, acquire_flag);

    let races = det.detect_races();
    let data_races: Vec<_> = races.iter().filter(|r| r.location == "data").collect();
    assert!(data_races.is_empty(), "spin-lock pattern should be race-free on data");
}

#[test]
fn test_full_workflow_broken_spin_lock() {
    // Broken spin-lock: writer forgets release ordering
    let mut det = DataRaceDetector::new();

    let write_data = det.add_access("data", AccessKind::Write, "t1", SourceSpan::default());
    let _relaxed_flag = det.add_access(
        "flag",
        AccessKind::AtomicWrite(MemoryOrdering::Relaxed), // Bug: should be Release
        "t1",
        SourceSpan::default(),
    );
    det.add_happens_before(write_data, _relaxed_flag);

    let _acquire_flag = det.add_access(
        "flag",
        AccessKind::AtomicRead(MemoryOrdering::Acquire),
        "t2",
        SourceSpan::default(),
    );
    let _read_data = det.add_access("data", AccessKind::Read, "t2", SourceSpan::default());
    det.add_happens_before(_acquire_flag, _read_data);

    // No sync pair established (because the writer used Relaxed)

    let races = det.detect_races();
    let data_races: Vec<_> = races.iter().filter(|r| r.location == "data").collect();
    assert_eq!(data_races.len(), 1, "broken spin-lock should race on data");
}

#[test]
fn test_full_workflow_checker_with_log() {
    let mut log = AtomicAccessLog::new();
    let release_idx = log.record(make_atomic_entry(
        "ready",
        AccessKind::AtomicWrite(MemoryOrdering::Release),
        "producer",
    ));
    let acquire_idx = log.record(make_atomic_entry(
        "ready",
        AccessKind::AtomicRead(MemoryOrdering::Acquire),
        "consumer",
    ));

    let mut hb = HappensBefore::new(2);
    hb.add_synchronizes_with(release_idx, acquire_idx);

    let checker = MemoryModelChecker::new(log, hb);

    // Check that the release-acquire pair is consistent.
    let violations = checker.check_release_acquire_consistency();
    assert!(violations.is_empty());

    // Overall check should be sound.
    let result = checker.check();
    assert!(result.is_sound);

    // No VCs generated.
    let vcs = checker.generate_vcs("producer_consumer");
    assert!(vcs.is_empty());
}

#[test]
fn test_aarch64_release_acquire_consumer_accepts_direct_hb_witness() {
    let mut log = AtomicAccessLog::new();
    let release_idx = log.record(make_atomic_entry(
        "ready",
        AccessKind::AtomicWrite(MemoryOrdering::Release),
        "producer",
    ));
    let acquire_idx = log.record(make_atomic_entry(
        "ready",
        AccessKind::AtomicRead(MemoryOrdering::Acquire),
        "consumer",
    ));

    let mut hb = HappensBefore::new(2);
    hb.add_synchronizes_with(release_idx, acquire_idx);

    let checker = MemoryModelChecker::new(log, hb);
    let release_fact = make_aarch64_atomic_fact(
        "stlr",
        MemoryAccessKind::Write,
        MemoryOrderingSemantics::Release,
        Aarch64ExclusiveMonitorSemantics::None,
        false,
        &[
            "release ordering event",
            "synchronization edge",
            "thread identity",
            "happens-before witness",
        ],
    );
    let acquire_fact = make_aarch64_atomic_fact(
        "ldar",
        MemoryAccessKind::Read,
        MemoryOrderingSemantics::Acquire,
        Aarch64ExclusiveMonitorSemantics::None,
        false,
        &[
            "acquire ordering event",
            "synchronization edge",
            "thread identity",
            "happens-before witness",
        ],
    );

    let consumed = checker.consume_aarch64_release_acquire_obligation(
        &release_fact,
        &acquire_fact,
        Aarch64ReleaseAcquireWitness {
            release_access_index: release_idx,
            acquire_access_index: acquire_idx,
        },
    );

    assert!(consumed.is_accepted());
    assert!(consumed.missing_witnesses.is_empty());
    assert!(consumed.consumed_witnesses.contains(&"release ordering event".to_string()));
    assert!(consumed.consumed_witnesses.contains(&"acquire ordering event".to_string()));
    assert!(consumed.consumed_witnesses.contains(&"synchronization edge".to_string()));
    assert!(consumed.consumed_witnesses.contains(&"thread identity".to_string()));
    assert!(consumed.consumed_witnesses.contains(&"happens-before witness".to_string()));
    assert!(consumed.diagnostic.contains("proof-grade accepted"));
}

#[test]
fn test_aarch64_release_acquire_producer_emits_witness_and_consumer_accepts() {
    let mut log = AtomicAccessLog::new();
    let release_idx = log.record(make_atomic_entry(
        "ready",
        AccessKind::AtomicWrite(MemoryOrdering::Release),
        "producer",
    ));
    let acquire_idx = log.record(make_atomic_entry(
        "ready",
        AccessKind::AtomicRead(MemoryOrdering::Acquire),
        "consumer",
    ));

    let mut hb = HappensBefore::new(2);
    hb.add_synchronizes_with(release_idx, acquire_idx);

    let checker = MemoryModelChecker::new(log, hb);
    let release_fact = make_aarch64_atomic_fact(
        "stlr",
        MemoryAccessKind::Write,
        MemoryOrderingSemantics::Release,
        Aarch64ExclusiveMonitorSemantics::None,
        false,
        &[
            "release ordering event",
            "synchronization edge",
            "thread identity",
            "happens-before witness",
        ],
    );
    let acquire_fact = make_aarch64_atomic_fact(
        "ldar",
        MemoryAccessKind::Read,
        MemoryOrderingSemantics::Acquire,
        Aarch64ExclusiveMonitorSemantics::None,
        false,
        &[
            "acquire ordering event",
            "synchronization edge",
            "thread identity",
            "happens-before witness",
        ],
    );

    let produced = checker.produce_aarch64_release_acquire_witness(&release_fact, &acquire_fact);
    let (witness, evidence) = match produced {
        Aarch64ReleaseAcquireWitnessEvidence::Produced { witness, evidence } => (witness, evidence),
        Aarch64ReleaseAcquireWitnessEvidence::Absent { certificate } => {
            panic!("expected release/acquire witness, got absence certificate {certificate:?}");
        }
    };

    assert_eq!(witness.release_access_index, release_idx);
    assert_eq!(witness.acquire_access_index, acquire_idx);
    for required in [
        "release ordering event",
        "acquire ordering event",
        "same atomic location witness",
        "thread identity",
        "synchronization edge",
        "happens-before witness",
    ] {
        assert!(
            evidence.contains(&required.to_string()),
            "producer evidence should contain {required}: {evidence:?}"
        );
    }

    let consumed =
        checker.consume_aarch64_release_acquire_obligation(&release_fact, &acquire_fact, witness);
    assert!(consumed.is_accepted(), "producer witness should satisfy consumer: {consumed:?}");
}

#[test]
fn test_aarch64_release_acquire_consumer_fails_closed_without_hb_witness() {
    let mut log = AtomicAccessLog::new();
    let release_idx = log.record(make_atomic_entry(
        "ready",
        AccessKind::AtomicWrite(MemoryOrdering::Release),
        "producer",
    ));
    let acquire_idx = log.record(make_atomic_entry(
        "ready",
        AccessKind::AtomicRead(MemoryOrdering::Acquire),
        "consumer",
    ));

    let checker = MemoryModelChecker::new(log, HappensBefore::new(2));
    let release_fact = make_aarch64_atomic_fact(
        "stlr",
        MemoryAccessKind::Write,
        MemoryOrderingSemantics::Release,
        Aarch64ExclusiveMonitorSemantics::None,
        false,
        &[],
    );
    let acquire_fact = make_aarch64_atomic_fact(
        "ldar",
        MemoryAccessKind::Read,
        MemoryOrderingSemantics::Acquire,
        Aarch64ExclusiveMonitorSemantics::None,
        false,
        &[],
    );

    let consumed = checker.consume_aarch64_release_acquire_obligation(
        &release_fact,
        &acquire_fact,
        Aarch64ReleaseAcquireWitness {
            release_access_index: release_idx,
            acquire_access_index: acquire_idx,
        },
    );

    assert!(!consumed.is_accepted());
    assert!(consumed.missing_witnesses.contains(&"synchronization edge".to_string()));
    assert!(consumed.missing_witnesses.contains(&"happens-before witness".to_string()));
    assert!(consumed.diagnostic.contains("fail-closed"));
    assert!(!consumed.diagnostic.contains("proof-grade accepted"));
}

#[test]
fn test_aarch64_release_acquire_producer_absence_certificate_without_hb_witness() {
    let mut log = AtomicAccessLog::new();
    let release_idx = log.record(make_atomic_entry(
        "ready",
        AccessKind::AtomicWrite(MemoryOrdering::Release),
        "producer",
    ));
    let acquire_idx = log.record(make_atomic_entry(
        "ready",
        AccessKind::AtomicRead(MemoryOrdering::Acquire),
        "consumer",
    ));

    let checker = MemoryModelChecker::new(log, HappensBefore::new(2));
    let release_fact = make_aarch64_atomic_fact(
        "stlr",
        MemoryAccessKind::Write,
        MemoryOrderingSemantics::Release,
        Aarch64ExclusiveMonitorSemantics::None,
        false,
        &[],
    );
    let acquire_fact = make_aarch64_atomic_fact(
        "ldar",
        MemoryAccessKind::Read,
        MemoryOrderingSemantics::Acquire,
        Aarch64ExclusiveMonitorSemantics::None,
        false,
        &[],
    );

    let produced = checker.produce_aarch64_release_acquire_witness(&release_fact, &acquire_fact);
    let certificate = produced
        .absence_certificate()
        .expect("missing HB must produce a fail-closed absence certificate");

    assert_eq!(certificate.boundary, Aarch64WitnessBoundary::ReleaseAcquire);
    assert_eq!(certificate.candidate_access_indices, vec![release_idx, acquire_idx]);
    assert!(certificate.available_evidence.contains(&"release ordering event".to_string()));
    assert!(certificate.available_evidence.contains(&"acquire ordering event".to_string()));
    assert!(certificate.available_evidence.contains(&"same atomic location witness".to_string()));
    assert!(certificate.available_evidence.contains(&"thread identity".to_string()));
    assert!(certificate.missing_witnesses.contains(&"synchronization edge".to_string()));
    assert!(certificate.missing_witnesses.contains(&"happens-before witness".to_string()));
    assert!(certificate.diagnostic.contains("witness absent"));
}

#[test]
fn test_aarch64_release_acquire_consumer_fails_closed_on_unconsumed_fact_witness() {
    let mut log = AtomicAccessLog::new();
    let release_idx = log.record(make_atomic_entry(
        "ready",
        AccessKind::AtomicWrite(MemoryOrdering::Release),
        "producer",
    ));
    let acquire_idx = log.record(make_atomic_entry(
        "ready",
        AccessKind::AtomicRead(MemoryOrdering::Acquire),
        "consumer",
    ));

    let mut hb = HappensBefore::new(2);
    hb.add_synchronizes_with(release_idx, acquire_idx);

    let checker = MemoryModelChecker::new(log, hb);
    let release_fact = make_aarch64_atomic_fact(
        "stlr",
        MemoryAccessKind::Write,
        MemoryOrderingSemantics::Release,
        Aarch64ExclusiveMonitorSemantics::None,
        false,
        &["release ordering event", "future architecture witness"],
    );
    let acquire_fact = make_aarch64_atomic_fact(
        "ldar",
        MemoryAccessKind::Read,
        MemoryOrderingSemantics::Acquire,
        Aarch64ExclusiveMonitorSemantics::None,
        false,
        &[
            "acquire ordering event",
            "synchronization edge",
            "thread identity",
            "happens-before witness",
        ],
    );

    let consumed = checker.consume_aarch64_release_acquire_obligation(
        &release_fact,
        &acquire_fact,
        Aarch64ReleaseAcquireWitness {
            release_access_index: release_idx,
            acquire_access_index: acquire_idx,
        },
    );

    assert!(!consumed.is_accepted());
    assert!(consumed.missing_witnesses.contains(&"future architecture witness".to_string()));
    assert!(consumed.diagnostic.contains("fail-closed"));
    assert!(!consumed.diagnostic.contains("proof-grade accepted"));
}

#[test]
fn test_aarch64_release_acquire_producer_absence_certificate_for_unconsumed_fact_witness() {
    let mut log = AtomicAccessLog::new();
    let release_idx = log.record(make_atomic_entry(
        "ready",
        AccessKind::AtomicWrite(MemoryOrdering::Release),
        "producer",
    ));
    let acquire_idx = log.record(make_atomic_entry(
        "ready",
        AccessKind::AtomicRead(MemoryOrdering::Acquire),
        "consumer",
    ));

    let mut hb = HappensBefore::new(2);
    hb.add_synchronizes_with(release_idx, acquire_idx);

    let checker = MemoryModelChecker::new(log, hb);
    let release_fact = make_aarch64_atomic_fact(
        "stlr",
        MemoryAccessKind::Write,
        MemoryOrderingSemantics::Release,
        Aarch64ExclusiveMonitorSemantics::None,
        false,
        &["release ordering event", "future architecture witness"],
    );
    let acquire_fact = make_aarch64_atomic_fact(
        "ldar",
        MemoryAccessKind::Read,
        MemoryOrderingSemantics::Acquire,
        Aarch64ExclusiveMonitorSemantics::None,
        false,
        &["acquire ordering event"],
    );

    let produced = checker.produce_aarch64_release_acquire_witness(&release_fact, &acquire_fact);
    let certificate = produced
        .absence_certificate()
        .expect("out-of-bound fact witness must stay visible as an absence certificate");

    assert!(certificate.available_evidence.contains(&"happens-before witness".to_string()));
    assert!(certificate.missing_witnesses.contains(&"future architecture witness".to_string()));
    assert!(certificate.diagnostic.contains("future architecture witness"));
}

#[test]
fn test_aarch64_exclusive_monitor_consumer_remains_fail_closed_without_monitor_witnesses() {
    let mut log = AtomicAccessLog::new();
    let release_idx = log.record(make_atomic_entry(
        "lock",
        AccessKind::AtomicWrite(MemoryOrdering::Release),
        "producer",
    ));
    let acquire_idx = log.record(make_atomic_entry(
        "lock",
        AccessKind::AtomicRead(MemoryOrdering::Acquire),
        "consumer",
    ));

    let mut hb = HappensBefore::new(2);
    hb.add_synchronizes_with(release_idx, acquire_idx);

    let checker = MemoryModelChecker::new(log, hb);
    let store_exclusive = make_aarch64_atomic_fact(
        "stlxr",
        MemoryAccessKind::Write,
        MemoryOrderingSemantics::Release,
        Aarch64ExclusiveMonitorSemantics::StoreConditional,
        true,
        &[
            "release ordering event",
            "synchronization edge",
            "exclusive-monitor reservation state",
            "exclusive-monitor invalidation",
            "store-conditional status result",
            "thread identity",
            "happens-before witness",
        ],
    );
    let load_exclusive = make_aarch64_atomic_fact(
        "ldaxr",
        MemoryAccessKind::Read,
        MemoryOrderingSemantics::Acquire,
        Aarch64ExclusiveMonitorSemantics::LoadReserve,
        false,
        &[
            "acquire ordering event",
            "synchronization edge",
            "exclusive-monitor reservation state",
            "exclusive-monitor invalidation",
            "thread identity",
            "happens-before witness",
        ],
    );

    let consumed = checker.consume_aarch64_release_acquire_obligation(
        &store_exclusive,
        &load_exclusive,
        Aarch64ReleaseAcquireWitness {
            release_access_index: release_idx,
            acquire_access_index: acquire_idx,
        },
    );

    assert!(!consumed.is_accepted());
    assert!(
        consumed.missing_witnesses.contains(&"exclusive-monitor reservation state".to_string())
    );
    assert!(consumed.missing_witnesses.contains(&"exclusive-monitor invalidation".to_string()));
    assert!(consumed.missing_witnesses.contains(&"store-conditional status result".to_string()));
    assert!(consumed.diagnostic.contains("fail-closed"));
    assert!(!consumed.diagnostic.contains("proof-grade accepted"));
}

fn consume_exclusive_monitor_pair(
    reservation_observed: bool,
    no_intervening_invalidation: bool,
    store_status: Option<Aarch64StoreConditionalStatus>,
    same_thread: bool,
    hb_edge: bool,
    load_ordering: MemoryOrdering,
    store_ordering: MemoryOrdering,
) -> Aarch64ProofObligationConsumption {
    let mut log = AtomicAccessLog::new();
    let load_idx =
        log.record(make_atomic_entry("lock", AccessKind::AtomicRead(load_ordering), "worker"));
    let store_thread = if same_thread { "worker" } else { "other-worker" };
    let store_idx = log.record(make_atomic_entry(
        "lock",
        AccessKind::AtomicWrite(store_ordering),
        store_thread,
    ));

    let mut hb = HappensBefore::new(2);
    if hb_edge {
        hb.add_edge(load_idx, store_idx);
    }

    let checker = MemoryModelChecker::new(log, hb);
    let load_exclusive = make_aarch64_atomic_fact(
        "ldaxr",
        MemoryAccessKind::Read,
        MemoryOrderingSemantics::Acquire,
        Aarch64ExclusiveMonitorSemantics::LoadReserve,
        false,
        &[
            "acquire ordering event",
            "synchronization edge",
            "exclusive-monitor reservation state",
            "exclusive-monitor invalidation",
            "thread identity",
            "happens-before witness",
        ],
    );
    let store_exclusive = make_aarch64_atomic_fact(
        "stlxr",
        MemoryAccessKind::Write,
        MemoryOrderingSemantics::Release,
        Aarch64ExclusiveMonitorSemantics::StoreConditional,
        true,
        &[
            "release ordering event",
            "synchronization edge",
            "exclusive-monitor reservation state",
            "exclusive-monitor invalidation",
            "store-conditional status result",
            "thread identity",
            "happens-before witness",
        ],
    );

    checker.consume_aarch64_exclusive_monitor_obligation(
        &load_exclusive,
        &store_exclusive,
        Aarch64ExclusiveMonitorWitness {
            load_reserve_access_index: load_idx,
            store_conditional_access_index: store_idx,
            reservation_observed,
            no_intervening_invalidation,
            store_status,
        },
    )
}

#[test]
fn test_aarch64_exclusive_monitor_consumer_accepts_full_success_boundary() {
    let consumed = consume_exclusive_monitor_pair(
        true,
        true,
        Some(Aarch64StoreConditionalStatus::Succeeded),
        true,
        true,
        MemoryOrdering::Acquire,
        MemoryOrdering::Release,
    );

    assert!(consumed.is_accepted());
    assert!(consumed.missing_witnesses.is_empty());
    for witness in [
        "acquire ordering event",
        "release ordering event",
        "exclusive-monitor reservation state",
        "exclusive-monitor invalidation",
        "thread identity",
        "store-conditional status result",
        "synchronization edge",
        "happens-before witness",
    ] {
        assert!(
            consumed.consumed_witnesses.contains(&witness.to_string()),
            "expected consumed witness {witness}; got {:?}",
            consumed.consumed_witnesses
        );
    }
    assert!(consumed.diagnostic.contains("exclusive-monitor proof-grade accepted"));
}

#[test]
fn test_aarch64_exclusive_monitor_producer_emits_success_witness_and_consumer_accepts() {
    let mut log = AtomicAccessLog::new();
    let load_idx = log.record(make_atomic_entry(
        "lock",
        AccessKind::AtomicRead(MemoryOrdering::Acquire),
        "worker",
    ));
    let store_idx = log.record(make_atomic_entry(
        "lock",
        AccessKind::AtomicWrite(MemoryOrdering::Release),
        "worker",
    ));

    let mut hb = HappensBefore::new(2);
    hb.add_edge(load_idx, store_idx);

    let checker = MemoryModelChecker::new(log, hb);
    let load_exclusive = make_aarch64_atomic_fact(
        "ldaxr",
        MemoryAccessKind::Read,
        MemoryOrderingSemantics::Acquire,
        Aarch64ExclusiveMonitorSemantics::LoadReserve,
        false,
        &[
            "acquire ordering event",
            "synchronization edge",
            "exclusive-monitor reservation state",
            "exclusive-monitor invalidation",
            "thread identity",
            "happens-before witness",
        ],
    );
    let store_exclusive = make_aarch64_atomic_fact(
        "stlxr",
        MemoryAccessKind::Write,
        MemoryOrderingSemantics::Release,
        Aarch64ExclusiveMonitorSemantics::StoreConditional,
        true,
        &[
            "release ordering event",
            "synchronization edge",
            "exclusive-monitor reservation state",
            "exclusive-monitor invalidation",
            "store-conditional status result",
            "thread identity",
            "happens-before witness",
        ],
    );

    let produced = checker.produce_aarch64_exclusive_monitor_witness(
        &load_exclusive,
        &store_exclusive,
        Some(Aarch64StoreConditionalStatus::Succeeded),
    );
    let (witness, evidence) = match produced {
        Aarch64ExclusiveMonitorWitnessEvidence::Produced { witness, evidence } => {
            (witness, evidence)
        }
        Aarch64ExclusiveMonitorWitnessEvidence::Absent { certificate } => {
            panic!("expected exclusive-monitor witness, got absence certificate {certificate:?}");
        }
    };

    assert_eq!(witness.load_reserve_access_index, load_idx);
    assert_eq!(witness.store_conditional_access_index, store_idx);
    assert!(witness.reservation_observed);
    assert!(witness.no_intervening_invalidation);
    assert_eq!(witness.store_status, Some(Aarch64StoreConditionalStatus::Succeeded));
    for required in [
        "acquire ordering event",
        "release ordering event",
        "exclusive-monitor reservation state",
        "exclusive-monitor invalidation",
        "thread identity",
        "store-conditional status result",
        "synchronization edge",
        "happens-before witness",
    ] {
        assert!(
            evidence.contains(&required.to_string()),
            "producer evidence should contain {required}: {evidence:?}"
        );
    }

    let consumed = checker.consume_aarch64_exclusive_monitor_obligation(
        &load_exclusive,
        &store_exclusive,
        witness,
    );
    assert!(consumed.is_accepted(), "producer witness should satisfy consumer: {consumed:?}");
}

#[test]
fn test_aarch64_exclusive_monitor_producer_absence_certificate_without_status() {
    let mut log = AtomicAccessLog::new();
    let load_idx = log.record(make_atomic_entry(
        "lock",
        AccessKind::AtomicRead(MemoryOrdering::Acquire),
        "worker",
    ));
    let store_idx = log.record(make_atomic_entry(
        "lock",
        AccessKind::AtomicWrite(MemoryOrdering::Release),
        "worker",
    ));

    let mut hb = HappensBefore::new(2);
    hb.add_edge(load_idx, store_idx);

    let checker = MemoryModelChecker::new(log, hb);
    let load_exclusive = make_aarch64_atomic_fact(
        "ldaxr",
        MemoryAccessKind::Read,
        MemoryOrderingSemantics::Acquire,
        Aarch64ExclusiveMonitorSemantics::LoadReserve,
        false,
        &[],
    );
    let store_exclusive = make_aarch64_atomic_fact(
        "stlxr",
        MemoryAccessKind::Write,
        MemoryOrderingSemantics::Release,
        Aarch64ExclusiveMonitorSemantics::StoreConditional,
        true,
        &[],
    );

    let produced =
        checker.produce_aarch64_exclusive_monitor_witness(&load_exclusive, &store_exclusive, None);
    let certificate = produced
        .absence_certificate()
        .expect("missing store status must produce a fail-closed absence certificate");

    assert_eq!(certificate.boundary, Aarch64WitnessBoundary::ExclusiveMonitor);
    assert_eq!(certificate.candidate_access_indices, vec![load_idx, store_idx]);
    assert!(
        certificate.available_evidence.contains(&"exclusive-monitor reservation state".to_string())
    );
    assert!(certificate.available_evidence.contains(&"exclusive-monitor invalidation".to_string()));
    assert!(certificate.missing_witnesses.contains(&"store-conditional status result".to_string()));
    assert!(certificate.diagnostic.contains("store-conditional status result"));
}

#[test]
fn test_aarch64_exclusive_monitor_consumer_requires_each_boundary_witness() {
    let cases = [
        (
            "missing reservation",
            false,
            true,
            Some(Aarch64StoreConditionalStatus::Succeeded),
            true,
            true,
            MemoryOrdering::Acquire,
            MemoryOrdering::Release,
            "exclusive-monitor reservation state",
        ),
        (
            "missing invalidation",
            true,
            false,
            Some(Aarch64StoreConditionalStatus::Succeeded),
            true,
            true,
            MemoryOrdering::Acquire,
            MemoryOrdering::Release,
            "exclusive-monitor invalidation",
        ),
        (
            "missing status",
            true,
            true,
            None,
            true,
            true,
            MemoryOrdering::Acquire,
            MemoryOrdering::Release,
            "store-conditional status result",
        ),
        (
            "failed status",
            true,
            true,
            Some(Aarch64StoreConditionalStatus::Failed),
            true,
            true,
            MemoryOrdering::Acquire,
            MemoryOrdering::Release,
            "successful store-conditional status result",
        ),
        (
            "wrong thread",
            true,
            true,
            Some(Aarch64StoreConditionalStatus::Succeeded),
            false,
            true,
            MemoryOrdering::Acquire,
            MemoryOrdering::Release,
            "thread identity",
        ),
        (
            "missing happens-before",
            true,
            true,
            Some(Aarch64StoreConditionalStatus::Succeeded),
            true,
            false,
            MemoryOrdering::Acquire,
            MemoryOrdering::Release,
            "happens-before witness",
        ),
        (
            "weak load ordering",
            true,
            true,
            Some(Aarch64StoreConditionalStatus::Succeeded),
            true,
            true,
            MemoryOrdering::Relaxed,
            MemoryOrdering::Release,
            "acquire ordering event",
        ),
    ];

    for (
        name,
        reservation_observed,
        no_intervening_invalidation,
        store_status,
        same_thread,
        hb_edge,
        load_ordering,
        store_ordering,
        expected_missing,
    ) in cases
    {
        let consumed = consume_exclusive_monitor_pair(
            reservation_observed,
            no_intervening_invalidation,
            store_status,
            same_thread,
            hb_edge,
            load_ordering,
            store_ordering,
        );

        assert!(!consumed.is_accepted(), "{name} should remain fail-closed");
        assert!(
            consumed.missing_witnesses.contains(&expected_missing.to_string()),
            "{name} should miss {expected_missing}; got {:?}",
            consumed.missing_witnesses
        );
        assert!(consumed.diagnostic.contains("fail-closed"), "{name}");
        assert!(!consumed.diagnostic.contains("proof-grade accepted"), "{name}");
    }
}

fn consume_barrier_boundary(
    observed_domain: Option<Aarch64BarrierDomain>,
    observed_effect: Option<Aarch64BarrierEffect>,
    pre_edge: bool,
    post_edge: bool,
    barrier_ordering: MemoryOrdering,
    same_thread: bool,
    missing_witnesses: &[&str],
) -> Aarch64ProofObligationConsumption {
    let mut log = AtomicAccessLog::new();
    let before_idx = log.record(make_atomic_entry(
        "payload",
        AccessKind::AtomicWrite(MemoryOrdering::Relaxed),
        "core0",
    ));
    let barrier_idx =
        log.record(make_atomic_entry("dmb.ish", AccessKind::Fence(barrier_ordering), "core0"));
    let after_thread = if same_thread { "core0" } else { "core1" };
    let after_idx = log.record(make_atomic_entry(
        "payload",
        AccessKind::AtomicRead(MemoryOrdering::Relaxed),
        after_thread,
    ));

    let mut hb = HappensBefore::new(3);
    if pre_edge {
        hb.add_edge(before_idx, barrier_idx);
    }
    if post_edge {
        hb.add_edge(barrier_idx, after_idx);
    }

    let checker = MemoryModelChecker::new(log, hb);
    let barrier = make_aarch64_barrier_fact(
        "dmb",
        Aarch64BarrierDomain::InnerShareable,
        Aarch64BarrierEffect::Full,
        MemoryOrderingSemantics::AcquireRelease,
        missing_witnesses,
    );

    checker.consume_aarch64_barrier_obligation(
        &barrier,
        Aarch64BarrierWitness {
            before_access_index: before_idx,
            barrier_access_index: barrier_idx,
            after_access_index: after_idx,
            observed_domain,
            observed_effect,
        },
    )
}

#[test]
fn test_aarch64_barrier_consumer_accepts_full_dmb_boundary() {
    let consumed = consume_barrier_boundary(
        Some(Aarch64BarrierDomain::InnerShareable),
        Some(Aarch64BarrierEffect::Full),
        true,
        true,
        MemoryOrdering::AcqRel,
        true,
        AARCH64_BARRIER_WITNESSES,
    );

    assert!(consumed.is_accepted());
    assert!(consumed.missing_witnesses.is_empty());
    for witness in AARCH64_BARRIER_WITNESSES {
        assert!(
            consumed.consumed_witnesses.contains(&(*witness).to_string()),
            "expected consumed barrier witness {witness}; got {:?}",
            consumed.consumed_witnesses
        );
    }
    assert!(consumed.diagnostic.contains("barrier proof-grade accepted"));
}

#[test]
fn test_aarch64_barrier_consumer_requires_domain_effect_and_program_order_witnesses() {
    let cases = [
        (
            "missing domain",
            None,
            Some(Aarch64BarrierEffect::Full),
            true,
            true,
            MemoryOrdering::AcqRel,
            true,
            "barrier domain witness",
        ),
        (
            "wrong effect",
            Some(Aarch64BarrierDomain::InnerShareable),
            Some(Aarch64BarrierEffect::Stores),
            true,
            true,
            MemoryOrdering::AcqRel,
            true,
            "barrier effect witness",
        ),
        (
            "weak fence ordering",
            Some(Aarch64BarrierDomain::InnerShareable),
            Some(Aarch64BarrierEffect::Full),
            true,
            true,
            MemoryOrdering::Acquire,
            true,
            "barrier ordering event",
        ),
        (
            "missing pre-barrier edge",
            Some(Aarch64BarrierDomain::InnerShareable),
            Some(Aarch64BarrierEffect::Full),
            false,
            true,
            MemoryOrdering::AcqRel,
            true,
            "pre-barrier program-order edge",
        ),
        (
            "missing post-barrier edge",
            Some(Aarch64BarrierDomain::InnerShareable),
            Some(Aarch64BarrierEffect::Full),
            true,
            false,
            MemoryOrdering::AcqRel,
            true,
            "post-barrier program-order edge",
        ),
        (
            "wrong thread",
            Some(Aarch64BarrierDomain::InnerShareable),
            Some(Aarch64BarrierEffect::Full),
            true,
            true,
            MemoryOrdering::AcqRel,
            false,
            "barrier thread identity",
        ),
    ];

    for (
        name,
        observed_domain,
        observed_effect,
        pre_edge,
        post_edge,
        barrier_ordering,
        same_thread,
        expected_missing,
    ) in cases
    {
        let consumed = consume_barrier_boundary(
            observed_domain,
            observed_effect,
            pre_edge,
            post_edge,
            barrier_ordering,
            same_thread,
            AARCH64_BARRIER_WITNESSES,
        );

        assert!(!consumed.is_accepted(), "{name} should remain fail-closed");
        assert!(
            consumed.missing_witnesses.contains(&expected_missing.to_string()),
            "{name} should miss {expected_missing}; got {:?}",
            consumed.missing_witnesses
        );
        assert!(consumed.diagnostic.contains("fail-closed"), "{name}");
        assert!(!consumed.diagnostic.contains("proof-grade accepted"), "{name}");
    }
}

#[test]
fn test_aarch64_barrier_consumer_fails_closed_on_unconsumed_fact_witness() {
    let mut witnesses = AARCH64_BARRIER_WITNESSES.to_vec();
    witnesses.push("future barrier-domain granule witness");

    let consumed = consume_barrier_boundary(
        Some(Aarch64BarrierDomain::InnerShareable),
        Some(Aarch64BarrierEffect::Full),
        true,
        true,
        MemoryOrdering::AcqRel,
        true,
        &witnesses,
    );

    assert!(!consumed.is_accepted());
    assert!(
        consumed.missing_witnesses.contains(&"future barrier-domain granule witness".to_string())
    );
    assert!(consumed.diagnostic.contains("fail-closed"));
    assert!(!consumed.diagnostic.contains("proof-grade accepted"));
}

#[test]
fn test_aarch64_sync_boundary_consumer_rejects_lifted_barrier_fact() {
    let checker = MemoryModelChecker::new(AtomicAccessLog::new(), HappensBefore::new(0));
    let dmb = make_aarch64_sync_fact(
        "dmb",
        Aarch64SyncBoundaryKind::DataMemoryBarrier,
        Aarch64SyncScope::InnerShareable,
        Aarch64SyncOrdering::LoadsAndStores,
        false,
        Some(0xb),
        &[
            "barrier ordering event",
            "shareability scope propagation",
            "memory-system visibility/completion",
            "happens-before witness",
        ],
    );

    let consumed = checker.consume_aarch64_sync_boundary_obligation(&dmb);

    assert!(!consumed.is_accepted());
    for witness in [
        "barrier ordering event",
        "shareability scope propagation",
        "memory-system visibility/completion",
        "happens-before witness",
        "proof model consumption",
    ] {
        assert!(
            consumed.missing_witnesses.contains(&witness.to_string()),
            "expected missing witness {witness}; got {:?}",
            consumed.missing_witnesses
        );
    }
    assert!(consumed.consumed_witnesses.is_empty());
    assert!(consumed.diagnostic.contains("opcode=dmb"));
    assert!(consumed.diagnostic.contains("fail-closed"));
}

#[test]
fn test_aarch64_sync_boundary_consumer_accepts_only_consumed_empty_witness_fact() {
    let checker = MemoryModelChecker::new(AtomicAccessLog::new(), HappensBefore::new(0));
    let mut consumed_isb = make_aarch64_sync_fact(
        "isb",
        Aarch64SyncBoundaryKind::InstructionSynchronizationBarrier,
        Aarch64SyncScope::FullSystem,
        Aarch64SyncOrdering::InstructionStream,
        false,
        Some(0xf),
        &[],
    );
    consumed_isb.consumed_by_proof_model = true;

    let consumed = checker.consume_aarch64_sync_boundary_obligation(&consumed_isb);

    assert!(consumed.is_accepted());
    assert!(consumed.missing_witnesses.is_empty());
    assert!(
        consumed.consumed_witnesses.contains(&"sync boundary proof model consumption".to_string())
    );
    assert!(consumed.diagnostic.contains("sync-boundary proof-grade accepted"));
}

// -----------------------------------------------------------------------
// Operation legality tests (L1-L5) — Part of #607
// -----------------------------------------------------------------------

/// Helper: build an AtomicOperation with given kind, ordering, and optional failure ordering.
fn make_atomic_op(
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

// -- L1: load cannot use Release or AcqRel --

#[test]
fn test_l1_load_release_is_illegal() {
    let ops = [make_atomic_op(AtomicOpKind::Load, AtomicOrdering::Release, None)];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "test_fn");
    assert_eq!(vcs.len(), 1, "load with Release should produce 1 violation");
    assert!(matches!(&vcs[0].kind, VcKind::InsufficientOrdering { .. }));
    assert!(vcs[0].kind.description().contains("L1"));
}

#[test]
fn test_l1_load_acqrel_is_illegal() {
    let ops = [make_atomic_op(AtomicOpKind::Load, AtomicOrdering::AcqRel, None)];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "test_fn");
    assert_eq!(vcs.len(), 1, "load with AcqRel should produce 1 violation");
}

#[test]
fn test_l1_load_acquire_is_legal() {
    let ops = [make_atomic_op(AtomicOpKind::Load, AtomicOrdering::Acquire, None)];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "test_fn");
    assert!(vcs.is_empty(), "load with Acquire is valid");
}

#[test]
fn test_l1_load_relaxed_is_legal() {
    let ops = [make_atomic_op(AtomicOpKind::Load, AtomicOrdering::Relaxed, None)];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "test_fn");
    assert!(vcs.is_empty(), "load with Relaxed is valid");
}

#[test]
fn test_l1_load_seqcst_is_legal() {
    let ops = [make_atomic_op(AtomicOpKind::Load, AtomicOrdering::SeqCst, None)];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "test_fn");
    assert!(vcs.is_empty(), "load with SeqCst is valid");
}

// -- L2: store cannot use Acquire or AcqRel --

#[test]
fn test_l2_store_acquire_is_illegal() {
    let ops = [make_atomic_op(AtomicOpKind::Store, AtomicOrdering::Acquire, None)];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "test_fn");
    assert_eq!(vcs.len(), 1, "store with Acquire should produce 1 violation");
    assert!(vcs[0].kind.description().contains("L2"));
}

#[test]
fn test_l2_store_acqrel_is_illegal() {
    let ops = [make_atomic_op(AtomicOpKind::Store, AtomicOrdering::AcqRel, None)];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "test_fn");
    assert_eq!(vcs.len(), 1, "store with AcqRel should produce 1 violation");
}

#[test]
fn test_l2_store_release_is_legal() {
    let ops = [make_atomic_op(AtomicOpKind::Store, AtomicOrdering::Release, None)];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "test_fn");
    assert!(vcs.is_empty(), "store with Release is valid");
}

#[test]
fn test_l2_store_relaxed_is_legal() {
    let ops = [make_atomic_op(AtomicOpKind::Store, AtomicOrdering::Relaxed, None)];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "test_fn");
    assert!(vcs.is_empty(), "store with Relaxed is valid");
}

#[test]
fn test_l2_store_seqcst_is_legal() {
    let ops = [make_atomic_op(AtomicOpKind::Store, AtomicOrdering::SeqCst, None)];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "test_fn");
    assert!(vcs.is_empty(), "store with SeqCst is valid");
}

// -- L3: CAS failure ordering cannot be Release or AcqRel --

#[test]
fn test_l3_cas_failure_release_is_illegal() {
    let ops = [make_atomic_op(
        AtomicOpKind::CompareExchange,
        AtomicOrdering::SeqCst,
        Some(AtomicOrdering::Release),
    )];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "test_fn");
    assert!(
        vcs.iter().any(|vc| vc.kind.description().contains("L3")),
        "CAS with failure=Release should trigger L3"
    );
}

#[test]
fn test_l3_cas_failure_acqrel_is_illegal() {
    let ops = [make_atomic_op(
        AtomicOpKind::CompareExchange,
        AtomicOrdering::SeqCst,
        Some(AtomicOrdering::AcqRel),
    )];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "test_fn");
    assert!(
        vcs.iter().any(|vc| vc.kind.description().contains("L3")),
        "CAS with failure=AcqRel should trigger L3"
    );
}

#[test]
fn test_l3_cas_failure_acquire_is_legal() {
    let ops = [make_atomic_op(
        AtomicOpKind::CompareExchange,
        AtomicOrdering::AcqRel,
        Some(AtomicOrdering::Acquire),
    )];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "test_fn");
    assert!(vcs.is_empty(), "CAS with failure=Acquire is valid when success=AcqRel");
}

#[test]
fn test_l3_cas_weak_failure_release_is_illegal() {
    let ops = [make_atomic_op(
        AtomicOpKind::CompareExchangeWeak,
        AtomicOrdering::SeqCst,
        Some(AtomicOrdering::Release),
    )];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "test_fn");
    assert!(
        vcs.iter().any(|vc| vc.kind.description().contains("L3")),
        "CAS weak with failure=Release should trigger L3"
    );
}

// -- L4: CAS failure ordering must be <= success ordering --

#[test]
fn test_l4_cas_failure_stronger_than_success() {
    // success=Relaxed, failure=Acquire: failure is stronger
    let ops = [make_atomic_op(
        AtomicOpKind::CompareExchange,
        AtomicOrdering::Relaxed,
        Some(AtomicOrdering::Acquire),
    )];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "test_fn");
    assert!(
        vcs.iter().any(|vc| vc.kind.description().contains("L4")),
        "CAS with failure stronger than success should trigger L4"
    );
}

#[test]
fn test_l4_cas_failure_equal_to_success_is_legal() {
    let ops = [make_atomic_op(
        AtomicOpKind::CompareExchange,
        AtomicOrdering::Acquire,
        Some(AtomicOrdering::Acquire),
    )];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "test_fn");
    assert!(vcs.is_empty(), "CAS with failure=success=Acquire is valid");
}

#[test]
fn test_l4_cas_failure_weaker_than_success_is_legal() {
    let ops = [make_atomic_op(
        AtomicOpKind::CompareExchange,
        AtomicOrdering::SeqCst,
        Some(AtomicOrdering::Relaxed),
    )];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "test_fn");
    assert!(vcs.is_empty(), "CAS with failure=Relaxed, success=SeqCst is valid");
}

#[test]
fn test_l4_cas_failure_seqcst_success_acquire() {
    // success=Acquire, failure=SeqCst: failure is strictly stronger
    let ops = [make_atomic_op(
        AtomicOpKind::CompareExchange,
        AtomicOrdering::Acquire,
        Some(AtomicOrdering::SeqCst),
    )];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "test_fn");
    assert!(
        vcs.iter().any(|vc| vc.kind.description().contains("L4")),
        "CAS with failure=SeqCst, success=Acquire should trigger L4"
    );
}

// -- L5: fence / compiler_fence cannot use Relaxed --

#[test]
fn test_l5_fence_relaxed_is_illegal() {
    let ops = [make_atomic_op(AtomicOpKind::Fence, AtomicOrdering::Relaxed, None)];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "test_fn");
    assert_eq!(vcs.len(), 1, "fence with Relaxed should produce 1 violation");
    assert!(vcs[0].kind.description().contains("L5"));
}

#[test]
fn test_l5_compiler_fence_relaxed_is_illegal() {
    let ops = [make_atomic_op(AtomicOpKind::CompilerFence, AtomicOrdering::Relaxed, None)];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "test_fn");
    assert_eq!(vcs.len(), 1, "compiler_fence with Relaxed should produce 1 violation");
    assert!(vcs[0].kind.description().contains("L5"));
}

#[test]
fn test_l5_fence_acquire_is_legal() {
    let ops = [make_atomic_op(AtomicOpKind::Fence, AtomicOrdering::Acquire, None)];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "test_fn");
    assert!(vcs.is_empty(), "fence with Acquire is valid");
}

#[test]
fn test_l5_fence_release_is_legal() {
    let ops = [make_atomic_op(AtomicOpKind::Fence, AtomicOrdering::Release, None)];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "test_fn");
    assert!(vcs.is_empty(), "fence with Release is valid");
}

#[test]
fn test_l5_fence_acqrel_is_legal() {
    let ops = [make_atomic_op(AtomicOpKind::Fence, AtomicOrdering::AcqRel, None)];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "test_fn");
    assert!(vcs.is_empty(), "fence with AcqRel is valid");
}

#[test]
fn test_l5_fence_seqcst_is_legal() {
    let ops = [make_atomic_op(AtomicOpKind::Fence, AtomicOrdering::SeqCst, None)];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "test_fn");
    assert!(vcs.is_empty(), "fence with SeqCst is valid");
}

// -- Valid operations produce no VCs --

#[test]
fn test_valid_operations_produce_no_vcs() {
    let ops = [
        make_atomic_op(AtomicOpKind::Load, AtomicOrdering::Acquire, None),
        make_atomic_op(AtomicOpKind::Store, AtomicOrdering::Release, None),
        make_atomic_op(AtomicOpKind::Fence, AtomicOrdering::SeqCst, None),
        make_atomic_op(
            AtomicOpKind::CompareExchange,
            AtomicOrdering::AcqRel,
            Some(AtomicOrdering::Acquire),
        ),
        make_atomic_op(AtomicOpKind::FetchAdd, AtomicOrdering::Relaxed, None),
    ];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "test_fn");
    assert!(vcs.is_empty(), "all valid operations should produce no VCs");
}

#[test]
fn test_empty_operations_produce_no_vcs() {
    let vcs = MemoryModelChecker::check_operation_legality(&[], "test_fn");
    assert!(vcs.is_empty());
}

#[test]
fn test_multiple_violations_in_one_pass() {
    let ops = [
        make_atomic_op(AtomicOpKind::Load, AtomicOrdering::Release, None), // L1
        make_atomic_op(AtomicOpKind::Store, AtomicOrdering::Acquire, None), // L2
        make_atomic_op(AtomicOpKind::Fence, AtomicOrdering::Relaxed, None), // L5
    ];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "multi_fn");
    assert_eq!(vcs.len(), 3, "should detect all 3 violations");
    assert_eq!(vcs[0].function, "multi_fn");
    assert_eq!(vcs[1].function, "multi_fn");
    assert_eq!(vcs[2].function, "multi_fn");
}

#[test]
fn test_l3_and_l4_can_fire_together_on_same_cas() {
    // CAS with success=Relaxed, failure=Release: L3 (Release forbidden) and L4 (failure > success)
    let ops = [make_atomic_op(
        AtomicOpKind::CompareExchange,
        AtomicOrdering::Relaxed,
        Some(AtomicOrdering::Release),
    )];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "test_fn");
    assert!(vcs.len() >= 2, "should fire both L3 and L4");
    assert!(vcs.iter().any(|vc| vc.kind.description().contains("L3")));
    assert!(vcs.iter().any(|vc| vc.kind.description().contains("L4")));
}

#[test]
fn test_rmw_operations_not_affected_by_l1_l2() {
    // RMW ops (fetch_add, exchange) accept all orderings including AcqRel/Release/Acquire.
    let ops = [
        make_atomic_op(AtomicOpKind::FetchAdd, AtomicOrdering::Release, None),
        make_atomic_op(AtomicOpKind::FetchAdd, AtomicOrdering::Acquire, None),
        make_atomic_op(AtomicOpKind::FetchAdd, AtomicOrdering::AcqRel, None),
        make_atomic_op(AtomicOpKind::Exchange, AtomicOrdering::Release, None),
    ];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "test_fn");
    assert!(vcs.is_empty(), "RMW operations accept all orderings");
}

#[test]
fn test_legality_vc_has_insufficient_ordering_kind() {
    let ops = [make_atomic_op(AtomicOpKind::Load, AtomicOrdering::Release, None)];
    let vcs = MemoryModelChecker::check_operation_legality(&ops, "my_fn");
    assert_eq!(vcs.len(), 1);
    match &vcs[0].kind {
        VcKind::InsufficientOrdering { variable, actual, required } => {
            assert_eq!(variable, "_0");
            assert_eq!(actual, "Release");
            assert!(required.contains("L1"));
        }
        other => panic!("expected InsufficientOrdering, got: {other:?}"),
    }
    assert_eq!(
        vcs[0].formula,
        Formula::Var(crate::generated_formula_symbol("memory_ordering", "reach__0"), Sort::Bool,)
    );
}

// -----------------------------------------------------------------------
// HappensBeforeGraph tests
// -----------------------------------------------------------------------

#[test]
fn test_hb_graph_empty() {
    let graph = HappensBeforeGraph::new();
    assert_eq!(graph.node_count(), 0);
    assert_eq!(graph.edge_count(), 0);
}

#[test]
fn test_hb_graph_add_nodes() {
    let mut graph = HappensBeforeGraph::new();
    let p1 = ConcurrencyPoint::new("fn_a", trust_types::BlockId(0), "main");
    let p2 = ConcurrencyPoint::new("fn_a", trust_types::BlockId(1), "main");

    let idx1 = graph.add_node(p1.clone());
    let idx2 = graph.add_node(p2.clone());
    assert_eq!(idx1, 0);
    assert_eq!(idx2, 1);
    assert_eq!(graph.node_count(), 2);

    // Adding the same point again returns existing index.
    let idx1_again = graph.add_node(p1);
    assert_eq!(idx1_again, 0);
    assert_eq!(graph.node_count(), 2);
}

#[test]
fn test_hb_graph_program_order() {
    let mut graph = HappensBeforeGraph::new();
    let p0 = ConcurrencyPoint::new("fn_a", trust_types::BlockId(0), "main");
    let p1 = ConcurrencyPoint::new("fn_a", trust_types::BlockId(1), "main");
    let p2 = ConcurrencyPoint::new("fn_a", trust_types::BlockId(2), "main");

    graph.add_node(p0.clone());
    graph.add_node(p1.clone());
    graph.add_node(p2.clone());

    graph.add_edge(&p0, &p1, HappensBeforeEdgeKind::ProgramOrder);
    graph.add_edge(&p1, &p2, HappensBeforeEdgeKind::ProgramOrder);

    assert!(graph.happens_before(&p0, &p1));
    assert!(graph.happens_before(&p1, &p2));
    assert!(graph.happens_before(&p0, &p2), "transitive HB");
    assert!(!graph.happens_before(&p2, &p0), "no reverse HB");
}

#[test]
fn test_hb_graph_spawn_join_edges() {
    let mut graph = HappensBeforeGraph::new();

    // Main thread: spawn at bb0, work at bb1, join at bb2
    let main_spawn = ConcurrencyPoint::new("main_fn", trust_types::BlockId(0), "main");
    let main_work = ConcurrencyPoint::new("main_fn", trust_types::BlockId(1), "main");
    let main_join = ConcurrencyPoint::new("main_fn", trust_types::BlockId(2), "main");

    // Child thread: entry at bb0, work at bb1, exit at bb2
    let child_entry = ConcurrencyPoint::new("worker_fn", trust_types::BlockId(0), "child");
    let child_work = ConcurrencyPoint::new("worker_fn", trust_types::BlockId(1), "child");
    let child_exit = ConcurrencyPoint::new("worker_fn", trust_types::BlockId(2), "child");

    for p in [&main_spawn, &main_work, &main_join, &child_entry, &child_work, &child_exit] {
        graph.add_node(p.clone());
    }

    // Main thread program order
    graph.add_edge(&main_spawn, &main_work, HappensBeforeEdgeKind::ProgramOrder);
    graph.add_edge(&main_work, &main_join, HappensBeforeEdgeKind::ProgramOrder);

    // Child thread program order
    graph.add_edge(&child_entry, &child_work, HappensBeforeEdgeKind::ProgramOrder);
    graph.add_edge(&child_work, &child_exit, HappensBeforeEdgeKind::ProgramOrder);

    // Spawn: main_spawn -> child_entry
    graph.add_edge(&main_spawn, &child_entry, HappensBeforeEdgeKind::Spawn);

    // Join: child_exit -> main_join
    graph.add_edge(&child_exit, &main_join, HappensBeforeEdgeKind::Join);

    // Test HB relationships
    assert!(graph.happens_before(&main_spawn, &child_entry), "spawn HB");
    assert!(graph.happens_before(&child_exit, &main_join), "join HB");
    assert!(
        graph.happens_before(&main_spawn, &child_exit),
        "transitive: spawn -> child PO -> exit"
    );
    assert!(
        graph.happens_before(&child_entry, &main_join),
        "transitive: child entry -> PO -> exit -> join"
    );

    // Non-ordered pairs (concurrent)
    assert!(!graph.are_ordered(&main_work, &child_work), "main_work and child_work are concurrent");
}

#[test]
fn test_hb_graph_sync_with_edge() {
    let mut graph = HappensBeforeGraph::new();

    let release = ConcurrencyPoint::new("fn_a", trust_types::BlockId(0), "t1");
    let acquire = ConcurrencyPoint::new("fn_b", trust_types::BlockId(0), "t2");

    graph.add_node(release.clone());
    graph.add_node(acquire.clone());
    graph.add_edge(&release, &acquire, HappensBeforeEdgeKind::SyncWith);

    assert!(graph.happens_before(&release, &acquire));
    assert_eq!(graph.edge_kind(&release, &acquire), Some(HappensBeforeEdgeKind::SyncWith));
}

#[test]
fn test_hb_graph_edge_kind_query() {
    let mut graph = HappensBeforeGraph::new();
    let p0 = ConcurrencyPoint::new("fn", trust_types::BlockId(0), "main");
    let p1 = ConcurrencyPoint::new("fn", trust_types::BlockId(1), "main");
    let p2 = ConcurrencyPoint::new("fn", trust_types::BlockId(2), "child");

    graph.add_node(p0.clone());
    graph.add_node(p1.clone());
    graph.add_node(p2.clone());

    graph.add_edge(&p0, &p1, HappensBeforeEdgeKind::ProgramOrder);
    graph.add_edge(&p0, &p2, HappensBeforeEdgeKind::Spawn);

    assert_eq!(graph.edge_kind(&p0, &p1), Some(HappensBeforeEdgeKind::ProgramOrder));
    assert_eq!(graph.edge_kind(&p0, &p2), Some(HappensBeforeEdgeKind::Spawn));
    assert_eq!(graph.edge_kind(&p1, &p2), None);
}

#[test]
fn test_hb_graph_reflexive() {
    let mut graph = HappensBeforeGraph::new();
    let p = ConcurrencyPoint::new("fn", trust_types::BlockId(0), "main");
    graph.add_node(p.clone());

    assert!(graph.happens_before(&p, &p), "reflexive HB");
}

#[test]
fn test_hb_graph_unknown_point_returns_false() {
    let graph = HappensBeforeGraph::new();
    let p1 = ConcurrencyPoint::new("fn", trust_types::BlockId(0), "main");
    let p2 = ConcurrencyPoint::new("fn", trust_types::BlockId(1), "main");

    assert!(!graph.happens_before(&p1, &p2));
    assert!(!graph.are_ordered(&p1, &p2));
}

#[test]
fn test_hb_graph_point_at() {
    let mut graph = HappensBeforeGraph::new();
    let p0 = ConcurrencyPoint::new("fn_a", trust_types::BlockId(0), "main");
    let p1 = ConcurrencyPoint::new("fn_a", trust_types::BlockId(1), "main");

    graph.add_node(p0.clone());
    graph.add_node(p1.clone());

    assert_eq!(graph.point_at(0), Some(&p0));
    assert_eq!(graph.point_at(1), Some(&p1));
    assert_eq!(graph.point_at(99), None);
}

// -----------------------------------------------------------------------
// build_happens_before integration tests
// -----------------------------------------------------------------------

/// Build a mock function with a spawn and a join for HB graph testing.
fn make_spawn_join_function() -> trust_types::VerifiableFunction {
    trust_types::VerifiableFunction {
        name: "spawner".to_string(),
        def_path: "test::spawner".to_string(),
        span: trust_types::SourceSpan::default(),
        body: trust_types::VerifiableBody {
            locals: vec![
                trust_types::LocalDecl { index: 0, ty: trust_types::Ty::Unit, name: None },
                trust_types::LocalDecl {
                    index: 1,
                    ty: trust_types::Ty::Unit,
                    name: Some("closure".into()),
                },
                trust_types::LocalDecl {
                    index: 2,
                    ty: trust_types::Ty::Unit,
                    name: Some("handle".into()),
                },
                trust_types::LocalDecl {
                    index: 3,
                    ty: trust_types::Ty::Unit,
                    name: Some("result".into()),
                },
            ],
            blocks: vec![
                // bb0: spawn
                trust_types::BasicBlock {
                    id: trust_types::BlockId(0),
                    stmts: vec![],
                    terminator: trust_types::Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::thread::spawn::<closure>".into(),
                        args: vec![trust_types::Operand::Move(trust_types::Place::local(1))],
                        dest: trust_types::Place::local(2),
                        target: Some(trust_types::BlockId(1)),
                        span: trust_types::SourceSpan::default(),
                        atomic: None,
                    },
                },
                // bb1: some work in main thread
                trust_types::BasicBlock {
                    id: trust_types::BlockId(1),
                    stmts: vec![],
                    terminator: trust_types::Terminator::Goto(trust_types::BlockId(2)),
                },
                // bb2: join
                trust_types::BasicBlock {
                    id: trust_types::BlockId(2),
                    stmts: vec![],
                    terminator: trust_types::Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::thread::JoinHandle::<()>::join".into(),
                        args: vec![trust_types::Operand::Move(trust_types::Place::local(2))],
                        dest: trust_types::Place::local(3),
                        target: Some(trust_types::BlockId(3)),
                        span: trust_types::SourceSpan::default(),
                        atomic: None,
                    },
                },
                // bb3: return
                trust_types::BasicBlock {
                    id: trust_types::BlockId(3),
                    stmts: vec![],
                    terminator: trust_types::Terminator::Return,
                },
            ],
            arg_count: 0,
            return_ty: trust_types::Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn test_build_happens_before_with_spawn_join() {
    let func = make_spawn_join_function();
    let log = AtomicAccessLog::new();
    let hb = HappensBefore::new(0);
    let checker = MemoryModelChecker::new(log, hb);

    let graph = checker.build_happens_before(&[&func]);

    // Should have nodes for all 4 blocks in main thread + spawn/join synthetic points
    assert!(graph.node_count() >= 4, "should have at least 4 nodes, got {}", graph.node_count());

    // Program-order edges exist within main thread
    let bb0 = ConcurrencyPoint::new("test::spawner", trust_types::BlockId(0), "main");
    let bb1 = ConcurrencyPoint::new("test::spawner", trust_types::BlockId(1), "main");
    let bb2 = ConcurrencyPoint::new("test::spawner", trust_types::BlockId(2), "main");
    let bb3 = ConcurrencyPoint::new("test::spawner", trust_types::BlockId(3), "main");

    assert!(graph.happens_before(&bb0, &bb1), "bb0 -> bb1 (program order)");
    assert!(graph.happens_before(&bb1, &bb2), "bb1 -> bb2 (program order)");
    assert!(graph.happens_before(&bb2, &bb3), "bb2 -> bb3 (program order)");
    assert!(graph.happens_before(&bb0, &bb3), "bb0 -> bb3 (transitive)");

    // Spawn edge should exist
    let child_entry =
        ConcurrencyPoint::new("test::spawner", trust_types::BlockId(0), "spawned_at_bb0");
    assert!(graph.happens_before(&bb0, &child_entry), "spawn point should HB child entry");
}

#[test]
fn test_build_happens_before_empty_function() {
    let func = trust_types::VerifiableFunction {
        name: "empty".to_string(),
        def_path: "test::empty".to_string(),
        span: trust_types::SourceSpan::default(),
        body: trust_types::VerifiableBody {
            locals: vec![trust_types::LocalDecl {
                index: 0,
                ty: trust_types::Ty::Unit,
                name: None,
            }],
            blocks: vec![trust_types::BasicBlock {
                id: trust_types::BlockId(0),
                stmts: vec![],
                terminator: trust_types::Terminator::Return,
            }],
            arg_count: 0,
            return_ty: trust_types::Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let log = AtomicAccessLog::new();
    let hb = HappensBefore::new(0);
    let checker = MemoryModelChecker::new(log, hb);

    let graph = checker.build_happens_before(&[&func]);
    assert_eq!(graph.node_count(), 1);
    assert_eq!(graph.edge_count(), 0);
}

#[test]
fn test_build_happens_before_with_release_acquire() {
    let mut log = AtomicAccessLog::new();
    log.record(make_atomic_entry("flag", AccessKind::AtomicWrite(MemoryOrdering::Release), "t1"));
    log.record(make_atomic_entry("flag", AccessKind::AtomicRead(MemoryOrdering::Acquire), "t2"));

    let hb = HappensBefore::new(2);
    let checker = MemoryModelChecker::new(log, hb);

    let graph = checker.build_happens_before(&[]);

    // Should have release-acquire sync edge
    assert!(graph.edge_count() >= 1, "should have at least 1 sync edge");

    // Find the release and acquire points and verify HB
    let release = ConcurrencyPoint::new("flag", trust_types::BlockId(0), "t1");
    let acquire = ConcurrencyPoint::new("flag", trust_types::BlockId(1), "t2");
    assert!(graph.happens_before(&release, &acquire), "release should HB acquire");
    assert_eq!(graph.edge_kind(&release, &acquire), Some(HappensBeforeEdgeKind::SyncWith));
}

#[test]
fn test_build_happens_before_fails_closed_on_invalid_release_acquire_evidence() {
    let release = make_atomic_entry("flag", AccessKind::AtomicWrite(MemoryOrdering::Release), "t1");
    let invalid_evidence = make_atomic_entry("data", AccessKind::Write, "t3");
    let acquire = make_atomic_entry("flag", AccessKind::AtomicRead(MemoryOrdering::Acquire), "t2");
    let log: AtomicAccessLog = serde_json::from_value(serde_json::json!({
        "entries": [release, invalid_evidence, acquire]
    }))
    .expect("deserialization can bypass AtomicAccessLog::record");

    let hb = HappensBefore::new(3);
    let checker = MemoryModelChecker::new(log, hb);
    let graph = checker.build_happens_before(&[]);

    let release = ConcurrencyPoint::new("flag", trust_types::BlockId(0), "t1");
    let acquire = ConcurrencyPoint::new("flag", trust_types::BlockId(2), "t2");
    assert_eq!(graph.edge_count(), 0);
    assert!(!graph.happens_before(&release, &acquire));
    assert_eq!(graph.edge_kind(&release, &acquire), None);
}

#[test]
fn test_build_happens_before_with_rmw_release_acquire() {
    let mut log = AtomicAccessLog::new();
    log.record(make_atomic_entry(
        "counter",
        AccessKind::AtomicRmw(MemoryOrdering::Release, AtomicRmwOp::Add),
        "t1",
    ));
    log.record(make_atomic_entry(
        "counter",
        AccessKind::AtomicRmw(MemoryOrdering::Acquire, AtomicRmwOp::Add),
        "t2",
    ));

    let hb = HappensBefore::new(2);
    let checker = MemoryModelChecker::new(log, hb);

    let graph = checker.build_happens_before(&[]);

    let release = ConcurrencyPoint::new("counter", trust_types::BlockId(0), "t1");
    let acquire = ConcurrencyPoint::new("counter", trust_types::BlockId(1), "t2");
    assert!(graph.happens_before(&release, &acquire), "RMW release should HB RMW acquire");
    assert_eq!(graph.edge_kind(&release, &acquire), Some(HappensBeforeEdgeKind::SyncWith));
}
