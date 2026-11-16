//! Private carrier-state controls. No admitted Host/Root or live graph is made.
use super::*;

fn intent() -> Intent {
    Intent {
        key: crate::bootstrap_graph::query::tests::request().key,
        selection: crate::bootstrap_graph::offline_preparation::IntentSelection {
            source_root: b"/source".to_vec(),
            output_root: b"/output".to_vec(),
            configured_targo: b"/source/build/stage0/bin/cargo".to_vec(),
            configured_compiler: b"/source/build/stage0/bin/trustc".to_vec(),
            environment: vec![(b"CARGO_NET_OFFLINE".to_vec(), b"true".to_vec())],
            budget_ns: 60_000_000_000,
        },
    }
}
fn attempt(intent: &Intent, queries: &mut QueryState) -> IntentAttempt {
    queries.reserve_offline().unwrap();
    let started = Instant::now();
    IntentAttempt {
        query: IntentQuery { key: intent.key.graph.clone() },
        started,
        deadline: started + Duration::from_secs(120),
        intent: None,
        acknowledged: false,
        failed: false,
    }
}
fn reply(intent: &Intent, remaining_root_ns: u64) -> IntentReply {
    IntentReply {
        query: IntentQuery { key: intent.key.graph.clone() },
        intent: intent.clone(),
        remaining_root_ns,
    }
}
#[test]
fn carrier_ack_never_completes_the_reserved_native_operation() {
    let intent = intent();
    let mut queries = QueryState::new();
    let mut attempt = attempt(&intent, &mut queries);
    assert!(queries.check(1).is_err());
    assert!(queries.begin().is_err());
    assert!(queries.reserve_offline().is_err());
    queries.enrollment_allowed().unwrap();
    let at = Instant::now() + Duration::from_secs(1);
    assert!(attempt.ready(&intent.key.graph, &queries, at).is_err());
    attempt.observe(reply(&intent, 60_000_000_000), Instant::now()).unwrap();
    assert!(attempt.ready(&intent.key.graph, &queries, at).is_err());
    attempt.acknowledged = true; // DATA-state only; production requires real EOF/ACK.
    attempt.ready(&intent.key.graph, &queries, at).unwrap();
    assert!(queries.check(1).is_err());
    assert!(queries.check(2).is_err());
    assert!(queries.begin().is_err());
    let mut enrollment = Enrollment {
        key: intent.key.graph.clone(),
        source: intent.selection.source_root.clone(),
        output: intent.selection.output_root.clone(),
        gnu: crate::bootstrap_graph::query::tests::request().gnu,
    };
    attempt.enrolled(&enrollment, &queries, at).unwrap();
    enrollment.source.push(b'x');
    assert!(attempt.enrolled(&enrollment, &queries, at).is_err());
}
#[test]
fn reconnect_can_only_shorten_the_same_original_endpoint() {
    let intent = intent();
    let mut queries = QueryState::new();
    let mut attempt = attempt(&intent, &mut queries);
    let initial_started = attempt.started;
    attempt.observe(reply(&intent, 90_000_000_000), initial_started).unwrap();
    assert_eq!(attempt.deadline, initial_started + Duration::from_secs(60));
    let original_end = attempt.deadline;
    attempt.observe(reply(&intent, 90_000_000_000), Instant::now()).unwrap();
    assert_eq!(attempt.deadline, original_end);
    let at = Instant::now();
    attempt.observe(reply(&intent, 30_000_000_000), at).unwrap();
    assert_eq!(attempt.deadline, at + Duration::from_secs(30));
    assert!(attempt.binding(&intent.key.graph, &queries, original_end).is_err());
}
#[test]
fn changed_intent_permanently_refuses_restored_replay_on_same_support() {
    let intent = intent();
    let mut queries = QueryState::new();
    let mut attempt = attempt(&intent, &mut queries);
    attempt.observe(reply(&intent, 60_000_000_000), Instant::now()).unwrap();
    let mut changed = intent.clone();
    changed.selection.environment.push((b"SECRET_PRESENT".to_vec(), vec![]));
    assert!(attempt.observe(reply(&changed, 60_000_000_000), Instant::now()).is_err());
    assert!(attempt.observe(reply(&intent, 60_000_000_000), Instant::now()).is_err());
    attempt.acknowledged = true;
    assert!(attempt.ready(&intent.key.graph, &queries, Instant::now()).is_err());
    assert!(queries.begin().is_err());
}
#[test]
fn intent_cannot_borrow_a_previous_querys_or_foreign_support_reservation() {
    let intent = intent();
    let mut ordinary = QueryState::new();
    ordinary.begin().unwrap();
    assert!(ordinary.reserve_offline().is_err());
    let mut queries = QueryState::new();
    let attempt = attempt(&intent, &mut queries);
    let mut foreign = intent.key.graph.clone();
    foreign.graph[0] ^= 1;
    assert!(attempt.binding(&foreign, &queries, Instant::now()).is_err());
    assert!(attempt.binding(&intent.key.graph, &QueryState::new(), Instant::now()).is_err());
}
