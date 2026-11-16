//! Carrier DATA-state controls only. No Host, live Root/Graph, namespace,
//! materialization, native ACK/completion, semantic Seed or SDK is fabricated.
use super::*;
use crate::bootstrap_graph::offline_preparation::StagedSelection;

fn intent() -> StagedIntent {
    StagedIntent { key: crate::bootstrap_graph::query::tests::request().key,
        selection: StagedSelection { source_root: b"/source".to_vec(),
            output_root: b"/output".to_vec(), environment: vec![
                (b"CARGO_NET_OFFLINE".to_vec(), b"true".to_vec()),
                (b"CARGO_HOME".to_vec(), vec![]),
                (b"TARGO_HOME".to_vec(), b"/native-home".to_vec()),
            ], budget_ns: 60_000_000_000 } }
}
fn staged_attempt() -> (StagedAttempt, QueryState, StagedIntent) {
    let intent = intent();
    let mut queries = QueryState::new(); queries.reserve_offline().unwrap();
    let mut attempt = StagedAttempt::new(StagedIntentQuery { key: intent.key.graph.clone() },
        Instant::now() + Duration::from_secs(120));
    let reply = StagedIntentReply { query: attempt.query.clone(), intent: intent.clone(),
        remaining_root_ns: 60_000_000_000 };
    let reply = StagedIntentReply::decode(&reply.encode().unwrap(), &attempt.query).unwrap();
    attempt.observe_intent(reply, Instant::now()).unwrap();
    attempt.acknowledged = true; // DATA fixture; production requires real EOF/peer checks/ACK.
    (attempt, queries, intent)
}
fn reservation(attempt: &StagedAttempt, remaining_root_ns: u64) -> ReservedPrograms {
    let query = attempt.reservation_query().unwrap();
    let reply = ReservedPrograms { query: query.clone(), namespace: b"/output/private-child".to_vec(),
        remaining_root_ns };
    ReservedPrograms::decode(&reply.encode().unwrap(), &query).unwrap()
}
fn programs(intent: &StagedIntent) -> ProgramSelection {
    ProgramSelection { key: intent.key.clone(), configured_targo: b"/output/private-child/bin/cargo".to_vec(),
        configured_compiler: b"/output/private-child/bin/trustc".to_vec() }
}
fn program_reply(selection: &ProgramSelection, remaining_root_ns: u64) -> ProgramSelectionReply {
    let reply = ProgramSelectionReply { selection: selection.clone(),
        namespace: b"/output/private-child".to_vec(), remaining_root_ns };
    ProgramSelectionReply::decode(&reply.encode().unwrap(), selection).unwrap()
}

#[test]
fn staged_carrier_acknowledgements_cannot_complete_the_native_operation() {
    let (mut attempt, mut queries, intent) = staged_attempt();
    assert!(attempt.complete().is_none());
    let reserved = reservation(&attempt, 30_000_000_000);
    attempt.observe_reservation(reserved, Instant::now()).unwrap();
    assert!(attempt.complete().is_none());
    attempt.reservation_retained = true; // DATA state only; production retains the SAME open carrier
    let selected = programs(&intent); attempt.select(&selected).unwrap();
    attempt.observe_programs(program_reply(&selected, 20_000_000_000), Instant::now()).unwrap();
    assert!(attempt.complete().is_none());
    attempt.programs_acknowledged = true; // DATA state only
    let complete = attempt.complete().unwrap();
    assert!(complete.key == intent.key);
    assert!(complete.selection.environment == intent.selection.environment);
    assert!(complete.selection.configured_targo == selected.configured_targo);
    assert!(queries.check(1).is_err()); assert!(queries.check(2).is_err());
    assert!(queries.begin().is_err()); assert!(queries.reserve_offline().is_err());
}
#[test]
fn staged_namespace_reconnect_only_restricts_the_original_endpoint() {
    let (mut attempt, queries, intent) = staged_attempt();
    let first = reservation(&attempt, 30_000_000_000);
    attempt.observe_reservation(first, Instant::now()).unwrap();
    let original = attempt.deadline;
    let repeat = reservation(&attempt, 60_000_000_000);
    attempt.observe_reservation(repeat, Instant::now()).unwrap();
    assert_eq!(attempt.deadline, original);
    assert!(attempt.binding(&intent.key.graph, &queries, original + Duration::from_secs(1)).is_err());
    let shorter = reservation(&attempt, 10_000_000_000);
    attempt.observe_reservation(shorter, Instant::now()).unwrap();
    assert!(attempt.deadline < original);
}

#[test]
fn expired_program_observations_keep_the_restrictive_endpoint_before_refusal() {
    let started = Instant::now() - Duration::from_secs(2);
    let (mut attempt, _, _) = staged_attempt();
    let expired = reservation(&attempt, 1);
    assert!(attempt.observe_reservation(expired, started).is_err());
    assert!(attempt.deadline < Instant::now());
    assert!(attempt.failed);

    let (mut attempt, _, intent) = staged_attempt();
    let reserved = reservation(&attempt, 30_000_000_000);
    attempt.observe_reservation(reserved, Instant::now()).unwrap();
    attempt.reservation_retained = true; // private DATA state, no Host/SDK constructor
    let selected = programs(&intent);
    attempt.select(&selected).unwrap();
    assert!(attempt.observe_programs(program_reply(&selected, 1), started).is_err());
    assert!(attempt.deadline < Instant::now());
    assert!(attempt.failed && attempt.complete().is_none());
}
#[test]
fn changed_namespace_permanently_refuses_restored_reconnect() {
    let (mut attempt, queries, intent) = staged_attempt();
    let original = reservation(&attempt, 30_000_000_000);
    attempt.observe_reservation(original.clone(), Instant::now()).unwrap();
    let mut changed = original.clone(); changed.namespace = b"/output/another-child".to_vec();
    assert!(attempt.observe_reservation(changed, Instant::now()).is_err());
    assert!(attempt.observe_reservation(original, Instant::now()).is_err());
    assert!(attempt.ready(&intent.key.graph, &queries, Instant::now()).is_err());
    assert!(attempt.reserved.is_some());
}
#[test]
fn program_selection_freezes_before_connect_and_wrong_attempt_cannot_recover() {
    let (mut attempt, _, intent) = staged_attempt();
    let reserved = reservation(&attempt, 30_000_000_000);
    attempt.observe_reservation(reserved, Instant::now()).unwrap();
    attempt.reservation_retained = true;
    let selected = programs(&intent); attempt.select(&selected).unwrap();
    attempt.select(&selected).unwrap(); // same DATA intent, not a new attempt
    let mut changed = selected.clone(); changed.configured_targo = b"/output/private-child/bin/targo".to_vec();
    assert!(attempt.select(&changed).is_err()); assert!(attempt.select(&selected).is_err());
    assert!(attempt.programs.as_ref() == Some(&selected));
    assert!(attempt.complete().is_none());
}
#[test]
fn unacknowledged_or_foreign_reservation_cannot_select_programs() {
    let (mut attempt, _, intent) = staged_attempt();
    let selected = programs(&intent);
    assert!(attempt.select(&selected).is_err());
    assert!(attempt.programs.is_none());
    let (mut attempt, _, intent) = staged_attempt();
    let mut foreign = reservation(&attempt, 30_000_000_000);
    foreign.query.key.operation = [91;16];
    assert!(attempt.observe_reservation(foreign, Instant::now()).is_err());
    assert!(attempt.select(&programs(&intent)).is_err());
    assert!(attempt.complete().is_none());
}
