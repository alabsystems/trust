// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use super::*;

fn replay(index: usize, fixture: &str) {
    let formula: Formula = serde_json::from_str(fixture).expect("typed frontend fixture");
    let backend = InProcessAyBackend::new().with_timeout(30_000);
    let program = backend.build_program(&formula).expect("typed formula translates to AY");
    let outcomes = {
        let _guard = ay_exec_lock().lock().unwrap_or_else(|error| error.into_inner());
        execute_direct::execute_incremental(&program).expect("native program executes")
    };
    assert_eq!(outcomes.len(), 1);
    let artifact = outcomes[0].unsat_proof.as_ref().expect("native UNSAT proof");
    artifact
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .expect("native strict checker accepts");
    assert_eq!(artifact.quality.trust_count, 0);
    let problem = problem_smt2(&formula);
    println!(
        "NATIVE_ALLOCATION_CERTIFICATE={}",
        serde_json::json!({
            "index": index,
            "type": "alethe_certificate",
            "version": "1.0",
            "problem": problem,
            "proof": artifact.alethe,
        })
    );
    let checked = clean_auto::bridge::ay_contract::verify_alethe_proof(&problem, &artifact.alethe);
    assert!(matches!(checked, Ok(true)), "allocation-{index}: {checked:?}");
}

#[test]
fn allocation_u32_native_artifact_replays() {
    replay(0, include_str!("../../tests/fixtures/frontend_allocation/allocation-0.json"));
}

#[test]
fn allocation_i64_native_artifact_replays() {
    replay(1, include_str!("../../tests/fixtures/frontend_allocation/allocation-1.json"));
}

#[test]
fn allocation_bool_native_artifact_replays() {
    replay(2, include_str!("../../tests/fixtures/frontend_allocation/allocation-2.json"));
}
