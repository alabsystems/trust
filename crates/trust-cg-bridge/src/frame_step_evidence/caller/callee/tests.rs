// Copyright 2026 Andrew Yates | Apache-2.0
use super::*;
use crate::compiler_input_capture::historical_b8_data_for_tests;

const CALLER: &str = "source_memory_caller";

fn guarded<T>(f: impl FnOnce() -> T) -> T {
    crate::original_conjunction_certificate::without_production(|| {
        super::super::super::terms::forbid_production(f)
    })
}

#[test]
fn actual_callee_byte_store_derives_conditional_frame_agreement() {
    std::thread::Builder::new().stack_size(32 << 20).spawn(check_actual).unwrap().join().unwrap();
}

#[test]
fn callee_data_trace_refuses_a_conditional_path_that_skips_the_store() {
    let data = historical_b8_data_for_tests();
    let original = guarded(|| binding::observe(&data.input(), CALLER).unwrap());
    assert_eq!(original.subject.store_step, 2);

    // CBZ x2,+12 and TBZ w2,#0,+12 both retain all five structurally
    // reachable instructions, but a taken branch skips the byte store.
    // A linear data-effect trace must not stand in for either path.
    for word in [0xb4000062u32, 0x36000062u32] {
        let mut changed = historical_b8_data_for_tests();
        let callee = BoundFunction::bind(
            &changed.object,
            &changed.m_cg,
            &original.subject.caller.callee_symbol,
            changed.relocation,
        )
        .unwrap();
        let code = callee.window().code.clone();
        let locations = changed
            .object
            .windows(code.len())
            .enumerate()
            .filter_map(|(index, bytes)| (bytes == code).then_some(index))
            .collect::<Vec<_>>();
        assert_eq!(locations.len(), 1);
        changed.object[locations[0]..locations[0] + 4].copy_from_slice(&word.to_le_bytes());
        let rebound = BoundFunction::bind(
            &changed.object,
            &changed.m_cg,
            &original.subject.caller.callee_symbol,
            changed.relocation,
        )
        .unwrap();
        assert_eq!(rebound.window().reachable.len(), 5);
        assert!(rebound.window().sites.is_empty());
        let refusal = guarded(|| binding::observe(&changed.input(), CALLER))
            .err()
            .expect("conditional callee must not become a linear data trace");
        assert!(
            refusal.starts_with("callee control flow is not straight-line before final RET:"),
            "unexpected refusal for conditional instruction {word:#010x}: {refusal}"
        );
    }
}

#[test]
fn original_callee_frame_packet_replays_without_production() {
    std::thread::Builder::new()
        .stack_size(32 << 20)
        .spawn(|| {
            let directory = std::path::PathBuf::from(
                std::env::var_os("TRUST_CALLEE_FRAME_COHORT")
                    .expect("actual callee cohort required"),
            );
            let data = historical_b8_data_for_tests();
            let packet = SeparateCalleeFramePacket::from_bytes(include_bytes!(
                "actual-separate-frame-packet.json"
            ))
            .unwrap();
            let fresh = CalleeFrameEnvironment::open(&directory).unwrap();
            guarded(|| fresh.replay_separate_callee(&packet, &data.input()).unwrap());
        })
        .unwrap()
        .join()
        .unwrap();
}

fn check_actual() {
    let directory = std::path::PathBuf::from(
        std::env::var_os("TRUST_CALLEE_FRAME_COHORT").expect("actual callee cohort required"),
    );
    let data = historical_b8_data_for_tests();
    // Retain the exact original real-data-effect control, including the
    // saved-LR alias which corrupts the eventual caller return target.
    super::super::tests::actual_callee_alias_control(&data.input());
    let normal = crate::call_event::verify_compiled_module(&data.input()).unwrap();
    let grades = normal
        .certificates
        .iter()
        .map(|row| (row.symbol.clone(), row.grade.clone()))
        .collect::<Vec<_>>();
    assert!(
        !normal.certificates.iter().find(|row| row.symbol == CALLER).unwrap().verdict.is_proven()
    );

    let trace = guarded(|| binding::observe(&data.input(), CALLER).unwrap());
    assert_eq!(trace.subject.store_step, 2);
    assert_eq!(trace.before.sp, trace.after.sp);
    let environment = CalleeFrameEnvironment::open(&directory).unwrap();
    let checked = environment.prove_separate_callee(&data.input(), CALLER).unwrap();
    let packet =
        SeparateCalleeFramePacket::from_bytes(&checked.packet().to_bytes().unwrap()).unwrap();
    println!(
        "actual callee byte-store/frame commutation: theory={:?}, wire={}, DAG={}, goal={}, proof={}; address separation/ABI/SourceNoUB/fetch remain open",
        checked._accepted.theory_id(),
        packet.to_bytes().unwrap().len(),
        packet.proof.len(),
        packet.goal_sha256,
        packet.proof_sha256,
    );
    if let Some(path) = std::env::var_os("TRUST_CALLEE_FRAME_PACKET_OUT") {
        use std::io::Write;
        let mut file = std::fs::OpenOptions::new().create_new(true).write(true).open(path).unwrap();
        file.write_all(&packet.to_bytes().unwrap()).unwrap();
    }
    drop(checked);
    drop(environment);
    let fresh = CalleeFrameEnvironment::open(&directory).unwrap();
    guarded(|| fresh.replay_separate_callee(&packet, &data.input()).unwrap());
    let expected = terms::build(&trace).unwrap();
    for which in 0..4 {
        let mut changed = packet.clone();
        changed.proof = encode_clean_expr_dag_v2(&expected.bad_proof(which).unwrap()).unwrap();
        changed.proof_sha256 = super::super::super::cohort::hash(&changed.proof);
        assert!(
            guarded(|| fresh.replay_separate_callee(&changed, &data.input())).is_err(),
            "accepted missing separation/wrong saved value/aliased destination/irrelevant proof {which}"
        );
    }
    for which in 0..5 {
        let mut changed = packet.clone();
        match which {
            0 => changed.subject.caller.call_pc += 4,
            1 => changed.subject.caller.callee_binding = "0".repeat(64),
            2 => changed.subject.data_states_sha256 = "0".repeat(64),
            3 => changed.subject.instructions[2][0] ^= 1,
            _ => changed.subject.store_step += 1,
        }
        assert!(guarded(|| fresh.replay_separate_callee(&changed, &data.input())).is_err());
    }
    let mut other = historical_b8_data_for_tests();
    let callee = BoundFunction::bind(
        &other.object,
        &other.m_cg,
        &packet.subject.caller.callee_symbol,
        other.relocation,
    )
    .unwrap();
    let code = callee.window().code.clone();
    let locations = other
        .object
        .windows(code.len())
        .enumerate()
        .filter_map(|(index, bytes)| (bytes == code).then_some(index))
        .collect::<Vec<_>>();
    assert_eq!(locations.len(), 1);
    other.object[locations[0]..locations[0] + 4].copy_from_slice(&0xd503201fu32.to_le_bytes());
    assert!(guarded(|| fresh.replay_separate_callee(&packet, &other.input())).is_err());

    let again = crate::call_event::verify_compiled_module(&data.input()).unwrap();
    assert_eq!(
        grades,
        again
            .certificates
            .iter()
            .map(|row| (row.symbol.clone(), row.grade.clone()))
            .collect::<Vec<_>>()
    );
    assert!(
        !again.certificates.iter().find(|row| row.symbol == CALLER).unwrap().verdict.is_proven()
    );
}
