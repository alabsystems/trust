// Copyright 2026 Andrew Yates | Apache-2.0
use super::*;
use crate::compiler_input_capture::historical_b8_data_for_tests;
const CALLER: &str = "source_memory_caller";
fn guarded<T>(f: impl FnOnce() -> T) -> T {
    crate::original_conjunction_certificate::without_production(|| {
        super::super::terms::forbid_production(f)
    })
}

#[test]
fn actual_compiler_frame_roundtrip_retains_conditional_reference_evidence() {
    std::thread::Builder::new().stack_size(32 << 20).spawn(check_actual).unwrap().join().unwrap();
}
fn check_actual() {
    let directory = std::path::PathBuf::from(
        std::env::var_os("TRUST_FRAME_CALLER_COHORT").expect("actual caller cohort required"),
    );
    let data = historical_b8_data_for_tests();
    actual_callee_alias_control(&data.input());
    let normal = crate::call_event::verify_compiled_module(&data.input()).unwrap();
    let grades = normal
        .certificates
        .iter()
        .map(|row| (row.symbol.clone(), row.grade.clone()))
        .collect::<Vec<_>>();
    assert!(
        !normal.certificates.iter().find(|row| row.symbol == CALLER).unwrap().verdict.is_proven()
    );
    let environment = CallerFrameEnvironment::open(&directory).unwrap();
    println!(
        "actual save/call/restore reference environment checked: {}",
        environment.cohort_digest()
    );
    let checked = environment.prove_conditional_frame(&data.input(), CALLER).unwrap();
    let packet =
        ConditionalCallerFramePacket::from_bytes(&checked.packet().to_bytes().unwrap()).unwrap();
    println!(
        "conditional physical+modeled frame evidence: theory={:?}, wire={}, DAG={}, goal={}, proof={}; actual-call/heap/ABI/SourceNoUB premises unsupplied",
        checked._accepted.theory_id(),
        packet.to_bytes().unwrap().len(),
        packet.proof.len(),
        packet.goal_sha256,
        packet.proof_sha256
    );
    if let Some(path) = std::env::var_os("TRUST_FRAME_CALLER_PACKET_OUT") {
        use std::io::Write;
        let mut file = std::fs::OpenOptions::new().create_new(true).write(true).open(path).unwrap();
        file.write_all(&packet.to_bytes().unwrap()).unwrap();
    }
    drop(checked);
    drop(environment);
    let fresh = CallerFrameEnvironment::open(&directory).unwrap();
    guarded(|| fresh.replay_conditional_frame(&packet, &data.input()).unwrap());
    let report =
        guarded(|| crate::call_event::observe_compiled_module_for_frame(&data.input()).unwrap());
    let certificate = report.certificates.iter().find(|row| row.symbol == CALLER).unwrap();
    let trace = binding::bind(&data.input(), certificate).unwrap();
    let expected = terms::build(&trace).unwrap();
    for which in 0..4 {
        let mut changed = packet.clone();
        changed.proof = encode_clean_expr_dag_v2(&expected.bad_proof(which).unwrap()).unwrap();
        changed.proof_sha256 = super::super::cohort::hash(&changed.proof);
        assert!(
            guarded(|| fresh.replay_conditional_frame(&changed, &data.input())).is_err(),
            "accepted wrong saved value/address/missing actual call agreement/proof {which}"
        );
    }
    for which in 0..4 {
        let mut changed = packet.clone();
        match which {
            0 => changed.subject.call_pc += 4,
            1 => changed.subject.callee_binding = "0".repeat(64),
            2 => changed.subject.states_sha256 = "0".repeat(64),
            _ => changed.subject.instructions[3][0] ^= 1,
        };
        assert!(guarded(|| fresh.replay_conditional_frame(&changed, &data.input())).is_err());
    }
    // Same source spelling and framed caller bytes, different real callee bytes.
    let mut other = historical_b8_data_for_tests();
    let callee = BoundFunction::bind(
        &other.object,
        &other.m_cg,
        &packet.subject.callee_symbol,
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
    assert!(guarded(|| fresh.replay_conditional_frame(&packet, &other.input())).is_err());
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

/// Execute the actual decoded save/helper/restore data effects in the existing
/// concrete machine semantics. This is a finite hostile control, not a source
/// heap, ABI, instruction-fetch or function-correctness proof.
pub(super) fn actual_callee_alias_control(input: &CerInput<'_>) {
    use trust_machine_sem::{Aarch64Semantics, ConcreteState, Effect, Semantics};

    let caller =
        BoundFunction::bind(input.object, input.m_cg, CALLER, input.relocation_model).unwrap();
    let call_pc = caller.window().start + 8;
    let callee_symbol = caller.window().site_at(call_pc).unwrap().callee.as_ref().unwrap();
    let callee =
        BoundFunction::bind(input.object, input.m_cg, callee_symbol, input.relocation_model)
            .unwrap();
    assert_eq!(caller.window().code.len(), 20);
    assert_eq!(callee.window().code.len(), 20);
    let execute = |state: &mut ConcreteState, bytes: &[u8], pc: u64, control: u8| {
        state.pc = pc;
        let decoded = trust_disasm::decode_aarch64(bytes, pc).unwrap();
        let effects = Aarch64Semantics.effects(&MachineState::symbolic(), &decoded).unwrap();
        let before = state.clone();
        let mut controls = 0;
        for effect in effects {
            match &effect {
                Effect::Call { return_addr, .. } if control == 1 => {
                    // The actual relocation-bound callee is selected above;
                    // this control does not certify BL instruction fetching.
                    controls += 1;
                    state.gpr[30] = before.eval_bv(return_addr, 64).unwrap() as u64;
                }
                Effect::Return { target } if control == 2 => {
                    controls += 1;
                    state.pc = before.eval_bv(target, 64).unwrap() as u64;
                }
                _ => state.apply_effect_with_eval_state(&before, &effect).unwrap(),
            }
        }
        assert_eq!(controls, usize::from(control != 0));
    };
    let original_sp = 0x1000;
    let original_fp = 0x0123_4567_89ab_cdef;
    let original_lr = 0xfedc_ba98_7654_3234;
    for alias in [false, true] {
        let mut state = ConcreteState::new();
        state.sp = original_sp;
        state.gpr[29] = original_fp;
        state.gpr[30] = original_lr;
        state.gpr[0] = if alias { original_sp - 8 } else { 0x900 };
        state.gpr[1] = 0x800;
        state.gpr[2] = 1;
        state.store_memory_le(0x800, 1, 0x5a).unwrap();
        for index in 0..2 {
            execute(
                &mut state,
                &caller.window().code[index * 4..index * 4 + 4],
                caller.window().start + index as u64 * 4,
                0,
            );
        }
        assert_eq!(state.sp, original_sp - 16);
        assert_eq!(state.load_memory_le(original_sp - 16, 8).unwrap(), original_fp.into());
        assert_eq!(state.load_memory_le(original_sp - 8, 8).unwrap(), original_lr.into());
        let saved =
            (0..16).map(|offset| state.memory[&(original_sp - 16 + offset)]).collect::<Vec<_>>();
        execute(&mut state, &caller.window().code[8..12], call_pc, 1);
        for index in 0..5 {
            execute(
                &mut state,
                &callee.window().code[index * 4..index * 4 + 4],
                callee.window().start + index as u64 * 4,
                if index == 4 { 2 } else { 0 },
            );
        }
        assert_eq!(state.pc, call_pc + 4);
        assert_eq!(state.gpr[0], 0x5a);
        let actual =
            (0..16).map(|offset| state.memory[&(original_sp - 16 + offset)]).collect::<Vec<_>>();
        assert_eq!(actual == saved, !alias);
        assert_eq!(actual[8], if alias { 1 } else { 0x34 });
        execute(&mut state, &caller.window().code[12..16], call_pc + 4, 0);
        assert_eq!(state.sp, original_sp);
        assert_eq!(state.gpr[29], original_fp);
        assert_eq!(state.gpr[30], if alias { (original_lr & !0xff) | 1 } else { original_lr });
        execute(&mut state, &caller.window().code[16..20], call_pc + 8, 2);
        assert_eq!(state.pc == original_lr, !alias);
        assert_eq!(state.memory[&0x800], 0x5a);
    }
    println!(
        "actual decoded helper preserves the frame for separate destination; saved-LR alias corrupts LR/RET and falsifies full call agreement"
    );
}
