// Copyright 2026 Andrew Yates | Apache-2.0
use std::path::PathBuf;

use super::*;
use crate::compiler_input_capture::CompilerInputCapture;

const INPUT: &[u8] = include_bytes!("../compiler_frame_inputs/actual-b8-caller-input.json");

#[test]
fn actual_compiler_entry_store_has_retained_conditional_reference_evidence() {
    // The existing actual compiler CER fixture requires the same 32MiB stack
    // as compiler_frame_inputs::tests; this does not change proof semantics.
    std::thread::Builder::new().stack_size(32 << 20).spawn(check_actual).unwrap().join().unwrap();
}
fn check_actual() {
    let directory = PathBuf::from(
        std::env::var_os("TRUST_FRAME_STEP_COHORT").expect("qualified cohort directory required"),
    );
    let data = CompilerInputCapture::from_bytes(INPUT).unwrap().decode_inputs().unwrap();
    let report = crate::call_event::verify_compiled_module(&data.input()).unwrap();
    let caller = report.certificates.iter().find(|c| c.symbol == "source_memory_caller").unwrap();
    assert!(!caller.verdict.is_proven());
    let original_grade = caller.grade.clone();
    let environment = FrameTheoremEnvironment::open(&directory).unwrap();
    println!("fresh reference theorem environment checked: {}", environment.cohort_digest());
    let checked = environment.prove_entry_step(&data.input(), caller).unwrap();
    let packet = ConditionalFramePacket::from_bytes(&checked.packet().to_bytes().unwrap()).unwrap();
    println!(
        "actual first STP conditional packet: theory={:?}, bytes={}, cohort={}, environment={}, goal={}, proof={}",
        checked._accepted.theory_id(),
        packet.to_bytes().unwrap().len(),
        packet.cohort_sha256,
        packet.environment_sha256,
        packet.goal_sha256,
        packet.proof_sha256
    );
    if let Some(path) = std::env::var_os("TRUST_FRAME_STEP_PACKET_OUT") {
        use std::io::Write;
        let mut file = std::fs::OpenOptions::new().create_new(true).write(true).open(path).unwrap();
        file.write_all(&packet.to_bytes().unwrap()).unwrap();
    }
    drop(checked);
    drop(environment);
    let fresh = FrameTheoremEnvironment::open(&directory).unwrap();
    crate::original_conjunction_certificate::without_production(|| {
        terms::forbid_production(|| fresh.replay_entry_step(&packet, &data.input()).unwrap())
    });
    assert_eq!(caller.grade, original_grade);
    assert!(!caller.verdict.is_proven());
    let (step, _) = actual_step(&data.input(), caller).unwrap();
    let expected = terms::build(&step).unwrap();
    for mutation in 0..3 {
        let mut changed = packet.clone();
        let false_proof = expected.bad_proof(mutation);
        changed.proof = serde_json::to_string(&false_proof).unwrap();
        changed.proof_sha256 = cohort::hash(changed.proof.as_bytes());
        assert!(
            fresh.replay_entry_step(&changed, &data.input()).is_err(),
            "kernel accepted address/value/proof substitution {mutation}"
        );
    }
    for mutation in 0..3 {
        let mut changed = packet.clone();
        match mutation {
            0 => changed.subject.pc += 4,
            1 => changed.subject.state_sha256 = "0".repeat(64),
            _ => changed.cohort_sha256 = "0".repeat(64),
        }
        assert!(fresh.replay_entry_step(&changed, &data.input()).is_err());
    }
    let mut wrong = caller.clone();
    wrong.text_sha256 = "0".repeat(64);
    assert!(actual_step(&data.input(), &wrong).is_err());
    // Relabeling public report fields cannot replace the private source/P
    // custody sealed alongside the actual entry observation.
    let mut other = CompilerInputCapture::from_bytes(INPUT).unwrap().decode_inputs().unwrap();
    let placement = other.placements.get_mut("source_memory_caller").unwrap();
    placement.params.swap(0, 1);
    let mut relabeled = caller.clone();
    relabeled.placement_sha256.insert("source_memory_caller".into(), placement.digest());
    assert!(fresh.prove_entry_step(&other.input(), &relabeled).is_err());
    assert!(fresh.replay_entry_step(&packet, &other.input()).is_err());
    // Tampering with a new bundle copy cannot affect the already captured
    // environment, and a new opener refuses before decoding changed bytes.
    let temporary = tempfile::tempdir().unwrap();
    copy_bundle(&directory, temporary.path());
    let leaf = temporary.path().join("SemRFrameStep.olean");
    let mut bytes = std::fs::read(&leaf).unwrap();
    let end = bytes.len() - 1;
    bytes[end] ^= 1;
    std::fs::write(&leaf, bytes).unwrap();
    assert!(FrameTheoremEnvironment::open(temporary.path()).is_err());
    crate::original_conjunction_certificate::without_production(|| {
        terms::forbid_production(|| fresh.replay_entry_step(&packet, &data.input()).unwrap())
    });
}
fn copy_bundle(from: &std::path::Path, to: &std::path::Path) {
    for entry in std::fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let dest = to.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            std::fs::create_dir(&dest).unwrap();
            copy_bundle(&entry.path(), &dest)
        } else {
            std::fs::copy(entry.path(), dest).unwrap();
        }
    }
}

#[test]
fn actual_caller_retains_authentic_save_call_restore_states() {
    std::thread::Builder::new().stack_size(32 << 20).spawn(|| {
        let data=CompilerInputCapture::from_bytes(INPUT).unwrap().decode_inputs().unwrap();
        let report=crate::original_conjunction_certificate::without_production(||
            crate::call_event::observe_compiled_module_for_frame(&data.input()).unwrap());
        let caller=report.certificates.iter().find(|row|row.symbol=="source_memory_caller").unwrap();
        assert!(!caller.verdict.is_proven());
        let pending=caller.frame_execution.as_ref().unwrap();assert_eq!(pending.steps().len(),5);
        assert_eq!(pending.calls().len(),1);assert_eq!(pending.exits().len(),1);
        let mut states=Vec::new();
        for (index,step) in pending.steps().iter().enumerate(){
            let (before,after)=pending.states_at(index).unwrap();
            assert_eq!(step.pre_sp,before.sp);assert_eq!(step.memory_before,before.memory);
            if index+1<pending.steps().len(){
                let (next,_)=pending.states_at(index+1).unwrap();
                assert_eq!(digest(&StateImage::from(after)).unwrap(),digest(&StateImage::from(next)).unwrap());
            }
            states.push(serde_json::json!({"index":index,"pc":step.pc,"instruction":step.instruction,"path":step.path,"control":step.control,"effects_debug":format!("{:?}",step.effects),"before":StateImage::from(before),"after":StateImage::from(after)}));
        }
        if let Some(path)=std::env::var_os("TRUST_FRAME_CALLER_TRACE_OUT"){
            use std::io::Write;
            let mut output=std::fs::OpenOptions::new().create_new(true).write(true).open(path).unwrap();
            output.write_all(&serde_json::to_vec_pretty(&states).unwrap()).unwrap();
        }
        println!("actual caller: five authentic adjacent callback states, one explicit abstract call, one RET; Unknown; no SourceNoUB/entry/call agreement discharged");
    }).unwrap().join().unwrap();
}
