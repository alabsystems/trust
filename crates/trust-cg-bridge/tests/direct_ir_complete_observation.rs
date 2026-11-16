//! COMPLETE original23 mathematical observations; no compiler admission.
use std::collections::BTreeMap;
use std::path::Path;
use std::sync::Arc;

use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use trust_cg_bridge::codegen_backend::TrustCgTargetArch;
use trust_cg_bridge::direct_ir_observation::{self as observation, DirectIrObservationPacket};
use trust_cg_bridge::verify_output_trust_ir::TrustIrGateSource;
use trust_types::{Formula, Sort};
const MODULE: &[u8] = include_bytes!("fixtures/direct_ir_observation/original-module.bin");
const OBJECT: &[u8] = include_bytes!("fixtures/direct_ir_observation/final-object.o");
const PACKET: &[u8] = include_bytes!("fixtures/direct_ir_observation/complete-raw.packet.json");
fn source(bytes: &[u8]) -> TrustIrGateSource {
    let m = trust_ir::binary::deserialize_module(bytes).unwrap();
    assert_eq!(trust_ir::binary::serialize_module(&m).unwrap(), bytes);
    assert!(trust_ir_build::validate_module(&m).is_empty());
    let f = &m.functions[0];
    TrustIrGateSource {
        symbol: f.name.clone(),
        func_id: f.id,
        module: Arc::new(m),
        abi_cross_check: None,
    }
}
fn save(out: &Path, name: &str, value: &impl serde::Serialize) {
    std::fs::create_dir_all(out).unwrap();
    std::fs::write(out.join(name), serde_json::to_vec_pretty(value).unwrap()).unwrap();
}
fn decode(v: Value) -> DirectIrObservationPacket {
    DirectIrObservationPacket::decode(&serde_json::to_vec(&v).unwrap()).unwrap()
}
fn refused(p: &DirectIrObservationPacket, s: &TrustIrGateSource, o: &[u8]) -> String {
    let error =
        observation::without_original_production(|| p.replay(s, o, TrustCgTargetArch::AArch64))
            .unwrap_err();
    if error.len() > 8192 {
        format!(
            "{} ... [actual refusal bytes={} sha256={:x}]",
            error.chars().take(8192).collect::<String>(),
            error.len(),
            Sha256::digest(error.as_bytes())
        )
    } else {
        error
    }
}
fn original_digest(v: &mut Value) {
    let rows: Vec<(Formula, Formula)> =
        serde_json::from_value(v["proof"]["original"].clone()).unwrap();
    v["proof"]["original_sha256"] =
        json!(format!("{:x}", Sha256::digest(serde_json::to_vec(&rows).unwrap())));
}
#[derive(serde::Serialize, serde::Deserialize)]
struct ContextWire {
    bits: Vec<String>,
    memories: Vec<String>,
    sorts: BTreeMap<String, Sort>,
    exact_byte_arrays: bool,
}

/// Executed by the separate actual kernel-feature-absent component.
pub fn missing_kernel_refuses(out: &Path) {
    let s = source(MODULE);
    let packet = DirectIrObservationPacket::decode(PACKET).unwrap();
    assert_eq!(
        observation::derive(&s, OBJECT, TrustCgTargetArch::AArch64).unwrap().equations().len(),
        23
    );
    let replay = packet.replay(&s, OBJECT, TrustCgTargetArch::AArch64).unwrap_err();
    assert!(replay.contains("kernel-recheck feature unavailable"), "{replay}");
    let producer = observation::prove(&s, OBJECT, TrustCgTargetArch::AArch64).unwrap_err();
    save(
        out,
        "missing-kernel-refusals.json",
        &json!({"actual_original_equations":23,"retained_replay":replay,"complete_production":producer}),
    );
}

/// Canonical tests keep a real positive on their ACTUAL selected kernel. Reuse
/// the frozen proof only after full current-input/kernel replay. A changed
/// environment is recorded as a historical refusal, followed by a DISTINCT
/// actual current producer phase; no old proof is relabelled or restamped.
pub fn select_current_packet(out: &Path) -> Vec<u8> {
    let s = source(MODULE);
    historical_identity(PACKET)
        .expect("maintained historical packet must retain its exact qualified identity");
    let historical = DirectIrObservationPacket::decode(PACKET).unwrap();
    let (wire, phase) = match observation::without_original_production(|| {
        historical.replay(&s, OBJECT, TrustCgTargetArch::AArch64)
    }) {
        Ok(checked) => {
            assert_eq!(checked.original_equations().len(), 23);
            (
                PACKET.to_vec(),
                "retained artifact genuinely replayed in the actual current environment",
            )
        }
        Err(error) if error.contains("actual trusted kernel environment mismatch") => {
            std::fs::create_dir_all(out).unwrap();
            std::fs::write(out.join("historical-environment-refusal.txt"), error).unwrap();
            let current = observation::prove(&s, OBJECT, TrustCgTargetArch::AArch64).expect(
                "changed selected kernel must genuinely prove all23, never skip the positive",
            );
            assert_eq!(current.original_equations().len(), 23);
            (
                serde_json::to_vec(current.packet()).unwrap(),
                "distinct actual current proof production after explicit historical environment refusal",
            )
        }
        Err(error) => panic!(
            "historical source/object/goal/proof regression is not an environment refresh: {error}"
        ),
    };
    std::fs::create_dir_all(out).unwrap();
    std::fs::write(out.join("selected-current.packet.json"), &wire).unwrap();
    save(
        out,
        "current-packet-selection.json",
        &json!({"phase":phase,"historical_packet_sha256":format!("{:x}",Sha256::digest(PACKET)),"selected_packet_sha256":format!("{:x}",Sha256::digest(&wire)),"complete_original_equations":23,"scope":"test artifact selection/producer phase ONLY; retained replay never produces a proof"}),
    );
    wire
}

fn historical_identity(wire: &[u8]) -> Result<(), String> {
    if format!("{:x}", Sha256::digest(wire))
        != "55c972f5eff184b4ba54a2b4870317c77f005edfeee44d2e2d46dadb5a532807"
    {
        return Err(
            "historical frame packet is not the exact qualified artifact; refresh is forbidden"
                .into(),
        );
    }
    Ok(())
}
pub fn selector_identity_controls(out: &Path) {
    historical_identity(PACKET).unwrap();
    let mut rows = Vec::new();
    for (label, kind) in
        [("altered environment digest", 0), ("altered proof", 1), ("changed historical byte", 2)]
    {
        let bad = if kind == 2 {
            let mut b = PACKET.to_vec();
            b[10] ^= 1;
            b
        } else {
            let mut v: Value = serde_json::from_slice(PACKET).unwrap();
            if kind == 0 {
                v["proof"]["environment_sha256"] = json!("0".repeat(64));
            } else {
                v["proof"]["terms"]["proof"] = v["proof"]["terms"]["goal"].clone();
            }
            serde_json::to_vec(&v).unwrap()
        };
        let error =
            observation::without_original_production(|| historical_identity(&bad)).unwrap_err();
        assert!(error.contains("refresh is forbidden"));
        rows.push(json!({"case":label,"refusal":error}));
    }
    save(
        out,
        "historical-selector-identity-controls.json",
        &json!({"original_qualified_sha256":"55c972f5eff184b4ba54a2b4870317c77f005edfeee44d2e2d46dadb5a532807","original_identity_passed":true,"production_forbidden":true,"kernel_feature_not_needed":true,"corruptions":rows}),
    );
}

/// SAME maintained source used by the fresh matching-SDK native replay probe.
pub fn fresh_complete_replay_and_hostile_controls(out: &Path) {
    replay_controls_with_packet(out, PACKET);
}

fn replay_controls_with_packet(out: &Path, wire: &[u8]) {
    let s = source(MODULE);
    let packet = DirectIrObservationPacket::decode(wire).unwrap();
    let start = std::time::Instant::now();
    let checked = observation::without_original_production(|| {
        packet.replay(&s, OBJECT, TrustCgTargetArch::AArch64)
    })
    .unwrap();
    let expected = observation::derive(&s, OBJECT, TrustCgTargetArch::AArch64).unwrap();
    assert_eq!(checked.original_equations(), expected.equations());
    assert_eq!(checked.original_equations().len(), 23);
    assert_eq!(checked.remaining_requirements().len(), 4);
    save(
        out,
        "complete23-fresh-replay.json",
        &json!({"actual_original_equations":23,"producer_forbidden":true,"seconds":start.elapsed().as_secs_f64(),"packet_bytes":wire.len(),"remaining_requirements":checked.remaining_requirements(),"scope":"universal conditional ORIGINAL return/rawO0 mathematical conjunction ONLY"}),
    );
    let mut failures = Vec::new();
    for (label, kind) in [
        ("deleted SP equation", 0),
        ("same-count duplicated row replacing SP", 1),
        ("reordered restored-register rows", 2),
    ] {
        let mut v: Value = serde_json::from_slice(wire).unwrap();
        let rows = v["proof"]["original"].as_array_mut().unwrap();
        match kind {
            0 => {
                rows.remove(12);
            }
            1 => rows[12] = rows[1].clone(),
            _ => rows.swap(11, 21),
        };
        original_digest(&mut v);
        let e = refused(&decode(v), &s, OBJECT);
        assert!(e.contains("independently expected original equations"), "{e}");
        failures.push(json!({"case":label,"refusal":e}));
    }
    let mut v: Value = serde_json::from_slice(wire).unwrap();
    let mut context: ContextWire = serde_json::from_value(v["proof"]["context"].clone()).unwrap();
    let high = "BVC_EQBIT_M8_w64_x5350_63";
    assert!(context.bits.iter().any(|x| x == high));
    context.bits.retain(|x| x != high);
    v["proof"]["context"] = serde_json::to_value(&context).unwrap();
    v["proof"]["context_sha256"] =
        json!(format!("{:x}", Sha256::digest(serde_json::to_vec(&context).unwrap())));
    let e = refused(&decode(v), &s, OBJECT);
    assert!(e.contains("independently rebuilt typed context"), "{e}");
    failures.push(json!({"case":"omitted high SP bit with recomputed context digest","refusal":e}));
    for (label, kind) in [
        ("wrong environment", 0),
        ("cyclic graph", 1),
        ("unbound BVar", 2),
        ("rebound function extent", 3),
    ] {
        let mut v: Value = serde_json::from_slice(wire).unwrap();
        match kind {
            0 => v["proof"]["environment_sha256"] = json!("0".repeat(64)),
            1 => v["proof"]["terms"]["terms"][0] = json!({"node":"App","function":0,"argument":0}),
            2 => v["proof"]["terms"]["terms"][0] = json!({"node":"BVar","index":4096}),
            _ => v["subject"]["extent"][1] = json!(24),
        };
        failures.push(json!({"case":label,"refusal":refused(&decode(v),&s,OBJECT)}));
    }
    // A well-framed proof replacement updates its digest and removes all now-
    // unreachable proof nodes; only an actual kernel type check can reject it.
    let mut v: Value = serde_json::from_slice(wire).unwrap();
    let root = v["proof"]["terms"]["goal"].as_u64().unwrap();
    v["proof"]["terms"]["terms"].as_array_mut().unwrap().truncate(root as usize + 1);
    v["proof"]["terms"]["proof"] = json!(root);
    v["proof"]["proof_sha256"] = v["proof"]["goal_sha256"].clone();
    let e = refused(&decode(v), &s, OBJECT);
    assert!(
        e.contains("kernel") && !e.contains("digest mismatch") && !e.contains("unaccounted"),
        "{e}"
    );
    failures.push(
        json!({"case":"well-framed goal-as-proof replacement reaches real kernel","refusal":e}),
    );
    let mut wrong = (*s.module).clone();
    let mut changed = 0;
    for n in &mut wrong.functions[0].blocks[0].body {
        if let trust_ir::Inst::Const { value: trust_ir::Constant::Int(v), .. } = &mut n.inst {
            assert_eq!(*v, 7);
            *v = 8;
            changed += 1;
        }
    }
    assert_eq!(changed, 1);
    assert!(trust_ir_build::validate_module(&wrong).is_empty());
    let w = source(&trust_ir::binary::serialize_module(&wrong).unwrap());
    let mut v: Value = serde_json::from_slice(wire).unwrap();
    v["subject"] =
        serde_json::to_value(observation::derive(&w, OBJECT, TrustCgTargetArch::AArch64).unwrap())
            .unwrap()["subject"]
            .clone();
    let e = refused(&decode(v), &w, OBJECT);
    assert!(e.contains("independently expected original equations"), "{e}");
    failures.push(json!({"case":"actual valid +8 module with forged outer binding","refusal":e}));
    let mut extra: Value = serde_json::from_slice(wire).unwrap();
    extra["compiler_grade"] = json!("KernelClosed");
    assert!(DirectIrObservationPacket::decode(&serde_json::to_vec(&extra).unwrap()).is_err());
    assert!(DirectIrObservationPacket::decode(&wire[..wire.len() - 1]).is_err());
    save(out, "complete23-hostile-refusals.json", &failures);
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            observation::without_original_production(|| {
                observation::prove(&s, OBJECT, TrustCgTargetArch::AArch64)
            })
        }))
        .is_err(),
        "producer denial instrumentation must really fire"
    );
}

pub fn actual_frame_object_mutations_refuse(out: &Path) {
    frame_mutations_with_packet(out, PACKET);
}

fn frame_mutations_with_packet(out: &Path, wire: &[u8]) {
    let s = source(MODULE);
    let packet = DirectIrObservationPacket::decode(wire).unwrap();
    let expected = observation::derive(&s, OBJECT, TrustCgTargetArch::AArch64).unwrap();
    let data = serde_json::to_value(&expected).unwrap();
    let words: Vec<u32> = data["subject"]["instruction_words"]
        .as_array()
        .unwrap()
        .iter()
        .map(|x| x.as_u64().unwrap() as u32)
        .collect();
    assert_eq!(words.len(), 7);
    let text: Vec<u8> = words.iter().flat_map(|x| x.to_le_bytes()).collect();
    let positions: Vec<_> = OBJECT
        .windows(text.len())
        .enumerate()
        .filter(|(_, b)| *b == text)
        .map(|(i, _)| i)
        .collect();
    assert_eq!(positions.len(), 1);
    let start = positions[0];
    assert_eq!(words[0] & 31, 29);
    assert_eq!((words[0] >> 10) & 31, 30);
    assert_eq!(words[5] & 31, 29);
    let mut rows = Vec::new();
    for (name, index, word) in [
        ("changed stored register", 0, (words[0] & !31) | 28),
        ("dropped pair store", 0, 0xd10043ff),
        ("swapped stored register bytes", 0, (words[0] & !(31 | (31 << 10))) | 30 | (29 << 10)),
        ("wrong restored register", 5, (words[5] & !31) | 28),
        ("wrong modular SP restoration", 5, (words[5] & !(127 << 15)) | (4 << 15)),
    ] {
        let mut mutant = OBJECT.to_vec();
        mutant[start + 4 * index..start + 4 * index + 4].copy_from_slice(&word.to_le_bytes());
        let m = observation::derive(&s, &mutant, TrustCgTargetArch::AArch64).unwrap();
        assert_eq!(m.equations().len(), 23);
        assert_eq!(
            m.equations()[0],
            expected.equations()[0],
            "scalar return is unchanged; raw ABI debt is indispensable"
        );
        assert_ne!(m.equations(), expected.equations());
        std::fs::create_dir_all(out).unwrap();
        std::fs::write(out.join(format!("mutant-{index}-{word:08x}.o")), &mutant).unwrap();
        let mut rebound: Value = serde_json::from_slice(wire).unwrap();
        rebound["subject"] = serde_json::to_value(&m).unwrap()["subject"].clone();
        let retained_error = refused(&decode(rebound), &s, &mutant);
        assert!(
            retained_error.contains("independently expected original equations"),
            "{retained_error}"
        );
        let fresh = observation::prove(&s, &mutant, TrustCgTargetArch::AArch64);
        assert!(fresh.is_err(), "false raw ABI/frame conjunction accepted: {name}");
        rows.push(json!({"case":name,"actual_instruction_index":index,"word":word,"same_scalar_return":true,"retained_refusal":retained_error,"fresh_complete_refusal":fresh.unwrap_err()}));
    }
    save(out, "actual-frame-object-refusals.json", &rows);
}

#[test]
fn complete23_replays_original_subject_with_production_forbidden() {
    let out = std::env::temp_dir().join(format!("trust-complete23-{}", std::process::id()));
    let wire = select_current_packet(&out);
    replay_controls_with_packet(&out, &wire);
}
#[test]
fn actual_frame_byte_and_sp_mutations_decline_complete_math() {
    let out = std::env::temp_dir().join(format!("trust-complete23-mutants-{}", std::process::id()));
    let wire = select_current_packet(&out);
    frame_mutations_with_packet(&out, &wire);
}

pub fn parser_boundaries(out: &Path) {
    let words =
        [2847898621u32, 2432697341, 3531604193, 2432703489, 2852193248, 2831252477, 3596551104];
    let bytes: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    assert_eq!(observation::test_instruction_words(&bytes).unwrap(), words);
    for n in [0, 1, 2, 3, 5, 27] {
        assert!(
            observation::test_instruction_words(&bytes[..n]).is_err(),
            "bad alignment {n} admitted"
        );
    }
    assert!(observation::derive(&source(MODULE), &[], TrustCgTargetArch::AArch64).is_err());
    save(
        out,
        "instruction-parser-boundaries.json",
        &json!({"actual_original_words":words,"positive_bytes":bytes.len(),"refused_lengths":[0,1,2,3,5,27],"empty_object_refused":true,"scope":"actual production instruction parser boundary; no proof/admission from parsed counts"}),
    );
}

/// The controller supplies an owned regular-file failure-output sentinel.
/// Failure diagnostics must not panic or convert a false frame into evidence.
pub fn failed_diagnostic_output_still_refuses(out: &Path) {
    let s = source(MODULE);
    let data =
        serde_json::to_value(observation::derive(&s, OBJECT, TrustCgTargetArch::AArch64).unwrap())
            .unwrap();
    let words: Vec<u32> = data["subject"]["instruction_words"]
        .as_array()
        .unwrap()
        .iter()
        .map(|w| w.as_u64().unwrap() as u32)
        .collect();
    let text: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    let starts: Vec<_> = OBJECT
        .windows(text.len())
        .enumerate()
        .filter(|(_, b)| *b == text)
        .map(|(i, _)| i)
        .collect();
    assert_eq!(starts.len(), 1);
    let mut mutant = OBJECT.to_vec();
    mutant[starts[0]..starts[0] + 4].copy_from_slice(&((words[0] & !31) | 28).to_le_bytes());
    let result = observation::prove(&s, &mutant, TrustCgTargetArch::AArch64);
    assert!(result.is_err());
    save(
        out,
        "failed-diagnostic-output.json",
        &json!({"false_complete_frame_refused":result.unwrap_err(),"native_process_survived_failed_diagnostic_write":true}),
    );
}
#[test]
fn instruction_parser_preserves_alignment_guard_without_unwrap() {
    parser_boundaries(
        &std::env::temp_dir().join(format!("trust-complete23-parser-{}", std::process::id())),
    );
}
#[test]
fn historical_selector_refuses_corruption_before_any_refresh() {
    selector_identity_controls(
        &std::env::temp_dir().join(format!("trust-complete23-selector-{}", std::process::id())),
    );
}
