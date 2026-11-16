//! Actual source-derived original Module and final canonical CG object.
//! These tests retain a RETURN-ONLY CIC observation; all raw ABI/frame/source
//! and emission requirements remain open. Wire data never grants admission.
use std::path::Path;
use std::sync::Arc;

use serde_json::{Value, json};
use trust_cg_bridge::codegen_backend::TrustCgTargetArch;
use trust_cg_bridge::direct_ir_observation::{self as observation, DirectIrReturnValuePacket};
use trust_cg_bridge::verify_output_trust_ir::TrustIrGateSource;
const MODULE: &[u8] = include_bytes!("fixtures/direct_ir_observation/original-module.bin");
const OBJECT: &[u8] = include_bytes!("fixtures/direct_ir_observation/final-object.o");
const PACKET: &[u8] = include_bytes!("fixtures/direct_ir_observation/return-only.packet.json");
fn source(bytes: &[u8]) -> TrustIrGateSource {
    let module = trust_ir::binary::deserialize_module(bytes).unwrap();
    assert_eq!(trust_ir::binary::serialize_module(&module).unwrap(), bytes);
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let f = &module.functions[0];
    TrustIrGateSource {
        symbol: f.name.clone(),
        func_id: f.id,
        module: Arc::new(module),
        abi_cross_check: None,
    }
}
fn packet(value: Value) -> DirectIrReturnValuePacket {
    DirectIrReturnValuePacket::decode(&serde_json::to_vec(&value).unwrap()).unwrap()
}
fn refused(p: &DirectIrReturnValuePacket, s: &TrustIrGateSource, o: &[u8]) -> String {
    observation::without_original_production(|| p.replay(s, o, TrustCgTargetArch::AArch64))
        .unwrap_err()
}
fn save(out: &Path, name: &str, value: &impl serde::Serialize) {
    std::fs::create_dir_all(out).unwrap();
    std::fs::write(out.join(name), serde_json::to_vec_pretty(value).unwrap()).unwrap();
}
/// Shared with the SDK-bound FIRST-entry probe; SAME maintained test source.
pub fn fresh_replay_and_hostile_controls(out: &Path) {
    let s = source(MODULE);
    let p = DirectIrReturnValuePacket::decode(PACKET).unwrap();
    let start = std::time::Instant::now();
    let checked = observation::without_original_production(|| {
        p.replay(&s, OBJECT, TrustCgTargetArch::AArch64)
    })
    .unwrap();
    assert_eq!(checked.original_return_equation().len(), 1);
    assert_eq!(checked.pending_raw_abi_equations().len(), 22);
    assert_eq!(checked.pending_raw_abi_names().len(), 22);
    save(
        out,
        "replay.json",
        &json!({"seconds":start.elapsed().as_secs_f64(),"packet_bytes":PACKET.len(),"checked_original_return_equations":1,"UNPROVED_raw_ABI_equations":22,"scope":"conditional original return value ONLY; NO full correctness/emission/ABI/frame/source license"}),
    );
    let mut failures = Vec::new();
    for (label, edit) in [
        ("wrong environment", 0),
        ("changed original equation", 1),
        ("proof root substitution", 2),
        ("cyclic graph", 3),
        ("open binder", 4),
        ("typed context mismatch", 5),
        ("erased raw ABI debt", 6),
        ("rebound function extent", 7),
    ] {
        let mut v: Value = serde_json::from_slice(PACKET).unwrap();
        match edit {
            0 => v["proof"]["environment_sha256"] = json!("0".repeat(64)),
            1 => v["proof"]["original"][0][0]["BvAdd"][1]["BitVec"]["value"] = json!(8),
            2 => v["proof"]["terms"]["proof"] = v["proof"]["terms"]["goal"].clone(),
            3 => v["proof"]["terms"]["terms"][0] = json!({"node":"App","function":0,"argument":0}),
            4 => v["proof"]["terms"]["terms"][0] = json!({"node":"BVar","index":4096}),
            5 => v["proof"]["context"]["sorts"]["X0"] = json!({"BitVec":32}),
            6 => v["pending_raw_abi_sha256"] = json!("0".repeat(64)),
            _ => v["subject"]["extent"][1] = json!(24),
        }
        failures.push(json!({"case":label,"refusal":refused(&packet(v),&s,OBJECT)}));
    }
    // A valid different actual IR Module, not a fake expected packet subject.
    let mut wrong = (*s.module).clone();
    let mut changed = 0;
    for n in &mut wrong.functions[0].blocks[0].body {
        if let trust_ir::Inst::Const { value: trust_ir::Constant::Int(x), .. } = &mut n.inst {
            assert_eq!(*x, 7);
            *x = 8;
            changed += 1;
        }
    }
    assert_eq!(changed, 1);
    assert!(trust_ir_build::validate_module(&wrong).is_empty());
    let wrong_bytes = trust_ir::binary::serialize_module(&wrong).unwrap();
    let w = source(&wrong_bytes);
    failures.push(json!({"case":"actual valid +8 Module","refusal":refused(&p,&w,OBJECT)}));
    let mut rebound: Value = serde_json::from_slice(PACKET).unwrap();
    rebound["subject"] =
        serde_json::to_value(observation::derive(&w, OBJECT, TrustCgTargetArch::AArch64).unwrap())
            .unwrap()["subject"]
            .clone();
    let reason = refused(&packet(rebound), &w, OBJECT);
    assert!(reason.contains("independently expected original equations mismatch"), "{reason}");
    failures.push(json!({"case":"forged outer Module binding still requires independently expected math","refusal":reason}));
    // Mutation changes an actual ADD immediate while preserving the entire
    // symbol/relocation/section table and every other real instruction.
    let data =
        serde_json::to_value(observation::derive(&s, OBJECT, TrustCgTargetArch::AArch64).unwrap())
            .unwrap();
    let words: Vec<u32> = data["subject"]["instruction_words"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| v.as_u64().unwrap() as u32)
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
    let mut changed = 0;
    for (i, w) in words.iter().enumerate() {
        if w & 0xffc0_0000 == 0x9100_0000 && (w >> 10) & 0xfff == 7 {
            mutant[starts[0] + 4 * i..starts[0] + 4 * i + 4]
                .copy_from_slice(&(w + (1 << 10)).to_le_bytes());
            changed += 1;
        }
    }
    assert_eq!(changed, 1);
    save(out, "mutant-object-bytes.json", &mutant);
    failures.push(
        json!({"case":"actual emitted ADD +7 changed to +8","refusal":refused(&p,&s,&mutant)}),
    );
    let mut rebound: Value = serde_json::from_slice(PACKET).unwrap();
    rebound["subject"] =
        serde_json::to_value(observation::derive(&s, &mutant, TrustCgTargetArch::AArch64).unwrap())
            .unwrap()["subject"]
            .clone();
    let reason = refused(&packet(rebound), &s, &mutant);
    assert!(reason.contains("independently expected original equations mismatch"), "{reason}");
    failures.push(json!({"case":"forged outer object binding cannot preserve a wrong equation","refusal":reason}));
    assert!(
        observation::prove_return_value(&s, &mutant, TrustCgTargetArch::AArch64).is_err(),
        "actual wrong ADD must not gain any return proof"
    );
    failures.push(json!({"case":"actual wrong ADD fresh proof production","refusal":"kernel/reflection correctly declines the false original return equation"}));
    let mut c = (*s.module).clone();
    c.functions[0].calling_conv = trust_ir::CallingConv::C;
    let c = source(&trust_ir::binary::serialize_module(&c).unwrap());
    assert!(observation::derive(&c, OBJECT, TrustCgTargetArch::AArch64).is_err());
    failures.push(json!({"case":"C ABI relabel","refusal":"bounded logical Rust profile refuses"}));
    assert!(DirectIrReturnValuePacket::decode(&vec![b' '; 8 * 1024 * 1024 + 1]).is_err());
    assert!(DirectIrReturnValuePacket::decode(&PACKET[..PACKET.len() - 1]).is_err());
    let mut unknown: Value = serde_json::from_slice(PACKET).unwrap();
    unknown["compiler_grade"] = json!("proved");
    assert!(DirectIrReturnValuePacket::decode(&serde_json::to_vec(&unknown).unwrap()).is_err());
    save(out, "hostile-refusals.json", &failures);
    // This tripwire must actually fire, proving the deny instrumentation is
    // live; replay above succeeds under the very same prohibition.
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            observation::without_original_production(|| {
                observation::prove_return_value(&s, OBJECT, TrustCgTargetArch::AArch64)
            })
        }))
        .is_err()
    );
}
#[test]
fn original_return_replay_keeps_full_subject_and_explicit_debts() {
    let out = std::env::var_os("TRUST_DIRECT_IR_OBSERVATION_OUTPUT")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| {
            std::env::temp_dir().join(format!("trust-direct-original-{}", std::process::id()))
        });
    fresh_replay_and_hostile_controls(&out);
}

/// A well-framed proof substitution updates its claimed digest, so the real
/// kernel type check (not just a stale wire hash) must reject it.
pub fn typed_proof_and_binder_refusals(out: &Path) {
    let s = source(MODULE);
    let mut v: Value = serde_json::from_slice(PACKET).unwrap();
    let goal = v["proof"]["terms"]["goal"].as_u64().unwrap();
    v["proof"]["terms"]["terms"].as_array_mut().unwrap().truncate(goal as usize + 1);
    v["proof"]["terms"]["proof"] = json!(goal);
    v["proof"]["proof_sha256"] = v["proof"]["goal_sha256"].clone();
    let type_error = refused(&packet(v), &s, OBJECT);
    assert!(type_error.contains("kernel") || type_error.contains("type"), "{type_error}");
    assert!(
        !type_error.contains("digest mismatch") && !type_error.contains("unaccounted"),
        "{type_error}"
    );
    let mut v: Value = serde_json::from_slice(PACKET).unwrap();
    v["proof"]["terms"]["terms"][0] = json!({"node":"BVar", "index":4096});
    let binder_error = refused(&packet(v), &s, OBJECT);
    assert!(binder_error.contains("bound") || binder_error.contains("scope"), "{binder_error}");
    assert!(!binder_error.contains("duplicate"), "{binder_error}");
    save(
        out,
        "typed-proof-and-binder-refusals.json",
        &json!({"fresh_kernel_rejects_goal_used_as_proof_with_updated_digest":type_error,"unique_unbound_BVar_rejected":binder_error}),
    );
}
#[test]
fn replay_rejects_well_framed_ill_typed_proof_and_unbound_binder() {
    let out = std::env::var_os("TRUST_DIRECT_IR_OBSERVATION_OUTPUT")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| {
            std::env::temp_dir().join(format!("trust-direct-typed-negative-{}", std::process::id()))
        });
    typed_proof_and_binder_refusals(&out);
}
