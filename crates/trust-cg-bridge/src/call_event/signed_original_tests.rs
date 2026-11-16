#![cfg(feature = "kernel-recheck")]
use super::*;
use crate::compiler_input_capture::CompilerInputCapture;
use crate::original_conjunction_certificate::without_production;

const LEAVES: [&str; 4] = ["trust_c_i8_id", "trust_c_i8_not", "trust_c_i16_id", "trust_c_i16_not"];
fn load_current() -> crate::compiler_input_capture::DecodedCompilerInputs {
    let bytes = include_bytes!("../../tests/fixtures/signed_e76_o0_original/compiler-input.json");
    assert_eq!(
        crate::object_replay::artifact_digest(bytes),
        "f8f368beb5df7b2668b1c5f7b1d2ee0b479215e23ef83786d1de630fd8b5180c"
    );
    CompilerInputCapture::from_bytes(bytes).unwrap().decode_inputs().unwrap()
}
fn replay(input: &CerInput<'_>, sidecar: &[u8]) -> Result<OriginalReplayReport, String> {
    without_production(|| replay_original_certificates(input, sidecar))
}
#[test]
fn actual_signed_leaves_keep_full_original_and_replay_in_fresh_process() {
    if let Some(directory) = std::env::var_os("TRUST_SIGNED_LEAF_REPLAY_CHILD") {
        let dir = std::path::PathBuf::from(directory);
        // Current inputs are independently selected compiled-in immutable e76
        // capture bytes, never reconstructed from the retained certificate.
        let current = load_current();
        let result =
            replay(&current.input(), &std::fs::read(dir.join("report.json")).unwrap()).unwrap();
        assert_eq!(result.rows.len(), 8);
        assert_eq!(result.rows.iter().filter(|r| r.replayed).count(), 6, "{result:?}");
        for name in LEAVES {
            assert!(result.rows.iter().find(|r| r.symbol == name).unwrap().replayed);
        }
        for name in ["trust_c_i8_tail", "trust_c_i16_tail"] {
            assert!(!result.rows.iter().find(|r| r.symbol == name).unwrap().replayed);
        }
        let mut mixed: serde_json::Value =
            serde_json::from_slice(&std::fs::read(dir.join("report.json")).unwrap()).unwrap();
        let legacy = include_bytes!("../../tests/fixtures/signed_leaf_original/store-i8-v1.json");
        assert_eq!(
            crate::object_replay::artifact_digest(legacy),
            "2374beb7e999459900575aacd2a122abb850a13207d1f679ade64835533d469a"
        );
        let rows = mixed["certificates"].as_array_mut().unwrap();
        rows.iter_mut().find(|r| r["symbol"] == "trust_c_i8_store").unwrap()["original_proof"] =
            serde_json::from_slice(legacy).unwrap();
        let stale = replay(&current.input(), &serde_json::to_vec(&mixed).unwrap()).unwrap();
        let rejected = stale.rows.iter().find(|r| r.symbol == "trust_c_i8_store").unwrap();
        assert!(!rejected.replayed && rejected.detail.contains("subject mismatch"), "{stale:?}");
        let fresh = std::fs::read(dir.join("current-compatible-v1.json")).unwrap();
        mixed["certificates"].as_array_mut().unwrap().iter_mut()
            .find(|r| r["symbol"] == "trust_c_i8_store").unwrap()["original_proof"] =
            serde_json::from_slice(&fresh).unwrap();
        let old_and_new = replay(&current.input(), &serde_json::to_vec(&mixed).unwrap()).unwrap();
        assert_eq!(old_and_new.rows.len(), 8);
        assert_eq!(old_and_new.rows.iter().filter(|r| r.replayed).count(), 6,
            "compatible v1 data must replay unchanged beside v2: {old_and_new:?}");
        for name in LEAVES.into_iter().chain(["trust_c_i8_store", "trust_c_i16_store"]) {
            assert!(old_and_new.rows.iter().find(|row| row.symbol == name).unwrap().replayed,
                "compatible mixed row {name}: {old_and_new:?}");
        }
        for name in ["trust_c_i8_tail", "trust_c_i16_tail"] {
            assert!(!old_and_new.rows.iter().find(|row| row.symbol == name).unwrap().replayed,
                "tail must remain outside original replay: {old_and_new:?}");
        }
        std::fs::write(
            dir.join("fresh-mixed-v1-v2.json"),
            serde_json::to_vec_pretty(&old_and_new).unwrap(),
        )
        .unwrap();
        std::fs::write(dir.join("fresh-replay.json"), serde_json::to_vec_pretty(&result).unwrap())
            .unwrap();
        return;
    }
    let current = load_current();
    let report = verify_compiled_module(&current.input()).unwrap();
    assert_eq!(report.certificates.len(), 8);
    assert_eq!(report.closure.closed_kernel.len(), 8);
    if let Some(out) = std::env::var_os("TRUST_SIGNED_LEAF_OUTPUT") {
        let out = std::path::PathBuf::from(out);
        std::fs::create_dir_all(&out).unwrap();
        std::fs::write(out.join("observed-report.json"), report.to_json()).unwrap();
    }

    for name in LEAVES {
        let row = report.certificate(name).unwrap();
        assert!(row.is_kernel_proved(), "{name}: {:?}", row.obligations);
        let packet =
            row.original_proof.as_ref().unwrap_or_else(|| panic!("{name}: {:?}", row.leaf_memory));
        assert_eq!(serde_json::to_value(packet).unwrap()["packet"]["model"], 2);
        let original = packet.original_equations();
        assert_eq!(original.len(), 27, "complete q64,21ABI,return,4entry laws");
        assert_eq!(
            trust_types::smt_logic::check_formula_sort(&original[22].0),
            Ok(Sort::BitVec(32))
        );
        assert_eq!(
            trust_types::smt_logic::check_formula_sort(&original[22].1),
            Ok(Sort::BitVec(32))
        );
        assert_eq!(row.leaf_memory.as_ref().unwrap().source_accesses, 0);
        assert_eq!(row.leaf_memory.as_ref().unwrap().machine_accesses, 0);
        assert_eq!(row.leaf_memory.as_ref().unwrap().source_coverage_bytes, 0);
        for bit in [31, 63] {
            assert!(original.iter().any(|(a, b)| {
                let mut found = false;
                for f in [a, b] {
                    f.visit(&mut |f| {
                        if matches!(f,Formula::BvExtract{high,..} if *high==bit) {
                            found = true;
                        }
                    });
                }
                found
            }));
        }
    }
    let tmp = tempfile::tempdir().unwrap();
    let out = std::env::var_os("TRUST_SIGNED_LEAF_OUTPUT")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| tmp.path().to_owned());
    std::fs::create_dir_all(&out).unwrap();
    let current_store = report.certificate("trust_c_i8_store").unwrap().original_proof.as_ref().unwrap();
    let compatible = current_store.test_legacy_wire_advice().unwrap();
    assert_eq!(serde_json::to_value(&compatible).unwrap()["packet"]["model"], 1);
    without_production(|| compatible.replay(current_store.original_equations())).unwrap();
    std::fs::write(out.join("current-compatible-v1.json"), serde_json::to_vec(&compatible).unwrap()).unwrap();
    std::fs::write(out.join("report.json"), report.to_json()).unwrap();
    std::fs::write(out.join("actual-current-object.o"), &current.object).unwrap();
    let child=std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact","call_event::signed_original_tests::actual_signed_leaves_keep_full_original_and_replay_in_fresh_process","--nocapture","--test-threads=1"])
        .env("TRUST_SIGNED_LEAF_REPLAY_CHILD",&out).output().unwrap();
    std::fs::write(out.join("child.stdout"), &child.stdout).unwrap();
    std::fs::write(out.join("child.stderr"), &child.stderr).unwrap();
    assert!(
        child.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&child.stdout),
        String::from_utf8_lossy(&child.stderr)
    );
    let sidecar = report.to_json();
    // Exact physical P and producer source are independently checked anew.
    let mut changed = load_current();
    let ReturnPlace::Scalar(ret) = &mut changed.placements.get_mut("trust_c_i8_id").unwrap().ret
    else {
        unreachable!()
    };
    ret.ext = AbiExt::Zext;
    assert!(
        replay(&changed.input(), sidecar.as_bytes()).map_or(true, |r| !r
            .rows
            .iter()
            .find(|r| r.symbol == "trust_c_i8_id")
            .unwrap()
            .replayed)
    );
    let mut changed = load_current();
    let producer = &mut changed.producers[changed.bodies["trust_c_i8_not"].producer];
    let mut module = (*producer.module).clone();
    let body = changed.bodies["trust_c_i8_not"].func;
    module.functions.iter_mut().find(|f| f.id == body).unwrap().name.push_str("_rebound");
    producer.module = Arc::new(module);
    assert!(
        replay(&changed.input(), sidecar.as_bytes()).map_or(true, |r| !r
            .rows
            .iter()
            .find(|r| r.symbol == "trust_c_i8_not")
            .unwrap()
            .replayed)
    );
    let mut forged: serde_json::Value = serde_json::from_str(&sidecar).unwrap();
    let rows = forged["certificates"].as_array_mut().unwrap();
    let row = rows.iter_mut().find(|r| r["symbol"] == "trust_c_i8_id").unwrap();
    row["original_proof"]["packet"]["proof_sha256"] = serde_json::json!("00".repeat(32));
    assert!(
        replay(&current.input(), &serde_json::to_vec(&forged).unwrap()).map_or(true, |r| !r
            .rows
            .iter()
            .find(|r| r.symbol == "trust_c_i8_id")
            .unwrap()
            .replayed)
    );
    let mut unknown: serde_json::Value = serde_json::from_str(&sidecar).unwrap();
    unknown["certificates"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|r| r["symbol"] == "trust_c_i8_id")
        .unwrap()["original_proof"]["packet"]["model"] = serde_json::json!(99);
    assert!(
        replay(&current.input(), &serde_json::to_vec(&unknown).unwrap()).map_or(true, |r| !r
            .rows
            .iter()
            .find(|r| r.symbol == "trust_c_i8_id")
            .unwrap()
            .replayed)
    );
    // Mutate only the real sign extension into zero extension; decode/model
    // verification is exercised, but these machine bytes are never executed.
    let parsed = crate::compiled_object::CompiledObject::parse(&current.object).unwrap();
    let text = &parsed.sections.iter().find(|s| s.name == "__TEXT,__text").unwrap().bytes;
    let text_offset = current.object.windows(text.len()).position(|b| b == text).unwrap();
    let row = report.certificate("trust_c_i8_id").unwrap();
    let range = row.extent.0 as usize..row.extent.1 as usize;
    let offset = range
        .step_by(4)
        .find(|at| {
            u32::from_le_bytes(text[*at..*at + 4].try_into().unwrap()) & 0x7f80_0000 == 0x1300_0000
        })
        .expect("actual signed extension");
    let mut object = current.object.clone();
    let at = text_offset + offset;
    let word = u32::from_le_bytes(object[at..at + 4].try_into().unwrap()) ^ 0x4000_0000;
    object[at..at + 4].copy_from_slice(&word.to_le_bytes());
    let input = CerInput { object: &object, ..current.input() };
    assert!(replay(&input, sidecar.as_bytes()).is_err());
    let bad = verify_compiled_module(&input).unwrap();
    assert!(!bad.certificate("trust_c_i8_id").unwrap().is_kernel_proved());
    std::fs::write(out.join("wrong-padding-report.json"), bad.to_json()).unwrap();
}

#[test]
fn retained_v1_specializes_to_v2_without_production_in_fresh_process() {
    if let Some(out) = std::env::var_os("TRUST_V1_SPECIALIZATION_CHILD") {
        // This is proof transport, not a fabricated machine call or caller
        // admission witness. The production caller owner still owes its sites.
        let historical = include_bytes!("../../tests/fixtures/signed_leaf_original/store-i8-v1.json");
        let stale: crate::original_conjunction_certificate::OriginalConjunctionCertificate =
            serde_json::from_slice(historical).unwrap();
        let refusal = without_production(|| stale.replay(stale.original_equations())).unwrap_err();
        assert!(refusal.contains("actual trusted kernel environment mismatch"), "{refusal}");
        let raw = std::fs::read(std::path::PathBuf::from(&out).join("current-compatible-v1.json")).unwrap();
        let old: crate::original_conjunction_certificate::OriginalConjunctionCertificate =
            serde_json::from_slice(&raw).unwrap();
        let instance = without_production(|| {
            let checked = old.replay(old.original_equations()).unwrap();
            let substitutions = checked
                .variable_sorts()
                .iter()
                .map(|(name, sort)| {
                    (name.clone(), Formula::Var(format!("caller::{name}"), sort.clone()))
                })
                .collect();
            let arg = Formula::Var("caller_argument".into(), Sort::BitVec(64));
            crate::original_conjunction_certificate::specialize_original_for_call(
                &checked,
                &substitutions,
                &[(arg.clone(), arg)],
            )
            .unwrap()
        });
        assert_eq!(instance.original_equations().len(), old.original_equations().len() + 1);
        assert_eq!(serde_json::to_value(instance.packet()).unwrap()["model"], 2);
        std::fs::write(std::path::PathBuf::from(out).join("v1-specialization.json"),serde_json::to_vec_pretty(&serde_json::json!({
            "old_model":1,"new_model":2,"historical_packet_refused":true,"old_packet_sha256":crate::object_replay::artifact_digest(&raw),
            "old_conjuncts":old.original_equations().len(),"new_conjuncts":instance.original_equations().len(),
            "producer_forbidden":true,"result":"kernel-checked proof specialization; no caller admission claim"})).unwrap()).unwrap();
        return;
    }
    let temp = tempfile::tempdir().unwrap();
    let out = std::env::var_os("TRUST_SIGNED_LEAF_OUTPUT")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| temp.path().to_owned());
    std::fs::create_dir_all(&out).unwrap();
    let historical: crate::original_conjunction_certificate::OriginalConjunctionCertificate =
        serde_json::from_slice(include_bytes!("../../tests/fixtures/signed_leaf_original/store-i8-v1.json")).unwrap();
    assert!(historical.test_legacy_wire_advice().err().unwrap().contains("historical packets cannot be retagged"));
    let current = load_current();
    let report = verify_compiled_module(&current.input()).unwrap();
    let checked = report.certificate("trust_c_i8_store").unwrap().original_proof.as_ref().unwrap();
    let compatible = checked.test_legacy_wire_advice().unwrap();
    without_production(|| compatible.replay(checked.original_equations())).unwrap();
    std::fs::write(out.join("current-compatible-v1.json"), serde_json::to_vec(&compatible).unwrap()).unwrap();
    let child=std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact","call_event::signed_original_tests::retained_v1_specializes_to_v2_without_production_in_fresh_process","--nocapture","--test-threads=1"])
        .env("TRUST_V1_SPECIALIZATION_CHILD",&out).output().unwrap();
    std::fs::write(out.join("v1-specialization.stdout"), &child.stdout).unwrap();
    std::fs::write(out.join("v1-specialization.stderr"), &child.stderr).unwrap();
    assert!(
        child.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&child.stdout),
        String::from_utf8_lossy(&child.stderr)
    );
}
