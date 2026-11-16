#![cfg(feature = "kernel-recheck")]
use super::*;
#[path = "../../tests/cer_common/mod.rs"]
mod cer_common;
use cer_common::*;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir::inst::{CastOp, Inst};
use trust_ir::{CallingConv, Endianness, Linkage, StructPassingPolicy, TargetInfo, Ty as IrTy};

use crate::call_event::{CerInput, CerReport, ProducerModule, replay_original_certificates};
use crate::verify_output::EmitPolicy;

fn fixture() -> Fixture {
    fixture_with_wide(false)
}
fn fixture_with_wide(include_wide: bool) -> Fixture {
    let mut b = ModBuilder::new("frameless_leaf_memory");
    let store = b.sig(&[IrTy::Ptr, IrTy::U64], Some(IrTy::U64));
    b.define("leaf_store", store, Linkage::External, |f| {
        let value = f.push_inst(Inst::Cast {
            op: CastOp::Trunc,
            src_ty: IrTy::U64,
            dst_ty: IrTy::U8,
            operand: f.p(1),
        });
        f.push_inst_void(Inst::Store {
            ty: IrTy::U8,
            ptr: f.p(0),
            value,
            volatile: false,
            align: Some(1),
        });
        let zero = f.konst(IrTy::U64, 0);
        f.ret(zero);
    });
    if include_wide {
        b.define("leaf_store_wide", store, Linkage::External, |f| {
            f.push_inst_void(Inst::Store {
                ty: IrTy::U64,
                ptr: f.p(0),
                value: f.p(1),
                volatile: false,
                align: Some(1),
            });
            let zero = f.konst(IrTy::U64, 0);
            f.ret(zero);
        });
    }
    let load = b.sig(&[IrTy::Ptr], Some(IrTy::U64));
    b.define("leaf_load", load, Linkage::External, |f| {
        let byte =
            f.push_inst(Inst::Load { ty: IrTy::U8, ptr: f.p(0), volatile: false, align: Some(1) });
        let value = f.push_inst(Inst::Cast {
            op: CastOp::ZExt,
            src_ty: IrTy::U8,
            dst_ty: IrTy::U64,
            operand: byte,
        });
        f.ret(value);
    });
    let copy = b.sig(&[IrTy::Ptr, IrTy::Ptr], Some(IrTy::U64));
    b.define("leaf_copy", copy, Linkage::External, |f| {
        let byte =
            f.push_inst(Inst::Load { ty: IrTy::U8, ptr: f.p(1), volatile: false, align: Some(1) });
        f.push_inst_void(Inst::Store {
            ty: IrTy::U8,
            ptr: f.p(0),
            value: byte,
            volatile: false,
            align: Some(1),
        });
        let zero = f.konst(IrTy::U64, 0);
        f.ret(zero);
    });
    b.define("leaf_gep", store, Linkage::External, |f| {
        let offset = f.konst(IrTy::U64, 1);
        let pointer = f.push_inst(Inst::GEP {
            pointee_ty: IrTy::U8,
            base: f.p(0),
            indices: vec![offset],
            inbounds: false,
        });
        let value = f.push_inst(Inst::Cast {
            op: CastOp::Trunc,
            src_ty: IrTy::U64,
            dst_ty: IrTy::U8,
            operand: f.p(1),
        });
        f.push_inst_void(Inst::Store {
            ty: IrTy::U8,
            ptr: pointer,
            value,
            volatile: false,
            align: Some(1),
        });
        let zero = f.konst(IrTy::U64, 0);
        f.ret(zero);
    });
    let mut module = b.finish();
    module.target_info = Some(TargetInfo {
        triple: DARWIN.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    });
    for function in &mut module.functions {
        function.calling_conv = CallingConv::Rust;
    }
    let object = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O3,
            parallel: false,
            emit_proofs: false,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(DARWIN).unwrap(),
    )
    .with_codegen_license(fixture_license())
    .compile(&module)
    .unwrap()
    .object_code;
    Fixture::with_object(module, object, DARWIN)
}

struct Sample {
    fixture: Fixture,
    sidecar: Vec<u8>,
    report: CerReport,
}
fn input(sample: &Sample) -> CerInput<'_> {
    let f = &sample.fixture;
    CerInput {
        m_cg: &f.m_cg,
        producers: &f.producers,
        bodies: &f.bodies,
        placements: &f.placements,
        object: &f.object,
        relocation_model: f.model,
    }
}
fn sample() -> &'static Sample {
    static SAMPLE: std::sync::OnceLock<Sample> = std::sync::OnceLock::new();
    SAMPLE.get_or_init(|| {
        assert!(
            std::env::var_os("TRUST_M8_ORIGINAL_OUTPUT_DIR").is_none(),
            "this control must use ordinary retention without diagnostic capture"
        );
        let fixture = fixture();
        let report = fixture.report();
        assert_eq!(report.certificates.len(), 4);
        assert_eq!(report.closure.closed_kernel.len(), 4, "{}", explain(&report));
        assert!(
            report
                .certificates
                .iter()
                .all(|row| row.is_kernel_proved() && row.original_proof.is_some()),
            "{}",
            explain(&report)
        );
        assert!(report.ships(EmitPolicy::StrictProvenOnly).is_ok());
        let sidecar = report.to_json().into_bytes();
        Sample { fixture, sidecar, report }
    })
}
fn packet(sample: &Sample) -> OriginalConjunctionCertificate {
    let value: serde_json::Value = serde_json::from_slice(&sample.sidecar).unwrap();
    serde_json::from_value(value["certificates"][0]["original_proof"].clone()).unwrap()
}
fn refused(input: &CerInput<'_>, bytes: &[u8]) {
    let result = without_production(|| replay_original_certificates(input, bytes));
    assert!(
        match &result {
            Err(_) => true,
            Ok(report) => !report.all_replayed(),
        },
        "{result:?}"
    );
}
#[derive(serde::Serialize, serde::Deserialize)]
struct ReplayInputs {
    m_cg: trust_ir::Module,
    producers: Vec<(trust_ir::Module, BTreeMap<trust_ir::value::FuncId, String>)>,
    bodies: Vec<(String, usize, trust_ir::value::FuncId)>,
    placements: BTreeMap<String, crate::call_event::FnPlacement>,
    relocation_model: crate::compiled_object::RelocationModel,
}
#[test]
fn actual_four_leaf_packets_replay_retained_terms_without_any_proof_producer() {
    // The subprocess takes this branch before sample()/Compiler/proof producer.
    // It has only untrusted retained packets and independently supplied actual
    // object/module/body/P inputs; no in-memory checked wrapper crosses here.
    if let Some(directory) = std::env::var_os("TRUST_ORIGINAL_PACKET_REPLAY_CHILD") {
        let directory = std::path::PathBuf::from(directory);
        let inputs: ReplayInputs =
            serde_json::from_slice(&std::fs::read(directory.join("expected-inputs.json")).unwrap())
                .unwrap();
        let object = std::fs::read(directory.join("object.o")).unwrap();
        let sidecar = std::fs::read(directory.join("ordinary-certificates.json")).unwrap();
        let producers: Vec<_> = inputs
            .producers
            .into_iter()
            .map(|(module, symbols)| ProducerModule { module: Arc::new(module), symbols })
            .collect();
        let bodies = inputs
            .bodies
            .into_iter()
            .map(|(name, producer, func)| {
                (name, crate::call_event::ProducerBody { producer, func })
            })
            .collect();
        let expected = CerInput {
            m_cg: &inputs.m_cg,
            producers: &producers,
            bodies: &bodies,
            placements: &inputs.placements,
            object: &object,
            relocation_model: inputs.relocation_model,
        };
        let replay =
            without_production(|| replay_original_certificates(&expected, &sidecar)).unwrap();
        assert_eq!(replay.rows.len(), 4);
        assert!(replay.all_replayed(), "{replay:?}");
        assert!(replay.rows.iter().all(|row| row.packet_bytes > 0 && row.term_nodes > 0));
        std::fs::write(
            directory.join("replay-result.json"),
            serde_json::to_vec_pretty(&replay).unwrap(),
        )
        .unwrap();
        return;
    }
    let s = sample();
    let temporary = tempfile::tempdir().unwrap();
    let out = temporary.path();
    let expected = ReplayInputs {
        m_cg: (*s.fixture.m_cg).clone(),
        producers: s
            .fixture
            .producers
            .iter()
            .map(|p| ((*p.module).clone(), p.symbols.clone()))
            .collect(),
        bodies: s
            .fixture
            .bodies
            .iter()
            .map(|(name, p)| (name.clone(), p.producer, p.func))
            .collect(),
        placements: s.fixture.placements.clone(),
        relocation_model: s.fixture.model,
    };
    std::fs::write(out.join("expected-inputs.json"), serde_json::to_vec(&expected).unwrap())
        .unwrap();
    std::fs::write(out.join("object.o"), &s.fixture.object).unwrap();
    std::fs::write(out.join("ordinary-certificates.json"), &s.sidecar).unwrap();
    let child = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "original_conjunction_certificate::tests::actual_four_leaf_packets_replay_retained_terms_without_any_proof_producer", "--nocapture", "--test-threads=1"])
        .env("TRUST_ORIGINAL_PACKET_REPLAY_CHILD",out)
        .env_remove("TRUST_M8_ORIGINAL_OUTPUT_DIR")
        .output().unwrap();
    std::fs::write(out.join("replay-child.stdout.log"), &child.stdout).unwrap();
    std::fs::write(out.join("replay-child.stderr.log"), &child.stderr).unwrap();
    assert!(
        child.status.success(),
        "fresh-process replay failed: {}\n{}",
        String::from_utf8_lossy(&child.stdout),
        String::from_utf8_lossy(&child.stderr)
    );
    let replay: crate::call_event::OriginalReplayReport =
        serde_json::from_slice(&std::fs::read(out.join("replay-result.json")).unwrap()).unwrap();
    assert!(replay.all_replayed());
    let total: usize = replay.rows.iter().map(|row| row.packet_bytes).sum();
    assert!(total < 8 * 1024 * 1024, "compact packet total {total}");
    std::fs::write(out.join("packet-metrics.json"),serde_json::to_vec_pretty(&serde_json::json!({
        "functions":4,"compact_total_bytes":total,"prior_raw_proof_json_bytes":90931233u64,
        "replay_millis":replay.elapsed_millis,"fresh_process":true,
        "proof_producer_and_solver_forbidden_during_replay":true,"child_exit_code":child.status.code()
    })).unwrap()).unwrap();
    if let Some(destination) = std::env::var_os("TRUST_ORIGINAL_PACKET_OUTPUT_DIR") {
        let destination = std::path::PathBuf::from(destination);
        std::fs::create_dir_all(&destination).unwrap();
        for file in std::fs::read_dir(out).unwrap() {
            let file = file.unwrap();
            std::fs::copy(file.path(), destination.join(file.file_name())).unwrap();
        }
    }
}

#[test]
fn retained_original_context_environment_and_valid_but_wrong_proof_all_refuse() {
    let original = packet(sample());
    let expected = original.packet.original.clone();
    let reject = |value: OriginalConjunctionCertificate| {
        assert!(without_production(|| value.replay(&expected)).is_err());
    };
    let mut changed = original.clone();
    changed.packet.original[0].0 = Formula::BitVec { value: 0, width: 64 };
    changed.packet.original_sha256 =
        encoded_hash(&changed.packet.original, MAX_ORIGINAL_BYTES).unwrap().0;
    reject(changed);
    let mut changed = original.clone();
    let name = changed.packet.context.bits.first().unwrap().clone();
    changed.packet.context.bits.remove(&name);
    changed.packet.context_sha256 =
        encoded_hash(&changed.packet.context, MAX_ORIGINAL_BYTES).unwrap().0;
    reject(changed);
    let mut changed = original.clone();
    changed.packet.environment_sha256 = "0".repeat(64);
    reject(changed);
    let mut changed = original.clone();
    changed.packet.environment_mode.push_str("-forged");
    reject(changed);
    let mut changed = original.clone();
    changed.packet.context.exact_byte_arrays = false;
    changed.packet.context_sha256 =
        encoded_hash(&changed.packet.context, MAX_ORIGINAL_BYTES).unwrap().0;
    reject(changed);
    let mut changed = original.clone();
    let mut narrowed = false;
    for (left, right) in &mut changed.packet.original {
        for formula in [left, right] {
            *formula = formula.clone().map(&mut |node| match node {
                Formula::Var(name, Sort::BitVec(64)) if name.starts_with("CER_LEAF_QUERY@") => {
                    narrowed = true;
                    Formula::BvZeroExt(
                        Box::new(Formula::BvExtract {
                            inner: Box::new(Formula::Var(name, Sort::BitVec(64))),
                            high: 31,
                            low: 0,
                        }),
                        32,
                    )
                }
                other => other,
            });
        }
    }
    assert!(narrowed);
    changed.packet.original_sha256 =
        encoded_hash(&changed.packet.original, MAX_ORIGINAL_BYTES).unwrap().0;
    reject(changed);
    // Valid DAG, all hashes updated, original goal unchanged: this reaches the
    // actual independent CIC checker rather than failing only a digest check.
    let mut changed = original.clone();
    let (goal, _) = changed.packet.terms.restore().unwrap();
    let false_proof = clean_kernel::Expr::const_str("True.intro");
    changed.packet.terms = TermPacket::capture(&goal, &false_proof).unwrap();
    changed.packet.proof_sha256 = encoded_hash(&false_proof, 64 * 1024 * 1024).unwrap().0;
    let failure = without_production(|| changed.replay(&expected)).unwrap_err();
    assert!(failure.contains("kernel rejection"), "{failure}");
}

#[test]
fn actual_subject_object_module_p_metadata_and_full_population_are_bound() {
    let s = sample();
    let real = input(s);
    // Changing, deleting or duplicating coverage equations cannot select a
    // different goal, skip a machine byte, or expand the full64 query domain.
    for mutation in 0..4 {
        let mut wire: serde_json::Value = serde_json::from_slice(&s.sidecar).unwrap();
        for row in wire["certificates"].as_array_mut().unwrap() {
            let mut packet: OriginalConjunctionCertificate =
                serde_json::from_value(row["original_proof"].clone()).unwrap();
            match mutation {
                0 => {
                    packet.packet.original[0].1 =
                        Formula::Var("not-an-actual-source-byte".into(), Sort::BitVec(64))
                }
                1 => {
                    packet.packet.original.remove(0);
                }
                2 => {
                    packet.packet.original.insert(0, packet.packet.original[0].clone());
                }
                _ => {
                    let (_, right) = packet
                        .packet
                        .original
                        .iter_mut()
                        .find(|(left, _)| matches!(left, Formula::Select(_, _)))
                        .unwrap();
                    if let Formula::Select(_, query) = right {
                        **query =
                            Formula::Var("not-the-fresh-full64-query".into(), Sort::BitVec(8));
                    }
                }
            }
            packet.packet.original_sha256 =
                encoded_hash(&packet.packet.original, MAX_ORIGINAL_BYTES).unwrap().0;
            row["original_proof"] = serde_json::to_value(packet).unwrap();
        }
        refused(&real, &serde_json::to_vec(&wire).unwrap());
    }
    let mut object = s.fixture.object.clone();
    let last = object.len() - 1;
    object[last] ^= 1;
    let mut changed = real;
    changed.object = &object;
    refused(&changed, &s.sidecar);
    let mut module = (*s.fixture.m_cg).clone();
    module.name.push_str("_different");
    let mut changed = real;
    changed.m_cg = &module;
    refused(&changed, &s.sidecar);
    let mut producers = s.fixture.producers.clone();
    let mut module = (*producers[0].module).clone();
    module.name.push_str("_different_source");
    producers[0].module = std::sync::Arc::new(module);
    let mut changed = real;
    changed.producers = &producers;
    refused(&changed, &s.sidecar);
    let mut placements = s.fixture.placements.clone();
    placements.get_mut("leaf_store").unwrap().ret = crate::call_event::ReturnPlace::Void;
    let mut changed = real;
    changed.placements = &placements;
    refused(&changed, &s.sidecar);
    let mut bodies = s.fixture.bodies.clone();
    bodies.get_mut("leaf_store").unwrap().producer = usize::MAX;
    let mut changed = real;
    changed.bodies = &bodies;
    refused(&changed, &s.sidecar);
    let mut changed = real;
    changed.relocation_model = crate::compiled_object::RelocationModel::Pic;
    refused(&changed, &s.sidecar);
    let mut value: serde_json::Value = serde_json::from_slice(&s.sidecar).unwrap();
    for row in value["certificates"].as_array_mut().unwrap() {
        row["text_sha256"] = serde_json::Value::String("0".repeat(64));
    }
    refused(&real, &serde_json::to_vec(&value).unwrap());
    let mut value: serde_json::Value = serde_json::from_slice(&s.sidecar).unwrap();
    for row in value["certificates"].as_array_mut().unwrap() {
        row["original_proof"] = serde_json::Value::Null;
    }
    let missing = without_production(|| {
        replay_original_certificates(&real, &serde_json::to_vec(&value).unwrap())
    })
    .unwrap();
    assert_eq!(missing.rows.len(), 4);
    assert!(!missing.all_replayed());
    let mut value: serde_json::Value = serde_json::from_slice(&s.sidecar).unwrap();
    value["certificates"].as_array_mut().unwrap().pop();
    refused(&real, &serde_json::to_vec(&value).unwrap());
}

#[test]
fn actual_missing_store_and_dead_read_cannot_reuse_a_subject_rebound_packet() {
    use crate::compiled_object::{CompiledObject, ObjectExpectations, ObjectLayout};
    let s = sample();
    let words = function_words(&s.fixture.object, "leaf_store");
    let store =
        words.iter().find(|(_, w)| w & 0xffc00000 == 0x39000000).copied().expect("actual STRB");
    let extract = words
        .iter()
        .find(|(_, w)| w & 0xfffffc00 == 0x53001c00)
        .copied()
        .expect("actual redundant byte truncation");
    for label in ["dropped-store", "dead-read"] {
        let mut object = s.fixture.object.clone();
        if label == "dropped-store" {
            patch_word(&mut object, store.0, 0xd503201f);
        } else {
            patch_word(&mut object, extract.0, 0x3940041f); // dead ldrb wzr,[x0,#1]
            patch_word(&mut object, store.0, (store.1 & !31) | 1); // same original low8 store
        }
        let mut actual = input(s);
        actual.object = &object;
        let parsed = CompiledObject::parse(&object).unwrap();
        let expectations =
            ObjectExpectations::from_module(actual.m_cg, parsed.format, actual.relocation_model)
                .unwrap();
        let layout = ObjectLayout::bind(parsed, &expectations).unwrap();
        let window = &layout.windows["leaf_store"];
        let mut fresh =
            s.report.certificates.iter().find(|row| row.symbol == "leaf_store").unwrap().clone();
        fresh.text_sha256 = window.text_sha256();
        let mut certificate: OriginalConjunctionCertificate = serde_json::from_value(
            serde_json::from_slice::<serde_json::Value>(&s.sidecar).unwrap()["certificates"]
                .as_array()
                .unwrap()
                .iter()
                .find(|row| row["symbol"] == "leaf_store")
                .unwrap()["original_proof"]
                .clone(),
        )
        .unwrap();
        // A hostile wire can rebind its public hashes to a new subject. That
        // grants no authority: fresh source/execution must still reconstruct
        // every original equality and consume the already-retained proof.
        certificate.subject = SubjectBinding::from_input(&actual, &fresh).unwrap();
        let mut wire: serde_json::Value = serde_json::from_slice(&s.sidecar).unwrap();
        wire["object_sha256"] = serde_json::Value::String(format!("{:x}", Sha256::digest(&object)));
        for row in wire["certificates"].as_array_mut().unwrap() {
            if row["symbol"] == "leaf_store" {
                row["text_sha256"] = serde_json::Value::String(fresh.text_sha256.clone());
                row["original_proof"] = serde_json::to_value(&certificate).unwrap();
            } else {
                row["original_proof"] = serde_json::Value::Null;
            }
        }
        let replay = without_production(|| {
            replay_original_certificates(&actual, &serde_json::to_vec(&wire).unwrap())
        })
        .unwrap();
        let row = replay.rows.iter().find(|row| row.symbol == "leaf_store").unwrap();
        assert!(!row.replayed, "{label}: {row:?}");
        assert!(
            !row.detail.contains("subject mismatch") && !row.detail.contains("metadata differs"),
            "must reach the actual semantic/census frontier: {label}: {row:?}"
        );
        assert!(
            row.detail.contains("original equations mismatch")
                || row.detail.contains("retained leaf")
                || row.detail.contains("source coverage"),
            "{label}: {row:?}"
        );
    }
}

#[test]
fn retained_grades_share_exact_ordinary_wire_and_population_bounds() {
    let sample = sample();
    let exact = bounded_pretty_len(&sample.report, MAX_SIDECAR_BYTES).unwrap();
    assert_eq!(exact, sample.sidecar.len());
    assert!(bounded_pretty_len(&sample.report, exact - 1).is_err());
    let mut report = sample.report.clone();
    enforce_report_limits(&mut report, MAX_REPLAY_FUNCTIONS + 1);
    assert_eq!(report.certificates.len(), 4);
    assert!(report.certificates.iter().all(|row| !row.is_kernel_proved()
        && row.original_proof.is_none()
        && row.grade == "Unknown"));
    assert!(report.closure.closed_kernel.is_empty());
    assert!(report.ships(EmitPolicy::StrictProvenOnly).is_err());
}
