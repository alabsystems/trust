#![cfg(feature = "kernel-recheck")]
use super::*;
#[path = "../../tests/cer_common/mod.rs"]
mod cer_common;
use cer_common::*;
use trust_ir::inst::{CastOp, Inst};
use trust_ir::{
    BodyGate, CallingConv, Endianness, Linkage, Producer, StructPassingPolicy, TargetInfo, Ty,
};

use crate::f1_compile::{
    F1CompileInput, F1OptLevel, F1Target, TRUST_DIRECT_LANE_AUTHORITY,
    compile_and_verify_trust_ir_module_captured,
};

fn config() -> F1CompileConfig {
    F1CompileConfig {
        force_frame_pointers: false,
        target: F1Target::Aarch64AppleDarwin,
        opt_level: F1OptLevel::O3,
        relocation: RelocationModel::Static,
        never_inline: BTreeSet::new(),
        upstream_mir_lane: false,
    }
}
#[test]
fn expected_configuration_distinguishes_force_frame_pointer_codegen() {
    let mut config = config();
    let ordinary = CompilerCaptureConfig::expected(&config, EmitPolicy::AllowUnknown).unwrap();
    config.force_frame_pointers = true;
    let forced = CompilerCaptureConfig::expected(&config, EmitPolicy::AllowUnknown).unwrap();
    assert_ne!(ordinary, forced);
    assert!(ordinary.effective_backend_settings.contains("aarch64_force_frame_pointers: false"));
    assert!(forced.effective_backend_settings.contains("aarch64_force_frame_pointers: true"));
    assert_eq!(ordinary.output_policy, forced.output_policy);
    assert_eq!(ordinary.abi_scope, forced.abi_scope);
}

fn model() -> Module {
    let mut builder = ModBuilder::new("compiler_capture_actual");
    let sig = builder.sig(&[Ty::Ptr, Ty::U64], Some(Ty::U64));
    builder.define("captured_store", sig, Linkage::External, |f| {
        let value = f.push_inst(Inst::Cast {
            op: CastOp::Trunc,
            src_ty: Ty::U64,
            dst_ty: Ty::U8,
            operand: f.p(1),
        });
        f.push_inst_void(Inst::Store {
            ty: Ty::U8,
            ptr: f.p(0),
            value,
            volatile: false,
            align: Some(1),
        });
        let zero = f.konst(Ty::U64, 0);
        f.ret(zero);
    });
    let mut module = builder.finish();
    module.target_info = Some(TargetInfo {
        triple: DARWIN.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    });
    for function in &mut module.functions {
        function.producer = Some(Producer::TRust);
        function.calling_conv = CallingConv::Rust;
        function.body_gate =
            Some(BodyGate::Gated { authority: TRUST_DIRECT_LANE_AUTHORITY.into(), evidence: None });
    }
    module
}
struct Sample {
    fixture: Fixture,
    configuration: CompilerCaptureConfig,
    capture: CompilerInputCapture,
    sidecar: Vec<u8>,
}
fn input(f: &Fixture) -> CerInput<'_> {
    CerInput {
        m_cg: &f.m_cg,
        producers: &f.producers,
        bodies: &f.bodies,
        placements: &f.placements,
        object: &f.object,
        relocation_model: f.model,
    }
}
fn sample() -> Sample {
    // This is an explicit hand-built ABI fixture, not a rustc FnAbi witness.
    let mut fixture = Fixture::with_object(model(), Vec::new(), DARWIN);
    let cfg = config();
    let observed = compile_and_verify_trust_ir_module_captured(&F1CompileInput {
        m_cg: &fixture.m_cg,
        producers: &fixture.producers,
        bodies: &fixture.bodies,
        placements: &fixture.placements,
        policy: EmitPolicy::StrictProvenOnly,
        config: &cfg,
    });
    let capture = observed.capture.unwrap();
    let shipped = observed.outcome.unwrap();
    assert_eq!(shipped.report.closure.closed_kernel, vec!["captured_store"]);
    fixture.object = shipped.object;
    Sample {
        fixture,
        configuration: CompilerCaptureConfig::expected(&cfg, EmitPolicy::StrictProvenOnly).unwrap(),
        capture,
        sidecar: shipped.report.to_json().into_bytes(),
    }
}

#[test]
fn actual_compiler_capture_replays_in_fresh_process_with_production_forbidden() {
    if let Some(directory) = std::env::var_os("TRUST_COMPILER_CAPTURE_REPLAY_CHILD") {
        let directory = std::path::PathBuf::from(directory);
        // The independent reference is supplied in a separate packet chosen by
        // the parent, never reconstructed from retained input/grade/hash data.
        let expected: Expected =
            serde_json::from_slice(&std::fs::read(directory.join("expected.json")).unwrap())
                .unwrap();
        let producers: Vec<_> = expected
            .producers
            .into_iter()
            .map(|(module, symbols)| ProducerModule { module: Arc::new(module), symbols })
            .collect();
        let bodies = expected
            .bodies
            .into_iter()
            .map(|(s, p, id)| (s, ProducerBody { producer: p, func: id }))
            .collect();
        let current = CerInput {
            m_cg: &expected.m_cg,
            producers: &producers,
            bodies: &bodies,
            placements: &expected.placements,
            object: &expected.object,
            relocation_model: RelocationModel::Static,
        };
        let capture = CompilerInputCapture::from_bytes(
            &std::fs::read(directory.join("capture.json")).unwrap(),
        )
        .unwrap();
        let sidecar = std::fs::read(directory.join("sidecar.json")).unwrap();
        let result = crate::original_conjunction_certificate::without_production(|| {
            capture.replay_original(&current, &expected.configuration, &sidecar)
        })
        .unwrap();
        assert!(result.all_replayed(), "{result:?}");
        assert_eq!(result.rows.len(), 1);
        return;
    }
    let s = sample();
    let directory = tempfile::tempdir().unwrap();
    let reference = Expected {
        m_cg: (*s.fixture.m_cg).clone(),
        producers: s
            .fixture
            .producers
            .iter()
            .map(|p| ((*p.module).clone(), p.symbols.clone()))
            .collect(),
        bodies: s.fixture.bodies.iter().map(|(n, p)| (n.clone(), p.producer, p.func)).collect(),
        placements: s.fixture.placements.clone(),
        object: s.fixture.object.clone(),
        configuration: s.configuration.clone(),
    };
    std::fs::write(directory.path().join("expected.json"), serde_json::to_vec(&reference).unwrap())
        .unwrap();
    std::fs::write(directory.path().join("capture.json"), s.capture.to_bytes().unwrap()).unwrap();
    std::fs::write(directory.path().join("sidecar.json"), s.sidecar).unwrap();
    let child=std::process::Command::new(std::env::current_exe().unwrap()).args(["--exact","compiler_input_capture::tests::actual_compiler_capture_replays_in_fresh_process_with_production_forbidden","--nocapture","--test-threads=1"])
        .env("TRUST_COMPILER_CAPTURE_REPLAY_CHILD",directory.path()).output().unwrap();
    assert!(
        child.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&child.stdout),
        String::from_utf8_lossy(&child.stderr)
    );
}
#[derive(Serialize, Deserialize)]
struct Expected {
    m_cg: Module,
    producers: Vec<(Module, BTreeMap<FuncId, String>)>,
    bodies: Vec<(String, usize, FuncId)>,
    placements: BTreeMap<String, FnPlacement>,
    object: Vec<u8>,
    configuration: CompilerCaptureConfig,
}

#[test]
fn forged_complete_self_hashes_do_not_authenticate_a_changed_source_or_object() {
    let s = sample();
    let mut changed = s.capture.clone();
    let mut module = changed.m_cg.decode().unwrap();
    module.name.push_str("_fabricated");
    changed.m_cg = ModuleBytes::capture(&module).unwrap();
    let decoded = CompilerInputCapture::from_bytes(&changed.to_bytes().unwrap()).unwrap();
    assert!(decoded.replay_original(&input(&s.fixture), &s.configuration, &s.sidecar).is_err());
    changed = s.capture.clone();
    let last = changed.object.len() - 1;
    changed.object[last] ^= 1;
    changed.object_sha256 = artifact_digest(&changed.object);
    let decoded = CompilerInputCapture::from_bytes(&changed.to_bytes().unwrap()).unwrap();
    assert!(decoded.replay_original(&input(&s.fixture), &s.configuration, &s.sidecar).is_err());
}

#[test]
fn replay_binds_all_producers_symbols_body_mapping_placements_and_configuration() {
    let s = sample();
    let mut producers = s.fixture.producers.clone();
    // Include an otherwise unused module/symbol entry in the actual reference:
    // a replayer may not silently discard it as irrelevant to the selected row.
    producers.push(ProducerModule::named_by_symbols(Arc::new(Module::new("unused_producer"))));
    let reference = CerInput { producers: &producers, ..input(&s.fixture) };
    let full = CompilerInputCapture::capture(&reference, s.configuration.clone()).unwrap();
    for mutation in 0..7 {
        let mut changed = full.clone();
        match mutation {
            0 => {
                changed.producers.pop();
            }
            1 => {
                changed.producers[1].symbols.push((44, "unused_symbol".into()));
            }
            2 => {
                changed.bodies[0].function = 44;
            }
            3 => {
                changed.placements.remove("captured_store");
            }
            4 => {
                changed.configuration.opt_level = 0;
            }
            5 => {
                changed.configuration.effective_backend_settings.push_str("_forged");
            }
            _ => {
                changed.configuration.upstream_mir_lane = true;
            }
        }
        assert!(
            changed.replay_original(&reference, &s.configuration, &s.sidecar).is_err(),
            "mutation{mutation}"
        );
    }
}

#[test]
fn malformed_population_labels_and_capacity_never_decode_as_complete_inputs() {
    let s = sample();
    for mutation in 0..5 {
        let mut changed = s.capture.clone();
        match mutation {
            0 => changed.expected_functions.clear(),
            1 => changed.bodies.push(changed.bodies[0].clone()),
            2 => changed.bodies[0].producer = 99,
            3 => {
                let repeated = changed.producers[0].symbols[0].clone();
                changed.producers[0].symbols.push(repeated);
            }
            _ => {
                changed.placements.insert(
                    "x".repeat(MAX_LABEL_BYTES + 1),
                    changed.placements["captured_store"].clone(),
                );
            }
        }
        assert!(CompilerInputCapture::from_bytes(&changed.to_bytes().unwrap()).is_err());
    }
    let mut too_many = (*s.fixture.m_cg).clone();
    while too_many.functions.len() <= MAX_FUNCTIONS {
        let mut f = too_many.functions[0].clone();
        f.id = FuncId::new(too_many.functions.len() as u32);
        f.name = format!("copy{}", f.id.index());
        too_many.functions.push(f);
    }
    let current = CerInput { m_cg: &too_many, ..input(&s.fixture) };
    let reason = CompilerInputCapture::capture(&current, s.configuration.clone()).unwrap_err();
    assert!(reason.status.contains("incomplete"));
    assert!(reason.to_bytes().unwrap().len() < MAX_PART_BYTES);
    assert!(CompilerInputCapture::from_bytes(&reason.to_bytes().unwrap()).is_err());
    assert!(CompilerInputCapture::from_bytes(&vec![b' '; MAX_WIRE_BYTES + 1]).is_err());
}

#[test]
fn forbidden_producer_refusal_is_unchanged_and_records_no_fictional_cer_input() {
    let mut module = model();
    module.functions[0].producer = Some(Producer::Clean);
    let fixture = Fixture::with_object(module, Vec::new(), DARWIN);
    let cfg = config();
    let result = compile_and_verify_trust_ir_module_captured(&F1CompileInput {
        m_cg: &fixture.m_cg,
        producers: &fixture.producers,
        bodies: &fixture.bodies,
        placements: &fixture.placements,
        policy: EmitPolicy::StrictProvenOnly,
        config: &cfg,
    });
    assert!(matches!(result.outcome, Err(crate::f1_compile::F1Refusal::Boundary(_))));
    let incomplete = result.capture.unwrap_err();
    assert!(incomplete.object_sha256.is_none());
    assert!(incomplete.reason.contains("not reached"));
}

#[test]
fn optional_capture_capacity_refusal_preserves_ordinary_strict_outcome() {
    let fixture = Fixture::with_object(model(), Vec::new(), DARWIN);
    let mut cfg = config();
    // These names do not change this module's code. They exceed only the
    // optional diagnostic configuration budget, not the normal Compiler path.
    cfg.never_inline = (0..=MAX_FUNCTIONS * 2).map(|i| format!("unused_{i}")).collect();
    let compiler_input = F1CompileInput {
        m_cg: &fixture.m_cg,
        producers: &fixture.producers,
        bodies: &fixture.bodies,
        placements: &fixture.placements,
        policy: EmitPolicy::StrictProvenOnly,
        config: &cfg,
    };
    let observed = compile_and_verify_trust_ir_module_captured(&compiler_input);
    let incomplete = observed.capture.unwrap_err();
    assert!(incomplete.reason.contains("configuration label/population budget"));
    assert!(incomplete.object_sha256.is_some());
    let captured = observed.outcome.unwrap();
    let ordinary = crate::f1_compile::compile_and_verify_trust_ir_module(&compiler_input).unwrap();
    assert_eq!(captured.object, ordinary.object);
    assert_eq!(captured.report.object_sha256, ordinary.report.object_sha256);
    assert_eq!(captured.report.closure.closed_kernel, vec!["captured_store"]);
    assert_eq!(captured.report.closure.closed_kernel, ordinary.report.closure.closed_kernel);
    assert_eq!(captured.report.certificates.len(), ordinary.report.certificates.len());
    assert_eq!(captured.unclosed, ordinary.unclosed);
}

#[test]
fn outer_wire_rejects_duplicate_placement_keys_and_noncanonical_json() {
    let s = sample();
    let bytes = s.capture.to_bytes().unwrap();
    let mut spaced = bytes.clone();
    spaced.push(b'\n');
    assert!(CompilerInputCapture::from_bytes(&spaced).is_err());
    let wire = String::from_utf8(bytes).unwrap();
    let row = serde_json::to_string(&s.capture.placements["captured_store"]).unwrap();
    let original = format!("\"placements\":{{\"captured_store\":{row}}}");
    let duplicate = format!("\"placements\":{{\"captured_store\":{row},\"captured_store\":{row}}}");
    let changed = wire.replacen(&original, &duplicate, 1);
    assert_ne!(wire, changed);
    // serde's BTreeMap itself accepts duplicate keys with the last value;
    // canonical wire decoding must retain and enforce their absence.
    assert_eq!(serde_json::from_str::<CompilerInputCapture>(&changed).unwrap(), s.capture);
    assert!(CompilerInputCapture::from_bytes(changed.as_bytes()).is_err());
}

#[test]
fn actual_archive_member_replays_original_in_fresh_child_without_proof_production() {
    if let Some(directory) = std::env::var_os("TRUST_COMPILER_ARCHIVE_REPLAY_CHILD") {
        let directory = std::path::PathBuf::from(directory);
        let expected: Expected =
            serde_json::from_slice(&std::fs::read(directory.join("expected.json")).unwrap())
                .unwrap();
        let producers: Vec<_> = expected
            .producers
            .into_iter()
            .map(|(module, symbols)| ProducerModule { module: Arc::new(module), symbols })
            .collect();
        let bodies = expected
            .bodies
            .into_iter()
            .map(|(name, producer, func)| (name, ProducerBody { producer, func }))
            .collect();
        let current = CerInput {
            m_cg: &expected.m_cg,
            producers: &producers,
            bodies: &bodies,
            placements: &expected.placements,
            object: &expected.object,
            relocation_model: RelocationModel::Static,
        };
        let capture = CompilerInputCapture::from_bytes(
            &std::fs::read(directory.join("capture.json")).unwrap(),
        )
        .unwrap();
        let archive = std::fs::read(directory.join("archive.rlib")).unwrap();
        let sidecar = std::fs::read(directory.join("sidecar.json")).unwrap();
        let replay = crate::original_conjunction_certificate::without_production(|| {
            capture.replay_original_in_archive(
                &current,
                &expected.configuration,
                &sidecar,
                &archive,
                "unit.o",
                ArchiveObjectPadding::DarwinEightByte,
            )
        })
        .unwrap();
        assert_eq!(replay.member.archive_sha256, artifact_digest(&archive));
        assert_eq!(replay.member.object_sha256, artifact_digest(&expected.object));
        assert!(replay.object_proofs.all_replayed());
        assert_eq!(replay.object_proofs.rows.len(), 1);
        assert!(replay.object_proofs.unverified_sections.is_empty());
        return;
    }
    let s = sample();
    let mut stream = std::io::Cursor::new(Vec::new());
    let members = [ar_archive_writer::NewArchiveMember::new(
        s.fixture.object.as_slice(),
        &ar_archive_writer::DEFAULT_OBJECT_READER,
        "unit.o".into(),
    )];
    ar_archive_writer::write_archive_to_stream(
        &mut stream,
        &members,
        ar_archive_writer::ArchiveKind::Darwin,
        false,
        None,
    )
    .unwrap();
    let archive = stream.into_inner();
    let reference = Expected {
        m_cg: (*s.fixture.m_cg).clone(),
        producers: s
            .fixture
            .producers
            .iter()
            .map(|p| ((*p.module).clone(), p.symbols.clone()))
            .collect(),
        bodies: s.fixture.bodies.iter().map(|(n, p)| (n.clone(), p.producer, p.func)).collect(),
        placements: s.fixture.placements.clone(),
        object: s.fixture.object.clone(),
        configuration: s.configuration.clone(),
    };
    let directory = tempfile::tempdir().unwrap();
    std::fs::write(directory.path().join("expected.json"), serde_json::to_vec(&reference).unwrap())
        .unwrap();
    std::fs::write(directory.path().join("capture.json"), s.capture.to_bytes().unwrap()).unwrap();
    std::fs::write(directory.path().join("sidecar.json"), &s.sidecar).unwrap();
    std::fs::write(directory.path().join("archive.rlib"), &archive).unwrap();
    let child=std::process::Command::new(std::env::current_exe().unwrap()).args(["--exact",
        "compiler_input_capture::tests::actual_archive_member_replays_original_in_fresh_child_without_proof_production",
        "--nocapture","--test-threads=1"])
        .env("TRUST_COMPILER_ARCHIVE_REPLAY_CHILD",directory.path()).output().unwrap();
    assert!(
        child.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&child.stdout),
        String::from_utf8_lossy(&child.stderr)
    );

    // Correct byte membership cannot authenticate a different current source.
    let mut changed = (*s.fixture.m_cg).clone();
    changed.name.push_str("_different_current_source");
    let wrong = CerInput { m_cg: &changed, ..input(&s.fixture) };
    crate::original_conjunction_certificate::without_production(|| {
        assert!(
            s.capture
                .replay_original_in_archive(
                    &wrong,
                    &s.configuration,
                    &s.sidecar,
                    &archive,
                    "unit.o",
                    ArchiveObjectPadding::DarwinEightByte
                )
                .is_err()
        );
        assert!(
            s.capture
                .replay_original_in_archive(
                    &input(&s.fixture),
                    &s.configuration,
                    &s.sidecar,
                    &archive,
                    "absent.o",
                    ArchiveObjectPadding::DarwinEightByte
                )
                .is_err()
        );
    });
}

#[path = "migration_tests.rs"]
mod migration_tests;

#[test]
fn frozen_old_modules_without_current_layout_table_remain_noncanonical() {
    let cases: &[(&[u8], &str)] = &[
        (
            include_bytes!("../../tests/fixtures/signed_o0_original/compiler-input.json"),
            "8b0fea9f81e69a36adab955bcb2bb3ad158aaaf1ebe63c20439da1944199f104",
        ),
        (
            include_bytes!("../compiler_frame_inputs/actual-b8-caller-input.json"),
            "fccc4c260617ebf86cc83a8bf32e56a17957aeb48949ea17050a997f116a2dae",
        ),
    ];
    for (bytes, digest) in cases {
        assert_eq!(crate::object_replay::artifact_digest(bytes), *digest);
        let error = CompilerInputCapture::from_bytes(bytes)
            .and_then(|capture| capture.decode_inputs())
            .err()
            .expect("historical transport must refuse before producing current inputs");
        assert_eq!(error, "compiler capture Module transport is noncanonical");
    }
}
