// These are transport/refusal tests. Only the existing sample() test helper
// invokes the real compiler; no migration routine invokes a compiler or prover.
use super::*;

const ORIGINAL: &[u8] = include_bytes!("../compiler_frame_inputs/actual-b8-caller-input.json");
const HISTORICAL: HistoricalModuleTransportProfile =
    HistoricalModuleTransportProfile::OmittedEmptyTrailingClosureLayouts;

fn original_data() -> CompilerInputCapture {
    // Deliberate raw DATA access for constructing adversaries, not an accepted
    // strict decode and never an independent positive replay reference.
    serde_json::from_slice(ORIGINAL).unwrap()
}

fn raw_module(capture: &mut CompilerInputCapture, producer: bool) -> &mut ModuleBytes {
    if producer { &mut capture.producers[0].module } else { &mut capture.m_cg }
}

fn set_module_bytes(module: &mut ModuleBytes, bytes: Vec<u8>) {
    module.sha256 = artifact_digest(&bytes);
    module.bytes = bytes;
}

fn historical_module_for_test(module: &mut ModuleBytes) {
    // A test-only serialization of already-current complete DATA. The actual
    // historical positive is ORIGINAL, not this helper's synthetic output.
    let prefix = module.bytes.strip_suffix(b",\"closure_layouts\":[]}").unwrap();
    let mut bytes = prefix.to_vec();
    bytes.push(b'}');
    set_module_bytes(module, bytes);
    module.transport_profile = None;
}

fn historical_capture_for_test(mut capture: CompilerInputCapture) -> Vec<u8> {
    historical_module_for_test(&mut capture.m_cg);
    for row in &mut capture.producers {
        historical_module_for_test(&mut row.module);
    }
    capture.to_bytes().unwrap()
}

#[test]
fn original_remains_refused_and_explicit_migration_retains_all_original_bytes() {
    assert_eq!(
        artifact_digest(ORIGINAL),
        "fccc4c260617ebf86cc83a8bf32e56a17957aeb48949ea17050a997f116a2dae"
    );
    let original = original_data();
    assert_eq!(original.to_bytes().unwrap(), ORIGINAL);
    assert!(original.m_cg.decode().is_err());
    assert!(CompilerInputCapture::from_bytes(ORIGINAL).is_err());
    let migrated = migrate_historical_capture_data(ORIGINAL, HISTORICAL).unwrap();
    let output = migrated.capture.to_bytes().unwrap();
    assert_ne!(output, ORIGINAL);
    assert_eq!(migrated.receipt.input_capture_sha256, artifact_digest(ORIGINAL));
    assert_eq!(migrated.receipt.output_capture_sha256, artifact_digest(&output));
    assert_eq!(
        artifact_digest(&output),
        "5da1ac01c637fac56a1a48cafc0554e56e5ea327fb5d0ddd928e936bbda713e6"
    );
    assert_eq!(migrated.receipt.input_capture_schema, SCHEMA);
    assert_eq!(migrated.receipt.output_capture_schema, SCHEMA);
    assert_eq!(migrated.receipt.output_module_profile, MODULE_TRANSPORT_PROFILE);
    assert_eq!(migrated.receipt.added_default_field.as_deref(), Some("closure_layouts"));
    assert_eq!(migrated.receipt.modules.len(), 1 + original.producers.len());
    assert_eq!(migrated.receipt.modules[0].input_sha256, original.m_cg.sha256);
    assert_eq!(migrated.receipt.modules[1].input_sha256, original.producers[0].module.sha256);
    assert_eq!(migrated.receipt.modules[0].site, "m_cg");
    assert_eq!(migrated.receipt.modules[1].site, "producers[0].module");
    let accepted = CompilerInputCapture::from_bytes(&output).unwrap();
    assert_eq!(accepted, migrated.capture);
    let data = accepted.decode_inputs().unwrap();
    assert_eq!(data.object, original.object);
    assert_eq!(migrated.receipt.object_sha256, original.object_sha256);
    assert_eq!(
        artifact_digest(&data.object),
        "c4b9e1fcbc611f998c791cacd906ae735a5371528725829739995fe92c24e941"
    );
    assert!(data.m_cg.blobs.is_empty() && data.m_cg.closure_layouts.is_empty());
    // Restore ONLY the ModuleBytes fields in a comparison copy: every other
    // producer/config/body/P/layout/object/population field must be identical.
    let mut restored = migrated.capture.clone();
    restored.m_cg = original.m_cg.clone();
    for (old, new) in original.producers.iter().zip(&mut restored.producers) {
        new.module = old.module.clone();
    }
    assert_eq!(restored, original);
    // Migration did not change the original DATA into a strict decoded value.
    assert_eq!(original.to_bytes().unwrap(), ORIGINAL);
    assert!(original.decode_inputs().is_err());
}

#[test]
fn migration_requires_explicit_matching_profile_and_checks_every_module_digest() {
    use HistoricalModuleTransportProfile::CompleteUnprofiled;
    assert!(migrate_historical_capture_data(ORIGINAL, CompleteUnprofiled).is_err());
    let current = migrate_historical_capture_data(ORIGINAL, HISTORICAL).unwrap().capture;
    assert!(migrate_historical_capture_data(&current.to_bytes().unwrap(), HISTORICAL).is_err());
    let mut unprofiled = current.clone();
    unprofiled.m_cg.transport_profile = None;
    for row in &mut unprofiled.producers {
        row.module.transport_profile = None;
    }
    let wire = unprofiled.to_bytes().unwrap();
    assert!(!String::from_utf8(wire.clone()).unwrap().contains("transport_profile"));
    assert_eq!(CompilerInputCapture::from_bytes(&wire).unwrap(), unprofiled);
    assert!(migrate_historical_capture_data(&wire, HISTORICAL).is_err());
    let tagged = migrate_historical_capture_data(&wire, CompleteUnprofiled).unwrap();
    assert_eq!(tagged.capture, current);
    assert_eq!(tagged.receipt.added_default_field, None);
    assert!(tagged.receipt.modules.iter().all(|row| {
        row.input_sha256 == row.output_sha256 && row.input_bytes == row.output_bytes
    }));
    for producer in [false, true] {
        let mut changed = original_data();
        raw_module(&mut changed, producer).sha256 = "0".repeat(64);
        assert!(migrate_historical_capture_data(&changed.to_bytes().unwrap(), HISTORICAL).is_err());
        let mut changed = current.clone();
        raw_module(&mut changed, producer).transport_profile = Some("unknown-profile".into());
        assert!(CompilerInputCapture::from_bytes(&changed.to_bytes().unwrap()).is_err());
        assert!(
            migrate_historical_capture_data(&changed.to_bytes().unwrap(), CompleteUnprofiled)
                .is_err()
        );
    }
}

#[test]
fn historical_modules_reject_unknown_duplicate_reordered_and_spaced_data_at_every_site() {
    for producer in [false, true] {
        for mutation in 0..7 {
            let mut changed = original_data();
            let module = raw_module(&mut changed, producer);
            let wire = String::from_utf8(module.bytes.clone()).unwrap();
            let value: Module = serde_json::from_str(&wire).unwrap();
            let name = serde_json::to_string(&value.name).unwrap();
            let altered = match mutation {
                0 => format!("{},\"unknown_future_field\":0}}", wire.strip_suffix('}').unwrap()),
                1 => wire.replacen("{\"name\":", &format!("{{\"name\":{name},\"name\":"), 1),
                2 => wire.replacen(
                    "\"proof_context\":null",
                    "\"proof_context\":null,\"unknown_future_field\":0",
                    1,
                ),
                3 => wire.replacen(
                    "\"proof_context\":null",
                    "\"proof_context\":null,\"proof_context\":null",
                    1,
                ),
                4 => format!(" {wire}"),
                5 => format!("{wire}\n"),
                _ => {
                    let start = format!("{{\"name\":{name},");
                    let rest = wire.strip_prefix(&start).unwrap().strip_suffix('}').unwrap();
                    format!("{{{rest},\"name\":{name}}}")
                }
            };
            assert_ne!(altered, wire, "producer={producer} mutation={mutation}");
            set_module_bytes(module, altered.into_bytes());
            assert!(
                migrate_historical_capture_data(&changed.to_bytes().unwrap(), HISTORICAL).is_err(),
                "producer={producer} mutation={mutation}"
            );
        }
    }
}

#[test]
fn historical_outer_canonicality_population_scope_and_budget_are_not_relaxed() {
    let original = original_data();
    let wire = String::from_utf8(ORIGINAL.to_vec()).unwrap();
    let (name, row) = original.placements.iter().next().unwrap();
    let entry =
        format!("{}:{}", serde_json::to_string(name).unwrap(), serde_json::to_string(row).unwrap());
    let duplicate = wire.replacen(&entry, &format!("{entry},{entry}"), 1);
    assert_ne!(duplicate, wire);
    assert!(migrate_historical_capture_data(duplicate.as_bytes(), HISTORICAL).is_err());
    let unknown = format!("{},\"unknown\":0}}", wire.strip_suffix('}').unwrap());
    assert!(migrate_historical_capture_data(unknown.as_bytes(), HISTORICAL).is_err());
    assert!(migrate_historical_capture_data(format!("{wire}\n").as_bytes(), HISTORICAL).is_err());
    assert!(migrate_historical_capture_data(&[], HISTORICAL).is_err());
    assert!(migrate_historical_capture_data(&vec![b' '; MAX_WIRE_BYTES + 1], HISTORICAL).is_err());
    for mutation in 0..5 {
        let mut changed = original.clone();
        match mutation {
            0 => changed.schema.push_str("-unknown"),
            1 => changed.scope.push_str("-unknown"),
            2 => changed.expected_functions.clear(),
            3 => changed.bodies.push(changed.bodies[0].clone()),
            _ => changed.producers.clear(),
        }
        assert!(migrate_historical_capture_data(&changed.to_bytes().unwrap(), HISTORICAL).is_err());
    }
}

#[test]
fn new_tables_cannot_be_erased_and_current_tables_still_roundtrip() {
    let mut current = migrate_historical_capture_data(ORIGINAL, HISTORICAL).unwrap().capture;
    let mut module = current.m_cg.decode().unwrap();
    module.closure_types.push(trust_ir::ty::ClosureTy::bare(trust_ir::value::FuncTyId::new(0)));
    module.closure_layouts.push(trust_ir::ClosureLayoutDescriptor {
        closure: trust_ir::value::ClosureTyId::new(0),
        size: 0,
        align: 1,
        capture_offsets: Vec::new(),
        origin: None,
    });
    module.blobs.push(trust_ir::blob::Blob::new(vec![1, 2, 3]));
    current.m_cg = ModuleBytes::capture(&module).unwrap();
    let decoded = CompilerInputCapture::from_bytes(&current.to_bytes().unwrap()).unwrap();
    assert_eq!(decoded.m_cg.decode().unwrap(), module);
    current.m_cg.transport_profile = None;
    for row in &mut current.producers {
        row.module.transport_profile = None;
    }
    let wire = current.to_bytes().unwrap();
    assert!(migrate_historical_capture_data(&wire, HISTORICAL).is_err());
    let upgraded = migrate_historical_capture_data(
        &wire,
        HistoricalModuleTransportProfile::CompleteUnprofiled,
    )
    .unwrap();
    assert_eq!(upgraded.capture.m_cg.decode().unwrap(), module);
    assert_eq!(upgraded.receipt.modules[0].input_sha256, upgraded.receipt.modules[0].output_sha256);
}

#[test]
fn canonical_migrated_data_never_authenticates_changed_inputs_for_original_replay() {
    // Actual compiled source/producers/P/object/config chosen independently of
    // every altered retained capture below. No decoded retained capture is its
    // own positive authentication reference.
    let s = sample();
    let base = historical_capture_for_test(s.capture.clone());
    let same = migrate_historical_capture_data(&base, HISTORICAL).unwrap();
    assert_eq!(same.capture, s.capture);
    for mutation in 0..10 {
        let mut changed = s.capture.clone();
        match mutation {
            0 => {
                let mut module = changed.m_cg.decode().unwrap();
                module.types.push(Ty::U8);
                changed.m_cg = ModuleBytes::capture(&module).unwrap();
            }
            1 => {
                let mut module = changed.producers[0].module.decode().unwrap();
                module.name.push_str("_foreign_producer");
                changed.producers[0].module = ModuleBytes::capture(&module).unwrap();
            }
            2 => {
                let mut module = changed.m_cg.decode().unwrap();
                let mut changed_store = false;
                for block in &mut module.functions[0].blocks {
                    for node in &mut block.body {
                        if let Inst::Store { volatile, .. } = &mut node.inst {
                            *volatile = !*volatile;
                            changed_store = true;
                        }
                    }
                }
                assert!(changed_store);
                changed.m_cg = ModuleBytes::capture(&module).unwrap();
            }
            3 => {
                let mut module = changed.m_cg.decode().unwrap();
                module.target_info.as_mut().unwrap().pointer_size = 4;
                changed.m_cg = ModuleBytes::capture(&module).unwrap();
            }
            4 => changed.producers[0].symbols.push((44, "foreign_symbol".into())),
            5 => changed.bodies[0].function = 44,
            6 => {
                changed.placements.remove("captured_store");
            }
            7 => changed.configuration.opt_level = 0,
            8 => {
                let last = changed.object.len() - 1;
                changed.object[last] ^= 1;
                changed.object_sha256 = artifact_digest(&changed.object);
            }
            _ => changed.configuration.effective_backend_settings.push_str("_foreign_settings"),
        }
        let wire = historical_capture_for_test(changed);
        // Valid canonical altered DATA can migrate. It is NOT authenticated.
        let migrated = migrate_historical_capture_data(&wire, HISTORICAL).unwrap();
        let reason = migrated
            .capture
            .replay_original(&input(&s.fixture), &s.configuration, &s.sidecar)
            .unwrap_err();
        assert_eq!(
            reason, "compiler capture independent current subject/config mismatch",
            "mutation={mutation}"
        );
    }
}

#[test]
fn raw_module_profile_null_duplicate_reorder_and_known_mixed_inputs_refuse() {
    use HistoricalModuleTransportProfile::CompleteUnprofiled;
    let current = migrate_historical_capture_data(ORIGINAL, HISTORICAL).unwrap().capture;
    let wire = String::from_utf8(current.to_bytes().unwrap()).unwrap();
    let tag = format!(
        "\"transport_profile\":{}",
        serde_json::to_string(MODULE_TRANSPORT_PROFILE).unwrap()
    );
    assert!(wire.contains(&tag));

    let null = wire.replacen(&tag, "\"transport_profile\":null", 1);
    // Option's raw null decodes as None, but exact outer canonicality rejects
    // it rather than treating an explicitly present null as omitted data.
    assert!(serde_json::from_str::<CompilerInputCapture>(&null).is_ok());
    assert!(CompilerInputCapture::from_bytes(null.as_bytes()).is_err());
    for profile in [HISTORICAL, CompleteUnprofiled] {
        assert!(migrate_historical_capture_data(null.as_bytes(), profile).is_err());
    }

    let duplicate = wire.replacen(&tag, &format!("{tag},{tag}"), 1);
    assert_ne!(duplicate, wire);
    assert!(serde_json::from_str::<CompilerInputCapture>(&duplicate).is_err());
    assert!(CompilerInputCapture::from_bytes(duplicate.as_bytes()).is_err());
    for profile in [HISTORICAL, CompleteUnprofiled] {
        assert!(migrate_historical_capture_data(duplicate.as_bytes(), profile).is_err());
    }

    let reordered = wire.replacen(&format!(",{tag}"), "", 1).replacen(
        "\"m_cg\":{\"bytes\":",
        &format!("\"m_cg\":{{{tag},\"bytes\":"),
        1,
    );
    assert_ne!(reordered, wire);
    assert!(serde_json::from_str::<CompilerInputCapture>(&reordered).is_ok());
    assert!(CompilerInputCapture::from_bytes(reordered.as_bytes()).is_err());
    for profile in [HISTORICAL, CompleteUnprofiled] {
        assert!(migrate_historical_capture_data(reordered.as_bytes(), profile).is_err());
    }

    // Exercise the known-tagged PRODUCER refusal after a successfully checked
    // unprofiled main Module, separately for BOTH explicit migration profiles.
    let mut historical_mixed = original_data();
    historical_mixed.producers[0].module = current.producers[0].module.clone();
    assert!(historical_mixed.m_cg.transport_profile.is_none());
    assert_eq!(
        historical_mixed.producers[0].module.transport_profile.as_deref(),
        Some(MODULE_TRANSPORT_PROFILE)
    );
    let error = migrate_historical_capture_data(&historical_mixed.to_bytes().unwrap(), HISTORICAL)
        .unwrap_err();
    assert_eq!(error, "historical Module migration requires an unprofiled input");

    let mut complete_mixed = current;
    complete_mixed.m_cg.transport_profile = None;
    let mixed_wire = complete_mixed.to_bytes().unwrap();
    // Mixed None/current tags are valid strictly CURRENT transport DATA.
    // The explicit migration API still refuses because it cannot relabel an
    // already-tagged producer as if it belonged to the requested old profile.
    assert!(CompilerInputCapture::from_bytes(&mixed_wire).is_ok());
    let error = migrate_historical_capture_data(&mixed_wire, CompleteUnprofiled).unwrap_err();
    assert_eq!(error, "historical Module migration requires an unprofiled input");
}

#[test]
fn both_explicit_migrations_replay_the_independently_selected_original_without_production() {
    use HistoricalModuleTransportProfile::CompleteUnprofiled;
    // The existing real compiler chooses source/producers/P/config/object and
    // produces the original sidecar BEFORE either migration or replay guard.
    // Expected inputs come from that separate actual fixture, never from a
    // decoded retained or migrated capture.
    let s = sample();
    let reference = input(&s.fixture);
    for profile in [HISTORICAL, CompleteUnprofiled] {
        let wire = match profile {
            HistoricalModuleTransportProfile::OmittedEmptyTrailingClosureLayouts => {
                historical_capture_for_test(s.capture.clone())
            }
            CompleteUnprofiled => {
                let mut unprofiled = s.capture.clone();
                unprofiled.m_cg.transport_profile = None;
                for row in &mut unprofiled.producers {
                    row.module.transport_profile = None;
                }
                unprofiled.to_bytes().unwrap()
            }
        };
        let migrated = migrate_historical_capture_data(&wire, profile).unwrap();
        assert_eq!(migrated.capture, s.capture);
        let report = crate::original_conjunction_certificate::without_production(|| {
            migrated.capture.replay_original(&reference, &s.configuration, &s.sidecar)
        })
        .unwrap();
        assert!(report.all_replayed(), "profile={profile:?}: {report:?}");
        assert_eq!(report.rows.len(), 1);
    }
}
