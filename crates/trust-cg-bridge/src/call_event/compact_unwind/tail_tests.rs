use super::*;

fn tail_fixture() -> Fixture {
    let mut b = ModBuilder::new("m5_actual_tail_instances");
    let store_sig = b.sig(&[Ty::Ptr, Ty::U64], Some(Ty::U64));
    let store = b.define("memory_store", store_sig, Linkage::External, |f| {
        let byte = f.push_inst(Inst::Cast {
            op: CastOp::Trunc,
            src_ty: Ty::U64,
            dst_ty: Ty::U8,
            operand: f.p(1),
        });
        f.push_inst_void(Inst::Store {
            ty: Ty::U8,
            ptr: f.p(0),
            value: byte,
            volatile: false,
            align: Some(1),
        });
        let zero = f.konst(Ty::U64, 0);
        f.ret(zero);
    });
    let copy_sig = b.sig(&[Ty::Ptr, Ty::Ptr], Some(Ty::U64));
    let copy = b.define("memory_copy", copy_sig, Linkage::External, |f| {
        let byte =
            f.push_inst(Inst::Load { ty: Ty::U8, ptr: f.p(1), volatile: false, align: Some(1) });
        f.push_inst_void(Inst::Store {
            ty: Ty::U8,
            ptr: f.p(0),
            value: byte,
            volatile: false,
            align: Some(1),
        });
        let zero = f.konst(Ty::U64, 0);
        f.ret(zero);
    });
    for (name, sig, target) in [("tail_store", store_sig, store), ("tail_copy", copy_sig, copy)] {
        b.define(name, sig, Linkage::External, |f| {
            let value = f.call(target, &[f.p(0), f.p(1)]);
            f.ret(value);
        });
    }
    let mut module = b.finish();
    module.target_info = Some(TargetInfo {
        triple: DARWIN.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    });
    for f in &mut module.functions {
        f.calling_conv = CallingConv::Rust;
    }
    let object = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O2,
            parallel: false,
            emit_proofs: false,
            never_inline: ["memory_store", "memory_copy"].into_iter().map(str::to_owned).collect(),
            ..Default::default()
        },
        TargetSpec::parse(DARWIN).unwrap(),
    )
    .with_codegen_license(fixture_license())
    .compile(&module)
    .unwrap()
    .object_code;
    Fixture::with_object(module, object, DARWIN)
}
fn tail_report() -> &'static (Fixture, CerReport) {
    static F: std::sync::OnceLock<(Fixture, CerReport)> = std::sync::OnceLock::new();
    F.get_or_init(|| {
        let f = tail_fixture();
        let report = f.report();
        (f, report)
    })
}
#[test]
#[cfg(feature = "kernel-recheck")]
fn complete_leaf_and_tail_population_retains_each_actual_prestate_and_fresh_replays() {
    // A separate process restores actual subject+proof bytes. It never compiles
    // an object or invokes the original conjunction producer.
    if let Some(path) = std::env::var_os("TRUST_TAIL_UNWIND_REPLAY_SUBJECT") {
        let path = std::path::PathBuf::from(path);
        let module =
            serde_json::from_slice(&std::fs::read(path.join("module.json")).unwrap()).unwrap();
        let f = Fixture::with_object(module, std::fs::read(path.join("object.o")).unwrap(), DARWIN);
        let replay = crate::original_conjunction_certificate::without_production(|| {
            replay_original_certificates(
                &input(&f),
                &std::fs::read(path.join("certificates.json")).unwrap(),
            )
        })
        .unwrap();
        assert_eq!(replay.rows.len(), 4);
        assert!(replay.all_replayed(), "{replay:?}");
        assert!(replay.unverified_sections.is_empty(), "{replay:?}");
        std::fs::write(path.join("fresh-replay.json"), serde_json::to_vec_pretty(&replay).unwrap())
            .unwrap();
        return;
    }
    let (f, report) = tail_report();
    assert_eq!(report.certificates.len(), 4);
    assert_eq!(report.closure.closed_kernel.len(), 4, "{}", explain(report));
    assert!(report.ships(crate::verify_output::EmitPolicy::StrictProvenOnly).is_ok());
    assert!(report.unverified_sections.is_empty(), "{:?}", report.compact_unwind);
    assert_eq!(report.compact_unwind.records.len(), 4);
    for cert in &report.certificates {
        let packet = cert.compact_unwind.as_ref().unwrap();
        assert_eq!(packet.prefix_pcs.len() * 4, packet.record.length as usize);
        assert_eq!(packet.original_proofs.len(), packet.prefix_pcs.len());
        assert!(packet.original_proofs.iter().all(|p| p.original_equations().len() == 22));
        if cert.symbol.starts_with("tail_") {
            assert_eq!(packet.prefix_pcs.last().copied(), cert.call_sites[0].offset);
        }
    }
    save("complete-leaf-tail", f, report);
    let path = std::env::var_os("TRUST_COMPACT_UNWIND_OUTPUT_DIR")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| {
            std::env::temp_dir().join(format!("trust-tail-unwind-{}", std::process::id()))
        })
        .join("fresh-replay");
    std::fs::create_dir_all(&path).unwrap();
    std::fs::write(path.join("module.json"), serde_json::to_vec_pretty(f.m_cg.as_ref()).unwrap())
        .unwrap();
    std::fs::write(path.join("object.o"), &f.object).unwrap();
    std::fs::write(path.join("certificates.json"), report.to_json()).unwrap();
    let output=std::process::Command::new(std::env::current_exe().unwrap()).args(["--exact","call_event::compact_unwind::tests::tail_tests::complete_leaf_and_tail_population_retains_each_actual_prestate_and_fresh_replays","--nocapture","--test-threads=1"])
        .env("TRUST_TAIL_UNWIND_REPLAY_SUBJECT",&path).output().unwrap();
    std::fs::write(path.join("child.log"), [output.stdout, output.stderr].concat()).unwrap();
    assert!(output.status.success(), "fresh replay child failed");
}
#[test]
#[cfg(feature = "kernel-recheck")]
fn tail_metadata_wire_subject_population_and_retention_cannot_license_functions() {
    let (f, report) = tail_report();
    let clean: serde_json::Value = serde_json::from_str(&report.to_json()).unwrap();
    let index = clean["certificates"]
        .as_array()
        .unwrap()
        .iter()
        .position(|v| v["symbol"] == "tail_store")
        .unwrap();
    for mode in 0..7 {
        let mut wire = clean.clone();
        let packet = &mut wire["certificates"][index]["compact_unwind"];
        match mode {
            0 => packet["model"] = "forged".into(),
            1 => packet["prefix_pcs"][0] = 0xffff_u64.into(),
            2 => packet["original_proofs"] = serde_json::json!([]),
            3 => packet["record"]["length"] = 8.into(),
            4 => packet["record"]["symbol"] = "memory_store".into(),
            5 => *packet = serde_json::Value::Null,
            6 => {
                packet["original_proofs"][0] = clean["certificates"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .find(|v| v["symbol"] == "memory_store")
                    .unwrap()["original_proof"]
                    .clone()
            }
            _ => unreachable!(),
        }
        let replay = crate::original_conjunction_certificate::without_production(|| {
            replay_original_certificates(&input(f), &serde_json::to_vec(&wire).unwrap())
        })
        .unwrap();
        assert!(
            replay.all_replayed(),
            "function proofs independent of metadata: {mode}: {replay:?}"
        );
        assert!(replay.unverified_sections.iter().any(|s| s == SECTION), "{mode}");
    }
    let (h, bytes, relocs) = section(&f.object);
    for mode in 0..3 {
        let bad = f.patched(|o| match mode {
            0 => o[bytes + 8..bytes + 12].copy_from_slice(&4_u32.to_le_bytes()),
            1 => {
                let x = word(o, relocs + 4).unwrap();
                o[relocs + 12..relocs + 16].copy_from_slice(&x.to_le_bytes());
            }
            2 => {
                let n = word(o, h + 60).unwrap();
                o[h + 60..h + 64].copy_from_slice(&(n - 1).to_le_bytes());
            }
            _ => unreachable!(),
        });
        assert!(
            crate::original_conjunction_certificate::without_production(|| {
                replay_original_certificates(&input(&bad), report.to_json().as_bytes())
            })
            .is_err()
        );
        assert!(bad.report().unverified_sections.iter().any(|s| s == SECTION));
    }
    let mut limited = report.clone();
    let before = limited
        .certificates
        .iter()
        .map(|c| (c.grade.clone(), c.original_proof.clone()))
        .collect::<Vec<_>>();
    preserve_function_retention_at(&mut limited, 1024);
    assert!(limited.unverified_sections.iter().any(|s| s == SECTION));
    assert!(limited.certificates.iter().all(|c| c.compact_unwind.is_none()));
    assert_eq!(
        before,
        limited
            .certificates
            .iter()
            .map(|c| (c.grade.clone(), c.original_proof.clone()))
            .collect::<Vec<_>>()
    );
}

fn prefix_fixture() -> Fixture {
    let mut b = ModBuilder::new("actual_tail_prefixes");
    let gs = b.sig(&[Ty::Ptr, Ty::U64, Ty::U64, Ty::U64], Some(Ty::U64));
    let leaf = b.define("prefix_leaf", gs, Linkage::External, |f| {
        let v = f.push_inst(Inst::Cast {
            op: CastOp::Trunc,
            src_ty: Ty::U64,
            dst_ty: Ty::U8,
            operand: f.p(1),
        });
        f.push_inst_void(Inst::Store {
            ty: Ty::U8,
            ptr: f.p(0),
            value: v,
            volatile: false,
            align: Some(1),
        });
        let z = f.konst(Ty::U64, 0);
        f.ret(z);
    });
    let cs = b.sig(&[Ty::Ptr], Some(Ty::U64));
    b.define("prefix_tail", cs, Linkage::External, |f| {
        let a = f.konst(Ty::U64, 1);
        let c = f.konst(Ty::U64, 2);
        let d = f.konst(Ty::U64, 3);
        let v = f.call(leaf, &[f.p(0), a, c, d]);
        f.ret(v);
    });
    let mut module = b.finish();
    module.target_info = Some(TargetInfo {
        triple: DARWIN.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    });
    for f in &mut module.functions {
        f.calling_conv = CallingConv::Rust;
    }
    let object = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O2,
            parallel: false,
            emit_proofs: false,
            never_inline: ["prefix_leaf".to_owned()].into_iter().collect(),
            ..Default::default()
        },
        TargetSpec::parse(DARWIN).unwrap(),
    )
    .with_codegen_license(fixture_license())
    .compile(&module)
    .unwrap()
    .object_code;
    Fixture::with_object(module, object, DARWIN)
}
#[test]
#[cfg(feature = "kernel-recheck")]
fn actual_tail_prestate_clobber_is_not_hidden_by_a_restored_transfer_state() {
    let f = prefix_fixture();
    let report = f.report();
    save("actual-multiple-tail-prefixes", &f, &report);
    let cert = report.certificate("prefix_tail").unwrap();
    let packet = cert.compact_unwind.as_ref().unwrap();
    assert!(packet.prefix_pcs.len() >= 4);
    let bound = ObjectLayout::bind(
        CompiledObject::parse(&f.object).unwrap(),
        &ObjectExpectations::from_module(&f.m_cg, ObjectFormat::MachO, f.model).unwrap(),
    )
    .unwrap();
    let start = bound.windows["prefix_tail"].start;
    assert_eq!(bound.windows["prefix_tail"].sites[0].offset, start + 12);
    for (mode, sequence) in [
        [0xaa1303e9, 0xd2800033, 0xaa0903f3], // save X19; X19=1; restore X19
        [0xaa1e03e9, 0xd280003e, 0xaa0903fe], // save LR; LR=1; restore LR
        [0xaa1d03e9, 0xd280003d, 0xaa0903fd], // save FP; FP=1; restore FP
        [0x910003e9, 0xd10043ff, 0x9100013f], // SP-derived prefix unsupported
        [0xd503233f, 0xd503201f, 0xd503201f], // PACIASP unsupported
    ]
    .into_iter()
    .enumerate()
    {
        let bad = f.patched(|o| {
            for (i, w) in sequence.into_iter().enumerate() {
                patch_word(o, start + i as u64 * 4, w)
            }
        });
        if mode < 3 {
            let actual = ObjectLayout::bind(
                CompiledObject::parse(&bad.object).unwrap(),
                &ObjectExpectations::from_module(&bad.m_cg, ObjectFormat::MachO, bad.model)
                    .unwrap(),
            )
            .unwrap();
            let trace = leaf_call_instance::tail_unwind::ActualTailUnwindPrefixes::derive(
                &input(&bad),
                &actual,
                "prefix_tail",
            )
            .unwrap();
            let (_, entry, prefixes) = trace.prefixes().unwrap();
            assert_eq!(prefixes.len(), 4);
            assert_eq!(
                prefixes[2].1.gpr[[19, 30, 29][mode]],
                Formula::BitVec { value: 1, width: 64 }
            );
            // Last state has restored raw register identity under actual ORs;
            // the separate intermediate original recovery goal still declines.
            let reg = [19, 30, 29][mode];
            assert!(
                crate::verify_output::try_kernel_recheckable_original_conjunction(&[(
                    prefixes[3].1.gpr[reg].clone(),
                    entry.gpr[reg].clone()
                )])
                .is_some()
            );
            let inventory = Inventory::read(&input(&bad), &actual).unwrap();
            let fresh = leaf_call_instance::fresh_certificate(
                &input(&bad),
                &actual,
                &actual.windows["prefix_tail"],
            )
            .unwrap();
            assert!(
                inventory
                    .check_tail(&input(&bad), &fresh, &trace, None)
                    .err()
                    .unwrap()
                    .contains("original22-lane")
            );
        }
        match bad.verify() {
            Ok(report) => {
                assert!(report.unverified_sections.iter().any(|s| s == SECTION));
                assert!(report.certificate("prefix_tail").unwrap().compact_unwind.is_none());
                save(&format!("tail-intermediate-clobber-{mode}"), &bad, &report);
            }
            Err(error) => {
                // PAC is outside the shared decoder/model; structural refusal
                // may precede a CER report and cannot grant metadata authority.
                assert_eq!(mode, 4);
                assert!(!error.reason.is_empty());
                if let Some(path) = std::env::var_os("TRUST_COMPACT_UNWIND_OUTPUT_DIR") {
                    let path = std::path::PathBuf::from(path).join("tail-pac-reader-refusal");
                    std::fs::create_dir_all(&path).unwrap();
                    std::fs::write(path.join("object.o"), &bad.object).unwrap();
                    std::fs::write(path.join("reason.txt"), error.to_string()).unwrap();
                }
            }
        }
    }
}
#[test]
#[cfg(not(feature = "kernel-recheck"))]
fn missing_kernel_cannot_check_actual_leaf_and_tail_metadata_population() {
    let f = tail_fixture();
    let report = refuses("tail-kernel-absent", &f);
    assert_eq!(report.certificates.len(), 4);
    assert!(report.certificates.iter().all(|r| r.compact_unwind.is_none()));
    assert!(report.compact_unwind.records.iter().all(|r| !r.checked));
}
