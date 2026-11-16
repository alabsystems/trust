use super::*;
#[path = "../../../tests/cer_common/mod.rs"]
mod cer_common;
use cer_common::*;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir::inst::CastOp;
use trust_ir::{CallingConv, Endianness, Linkage, StructPassingPolicy, TargetInfo, Ty};

fn fixture() -> Fixture {
    let mut builder = ModBuilder::new("unwind_four_actual_leaves");
    let store = builder.sig(&[Ty::Ptr, Ty::U64], Some(Ty::U64));
    builder.define("leaf_store", store, Linkage::External, |f| {
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
    let load = builder.sig(&[Ty::Ptr], Some(Ty::U64));
    builder.define("leaf_load", load, Linkage::External, |f| {
        let byte =
            f.push_inst(Inst::Load { ty: Ty::U8, ptr: f.p(0), volatile: false, align: Some(1) });
        let value = f.push_inst(Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::U8,
            dst_ty: Ty::U64,
            operand: byte,
        });
        f.ret(value);
    });
    let copy = builder.sig(&[Ty::Ptr, Ty::Ptr], Some(Ty::U64));
    builder.define("leaf_copy", copy, Linkage::External, |f| {
        let value =
            f.push_inst(Inst::Load { ty: Ty::U8, ptr: f.p(1), volatile: false, align: Some(1) });
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
    builder.define("leaf_gep", store, Linkage::External, |f| {
        let offset = f.konst(Ty::U64, 1);
        let ptr = f.push_inst(Inst::GEP {
            pointee_ty: Ty::U8,
            base: f.p(0),
            indices: vec![offset],
            inbounds: false,
        });
        let value = f.push_inst(Inst::Cast {
            op: CastOp::Trunc,
            src_ty: Ty::U64,
            dst_ty: Ty::U8,
            operand: f.p(1),
        });
        f.push_inst_void(Inst::Store { ty: Ty::U8, ptr, value, volatile: false, align: Some(1) });
        let zero = f.konst(Ty::U64, 0);
        f.ret(zero);
    });
    compile(builder.finish(), OptLevel::O3)
}
fn compile(mut module: Module, opt: OptLevel) -> Fixture {
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
            opt_level: opt,
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
fn save(name: &str, f: &Fixture, report: &CerReport) {
    if let Some(path) = std::env::var_os("TRUST_COMPACT_UNWIND_OUTPUT_DIR") {
        let path = std::path::PathBuf::from(path).join(name);
        std::fs::create_dir_all(&path).unwrap();
        std::fs::write(path.join("object.o"), &f.object).unwrap();
        std::fs::write(path.join("module.json"), serde_json::to_vec_pretty(&f.m_cg).unwrap())
            .unwrap();
        std::fs::write(path.join("certificates.json"), report.to_json()).unwrap();
    }
}
fn section(o: &[u8]) -> (usize, usize, usize) {
    let mut command = 32;
    for _ in 0..word(o, 16).unwrap() {
        if word(o, command).unwrap() == 0x19 {
            for i in 0..word(o, command + 64).unwrap() as usize {
                let s = command + 72 + i * 80;
                if o[s..s + 16] == *b"__compact_unwind" {
                    return (
                        s,
                        word(o, s + 48).unwrap() as usize,
                        word(o, s + 56).unwrap() as usize,
                    );
                }
            }
        }
        command += word(o, command + 4).unwrap() as usize;
    }
    panic!("actual __compact_unwind absent")
}
fn refuses(name: &str, f: &Fixture) -> CerReport {
    let report = f.report();
    assert!(report.unverified_sections.iter().any(|s| s == SECTION), "{:?}", report.compact_unwind);
    save(name, f, &report);
    report
}
#[test]
#[cfg(feature = "kernel-recheck")]
fn four_full_compiler_leaf_records_have_actual_prefix_kernel_proofs() {
    let f = fixture();
    let report = f.report();
    save("four-actual-leaves", &f, &report);
    assert_eq!(report.certificates.len(), 4);
    assert_eq!(report.closure.closed_kernel.len(), 4, "{}", explain(&report));
    assert!(report.ships(crate::verify_output::EmitPolicy::StrictProvenOnly).is_ok());
    assert!(report.unverified_sections.is_empty(), "{:?}", report.compact_unwind);
    assert_eq!(report.compact_unwind.records.len(), 4);
    assert!(report.compact_unwind.records.iter().all(|row| row.checked));
    for cert in &report.certificates {
        let unwind = cert.compact_unwind.as_ref().unwrap();
        assert_eq!(unwind.record.length as usize, unwind.prefix_pcs.len() * 4);
        assert_eq!(unwind.original_proofs.len(), unwind.prefix_pcs.len());
        for proof in &unwind.original_proofs {
            assert_eq!(proof.original_equations().len(), 22);
            assert!(proof.encoded_bytes().unwrap() > 0);
            assert!(
                proof.original_equations().iter().any(|(a, _)| matches!(a, Formula::BvAdd(..)))
            );
        }
    }
    let replay = crate::original_conjunction_certificate::without_production(|| {
        replay_original_certificates(&input(&f), report.to_json().as_bytes())
    })
    .unwrap();
    assert!(replay.all_replayed());
    assert!(replay.unverified_sections.is_empty());
}
#[test]
fn encoding_extent_personality_lsda_and_header_mutations_stay_unverified() {
    let f = fixture();
    let (header, bytes, _) = section(&f.object);
    for mode in 0..8 {
        let bad = f.patched(|o| match mode {
            0 => o[bytes + 12..bytes + 16].copy_from_slice(&0x0400_0000u32.to_le_bytes()),
            1 => o[bytes + 12..bytes + 16].copy_from_slice(&0x0200_1000u32.to_le_bytes()),
            2 => o[bytes + 12..bytes + 16].copy_from_slice(&0x0200_0001u32.to_le_bytes()),
            3 => o[bytes + 8..bytes + 12].copy_from_slice(&4u32.to_le_bytes()),
            4 => o[bytes + 8..bytes + 12].copy_from_slice(&u32::MAX.to_le_bytes()),
            5 => o[bytes + 16] = 1,
            6 => o[bytes + 24] = 1,
            7 => o[header + 64..header + 68].copy_from_slice(&0u32.to_le_bytes()),
            _ => unreachable!(),
        });
        refuses(&format!("record-mutant-{mode}"), &bad);
    }
    // A file-header cpusubtype other than CPU_SUBTYPE_ARM64_ALL (here arm64e)
    // is one Apple ld ignores with a warning, so the object reader refuses the
    // whole object at parse, before the unwind section is read.
    let bad = f.patched(|o| o[8..12].copy_from_slice(&2u32.to_le_bytes()));
    let refusal = bad.verify().expect_err("a cpusubtype-2 object is refused at parse");
    assert!(refusal.to_string().contains("cpusubtype"), "{refusal}");
}
#[test]
fn relocation_target_addend_missing_and_duplicate_population_refuse() {
    let f = fixture();
    let (header, bytes, relocs) = section(&f.object);
    for mode in 0..8 {
        let bad = f.patched(|o| match mode {
            0 => o[bytes] = 4,
            1 => {
                let x = word(o, relocs + 4).unwrap() | (1 << 24);
                o[relocs + 4..relocs + 8].copy_from_slice(&x.to_le_bytes());
            }
            2 => {
                let x = word(o, relocs + 4).unwrap() & !(3 << 25);
                o[relocs + 4..relocs + 8].copy_from_slice(&x.to_le_bytes());
            }
            3 => {
                let n = word(o, header + 60).unwrap();
                o[header + 60..header + 64].copy_from_slice(&(n - 1).to_le_bytes());
            }
            4 => {
                let x = word(o, relocs + 4).unwrap();
                o[relocs + 12..relocs + 16].copy_from_slice(&x.to_le_bytes());
            }
            5 => {
                let x = word(o, relocs).unwrap();
                o[relocs + 8..relocs + 12].copy_from_slice(&x.to_le_bytes());
            }
            6 => {
                let x = word(o, relocs + 4).unwrap() & !(1 << 27);
                o[relocs + 4..relocs + 8].copy_from_slice(&x.to_le_bytes());
            }
            7 => {
                let x = word(o, relocs + 4).unwrap() | (3 << 28);
                o[relocs + 4..relocs + 8].copy_from_slice(&x.to_le_bytes());
            }
            _ => unreachable!(),
        });
        match bad.verify() {
            Ok(report) => {
                assert!(report.unverified_sections.iter().any(|s| s == SECTION));
                save(&format!("reloc-mutant-{mode}"), &bad, &report);
            }
            Err(error) => assert!(!error.reason.is_empty()), // O1 may independently reject malformed symbols/relocations.
        }
    }
}
#[test]
#[cfg(feature = "kernel-recheck")]
fn temporary_saved_register_lr_fp_sp_clobbers_cannot_use_exit_equality() {
    let f = fixture();
    let start = symbol_offset(&f.object, "leaf_gep");
    assert!(function_words(&f.object, "leaf_gep").len() >= 4);
    let sequences = [
        [0xaa1303e9, 0xaa0003f3, 0xaa0903f3], // X9=X19; X19=X0; X19=X9
        [0xaa1e03e9, 0xaa0003fe, 0xaa0903fe], // LR restored before RET
        [0xaa1d03e9, 0xaa0003fd, 0xaa0903fd], // FP restored before RET
        [0x910003e9, 0xd10043ff, 0x9100013f], // X9=SP; SP-=16; SP=X9
        [0x9e660109, 0x9e670008, 0x9e670128], // D8 -> X9; D8=X0; D8=X9
    ];
    for (mode, words) in sequences.into_iter().enumerate() {
        let bad = f.patched(|o| {
            for (i, word) in words.into_iter().enumerate() {
                patch_word(o, start + i as u64 * 4, word);
            }
        });
        let report = refuses(&format!("temporary-prefix-clobber-{mode}"), &bad);
        assert!(report.certificate("leaf_gep").unwrap().compact_unwind.is_none());
    }
}
#[test]
#[cfg(feature = "kernel-recheck")]
fn retained_wire_is_not_metadata_authority_and_requires_actual_subject() {
    let f = fixture();
    let report = f.report();
    let mut wire: serde_json::Value = serde_json::from_str(&report.to_json()).unwrap();
    wire["certificates"][0]["compact_unwind"]["model"] =
        serde_json::Value::String("fabricated".into());
    let replay = crate::original_conjunction_certificate::without_production(|| {
        replay_original_certificates(&input(&f), &serde_json::to_vec(&wire).unwrap())
    })
    .unwrap();
    assert!(replay.all_replayed(), "the independent function proof remains intact");
    assert!(replay.unverified_sections.iter().any(|s| s == SECTION));
    let mut changed = f.patched(|o| {
        let (_, b, _) = section(o);
        o[b + 12] ^= 1;
    });
    assert!(replay_original_certificates(&input(&changed), report.to_json().as_bytes()).is_err());
    changed.model = RelocationModel::Pic;
    assert!(replay_original_certificates(&input(&changed), report.to_json().as_bytes()).is_err());
}
#[test]
fn nonzero_frame_call_and_incomplete_control_keep_metadata_unverified() {
    let mut b = ModBuilder::new("actual_call_frame");
    let sig = b.sig(&[Ty::U64], Some(Ty::U64));
    let callee = b.define("callee", sig, Linkage::External, |f| {
        f.ret(f.p(0));
    });
    b.define("caller", sig, Linkage::External, |f| {
        let r = f.call(callee, &[f.p(0)]);
        f.ret(r);
    });
    let f = compile(b.finish(), OptLevel::O0);
    let report = refuses("actual-o0-call-frame", &f);
    assert_eq!(report.certificates.len(), 2);
    let base = fixture();
    let start = symbol_offset(&base.object, "leaf_gep");
    let bad = base.patched(|o| patch_word(o, start, 0xd4200000));
    match bad.verify() {
        Ok(report) => assert!(report.unverified_sections.iter().any(|s| s == SECTION)),
        Err(_) => {}
    }
}
#[test]
#[cfg(not(feature = "kernel-recheck"))]
fn without_actual_kernel_no_metadata_record_is_verified() {
    let f = fixture();
    let report = refuses("kernel-absent", &f);
    assert!(report.certificates.iter().all(|c| c.compact_unwind.is_none()));
    assert!(report.compact_unwind.records.iter().all(|r| !r.checked));
}

#[test]
#[cfg(feature = "kernel-recheck")]
fn optional_metadata_retention_cannot_change_actual_function_grades() {
    let f = fixture();
    let mut report = f.report();
    assert!(report.unverified_sections.is_empty());
    assert_eq!(report.certificates.len(), 4);
    assert_eq!(report.closure.closed_kernel.len(), 4);
    assert!(report.ships(crate::verify_output::EmitPolicy::StrictProvenOnly).is_ok());
    save("final-four-actual-leaves", &f, &report);
    let replay = crate::original_conjunction_certificate::without_production(|| {
        replay_original_certificates(&input(&f), report.to_json().as_bytes())
    })
    .unwrap();
    assert!(replay.all_replayed());
    assert!(replay.unverified_sections.is_empty());
    let before: Vec<_> = report
        .certificates
        .iter()
        .map(|c| (c.symbol.clone(), c.grade.clone(), c.original_proof.clone()))
        .collect();
    preserve_function_retention_at(&mut report, 1024);
    assert!(report.unverified_sections.iter().any(|s| s == SECTION));
    assert!(report.certificates.iter().all(|c| c.compact_unwind.is_none()));
    // No new null fields or diagnostic envelope may push a legacy report at
    // its exact byte boundary into an unrelated function-grade downgrade.
    let wire: serde_json::Value = serde_json::from_str(&report.to_json()).unwrap();
    assert!(wire.get("compact_unwind").is_none());
    assert!(
        wire["certificates"]
            .as_array()
            .unwrap()
            .iter()
            .all(|row| row.get("compact_unwind").is_none())
    );
    assert_eq!(
        before,
        report
            .certificates
            .iter()
            .map(|c| (c.symbol.clone(), c.grade.clone(), c.original_proof.clone()))
            .collect::<Vec<_>>()
    );
    crate::original_conjunction_certificate::enforce_report_limits(&mut report, 4);
    assert_eq!(report.certificates.len(), 4);
    assert_eq!(report.closure.closed_kernel.len(), 4);
    assert!(report.ships(crate::verify_output::EmitPolicy::StrictProvenOnly).is_ok());
    save("optional-metadata-retention-budget", &f, &report);
}

#[path = "tail_tests.rs"]
mod tail_tests;

#[test]
fn a_record_that_ends_before_actual_code_names_the_unvisited_instructions() {
    let f = fixture();
    let (_, bytes, _) = section(&f.object);
    // The first record's function has more than one instruction; a 4-byte length
    // leaves actual code past the record, which the inventory itself refuses.
    let bad = f.patched(|o| o[bytes + 8..bytes + 12].copy_from_slice(&4u32.to_le_bytes()));
    let report = refuses("record-short-length", &bad);
    assert_eq!(
        report.compact_unwind.detail, "compact unwind length omits actual non-padding instructions",
        "{:?}",
        report.compact_unwind
    );
}
#[test]
fn metadata_reads_are_bounded_errors() {
    let bytes: Vec<u8> = (0u8..16).collect();
    assert_eq!(word(&bytes, 0), Ok(0x0302_0100));
    assert_eq!(word(&bytes, 12), Ok(0x0f0e_0d0c));
    assert_eq!(quad(&bytes, 8), Ok(0x0f0e_0d0c_0b0a_0908));
    assert_eq!(word(&bytes, 13), Err("metadata word out of bounds".into()));
    assert_eq!(quad(&bytes, 9), Err("metadata pointer out of bounds".into()));
    assert_eq!(word(&bytes, usize::MAX), Err("metadata offset overflow".into()));
    assert_eq!(quad(&bytes, usize::MAX - 7), Err("metadata offset overflow".into()));
}
