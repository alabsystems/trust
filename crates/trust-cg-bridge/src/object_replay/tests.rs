//! Every test here that emits its fixture under `EmitPolicy::StrictProvenOnly`
//! needs that emission to reach [PROVED], and only the Clean kernel re-check
//! awards [PROVED]: under `ay-proofs` alone the gate answers `Unknown`
//! ("[VALIDATED] (ay-only authority)"). Those tests are therefore
//! `#[cfg(feature = "kernel-recheck")]`, and the lane that runs them is
//! `--features kernel-recheck` (docs/VALIDATION_LADDER.md, Rung 1). Tests with no
//! such fixture run under `ay-proofs` too.

use trust_ir::inst::Inst;
use trust_ir::node::InstrNode;
use trust_ir::ty::FuncTy;
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{Block, CallingConv, Constant, Function, Module, Ty};

use super::*;
#[cfg(feature = "kernel-recheck")]
use crate::codegen_backend::{BridgeFramePointerPolicy, BridgeOptimizationLevel};
#[cfg(feature = "kernel-recheck")]
use crate::verify_output::{EmitPolicy, extract_text_from_object};
#[cfg(feature = "kernel-recheck")]
use crate::verify_output_trust_ir::{
    emit_trust_ir_module_object_with_replay, verify_trust_ir_output_preserved,
};

fn source(name: &str, value: i128) -> TrustIrGateSource {
    let mut module = Module::new("retained-object-fixture");
    module.func_types.push(FuncTy {
        params: vec![Ty::U8],
        returns: vec![Ty::U8],
        is_vararg: false,
        abi: None,
    });
    let mut function = Function::new(FuncId::new(0), name, FuncTyId::new(0), BlockId::new(0));
    function.calling_conv = CallingConv::Rust;
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::U8));
    block.body.push(
        InstrNode::new(Inst::Const { ty: Ty::U8, value: Constant::Int(value) })
            .with_result(ValueId::new(1)),
    );
    block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(1)] }));
    function.blocks.push(block);
    module.functions.push(function);
    TrustIrGateSource {
        symbol: name.into(),
        module: module.into(),
        func_id: FuncId::new(0),
        abi_cross_check: None,
    }
}

#[cfg(feature = "kernel-recheck")]
fn backend() -> TrustCgCodegenBackend {
    TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::AArch64, "aarch64-apple-darwin")
        .with_optimization_level(BridgeOptimizationLevel::O0)
}

#[cfg(feature = "kernel-recheck")]
fn fixture_with_backend(
    backend: TrustCgCodegenBackend,
) -> (TrustIrGateSource, TrustCgCodegenBackend, ObjectReplayArtifact) {
    let source = source("retained_constant", 7);
    let (object, report, artifact) = emit_trust_ir_module_object_with_replay(
        std::slice::from_ref(&source),
        &[],
        &[],
        EmitPolicy::StrictProvenOnly,
        &backend,
    )
    .expect("existing strict object gate must succeed for this actual constant");
    assert_eq!(report.proved, 1);
    assert_eq!(report.uncertified(), 0);
    let artifact = artifact.expect("complete diagnostic capture");
    assert_eq!(artifact.object_bytes, object.bytes);
    (source, backend, artifact)
}

#[cfg(feature = "kernel-recheck")]
fn fixture() -> (TrustIrGateSource, TrustCgCodegenBackend, ObjectReplayArtifact) {
    fixture_with_backend(backend())
}

// An actual independently source-bound proof payload for the retained object's
// reconstructed formula. This test producer is explicitly not an assertion
// that the production fast path retained a term when it returned only a label.
#[cfg(feature = "kernel-recheck")]
fn bitblast_fixture_with_backend(
    backend: TrustCgCodegenBackend,
) -> (TrustIrGateSource, TrustCgCodegenBackend, ObjectReplayArtifact) {
    let (source, backend, mut artifact) = fixture_with_backend(backend);
    let obligation = artifact.functions[0].obligation.as_ref().unwrap();
    let budget = ay_proof::BvExprProofBudget::conservative(
        Duration::from_secs(10),
        MAX_RECHECKABLE_REFUTATION_STEPS,
    )
    .unwrap();
    let proof = ay_proof::export_bv_blast_proof_expr_bounded(
        &formula_to_bvexpr(&obligation.machine_value).unwrap(),
        &formula_to_bvexpr(&obligation.spec_value).unwrap(),
        &budget,
    )
    .unwrap();
    artifact.functions[0].evidence = RetainedEvidence::BitBlast { proof: Box::new(proof) };
    (source, backend, artifact)
}

#[cfg(feature = "kernel-recheck")]
fn bitblast_fixture() -> (TrustIrGateSource, TrustCgCodegenBackend, ObjectReplayArtifact) {
    bitblast_fixture_with_backend(backend())
}

#[cfg(feature = "kernel-recheck")]
fn all_replayed(report: ObjectReplayReport) -> bool {
    !report.rows.is_empty() && report.rows.iter().all(|(_, result)| result.is_ok())
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn real_gate_retains_label_only_as_explicit_non_replayable() {
    let (source, backend, artifact) = fixture();
    let decoded = ObjectReplayArtifact::from_bytes(&artifact.to_bytes().unwrap()).unwrap();
    assert_eq!(artifact, decoded);
    let report = decoded.replay(&[source], &artifact.object_bytes, &backend, &[], &[]).unwrap();
    assert_eq!(report.rows.len(), 1);
    match &artifact.functions[0].evidence {
        RetainedEvidence::NonReplayable { original_kind, .. } => {
            assert_eq!(original_kind, "kernel-instantiated-label-only");
            assert!(report.rows[0].1.as_ref().unwrap_err().contains("non-replayable"));
        }
        RetainedEvidence::BitBlast { .. } => assert!(all_replayed(report)),
        other => panic!("unexpected actual constant evidence: {other:?}"),
    }
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn actual_object_source_bound_retained_refutation_roundtrips_and_kernel_replays() {
    let (source, backend, artifact) = bitblast_fixture();
    let bytes = artifact.to_bytes().unwrap();
    let decoded = ObjectReplayArtifact::from_bytes(&bytes).unwrap();
    assert!(all_replayed(
        decoded.replay(&[source], &artifact.object_bytes, &backend, &[], &[]).unwrap()
    ));
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn replay_rejects_object_relabelled_for_another_cpu() {
    let (source, backend, mut artifact) = bitblast_fixture();
    assert!(all_replayed(
        artifact
            .replay(std::slice::from_ref(&source), &artifact.object_bytes, &backend, &[], &[])
            .unwrap()
    ));
    artifact.object_bytes[4..8].copy_from_slice(&0x0100_0007u32.to_le_bytes());
    artifact.object_sha256 = hash(&artifact.object_bytes);
    assert!(artifact.replay(&[source], &artifact.object_bytes, &backend, &[], &[]).is_err());
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn replay_rejects_rebound_target_with_unchanged_object_and_proof() {
    let (source, _, mut artifact) = bitblast_fixture();
    let linux = TrustCgCodegenBackend::new_for_triple(
        TrustCgTargetArch::AArch64,
        "aarch64-unknown-linux-gnu",
    );
    artifact.backend = linux.object_replay_descriptor().unwrap();
    assert!(artifact.replay(&[source], &artifact.object_bytes, &linux, &[], &[]).is_err());
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn replay_rejects_foreign_format_row_with_unchanged_machine_text() {
    let (source, backend, mut artifact) = bitblast_fixture_with_backend(
        backend().with_frame_pointer_policy(BridgeFramePointerPolicy::Always),
    );
    assert!(all_replayed(
        artifact
            .replay(std::slice::from_ref(&source), &artifact.object_bytes, &backend, &[], &[])
            .unwrap()
    ));
    let original_obligation = artifact.functions[0].obligation.clone();
    let linux = TrustCgCodegenBackend::new_for_triple(
        TrustCgTargetArch::AArch64,
        "aarch64-unknown-linux-gnu",
    )
    .with_frame_pointer_policy(BridgeFramePointerPolicy::Always);
    let (verdict, foreign) = verify_trust_ir_output_preserved(&source, &linux);
    assert!(verdict.is_proven(), "Linux control: {verdict:?}");
    let foreign = foreign.expect("Linux object");
    assert_eq!(
        extract_text_from_object(&artifact.functions[0].object_bytes).unwrap().0,
        extract_text_from_object(&foreign).unwrap().0,
        "only the container target may change"
    );
    artifact.functions[0].object_bytes = foreign;
    artifact.functions[0].object_sha256 = hash(&artifact.functions[0].object_bytes);
    artifact.functions[0].symbols = raw_symbols(&artifact.functions[0].object_bytes).unwrap();
    artifact.functions[0].obligation = trust_ir_gate_obligation(
        &source,
        &artifact.functions[0].object_bytes,
        backend.target_arch(),
    );
    assert_eq!(artifact.functions[0].obligation, original_obligation);
    let result = artifact.replay(&[source], &artifact.object_bytes, &backend, &[], &[]);
    assert!(
        matches!(result, Err(ref reason) if reason.contains("target mismatch")),
        "foreign row must refuse at the target boundary: {result:?}"
    );
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn replay_rejects_aarch64_elf_abi_header_mutations_in_proved_row() {
    let linux = TrustCgCodegenBackend::new_for_triple(
        TrustCgTargetArch::AArch64,
        "aarch64-unknown-linux-gnu",
    );
    let (source, backend, artifact) = bitblast_fixture_with_backend(linux);
    assert!(all_replayed(
        artifact
            .replay(std::slice::from_ref(&source), &artifact.object_bytes, &backend, &[], &[])
            .unwrap()
    ));
    for (offset, field) in [
        (8, "EI_ABIVERSION"),
        (48, "e_flags[0]"),
        (49, "e_flags[1]"),
        (50, "e_flags[2]"),
        (51, "e_flags[3]"),
    ] {
        let mut mutated = artifact.clone();
        let original = &artifact.functions[0].object_bytes;
        assert_eq!(original[offset], 0, "emitter default for {field}");
        mutated.functions[0].object_bytes[offset] = 1;
        mutated.functions[0].object_sha256 = hash(&mutated.functions[0].object_bytes);
        assert_eq!(
            extract_text_from_object(original).unwrap().0,
            extract_text_from_object(&mutated.functions[0].object_bytes).unwrap().0,
            "{field} mutation must leave machine text unchanged"
        );
        let result = mutated.replay(
            std::slice::from_ref(&source),
            &artifact.object_bytes,
            &backend,
            &[],
            &[],
        );
        assert!(
            matches!(result, Err(ref reason) if reason.contains("target mismatch")),
            "{field} must refuse at the replay target boundary: {result:?}"
        );
    }
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn replay_rejects_malformed_elf_function_symbol_binding() {
    let linux = TrustCgCodegenBackend::new_for_triple(
        TrustCgTargetArch::AArch64,
        "aarch64-unknown-linux-gnu",
    );
    let (source, backend, artifact) = bitblast_fixture_with_backend(linux);
    assert!(all_replayed(
        artifact
            .replay(std::slice::from_ref(&source), &artifact.object_bytes, &backend, &[], &[])
            .unwrap()
    ));
    let mut mutated = artifact.clone();
    let object = &mut mutated.functions[0].object_bytes;
    let records = trust_cg_codegen::elf::reparse::read_object_records(object).unwrap();
    let symbol_index =
        records.symbols.iter().position(|symbol| symbol.name == source.symbol).unwrap();
    assert_eq!(records.symbols[symbol_index].binding, 1, "emitted function is global");
    let section_table = u64::from_le_bytes(object[40..48].try_into().unwrap()) as usize;
    let section_count = u16::from_le_bytes(object[60..62].try_into().unwrap()) as usize;
    let symtab_section = (0..section_count)
        .map(|index| section_table + index * 64)
        .find(|&at| {
            u32::from_le_bytes(object[at + 4..at + 8].try_into().unwrap())
                == trust_cg_codegen::elf::constants::SHT_SYMTAB
        })
        .expect("emitted symbol table");
    let first_global =
        u32::from_le_bytes(object[symtab_section + 44..symtab_section + 48].try_into().unwrap())
            as usize;
    assert!(symbol_index >= first_global, "function starts in global partition");
    let symtab_offset =
        u64::from_le_bytes(object[symtab_section + 24..symtab_section + 32].try_into().unwrap())
            as usize;
    object[symtab_offset + symbol_index * 24 + 4] &= 0x0f;
    assert_eq!(
        extract_text_from_object(&artifact.functions[0].object_bytes).unwrap().0,
        extract_text_from_object(object).unwrap().0,
        "binding mutation leaves machine text unchanged"
    );
    mutated.functions[0].object_sha256 = hash(object);
    let result =
        mutated.replay(std::slice::from_ref(&source), &artifact.object_bytes, &backend, &[], &[]);
    assert!(
        matches!(result, Err(ref reason) if reason.contains("symbol binding")),
        "replay must refuse malformed row binding: {result:?}"
    );
}

#[cfg(feature = "kernel-recheck")]
fn rebind_elf_function_for_test(object: &mut [u8], name: &str, binding: u8, local: bool) {
    let records = trust_cg_codegen::elf::reparse::read_object_records(object).unwrap();
    let symbol_index = records.symbols.iter().position(|symbol| symbol.name == name).unwrap();
    assert_eq!(records.symbols[symbol_index].binding, 1);
    let section_table = u64::from_le_bytes(object[40..48].try_into().unwrap()) as usize;
    let section_count = u16::from_le_bytes(object[60..62].try_into().unwrap()) as usize;
    let symtab_section = (0..section_count)
        .map(|index| section_table + index * 64)
        .find(|&at| {
            u32::from_le_bytes(object[at + 4..at + 8].try_into().unwrap())
                == trust_cg_codegen::elf::constants::SHT_SYMTAB
        })
        .expect("emitted symbol table");
    let first_global =
        u32::from_le_bytes(object[symtab_section + 44..symtab_section + 48].try_into().unwrap())
            as usize;
    assert_eq!(symbol_index, first_global, "function is first nonlocal symbol");
    let symtab_offset =
        u64::from_le_bytes(object[symtab_section + 24..symtab_section + 32].try_into().unwrap())
            as usize;
    let info_at = symtab_offset + symbol_index * 24 + 4;
    object[info_at] = (binding << 4) | (object[info_at] & 0x0f);
    if local {
        object[symtab_section + 44..symtab_section + 48]
            .copy_from_slice(&u32::try_from(first_global + 1).unwrap().to_le_bytes());
    }
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn replay_rejects_valid_elf_rebinding_of_row_and_merged_object() {
    let linux = TrustCgCodegenBackend::new_for_triple(
        TrustCgTargetArch::AArch64,
        "aarch64-unknown-linux-gnu",
    );
    let (source, backend, artifact) = bitblast_fixture_with_backend(linux);
    assert!(all_replayed(
        artifact
            .replay(std::slice::from_ref(&source), &artifact.object_bytes, &backend, &[], &[])
            .unwrap()
    ));
    for (name, binding, local) in [("weak", 2u8, false), ("local", 0u8, true)] {
        for merged in [false, true] {
            let mut mutated = artifact.clone();
            let original =
                if merged { &artifact.object_bytes } else { &artifact.functions[0].object_bytes };
            let bytes = if merged {
                &mut mutated.object_bytes
            } else {
                &mut mutated.functions[0].object_bytes
            };
            rebind_elf_function_for_test(bytes, &source.symbol, binding, local);
            assert!(backend.require_object_target(bytes).is_ok(), "{name} is structurally valid");
            assert_eq!(
                extract_text_from_object(original).unwrap().0,
                extract_text_from_object(bytes).unwrap().0,
                "{name} rebinding must not change machine text"
            );
            if merged {
                mutated.object_sha256 = hash(&mutated.object_bytes);
            } else {
                mutated.functions[0].object_sha256 = hash(&mutated.functions[0].object_bytes);
            }
            let result = mutated.replay(
                std::slice::from_ref(&source),
                &mutated.object_bytes,
                &backend,
                &[],
                &[],
            );
            assert!(
                matches!(result, Err(ref reason) if reason.contains("binding")),
                "{name} {} object must refuse: {result:?}",
                if merged { "merged" } else { "row" }
            );
        }
    }
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn changed_source_body_cannot_borrow_old_object_proof_even_with_new_hashes() {
    let (mut source, backend, mut artifact) = bitblast_fixture();
    std::sync::Arc::make_mut(&mut source.module).functions[0].blocks[0].body[0].inst =
        Inst::Const { ty: Ty::U8, value: Constant::Int(8) };
    artifact.functions[0].module_bytes = encode(&source.module, MAX_PART_BYTES).unwrap();
    artifact.functions[0].module_sha256 = hash(&artifact.functions[0].module_bytes);
    artifact.functions[0].obligation = trust_ir_gate_obligation(
        &source,
        &artifact.functions[0].object_bytes,
        backend.target_arch(),
    );
    assert!(!all_replayed(
        artifact.replay(&[source], &artifact.object_bytes, &backend, &[], &[]).unwrap()
    ));
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn changed_actual_machine_immediate_cannot_rebind_old_proof() {
    let (source, backend, mut artifact) = bitblast_fixture();
    for bytes in [&mut artifact.object_bytes, &mut artifact.functions[0].object_bytes] {
        let (code, _) = extract_text_from_object(bytes).unwrap();
        let at = bytes.windows(code.len()).position(|window| window == code).unwrap();
        assert_eq!(code.len() % 4, 0);
        let words: Vec<_> =
            code.chunks_exact(4).map(|word| u32::from_le_bytes(word.try_into().unwrap())).collect();
        eprintln!("actual original instruction words: {words:08x?}");
        // Read the actual instruction population, not an assumed first
        // instruction/register assignment. The fixture has one MOVZ of 7.
        let constants: Vec<_> = words
            .iter()
            .enumerate()
            .filter(|(_, word)| **word & 0x7f80_0000 == 0x5280_0000 && (**word >> 5) & 0xffff == 7)
            .collect();
        assert_eq!(constants.len(), 1, "unique actual constant-producing MOVZ");
        let (index, word) = constants[0];
        let changed = (*word & !(0xffff << 5)) | (8 << 5);
        bytes[at + 4 * index..at + 4 * index + 4].copy_from_slice(&changed.to_le_bytes());
    }
    artifact.object_sha256 = hash(&artifact.object_bytes);
    artifact.functions[0].object_sha256 = hash(&artifact.functions[0].object_bytes);
    artifact.functions[0].obligation = trust_ir_gate_obligation(
        &source,
        &artifact.functions[0].object_bytes,
        backend.target_arch(),
    );
    let changed = artifact.functions[0].obligation.as_ref().unwrap();
    assert_ne!(
        changed.machine_value, changed.spec_value,
        "the actual decoded machine value must change, not merely object metadata"
    );
    assert!(!all_replayed(
        artifact.replay(&[source], &artifact.object_bytes, &backend, &[], &[]).unwrap()
    ));
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn dropped_duplicate_and_mixed_symbol_rows_refuse() {
    let (source, backend, artifact) = fixture();
    let mut missing = artifact.clone();
    missing.functions.clear();
    assert!(
        missing
            .replay(std::slice::from_ref(&source), &artifact.object_bytes, &backend, &[], &[])
            .is_err()
    );
    let mut duplicate = artifact.clone();
    duplicate.functions.push(duplicate.functions[0].clone());
    duplicate.preserved.push(duplicate.preserved[0].clone());
    assert!(
        duplicate
            .replay(&[source.clone(), source.clone()], &artifact.object_bytes, &backend, &[], &[])
            .is_err()
    );
    let mut wrong = artifact.clone();
    wrong.functions[0].symbol = "another_symbol".into();
    assert!(wrong.replay(&[source], &artifact.object_bytes, &backend, &[], &[]).is_err());
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn changed_func_id_abi_backend_or_extent_refuses() {
    let (mut source, backend, artifact) = fixture();
    let mut wrong = artifact.clone();
    wrong.functions[0].func_id = 99;
    assert!(
        wrong
            .replay(std::slice::from_ref(&source), &artifact.object_bytes, &backend, &[], &[])
            .is_err()
    );
    wrong = artifact.clone();
    wrong.preserved[0].text_offset += 4;
    assert!(
        wrong
            .replay(std::slice::from_ref(&source), &artifact.object_bytes, &backend, &[], &[])
            .is_err()
    );
    let changed =
        TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::AArch64, "aarch64-apple-darwin")
            .with_optimization_level(BridgeOptimizationLevel::O1);
    assert!(
        artifact
            .replay(std::slice::from_ref(&source), &artifact.object_bytes, &changed, &[], &[])
            .is_err()
    );
    std::sync::Arc::make_mut(&mut source.module).functions[0].calling_conv = CallingConv::C;
    assert!(artifact.replay(&[source], &artifact.object_bytes, &backend, &[], &[]).is_err());
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn conditional_and_ambient_claims_never_borrow_unconditional_evidence() {
    let (_, _, artifact) = bitblast_fixture();
    let row = &artifact.functions[0];
    for slot in 0..5 {
        let mut obligation = row.obligation.as_ref().unwrap().clone();
        match slot {
            0 => obligation.spec_reach = Formula::Bool(false),
            1 => obligation.machine_reach = Formula::Bool(false),
            2 => obligation.ambient_pre.push(Formula::Bool(true)),
            // O0: a solver-only ABI conjunct is not covered by the retained
            // value certificate either.
            3 => obligation.abi_residue.push(crate::verify_output::AbiConjunct {
                slot: "X19".into(),
                claim: Formula::Bool(true),
            }),
            _ => obligation.spec_side_conditions.push(Formula::Bool(true)),
        }
        assert!(
            replay_evidence(&obligation, &row.evidence)
                .unwrap_err()
                .contains("conditional/effect/modeling")
        );
    }
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn corrupt_graph_and_refutation_refuse_without_replacing_the_retained_proof() {
    let (source, backend, mut artifact) = bitblast_fixture();
    let original = artifact.clone();
    let RetainedEvidence::BitBlast { proof } = &mut artifact.functions[0].evidence else {
        panic!()
    };
    proof.clauses.pop();
    assert!(!all_replayed(
        artifact
            .replay(std::slice::from_ref(&source), &artifact.object_bytes, &backend, &[], &[])
            .unwrap()
    ));
    artifact = original;
    let RetainedEvidence::BitBlast { proof } = &mut artifact.functions[0].evidence else {
        panic!()
    };
    proof.refutation.steps.clear();
    assert!(!all_replayed(
        artifact.replay(&[source], &artifact.object_bytes, &backend, &[], &[]).unwrap()
    ));
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn wire_bounds_unknown_fields_and_schema_refuse() {
    assert!(ObjectReplayArtifact::from_bytes(&vec![b' '; MAX_WIRE_BYTES + 1]).is_err());
    let (_, _, artifact) = fixture();
    let mut value: serde_json::Value =
        serde_json::from_slice(&artifact.to_bytes().unwrap()).unwrap();
    value["invented_authority"] = true.into();
    assert!(ObjectReplayArtifact::from_bytes(&serde_json::to_vec(&value).unwrap()).is_err());
    value.as_object_mut().unwrap().remove("invented_authority");
    value["schema"] = (SCHEMA + 1).into();
    assert!(ObjectReplayArtifact::from_bytes(&serde_json::to_vec(&value).unwrap()).is_err());
    let nested = (0..100)
        .fold(serde_json::Value::Bool(true), |value, _| serde_json::Value::Array(vec![value]));
    assert!(encode(&nested, MAX_PART_BYTES).is_err());
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn static_and_linkage_context_cannot_be_dropped_or_relabelled() {
    let (source, backend, artifact) = fixture();
    assert!(
        artifact
            .replay(
                std::slice::from_ref(&source),
                &artifact.object_bytes,
                &backend,
                &[FunctionLinkage::Internal],
                &[]
            )
            .is_err()
    );
    let statics = vec![trust_cg_codegen::pipeline::ObjectGlobal {
        name: "external-data".into(),
        data: vec![1],
        mutable: false,
        is_external: true,
        symbol_refs: vec![],
        is_thread_local: false,
        is_import: false,
        is_weak: false,
        align: 1,
        visibility: trust_ir::Visibility::Default,
        retained: false,
        section: None,
        comdat: false,
    }];
    assert!(artifact.replay(&[source], &artifact.object_bytes, &backend, &[], &statics).is_err());

    // Linker-visible changes must invalidate the retained context even when
    // the global's name, bytes, alignment, and linkage are identical.
    let original = statics_identity(&statics).unwrap();
    for visibility in [trust_ir::Visibility::Hidden, trust_ir::Visibility::Protected] {
        let mut changed = statics.clone();
        changed[0].visibility = visibility;
        assert_ne!(statics_identity(&changed).unwrap(), original);
    }
    let mut changed = statics;
    changed[0].retained = true;
    assert_ne!(statics_identity(&changed).unwrap(), original);
}

#[cfg(feature = "kernel-recheck")]
fn two_function_fixture() -> (Vec<TrustIrGateSource>, TrustCgCodegenBackend, ObjectReplayArtifact) {
    let sources = vec![source("retained_first", 7), source("retained_second", 7)];
    let backend = backend();
    let (_, report, artifact) = emit_trust_ir_module_object_with_replay(
        &sources,
        &[],
        &[],
        EmitPolicy::StrictProvenOnly,
        &backend,
    )
    .unwrap();
    assert_eq!(report.proved, 2);
    (sources, backend, artifact.unwrap())
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn replay_refuses_unmatched_actual_defined_text_symbol() {
    let (mut sources, backend, mut artifact) = two_function_fixture();
    sources.pop();
    artifact.functions.pop();
    artifact.preserved.pop();
    assert!(
        artifact.replay(&sources, &artifact.object_bytes, &backend, &[], &[]).is_err(),
        "the actual second defined text symbol must not disappear with its metadata row"
    );
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn replay_refuses_duplicate_actual_defined_text_symbol() {
    let (mut sources, backend, mut artifact) = two_function_fixture();
    let bytes = &mut artifact.object_bytes;
    let rd = |bytes: &[u8], at: usize| u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap());
    assert_eq!(rd(bytes, 0), 0xfeed_facf);
    let mut command = 32;
    let mut symtab = None;
    for _ in 0..rd(bytes, 16) {
        if rd(bytes, command) == 2 {
            assert!(symtab.is_none());
            symtab = Some((rd(bytes, command + 8) as usize, rd(bytes, command + 12) as usize));
        }
        command += rd(bytes, command + 4) as usize;
    }
    let (offset, count) = symtab.unwrap();
    let definitions: Vec<_> = (0..count)
        .map(|i| offset + 16 * i)
        .filter(|&at| bytes[at + 4] & 0x0e == 0x0e && bytes[at + 5] == 1)
        .collect();
    assert_eq!(definitions.len(), 2, "entire actual defined-text population");
    let first = bytes[definitions[0]..definitions[0] + 16].to_vec();
    bytes[definitions[1]..definitions[1] + 16].copy_from_slice(&first);
    artifact.object_sha256 = hash(bytes);
    sources.pop();
    artifact.functions.pop();
    artifact.preserved.pop();
    assert!(
        artifact.replay(&sources, &artifact.object_bytes, &backend, &[], &[]).is_err(),
        "duplicate raw symbol rows must not collapse into a first/last writer map"
    );
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn unknown_scope_is_not_artifact_authored_schema_semantics() {
    let (_, _, artifact) = fixture();
    let mut value: serde_json::Value =
        serde_json::from_slice(&artifact.to_bytes().unwrap()).unwrap();
    value["scope"] = "invented complete executable authority".into();
    assert!(ObjectReplayArtifact::from_bytes(&serde_json::to_vec(&value).unwrap()).is_err());
}

#[test]
fn capture_refusals_bind_context_without_inventing_source_completeness() {
    let a = capture_refusal_bytes("capacity", "first-cgu", b"actual object", 33).unwrap();
    let b = capture_refusal_bytes("capacity", "second-cgu", b"actual object", 33).unwrap();
    let c = capture_refusal_bytes("capacity", "first-cgu", b"changed object", 33).unwrap();
    assert_ne!(a, b);
    assert_ne!(a, c);
    let row: serde_json::Value = serde_json::from_slice(&a).unwrap();
    assert_eq!(row["codegen_unit"], "first-cgu");
    assert_eq!(row["object_sha256"], hash(b"actual object"));
    assert_eq!(row["source_count"], 33);
    assert_eq!(row["source_population_bound"], false);
    assert_eq!(row["status"], "non-replayable-capture-refused");
    assert!(ObjectReplayArtifact::from_bytes(&a).is_err());
}

#[cfg(feature = "kernel-recheck")]
fn repeated_shared_symbol_name(object: &[u8], count: usize, raw_name: &str) -> Vec<u8> {
    let mut bytes = object.to_vec();
    let rd = |bytes: &[u8], at: usize| u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap());
    assert_eq!(rd(&bytes, 0), 0xfeed_facf);
    let mut command = 32;
    let mut symtab = None;
    for _ in 0..rd(&bytes, 16) {
        if rd(&bytes, command) == 2 {
            assert!(symtab.is_none());
            symtab = Some(command);
        }
        command += rd(&bytes, command + 4) as usize;
    }
    let command = symtab.unwrap();
    let start = rd(&bytes, command + 8) as usize;
    let length = rd(&bytes, command + 12) as usize;
    let original = (0..length)
        .map(|i| start + i * 16)
        .find(|&at| bytes[at + 4] & 0x0e == 0x0e && bytes[at + 5] == 1)
        .unwrap();
    let mut row: [u8; 16] = bytes[original..original + 16].try_into().unwrap();
    row[..4].copy_from_slice(&0u32.to_le_bytes());
    bytes.resize((bytes.len() + 7) & !7, 0);
    let symbols = bytes.len();
    for _ in 0..count {
        bytes.extend_from_slice(&row);
    }
    let strings = bytes.len();
    bytes.extend_from_slice(raw_name.as_bytes());
    bytes.push(0);
    for (offset, value) in [(8, symbols), (12, count), (16, strings), (20, raw_name.len() + 1)] {
        bytes[command + offset..command + offset + 4]
            .copy_from_slice(&u32::try_from(value).unwrap().to_le_bytes());
    }
    bytes
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn raw_symbol_row_budget_refuses_repeated_shared_names() {
    let (_, _, artifact) = fixture();
    let within = repeated_shared_symbol_name(&artifact.object_bytes, 32, "_shared");
    assert_eq!(raw_symbols(&within).unwrap().len(), 32);
    let excess = repeated_shared_symbol_name(&artifact.object_bytes, 33, "_shared");
    assert!(
        raw_symbols(&excess).is_err(),
        "raw diagnostic must refuse before allocating a 33rd row"
    );
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn raw_symbol_name_budget_refuses_shared_string_amplification() {
    let (_, _, artifact) = fixture();
    let name = format!("_{}", "a".repeat(32767));
    let within = repeated_shared_symbol_name(&artifact.object_bytes, 1, &name);
    let rows = raw_symbols(&within).unwrap();
    assert_eq!(rows[0].raw_name.len() + rows[0].name.len(), 65535);
    let excess = repeated_shared_symbol_name(&artifact.object_bytes, 2, &name);
    assert!(
        raw_symbols(&excess).is_err(),
        "one shared input string cannot amplify beyond the diagnostic name-byte budget"
    );
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn raw_macho_truncated_section_refuses_without_panicking() {
    let (_, _, artifact) = fixture();
    let mut bytes = artifact.object_bytes;
    assert_eq!(u32::from_le_bytes(bytes[32..36].try_into().unwrap()), 0x19);
    bytes.truncate(112); // nsects exists, but the first 16-byte section name does not.
    assert!(extract_text_from_object(&bytes).is_err());
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn raw_macho_overflowing_text_extent_refuses_without_panicking() {
    let (_, _, artifact) = fixture();
    let mut bytes = artifact.object_bytes;
    assert_eq!(u32::from_le_bytes(bytes[32..36].try_into().unwrap()), 0x19);
    bytes[144..152].copy_from_slice(&u64::MAX.to_le_bytes());
    assert!(extract_text_from_object(&bytes).is_err());
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn raw_macho_zero_size_command_refuses_before_section_success() {
    let (_, _, artifact) = fixture();
    let mut bytes = artifact.object_bytes;
    assert_eq!(u32::from_le_bytes(bytes[32..36].try_into().unwrap()), 0x19);
    bytes[36..40].copy_from_slice(&0u32.to_le_bytes());
    assert!(extract_text_from_object(&bytes).is_err());
}

#[cfg(feature = "kernel-recheck")]
fn actual_elf_object() -> Vec<u8> {
    let source = source("retained_elf_constant", 7);
    let backend = TrustCgCodegenBackend::new_for_triple(
        TrustCgTargetArch::AArch64,
        "aarch64-unknown-linux-gnu",
    )
    .with_optimization_level(BridgeOptimizationLevel::O0);
    let (object, report, _) = emit_trust_ir_module_object_with_replay(
        &[source],
        &[],
        &[],
        EmitPolicy::StrictProvenOnly,
        &backend,
    )
    .unwrap();
    assert_eq!(report.proved, 1);
    assert_eq!(report.uncertified(), 0);
    assert_eq!(&object.bytes[..6], b"\x7fELF\x02\x01");
    assert!(!extract_text_from_object(&object.bytes).unwrap().0.is_empty());
    object.bytes
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn raw_elf_overflowing_section_table_refuses_without_panicking() {
    let mut bytes = actual_elf_object();
    bytes[40..48].copy_from_slice(&(u64::MAX - 7).to_le_bytes());
    bytes[60..62].copy_from_slice(&1u16.to_le_bytes());
    bytes[62..64].copy_from_slice(&0u16.to_le_bytes());
    assert!(extract_text_from_object(&bytes).is_err());
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn raw_elf_truncated_declared_section_table_refuses_before_text_success() {
    let mut bytes = actual_elf_object();
    let table = usize::try_from(u64::from_le_bytes(bytes[40..48].try_into().unwrap())).unwrap();
    let width = usize::from(u16::from_le_bytes(bytes[58..60].try_into().unwrap()));
    let count = u16::from_le_bytes(bytes[60..62].try_into().unwrap());
    let original_end = table + usize::from(count) * width;
    assert_eq!(original_end, bytes.len(), "actual emitter's complete section table is last");
    let extended_count = count.checked_add(1).unwrap();
    bytes[60..62].copy_from_slice(&extended_count.to_le_bytes());
    // All original sections, including the named text and names table, survive.
    // Only the final newly declared section header is one byte short.
    bytes.resize(original_end + width - 1, 0);
    assert!(extract_text_from_object(&bytes).is_err());
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn production_scalar_constant_retains_actual_replayable_certificate() {
    let (source, backend, artifact) = fixture();
    assert!(
        matches!(&artifact.functions[0].evidence, RetainedEvidence::BitBlast { .. }),
        "the actual production observer must retain a generated proof, not a theorem label"
    );
    let decoded = ObjectReplayArtifact::from_bytes(&artifact.to_bytes().unwrap()).unwrap();
    let report = decoded.replay(&[source], &artifact.object_bytes, &backend, &[], &[]).unwrap();
    assert_eq!(report.rows.len(), 1);
    assert!(all_replayed(report));
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn production_scalar_identity_retains_actual_replayable_certificate() {
    let mut source = source("retained_identity", 7);
    std::sync::Arc::make_mut(&mut source.module).functions[0].blocks[0].body =
        vec![InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] })];
    let backend = backend();
    let (object, report, artifact) = emit_trust_ir_module_object_with_replay(
        std::slice::from_ref(&source),
        &[],
        &[],
        EmitPolicy::StrictProvenOnly,
        &backend,
    )
    .unwrap();
    assert_eq!(report.proved, 1);
    assert_eq!(report.uncertified(), 0);
    let artifact = artifact.unwrap();
    assert_eq!(artifact.object_bytes, object.bytes);
    assert!(
        matches!(&artifact.functions[0].evidence, RetainedEvidence::BitBlast { .. }),
        "identity must carry its actual production proof, not a test-only replacement"
    );
    let decoded = ObjectReplayArtifact::from_bytes(&artifact.to_bytes().unwrap()).unwrap();
    let report = decoded.replay(&[source], &object.bytes, &backend, &[], &[]).unwrap();
    assert_eq!(report.rows.len(), 1);
    assert!(all_replayed(report));
}

#[cfg(feature = "kernel-recheck")]
fn scalar_binary_source(name: &str, op: trust_ir::inst::BinOp) -> TrustIrGateSource {
    let mut source = source(name, 7);
    std::sync::Arc::make_mut(&mut source.module).func_types[0].params = vec![Ty::U32, Ty::U32];
    std::sync::Arc::make_mut(&mut source.module).func_types[0].returns = vec![Ty::U32];
    let block = &mut std::sync::Arc::make_mut(&mut source.module).functions[0].blocks[0];
    block.params = vec![(ValueId::new(0), Ty::U32), (ValueId::new(1), Ty::U32)];
    block.body = vec![
        InstrNode::new(Inst::BinOp { op, ty: Ty::U32, lhs: ValueId::new(0), rhs: ValueId::new(1) })
            .with_result(ValueId::new(2)),
        InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
    ];
    source
}

#[cfg(feature = "kernel-recheck")]
fn assert_production_binary_certificate(source: TrustIrGateSource) {
    let backend = backend();
    let (object, report, artifact) = emit_trust_ir_module_object_with_replay(
        std::slice::from_ref(&source),
        &[],
        &[],
        EmitPolicy::StrictProvenOnly,
        &backend,
    )
    .unwrap();
    assert_eq!(report.proved, 1);
    assert_eq!(report.uncertified(), 0);
    let artifact = artifact.unwrap();
    assert_eq!(artifact.object_bytes, object.bytes);
    let RetainedEvidence::BitBlast { proof } = &artifact.functions[0].evidence else {
        panic!("the actual production fast path must retain a proof, not merely its label")
    };
    let proof_bytes = encode(proof, MAX_PART_BYTES).unwrap();
    eprintln!(
        "actual production BitBlast: steps={} bytes={} sha256={}",
        proof.refutation.steps.len(),
        proof_bytes.len(),
        hash(&proof_bytes)
    );
    let decoded = ObjectReplayArtifact::from_bytes(&artifact.to_bytes().unwrap()).unwrap();
    assert!(all_replayed(decoded.replay(&[source], &object.bytes, &backend, &[], &[]).unwrap()));
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn production_scalar_add_bitblast_respects_the_step_budget() {
    // A better exporter can fit Add under the unchanged production cap. Check
    // actual retained steps, then require a real refusal under a smaller bound.
    let source = scalar_binary_source("retained_add", trust_ir::inst::BinOp::Add);
    let backend = backend();
    let (object, report, artifact) = emit_trust_ir_module_object_with_replay(
        std::slice::from_ref(&source),
        &[],
        &[],
        EmitPolicy::StrictProvenOnly,
        &backend,
    )
    .unwrap();
    assert_eq!(report.proved, 1);
    assert_eq!(report.uncertified(), 0);
    assert_eq!(MAX_RECHECKABLE_REFUTATION_STEPS, 2048);
    let artifact = artifact.unwrap();
    assert_eq!(artifact.object_bytes, object.bytes);
    assert_eq!(artifact.functions.len(), 1);
    let RetainedEvidence::BitBlast { proof } = &artifact.functions[0].evidence else {
        panic!("the default bounded export must retain its actual replay-checked Add proof")
    };
    assert!(proof.refutation.steps.len() > 1);
    assert!(proof.refutation.steps.len() <= MAX_RECHECKABLE_REFUTATION_STEPS);
    eprintln!("actual Add retained resolution steps={}", proof.refutation.steps.len());
    let budget = ay_proof::BvExprProofBudget::conservative(Duration::from_secs(10), 1).unwrap();
    let detail = scalar_certificate::capture_scalar_certificate(
        &source,
        &artifact.functions[0].object_bytes,
        backend.target_arch(),
        &budget,
    )
    .unwrap_err();
    assert_eq!(
        detail,
        "scalar certificate: bounded export refused: proof resource `resolution derived steps` exceeds limit 1 (actual 2)"
    );
    eprintln!("actual low-budget refusal: {detail}");
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn production_scalar_and_retains_actual_replayable_certificate() {
    assert_production_binary_certificate(scalar_binary_source(
        "retained_and",
        trust_ir::inst::BinOp::And,
    ));
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn production_scalar_add_retains_actual_replayable_certificate() {
    assert_production_binary_certificate(scalar_binary_source(
        "retained_add",
        trust_ir::inst::BinOp::Add,
    ));
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn lower_budget_selection_retains_and_replays_a_real_compact_kernel_term() {
    let source = scalar_binary_source("retained_add", trust_ir::inst::BinOp::Add);
    let backend = backend();
    let (object, report, artifact) = emit_trust_ir_module_object_with_replay(
        std::slice::from_ref(&source),
        &[],
        &[],
        EmitPolicy::StrictProvenOnly,
        &backend,
    )
    .unwrap();
    assert_eq!(report.proved, 1);
    assert_eq!(report.uncertified(), 0);
    assert_eq!(MAX_RECHECKABLE_REFUTATION_STEPS, 2048);
    let mut artifact = artifact.unwrap();
    assert_eq!(artifact.object_bytes, object.bytes);
    assert_eq!(artifact.functions.len(), 1);
    // This drives the same selection used by observe, under an explicit test
    // budget. It does not claim the default public route still falls back.
    let budget = ay_proof::BvExprProofBudget::conservative(Duration::from_secs(10), 1).unwrap();
    let refusal = scalar_certificate::capture_scalar_certificate(
        &source,
        &artifact.functions[0].object_bytes,
        backend.target_arch(),
        &budget,
    )
    .unwrap_err();
    assert_eq!(
        refusal,
        "scalar certificate: bounded export refused: proof resource `resolution derived steps` exceeds limit 1 (actual 2)"
    );
    artifact.functions[0].evidence = capture_kernel_instantiation(
        &source,
        &artifact.functions[0].object_bytes,
        backend.target_arch(),
        &budget,
    );
    let bytes = artifact.to_bytes().unwrap();
    let wire: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(wire["schema"], 3);
    assert_eq!(wire["functions"][0]["evidence"]["kind"], "CompactInstantiation");
    let decoded = ObjectReplayArtifact::from_bytes(&bytes).unwrap();
    let replay = decoded.replay(&[source], &object.bytes, &backend, &[], &[]).unwrap();
    assert_eq!(replay.rows.len(), 1);
    assert!(all_replayed(replay));
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn legacy_schema_retains_old_proof_scope_without_new_variant_authority() {
    let (source, backend, mut artifact) = fixture();
    assert!(matches!(artifact.functions[0].evidence, RetainedEvidence::BitBlast { .. }));
    artifact.schema = 1;
    artifact.scope = LEGACY_SCOPE.into();
    artifact.functions[0].abi_context = RetainedAbiContext::LegacyAbsent;
    let decoded = ObjectReplayArtifact::from_bytes(&artifact.to_bytes().unwrap()).unwrap();
    assert!(all_replayed(
        decoded
            .replay(std::slice::from_ref(&source), &artifact.object_bytes, &backend, &[], &[])
            .unwrap()
    ));
    artifact.scope = SCOPE.into();
    assert!(ObjectReplayArtifact::from_bytes(&artifact.to_bytes().unwrap()).is_err());
    artifact.schema = SCHEMA + 1;
    assert!(ObjectReplayArtifact::from_bytes(&artifact.to_bytes().unwrap()).is_err());
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn actual_scalar_capture_preserves_live_abi_context_without_minting_it_from_wire() {
    let mut source = source("retained_cross_checked", 7);
    // This is an explicit caller-supplied diagnostic token, not a rustc FnAbi
    // measurement. The scalar fixture needs no aggregate ABI attestation.
    source.abi_cross_check =
        Some(crate::AbiPassModeCrossCheck::attested_by("test caller: no aggregate crossing"));
    let backend = backend();
    let (object, report, artifact) = emit_trust_ir_module_object_with_replay(
        std::slice::from_ref(&source),
        &[],
        &[],
        EmitPolicy::StrictProvenOnly,
        &backend,
    )
    .unwrap();
    assert_eq!(report.proved, 1);
    assert_eq!(report.uncertified(), 0);
    let artifact = artifact.unwrap();
    assert_eq!(
        artifact.functions[0].abi_context,
        RetainedAbiContext::CrossChecked { authority: "test caller: no aggregate crossing".into() }
    );
    let decoded = ObjectReplayArtifact::from_bytes(&artifact.to_bytes().unwrap()).unwrap();
    assert!(all_replayed(
        decoded.replay(std::slice::from_ref(&source), &object.bytes, &backend, &[], &[],).unwrap()
    ));
    for context in [None, Some(crate::AbiPassModeCrossCheck::attested_by("different caller"))] {
        let mut changed = source.clone();
        changed.abi_cross_check = context;
        assert_eq!(
            decoded.replay(&[changed], &object.bytes, &backend, &[], &[]).unwrap_err(),
            "object replay ABI cross-check context mismatch"
        );
    }
    let mut forged = decoded;
    forged.functions[0].abi_context =
        RetainedAbiContext::CrossChecked { authority: "different caller".into() };
    assert_eq!(
        forged.replay(&[source], &object.bytes, &backend, &[], &[]).unwrap_err(),
        "object replay ABI cross-check context mismatch"
    );
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn abi_context_schema_is_explicit_and_legacy_wire_cannot_borrow_live_attestation() {
    let (mut source, backend, artifact) = fixture();
    let mut wire: serde_json::Value =
        serde_json::from_slice(&artifact.to_bytes().unwrap()).unwrap();
    wire["functions"][0].as_object_mut().unwrap().remove("abi_context");
    assert!(
        ObjectReplayArtifact::from_bytes(&serde_json::to_vec(&wire).unwrap()).is_err(),
        "schema3 requires an explicit None or captured cross-check"
    );
    for (schema, scope) in [(1, LEGACY_SCOPE), (2, SCOPE)] {
        wire["schema"] = schema.into();
        wire["scope"] = scope.into();
        let decoded =
            ObjectReplayArtifact::from_bytes(&serde_json::to_vec(&wire).unwrap()).unwrap();
        assert_eq!(decoded.functions[0].abi_context, RetainedAbiContext::LegacyAbsent);
        assert!(all_replayed(
            decoded
                .replay(std::slice::from_ref(&source), &artifact.object_bytes, &backend, &[], &[],)
                .unwrap()
        ));
        source.abi_cross_check = Some(crate::AbiPassModeCrossCheck::attested_by("new live caller"));
        assert_eq!(
            decoded
                .replay(std::slice::from_ref(&source), &artifact.object_bytes, &backend, &[], &[],)
                .unwrap_err(),
            "object replay ABI cross-check context mismatch"
        );
        source.abi_cross_check = None;
        let mut relabelled = artifact.clone();
        relabelled.schema = schema;
        relabelled.scope = scope.into();
        assert!(
            ObjectReplayArtifact::from_bytes(&relabelled.to_bytes().unwrap()).is_err(),
            "an explicit modern context cannot masquerade as an old schema"
        );
    }
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn wire_abi_label_never_substitutes_for_converter_admission() {
    use trust_ir::ty::FieldDef;
    use trust_ir::value::StructId;
    use trust_ir::{Endianness, StructDef, StructPassingPolicy, TargetInfo};

    let (mut source, backend, mut artifact) = fixture();
    std::sync::Arc::make_mut(&mut source.module).target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::Unclassified,
    });
    std::sync::Arc::make_mut(&mut source.module).structs.push(StructDef {
        id: StructId::new(0),
        name: "Pair".into(),
        fields: vec![
            FieldDef { name: "first".into(), ty: Ty::Usize, offset: Some(0) },
            FieldDef { name: "second".into(), ty: Ty::Usize, offset: Some(8) },
        ],
        size: Some(16),
        align: Some(8),
        repr: Default::default(),
        origin: None,
    });
    let ty = Ty::Struct(StructId::new(0));
    std::sync::Arc::make_mut(&mut source.module).func_types[0].params[0] = ty.clone();
    std::sync::Arc::make_mut(&mut source.module).functions[0].blocks[0].params[0].1 = ty;
    assert!(matches!(
        crate::lower_module_to_lir_maybe_cross_checked(&source.module, source.func_id, None,),
        Err(crate::ModuleLirError::UnclassifiedAggregateAbi { .. })
    ));
    let test_claim = crate::AbiPassModeCrossCheck::attested_by("test shape only, not FnAbi proof");
    assert!(
        crate::lower_module_to_lir_maybe_cross_checked(
            &source.module,
            source.func_id,
            Some(&test_claim),
        )
        .is_ok(),
        "the aggregate fixture is otherwise lowerable"
    );

    // Rebind the changed source bytes so source hashing is not the refusal.
    // Keep live None: the artifact's text is never turned into test_claim.
    let row = &mut artifact.functions[0];
    row.module_bytes = encode(&source.module, MAX_PART_BYTES).unwrap();
    row.module_sha256 = hash(&row.module_bytes);
    row.abi_context = RetainedAbiContext::CrossChecked { authority: test_claim.authority().into() };
    assert_eq!(
        artifact
            .replay(std::slice::from_ref(&source), &artifact.object_bytes, &backend, &[], &[],)
            .unwrap_err(),
        "object replay ABI cross-check context mismatch"
    );
    artifact.functions[0].abi_context = RetainedAbiContext::NoCrossCheck;
    let refused = artifact
        .replay(std::slice::from_ref(&source), &artifact.object_bytes, &backend, &[], &[])
        .unwrap_err();
    assert!(refused.starts_with("object replay current lowering refused:"), "{refused}");
    assert!(refused.contains("unclassified"), "{refused}");

    // A replay that silently substitutes None also fails this close positive.
    // Reaching the independent per-row obligation stage is NOT an assertion of
    // aggregate semantic faithfulness or an actual rustc FnAbi measurement.
    source.abi_cross_check = Some(test_claim);
    artifact.functions[0].abi_context = abi_context(&source).unwrap();
    let report = artifact
        .replay(&[source], &artifact.object_bytes, &backend, &[], &[])
        .expect("the exact live aggregate cross-check must reach obligation replay");
    assert_eq!(report.rows.len(), 1);
}

#[test]
fn retained_abi_authority_text_is_bounded_before_copy() {
    let mut source = source("bounded_context", 7);
    source.abi_cross_check =
        Some(crate::AbiPassModeCrossCheck::attested_by("a".repeat(MAX_PART_BYTES + 1)));
    assert!(abi_context(&source).unwrap_err().contains("serialization capacity exceeded"));
}
