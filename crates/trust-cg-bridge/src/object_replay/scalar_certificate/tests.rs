//! Every test here that emits its fixture under `EmitPolicy::StrictProvenOnly`
//! needs that emission to reach [PROVED], and only the Clean kernel re-check
//! awards [PROVED]: under `ay-proofs` alone the gate answers `Unknown`
//! ("[VALIDATED] (ay-only authority)"). Those tests are therefore
//! `#[cfg(feature = "kernel-recheck")]`, and the lane that runs them is
//! `--features kernel-recheck` (docs/VALIDATION_LADDER.md, Rung 1). Tests with no
//! such fixture run under `ay-proofs` too.

use trust_cg_codegen::macho::{AArch64RelocKind, MachOWriter, Relocation};
use trust_ir::node::InstrNode;
use trust_ir::ty::FuncTy;
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{Block, Function, Module};

use super::*;
#[cfg(feature = "kernel-recheck")]
use crate::codegen_backend::BridgeOptimizationLevel;
#[cfg(feature = "kernel-recheck")]
use crate::verify_output::EmitPolicy;
#[cfg(feature = "kernel-recheck")]
use crate::verify_output_trust_ir::emit_trust_ir_module_object_with_replay;

fn source() -> TrustIrGateSource {
    let mut module = Module::new("scalar-certificate-close-controls");
    module.func_types.push(FuncTy {
        params: vec![Ty::U32, Ty::U32],
        returns: vec![Ty::U32],
        is_vararg: false,
        abi: None,
    });
    let mut function =
        Function::new(FuncId::new(0), "scalar_add", FuncTyId::new(0), BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params = vec![(ValueId::new(0), Ty::U32), (ValueId::new(1), Ty::U32)];
    block.body = vec![
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::U32,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        })
        .with_result(ValueId::new(2)),
        InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
    ];
    function.blocks.push(block);
    module.functions.push(function);
    TrustIrGateSource {
        symbol: "scalar_add".into(),
        module: module.into(),
        func_id: FuncId::new(0),
        abi_cross_check: None,
    }
}

#[cfg(feature = "kernel-recheck")]
fn actual() -> (TrustIrGateSource, Vec<u8>) {
    let source = source();
    let backend =
        TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::AArch64, "aarch64-apple-darwin")
            .with_optimization_level(BridgeOptimizationLevel::O0);
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
    assert_eq!(artifact.unwrap().object_bytes, object.bytes);
    (source, object.bytes)
}

#[cfg(feature = "kernel-recheck")]
fn budget() -> ay_proof::BvExprProofBudget {
    ay_proof::BvExprProofBudget::conservative(
        Duration::from_secs(10),
        MAX_RECHECKABLE_REFUTATION_STEPS,
    )
    .unwrap()
}

fn object_from_text(source: &TrustIrGateSource, text: &[u8], relocation: bool) -> Vec<u8> {
    let mut writer = MachOWriter::new();
    writer.add_text_section(text);
    writer.add_symbol(&format!("_{}", source.symbol), 1, 0, true).unwrap();
    if relocation {
        writer
            .add_relocation(
                0,
                Relocation {
                    offset: 0,
                    symbol_index: 1,
                    kind: AArch64RelocKind::Unsigned,
                    pc_relative: false,
                    length: 2,
                    is_extern: false,
                },
            )
            .unwrap();
    }
    writer.write().unwrap()
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn actual_machine_unused_events_do_not_borrow_scalar_equality() {
    let (source, object) = actual();
    let (text, _) = extract_text_from_object(&object).unwrap();
    qualify_machine(&source, &object, TrustCgTargetArch::AArch64).unwrap();
    for word in [0xd503_203fu32, 0xd503_209f] {
        // YIELD and SEV: old effects are empty.
        let decoded = decode_aarch64(&word.to_le_bytes(), 0).unwrap();
        assert!(matches!(decoded.opcode, Opcode::Yield | Opcode::Sev));
        assert!(Aarch64Semantics.effects(&MachineState::symbolic(), &decoded).unwrap().is_empty());
        let mut changed = word.to_le_bytes().to_vec();
        changed.extend_from_slice(&text);
        let changed = object_from_text(&source, &changed, false);
        assert!(
            qualify_machine(&source, &changed, TrustCgTargetArch::AArch64)
                .unwrap_err()
                .contains("opcode")
        );
    }
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn actual_machine_ret_register_and_trailing_words_refuse() {
    let (source, object) = actual();
    let (text, _) = extract_text_from_object(&object).unwrap();
    assert_eq!(&text[text.len() - 4..], &0xd65f_03c0u32.to_le_bytes());
    let mut altered = text.clone();
    let len = altered.len();
    altered[len - 4..].copy_from_slice(&0xd65f_0000u32.to_le_bytes());
    assert!(
        qualify_machine(
            &source,
            &object_from_text(&source, &altered, false),
            TrustCgTargetArch::AArch64
        )
        .unwrap_err()
        .contains("RET X30")
    );
    let mut trailing = text;
    trailing.extend_from_slice(&0xd503_201fu32.to_le_bytes());
    assert!(
        qualify_machine(
            &source,
            &object_from_text(&source, &trailing, false),
            TrustCgTargetArch::AArch64
        )
        .is_err()
    );
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn relocation_only_object_twin_refuses_with_identical_text() {
    let (source, object) = actual();
    let (text, _) = extract_text_from_object(&object).unwrap();
    let plain = object_from_text(&source, &text, false);
    let relocated = object_from_text(&source, &text, true);
    assert_ne!(plain, relocated);
    assert_eq!(
        extract_text_from_object(&plain).unwrap(),
        extract_text_from_object(&relocated).unwrap()
    );
    no_relocations(&plain).unwrap();
    assert!(no_relocations(&relocated).unwrap_err().contains("relocation"));
}

#[test]
fn source_unused_instruction_claim_and_ssa_twins_refuse() {
    let original = source();
    qualify_source(&original).unwrap();
    let mut unused = original.clone();
    std::sync::Arc::make_mut(&mut unused.module).functions[0].blocks[0].body.insert(
        0,
        InstrNode::new(Inst::BinOp {
            op: BinOp::Mul,
            ty: Ty::U32,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        })
        .with_result(ValueId::new(3)),
    );
    assert!(qualify_source(&unused).unwrap_err().contains("unsupported source instruction"));
    let mut assumed = original.clone();
    std::sync::Arc::make_mut(&mut assumed.module).functions[0].summary =
        Some(trust_ir::FunctionSummary::default());
    assert!(qualify_source(&assumed).unwrap_err().contains("context/claims"));
    let mut duplicate = original.clone();
    std::sync::Arc::make_mut(&mut duplicate.module).functions[0].blocks[0].body[0].results =
        vec![ValueId::new(0)];
    assert!(qualify_source(&duplicate).is_err());
    let mut wrong_type = original;
    std::sync::Arc::make_mut(&mut wrong_type.module).functions[0].blocks[0].params[0].1 = Ty::U16;
    assert!(qualify_source(&wrong_type).unwrap_err().contains("parameter type"));
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn reserved_register_flags_and_unused_store_refuse() {
    let (source, object) = actual();
    let (text, _) = extract_text_from_object(&object).unwrap();
    for word in [0xaa00_03f3u32, 0xab01_0000, 0xf900_0000] {
        // MOV X19,X0; ADDS X0,X0,X1; STR X0,[X0]
        let mut changed = word.to_le_bytes().to_vec();
        changed.extend_from_slice(&text);
        assert!(
            qualify_machine(
                &source,
                &object_from_text(&source, &changed, false),
                TrustCgTargetArch::AArch64
            )
            .is_err()
        );
    }
}

#[test]
fn source_and_machine_expansion_budgets_refuse_before_goal_construction() {
    let mut source = source();
    let body = &mut std::sync::Arc::make_mut(&mut source.module).functions[0].blocks[0].body;
    body.pop();
    for id in 3..32 {
        body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::U32,
                lhs: ValueId::new(id - 1),
                rhs: ValueId::new(id - 1),
            })
            .with_result(ValueId::new(id)),
        );
    }
    body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(31)] }));
    assert!(qualify_source(&source).unwrap_err().contains("budget"));
    let text: Vec<u8> = std::iter::repeat_n(0x8b00_0000u32, 32)
        .chain([0xd65f_03c0])
        .flat_map(u32::to_le_bytes)
        .collect();
    assert!(
        qualify_machine(
            &source,
            &object_from_text(&source, &text, false),
            TrustCgTargetArch::AArch64
        )
        .unwrap_err()
        .contains("budget")
    );
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn real_object_wrong_source_and_exhausted_export_budget_stay_refused() {
    let (source, object) = actual();
    let tiny = ay_proof::BvExprProofBudget::conservative(
        Duration::from_nanos(1),
        MAX_RECHECKABLE_REFUTATION_STEPS,
    )
    .unwrap();
    assert!(
        capture_scalar_certificate(&source, &object, TrustCgTargetArch::AArch64, &tiny)
            .unwrap_err()
            .contains("bounded export")
    );
    let mut changed = source;
    let Inst::BinOp { op, .. } =
        &mut std::sync::Arc::make_mut(&mut changed.module).functions[0].blocks[0].body[0].inst
    else {
        panic!()
    };
    *op = BinOp::Sub;
    assert!(
        capture_scalar_certificate(&changed, &object, TrustCgTargetArch::AArch64, &budget())
            .is_err()
    );
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn malformed_container_refuses_without_offset_panics() {
    let (source, object) = actual();
    for offset in [20usize, 36] {
        let mut changed = object.clone();
        changed[offset..offset + 4].copy_from_slice(&u32::MAX.to_le_bytes());
        assert!(qualify_machine(&source, &changed, TrustCgTargetArch::AArch64).is_err());
    }
    for end in [0, 4, 31, 39] {
        assert!(qualify_machine(&source, &object[..end], TrustCgTargetArch::AArch64).is_err());
    }
}

#[cfg(feature = "kernel-recheck")]
#[test]
fn actual_recovered_and_proof_rejects_changed_source_and_object() {
    let mut source = source();
    source.symbol = "scalar_and".into();
    std::sync::Arc::make_mut(&mut source.module).functions[0].name = source.symbol.clone();
    let Inst::BinOp { op, .. } =
        &mut std::sync::Arc::make_mut(&mut source.module).functions[0].blocks[0].body[0].inst
    else {
        panic!()
    };
    *op = BinOp::And;
    let backend =
        TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::AArch64, "aarch64-apple-darwin")
            .with_optimization_level(BridgeOptimizationLevel::O0);
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
    assert_eq!(artifact.functions.len(), 1);
    assert!(matches!(&artifact.functions[0].evidence, RetainedEvidence::BitBlast { .. }));
    // No test-produced proof is substituted: every twin retains this exact
    // production observer's actual AND refutation.
    let replay =
        artifact.replay(std::slice::from_ref(&source), &object.bytes, &backend, &[], &[]).unwrap();
    assert_eq!(replay.rows.len(), 1);
    assert!(replay.rows[0].1.is_ok());

    let mut changed_source = source.clone();
    let Inst::BinOp { op, .. } =
        &mut std::sync::Arc::make_mut(&mut changed_source.module).functions[0].blocks[0].body[0]
            .inst
    else {
        panic!()
    };
    *op = BinOp::Or;
    let mut source_twin = artifact.clone();
    let row = &mut source_twin.functions[0];
    row.module_bytes = encode(&changed_source.module, MAX_PART_BYTES).unwrap();
    row.module_sha256 = hash(&row.module_bytes);
    row.obligation =
        trust_ir_gate_obligation(&changed_source, &row.object_bytes, backend.target_arch());
    let changed = row.obligation.as_ref().unwrap();
    assert_ne!(changed.machine_value, changed.spec_value);
    let replay = source_twin.replay(&[changed_source], &object.bytes, &backend, &[], &[]).unwrap();
    assert_eq!(replay.rows.len(), 1);
    assert!(replay.rows[0].1.is_err(), "fresh hashes must not rebind the old AND proof to OR");

    let mut object_twin = artifact;
    for bytes in [&mut object_twin.object_bytes, &mut object_twin.functions[0].object_bytes] {
        let (text, _) = extract_text_from_object(bytes).unwrap();
        let offsets: Vec<_> = bytes
            .windows(text.len())
            .enumerate()
            .filter_map(|(i, window)| (window == text).then_some(i))
            .collect();
        assert_eq!(
            offsets.len(),
            1,
            "locate the unique actual text, not a guessed register or offset"
        );
        let ands: Vec<_> = text
            .chunks_exact(4)
            .enumerate()
            .filter_map(|(i, word)| {
                (decode_aarch64(word, (i * 4) as u64).unwrap().opcode == Opcode::And)
                    .then_some((i, u32::from_le_bytes(word.try_into().unwrap())))
            })
            .collect();
        assert_eq!(ands.len(), 1, "complete actual opcode population has one AND");
        let (index, word) = ands[0];
        let changed = (word ^ (1 << 30)).to_le_bytes();
        assert_eq!(decode_aarch64(&changed, (index * 4) as u64).unwrap().opcode, Opcode::Eor);
        let at = offsets[0] + index * 4;
        bytes[at..at + 4].copy_from_slice(&changed);
    }
    object_twin.object_sha256 = hash(&object_twin.object_bytes);
    let row = &mut object_twin.functions[0];
    row.object_sha256 = hash(&row.object_bytes);
    row.obligation = trust_ir_gate_obligation(&source, &row.object_bytes, backend.target_arch());
    let changed = row.obligation.as_ref().unwrap();
    assert_ne!(changed.machine_value, changed.spec_value);
    let replay =
        object_twin.replay(&[source], &object_twin.object_bytes, &backend, &[], &[]).unwrap();
    assert_eq!(replay.rows.len(), 1);
    assert!(
        replay.rows[0].1.is_err(),
        "fresh object hashes must not rebind the old AND proof to XOR"
    );
}

/// Pins the readers' exact reads and errors. Their former `try_into().unwrap()`
/// could not fail after a bounds-checked `get`, so this also passes on the code
/// before that rewrite: it guards the rewrite, not a reachable panic.
#[test]
fn byte_readers_read_exact_fields_and_refuse_truncation_and_offset_overflow() {
    let bytes = [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08];
    assert_eq!(u16_at(&bytes, 6), Ok(0x0807));
    assert_eq!(u32_at(&bytes, 4), Ok(0x0807_0605));
    assert_eq!(u64_at(&bytes, 0), Ok(0x0807_0605_0403_0201));
    assert_eq!(u16_at(&bytes, 7), Err("scalar certificate: truncated u16".into()));
    assert_eq!(u32_at(&bytes, 5), Err("scalar certificate: truncated u32".into()));
    assert_eq!(u64_at(&bytes, 1), Err("scalar certificate: truncated u64".into()));
    assert_eq!(u64_at(&bytes, usize::MAX - 7), Err("scalar certificate: offset overflow".into()));
}

#[test]
fn ret_x30_word_is_exactly_its_four_encoded_bytes() {
    let ret = 0xd65f_03c0_u32.to_le_bytes();
    assert!(is_ret_x30_word(&ret));
    // A slice of another length is not the word. The former
    // `u32::from_le_bytes(bytes.try_into().unwrap())` panicked on each of these.
    assert!(!is_ret_x30_word(&ret[..3]));
    assert!(!is_ret_x30_word(&[ret[0], ret[1], ret[2], ret[3], 0]));
    assert!(!is_ret_x30_word(&[]));
    // `RET X0` and the big-endian spelling of `RET X30` are other words.
    assert!(!is_ret_x30_word(&0xd65f_0000_u32.to_le_bytes()));
    assert!(!is_ret_x30_word(&0xd65f_03c0_u32.to_be_bytes()));
}
