use trust_ir::{Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode, ParamId, Ty, ValueId};

use crate::template_metadata::{self as codec, GenericSlot, OwnerBindings, SlotKind};

/// Also the template-instance TEST-ORACLE's envelope-byte control input (`oracle.rs`).
pub(super) fn fixture() -> (OwnerBindings, trust_ir::template::Template, Vec<u8>) {
    let t = crate::template_lowering::type_param_sentinel(0);
    let mut m = trust_ir::Module::new("owner_binding_control");
    let ft = m
        .intern_func_type(FuncTy {
            params: vec![t.clone()],
            returns: vec![t.clone()],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let mut b = Block::new(BlockId::new(0)).with_param(ValueId::new(0), t);
    b.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
    let mut f = Function::new(FuncId::new(0), "identity", ft, BlockId::new(0))
        .with_producer(trust_ir::Producer::TRust);
    f.blocks = vec![b];
    m.try_add_function(f).unwrap();
    let facts = crate::template_lowering::LaneFacts {
        owner: Some((11, 12)),
        parameter_indices: vec![1],
        params: vec![crate::template_lowering::LaneParam::Type],
        ..Default::default()
    };
    let template =
        crate::template_lowering::abstract_template(&m, &facts, "control::identity".into())
            .unwrap();
    let bindings = OwnerBindings {
        owner: (11, 12),
        slots: vec![
            GenericSlot { definition: (11, 13), kind: SlotKind::Lifetime },
            GenericSlot { definition: (11, 14), kind: SlotKind::Type(ParamId::new(0)) },
        ],
    };
    let evidence = crate::rmeta_entry::encode_evidence(&crate::rmeta_entry::Evidence {
        arg_count: 1,
        arg_enum: vec![false],
        ..Default::default()
    });
    (bindings, template, evidence)
}

#[test]
fn typed_const_hole_is_bound_to_original_owner_dependencies_without_admission() {
    use trust_ir::template::{HoleDef, HoleKind, TemplateArg};
    use trust_ir::{ConstantG, HoleId, InstG, InstrNodeG, TemplateRef, TyG};
    let (bindings, mut template, evidence) = fixture();
    let key = crate::template_key::encode(&crate::template_key::HoleKey::Const(
        crate::template_key::KeyConstItem::Assoc {
            item: (11, 99),
            args: vec![crate::template_key::KeyArg::Type(crate::template_key::KeyTy::Param(1))],
        },
    ))
    .unwrap();
    template.header.holes.push(HoleDef {
        kind: HoleKind::Const { ty: Ty::U64 },
        key,
        args: vec![TemplateArg::Type(TyG::Ext(TemplateRef::Param(ParamId::new(0))))],
    });
    template.module.functions[0].blocks[0].body.insert(
        0,
        InstrNodeG::new(InstG::Const {
            ty: TyG::U64,
            value: ConstantG::Ext(TemplateRef::Hole(HoleId::new(0))),
        })
        .with_result(ValueId::new(1)),
    );
    let bytes = codec::frame(&bindings, &template, false, &evidence).unwrap();
    assert_eq!(codec::read(&bytes, &bindings, false).unwrap().template(), &template);
    template.header.holes[0].args.clear();
    assert!(
        codec::frame(&bindings, &template, false, &evidence)
            .unwrap_err()
            .0
            .contains("dependencies")
    );
}
#[test]
fn a_template_instance_refuses_a_tensor_weight_blob_table_by_name() {
    let (_, template, _) = fixture();
    let mut module = template.module;
    assert_eq!(super::instantiate::untransported_template_tables(&module), None);
    module.blobs.push(trust_ir::blob::Blob::new(vec![0, 0, 0, 0]));
    assert_eq!(
        super::instantiate::untransported_template_tables(&module),
        Some("template instance requires unsupported tensor weight-blob transport"),
    );
}

#[test]
fn authenticated_roundtrip_retains_every_positional_slot_and_evidence() {
    let (b, t, e) = fixture();
    let bytes = codec::frame(&b, &t, true, &e).unwrap();
    let a = codec::read(&bytes, &b, true).unwrap();
    assert_eq!(a.bindings(), &b);
    assert_eq!(a.template(), &t);
    assert_eq!(crate::rmeta_entry::encode_evidence(a.evidence()), e);
    assert!(a.overflow_checks());
    assert_eq!(bytes, codec::frame(&b, &t, true, &e).unwrap());
}

#[test]
fn typed_type_hole_is_bound_to_original_owner_dependencies_without_admission() {
    use trust_ir::template::{HoleDef, HoleKind, TemplateArg, TypeContract};
    use trust_ir::{HoleId, InstG, InstrNodeG, TemplateRef, TyG};
    let (bindings, mut template, evidence) = fixture();
    let key = crate::template_key::encode(&crate::template_key::HoleKey::Type(
        crate::template_key::KeyTy::Param(1),
    )).unwrap();
    template.header.holes.push(HoleDef { kind: HoleKind::Type { contract: TypeContract::Opaque },
        key, args: vec![TemplateArg::Type(TyG::Ext(TemplateRef::Param(ParamId::new(0))))] });
    template.module.functions[0].blocks[0].body.insert(0,
        InstrNodeG::new(InstG::Alloca {
            ty: TyG::Ext(TemplateRef::Hole(HoleId::new(0))), count: None, align: None,
        }).with_result(ValueId::new(1)));
    let bytes = codec::frame(&bindings, &template, false, &evidence).unwrap();
    assert_eq!(codec::read(&bytes, &bindings, false).unwrap().template(), &template);
    template.header.holes[0].args.clear();
    assert!(codec::frame(&bindings, &template, false, &evidence).unwrap_err().0.contains("dependencies"));
}
#[test]
fn requested_owner_and_parameter_definitions_are_independent_of_recomputed_digest() {
    let (b, t, e) = fixture();
    let mut wrong = b.clone();
    wrong.owner = (11, 99);
    let bytes = codec::frame(&wrong, &t, true, &e).unwrap();
    assert!(codec::read(&bytes, &b, true).unwrap_err().0.contains("owner mismatch"));
    wrong = b.clone();
    wrong.slots[1].definition = (11, 999);
    let bytes = codec::frame(&wrong, &t, true, &e).unwrap();
    assert!(codec::read(&bytes, &b, true).unwrap_err().0.contains("positional binding"));
}
#[test]
fn omitted_erased_lifetime_and_changed_slot_kind_refuse() {
    let (b, t, e) = fixture();
    let mut wrong = b.clone();
    wrong.slots.remove(0);
    let bytes = codec::frame(&wrong, &t, true, &e).unwrap();
    assert!(codec::read(&bytes, &b, true).unwrap_err().0.contains("slot count"));
    wrong = b.clone();
    wrong.slots[1].kind = SlotKind::Const { param: ParamId::new(0), ty: Ty::U64 };
    assert!(codec::frame(&wrong, &t, true, &e).is_err());
}
#[test]
fn module_evidence_and_schema_tampering_refuse_before_payload_decode() {
    let (b, t, e) = fixture();
    let good = codec::frame(&b, &t, true, &e).unwrap();
    for index in [8, 12, 56, good.len() - 1] {
        let mut bad = good.clone();
        bad[index] ^= 1;
        assert!(codec::read(&bad, &b, true).is_err(), "tamper at {index}");
    }
    let mut trailing = good.clone();
    trailing.push(0);
    assert!(codec::read(&trailing, &b, true).is_err());
    for n in [0, 7, 15, 47, 55, good.len() - 1] {
        assert!(codec::read(&good[..n], &b, true).is_err());
    }
    assert!(codec::read(&good, &b, false).unwrap_err().0.contains("overflow-check mode"));
}
#[test]
fn a_level_r_codec_cannot_decode_a_level_s_envelope() {
    let (b, t, e) = fixture();
    let bytes = codec::frame(&b, &t, true, &e).unwrap();
    assert!(crate::rmeta_entry::decode_entry(&bytes).is_err());
}

#[test]
fn rust_binding_refuses_a_different_language_even_with_valid_structure() {
    let (b, mut t, e) = fixture();
    t.module.functions[0].producer = Some(trust_ir::Producer::Clean);
    assert!(codec::frame(&b, &t, true, &e).unwrap_err().0.contains("Rust producer binding"));
}

/// Re-seal a changed template without going through the validating writer: a
/// producer able to recompute SHA256 must still obey the independent Rust map.
fn reseal_template(
    good: &[u8],
    bindings: &OwnerBindings,
    template: &trust_ir::template::Template,
    evidence: &[u8],
) -> Vec<u8> {
    let slots_len: usize = bindings
        .slots
        .iter()
        .map(|s| match s.kind {
            SlotKind::Lifetime => 17,
            SlotKind::Type(_) => 21,
            SlotKind::Const { .. } => 22,
        })
        .sum();
    let mut payload = good[56..56 + 21 + slots_len].to_vec();
    payload.extend_from_slice(&template.digest().unwrap().bytes);
    let module = trust_ir::binary::serialize_template(template).unwrap();
    for part in [&module[..], evidence] {
        payload.extend_from_slice(&(part.len() as u64).to_le_bytes());
        payload.extend_from_slice(part);
    }
    let mut preimage = good[..16].to_vec();
    preimage.extend_from_slice(&payload);
    let digest =
        trust_ir::proof::ProofDigest::sha256_domain("trust.rmeta.template-envelope.v1", &preimage);
    let mut out = good[..16].to_vec();
    out.extend_from_slice(&digest.bytes);
    out.extend_from_slice(&(payload.len() as u64).to_le_bytes());
    out.extend_from_slice(&payload);
    out
}

#[test]
fn resealed_evidence_signature_mismatch_refuses() {
    let (b, t, e) = fixture();
    let good = codec::frame(&b, &t, true, &e).unwrap();
    for (arg_count, arg_enum) in
        [(0, vec![]), (2, vec![false; 2]), (1, vec![]), (1, vec![false; 2])]
    {
        let mut evidence = crate::rmeta_entry::decode_evidence(&e).unwrap();
        evidence.arg_count = arg_count;
        evidence.arg_enum = arg_enum;
        let bytes = crate::rmeta_entry::encode_evidence(&evidence);
        let forged = reseal_template(&good, &b, &t, &bytes);
        let written = codec::frame(&b, &t, true, &bytes);
        let read = codec::read(&forged, &b, true);
        assert!(
            written.is_err() && read.is_err(),
            "inconsistent argument evidence accepted: writer={}, reader={}",
            written.is_ok(),
            read.is_ok()
        );
        assert!(written.unwrap_err().0.contains("evidence argument"));
        assert!(read.unwrap_err().0.contains("evidence argument"));
    }
}

fn callee_fixture() -> (OwnerBindings, trust_ir::template::Template, Vec<u8>) {
    use trust_ir::template::{HoleDef, HoleKind, TemplateArg, TemplateParam, hole_row_name};
    use trust_ir::{HoleId, TemplateRef, TyG};

    use crate::template_key::{HoleKey, KeyArg, KeyTy};

    let (mut b, mut t, _) = fixture();
    b.slots.push(GenericSlot { definition: (11, 15), kind: SlotKind::Type(ParamId::new(1)) });
    t.header.params.push(TemplateParam::Type);
    let mut decl = t.module.functions[0].clone();
    decl.id = FuncId::new(1);
    decl.name = hole_row_name(HoleId::new(0));
    decl.blocks.clear();
    decl.body_gate = None;
    t.module.functions.push(decl);
    let key = HoleKey::Callee { item: (11, 30), args: vec![KeyArg::Type(KeyTy::Param(1))] };
    t.header.holes.push(HoleDef {
        kind: HoleKind::Callee { decl: FuncId::new(1) },
        key: crate::template_key::encode(&key).unwrap(),
        args: vec![TemplateArg::Type(TyG::Ext(TemplateRef::Param(ParamId::new(0))))],
    });
    let e = crate::rmeta_entry::encode_evidence(&crate::rmeta_entry::Evidence {
        arg_count: 1,
        arg_enum: vec![false],
        ledger: vec![crate::rmeta_entry::EvidenceLedgerRow {
            func_id: 1,
            ids: vec![(11, 30)],
            site: None,
        }],
        ..Default::default()
    });
    (b, t, e)
}

#[test]
fn resealed_ledger_population_mismatch_refuses() {
    let (b, t, e) = callee_fixture();
    let good = codec::frame(&b, &t, true, &e).unwrap();
    let original = crate::rmeta_entry::decode_evidence(&e).unwrap();
    let mut extra = original.clone();
    extra.ledger.push(crate::rmeta_entry::EvidenceLedgerRow {
        func_id: 2,
        ids: vec![(11, 99)],
        site: None,
    });
    let mut duplicate = original.clone();
    duplicate.ledger.push(original.ledger[0].clone());
    let mut body = original.clone();
    body.ledger[0].func_id = 0;
    let mut missing = original.clone();
    missing.ledger.clear();
    for evidence in [extra, duplicate, body, missing] {
        let bytes = crate::rmeta_entry::encode_evidence(&evidence);
        let forged = reseal_template(&good, &b, &t, &bytes);
        let written = codec::frame(&b, &t, true, &bytes);
        let read = codec::read(&forged, &b, true);
        assert!(
            written.is_err() && read.is_err(),
            "inconsistent ledger accepted: writer={}, reader={}",
            written.is_ok(),
            read.is_ok()
        );
        assert!(written.unwrap_err().0.contains("ledger"));
        assert!(read.unwrap_err().0.contains("ledger"));
    }
}

#[test]
fn resealed_dependency_and_typed_ledger_substitution_refuse() {
    use trust_ir::template::TemplateArg;
    use trust_ir::{TemplateRef, TyG};

    use crate::template_key::{HoleKey, KeyArg, KeyTy};

    let (b, t, e) = callee_fixture();
    let good = codec::frame(&b, &t, true, &e).unwrap();
    codec::read(&good, &b, true).unwrap();

    let mut wrong = t.clone();
    wrong.header.holes[0].args[0] =
        TemplateArg::Type(TyG::Ext(TemplateRef::Param(ParamId::new(1))));
    assert!(codec::frame(&b, &wrong, true, &e).unwrap_err().0.contains("dependencies"));
    let forged = reseal_template(&good, &b, &wrong, &e);
    assert!(codec::read(&forged, &b, true).unwrap_err().0.contains("dependencies"));

    let mut wrong = t;
    wrong.header.holes[0].key = crate::template_key::encode(&HoleKey::Callee {
        item: (11, 31),
        args: vec![KeyArg::Type(KeyTy::Param(1))],
    })
    .unwrap();
    let forged = reseal_template(&good, &b, &wrong, &e);
    assert!(codec::read(&forged, &b, true).unwrap_err().0.contains("retained ledger mismatch"));
}
