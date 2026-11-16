use trust_types::Sort;

use super::*;

fn input(name: &str) -> Formula {
    Formula::Var(name.into(), Sort::BitVec(64))
}
fn low(value: Formula) -> Formula {
    Formula::BvExtract { inner: Box::new(value), high: 31, low: 0 }
}
fn add() -> Formula {
    Formula::BvAdd(Box::new(low(input("X0"))), Box::new(low(input("X1"))), 32)
}
fn check(formula: &Formula) -> Result<u32, String> {
    kernel::formula_width(formula, &mut 0, 0, &mut BTreeSet::new(), false)
}

#[test]
fn supported_widths_extract_and_extension_are_exact() {
    assert_eq!(check(&add()).unwrap(), 32);
    let wrapped = low(Formula::BvZeroExt(
        Box::new(Formula::BvOr(
            Box::new(Formula::BitVec { value: 0, width: 32 }),
            Box::new(add()),
            32,
        )),
        32,
    ));
    assert_eq!(check(&wrapped).unwrap(), 32);
}

#[test]
fn mismatched_high_low_extension_and_arithmetic_width_refuse() {
    for (high, low_bit) in [(15, 0), (32, 0), (31, 1), (u32::MAX, 0)] {
        let formula = Formula::BvExtract {
            inner: Box::new(Formula::BvZeroExt(Box::new(add()), 32)),
            high,
            low: low_bit,
        };
        assert!(check(&formula).is_err());
    }
    for extra in [0, 16, 31, 33, u32::MAX] {
        assert!(check(&low(Formula::BvZeroExt(Box::new(add()), extra))).is_err());
    }
    for width in [0, 8, 16, 64, u32::MAX] {
        assert!(
            check(&Formula::BvAdd(Box::new(low(input("X0"))), Box::new(low(input("X1"))), width))
                .is_err()
        );
    }
    assert!(check(&low(add())).is_err(), "an extract expecting64 cannot consume32");
}

#[test]
fn unowned_and_aliased_register_leaves_refuse() {
    for name in ["X2", "X00", "X01", "x0", "X0.0", "SP", "X30", "BVC_LEAF_X0_64"] {
        assert!(check(&low(input(name))).is_err());
    }
    assert!(check(&low(Formula::Var("X0".into(), Sort::BitVec(32)))).is_err());
    assert!(check(&low(Formula::Var("X0".into(), Sort::Bool))).is_err());
}

#[test]
fn unsupported_formula_effects_and_standalone_zero_extension_refuse() {
    assert!(check(&Formula::Bool(true)).is_err());
    assert!(check(&Formula::BvZeroExt(Box::new(add()), 32)).is_err());
    assert!(
        check(&Formula::BvSub(Box::new(low(input("X0"))), Box::new(low(input("X1"))), 32)).is_err()
    );
    assert!(
        check(&Formula::BvOr(Box::new(low(input("X0"))), Box::new(low(input("X1"))), 32)).is_err()
    );
    assert!(check(&Formula::BitVec { value: 1, width: 32 }).is_err());
}

#[test]
fn formula_depth_and_population_budgets_are_real() {
    let mut deep = low(input("X0"));
    for _ in 0..70 {
        deep = low(Formula::BvZeroExt(Box::new(deep), 32));
    }
    assert!(check(&deep).unwrap_err().contains("budget"));
    let mut wide = add();
    for _ in 0..10 {
        wide = Formula::BvAdd(Box::new(wide.clone()), Box::new(wide), 32);
    }
    assert!(check(&wide).unwrap_err().contains("budget"));
}

// This is ONLY a wire-shape fixture, deliberately not a claimed proof. Actual
// production and kernel controls below use the real emitted Add certificate.
fn wire() -> CompactCertificate {
    CompactCertificate {
        model: MODEL,
        leaves: vec![("X0".into(), 64), ("X1".into(), 64)],
        environment_sha256: "0".repeat(64),
        terms: vec![TermNode::Const {
            name: vec![NamePart::Str { value: "Bool".into() }],
            universes: vec![],
        }],
        goal: 0,
        proof: 0,
    }
}

#[test]
fn canonical_flat_wire_roundtrips_without_identity_projection() {
    let value = wire();
    value.validate_graph().unwrap();
    let bytes = encode(&value, MAX_CERTIFICATE_BYTES).unwrap();
    assert_eq!(serde_json::from_slice::<CompactCertificate>(&bytes).unwrap(), value);
    let numeric = vec![NamePart::Str { value: "owner".into() }, NamePart::Num { value: 7 }];
    let string = vec![NamePart::Str { value: "owner".into() }, NamePart::Str { value: "7".into() }];
    assert_ne!(numeric, string);
    assert_ne!(
        vec![NamePart::Str { value: "owner.dot".into() }],
        vec![NamePart::Str { value: "owner".into() }, NamePart::Str { value: "dot".into() }]
    );
}

#[test]
fn cyclic_forward_and_invalid_roots_refuse() {
    for node in [
        TermNode::App { function: 1, argument: 0 },
        TermNode::App { function: 0, argument: u32::MAX },
    ] {
        let mut value = wire();
        value.terms.push(node);
        value.proof = 1;
        assert!(value.validate_graph().is_err());
    }
    let mut value = wire();
    value.goal = u32::MAX;
    assert!(value.validate_graph().is_err());
}

#[test]
fn duplicate_and_unreachable_term_rows_refuse() {
    let mut value = wire();
    value.terms.push(value.terms[0].clone());
    value.proof = 1;
    assert!(value.validate_graph().unwrap_err().contains("duplicate"));
    let mut value = wire();
    value.terms.push(TermNode::Const {
        name: vec![NamePart::Str { value: "Nat".into() }],
        universes: vec![],
    });
    assert!(value.validate_graph().unwrap_err().contains("unaccounted"));
}

#[test]
fn expanded_graph_depth_name_and_universe_bounds_refuse() {
    let mut value = wire();
    for index in 1..30 {
        value.terms.push(TermNode::App { function: index - 1, argument: index - 1 });
        value.proof = index;
    }
    assert!(value.validate_graph().unwrap_err().contains("budget"));
    let mut value = wire();
    for index in 1..260 {
        value.terms.push(TermNode::App { function: index - 1, argument: 0 });
        value.proof = index;
    }
    assert!(value.validate_graph().unwrap_err().contains("budget"));
    for node in [
        TermNode::Const { name: vec![NamePart::Str { value: "x".repeat(257) }], universes: vec![] },
        TermNode::Const { name: vec![NamePart::Str { value: "Bool".into() }], universes: vec![5] },
    ] {
        let mut value = wire();
        value.terms[0] = node;
        assert!(value.validate_graph().is_err());
    }
}

#[test]
fn model_leaf_environment_and_unknown_fields_are_fail_closed() {
    for field in ["model", "leaves", "environment_sha256"] {
        let mut value = serde_json::to_value(wire()).unwrap();
        value[field] = match field {
            "model" => 2.into(),
            "leaves" => serde_json::json!([["X0", 64], ["X0", 64]]),
            _ => "not-a-digest".into(),
        };
        assert!(
            serde_json::from_value::<CompactCertificate>(value).unwrap().validate_graph().is_err()
        );
    }
    let mut value = serde_json::to_value(wire()).unwrap();
    value["assumed_proof"] = true.into();
    assert!(serde_json::from_value::<CompactCertificate>(value).is_err());
}

fn actual() -> (TrustIrGateSource, TrustCgCodegenBackend, ObjectReplayArtifact) {
    use trust_ir::inst::{BinOp, Inst};
    use trust_ir::node::InstrNode;
    use trust_ir::ty::FuncTy;
    use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
    use trust_ir::{Block, Function, Module, Ty};

    use crate::codegen_backend::BridgeOptimizationLevel;
    use crate::verify_output::EmitPolicy;
    let mut module = Module::new("compact-certificate-actual-close-controls");
    module.func_types.push(FuncTy {
        params: vec![Ty::U32, Ty::U32],
        returns: vec![Ty::U32],
        is_vararg: false,
        abi: None,
    });
    let mut function =
        Function::new(FuncId::new(0), "compact_add", FuncTyId::new(0), BlockId::new(0));
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
    let source = TrustIrGateSource {
        symbol: "compact_add".into(),
        module: module.into(),
        func_id: FuncId::new(0),
        abi_cross_check: None,
    };
    let backend =
        TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::AArch64, "aarch64-apple-darwin")
            .with_optimization_level(BridgeOptimizationLevel::O0);
    let (object, report, artifact) =
        crate::verify_output_trust_ir::emit_trust_ir_module_object_with_replay(
            std::slice::from_ref(&source),
            &[],
            &[],
            EmitPolicy::StrictProvenOnly,
            &backend,
        )
        .unwrap();
    assert_eq!(report.proved, 1);
    assert_eq!(report.uncertified(), 0);
    let mut artifact = artifact.unwrap();
    assert_eq!(artifact.object_bytes, object.bytes);
    assert_eq!(artifact.functions.len(), 1);
    // Default production may now retain a bounded bitblast proof. Exercise its
    // real fallback selection with a smaller export budget so the compact
    // ownership and mutation checks never depend on an inefficient exporter.
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
    assert!(
        matches!(artifact.functions[0].evidence, RetainedEvidence::CompactInstantiation { .. }),
        "{:?}",
        artifact.functions[0].evidence
    );
    let report =
        artifact.replay(std::slice::from_ref(&source), &object.bytes, &backend, &[], &[]).unwrap();
    assert_eq!(report.rows.len(), 1);
    assert!(report.rows[0].1.is_ok(), "{:?}", report);
    (source, backend, artifact)
}

#[test]
fn actual_retained_term_rejects_name_leaf_goal_environment_and_reference_twins() {
    let (source, backend, artifact) = actual();
    let RetainedEvidence::CompactInstantiation { certificate } = &artifact.functions[0].evidence
    else {
        panic!()
    };
    let original_bytes = encode(certificate, MAX_CERTIFICATE_BYTES).unwrap();
    eprintln!(
        "actual compact certificate: nodes={} bytes={} sha256={} environment={}",
        certificate.terms.len(),
        original_bytes.len(),
        hash(&original_bytes),
        certificate.environment_sha256
    );
    let mut twins = Vec::new();
    let mut twin = certificate.clone();
    twin.environment_sha256 = "0".repeat(64);
    twins.push(twin);
    let mut twin = certificate.clone();
    twin.leaves[0].0 = "X1".into();
    twins.push(twin);
    let mut twin = certificate.clone();
    let goal = twin.goal;
    twin.goal = twin.proof;
    twin.proof = goal;
    twins.push(twin);
    let mut twin = certificate.clone();
    twin.terms.push(twin.terms[0].clone());
    twins.push(twin);
    let mut twin = certificate.clone();
    let leaf = twin.terms.iter_mut().find(|node| matches!(node,TermNode::Const { name, .. } if name == &vec![NamePart::Str { value:"BVC_LEAF_X0_64".into() }])).expect("actual exact X0 leaf");
    *leaf = TermNode::Const {
        name: vec![NamePart::Str { value: "BVC_LEAF_X1_64".into() }],
        universes: vec![],
    };
    twins.push(twin);
    let mut twin = certificate.clone();
    let TermNode::Const { name, .. } = &mut twin.terms[0] else { panic!() };
    *name = vec![NamePart::Str { value: "Eq.trans".into() }];
    twins.push(twin);
    let mut twin = certificate.clone();
    let TermNode::Const { name, .. } = &mut twin.terms[0] else { panic!() };
    *name = vec![NamePart::Num { value: 7 }];
    twins.push(twin);
    let mut twin = certificate.clone();
    let TermNode::Const { universes, .. } = &mut twin.terms[0] else { panic!() };
    *universes = vec![2];
    twins.push(twin);
    let mut twin = certificate.clone();
    let TermNode::App { function, argument } = &mut twin.terms[certificate.proof as usize] else {
        panic!()
    };
    std::mem::swap(function, argument);
    twins.push(twin);
    assert_eq!(twins.len(), 9);
    for twin in twins {
        assert!(
            replay(&source, &artifact.functions[0].object_bytes, backend.target_arch(), &twin)
                .is_err()
        );
        assert_eq!(
            encode(certificate, MAX_CERTIFICATE_BYTES).unwrap(),
            original_bytes,
            "original actual proof is never replaced"
        );
    }
    let mut malformed = Vec::new();
    let mut twin = certificate.clone();
    twin.model = MODEL + 1;
    malformed.push(twin);
    let mut twin = certificate.clone();
    twin.terms.push(twin.terms[0].clone());
    malformed.push(twin);
    let mut twin = certificate.clone();
    twin.terms[0] = TermNode::App { function: 0, argument: 0 };
    malformed.push(twin);
    let mut twin = certificate.clone();
    twin.leaves[0] = twin.leaves[1].clone();
    malformed.push(twin);
    for certificate in malformed {
        let mut twin = artifact.clone();
        twin.functions[0].evidence = RetainedEvidence::CompactInstantiation { certificate };
        assert!(
            ObjectReplayArtifact::from_bytes(&twin.to_bytes().unwrap()).is_err(),
            "unknown compact model and malformed graphs refuse during wire decode"
        );
    }
    let mut old = artifact.clone();
    old.schema = 1;
    old.scope = LEGACY_SCOPE.into();
    old.functions[0].abi_context = super::super::RetainedAbiContext::LegacyAbsent;
    assert!(
        ObjectReplayArtifact::from_bytes(&old.to_bytes().unwrap()).is_err(),
        "compact cannot masquerade as legacy evidence"
    );
    assert!(old.replay(&[source], &old.object_bytes, &backend, &[], &[]).is_err());
}

#[test]
fn actual_add_term_rejects_rebound_source_object_and_parameter_ownership() {
    use trust_disasm::{Opcode, decode_aarch64};
    use trust_ir::inst::{BinOp, Inst};
    let (source, backend, artifact) = actual();
    let mut changed_source = source.clone();
    let Inst::BinOp { op, .. } =
        &mut std::sync::Arc::make_mut(&mut changed_source.module).functions[0].blocks[0].body[0]
            .inst
    else {
        panic!()
    };
    *op = BinOp::Sub;
    let mut twin = artifact.clone();
    let row = &mut twin.functions[0];
    row.module_bytes = encode(&changed_source.module, MAX_PART_BYTES).unwrap();
    row.module_sha256 = hash(&row.module_bytes);
    row.obligation =
        trust_ir_gate_obligation(&changed_source, &row.object_bytes, backend.target_arch());
    let report = twin.replay(&[changed_source], &twin.object_bytes, &backend, &[], &[]).unwrap();
    assert_eq!(report.rows.len(), 1);
    assert!(report.rows[0].1.is_err());
    let mut changed_source = source.clone();
    let Inst::BinOp { lhs, rhs, .. } =
        &mut std::sync::Arc::make_mut(&mut changed_source.module).functions[0].blocks[0].body[0]
            .inst
    else {
        panic!()
    };
    *rhs = *lhs;
    let RetainedEvidence::CompactInstantiation { certificate } = &artifact.functions[0].evidence
    else {
        panic!()
    };
    assert!(
        replay(
            &changed_source,
            &artifact.functions[0].object_bytes,
            backend.target_arch(),
            certificate
        )
        .is_err()
    );
    // Stay inside the supported source/machine/formula language, but compute
    // x + 2*y. This must reach and fail the actual generated-term kernel check,
    // not merely fail an identity hash or the instruction/formula allowlist.
    let (text, _) = extract_text_from_object(&artifact.functions[0].object_bytes).unwrap();
    let adds: Vec<_> = text
        .chunks_exact(4)
        .enumerate()
        .filter_map(|(i, bytes)| {
            (decode_aarch64(bytes, (i * 4) as u64).unwrap().opcode == Opcode::Add)
                .then_some((i, u32::from_le_bytes(bytes.try_into().unwrap())))
        })
        .collect();
    assert_eq!(adds.len(), 1);
    let (index, word) = adds[0];
    let second_add = (word & !(31 << 5)) | ((word & 31) << 5);
    let mut twice_text = text.to_vec();
    twice_text.splice((index + 1) * 4..(index + 1) * 4, second_add.to_le_bytes());
    let mut writer = trust_cg_codegen::macho::MachOWriter::new();
    writer.add_text_section(&twice_text);
    writer.add_symbol(&format!("_{}", source.symbol), 1, 0, true).unwrap();
    let twice_object = writer.write().unwrap();
    scalar_certificate::qualify_machine(&source, &twice_object, backend.target_arch()).unwrap();
    let twice_obligation = trust_ir_gate_obligation(&source, &twice_object, backend.target_arch())
        .expect("supported changed machine has a reconstructed obligation");
    assert_eq!(check(&twice_obligation.machine_value).unwrap(), 32);
    assert_eq!(check(&twice_obligation.spec_value).unwrap(), 32);
    assert_ne!(twice_obligation.machine_value, twice_obligation.spec_value);
    let refusal = capture(&source, &twice_object, backend.target_arch()).unwrap_err();
    assert!(refusal.contains("generated kernel term refused"), "{refusal}");
    let mut twin = artifact;
    for bytes in [&mut twin.object_bytes, &mut twin.functions[0].object_bytes] {
        let (text, _) = extract_text_from_object(bytes).unwrap();
        let offsets: Vec<_> = bytes
            .windows(text.len())
            .enumerate()
            .filter_map(|(i, w)| (w == text).then_some(i))
            .collect();
        assert_eq!(offsets.len(), 1);
        let adds: Vec<_> = text
            .chunks_exact(4)
            .enumerate()
            .filter_map(|(i, w)| {
                (decode_aarch64(w, (i * 4) as u64).unwrap().opcode == Opcode::Add)
                    .then_some((i, u32::from_le_bytes(w.try_into().unwrap())))
            })
            .collect();
        assert_eq!(adds.len(), 1, "complete actual opcode population has one Add");
        let (index, word) = adds[0];
        let changed = (word ^ (1 << 30)).to_le_bytes();
        assert_eq!(decode_aarch64(&changed, (index * 4) as u64).unwrap().opcode, Opcode::Sub);
        let at = offsets[0] + index * 4;
        bytes[at..at + 4].copy_from_slice(&changed);
    }
    twin.object_sha256 = hash(&twin.object_bytes);
    let row = &mut twin.functions[0];
    row.object_sha256 = hash(&row.object_bytes);
    row.obligation = trust_ir_gate_obligation(&source, &row.object_bytes, backend.target_arch());
    let changed = row.obligation.as_ref().unwrap();
    assert_ne!(changed.machine_value, changed.spec_value);
    let report = twin.replay(&[source], &twin.object_bytes, &backend, &[], &[]).unwrap();
    assert_eq!(report.rows.len(), 1);
    assert!(report.rows[0].1.is_err());
}
