// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use super::*;

fn fixture(directory: &Path) -> CaseInputs {
    let (current, candidate) = super::super::tests::fixture(directory);
    let cases = LegacyManifest {
        schema: CASE_V1.to_owned(),
        inputs: LegacyInputs::from(&current),
        certificates: vec![CaseArtifact::new(0, &candidate)],
    };
    let properties = LegacyPropertyManifest {
        schema: PROPERTY_V1.to_owned(),
        api_schema: trust_spec_temporal::INVARIANT_MODEL_PROGRAM_PROPERTY_SCHEMA_V1.to_owned(),
        inputs: LegacyInputs::from(&current),
        certificates: vec![CaseArtifact::new(0, &candidate)],
    };
    fs::write(directory.join("case-set.json"), serde_json::to_vec(&cases).unwrap()).unwrap();
    fs::write(directory.join("source-property-set.json"), serde_json::to_vec(&properties).unwrap())
        .unwrap();
    fs::write(directory.join("source-refinement-0.json"), candidate).unwrap();
    current
}

#[test]
fn normal_legacy_reuse_refuses_but_explicit_complete_candidate_intake_records_original_bytes() {
    let prior = tempfile::tempdir().unwrap();
    let current = fixture(prior.path());
    assert!(CaseSet::load(prior.path(), &current).is_err());
    assert!(SourcePropertySet::load(prior.path(), &current).is_err());
    let imported = ImportedProofCandidates::load(prior.path(), &current).unwrap();
    let output = tempfile::tempdir().unwrap();
    imported.capture_provenance(output.path()).unwrap();
    assert_eq!(
        fs::read(output.path().join("imported-case-set.v1.json")).unwrap(),
        fs::read(prior.path().join("case-set.json")).unwrap()
    );
    assert_eq!(
        fs::read(output.path().join("imported-source-property-set.v1.json")).unwrap(),
        fs::read(prior.path().join("source-property-set.json")).unwrap()
    );
    assert_eq!(imported.read_case(0).unwrap(), imported.read_property(0).unwrap());
    assert!(
        imported.capture_provenance(output.path()).is_err(),
        "capture never overwrites prior evidence"
    );
}

#[test]
fn every_recorded_legacy_key_and_both_complete_inventories_are_required() {
    let prior = tempfile::tempdir().unwrap();
    let current = fixture(prior.path());
    let original = fs::read(prior.path().join("case-set.json")).unwrap();
    let value: serde_json::Value = serde_json::from_slice(&original).unwrap();
    for pointer in [
        "/inputs/source",
        "/inputs/source_sha256",
        "/inputs/compiler/executable",
        "/inputs/compiler/launcher_sha256",
        "/inputs/source_path_policy",
        "/inputs/module_sha256",
        "/inputs/suite/function",
        "/inputs/suite/mutation_from",
        "/inputs/suite/mutation_to",
    ] {
        let mut changed = value.clone();
        *changed.pointer_mut(pointer).unwrap() = serde_json::json!("different");
        fs::write(prior.path().join("case-set.json"), serde_json::to_vec(&changed).unwrap())
            .unwrap();
        assert!(ImportedProofCandidates::load(prior.path(), &current).is_err(), "{pointer}");
    }
    for pointer in [
        "/inputs/compiler/version",
        "/inputs/compiler/driver_files",
        "/inputs/extraction_flags",
        "/inputs/suite/cases",
        "/certificates",
    ] {
        let mut changed = value.clone();
        *changed.pointer_mut(pointer).unwrap() = serde_json::json!([]);
        fs::write(prior.path().join("case-set.json"), serde_json::to_vec(&changed).unwrap())
            .unwrap();
        assert!(ImportedProofCandidates::load(prior.path(), &current).is_err(), "{pointer}");
    }
    let mut changed = value.clone();
    changed["inputs"]["function_id"] = serde_json::json!(99);
    fs::write(prior.path().join("case-set.json"), serde_json::to_vec(&changed).unwrap()).unwrap();
    assert!(ImportedProofCandidates::load(prior.path(), &current).is_err());
    for (pointer, replacement) in [
        ("/inputs/suite/fuel", serde_json::json!(9)),
        ("/inputs/suite/cases/0/arguments", serde_json::json!([true])),
        ("/inputs/suite/cases/0/expected", serde_json::json!(false)),
        ("/inputs/suite/cases/0/permitted", serde_json::json!(false)),
    ] {
        let mut changed = value.clone();
        *changed.pointer_mut(pointer).unwrap() = replacement;
        fs::write(prior.path().join("case-set.json"), serde_json::to_vec(&changed).unwrap())
            .unwrap();
        assert!(ImportedProofCandidates::load(prior.path(), &current).is_err(), "{pointer}");
    }
    fs::write(prior.path().join("case-set.json"), original).unwrap();
    let original_property = fs::read(prior.path().join("source-property-set.json")).unwrap();
    for key in ["schema", "api_schema"] {
        let mut property: serde_json::Value = serde_json::from_slice(&original_property).unwrap();
        property[key] = serde_json::json!("unknown");
        fs::write(
            prior.path().join("source-property-set.json"),
            serde_json::to_vec(&property).unwrap(),
        )
        .unwrap();
        assert!(ImportedProofCandidates::load(prior.path(), &current).is_err());
    }
    fs::remove_file(prior.path().join("source-property-set.json")).unwrap();
    assert!(ImportedProofCandidates::load(prior.path(), &current).is_err());
}

#[test]
fn transport_capacity_is_checked_before_any_proof_work_and_at_publication() {
    let directory = tempfile::tempdir().unwrap();
    let (mut inputs, candidate) = super::super::tests::fixture(directory.path());
    validate_transport_capacity(&inputs).unwrap();
    inputs.compiler.driver_files = vec![(PathBuf::from("x".repeat(2048)), "0".repeat(64)); 1024];
    assert!(validate_transport_capacity(&inputs).is_err());
    let output = tempfile::tempdir().unwrap();
    assert!(
        publish_case_set(output.path(), inputs.clone(), vec![CaseArtifact::new(0, &candidate)])
            .is_err()
    );
    assert!(
        publish_source_property_set(output.path(), inputs, vec![CaseArtifact::new(0, &candidate)])
            .is_err()
    );
    assert!(!output.path().join("case-set.json").exists());
    assert!(!output.path().join("source-property-set.json").exists());
}

#[test]
fn imported_proof_with_recomputed_manifest_digest_still_requires_current_kernel_replay() {
    use trust_ir::{
        Block, BlockId, Constant, FuncId, FuncTy, FuncTyId, Function, Inst, InstrNode, Module, Ty,
        ValueId,
    };
    use trust_spec_temporal::literal_refinement::LiteralRefinementError;
    // Explicit IR codec fixture only, not production Rust-source evidence.
    let mut module = Module::new("legacy_import_kernel_fixture");
    module.func_types.push(FuncTy {
        params: vec![],
        returns: vec![Ty::Bool],
        is_vararg: false,
        abi: None,
    });
    let mut function = Function::new(FuncId::new(0), "answer", FuncTyId::new(0), BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.body.push(
        InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
            .with_result(ValueId::new(0)),
    );
    block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
    function.blocks.push(block);
    module.functions.push(function);
    let module = trust_ir::binary::serialize_module(&module).unwrap();
    let directory = tempfile::tempdir().unwrap();
    let mut current = fixture(directory.path());
    current.module_sha256 = sha256(&module);
    let case = &current.suite.cases[0];
    let claim = super::super::super::property(case, current.suite.fuel);
    let mut certificate = super::super::super::certify_literal_property(
        &module,
        0,
        &super::super::super::invocation(case),
        &claim,
        "SourceQualification.checked",
    )
    .unwrap();
    super::super::super::recheck_case_blob(
        &serde_json::to_vec(&certificate).unwrap(),
        &module,
        0,
        case,
        current.suite.fuel,
    )
    .unwrap();
    certificate.property.proof_term.clear();
    let altered = serde_json::to_vec(&certificate).unwrap();
    fs::write(directory.path().join("case-0.json"), &altered).unwrap();
    let cases = LegacyManifest {
        schema: CASE_V1.to_owned(),
        inputs: LegacyInputs::from(&current),
        certificates: vec![CaseArtifact::new(0, &altered)],
    };
    fs::write(directory.path().join("case-set.json"), serde_json::to_vec(&cases).unwrap()).unwrap();
    let mut properties: LegacyPropertyManifest = serde_json::from_slice(
        &fs::read(directory.path().join("source-property-set.json")).unwrap(),
    )
    .unwrap();
    properties.inputs = LegacyInputs::from(&current);
    fs::write(
        directory.path().join("source-property-set.json"),
        serde_json::to_vec(&properties).unwrap(),
    )
    .unwrap();
    let imported = ImportedProofCandidates::load(directory.path(), &current).unwrap();
    let candidate =
        imported.read_case(0).expect("the altered proof has its recomputed transport digest");
    let error =
        super::super::super::recheck_case_blob(&candidate, &module, 0, case, current.suite.fuel)
            .unwrap_err();
    assert!(matches!(
        error.downcast_ref::<LiteralRefinementError>(),
        Some(LiteralRefinementError::ArtifactMismatch { .. })
    ));
}
