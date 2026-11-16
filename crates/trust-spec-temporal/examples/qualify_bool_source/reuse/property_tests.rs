// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Untrusted property transport controls. The explicit IR fixture is checker
//! plumbing, not a claim about Rust resource source or the fixed custody policy.

use super::*;

fn fixture(directory: &Path) -> (CaseInputs, Vec<u8>) {
    let (inputs, bytes) = super::tests::fixture(directory);
    write_new(&directory.join("source-refinement-0.json"), &bytes).unwrap();
    publish_source_property_set(directory, inputs.clone(), vec![CaseArtifact::new(0, &bytes)])
        .unwrap();
    (inputs, bytes)
}

#[test]
fn property_identity_api_and_inventory_are_required() {
    let dir = tempfile::tempdir().unwrap();
    let (inputs, _) = fixture(dir.path());
    SourcePropertySet::load(dir.path(), &inputs).unwrap();
    let mut changed = inputs.clone();
    changed.source_sha256.push('0');
    assert!(SourcePropertySet::load(dir.path(), &changed).is_err());
    changed = inputs.clone();
    changed.compiler.version.push(0);
    assert!(SourcePropertySet::load(dir.path(), &changed).is_err());
    changed = inputs.clone();
    changed.module_sha256.push('0');
    assert!(SourcePropertySet::load(dir.path(), &changed).is_err());
    changed = inputs.clone();
    changed.suite.fuel += 1;
    assert!(SourcePropertySet::load(dir.path(), &changed).is_err());

    let path = dir.path().join("source-property-set.json");
    let original = fs::read(&path).unwrap();
    for field in ["schema", "api_schema"] {
        let mut manifest: serde_json::Value = serde_json::from_slice(&original).unwrap();
        manifest[field] = serde_json::json!("unknown");
        fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
        assert!(SourcePropertySet::load(dir.path(), &inputs).is_err());
    }
    for certificates in [
        vec![],
        vec![CaseArtifact::new(1, b"candidate")],
        vec![CaseArtifact::new(0, b"candidate"); 2],
    ] {
        let mut manifest: PropertyManifest = serde_json::from_slice(&original).unwrap();
        manifest.certificates = certificates;
        fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
        assert!(SourcePropertySet::load(dir.path(), &inputs).is_err());
    }
    let mut unknown: serde_json::Value = serde_json::from_slice(&original).unwrap();
    unknown["saved_verdict"] = serde_json::json!(true);
    fs::write(&path, serde_json::to_vec(&unknown).unwrap()).unwrap();
    assert!(SourcePropertySet::load(dir.path(), &inputs).is_err());
}

#[test]
fn property_candidates_are_bounded_owned_bytes_and_digest_changes_are_refused() {
    let dir = tempfile::tempdir().unwrap();
    let (inputs, expected) = fixture(dir.path());
    let loaded = SourcePropertySet::load(dir.path(), &inputs).unwrap();
    let owned = loaded.read_case(0).unwrap();
    let path = dir.path().join("source-refinement-0.json");
    fs::write(&path, b"replaced after read").unwrap();
    assert!(loaded.read_case(0).is_err());
    let output = tempfile::tempdir().unwrap();
    write_new(&output.path().join("source-refinement-0.json"), &owned).unwrap();
    assert_eq!(fs::read(output.path().join("source-refinement-0.json")).unwrap(), expected);
    fs::remove_file(&path).unwrap();
    std::os::unix::fs::symlink(output.path().join("source-refinement-0.json"), &path).unwrap();
    assert!(loaded.read_case(0).is_err());
    fs::remove_file(&path).unwrap();
    fs::File::create(&path).unwrap().set_len(CERTIFICATE_LIMIT + 1).unwrap();
    assert!(loaded.read_case(0).is_err());
    fs::remove_file(&path).unwrap();
    assert!(loaded.read_case(0).is_err());
}

#[test]
fn complete_property_inventory_retains_the_input_order() {
    let dir = tempfile::tempdir().unwrap();
    let (mut inputs, bytes) = super::tests::fixture(dir.path());
    inputs.suite.cases = [false, true]
        .into_iter()
        .map(|argument| super::super::Case {
            arguments: vec![argument],
            expected: true,
            permitted: true,
        })
        .collect();
    super::super::validate(&inputs.suite).unwrap();
    for index in 0..2 {
        write_new(&dir.path().join(format!("source-refinement-{index}.json")), &bytes).unwrap();
    }
    publish_source_property_set(
        dir.path(),
        inputs.clone(),
        vec![CaseArtifact::new(0, &bytes), CaseArtifact::new(1, &bytes)],
    )
    .unwrap();
    let loaded = SourcePropertySet::load(dir.path(), &inputs).unwrap();
    assert_eq!(loaded.read_case(1).unwrap(), bytes);
    let path = dir.path().join("source-property-set.json");
    let mut manifest: PropertyManifest = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
    manifest.certificates.reverse();
    fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
    assert!(SourcePropertySet::load(dir.path(), &inputs).is_err());
}

#[test]
fn property_prior_overlap_is_refused_before_output_and_both_priors_may_match() {
    let dir = tempfile::tempdir().unwrap();
    let prior = dir.path().join("prior");
    fs::create_dir(&prior).unwrap();
    let alias = dir.path().join("alias");
    std::os::unix::fs::symlink(&prior, &alias).unwrap();
    let nested = alias.join("output");
    assert!(admit_directories(&nested, None, Some(&prior)).is_err());
    assert!(!nested.exists());
    let output = dir.path().join("output");
    let (_, cases, properties) = admit_directories(&output, Some(&prior), Some(&alias)).unwrap();
    assert_eq!(cases, properties);
}

const MODEL: &str = r#"
namespace PropertyCodec
open Trust.Temporal.FiniteModel
def X : ScalarExpr := ScalarExpr.var "x"
def Model : Trust.Temporal.FiniteModel.Model :=
  Trust.Temporal.FiniteModel.Model.mk "PropertyCodec" []
    [StateVar.mk "x" 0] []
    [Action.mk "Stutter" Guard.always [Update.mk "x" X]]
    [Invariant.mk "Reflexive" (ScalarExpr.eq X X)]
end PropertyCodec
"#;

const REFINEMENT: &str = r#"
namespace PropertyCodec
open Trust.Temporal.FiniteModel
def Zero : State := State.mk (fun _ => 0) (fun _ _ => false)
def Projection (_ : IRConfig) : State := Zero
def I (_ : IRConfig) : Prop := True
theorem initialZero : Initial Model Zero :=
  And.intro (And.intro (fun _ _ => rfl) (fun _ _ _ => rfl))
    (And.intro
      (fun entry found => @everyMember StateVar
        (fun x : StateVar => Zero.scalar x.name = x.init)
        entry (_root_.Trust.Temporal.FiniteModel.Model.variables _root_.PropertyCodec.Model)
        ⟨rfl, True.intro⟩ found)
      (fun entry found => False.elim (memberNilFalse found)))
theorem refines : Trust.Temporal.InvariantForwardRefinement
    Trust.LiteralRefinement.Model (StateMachine Model) Projection I :=
  { init_invariant := fun _ _ => True.intro
    preserve_invariant := fun _ _ _ _ => True.intro
    init := fun _ _ => initialZero
    next := fun _ _ _ _ => Or.inr rfl }
end PropertyCodec
"#;

const PROPERTY: &str = r#"
namespace PropertyCodec
theorem checked (behavior : Trust.Temporal.Behavior IRConfig)
    (runs : Trust.Temporal.Runs Trust.LiteralRefinement.Model behavior) :
    Trust.Temporal.Runs (Trust.Temporal.FiniteModel.StateMachine Model)
      (fun n => Projection (behavior n)) :=
  Trust.Temporal.invariantForwardRefinementRuns
    Trust.LiteralRefinement.Model (Trust.Temporal.FiniteModel.StateMachine Model)
    Projection I refines behavior runs
end PropertyCodec
"#;

#[test]
fn a_recomputed_property_digest_cannot_admit_a_spliced_checked_term() {
    use trust_ir::{
        Block, BlockId, Constant, FuncId, FuncTy, FuncTyId, Function, Inst, InstrNode, Module, Ty,
        ValueId,
    };
    use trust_spec_temporal::literal_refinement::LiteralInvocation;
    use trust_spec_temporal::{
        ModelProgramRefinementError, certify_invariant_model_program_property,
        recheck_invariant_model_program_property,
    };

    let mut module = Module::new("property_transport_codec");
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
    let invocation = LiteralInvocation::closed(vec![], 0);
    let mut certificate = certify_invariant_model_program_property(
        &module,
        0,
        &invocation,
        MODEL,
        "PropertyCodec.Model",
        REFINEMENT,
        "PropertyCodec.I",
        "PropertyCodec.Projection",
        "PropertyCodec.refines",
        "",
        PROPERTY,
        "PropertyCodec.checked",
    )
    .unwrap();
    let replay = |certificate: &_| {
        recheck_invariant_model_program_property(
            certificate,
            &module,
            0,
            &invocation,
            MODEL,
            "PropertyCodec.Model",
            REFINEMENT,
            "PropertyCodec.I",
            "PropertyCodec.Projection",
            "PropertyCodec.refines",
            "",
            PROPERTY,
            "PropertyCodec.checked",
        )
    };
    let dir = tempfile::tempdir().unwrap();
    let (mut inputs, _) = super::tests::fixture(dir.path());
    inputs.module_sha256 = sha256(&module);
    let encoded = serde_json::to_vec(&certificate).unwrap();
    write_new(&dir.path().join("source-refinement-0.json"), &encoded).unwrap();
    publish_source_property_set(dir.path(), inputs.clone(), vec![CaseArtifact::new(0, &encoded)])
        .unwrap();
    let loaded = SourcePropertySet::load(dir.path(), &inputs).unwrap();
    replay(&serde_json::from_slice(&loaded.read_case(0).unwrap()).unwrap()).unwrap();

    // A valid encoded term from a different theorem, with a freshly recomputed
    // transport digest, must still fail the unchanged public proof replay.
    certificate.property.proof_term = certificate.refinement.theorems[0].proof_term.clone();
    let tampered = serde_json::to_vec(&certificate).unwrap();
    fs::write(dir.path().join("source-refinement-0.json"), &tampered).unwrap();
    let manifest = PropertyManifest {
        schema: PROPERTY_SCHEMA.to_owned(),
        api_schema: trust_spec_temporal::INVARIANT_MODEL_PROGRAM_PROPERTY_SCHEMA_V1.to_owned(),
        inputs: inputs.clone(),
        certificates: vec![CaseArtifact::new(0, &tampered)],
    };
    fs::write(dir.path().join("source-property-set.json"), serde_json::to_vec(&manifest).unwrap())
        .unwrap();
    let loaded = SourcePropertySet::load(dir.path(), &inputs).unwrap();
    let candidate = loaded.read_case(0).expect("the tampered term has a matching transport digest");
    assert_eq!(candidate, tampered);
    assert!(matches!(
        replay(&serde_json::from_slice(&candidate).unwrap()),
        Err(ModelProgramRefinementError::ArtifactMismatch {
            field: "property theorem or proof",
            ..
        })
    ));
}
