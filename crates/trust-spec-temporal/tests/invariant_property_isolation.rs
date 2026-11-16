// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Hostile integration controls for composed property intake and source-unit isolation.
//!
//! This explicit IR/model fixture tests the generic checker. It supplies no actual
//! Rust resource-policy, custody, operating-system or machine-code evidence.

use std::sync::OnceLock;

use trust_ir::{
    Block, BlockId, FuncId, FuncTy, FuncTyId, Function, Inst, InstrNode, Module, Ty, ValueId,
};
use trust_spec_temporal::literal_refinement::LiteralInvocation;
use trust_spec_temporal::{
    CleanTemporalCertificateError, INVARIANT_MODEL_PROGRAM_PROPERTY_SCHEMA_V1,
    InvariantModelProgramPropertyCertificate, ModelProgramRefinementError,
    certify_invariant_model_program_property, recheck_invariant_model_program_property,
};

const MODEL_NAME: &str = "PropertyIsolationFixture.Model";
const INVARIANT_NAME: &str = "PropertyIsolationFixture.SourceInvariant";
const PROJECTION_NAME: &str = "PropertyIsolationFixture.Projection";
const REFINEMENT_NAME: &str = "PropertyIsolationFixture.ProgramRefines";
const PROPERTY_NAME: &str = "PropertyIsolationFixture.FinalRuns";

const MODEL_SOURCE: &str = r#"
namespace PropertyIsolationFixture
open Trust.Temporal.FiniteModel

def X : ScalarExpr := ScalarExpr.var "x"

def Model : Trust.Temporal.FiniteModel.Model :=
  Trust.Temporal.FiniteModel.Model.mk "PropertyIsolationFixture" []
    [StateVar.mk "x" 0] []
    [Action.mk "Stutter" Guard.always [Update.mk "x" X]]
    [Invariant.mk "Reflexive" (ScalarExpr.eq X X)]

end PropertyIsolationFixture
"#;

const REFINEMENT_SOURCE: &str = r#"
namespace PropertyIsolationFixture
open Trust.Temporal.FiniteModel

def AbstractZero : State := State.mk (fun _ => 0) (fun _ _ => false)
def Projection (_ : IRConfig) : State := AbstractZero
def SourceInvariant (_ : IRConfig) : Prop := True
def refinementSlow (n : Nat) : Nat := n + 1

theorem noMemberNil {α : Type} {value : α}
    (member : Member value []) : False :=
  @Member.rec α value
    (fun list _ =>
      match list with
      | [] => False
      | _ :: _ => True)
    (fun _ => True.intro)
    (fun _ _ _ _ => True.intro)
    [] member

theorem memberUncons {α : Type} {value head : α} {tail : List α}
    (member : Member value (head :: tail)) :
    value = head ∨ Member value tail :=
  @Member.rec α value
    (fun list _ =>
      match list with
      | [] => True
      | first :: rest => value = first ∨ Member value rest)
    (fun _ => Or.inl rfl)
    (fun _ _ previous _ => Or.inr previous)
    (head :: tail) member

theorem memberSingleton {α : Type} {value only : α}
    (member : Member value [only]) : value = only :=
  match memberUncons member with
  | Or.inl same => same
  | Or.inr impossible => False.elim (noMemberNil impossible)

theorem initialScalars (entry : StateVar)
    (member : Member entry [StateVar.mk "x" 0]) :
    AbstractZero.scalar entry.name = entry.init := by
  have same : entry = StateVar.mk "x" 0 := memberSingleton member
  rewrite [same]
  rfl

theorem projectionInitial : Initial Model AbstractZero :=
  And.intro
    (And.intro (fun _ _ => rfl) (fun _ _ _ => rfl))
    (And.intro initialScalars
      (fun entry member index => False.elim (noMemberNil member)))

theorem ProgramRefines :
    Trust.Temporal.InvariantForwardRefinement
      Trust.LiteralRefinement.Model
      (Trust.Temporal.FiniteModel.StateMachine Model)
      Projection SourceInvariant :=
  { init_invariant := fun _ _ => True.intro
    preserve_invariant := fun _ _ _ _ => True.intro
    init := fun _ _ => projectionInitial
    next := fun _ _ _ _ => Or.inr rfl }

end PropertyIsolationFixture
"#;

const SUPPORT_SOURCE: &str = r#"
namespace PropertyIsolationFixture

def supportSlow (n : Nat) : Nat := n + 2
def supportFast (n : Nat) : Nat := n + 1
attribute [implemented_by supportFast] supportSlow
def supportForeign (n : Nat) : Nat := n
attribute [extern "property_isolation_support"] supportForeign
theorem supportReady : True := True.intro

end PropertyIsolationFixture
"#;

const PROPERTY_SOURCE: &str = r#"
namespace PropertyIsolationFixture

def propertySlow (n : Nat) : Nat := n + 2
def propertyFast (n : Nat) : Nat := n + 1
attribute [implemented_by propertyFast] propertySlow
def propertyForeign (n : Nat) : Nat := n
attribute [extern "property_isolation_final"] propertyForeign

theorem FinalRuns
    (behavior : Trust.Temporal.Behavior IRConfig)
    (runs : Trust.Temporal.Runs Trust.LiteralRefinement.Model behavior) :
    Trust.Temporal.Runs
      (Trust.Temporal.FiniteModel.StateMachine Model)
      (fun n => Projection (behavior n)) ∧ True :=
  And.intro
    (Trust.Temporal.invariantForwardRefinementRuns
      Trust.LiteralRefinement.Model
      (Trust.Temporal.FiniteModel.StateMachine Model)
      Projection SourceInvariant ProgramRefines behavior runs)
    supportReady

end PropertyIsolationFixture
"#;

fn fixture_bytes() -> Vec<u8> {
    let mut module = Module::new("invariant_property_isolation");
    module.func_types.push(FuncTy {
        params: vec![],
        returns: vec![Ty::U8],
        is_vararg: false,
        abi: None,
    });
    let mut function = Function::new(FuncId::new(0), "answer", FuncTyId::new(0), BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.body.push(
        InstrNode::new(Inst::Const { ty: Ty::U8, value: trust_ir::Constant::Int(7) })
            .with_result(ValueId::new(0)),
    );
    block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
    function.blocks.push(block);
    module.functions.push(function);
    trust_ir::binary::serialize_module(&module).expect("serialize the explicit plumbing fixture")
}

fn certify(
    support: &str,
    property: &str,
) -> Result<InvariantModelProgramPropertyCertificate, ModelProgramRefinementError> {
    certify_invariant_model_program_property(
        &fixture_bytes(),
        0,
        &LiteralInvocation::closed(vec![], 0),
        MODEL_SOURCE,
        MODEL_NAME,
        REFINEMENT_SOURCE,
        INVARIANT_NAME,
        PROJECTION_NAME,
        REFINEMENT_NAME,
        support,
        property,
        PROPERTY_NAME,
    )
}

fn certificate() -> &'static InvariantModelProgramPropertyCertificate {
    static CERTIFICATE: OnceLock<InvariantModelProgramPropertyCertificate> = OnceLock::new();
    CERTIFICATE.get_or_init(|| {
        certify(SUPPORT_SOURCE, PROPERTY_SOURCE).expect("the staged positive fixture must certify")
    })
}

fn recheck(
    candidate: &InvariantModelProgramPropertyCertificate,
) -> Result<(), ModelProgramRefinementError> {
    recheck_with_sources(candidate, SUPPORT_SOURCE, PROPERTY_SOURCE)
}

fn recheck_with_sources(
    candidate: &InvariantModelProgramPropertyCertificate,
    support: &str,
    property: &str,
) -> Result<(), ModelProgramRefinementError> {
    recheck_invariant_model_program_property(
        candidate,
        &fixture_bytes(),
        0,
        &LiteralInvocation::closed(vec![], 0),
        MODEL_SOURCE,
        MODEL_NAME,
        REFINEMENT_SOURCE,
        INVARIANT_NAME,
        PROJECTION_NAME,
        REFINEMENT_NAME,
        support,
        property,
        PROPERTY_NAME,
    )
}

#[test]
fn invalid_children_and_inner_proofs_precede_property_size_limits() {
    use trust_spec_temporal::literal_refinement::LiteralRefinementError;

    // A valid, complete support unit beyond the documented 32 MiB input
    // limit. If a refactor moves this guard before inner replay, it masks
    // the more fundamental child/proof failures below.
    let support = format!("{SUPPORT_SOURCE}\n{}", " ".repeat(32 * 1024 * 1024));
    let mut oversized = certificate().clone();
    oversized.support_source = support.clone();

    let mut bad_child = oversized.clone();
    bad_child.refinement.literal.module_bytes.push(0);
    assert!(matches!(
        recheck_with_sources(&bad_child, &support, PROPERTY_SOURCE),
        Err(ModelProgramRefinementError::Literal(LiteralRefinementError::ModuleMismatch))
    ));

    let mut bad_proof = oversized.clone();
    bad_proof.refinement.theorems[0].proof_term.clear();
    assert!(matches!(
        recheck_with_sources(&bad_proof, &support, PROPERTY_SOURCE),
        Err(ModelProgramRefinementError::ArtifactMismatch { field: "proof term", .. })
    ));

    // The unchanged inner artifact must reach and enforce the support bound.
    assert!(matches!(
        recheck_with_sources(&oversized, &support, PROPERTY_SOURCE),
        Err(ModelProgramRefinementError::SourceTooLarge {
            role: "support", bytes, maximum,
        }) if bytes == support.len() && maximum == 32 * 1024 * 1024
    ));
}

#[test]
fn composed_property_replay_binds_sources_inner_proofs_and_final_proof() {
    let original = certificate();
    assert_eq!(original.schema, INVARIANT_MODEL_PROGRAM_PROPERTY_SCHEMA_V1);
    let wire = serde_json::to_vec(original).expect("encode the property certificate");
    let decoded = serde_json::from_slice(&wire).expect("decode the property certificate");
    recheck(&decoded).expect("independent fresh replay of the serialized property");

    let mut candidate = original.clone();
    candidate.support_source.push_str("\n-- different support bytes\n");
    assert_eq!(recheck(&candidate), Err(ModelProgramRefinementError::SupportSourceMismatch));

    candidate = original.clone();
    candidate.property_source.push_str("\n-- different final property bytes\n");
    assert_eq!(recheck(&candidate), Err(ModelProgramRefinementError::PropertySourceMismatch));

    candidate = original.clone();
    candidate.property.theorem = "PropertyIsolationFixture.AnotherGoal".to_owned();
    assert_eq!(recheck(&candidate), Err(ModelProgramRefinementError::PropertyTheoremMismatch));

    candidate = original.clone();
    candidate.refinement.theorems.pop();
    assert_eq!(recheck(&candidate), Err(ModelProgramRefinementError::TheoremSetMismatch));

    candidate = original.clone();
    candidate.refinement.literal.module_bytes.push(0);
    assert!(matches!(recheck(&candidate), Err(ModelProgramRefinementError::Literal(_))));

    candidate = original.clone();
    candidate.property.proof_term = b"0".to_vec();
    assert!(matches!(
        recheck(&candidate),
        Err(ModelProgramRefinementError::ArtifactMismatch { .. })
    ));

    let mut unknown = serde_json::to_value(original).expect("encode the outer certificate");
    unknown
        .as_object_mut()
        .expect("certificate object")
        .insert("future_authority".to_owned(), serde_json::json!(true));
    assert!(serde_json::from_value::<InvariantModelProgramPropertyCertificate>(unknown).is_err());
}

fn imported_rebinding_error(
    result: Result<InvariantModelProgramPropertyCertificate, ModelProgramRefinementError>,
    declaration: &str,
) {
    let error = result.expect_err("later source units cannot rebind an earlier declaration");
    let ModelProgramRefinementError::Clean(error) = error else {
        panic!("expected an actual Clean source-unit refusal, got {error}");
    };
    let detail = error.to_string();
    assert!(detail.contains(declaration), "{detail}");
    assert!(detail.contains("imported module"), "{detail}");
}

#[test]
fn support_and_property_keep_their_own_attributes_but_cannot_rebind_imports() {
    // Both positive units apply implemented_by and extern to their own declarations.
    // A blanket attribute refusal would fail this accepted control.
    certificate();

    let support_attack = format!(
        "{SUPPORT_SOURCE}\n\
         def supportAttack (n : Nat) : Nat := n + 3\n\
         attribute [implemented_by supportAttack] PropertyIsolationFixture.refinementSlow\n"
    );
    imported_rebinding_error(
        certify(&support_attack, PROPERTY_SOURCE),
        "PropertyIsolationFixture.refinementSlow",
    );

    let property_attack = format!(
        "{PROPERTY_SOURCE}\n\
         def propertyAttack (n : Nat) : Nat := n + 3\n\
         attribute [implemented_by propertyAttack] PropertyIsolationFixture.supportSlow\n"
    );
    imported_rebinding_error(
        certify(SUPPORT_SOURCE, &property_attack),
        "PropertyIsolationFixture.supportSlow",
    );

    let support_extern = format!(
        "{SUPPORT_SOURCE}\n\
         attribute [extern \"property_isolation_attack\"] PropertyIsolationFixture.refinementSlow\n"
    );
    imported_rebinding_error(
        certify(&support_extern, PROPERTY_SOURCE),
        "PropertyIsolationFixture.refinementSlow",
    );

    let property_extern = format!(
        "{PROPERTY_SOURCE}\n\
         attribute [extern \"property_isolation_attack\"] PropertyIsolationFixture.supportForeign\n"
    );
    imported_rebinding_error(
        certify(SUPPORT_SOURCE, &property_extern),
        "PropertyIsolationFixture.supportForeign",
    );
}

#[test]
fn eof_closed_namespaces_cannot_capture_the_next_property_unit_or_its_goal() {
    certificate();
    // Lean closes a namespace at EOF. Parsing the support and property as
    // independent files must retain that legal syntax without letting the
    // support namespace capture the next unit's declarations.
    let support = format!("{SUPPORT_SOURCE}\nnamespace SupportScope\ndef marker : Nat := 0\n");
    let property = format!("{PROPERTY_SOURCE}\nnamespace PropertyScope\ndef marker : Nat := 0\n");
    let accepted = certify(&support, &property)
        .expect("EOF closes each unit's namespace before the next unit starts");
    assert_eq!(accepted.property.theorem, PROPERTY_NAME);

    // A same-spelled theorem in a nested EOF-closed namespace is not the
    // caller's requested root goal, even when its proof is otherwise valid.
    let shadow =
        format!("namespace CaptureScope\nopen _root_.PropertyIsolationFixture\n{PROPERTY_SOURCE}");
    let error = certify(SUPPORT_SOURCE, &shadow)
        .expect_err("a nested theorem cannot stand in for the requested root declaration");
    assert!(
        matches!(&error, ModelProgramRefinementError::Clean(
            CleanTemporalCertificateError::MissingTheorem(name)
        ) if name == PROPERTY_NAME),
        "{error}",
    );
}
