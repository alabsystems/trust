//! Fixed resource permission policies composed with actual compiler-emitted semantics.
use std::error::Error;
use std::path::Path;

#[path = "refinement/evidence.rs"]
mod evidence;

use trust_spec_temporal::{
    CleanAutomaticScalarProof, InvariantModelProgramPropertyCertificate,
    certify_invariant_model_program_property, recheck_automatic_clean_scalar_model,
    recheck_invariant_model_program_property,
};

use super::{Case, Suite, failure, invocation};

const MODEL: &str = "SourcePermission.Model";
const INVARIANT: &str = "SourcePermission.I";
const PROJECTION: &str = "SourcePermission.Projection";
const REFINEMENT: &str = "SourcePermission.refines";
const PROPERTY: &str = "SourcePermission.checked";
const SAFETY: &str = "TrustGeneratedR5AutomaticScalar.AppliedProof";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum FixedPolicy {
    Custody,
    Attribution,
    WorkerPause,
    SourceClose,
}

impl FixedPolicy {
    pub(super) fn validate(self, suite: &Suite) -> Result<(), Box<dyn Error>> {
        match self {
            Self::Custody => validate(suite),
            Self::SourceClose => {
                super::validate(suite)?;
                if suite.function != "may_close_source_descriptions"
                    || suite.mutation_from != "!handler_active && "
                    || !suite.mutation_to.is_empty()
                    || suite.cases.iter().any(|case| {
                        case.arguments.len() != 2 || {
                            let allowed = !case.arguments[0] && case.arguments[1];
                            case.permitted != allowed || case.expected != allowed
                        }
                    })
                {
                    return Err(failure(
                        "source close requires the exact inactive-handler and original-root policy",
                    ));
                }
                Ok(())
            }
            Self::WorkerPause => {
                super::validate(suite)?;
                if suite.function != "may_pause_extra_workers"
                    || suite.mutation_from != " && credits_zero"
                    || !suite.mutation_to.is_empty()
                    || suite.cases.iter().any(|case| {
                        case.arguments.len() != 3 || {
                            let allowed = case.arguments.iter().all(|value| *value);
                            case.permitted != allowed || case.expected != allowed
                        }
                    })
                {
                    return Err(failure(
                        "worker pause requires the exact three-input eligibility policy",
                    ));
                }
                Ok(())
            }
            Self::Attribution => {
                super::validate(suite)?;
                if suite.function != "may_attribute_group"
                    || suite.cases.iter().any(|case| {
                        case.arguments.len() != 2 || {
                            let allowed = !case.arguments[0] && !case.arguments[1];
                            case.permitted != allowed || case.expected != allowed
                        }
                    })
                {
                    return Err(failure(
                        "attribution refinement requires the exact two-input sampling policy",
                    ));
                }
                Ok(())
            }
        }
    }

    fn request_schema(self) -> &'static str {
        match self {
            Self::Custody => "trust.custody-proof-request/v1",
            Self::Attribution => "trust.attribution-proof-request/v1",
            Self::WorkerPause => "trust.worker-pause-proof-request/v1",
            Self::SourceClose => "trust.source-close-proof-request/v1",
        }
    }

    fn attempt_schema(self) -> &'static str {
        match self {
            Self::Custody => "trust.custody-proof-attempt/v1",
            Self::Attribution => "trust.attribution-proof-attempt/v1",
            Self::WorkerPause => "trust.worker-pause-proof-attempt/v1",
            Self::SourceClose => "trust.source-close-proof-attempt/v1",
        }
    }
}

pub(super) fn validate(suite: &Suite) -> Result<(), Box<dyn Error>> {
    if suite.function != "may_release"
        || suite.cases.iter().any(|case| {
            case.arguments.len() != 3 || {
                let allowed = case.arguments[0] || (case.arguments[1] && case.arguments[2]);
                case.permitted != allowed || case.expected != allowed
            }
        })
    {
        return Err(failure("custody refinement requires the exact three-input release policy"));
    }
    Ok(())
}

pub(super) struct CheckedModel<'a> {
    proof: &'a CleanAutomaticScalarProof,
    source: String,
    policy: FixedPolicy,
}

impl<'a> CheckedModel<'a> {
    pub(super) fn new(
        suite: &Suite,
        proof: &'a CleanAutomaticScalarProof,
        policy: FixedPolicy,
    ) -> Result<Self, Box<dyn Error>> {
        policy.validate(suite)?;
        let source = super::model(suite);
        recheck_automatic_clean_scalar_model(proof, &source)?;
        if proof.applied_proof.proof_definition != SAFETY
            || proof.applied_proof.binding.model_definition != "SourceQualification.Model"
        {
            return Err(failure("unexpected scalar safety proof binding"));
        }
        Ok(Self {
            proof,
            policy,
            source: format!(
                "{source}\nnamespace SourcePermission\ndef Model : _root_.Trust.Temporal.FiniteModel.Model := _root_.SourceQualification.Model.asModel\nend SourcePermission\n"
            ),
        })
    }
}

#[derive(Clone, Copy)]
pub(super) enum ProjectionMode {
    Actual,
    Constant,
    Expected,
}

pub(super) fn is_named_proof_refusal(error: &(dyn Error + 'static), declaration: &str) -> bool {
    matches!(
        error.downcast_ref::<trust_spec_temporal::ModelProgramRefinementError>(),
        Some(trust_spec_temporal::ModelProgramRefinementError::Clean(
            trust_spec_temporal::CleanTemporalCertificateError::Elaborate { detail, .. }
        )) if detail.strip_prefix(&format!("declaration `{declaration}` failed: "))
            .is_some_and(|cause| cause.contains("TypeMismatch {"))
    )
}

fn member(index: usize) -> String {
    (0..index).fold("Member.head _".to_owned(), |tail, _| format!("Member.tail _ _ ({tail})"))
}

fn source(
    suite: &Suite,
    case: &Case,
    index: usize,
    observed: bool,
    mode: ProjectionMode,
) -> String {
    let actual = match mode {
        ProjectionMode::Actual => "if b then 1 else 0".to_owned(),
        ProjectionMode::Constant => "0".to_owned(),
        ProjectionMode::Expected => u8::from(case.expected).to_string(),
    };
    format!(
        r#"
namespace SourcePermission
open Trust.Temporal.FiniteModel

def Values : IRList IRScalar := IRList.cons IRScalar (IRScalar.bool_ {observed}) (IRList.nil IRScalar)
def Outcome : IROutcome := IROutcome.ret Values
theorem initial_returns :
  ir_run {fuel} _root_.Trust.LiteralRefinement.Program _root_.Trust.LiteralRefinement.Initial = Outcome := rfl
def I (q : IRConfig) : Prop := ∃ f : Nat, ir_run f _root_.Trust.LiteralRefinement.Program q = Outcome

def NotReturned (outcome : IROutcome) : Prop :=
  match outcome with
  | IROutcome.ret _ => False
  | _ => True
theorem fuelOutNotReturn (same : IROutcome.fuel_out = Outcome) : False :=
  Eq.mp (congrArg NotReturned same) True.intro
theorem runHalted (outcome : IROutcome) (fuel : Nat) :
    ir_run fuel _root_.Trust.LiteralRefinement.Program (IRConfig.halted outcome) = outcome :=
  Nat.rec (motive := fun n : Nat =>
    ir_run n _root_.Trust.LiteralRefinement.Program (IRConfig.halted outcome) = outcome)
    rfl (fun _ _ => rfl) fuel

theorem initial_I (q : IRConfig) (h : _root_.Trust.LiteralRefinement.Model.init q) : I q :=
  Eq.mpr (congrArg I h) (Exists.intro {fuel} initial_returns)

theorem preserve (before after : IRConfig) (previous : I before)
    (step : _root_.Trust.LiteralRefinement.Model.next before after) : I after := by
  cases before with
  | halted outcome => exact False.elim step
  | running machine =>
    exact Exists.elim previous (fun fuel h =>
      let fuelProof : ∀ f : Nat,
          ir_run f _root_.Trust.LiteralRefinement.Program (IRConfig.running machine) = Outcome → I after :=
        Nat.rec
          (fun zero => False.elim (fuelOutNotReturn zero))
          (fun n _ successful => Exists.intro n
            (Eq.mpr (congrArg (fun q => ir_run n _root_.Trust.LiteralRefinement.Program q = Outcome) step) successful))
      fuelProof fuel h)

def Zero : State := State.mk (fun _ => 0) (fun _ _ => false)
def Observation (released permitted : Nat) : State :=
  State.mk (fun name => if name = "released" then released else if name = "permitted" then permitted else 0)
    (fun _ _ => false)
def Projection (q : IRConfig) : State :=
  match q with
  | IRConfig.running _ => Zero
  | IRConfig.halted outcome =>
    match outcome with
    | IROutcome.ret values =>
      match values with
      | IRList.cons (IRScalar.bool_ b) IRList.nil => Observation ({actual}) {permission}
      | _ => Zero
    | _ => Zero

def Advance (q : IRConfig) : IRConfig :=
  match q with
  | IRConfig.running machine => ir_step _root_.Trust.LiteralRefinement.Program machine
  | IRConfig.halted outcome => IRConfig.halted outcome
def Trace : Nat → IRConfig :=
  Nat.rec _root_.Trust.LiteralRefinement.Initial (fun _ previous => Advance previous)
theorem advanceAllowed (q : IRConfig) :
    _root_.Trust.LiteralRefinement.Model.next q (Advance q) ∨ Advance q = q := by
  cases q with
  | running machine => exact Or.inl rfl
  | halted outcome => exact Or.inr rfl
theorem traceRuns : _root_.Trust.Temporal.Runs _root_.Trust.LiteralRefinement.Model Trace :=
  And.intro rfl (fun n => advanceAllowed (Trace n))

theorem project_return_exact (b : Bool) :
  (Projection (IRConfig.halted (IROutcome.ret
    (IRList.cons IRScalar (IRScalar.bool_ b) (IRList.nil IRScalar))))).scalar "released" =
      (if b then 1 else 0) := by cases b <;> rfl

def Released : StateVar := StateVar.mk "released" 0
def Permitted : StateVar := StateVar.mk "permitted" 0
theorem releasedMember : Member Released
    (_root_.Trust.Temporal.FiniteModel.Model.variables _root_.SourcePermission.Model) := Member.head _
theorem permittedMember : Member Permitted
    (_root_.Trust.Temporal.FiniteModel.Model.variables _root_.SourcePermission.Model) := Member.tail _ _ (Member.head _)
theorem declaredReleased : DeclaresScalar Model "released" := Exists.intro Released ⟨releasedMember, rfl⟩
theorem declaredPermitted : DeclaresScalar Model "permitted" := Exists.intro Permitted ⟨permittedMember, rfl⟩

theorem observationCanonical (r p : Nat) : CanonicalState Model (Observation r p) :=
  And.intro
    (fun name absent =>
      let notR : ¬ (name = "released") := fun same =>
        absent (Exists.intro Released ⟨releasedMember, Eq.symm same⟩)
      let notP : ¬ (name = "permitted") := fun same =>
        absent (Exists.intro Permitted ⟨permittedMember, Eq.symm same⟩)
      Eq.trans (if_neg notR) (if_neg notP))
    (fun _ _ _ => rfl)

theorem initialZero : Initial Model Zero :=
  And.intro (And.intro (fun _ _ => rfl) (fun _ _ _ => rfl))
    (And.intro
      (fun entry found => everyMember (fun x : StateVar => Zero.scalar x.name = x.init)
        entry (_root_.Trust.Temporal.FiniteModel.Model.variables _root_.SourcePermission.Model)
          ⟨rfl, ⟨rfl, True.intro⟩⟩ found)
      (fun entry found => False.elim (memberNilFalse found)))

def CaseAction : Action := Action.mk "Case{index}" Guard.always
  [Update.mk "released" (ScalarExpr.int {expected_bit}), Update.mk "permitted" (ScalarExpr.int {permission})]
def Destination : State := Observation {observed_bit} {permission}
def ScalarActionClause (entry : StateVar) : Prop :=
  (∃ update : Update, Member update CaseAction.updates ∧ update.var = entry.name ∧
    Evaluates Model [] Zero update.value (Value.nat (Destination.scalar entry.name))) ∨
  (NoUpdate CaseAction entry.name ∧ Destination.scalar entry.name = Zero.scalar entry.name)
theorem returnAction : Next Model Zero Destination :=
  Exists.intro CaseAction (And.intro ({action_member})
    (And.intro True.intro
      (And.intro (observationCanonical {observed_bit} {permission})
        (And.intro
          (fun entry found => @everyMember StateVar ScalarActionClause
            entry (_root_.Trust.Temporal.FiniteModel.Model.variables _root_.SourcePermission.Model)
            ⟨Or.inl (Exists.intro (Update.mk "released" (ScalarExpr.int {expected_bit}))
                ⟨Member.head _, ⟨rfl, Evaluates.int {expected_bit}⟩⟩),
             ⟨Or.inl (Exists.intro (Update.mk "permitted" (ScalarExpr.int {permission}))
                ⟨Member.tail _ _ (Member.head _), ⟨rfl, Evaluates.int {permission}⟩⟩), True.intro⟩⟩ found)
          (fun entry found => False.elim (memberNilFalse found))))))

theorem haltedOutcome (outcome : IROutcome) (h : I (IRConfig.halted outcome)) : outcome = Outcome :=
  Exists.elim h (fun fuel successful =>
    Eq.trans (Eq.symm (runHalted outcome fuel)) successful)

theorem refines : _root_.Trust.Temporal.InvariantForwardRefinement
    _root_.Trust.LiteralRefinement.Model (StateMachine Model) Projection I := by
  refine ⟨initial_I, preserve, ?_, ?_⟩
  · intro state initial
    exact Eq.mpr (congrArg (fun q => Initial Model (Projection q)) initial) initialZero
  · intro before after previous step
    cases before with
    | halted outcome => exact False.elim step
    | running machine =>
      cases after with
      | running nextMachine => exact Or.inr rfl
      | halted outcome =>
        have same : outcome = Outcome := haltedOutcome outcome (preserve (IRConfig.running machine) (IRConfig.halted outcome) previous step)
        exact Or.inl (Eq.mpr (congrArg (fun o => Next Model Zero (Projection (IRConfig.halted o))) same) returnAction)

end SourcePermission
"#,
        fuel = suite.fuel,
        permission = u8::from(case.permitted),
        expected_bit = u8::from(case.expected),
        observed_bit = u8::from(observed),
        action_member = member(index)
    )
}

fn closing(case: &Case, fuel: u64) -> String {
    let permission = if case.permitted {
        "fun _ _ _ _ => rfl".to_owned()
    } else {
        r#"by
  intro behavior runs index returned
  have actual := (sourceSafe behavior runs) index PermissionInvariant (Member.head _)
  have atReturn : InvariantHolds Model PermissionInvariant
      (Projection (IRConfig.halted (IROutcome.ret
        (IRList.cons IRScalar (IRScalar.bool_ true) (IRList.nil IRScalar))))) :=
    Eq.mp (congrArg (fun q => InvariantHolds Model PermissionInvariant (Projection q)) returned) actual
  let state := Projection (IRConfig.halted (IROutcome.ret
    (IRList.cons IRScalar (IRScalar.bool_ true) (IRList.nil IRScalar))))
  have releasedExact := exactScalarVar Model state "released" 1 declaredReleased
    (project_return_exact true) (noFunction "released")
  have permittedExact := exactScalarVar Model state "permitted" 0 declaredPermitted rfl
    (noFunction "permitted")
  exact False.elim (falseOfExactFalseEvaluatesTrue Model state PermissionInvariant.value
    (exactScalarLeFalse Model state (ScalarExpr.var "released") (ScalarExpr.var "permitted")
      1 0 releasedExact permittedExact (by decide)) atReturn)
"#.to_owned()
    };
    let witness = if case.expected {
        format!(
            r#"
theorem changes :
    (_root_.Trust.Temporal.Runs _root_.Trust.LiteralRefinement.Model Trace) ∧
    ((Projection _root_.Trust.LiteralRefinement.Initial).scalar "released" = 0 ∧
    (Projection (Trace {fuel})).scalar "released" = 1) := ⟨traceRuns, ⟨rfl, rfl⟩⟩
theorem checked :
    (_root_.Trust.Temporal.Satisfies _root_.Trust.LiteralRefinement.Model
      (_root_.Trust.Temporal.Pullback Projection (SafetyFormula Model))) ∧
    ((∀ behavior : _root_.Trust.Temporal.Behavior IRConfig,
      _root_.Trust.Temporal.Runs _root_.Trust.LiteralRefinement.Model behavior →
      ∀ index : Nat, behavior index = IRConfig.halted (IROutcome.ret
        (IRList.cons IRScalar (IRScalar.bool_ true) (IRList.nil IRScalar))) → true = true) ∧
    ((_root_.Trust.Temporal.Runs _root_.Trust.LiteralRefinement.Model Trace) ∧
     ((Projection _root_.Trust.LiteralRefinement.Initial).scalar "released" = 0 ∧
      (Projection (Trace {fuel})).scalar "released" = 1))) := ⟨sourceSafe, ⟨permission, changes⟩⟩
"#
        )
    } else {
        r#"
theorem checked :
    (_root_.Trust.Temporal.Satisfies _root_.Trust.LiteralRefinement.Model
      (_root_.Trust.Temporal.Pullback Projection (SafetyFormula Model))) ∧
    (∀ behavior : _root_.Trust.Temporal.Behavior IRConfig,
    _root_.Trust.Temporal.Runs _root_.Trust.LiteralRefinement.Model behavior →
    ∀ index : Nat, behavior index = IRConfig.halted (IROutcome.ret
      (IRList.cons IRScalar (IRScalar.bool_ true) (IRList.nil IRScalar))) → false = true) := ⟨sourceSafe, permission⟩
"#.to_owned()
    };
    format!(
        r#"
namespace SourcePermission
open Trust.Temporal.FiniteModel
theorem modelSafe : SafetyClaim Model := _root_.{SAFETY}
theorem sourceSafe : _root_.Trust.Temporal.Satisfies _root_.Trust.LiteralRefinement.Model
    (_root_.Trust.Temporal.Pullback Projection (SafetyFormula Model)) :=
  _root_.Trust.Temporal.invariantForwardRefinementSatisfies
    _root_.Trust.LiteralRefinement.Model (StateMachine Model) Projection I refines (SafetyFormula Model) modelSafe
def PermissionInvariant : Invariant := Invariant.mk "PermissionBeforeRelease"
  (ScalarExpr.le (ScalarExpr.var "released") (ScalarExpr.var "permitted"))
theorem noFunction (name range : String) (h : FunctionRange Model name range) : False :=
  Exists.elim h (fun entry facts => memberNilFalse facts.1)
theorem permission : ∀ behavior : _root_.Trust.Temporal.Behavior IRConfig,
    _root_.Trust.Temporal.Runs _root_.Trust.LiteralRefinement.Model behavior →
    ∀ index : Nat, behavior index = IRConfig.halted (IROutcome.ret
      (IRList.cons IRScalar (IRScalar.bool_ true) (IRList.nil IRScalar))) → {permitted} = true :=
  {permission}
{witness}
end SourcePermission
"#,
        permitted = case.permitted
    )
}

struct ProofRequest {
    invocation: trust_spec_temporal::literal_refinement::LiteralInvocation,
    refinement_source: String,
    property_source: String,
}

impl ProofRequest {
    fn new(suite: &Suite, index: usize, observed: bool, mode: ProjectionMode) -> Self {
        let case = &suite.cases[index];
        Self {
            invocation: invocation(case),
            refinement_source: source(suite, case, index, observed, mode),
            property_source: closing(case, suite.fuel),
        }
    }

    fn capture(
        &self,
        directory: &Path,
        bytes: &[u8],
        id: u32,
        index: usize,
        observed: bool,
        model: &CheckedModel<'_>,
    ) -> Result<(), Box<dyn Error>> {
        let request = serde_json::json!({
        "schema": model.policy.request_schema(),
        "api_schema": trust_spec_temporal::INVARIANT_MODEL_PROGRAM_PROPERTY_SCHEMA_V1,
        "module_sha256": super::sha256(bytes),
        "function_id": id,
        "invocation": self.invocation,
        "case_index": index,
        "observed": observed,
        "model_source": model.source,
        "model_definition": MODEL,
        "refinement_source": self.refinement_source,
        "invariant_definition": INVARIANT,
        "projection_definition": PROJECTION,
        "refinement_theorem": REFINEMENT,
        "support_source": model.proof.generated_suffix,
        "property_source": self.property_source,
        "property_theorem": PROPERTY,
        });
        evidence::begin(directory, bytes, &request, model.proof)
    }

    fn replay(
        &self,
        certificate: &InvariantModelProgramPropertyCertificate,
        bytes: &[u8],
        id: u32,
        model: &CheckedModel<'_>,
    ) -> Result<(), trust_spec_temporal::ModelProgramRefinementError> {
        recheck_invariant_model_program_property(
            certificate,
            bytes,
            id,
            &self.invocation,
            &model.source,
            MODEL,
            &self.refinement_source,
            INVARIANT,
            PROJECTION,
            REFINEMENT,
            &model.proof.generated_suffix,
            &self.property_source,
            PROPERTY,
        )
    }
}

pub(super) fn certify(
    bytes: &[u8],
    id: u32,
    suite: &Suite,
    index: usize,
    observed: bool,
    model: &CheckedModel<'_>,
    mode: ProjectionMode,
    evidence_directory: &Path,
) -> Result<InvariantModelProgramPropertyCertificate, Box<dyn Error>> {
    let request = ProofRequest::new(suite, index, observed, mode);
    request.capture(evidence_directory, bytes, id, index, observed, model)?;
    match certify_invariant_model_program_property(
        bytes,
        id,
        &request.invocation,
        &model.source,
        MODEL,
        &request.refinement_source,
        INVARIANT,
        PROJECTION,
        REFINEMENT,
        &model.proof.generated_suffix,
        &request.property_source,
        PROPERTY,
    ) {
        Ok(certificate) => {
            evidence::accepted(evidence_directory, &certificate, model.policy.attempt_schema())?;
            Ok(certificate)
        }
        Err(error) => {
            evidence::rejected(evidence_directory, &error, model.policy.attempt_schema())?;
            Err(Box::new(error))
        }
    }
}

pub(super) fn replay(
    certificate: &InvariantModelProgramPropertyCertificate,
    bytes: &[u8],
    id: u32,
    suite: &Suite,
    index: usize,
    model: &CheckedModel<'_>,
) -> Result<(), Box<dyn Error>> {
    let request =
        ProofRequest::new(suite, index, suite.cases[index].expected, ProjectionMode::Actual);
    Ok(request.replay(certificate, bytes, id, model)?)
}

/// A candidate is input to the existing checker, never an accepted prior verdict.
pub(super) fn replay_candidate(
    candidate: &[u8],
    bytes: &[u8],
    id: u32,
    suite: &Suite,
    index: usize,
    model: &CheckedModel<'_>,
    evidence_directory: &Path,
) -> Result<InvariantModelProgramPropertyCertificate, Box<dyn Error>> {
    let observed = suite.cases[index].expected;
    let request = ProofRequest::new(suite, index, observed, ProjectionMode::Actual);
    request.capture(evidence_directory, bytes, id, index, observed, model)?;
    super::reuse::write_new(&evidence_directory.join("candidate.json"), candidate)?;
    let certificate = match serde_json::from_slice(candidate) {
        Ok(certificate) => certificate,
        Err(error) => {
            evidence::decode_rejected(evidence_directory, &error, model.policy.attempt_schema())?;
            return Err(Box::new(error));
        }
    };
    match request.replay(&certificate, bytes, id, model) {
        Ok(()) => {
            evidence::replayed(evidence_directory, model.policy.attempt_schema())?;
            Ok(certificate)
        }
        Err(error) => {
            evidence::rejected(evidence_directory, &error, model.policy.attempt_schema())?;
            Err(Box::new(error))
        }
    }
}

pub(super) fn splice_controls(
    certificate: &InvariantModelProgramPropertyCertificate,
    bytes: &[u8],
    id: u32,
    suite: &Suite,
    model: &CheckedModel<'_>,
) -> Result<usize, Box<dyn Error>> {
    use trust_spec_temporal::literal_refinement::{LiteralRefinementError, LiteralScalar};
    use trust_spec_temporal::model_program_refinement::ModelProgramRefinementError as E;
    let mut controls = Vec::new();
    let mut changed = certificate.clone();
    changed.support_source.push_str("\n-- spliced holds source\n");
    controls.push((changed, 0));
    changed = certificate.clone();
    changed.property_source.push_str("\n-- spliced property\n");
    controls.push((changed, 1));
    changed = certificate.clone();
    changed.refinement.projection_definition = "SourcePermission.OtherProjection".to_owned();
    controls.push((changed, 2));
    changed = certificate.clone();
    changed.refinement.model.clean_source.push_str("\n-- spliced model\n");
    controls.push((changed, 3));
    changed = certificate.clone();
    if let LiteralScalar::Bool { value } = &mut changed.refinement.literal.invocation.arguments[0] {
        *value = !*value;
    }
    controls.push((changed, 4));
    changed = certificate.clone();
    changed.refinement.literal.module_bytes.push(0);
    controls.push((changed, 5));
    changed = certificate.clone();
    changed.property.proof_term.clear();
    controls.push((changed, 6));
    for (changed, kind) in controls {
        let error = match replay(&changed, bytes, id, suite, 0, model) {
            Ok(()) => {
                return Err(failure("fixed source-policy replay accepted a spliced artifact"));
            }
            Err(error) => error,
        };
        let expected = match (kind, error.downcast_ref::<E>()) {
            (0, Some(E::SupportSourceMismatch))
            | (1, Some(E::PropertySourceMismatch))
            | (2, Some(E::ProjectionDefinitionMismatch))
            | (3, Some(E::ModelSourceMismatch))
            | (4, Some(E::Literal(LiteralRefinementError::InvocationMismatch)))
            | (5, Some(E::Literal(LiteralRefinementError::ModuleMismatch)))
            | (6, Some(E::ArtifactMismatch { field: "property theorem or proof", .. })) => true,
            _ => false,
        };
        if !expected {
            return Err(failure(format!("unrelated splice refusal: {error}")));
        }
    }
    let mut changed = (*model.proof).clone();
    changed.applied_proof.canonical_inhabitant.clear();
    match CheckedModel::new(suite, &changed, model.policy) {
        Ok(_) => {
            return Err(failure("fixed source policy accepted a spliced model safety inhabitant"));
        }
        Err(error)
            if matches!(
                error.downcast_ref::<trust_spec_temporal::CleanScalarModelError>(),
                Some(trust_spec_temporal::CleanScalarModelError::ArtifactMismatch(_))
            ) => {}
        Err(error) => return Err(failure(format!("unrelated safety-proof refusal: {error}"))),
    }
    Ok(8)
}

#[cfg(test)]
mod evidence_tests {
    use trust_spec_temporal::{CleanTemporalCertificateError, ModelProgramRefinementError};

    use super::is_named_proof_refusal;

    #[test]
    fn an_io_error_named_like_the_target_is_not_a_proof_control() {
        const TARGET: &str = "SourcePermission.returnAction";
        let io = std::io::Error::other(format!("cannot write {TARGET}"));
        assert!(!is_named_proof_refusal(&io, TARGET));
        let semantic = ModelProgramRefinementError::Clean(
            CleanTemporalCertificateError::Elaborate {
                unit: "authored model/program refinement",
                detail: format!(
                    "declaration `{TARGET}` failed: TypeMismatch {{ expected: false, actual: true }}"
                ),
            },
        );
        assert!(is_named_proof_refusal(&semantic, TARGET));
        assert!(!is_named_proof_refusal(&semantic, "SourcePermission.unrelated"));
        let missing_identifier =
            ModelProgramRefinementError::Clean(CleanTemporalCertificateError::Elaborate {
                unit: "authored model/program refinement",
                detail: format!("declaration `{TARGET}` failed: UnknownIdent(\"missing\")"),
            });
        assert!(!is_named_proof_refusal(&missing_identifier, TARGET));
        let echoed_target =
            ModelProgramRefinementError::Clean(CleanTemporalCertificateError::Elaborate {
                unit: "authored model/program refinement",
                detail: format!("declaration `Other` failed: TypeMismatch {{ actual: {TARGET} }}"),
            });
        assert!(!is_named_proof_refusal(&echoed_target, TARGET));
    }

    #[test]
    fn malformed_candidate_is_captured_before_decode_and_cannot_count_as_replay() {
        let suite: super::Suite =
            serde_json::from_str(include_str!("../cleanup_permission.json")).unwrap();
        let model_source = super::super::model(&suite);
        let proof = trust_spec_temporal::certify_automatic_clean_scalar_model(
            &model_source,
            "SourceQualification.Model",
        )
        .unwrap();
        let model = super::CheckedModel::new(&suite, &proof, super::FixedPolicy::Custody).unwrap();
        let dir = tempfile::tempdir().unwrap();
        let attempt = dir.path().join("attempt");
        let candidate = b"not a property certificate";
        // Deliberately not IR: a malformed candidate must fail before that
        // endpoint is consulted. These are capture/codec fixtures only.
        let error = super::replay_candidate(candidate, b"module", 0, &suite, 0, &model, &attempt)
            .unwrap_err();
        assert!(error.downcast_ref::<serde_json::Error>().is_some());
        assert_eq!(std::fs::read(attempt.join("candidate.json")).unwrap(), candidate);
        assert_eq!(std::fs::read(attempt.join("module.trust-ir.bin")).unwrap(), b"module");
        let request: serde_json::Value =
            serde_json::from_slice(&std::fs::read(attempt.join("request.json")).unwrap()).unwrap();
        assert_eq!(
            request["refinement_source"],
            super::source(&suite, &suite.cases[0], 0, false, super::ProjectionMode::Actual)
        );
        let outcome: serde_json::Value =
            serde_json::from_slice(&std::fs::read(attempt.join("outcome.json")).unwrap()).unwrap();
        assert_eq!(outcome["outcome"], "candidate-decode-rejected");
        assert!(!attempt.join("certificate.json").exists());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fixed_source_close_policy_requires_complete_table_and_the_active_handler_mutant() {
        let original: Suite =
            serde_json::from_str(include_str!("../source_close_permission.json")).unwrap();
        FixedPolicy::SourceClose.validate(&original).unwrap();
        for index in 0..original.cases.len() {
            let mut changed = original.clone();
            changed.cases[index].expected = !changed.cases[index].expected;
            changed.cases[index].permitted = changed.cases[index].expected;
            assert!(FixedPolicy::SourceClose.validate(&changed).is_err());
        }
        let mut changed = original.clone();
        changed.cases.pop();
        assert!(FixedPolicy::SourceClose.validate(&changed).is_err());
        let mut changed = original.clone();
        changed.cases[3] = changed.cases[2].clone();
        assert!(FixedPolicy::SourceClose.validate(&changed).is_err());
        let mut changed = original.clone();
        changed.function = "may_release".into();
        assert!(FixedPolicy::SourceClose.validate(&changed).is_err());
        assert!(FixedPolicy::Custody.validate(&original).is_err());
        assert!(FixedPolicy::Attribution.validate(&original).is_err());
        assert!(FixedPolicy::WorkerPause.validate(&original).is_err());
        for (from, to) in
            [(" && closed_root_matches", ""), ("!handler_active && ", "handler_active || ")]
        {
            let mut changed = original.clone();
            changed.mutation_from = from.into();
            changed.mutation_to = to.into();
            assert!(FixedPolicy::SourceClose.validate(&changed).is_err());
        }
    }

    #[test]
    fn fixed_worker_pause_policy_requires_all_inputs_and_complete_equivalence_table() {
        let original: Suite =
            serde_json::from_str(include_str!("../worker_pause_permission.json")).unwrap();
        FixedPolicy::WorkerPause.validate(&original).unwrap();
        for index in 0..original.cases.len() {
            let mut changed = original.clone();
            changed.cases[index].expected = !changed.cases[index].expected;
            changed.cases[index].permitted = changed.cases[index].expected;
            assert!(FixedPolicy::WorkerPause.validate(&changed).is_err());
        }
        let mut changed = original.clone();
        changed.cases.pop();
        assert!(FixedPolicy::WorkerPause.validate(&changed).is_err());
        let mut changed = original.clone();
        changed.function = "may_release".into();
        assert!(FixedPolicy::WorkerPause.validate(&changed).is_err());
        assert!(FixedPolicy::Custody.validate(&original).is_err());
        assert!(FixedPolicy::Attribution.validate(&original).is_err());
        for (from, to) in [(" && acquiring_zero", ""), (" && credits_zero", " || credits_zero")] {
            let mut changed = original.clone();
            changed.mutation_from = from.into();
            changed.mutation_to = to.into();
            assert!(FixedPolicy::WorkerPause.validate(&changed).is_err());
        }
    }

    #[test]
    fn fixed_attribution_policy_refuses_vacuity_wrong_binding_and_incomplete_inputs() {
        let original: Suite =
            serde_json::from_str(include_str!("../group_attribution_permission.json")).unwrap();
        FixedPolicy::Attribution.validate(&original).unwrap();
        assert!(FixedPolicy::Custody.validate(&original).is_err());
        for index in 1..original.cases.len() {
            let mut changed = original.clone();
            changed.cases[index].expected = true;
            changed.cases[index].permitted = true;
            super::super::validate(&changed).unwrap();
            assert!(FixedPolicy::Attribution.validate(&changed).is_err());
        }
        let mut changed = original.clone();
        changed.function = "may_release".into();
        assert!(FixedPolicy::Attribution.validate(&changed).is_err());
        let mut changed = original.clone();
        changed.cases.pop();
        assert!(FixedPolicy::Attribution.validate(&changed).is_err());
        let mut changed = original.clone();
        changed.cases[1] = changed.cases[0].clone();
        assert!(FixedPolicy::Attribution.validate(&changed).is_err());
        let mut changed = original.clone();
        for case in &mut changed.cases {
            case.arguments.push(false);
        }
        assert!(FixedPolicy::Attribution.validate(&changed).is_err());
    }

    #[test]
    fn fixed_custody_policy_rejects_an_all_permitted_or_changed_input_table() {
        let mut suite: Suite =
            serde_json::from_str(include_str!("../cleanup_permission.json")).unwrap();
        validate(&suite).unwrap();
        for case in &mut suite.cases {
            case.permitted = true;
        }
        super::super::validate(&suite)
            .expect("the legacy authored-table lane permits broader claims");
        assert!(validate(&suite).is_err(), "fixed custody permission must not become vacuous");
        let mut suite: Suite =
            serde_json::from_str(include_str!("../cleanup_permission.json")).unwrap();
        suite.cases[0].arguments.pop();
        assert!(validate(&suite).is_err());
    }
}
