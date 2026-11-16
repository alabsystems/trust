//! Proof-carrying refinement from exact program semantics to an authored model.
//!
//! [`crate::literal_refinement`] constructs the concrete transition system
//! directly from canonical TrustIR bytes.  This lane composes that exact system
//! with a kernel-elaborated [`crate::CleanFiniteModelArtifact`] and an authored
//! Clean forward-simulation proof.  The fixed wrapper forces the proof to name
//! the exact program, exact model, and exact projection, then derives both run
//! preservation and temporal-property transport in the Clean kernel.
//!
//! Replay rebuilds an isolated EvalIR + temporal + finite-model environment,
//! rechecks both child artifacts, parses every component as an isolated source
//! unit, regenerates the fixed wrapper, compares theorem types and proof terms
//! byte-for-byte, and asks the kernel to check the stored terms again.  A model
//! with no such proof remains a claim about that model only; it gains no program
//! authority.

use std::fmt;

use clean_elab::FileContext;
use clean_kernel::env::Environment;
use clean_kernel::expr::Expr;
use clean_kernel::name::Name;
use clean_kernel::tc::TypeChecker;

use crate::clean_model_lane::{
    CleanFiniteModel, CleanFiniteModelArtifact, CleanScalarModelError, FINITE_MODEL_PRELUDE,
    clean_finite_models_equal_stack_safe, decode_clean_finite_model_from_environment,
    extract_clean_finite_model, recheck_clean_finite_model_artifact,
};
use crate::clean_surface::{
    CLEAN_TEMPORAL_PRELUDE, CleanTemporalCertificateError, checked_theorem,
    elaborate_suffix_with_parser_prelude, elaborate_unit,
};
use crate::literal_refinement::{
    LiteralInvocation, LiteralRefinementCertificate, LiteralRefinementError,
    certify_literal_refinement, recheck_literal_refinement,
};

/// Retired parent schema embedding the pre-inline-aggregate literal certificate.
pub const MODEL_PROGRAM_REFINEMENT_SCHEMA_V1: &str = "trust.model-program-refinement/v1";

/// Current wire schema for a proof-carrying exact-program/model refinement.
pub const MODEL_PROGRAM_REFINEMENT_SCHEMA_V2: &str = "trust.model-program-refinement/v2";

const MAX_AUTHORED_SOURCE_BYTES: usize = 32 * 1024 * 1024;
const MAX_COMBINED_SOURCE_BYTES: usize = 96 * 1024 * 1024;
const KERNEL_STACK_BYTES: usize = 64 * 1024 * 1024;

const THEOREM_NAMES: [&str; 4] = [
    "Trust.ModelProgramRefinement.AppliedRefinement",
    "Trust.ModelProgramRefinement.AppliedRuns",
    "Trust.ModelProgramRefinement.AppliedPropertyTransport",
    "Trust.ModelProgramRefinement.AppliedFairPropertyTransport",
];

/// Separate schema: the existing v2 certificate still proves all-state simulation.
pub const INVARIANT_MODEL_PROGRAM_REFINEMENT_SCHEMA_V1: &str =
    "trust.invariant-model-program-refinement/v1";

const INVARIANT_THEOREM_NAMES: [&str; 7] = [
    "Trust.InvariantModelProgramRefinement.AppliedRefinement",
    "Trust.InvariantModelProgramRefinement.AppliedInitialInvariant",
    "Trust.InvariantModelProgramRefinement.AppliedPreservation",
    "Trust.InvariantModelProgramRefinement.AppliedRunInvariant",
    "Trust.InvariantModelProgramRefinement.AppliedRuns",
    "Trust.InvariantModelProgramRefinement.AppliedPropertyTransport",
    "Trust.InvariantModelProgramRefinement.AppliedFairPropertyTransport",
];

/// One theorem artifact regenerated and checked in the composed environment.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ModelProgramRefinementTheorem {
    pub theorem: String,
    pub theorem_type: Vec<u8>,
    pub proof_term: Vec<u8>,
}

/// Exact, independently replayable evidence that a finite model abstracts one
/// canonical closed TrustIR invocation.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ModelProgramRefinementCertificate {
    pub schema: String,
    pub literal: LiteralRefinementCertificate,
    pub model: CleanFiniteModelArtifact,
    /// Exact authored declarations containing the projection and refinement
    /// theorem.  The model source remains independently bound by `model`.
    pub refinement_source: String,
    pub projection_definition: String,
    pub refinement_theorem: String,
    pub theorems: Vec<ModelProgramRefinementTheorem>,
}

/// Exact-program refinement with a kernel-proved invariant of the original
/// program machine. The invariant never replaces or restricts its `Next`.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct InvariantModelProgramRefinementCertificate {
    pub schema: String,
    pub literal: LiteralRefinementCertificate,
    pub model: CleanFiniteModelArtifact,
    pub refinement_source: String,
    pub invariant_definition: String,
    pub projection_definition: String,
    pub refinement_theorem: String,
    pub theorems: Vec<ModelProgramRefinementTheorem>,
}

pub const INVARIANT_MODEL_PROGRAM_PROPERTY_SCHEMA_V1: &str =
    "trust.invariant-model-program-property/v1";

/// An authored property checked after separately imported program/model,
/// support, and refinement units. Callers own the chosen property; this does
/// not infer a fixed resource-policy claim from an arbitrary theorem.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub struct InvariantModelProgramPropertyCertificate {
    pub schema: String,
    pub refinement: InvariantModelProgramRefinementCertificate,
    pub support_source: String,
    pub property_source: String,
    pub property: ModelProgramRefinementTheorem,
}

/// Fail-closed diagnostics from model/program refinement or replay.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModelProgramRefinementError {
    SchemaMismatch { found: String },
    Literal(LiteralRefinementError),
    Model(CleanScalarModelError),
    Clean(CleanTemporalCertificateError),
    InvalidDeclarationName { role: &'static str, name: String },
    SourceTooLarge { role: &'static str, bytes: usize, maximum: usize },
    ModelSourceMismatch,
    RefinementSourceMismatch,
    ModelDefinitionMismatch,
    ProjectionDefinitionMismatch,
    InvariantDefinitionMismatch,
    SupportSourceMismatch,
    PropertySourceMismatch,
    PropertyTheoremMismatch,
    RefinementTheoremMismatch,
    ComposedModelMismatch,
    TheoremSetMismatch,
    ArtifactMismatch { theorem: String, field: &'static str },
    MalformedArtifact(String),
    KernelRejected(String),
    CleanSpecBuild(String),
}

impl fmt::Display for ModelProgramRefinementError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SchemaMismatch { found } => {
                write!(formatter, "unsupported model/program-refinement schema `{found}`")
            }
            Self::Literal(error) => write!(formatter, "literal program declined: {error}"),
            Self::Model(error) => write!(formatter, "finite model declined: {error}"),
            Self::Clean(error) => write!(formatter, "Clean refinement check failed: {error}"),
            Self::InvalidDeclarationName { role, name } => {
                write!(formatter, "invalid fully qualified {role} name `{name}`")
            }
            Self::SourceTooLarge { role, bytes, maximum } => {
                write!(formatter, "{role} source is {bytes} bytes; refinement limit is {maximum}")
            }
            Self::ModelSourceMismatch => {
                formatter.write_str("refinement certificate is bound to different model source")
            }
            Self::RefinementSourceMismatch => formatter
                .write_str("refinement certificate is bound to different authored proof source"),
            Self::ModelDefinitionMismatch => formatter
                .write_str("refinement certificate names a different finite-model definition"),
            Self::ProjectionDefinitionMismatch => formatter
                .write_str("refinement certificate names a different projection definition"),
            Self::InvariantDefinitionMismatch => {
                formatter.write_str("refinement certificate names a different source invariant")
            }
            Self::SupportSourceMismatch => {
                formatter.write_str("program property is bound to different support source")
            }
            Self::PropertySourceMismatch => {
                formatter.write_str("program property is bound to different property source")
            }
            Self::PropertyTheoremMismatch => {
                formatter.write_str("program property names a different theorem")
            }
            Self::RefinementTheoremMismatch => {
                formatter.write_str("refinement certificate names a different simulation theorem")
            }
            Self::ComposedModelMismatch => formatter.write_str(
                "finite model denotes different data in the composed program environment",
            ),
            Self::TheoremSetMismatch => formatter.write_str(
                "model/program refinement does not carry the complete ordered theorem set",
            ),
            Self::ArtifactMismatch { theorem, field } => {
                write!(formatter, "{field} for `{theorem}` differs from fresh elaboration")
            }
            Self::MalformedArtifact(detail) => {
                write!(formatter, "malformed model/program refinement artifact: {detail}")
            }
            Self::KernelRejected(detail) => {
                write!(formatter, "Clean kernel rejected stored refinement proof: {detail}")
            }
            Self::CleanSpecBuild(detail) => {
                write!(formatter, "cannot build composed Clean refinement context: {detail}")
            }
        }
    }
}

impl std::error::Error for ModelProgramRefinementError {}

impl From<LiteralRefinementError> for ModelProgramRefinementError {
    fn from(error: LiteralRefinementError) -> Self {
        Self::Literal(error)
    }
}

impl From<CleanScalarModelError> for ModelProgramRefinementError {
    fn from(error: CleanScalarModelError) -> Self {
        Self::Model(error)
    }
}

impl From<CleanTemporalCertificateError> for ModelProgramRefinementError {
    fn from(error: CleanTemporalCertificateError) -> Self {
        Self::Clean(error)
    }
}

fn validate_declaration_name(
    role: &'static str,
    name: &str,
) -> Result<(), ModelProgramRefinementError> {
    // Mirror clean-parser's unescaped Lean identifier grammar. Restricting the
    // interpolated value to dot-separated identifier tokens makes wrapper
    // generation injection-safe without excluding ordinary `_`, Unicode, or
    // theorem-style `foo'` / `foo?` / `foo!` declarations.
    let is_modifier_letter = |character: char| ('\u{02B0}'..='\u{02FF}').contains(&character);
    let is_start = |character: char| {
        !is_modifier_letter(character)
            && (character.is_alphabetic()
                || character == '_'
                || (character.is_numeric() && !character.is_ascii_digit()))
    };
    let is_continue = |character: char| {
        !is_modifier_letter(character)
            && (character.is_alphanumeric() || matches!(character, '_' | '\'' | '?' | '!'))
    };
    let valid_segment = |segment: &str| {
        let mut chars = segment.chars();
        matches!(chars.next(), Some(first) if is_start(first)) && chars.all(is_continue)
    };
    if name.is_empty()
        || name.len() > 512
        || name.split('.').any(|segment| segment == "_root_")
        || !name.split('.').all(valid_segment)
    {
        return Err(ModelProgramRefinementError::InvalidDeclarationName {
            role,
            name: name.to_owned(),
        });
    }
    Ok(())
}

fn check_source_size(
    role: &'static str,
    source: &str,
    maximum: usize,
) -> Result<(), ModelProgramRefinementError> {
    if source.len() > maximum {
        return Err(ModelProgramRefinementError::SourceTooLarge {
            role,
            bytes: source.len(),
            maximum,
        });
    }
    Ok(())
}

fn wrapper_source(
    model_definition: &str,
    projection_definition: &str,
    refinement_theorem: &str,
) -> String {
    format!(
        r#"
namespace Trust
namespace ModelProgramRefinement

def AppliedProjection : _root_.IRConfig →
    _root_.Trust.Temporal.FiniteModel.State :=
  _root_.{projection_definition}

theorem AppliedRefinement :
    _root_.Trust.Temporal.ForwardRefinement
      _root_.Trust.LiteralRefinement.Model
      (_root_.Trust.Temporal.FiniteModel.StateMachine _root_.{model_definition})
      AppliedProjection :=
  _root_.{refinement_theorem}

theorem AppliedRuns (behavior : _root_.Trust.Temporal.Behavior _root_.IRConfig)
    (runs : _root_.Trust.Temporal.Runs
      _root_.Trust.LiteralRefinement.Model behavior) :
    _root_.Trust.Temporal.Runs
      (_root_.Trust.Temporal.FiniteModel.StateMachine _root_.{model_definition})
      (fun n => AppliedProjection (behavior n)) :=
  _root_.Trust.Temporal.forwardRefinementRuns
    _root_.Trust.LiteralRefinement.Model
    (_root_.Trust.Temporal.FiniteModel.StateMachine _root_.{model_definition})
    AppliedProjection AppliedRefinement behavior runs

theorem AppliedPropertyTransport
    (F : _root_.Trust.Temporal.Formula
      _root_.Trust.Temporal.FiniteModel.State)
    (holds : _root_.Trust.Temporal.Satisfies
      (_root_.Trust.Temporal.FiniteModel.StateMachine _root_.{model_definition}) F) :
    _root_.Trust.Temporal.Satisfies _root_.Trust.LiteralRefinement.Model
      (_root_.Trust.Temporal.Pullback AppliedProjection F) :=
  _root_.Trust.Temporal.forwardRefinementSatisfies
    _root_.Trust.LiteralRefinement.Model
    (_root_.Trust.Temporal.FiniteModel.StateMachine _root_.{model_definition})
    AppliedProjection AppliedRefinement F holds

theorem AppliedFairPropertyTransport
    {{Index : Type}}
    (constraints : Index →
      _root_.Trust.Temporal.FairnessConstraint
        _root_.Trust.Temporal.FiniteModel.State)
    (F : _root_.Trust.Temporal.Formula
      _root_.Trust.Temporal.FiniteModel.State)
    (holds : _root_.Trust.Temporal.SatisfiesUnderFairness
      (_root_.Trust.Temporal.FiniteModel.StateMachine _root_.{model_definition})
      constraints F) :
    ∀ behavior : _root_.Trust.Temporal.Behavior _root_.IRConfig,
      _root_.Trust.Temporal.Runs
        _root_.Trust.LiteralRefinement.Model behavior →
      _root_.Trust.Temporal.FairFamily constraints
        (fun n => AppliedProjection (behavior n)) →
      _root_.Trust.Temporal.Pullback AppliedProjection F behavior :=
  _root_.Trust.Temporal.forwardRefinementSatisfiesUnderFairness
    _root_.Trust.LiteralRefinement.Model
    (_root_.Trust.Temporal.FiniteModel.StateMachine _root_.{model_definition})
    AppliedProjection AppliedRefinement constraints F holds

end ModelProgramRefinement
end Trust
"#,
    )
}

fn invariant_wrapper_source(
    model_definition: &str,
    invariant_definition: &str,
    projection_definition: &str,
    refinement_theorem: &str,
) -> String {
    format!(
        r#"
namespace Trust
namespace InvariantModelProgramRefinement

def AppliedInvariant : _root_.IRConfig → Prop := _root_.{invariant_definition}
def AppliedProjection : _root_.IRConfig →
    _root_.Trust.Temporal.FiniteModel.State := _root_.{projection_definition}

theorem AppliedRefinement :
    _root_.Trust.Temporal.InvariantForwardRefinement
      _root_.Trust.LiteralRefinement.Model
      (_root_.Trust.Temporal.FiniteModel.StateMachine _root_.{model_definition})
      AppliedProjection AppliedInvariant := _root_.{refinement_theorem}

theorem AppliedInitialInvariant (state : _root_.IRConfig)
    (initial : _root_.Trust.LiteralRefinement.Model.init state) :
    AppliedInvariant state := AppliedRefinement.init_invariant state initial

theorem AppliedPreservation (before after : _root_.IRConfig)
    (invariant : AppliedInvariant before)
    (step : _root_.Trust.LiteralRefinement.Model.next before after) :
    AppliedInvariant after := AppliedRefinement.preserve_invariant before after invariant step

theorem AppliedRunInvariant (behavior : _root_.Trust.Temporal.Behavior _root_.IRConfig)
    (runs : _root_.Trust.Temporal.Runs _root_.Trust.LiteralRefinement.Model behavior) :
    ∀ n : Nat, AppliedInvariant (behavior n) :=
  _root_.Trust.Temporal.invariantForwardRefinementInvariant
    _root_.Trust.LiteralRefinement.Model
    (_root_.Trust.Temporal.FiniteModel.StateMachine _root_.{model_definition})
    AppliedProjection AppliedInvariant AppliedRefinement behavior runs

theorem AppliedRuns (behavior : _root_.Trust.Temporal.Behavior _root_.IRConfig)
    (runs : _root_.Trust.Temporal.Runs _root_.Trust.LiteralRefinement.Model behavior) :
    _root_.Trust.Temporal.Runs
      (_root_.Trust.Temporal.FiniteModel.StateMachine _root_.{model_definition})
      (fun n => AppliedProjection (behavior n)) :=
  _root_.Trust.Temporal.invariantForwardRefinementRuns
    _root_.Trust.LiteralRefinement.Model
    (_root_.Trust.Temporal.FiniteModel.StateMachine _root_.{model_definition})
    AppliedProjection AppliedInvariant AppliedRefinement behavior runs

theorem AppliedPropertyTransport
    (F : _root_.Trust.Temporal.Formula _root_.Trust.Temporal.FiniteModel.State)
    (holds : _root_.Trust.Temporal.Satisfies
      (_root_.Trust.Temporal.FiniteModel.StateMachine _root_.{model_definition}) F) :
    _root_.Trust.Temporal.Satisfies _root_.Trust.LiteralRefinement.Model
      (_root_.Trust.Temporal.Pullback AppliedProjection F) :=
  _root_.Trust.Temporal.invariantForwardRefinementSatisfies
    _root_.Trust.LiteralRefinement.Model
    (_root_.Trust.Temporal.FiniteModel.StateMachine _root_.{model_definition})
    AppliedProjection AppliedInvariant AppliedRefinement F holds

theorem AppliedFairPropertyTransport
    {{Index : Type}}
    (constraints : Index → _root_.Trust.Temporal.FairnessConstraint
      _root_.Trust.Temporal.FiniteModel.State)
    (F : _root_.Trust.Temporal.Formula _root_.Trust.Temporal.FiniteModel.State)
    (holds : _root_.Trust.Temporal.SatisfiesUnderFairness
      (_root_.Trust.Temporal.FiniteModel.StateMachine _root_.{model_definition})
      constraints F) :
    ∀ behavior : _root_.Trust.Temporal.Behavior _root_.IRConfig,
      _root_.Trust.Temporal.Runs _root_.Trust.LiteralRefinement.Model behavior →
      _root_.Trust.Temporal.FairFamily constraints (fun n => AppliedProjection (behavior n)) →
      _root_.Trust.Temporal.Pullback AppliedProjection F behavior :=
  _root_.Trust.Temporal.invariantForwardRefinementSatisfiesUnderFairness
    _root_.Trust.LiteralRefinement.Model
    (_root_.Trust.Temporal.FiniteModel.StateMachine _root_.{model_definition})
    AppliedProjection AppliedInvariant AppliedRefinement constraints F holds

end InvariantModelProgramRefinement
end Trust
"#,
    )
}

fn check_combined_source_size(
    literal_source: &str,
    model_source: &str,
    refinement_source: &str,
    wrapper: &str,
) -> Result<(), ModelProgramRefinementError> {
    let capacity = literal_source
        .len()
        .checked_add(model_source.len())
        .and_then(|bytes| bytes.checked_add(refinement_source.len()))
        .and_then(|bytes| bytes.checked_add(wrapper.len()))
        .and_then(|bytes| bytes.checked_add(3))
        .ok_or(ModelProgramRefinementError::SourceTooLarge {
            role: "combined",
            bytes: usize::MAX,
            maximum: MAX_COMBINED_SOURCE_BYTES,
        })?;
    if capacity > MAX_COMBINED_SOURCE_BYTES {
        return Err(ModelProgramRefinementError::SourceTooLarge {
            role: "combined",
            bytes: capacity,
            maximum: MAX_COMBINED_SOURCE_BYTES,
        });
    }
    Ok(())
}

fn run_on_kernel_stack<T, F>(operation: F) -> Result<T, ModelProgramRefinementError>
where
    T: Send + 'static,
    F: FnOnce() -> Result<T, ModelProgramRefinementError> + Send + 'static,
{
    // A persistent worker, so `fresh_composed_context`'s per-thread cache
    // survives from one call to the next (see `crate::kernel_worker`).
    const _: () = assert!(KERNEL_STACK_BYTES <= crate::kernel_worker::KERNEL_WORKER_STACK_BYTES);
    crate::kernel_worker::run_on_kernel_worker(operation).map_err(|error| match error {
        crate::kernel_worker::KernelWorkerError::Spawn(error) => {
            ModelProgramRefinementError::CleanSpecBuild(error.to_string())
        }
        crate::kernel_worker::KernelWorkerError::Panicked => {
            ModelProgramRefinementError::CleanSpecBuild(
                "isolated refinement worker panicked".to_owned(),
            )
        }
    })?
}

fn fresh_composed_context() -> Result<(Environment, FileContext), ModelProgramRefinementError> {
    // Trust (Clean R80 item 2; `docs/DECISION_QUEUE.md` R80-CONSUMERS-1): the
    // context goes out as a `FileContext::fork_run` copy, a new elaboration run
    // to which the cached prelude's declarations are imported; a plain clone
    // keeps the prelude's run (see `elaborate_composed_context` for the units
    // elaborated after it).
    //
    // Keep the current worker-local cache policy. Pinned Clean's FileContext
    // and Environment are Send + Sync; sharing the prelude globally is a
    // separate optimization. This build is a pure function of compile-time
    // EvalIR/temporal sources with external import search disabled. Each worker
    // builds the same frontier and hands out owned, isolated run forks.
    thread_local! {
        static COMPOSED_PRELUDE: std::cell::OnceCell<
            Result<(Environment, FileContext), ModelProgramRefinementError>,
        > = const { std::cell::OnceCell::new() };
    }
    COMPOSED_PRELUDE.with(|cache| {
        cache
            .get_or_init(|| {
                let spec =
                    clean_verify::eval_ir::build_prelude_spec_with_stack().map_err(|error| {
                        ModelProgramRefinementError::CleanSpecBuild(error.to_string())
                    })?;
                let mut environment = spec.env().clone();
                let mut context = FileContext::new();
                context.disable_external_import_search();
                elaborate_unit(
                    &mut environment,
                    &mut context,
                    CLEAN_TEMPORAL_PRELUDE,
                    "temporal prelude in composed EvalIR environment",
                    None,
                )?;
                Ok((environment, context))
            })
            .as_ref()
            .map(|(environment, context)| (environment.clone(), context.fork_run()))
            .map_err(Clone::clone)
    })
}

fn parser_prelude() -> String {
    let mut prelude =
        String::with_capacity(CLEAN_TEMPORAL_PRELUDE.len() + FINITE_MODEL_PRELUDE.len() + 1);
    prelude.push_str(CLEAN_TEMPORAL_PRELUDE);
    prelude.push('\n');
    prelude.push_str(FINITE_MODEL_PRELUDE);
    prelude
}

fn encode_expression(expression: &Expr) -> Result<Vec<u8>, ModelProgramRefinementError> {
    serde_json::to_vec(expression)
        .map_err(|error| ModelProgramRefinementError::MalformedArtifact(error.to_string()))
}

fn elaborate_composed_context(
    literal_source: &str,
    model_source: &str,
    model_definition: &str,
    expected_model: &CleanFiniteModel,
    refinement_source: &str,
    wrapper: &str,
) -> Result<(Environment, FileContext), ModelProgramRefinementError> {
    #[cfg(test)]
    frontier_tests::record_prefix(refinement_source);
    let (mut environment, mut context) = fresh_composed_context()?;

    // Preserve the literal child's exact declaration frontier. In particular,
    // the finite-model prelude and authored sources must not participate in
    // resolution of the generated program semantics.
    elaborate_suffix_with_parser_prelude(
        &mut environment,
        &mut context,
        CLEAN_TEMPORAL_PRELUDE,
        literal_source,
        "exact literal program in composed environment",
    )?;
    elaborate_suffix_with_parser_prelude(
        &mut environment,
        &mut context,
        CLEAN_TEMPORAL_PRELUDE,
        FINITE_MODEL_PRELUDE,
        "finite-model prelude in composed EvalIR environment",
    )?;

    // Trust (Clean R80 item 2; `docs/DECISION_QUEUE.md` R80-CONSUMERS-1): each
    // authored unit is elaborated in a run of its own, so its `attribute
    // [implemented_by]` / `[extern]` commands may bind only its own
    // declarations; everything elaborated before it is imported to it, as Lean
    // refuses those. Both entries also elaborate the model alone over the
    // finite-model context first (`extract_clean_finite_model`,
    // `recheck_clean_finite_model_artifact`), whose fork refuses it there; this
    // run does not rely on that. The fixed wrapper after the refinement binds
    // nothing.
    context = context.fork_run();
    let parser_prelude = parser_prelude();
    elaborate_suffix_with_parser_prelude(
        &mut environment,
        &mut context,
        &parser_prelude,
        model_source,
        "finite model in composed program environment",
    )?;
    let composed_model =
        decode_clean_finite_model_from_environment(&environment, model_definition)?;
    if !clean_finite_models_equal_stack_safe(expected_model, &composed_model) {
        return Err(ModelProgramRefinementError::ComposedModelMismatch);
    }

    // Trust (R80-CONSUMERS-1): the authored refinement's own run (above).
    context = context.fork_run();

    // Parse each independently supplied unit to EOF. Concatenating an authored
    // unit with the fixed wrapper would let an unclosed namespace capture the
    // wrapper and leave attacker-selected declarations at its expected names.
    elaborate_suffix_with_parser_prelude(
        &mut environment,
        &mut context,
        &parser_prelude,
        refinement_source,
        "authored model/program refinement",
    )?;
    elaborate_suffix_with_parser_prelude(
        &mut environment,
        &mut context,
        &parser_prelude,
        wrapper,
        "fixed model/program refinement wrapper",
    )?;
    Ok((environment, context))
}

fn check_source(
    literal_source: String,
    model_source: String,
    model_definition: String,
    expected_model: CleanFiniteModel,
    refinement_source: String,
    wrapper: String,
    stored_artifacts: Option<Vec<ModelProgramRefinementTheorem>>,
) -> Result<Vec<ModelProgramRefinementTheorem>, ModelProgramRefinementError> {
    check_source_theorems(
        literal_source,
        model_source,
        model_definition,
        expected_model,
        refinement_source,
        wrapper,
        &THEOREM_NAMES,
        stored_artifacts,
    )
}

#[allow(clippy::too_many_arguments)]
fn check_source_theorems(
    literal_source: String,
    model_source: String,
    model_definition: String,
    expected_model: CleanFiniteModel,
    refinement_source: String,
    wrapper: String,
    theorem_names: &'static [&'static str],
    stored_artifacts: Option<Vec<ModelProgramRefinementTheorem>>,
) -> Result<Vec<ModelProgramRefinementTheorem>, ModelProgramRefinementError> {
    validate_stored_theorem_set(stored_artifacts.as_deref(), theorem_names)?;
    run_on_kernel_stack(move || {
        let (environment, _) = elaborate_composed_context(
            &literal_source,
            &model_source,
            &model_definition,
            &expected_model,
            &refinement_source,
            &wrapper,
        )?;
        check_theorems_in_environment(&environment, theorem_names, stored_artifacts.as_deref())
    })
}

fn validate_stored_theorem_set(
    stored_artifacts: Option<&[ModelProgramRefinementTheorem]>,
    theorem_names: &[&str],
) -> Result<(), ModelProgramRefinementError> {
    if stored_artifacts.is_some_and(|stored| {
        stored.len() != theorem_names.len()
            || stored
                .iter()
                .zip(theorem_names)
                .any(|(artifact, expected)| artifact.theorem != *expected)
    }) {
        return Err(ModelProgramRefinementError::TheoremSetMismatch);
    }
    Ok(())
}

/// Synchronous portion shared by standalone replay and the request-local
/// frontier. The caller owns its large-stack worker and original environment.
fn check_theorems_in_environment(
    environment: &Environment,
    theorem_names: &[&str],
    stored_artifacts: Option<&[ModelProgramRefinementTheorem]>,
) -> Result<Vec<ModelProgramRefinementTheorem>, ModelProgramRefinementError> {
    validate_stored_theorem_set(stored_artifacts, theorem_names)?;
    let fresh = theorem_names
        .iter()
        .map(|theorem| {
            let (theorem_type, proof_term) = checked_theorem(environment, theorem)?;
            Ok(ModelProgramRefinementTheorem {
                theorem: (*theorem).to_owned(),
                theorem_type: encode_expression(theorem_type)?,
                proof_term: encode_expression(proof_term)?,
            })
        })
        .collect::<Result<Vec<_>, ModelProgramRefinementError>>()?;

    if let Some(stored_artifacts) = stored_artifacts {
        for (artifact, fresh_artifact) in stored_artifacts.iter().zip(&fresh) {
            if artifact.theorem_type != fresh_artifact.theorem_type {
                return Err(ModelProgramRefinementError::ArtifactMismatch {
                    theorem: artifact.theorem.clone(),
                    field: "theorem type",
                });
            }
            if artifact.proof_term != fresh_artifact.proof_term {
                return Err(ModelProgramRefinementError::ArtifactMismatch {
                    theorem: artifact.theorem.clone(),
                    field: "proof term",
                });
            }
            let stored_type: Expr =
                serde_json::from_slice(&artifact.theorem_type).map_err(|error| {
                    ModelProgramRefinementError::MalformedArtifact(error.to_string())
                })?;
            let stored_proof: Expr =
                serde_json::from_slice(&artifact.proof_term).map_err(|error| {
                    ModelProgramRefinementError::MalformedArtifact(error.to_string())
                })?;
            let declaration =
                environment.get_const(&Name::from_string(&artifact.theorem)).ok_or_else(|| {
                    ModelProgramRefinementError::MalformedArtifact(format!(
                        "fresh environment lacks theorem `{}`",
                        artifact.theorem
                    ))
                })?;
            if encode_expression(&declaration.type_)? != artifact.theorem_type {
                return Err(ModelProgramRefinementError::ArtifactMismatch {
                    theorem: artifact.theorem.clone(),
                    field: "registered theorem type",
                });
            }
            TypeChecker::with_mode(environment, environment.mode())
                .check_type(&stored_proof, &stored_type)
                .map_err(|error| ModelProgramRefinementError::KernelRejected(error.to_string()))?;
        }
    }
    Ok(fresh)
}

/// Certify a kernel-checked forward simulation from one exact closed program
/// invocation to one exact finite model.
#[allow(clippy::too_many_arguments)]
pub fn certify_model_program_refinement(
    module_bytes: &[u8],
    function_id: u32,
    invocation: &LiteralInvocation,
    model_source: &str,
    model_definition: &str,
    refinement_source: &str,
    projection_definition: &str,
    refinement_theorem: &str,
) -> Result<ModelProgramRefinementCertificate, ModelProgramRefinementError> {
    validate_declaration_name("model definition", model_definition)?;
    validate_declaration_name("projection definition", projection_definition)?;
    validate_declaration_name("refinement theorem", refinement_theorem)?;
    check_source_size("model", model_source, MAX_AUTHORED_SOURCE_BYTES)?;
    check_source_size("authored refinement", refinement_source, MAX_AUTHORED_SOURCE_BYTES)?;

    let literal = certify_literal_refinement(module_bytes, function_id, invocation)?;
    let (model, decoded_model) = extract_clean_finite_model(model_source, model_definition)?;
    let wrapper = wrapper_source(model_definition, projection_definition, refinement_theorem);
    check_combined_source_size(&literal.clean_source, model_source, refinement_source, &wrapper)?;
    let theorems = check_source(
        literal.clean_source.clone(),
        model_source.to_owned(),
        model_definition.to_owned(),
        decoded_model,
        refinement_source.to_owned(),
        wrapper.clone(),
        None,
    )?;
    let certificate = ModelProgramRefinementCertificate {
        schema: MODEL_PROGRAM_REFINEMENT_SCHEMA_V2.to_owned(),
        literal,
        model,
        refinement_source: refinement_source.to_owned(),
        projection_definition: projection_definition.to_owned(),
        refinement_theorem: refinement_theorem.to_owned(),
        theorems,
    };
    recheck_model_program_refinement(
        &certificate,
        module_bytes,
        function_id,
        invocation,
        model_source,
        model_definition,
        refinement_source,
        projection_definition,
        refinement_theorem,
    )?;
    Ok(certificate)
}

/// Replay a model/program refinement from exact caller-supplied inputs.
#[allow(clippy::too_many_arguments)]
pub fn recheck_model_program_refinement(
    certificate: &ModelProgramRefinementCertificate,
    expected_module_bytes: &[u8],
    expected_function_id: u32,
    expected_invocation: &LiteralInvocation,
    expected_model_source: &str,
    expected_model_definition: &str,
    expected_refinement_source: &str,
    expected_projection_definition: &str,
    expected_refinement_theorem: &str,
) -> Result<(), ModelProgramRefinementError> {
    if certificate.schema != MODEL_PROGRAM_REFINEMENT_SCHEMA_V2 {
        return Err(ModelProgramRefinementError::SchemaMismatch {
            found: certificate.schema.clone(),
        });
    }
    if certificate.model.clean_source != expected_model_source {
        return Err(ModelProgramRefinementError::ModelSourceMismatch);
    }
    if certificate.model.model_definition != expected_model_definition {
        return Err(ModelProgramRefinementError::ModelDefinitionMismatch);
    }
    if certificate.refinement_source != expected_refinement_source {
        return Err(ModelProgramRefinementError::RefinementSourceMismatch);
    }
    if certificate.projection_definition != expected_projection_definition {
        return Err(ModelProgramRefinementError::ProjectionDefinitionMismatch);
    }
    if certificate.refinement_theorem != expected_refinement_theorem {
        return Err(ModelProgramRefinementError::RefinementTheoremMismatch);
    }
    validate_declaration_name("model definition", expected_model_definition)?;
    validate_declaration_name("projection definition", expected_projection_definition)?;
    validate_declaration_name("refinement theorem", expected_refinement_theorem)?;
    check_source_size("model", expected_model_source, MAX_AUTHORED_SOURCE_BYTES)?;
    check_source_size(
        "authored refinement",
        expected_refinement_source,
        MAX_AUTHORED_SOURCE_BYTES,
    )?;

    let wrapper = wrapper_source(
        expected_model_definition,
        expected_projection_definition,
        expected_refinement_theorem,
    );
    check_combined_source_size(
        &certificate.literal.clean_source,
        expected_model_source,
        expected_refinement_source,
        &wrapper,
    )?;
    if certificate.theorems.len() != THEOREM_NAMES.len()
        || certificate
            .theorems
            .iter()
            .zip(THEOREM_NAMES)
            .any(|(artifact, expected)| artifact.theorem != expected)
    {
        return Err(ModelProgramRefinementError::TheoremSetMismatch);
    }

    recheck_literal_refinement(
        &certificate.literal,
        expected_module_bytes,
        expected_function_id,
        expected_invocation,
    )?;
    let decoded_model =
        recheck_clean_finite_model_artifact(&certificate.model, expected_model_source)?;
    let fresh = check_source(
        certificate.literal.clean_source.clone(),
        expected_model_source.to_owned(),
        expected_model_definition.to_owned(),
        decoded_model,
        expected_refinement_source.to_owned(),
        wrapper,
        Some(certificate.theorems.clone()),
    )?;
    for (stored, fresh) in certificate.theorems.iter().zip(fresh) {
        if stored.theorem_type != fresh.theorem_type {
            return Err(ModelProgramRefinementError::ArtifactMismatch {
                theorem: stored.theorem.clone(),
                field: "theorem type",
            });
        }
        if stored.proof_term != fresh.proof_term {
            return Err(ModelProgramRefinementError::ArtifactMismatch {
                theorem: stored.theorem.clone(),
                field: "proof term",
            });
        }
    }
    Ok(())
}

/// Certify invariant-relative simulation of the exact original program machine.
///
/// The authored theorem must prove initialization and preservation of the named
/// invariant, plus initial-state and step simulation. Property transport remains
/// conditional on a proof of the exact model's property; model data alone is not
/// that proof. This generic API permits constant projections and grants no fixed
/// source-policy claim merely from their existence.
#[allow(clippy::too_many_arguments)]
pub fn certify_invariant_model_program_refinement(
    module_bytes: &[u8],
    function_id: u32,
    invocation: &LiteralInvocation,
    model_source: &str,
    model_definition: &str,
    refinement_source: &str,
    invariant_definition: &str,
    projection_definition: &str,
    refinement_theorem: &str,
) -> Result<InvariantModelProgramRefinementCertificate, ModelProgramRefinementError> {
    validate_declaration_name("model definition", model_definition)?;
    validate_declaration_name("source invariant", invariant_definition)?;
    validate_declaration_name("projection definition", projection_definition)?;
    validate_declaration_name("refinement theorem", refinement_theorem)?;
    check_source_size("model", model_source, MAX_AUTHORED_SOURCE_BYTES)?;
    check_source_size("authored refinement", refinement_source, MAX_AUTHORED_SOURCE_BYTES)?;
    let literal = certify_literal_refinement(module_bytes, function_id, invocation)?;
    let (model, decoded_model) = extract_clean_finite_model(model_source, model_definition)?;
    let wrapper = invariant_wrapper_source(
        model_definition,
        invariant_definition,
        projection_definition,
        refinement_theorem,
    );
    check_combined_source_size(&literal.clean_source, model_source, refinement_source, &wrapper)?;
    let theorems = check_source_theorems(
        literal.clean_source.clone(),
        model_source.to_owned(),
        model_definition.to_owned(),
        decoded_model,
        refinement_source.to_owned(),
        wrapper,
        &INVARIANT_THEOREM_NAMES,
        None,
    )?;
    let certificate = InvariantModelProgramRefinementCertificate {
        schema: INVARIANT_MODEL_PROGRAM_REFINEMENT_SCHEMA_V1.to_owned(),
        literal,
        model,
        refinement_source: refinement_source.to_owned(),
        invariant_definition: invariant_definition.to_owned(),
        projection_definition: projection_definition.to_owned(),
        refinement_theorem: refinement_theorem.to_owned(),
        theorems,
    };
    recheck_invariant_model_program_refinement(
        &certificate,
        module_bytes,
        function_id,
        invocation,
        model_source,
        model_definition,
        refinement_source,
        invariant_definition,
        projection_definition,
        refinement_theorem,
    )?;
    Ok(certificate)
}

/// Replay from caller-supplied exact program, model, invariant and proof inputs.
/// Saved verdicts and invariant-restricted replacement machines are not authority.
#[allow(clippy::too_many_arguments)]
pub fn recheck_invariant_model_program_refinement(
    certificate: &InvariantModelProgramRefinementCertificate,
    expected_module_bytes: &[u8],
    expected_function_id: u32,
    expected_invocation: &LiteralInvocation,
    expected_model_source: &str,
    expected_model_definition: &str,
    expected_refinement_source: &str,
    expected_invariant_definition: &str,
    expected_projection_definition: &str,
    expected_refinement_theorem: &str,
) -> Result<(), ModelProgramRefinementError> {
    let prepared = prepare_invariant_replay(
        certificate,
        expected_module_bytes,
        expected_function_id,
        expected_invocation,
        expected_model_source,
        expected_model_definition,
        expected_refinement_source,
        expected_invariant_definition,
        expected_projection_definition,
        expected_refinement_theorem,
    )?;
    check_source_theorems(
        prepared.literal_source,
        prepared.model_source,
        prepared.model_definition,
        prepared.decoded_model,
        prepared.refinement_source,
        prepared.wrapper,
        &INVARIANT_THEOREM_NAMES,
        Some(prepared.theorems),
    )?;
    Ok(())
}

/// Exact-input preparation shared by standalone and property replay. This is
/// data, not a checked environment or transferable proof authority.
struct PreparedInvariantReplay {
    literal_source: String,
    model_source: String,
    model_definition: String,
    decoded_model: CleanFiniteModel,
    refinement_source: String,
    wrapper: String,
    theorems: Vec<ModelProgramRefinementTheorem>,
}

#[allow(clippy::too_many_arguments)]
fn prepare_invariant_replay(
    certificate: &InvariantModelProgramRefinementCertificate,
    expected_module_bytes: &[u8],
    expected_function_id: u32,
    expected_invocation: &LiteralInvocation,
    expected_model_source: &str,
    expected_model_definition: &str,
    expected_refinement_source: &str,
    expected_invariant_definition: &str,
    expected_projection_definition: &str,
    expected_refinement_theorem: &str,
) -> Result<PreparedInvariantReplay, ModelProgramRefinementError> {
    if certificate.schema != INVARIANT_MODEL_PROGRAM_REFINEMENT_SCHEMA_V1 {
        return Err(ModelProgramRefinementError::SchemaMismatch {
            found: certificate.schema.clone(),
        });
    }
    if certificate.model.clean_source != expected_model_source {
        return Err(ModelProgramRefinementError::ModelSourceMismatch);
    }
    if certificate.model.model_definition != expected_model_definition {
        return Err(ModelProgramRefinementError::ModelDefinitionMismatch);
    }
    if certificate.refinement_source != expected_refinement_source {
        return Err(ModelProgramRefinementError::RefinementSourceMismatch);
    }
    if certificate.invariant_definition != expected_invariant_definition {
        return Err(ModelProgramRefinementError::InvariantDefinitionMismatch);
    }
    if certificate.projection_definition != expected_projection_definition {
        return Err(ModelProgramRefinementError::ProjectionDefinitionMismatch);
    }
    if certificate.refinement_theorem != expected_refinement_theorem {
        return Err(ModelProgramRefinementError::RefinementTheoremMismatch);
    }
    validate_declaration_name("model definition", expected_model_definition)?;
    validate_declaration_name("source invariant", expected_invariant_definition)?;
    validate_declaration_name("projection definition", expected_projection_definition)?;
    validate_declaration_name("refinement theorem", expected_refinement_theorem)?;
    check_source_size("model", expected_model_source, MAX_AUTHORED_SOURCE_BYTES)?;
    check_source_size(
        "authored refinement",
        expected_refinement_source,
        MAX_AUTHORED_SOURCE_BYTES,
    )?;
    let wrapper = invariant_wrapper_source(
        expected_model_definition,
        expected_invariant_definition,
        expected_projection_definition,
        expected_refinement_theorem,
    );
    check_combined_source_size(
        &certificate.literal.clean_source,
        expected_model_source,
        expected_refinement_source,
        &wrapper,
    )?;
    recheck_literal_refinement(
        &certificate.literal,
        expected_module_bytes,
        expected_function_id,
        expected_invocation,
    )?;
    let decoded_model =
        recheck_clean_finite_model_artifact(&certificate.model, expected_model_source)?;
    validate_stored_theorem_set(Some(&certificate.theorems), &INVARIANT_THEOREM_NAMES)?;
    Ok(PreparedInvariantReplay {
        literal_source: certificate.literal.clean_source.clone(),
        model_source: expected_model_source.to_owned(),
        model_definition: expected_model_definition.to_owned(),
        decoded_model,
        refinement_source: expected_refinement_source.to_owned(),
        wrapper,
        theorems: certificate.theorems.clone(),
    })
}

#[allow(clippy::too_many_arguments)]
fn check_program_property(
    literal_source: String,
    model_source: String,
    model_definition: String,
    expected_model: CleanFiniteModel,
    refinement_source: String,
    support_source: String,
    property_source: String,
    theorem: String,
    refinement_wrapper: String,
    refinement_theorems: Vec<ModelProgramRefinementTheorem>,
    stored: Option<ModelProgramRefinementTheorem>,
) -> Result<ModelProgramRefinementTheorem, ModelProgramRefinementError> {
    check_property_source_sizes(
        [
            literal_source.len(),
            model_source.len(),
            refinement_source.len(),
            refinement_wrapper.len(),
        ],
        &support_source,
        &property_source,
    )?;
    run_on_kernel_stack(move || {
        let (environment, context) = elaborate_composed_context(
            &literal_source,
            &model_source,
            &model_definition,
            &expected_model,
            &refinement_source,
            &refinement_wrapper,
        )?;
        extend_program_property(
            environment,
            context,
            &support_source,
            &property_source,
            &theorem,
            &refinement_theorems,
            stored.as_ref(),
        )
    })
}

fn check_property_source_sizes(
    prefix_lengths: [usize; 4],
    support_source: &str,
    property_source: &str,
) -> Result<(), ModelProgramRefinementError> {
    check_source_size("support", support_source, MAX_AUTHORED_SOURCE_BYTES)?;
    check_source_size("property", property_source, MAX_AUTHORED_SOURCE_BYTES)?;
    let [literal, model, refinement, wrapper] = prefix_lengths;
    let combined =
        [literal, model, refinement, support_source.len(), property_source.len(), wrapper]
            .into_iter()
            .try_fold(5usize, usize::checked_add)
            .ok_or(ModelProgramRefinementError::SourceTooLarge {
                role: "combined",
                bytes: usize::MAX,
                maximum: MAX_COMBINED_SOURCE_BYTES,
            })?;
    if combined > MAX_COMBINED_SOURCE_BYTES {
        return Err(ModelProgramRefinementError::SourceTooLarge {
            role: "combined",
            bytes: combined,
            maximum: MAX_COMBINED_SOURCE_BYTES,
        });
    }
    Ok(())
}

/// Consumes this request's environment. Neither a failed extension nor its
/// partially elaborated declarations can be retried as another request.
fn extend_program_property(
    mut environment: Environment,
    mut context: FileContext,
    support_source: &str,
    property_source: &str,
    theorem: &str,
    refinement_theorems: &[ModelProgramRefinementTheorem],
    stored: Option<&ModelProgramRefinementTheorem>,
) -> Result<ModelProgramRefinementTheorem, ModelProgramRefinementError> {
    // The inner proof is checked in precisely its independent declaration
    // frontier before any support name can affect resolution. Later units
    // import this frontier and cannot replace its declarations.
    if refinement_theorems.len() != INVARIANT_THEOREM_NAMES.len()
        || refinement_theorems
            .iter()
            .zip(INVARIANT_THEOREM_NAMES)
            .any(|(artifact, name)| artifact.theorem != name)
    {
        return Err(ModelProgramRefinementError::TheoremSetMismatch);
    }
    for artifact in refinement_theorems {
        let (ty, proof) = checked_theorem(&environment, &artifact.theorem)?;
        if encode_expression(ty)? != artifact.theorem_type
            || encode_expression(proof)? != artifact.proof_term
        {
            return Err(ModelProgramRefinementError::ArtifactMismatch {
                theorem: artifact.theorem.clone(),
                field: "property refinement frontier",
            });
        }
    }
    let parser_prelude = parser_prelude();
    for (source, label) in [
        (support_source, "isolated model/program property support"),
        (property_source, "isolated model/program property"),
    ] {
        context = context.fork_run();
        elaborate_suffix_with_parser_prelude(
            &mut environment,
            &mut context,
            &parser_prelude,
            source,
            label,
        )?;
    }
    let (theorem_type, proof_term) = checked_theorem(&environment, theorem)?;
    let fresh = ModelProgramRefinementTheorem {
        theorem: theorem.to_owned(),
        theorem_type: encode_expression(theorem_type)?,
        proof_term: encode_expression(proof_term)?,
    };
    if let Some(stored) = stored {
        if *stored != fresh {
            return Err(ModelProgramRefinementError::ArtifactMismatch {
                theorem: theorem.to_owned(),
                field: "property theorem or proof",
            });
        }
        let ty: Expr = serde_json::from_slice(&stored.theorem_type)
            .map_err(|error| ModelProgramRefinementError::MalformedArtifact(error.to_string()))?;
        let proof: Expr = serde_json::from_slice(&stored.proof_term)
            .map_err(|error| ModelProgramRefinementError::MalformedArtifact(error.to_string()))?;
        TypeChecker::with_mode(&environment, environment.mode())
            .check_type(&proof, &ty)
            .map_err(|error| ModelProgramRefinementError::KernelRejected(error.to_string()))?;
    }
    Ok(fresh)
}

/// Created only after every inner artifact has freshly passed in this exact
/// environment. It exists and is consumed within one kernel-worker request;
/// it is never returned, cloned, serialized or retained for another request.
struct CheckedFrontier {
    environment: Environment,
    context: FileContext,
    prefix_lengths: [usize; 4],
    theorems: Vec<ModelProgramRefinementTheorem>,
}

impl CheckedFrontier {
    fn check(prepared: PreparedInvariantReplay) -> Result<Self, ModelProgramRefinementError> {
        let prefix_lengths = [
            prepared.literal_source.len(),
            prepared.model_source.len(),
            prepared.refinement_source.len(),
            prepared.wrapper.len(),
        ];
        let (environment, context) = elaborate_composed_context(
            &prepared.literal_source,
            &prepared.model_source,
            &prepared.model_definition,
            &prepared.decoded_model,
            &prepared.refinement_source,
            &prepared.wrapper,
        )?;
        check_theorems_in_environment(
            &environment,
            &INVARIANT_THEOREM_NAMES,
            Some(&prepared.theorems),
        )?;
        Ok(Self { environment, context, prefix_lengths, theorems: prepared.theorems })
    }

    fn check_property(
        self,
        support_source: &str,
        property_source: &str,
        theorem: &str,
        stored: &ModelProgramRefinementTheorem,
    ) -> Result<(), ModelProgramRefinementError> {
        // Preserve the public replay's error priority: invalid inner proofs
        // fail before oversized support/property sources are considered.
        check_property_source_sizes(self.prefix_lengths, support_source, property_source)?;
        extend_program_property(
            self.environment,
            self.context,
            support_source,
            property_source,
            theorem,
            &self.theorems,
            Some(stored),
        )?;
        Ok(())
    }
}

/// Check a final authored property after separate model, support and refinement
/// units. Fixed-policy callers must regenerate their exact goal and projection.
#[allow(clippy::too_many_arguments)]
pub fn certify_invariant_model_program_property(
    module_bytes: &[u8],
    function_id: u32,
    invocation: &LiteralInvocation,
    model_source: &str,
    model_definition: &str,
    refinement_source: &str,
    invariant_definition: &str,
    projection_definition: &str,
    refinement_theorem: &str,
    support_source: &str,
    property_source: &str,
    property_theorem: &str,
) -> Result<InvariantModelProgramPropertyCertificate, ModelProgramRefinementError> {
    validate_declaration_name("property theorem", property_theorem)?;
    let refinement = certify_invariant_model_program_refinement(
        module_bytes,
        function_id,
        invocation,
        model_source,
        model_definition,
        refinement_source,
        invariant_definition,
        projection_definition,
        refinement_theorem,
    )?;
    let decoded_model = recheck_clean_finite_model_artifact(&refinement.model, model_source)?;
    let wrapper = invariant_wrapper_source(
        model_definition,
        invariant_definition,
        projection_definition,
        refinement_theorem,
    );
    let property = check_program_property(
        refinement.literal.clean_source.clone(),
        model_source.to_owned(),
        model_definition.to_owned(),
        decoded_model,
        refinement_source.to_owned(),
        support_source.to_owned(),
        property_source.to_owned(),
        property_theorem.to_owned(),
        wrapper,
        refinement.theorems.clone(),
        None,
    )?;
    let certificate = InvariantModelProgramPropertyCertificate {
        schema: INVARIANT_MODEL_PROGRAM_PROPERTY_SCHEMA_V1.to_owned(),
        refinement,
        support_source: support_source.to_owned(),
        property_source: property_source.to_owned(),
        property,
    };
    recheck_invariant_model_program_property(
        &certificate,
        module_bytes,
        function_id,
        invocation,
        model_source,
        model_definition,
        refinement_source,
        invariant_definition,
        projection_definition,
        refinement_theorem,
        support_source,
        property_source,
        property_theorem,
    )?;
    Ok(certificate)
}

/// Replay the exact inputs while preserving every source-unit import boundary.
#[allow(clippy::too_many_arguments)]
pub fn recheck_invariant_model_program_property(
    certificate: &InvariantModelProgramPropertyCertificate,
    module_bytes: &[u8],
    function_id: u32,
    invocation: &LiteralInvocation,
    model_source: &str,
    model_definition: &str,
    refinement_source: &str,
    invariant_definition: &str,
    projection_definition: &str,
    refinement_theorem: &str,
    support_source: &str,
    property_source: &str,
    property_theorem: &str,
) -> Result<(), ModelProgramRefinementError> {
    if certificate.schema != INVARIANT_MODEL_PROGRAM_PROPERTY_SCHEMA_V1 {
        return Err(ModelProgramRefinementError::SchemaMismatch {
            found: certificate.schema.clone(),
        });
    }
    if certificate.support_source != support_source {
        return Err(ModelProgramRefinementError::SupportSourceMismatch);
    }
    if certificate.property_source != property_source {
        return Err(ModelProgramRefinementError::PropertySourceMismatch);
    }
    if certificate.property.theorem != property_theorem {
        return Err(ModelProgramRefinementError::PropertyTheoremMismatch);
    }
    validate_declaration_name("property theorem", property_theorem)?;
    let prepared = prepare_invariant_replay(
        &certificate.refinement,
        module_bytes,
        function_id,
        invocation,
        model_source,
        model_definition,
        refinement_source,
        invariant_definition,
        projection_definition,
        refinement_theorem,
    )?;
    // Stage a rejected size check without copying an oversized input. Its
    // error is returned only after full inner replay, preserving error order.
    let extension = check_property_source_sizes(
        [
            prepared.literal_source.len(),
            prepared.model_source.len(),
            prepared.refinement_source.len(),
            prepared.wrapper.len(),
        ],
        support_source,
        property_source,
    )
    .map(|()| {
        (
            support_source.to_owned(),
            property_source.to_owned(),
            property_theorem.to_owned(),
            certificate.property.clone(),
        )
    });
    run_on_kernel_stack(move || {
        let frontier = CheckedFrontier::check(prepared)?;
        let (support_source, property_source, property_theorem, stored) = extension?;
        frontier.check_property(&support_source, &property_source, &property_theorem, &stored)
    })
}

#[cfg(test)]
#[path = "model_program_refinement/frontier_tests.rs"]
mod frontier_tests;

#[cfg(test)]
mod tests {
    use std::sync::OnceLock;

    use trust_ir::{
        Block, FuncId, FuncTy, FuncTyId, Function, Inst, InstrNode, Module, Ty, ValueId,
    };

    use super::*;

    /// Mutation control for the per-thread composed-context cache: the lane
    /// must run on persistent workers, or every call rebuilds the context.
    #[test]
    fn composed_lane_runs_on_reused_workers() {
        assert!(crate::kernel_worker::lane_reuses_a_worker(|| run_on_kernel_stack(|| Ok(
            crate::kernel_worker::probe_ran_on_this_thread_before()
        ))));
    }

    const MODEL_SOURCE: &str = r#"
namespace RefinementFixture

open Trust.Temporal.FiniteModel

def X : ScalarExpr := ScalarExpr.var "x"

def Model : Trust.Temporal.FiniteModel.Model :=
  Trust.Temporal.FiniteModel.Model.mk "ProgramAbstraction" []
    [StateVar.mk "x" 0] []
    [Action.mk "Stutter" Guard.always [Update.mk "x" X]]
    [Invariant.mk "Reflexive" (ScalarExpr.eq X X)]

end RefinementFixture
"#;

    /// The authored projection and forward simulation. `initialScalars` ends
    /// with an explicit `rfl`: Clean's `rw`, like Lean 4.8.0's macro
    /// (`rewrite …; try (with_reducible rfl)`), closes a goal only by REDUCIBLE
    /// `rfl` (Clean 6522ff6bb, in the feee691d2 pin), and what `rw [same]`
    /// leaves, `AbstractZero.scalar (StateVar.mk "x" 0).name =
    /// (StateVar.mk "x" 0).init`, needs `AbstractZero`, a plain `def`, unfolded.
    const REFINEMENT_SOURCE: &str = r#"
namespace RefinementFixture

open Trust.Temporal.FiniteModel

def AbstractZero : State :=
  State.mk (fun _ => 0) (fun _ _ => false)

def Projection (_ : IRConfig) : State := AbstractZero

theorem abstractZeroScalar (name : String) :
    AbstractZero.scalar name = 0 := rfl

theorem abstractZeroFunction (name : String) (index : Nat) :
    AbstractZero.function name index = false := rfl

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

theorem noInitialFunctions (entry : FunctionVar)
    (member : Member entry (List.nil FunctionVar)) (index : Nat) :
    AbstractZero.function entry.name index = false :=
  False.elim (noMemberNil member)

theorem projectionCanonical : CanonicalState Model AbstractZero :=
  And.intro
    (fun (name : String) (absent : ¬ DeclaresScalar Model name) =>
      abstractZeroScalar name)
    (fun (name : String) (value : Nat)
        (absent : ¬ DeclaresFunctionAt Model name value) =>
      abstractZeroFunction name value)

theorem initialScalars (entry : StateVar)
    (member : Member entry [StateVar.mk "x" 0]) :
    AbstractZero.scalar entry.name = entry.init := by
  have same : entry = StateVar.mk "x" 0 := memberSingleton member
  rewrite [same]
  rfl

theorem projectionInitial : Initial Model AbstractZero :=
  And.intro projectionCanonical
    (And.intro initialScalars noInitialFunctions)

theorem ProgramRefinesModel :
    Trust.Temporal.ForwardRefinement
      Trust.LiteralRefinement.Model
      (Trust.Temporal.FiniteModel.StateMachine Model)
      Projection :=
  { init := fun _ _ => projectionInitial
    next := fun _ _ _ => Or.inr rfl }

end RefinementFixture
"#;

    const INVARIANT_EXTENSION: &str = r#"
namespace RefinementFixture

def SourceInvariant (_ : IRConfig) : Prop := True

theorem ProgramRefinesInvariantModel :
    Trust.Temporal.InvariantForwardRefinement
      Trust.LiteralRefinement.Model
      (Trust.Temporal.FiniteModel.StateMachine Model)
      Projection SourceInvariant :=
  { init_invariant := fun _ _ => True.intro
    preserve_invariant := fun _ _ _ _ => True.intro
    init := ProgramRefinesModel.init
    next := fun before after _ step => ProgramRefinesModel.next before after step }

end RefinementFixture
"#;

    fn invariant_source() -> String {
        format!("{REFINEMENT_SOURCE}\n{INVARIANT_EXTENSION}")
    }

    fn certify_invariant() -> InvariantModelProgramRefinementCertificate {
        static CERTIFICATE: OnceLock<InvariantModelProgramRefinementCertificate> = OnceLock::new();
        CERTIFICATE
            .get_or_init(|| {
                certify_invariant_model_program_refinement(
                    &fixture_bytes(),
                    0,
                    &LiteralInvocation::closed(vec![], 0),
                    MODEL_SOURCE,
                    "RefinementFixture.Model",
                    &invariant_source(),
                    "RefinementFixture.SourceInvariant",
                    "RefinementFixture.Projection",
                    "RefinementFixture.ProgramRefinesInvariantModel",
                )
                .expect("generic invariant-relative fixture carries all premises")
            })
            .clone()
    }

    fn recheck_invariant_fixture(
        certificate: &InvariantModelProgramRefinementCertificate,
    ) -> Result<(), ModelProgramRefinementError> {
        recheck_invariant_model_program_refinement(
            certificate,
            &fixture_bytes(),
            0,
            &LiteralInvocation::closed(vec![], 0),
            MODEL_SOURCE,
            "RefinementFixture.Model",
            &invariant_source(),
            "RefinementFixture.SourceInvariant",
            "RefinementFixture.Projection",
            "RefinementFixture.ProgramRefinesInvariantModel",
        )
    }

    #[test]
    fn invariant_relative_refinement_freshly_replays_all_premises_and_transport() {
        let certificate = certify_invariant();
        assert_eq!(certificate.schema, INVARIANT_MODEL_PROGRAM_REFINEMENT_SCHEMA_V1);
        assert_eq!(certificate.theorems.len(), INVARIANT_THEOREM_NAMES.len());
        let encoded = serde_json::to_vec(&certificate).unwrap();
        let decoded = serde_json::from_slice(&encoded).unwrap();
        recheck_invariant_fixture(&decoded).expect("fresh kernel replay of all seven exact goals");
    }

    #[test]
    fn invariant_relative_splices_and_missing_proof_artifacts_fail_closed() {
        let certificate = certify_invariant();
        let mut altered = certificate.clone();
        altered.invariant_definition = "RefinementFixture.OtherInvariant".to_owned();
        assert_eq!(
            recheck_invariant_fixture(&altered),
            Err(ModelProgramRefinementError::InvariantDefinitionMismatch)
        );
        altered = certificate.clone();
        altered.schema = MODEL_PROGRAM_REFINEMENT_SCHEMA_V2.to_owned();
        assert!(matches!(
            recheck_invariant_fixture(&altered),
            Err(ModelProgramRefinementError::SchemaMismatch { .. })
        ));
        altered = certificate.clone();
        altered.refinement_source.push_str("\n-- different bound source\n");
        assert_eq!(
            recheck_invariant_fixture(&altered),
            Err(ModelProgramRefinementError::RefinementSourceMismatch)
        );
        altered = certificate.clone();
        altered.projection_definition = "RefinementFixture.OtherProjection".to_owned();
        assert_eq!(
            recheck_invariant_fixture(&altered),
            Err(ModelProgramRefinementError::ProjectionDefinitionMismatch)
        );
        altered = certificate.clone();
        altered.model.clean_source.push_str("\n-- different model source\n");
        assert_eq!(
            recheck_invariant_fixture(&altered),
            Err(ModelProgramRefinementError::ModelSourceMismatch)
        );
        altered = certificate.clone();
        altered.refinement_theorem = "RefinementFixture.OtherProof".to_owned();
        assert_eq!(
            recheck_invariant_fixture(&altered),
            Err(ModelProgramRefinementError::RefinementTheoremMismatch)
        );
        altered = certificate.clone();
        altered.theorems.remove(2);
        assert_eq!(
            recheck_invariant_fixture(&altered),
            Err(ModelProgramRefinementError::TheoremSetMismatch)
        );
        altered = certificate.clone();
        altered.theorems[2].proof_term = certificate.theorems[1].proof_term.clone();
        assert!(matches!(
            recheck_invariant_fixture(&altered),
            Err(ModelProgramRefinementError::ArtifactMismatch { field: "proof term", .. })
        ));
        altered = certificate;
        altered.literal.function_id = 1;
        assert!(matches!(
            recheck_invariant_fixture(&altered),
            Err(ModelProgramRefinementError::Literal(_))
        ));
    }

    #[test]
    fn invariant_relative_requires_initialization_and_actual_step_preservation() {
        for source in [
            invariant_source().replace("    preserve_invariant := fun _ _ _ _ => True.intro\n", ""),
            invariant_source().replace(
                "preserve_invariant := fun _ _ _ _ => True.intro",
                "preserve_invariant := fun _ _ _ _ => 0",
            ),
            invariant_source().replace(
                "def SourceInvariant (_ : IRConfig) : Prop := True",
                "def SourceInvariant (_ : IRConfig) : Prop := False",
            ),
        ] {
            let error = certify_invariant_model_program_refinement(
                &fixture_bytes(),
                0,
                &LiteralInvocation::closed(vec![], 0),
                MODEL_SOURCE,
                "RefinementFixture.Model",
                &source,
                "RefinementFixture.SourceInvariant",
                "RefinementFixture.Projection",
                "RefinementFixture.ProgramRefinesInvariantModel",
            )
            .expect_err("an absent/false preservation or initial invariant is not a simulation");
            assert!(
                error.to_string().contains("ProgramRefinesInvariantModel"),
                "must fail at the actual invariant theorem, not an unrelated declaration: {error}"
            );
        }
    }

    const CONTEXT_SENSITIVE_MODEL_SOURCE: &str = r#"
def FunctionId : Nat := 9

namespace Trust
namespace LiteralRefinement
namespace ContextAttack

open Trust.Temporal.FiniteModel

def Chosen : Nat := FunctionId
def X : ScalarExpr := ScalarExpr.var "x"

def Model : Trust.Temporal.FiniteModel.Model :=
  Trust.Temporal.FiniteModel.Model.mk "ContextAttack" []
    [StateVar.mk "x" Chosen] []
    [Action.mk "Stutter" Guard.always [Update.mk "x" X]]
    [Invariant.mk "Reflexive" (ScalarExpr.eq X X)]

end ContextAttack
end LiteralRefinement
end Trust
"#;

    const DUMMY_PROGRAM_SOURCE: &str = r#"
inductive IRConfig where
  | mk : Nat → IRConfig

namespace Trust
namespace LiteralRefinement

def Model : Trust.Temporal.StateMachine IRConfig :=
  { init := fun _ => True, next := fun _ _ => True }

end LiteralRefinement
end Trust
"#;

    fn fixture_bytes() -> Vec<u8> {
        let mut module = Module::new("model_program_refinement_fixture");
        module.func_types.push(FuncTy {
            params: vec![],
            returns: vec![Ty::U8],
            is_vararg: false,
            abi: None,
        });
        let mut function =
            Function::new(FuncId::new(0), "answer", FuncTyId::new(0), trust_ir::BlockId::new(0));
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::U8, value: trust_ir::Constant::Int(7) })
                .with_result(ValueId::new(0)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
        function.blocks.push(block);
        module.functions.push(function);
        trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture")
    }

    fn certify() -> ModelProgramRefinementCertificate {
        static CERTIFICATE: OnceLock<ModelProgramRefinementCertificate> = OnceLock::new();
        CERTIFICATE
            .get_or_init(|| {
                let bytes = fixture_bytes();
                certify_model_program_refinement(
                    &bytes,
                    0,
                    &LiteralInvocation::closed(vec![], 0),
                    MODEL_SOURCE,
                    "RefinementFixture.Model",
                    REFINEMENT_SOURCE,
                    "RefinementFixture.Projection",
                    "RefinementFixture.ProgramRefinesModel",
                )
                .expect("fixture carries a constructive exact forward simulation")
            })
            .clone()
    }

    fn check_fixture_units(
        model_source: &str,
        model_definition: &str,
        refinement_source: &str,
        projection_definition: &str,
        refinement_theorem: &str,
    ) -> Result<Vec<ModelProgramRefinementTheorem>, ModelProgramRefinementError> {
        let literal_source = certify().literal.clean_source;
        let (_, decoded_model) = extract_clean_finite_model(model_source, model_definition)?;
        let wrapper = wrapper_source(model_definition, projection_definition, refinement_theorem);
        check_combined_source_size(&literal_source, model_source, refinement_source, &wrapper)?;
        check_source(
            literal_source,
            model_source.to_owned(),
            model_definition.to_owned(),
            decoded_model,
            refinement_source.to_owned(),
            wrapper,
            None,
        )
    }

    fn namespace_shadow_refinement_source() -> String {
        let source = REFINEMENT_SOURCE
            .replace("Trust.Temporal.", "_root_.Trust.Temporal.")
            .replace("Trust.LiteralRefinement.", "_root_.Trust.LiteralRefinement.")
            .replace("IRConfig", "_root_.IRConfig");
        let source = source.replacen(
            "namespace RefinementFixture",
            r#"namespace Trust
namespace ModelProgramRefinement
namespace RefinementFixture

def Model : _root_.Trust.Temporal.FiniteModel.Model :=
  _root_.RefinementFixture.Model"#,
            1,
        );
        source.replacen(
            "end RefinementFixture",
            "end RefinementFixture\nend ModelProgramRefinement\nend Trust",
            1,
        )
    }

    fn wrapper_capture_refinement_source() -> String {
        format!(
            r#"{REFINEMENT_SOURCE}

namespace Trust
namespace ModelProgramRefinement

theorem AppliedRefinement : True := True.intro
theorem AppliedRuns : True := True.intro
theorem AppliedPropertyTransport : True := True.intro
theorem AppliedFairPropertyTransport : True := True.intro

end ModelProgramRefinement
end Trust

namespace Evil
"#,
        )
    }

    #[test]
    fn authored_refinement_fixture_elaborates_in_finite_context() {
        let source = format!("{MODEL_SOURCE}\n{DUMMY_PROGRAM_SOURCE}\n{REFINEMENT_SOURCE}");
        extract_clean_finite_model(&source, "RefinementFixture.Model")
            .expect("authored model and forward simulation elaborate together");
    }

    #[test]
    fn initial_scalars_proof_rejects_a_wrong_declared_initial_value() {
        let false_refinement = REFINEMENT_SOURCE.replacen(
            "AbstractZero.scalar entry.name = entry.init := by",
            "AbstractZero.scalar entry.name = entry.init + 1 := by",
            1,
        );
        assert_ne!(false_refinement, REFINEMENT_SOURCE);
        let source = format!("{MODEL_SOURCE}\n{DUMMY_PROGRAM_SOURCE}\n{false_refinement}");
        let error = extract_clean_finite_model(&source, "RefinementFixture.Model")
            .expect_err("rewriting membership must not prove the false initial scalar equality");
        assert!(
            error.to_string().contains("RefinementFixture.initialScalars"),
            "the false equality must fail in its proof declaration: {error}"
        );
    }

    #[test]
    fn exact_model_program_refinement_freshly_replays() {
        let certificate = certify();
        assert_eq!(certificate.schema, MODEL_PROGRAM_REFINEMENT_SCHEMA_V2);
        assert_eq!(
            certificate.literal.schema,
            crate::literal_refinement::LITERAL_REFINEMENT_SCHEMA_V2
        );
        let encoded = serde_json::to_vec(&certificate).expect("certificate must serialize");
        let certificate: ModelProgramRefinementCertificate =
            serde_json::from_slice(&encoded).expect("current certificate must deserialize");
        recheck_model_program_refinement(
            &certificate,
            &fixture_bytes(),
            0,
            &LiteralInvocation::closed(vec![], 0),
            MODEL_SOURCE,
            "RefinementFixture.Model",
            REFINEMENT_SOURCE,
            "RefinementFixture.Projection",
            "RefinementFixture.ProgramRefinesModel",
        )
        .expect("fresh replay accepts exact program/model/projection/proof inputs");
    }

    #[test]
    fn model_projection_proof_and_artifact_splices_fail_closed() {
        let certificate = certify();
        let invocation = LiteralInvocation::closed(vec![], 0);
        assert!(matches!(
            recheck_model_program_refinement(
                &certificate,
                &fixture_bytes(),
                0,
                &invocation,
                &MODEL_SOURCE.replace("ProgramAbstraction", "OtherAbstraction"),
                "RefinementFixture.Model",
                REFINEMENT_SOURCE,
                "RefinementFixture.Projection",
                "RefinementFixture.ProgramRefinesModel",
            ),
            Err(ModelProgramRefinementError::ModelSourceMismatch)
        ));
        assert!(matches!(
            recheck_model_program_refinement(
                &certificate,
                &fixture_bytes(),
                0,
                &invocation,
                MODEL_SOURCE,
                "RefinementFixture.Model",
                &REFINEMENT_SOURCE.replace("Or.inr rfl", "Or.inl rfl"),
                "RefinementFixture.Projection",
                "RefinementFixture.ProgramRefinesModel",
            ),
            Err(ModelProgramRefinementError::RefinementSourceMismatch)
        ));

        let mut tampered = certificate.clone();
        tampered.theorems[0].proof_term.push(0);
        assert!(matches!(
            recheck_model_program_refinement(
                &tampered,
                &fixture_bytes(),
                0,
                &invocation,
                MODEL_SOURCE,
                "RefinementFixture.Model",
                REFINEMENT_SOURCE,
                "RefinementFixture.Projection",
                "RefinementFixture.ProgramRefinesModel",
            ),
            Err(ModelProgramRefinementError::ArtifactMismatch { field: "proof term", .. })
        ));

        let mut wrong_schema = certificate.clone();
        wrong_schema.schema = MODEL_PROGRAM_REFINEMENT_SCHEMA_V1.to_owned();
        assert!(matches!(
            recheck_model_program_refinement(
                &wrong_schema,
                &fixture_bytes(),
                0,
                &invocation,
                MODEL_SOURCE,
                "RefinementFixture.Model",
                REFINEMENT_SOURCE,
                "RefinementFixture.Projection",
                "RefinementFixture.ProgramRefinesModel",
            ),
            Err(ModelProgramRefinementError::SchemaMismatch { .. })
        ));

        let mut retired_child = certificate.clone();
        retired_child.literal.schema =
            crate::literal_refinement::LITERAL_REFINEMENT_SCHEMA_V1.to_owned();
        assert!(matches!(
            recheck_model_program_refinement(
                &retired_child,
                &fixture_bytes(),
                0,
                &invocation,
                MODEL_SOURCE,
                "RefinementFixture.Model",
                REFINEMENT_SOURCE,
                "RefinementFixture.Projection",
                "RefinementFixture.ProgramRefinesModel",
            ),
            Err(ModelProgramRefinementError::Literal(
                LiteralRefinementError::SchemaMismatch { .. }
            ))
        ));

        let mut unknown_parent =
            serde_json::to_value(&certificate).expect("certificate must serialize");
        unknown_parent
            .as_object_mut()
            .expect("certificate is an object")
            .insert("future_authority".to_owned(), serde_json::json!(true));
        assert!(
            serde_json::from_value::<ModelProgramRefinementCertificate>(unknown_parent).is_err(),
            "unknown parent fields must fail closed"
        );

        let mut retired_child_wire =
            serde_json::to_value(&certificate).expect("certificate must serialize");
        retired_child_wire["literal"]["schema"] =
            serde_json::json!(crate::literal_refinement::LITERAL_REFINEMENT_SCHEMA_V1);
        retired_child_wire["literal"]["invocation"]["next_aggregate"] = serde_json::json!(0);
        assert!(
            serde_json::from_value::<ModelProgramRefinementCertificate>(retired_child_wire)
                .is_err(),
            "a parent must not deserialize the retired child invocation shape"
        );

        let mut wrong_set = certificate.clone();
        wrong_set.theorems.swap(0, 1);
        assert!(matches!(
            recheck_model_program_refinement(
                &wrong_set,
                &fixture_bytes(),
                0,
                &invocation,
                MODEL_SOURCE,
                "RefinementFixture.Model",
                REFINEMENT_SOURCE,
                "RefinementFixture.Projection",
                "RefinementFixture.ProgramRefinesModel",
            ),
            Err(ModelProgramRefinementError::TheoremSetMismatch)
        ));

        let mut child_splice = certificate.clone();
        child_splice.literal.module_bytes.push(0);
        assert!(matches!(
            recheck_model_program_refinement(
                &child_splice,
                &fixture_bytes(),
                0,
                &invocation,
                MODEL_SOURCE,
                "RefinementFixture.Model",
                REFINEMENT_SOURCE,
                "RefinementFixture.Projection",
                "RefinementFixture.ProgramRefinesModel",
            ),
            Err(ModelProgramRefinementError::Literal(LiteralRefinementError::ModuleMismatch))
        ));
    }

    #[test]
    fn namespace_relative_declarations_cannot_shadow_requested_root_names() {
        let error = check_fixture_units(
            MODEL_SOURCE,
            "RefinementFixture.Model",
            &namespace_shadow_refinement_source(),
            "RefinementFixture.Projection",
            "RefinementFixture.ProgramRefinesModel",
        )
        .expect_err("nested attacker declarations cannot substitute for missing root declarations");
        assert!(matches!(error, ModelProgramRefinementError::Clean(_)), "{error}");
    }

    #[test]
    fn ambient_literal_names_cannot_change_independently_decoded_model() {
        let error = check_fixture_units(
            CONTEXT_SENSITIVE_MODEL_SOURCE,
            "Trust.LiteralRefinement.ContextAttack.Model",
            "",
            "Missing.Projection",
            "Missing.Refinement",
        )
        .expect_err("a context-sensitive helper must not change the composed model");
        assert_eq!(error, ModelProgramRefinementError::ComposedModelMismatch);
    }

    #[test]
    fn unclosed_authored_namespace_cannot_capture_fixed_wrapper() {
        let error = check_fixture_units(
            MODEL_SOURCE,
            "RefinementFixture.Model",
            &wrapper_capture_refinement_source(),
            "RefinementFixture.Projection",
            "RefinementFixture.ProgramRefinesModel",
        )
        .expect_err("the fixed wrapper must be parsed as an isolated root unit");
        assert!(matches!(error, ModelProgramRefinementError::Clean(_)), "{error}");
    }

    #[test]
    fn false_forward_simulation_is_rejected() {
        let false_proof = REFINEMENT_SOURCE.replace("Or.inr rfl", "Or.inl rfl");
        let error = check_fixture_units(
            MODEL_SOURCE,
            "RefinementFixture.Model",
            &false_proof,
            "RefinementFixture.Projection",
            "RefinementFixture.ProgramRefinesModel",
        )
        .expect_err("an invalid abstract-step branch cannot certify");
        assert!(matches!(error, ModelProgramRefinementError::Clean(_)), "{error}");
    }

    #[test]
    fn declaration_name_injection_is_rejected_before_elaboration() {
        let bytes = fixture_bytes();
        assert!(matches!(
            certify_model_program_refinement(
                &bytes,
                0,
                &LiteralInvocation::closed(vec![], 0),
                MODEL_SOURCE,
                "RefinementFixture.Model)\naxiom forged : False",
                REFINEMENT_SOURCE,
                "RefinementFixture.Projection",
                "RefinementFixture.ProgramRefinesModel",
            ),
            Err(ModelProgramRefinementError::InvalidDeclarationName {
                role: "model definition",
                ..
            })
        ));
    }

    #[test]
    fn declaration_name_gate_matches_clean_unescaped_identifier_shape() {
        for name in ["_private.Model", "Δ.Model'", "Model.pred?", "Model.bang!"] {
            validate_declaration_name("fixture", name)
                .unwrap_or_else(|error| panic!("valid Clean name `{name}` declined: {error}"));
        }
        for name in [
            "",
            ".Model",
            "Model.",
            "Model..Proof",
            "7Model",
            "Model-name",
            "Model\naxiom forged : False",
            "Model.ˢ",
            "_root_.Model",
            "Model._root_.Proof",
        ] {
            assert!(matches!(
                validate_declaration_name("fixture", name),
                Err(ModelProgramRefinementError::InvalidDeclarationName { .. })
            ));
        }
    }

    /// Trust (Clean R80 item 2; `docs/DECISION_QUEUE.md` R80-CONSUMERS-1): the
    /// authored refinement is elaborated in a run of its own, so the command form
    /// of `[implemented_by]` may bind only its own declarations; the preludes',
    /// the generated program's and the authored model's are imported to it, and
    /// Lean refuses them as imported. Each source first binds a declaration of
    /// its own, the control: had that been refused, the refusal would name it.
    /// Before the fix every unit of the composed context shared the cached
    /// prelude's run, and both sources certified.
    #[test]
    fn authored_refinement_cannot_rebind_an_earlier_unit_declaration() {
        const OWN: &str = "def mySlow (n : Nat) : Nat := n + 2\n\
                           def myFast (n : Nat) : Nat := n + 1\n\
                           attribute [implemented_by myFast] mySlow\n";
        let finite_prelude = format!(
            "{REFINEMENT_SOURCE}\n{OWN}\
             def myProjection (value : Trust.Temporal.FiniteModel.Value) : Nat := 0\n\
             attribute [implemented_by myProjection] \
             Trust.Temporal.FiniteModel.valueNatProjection\n"
        );
        let model = format!(
            "{REFINEMENT_SOURCE}\n{OWN}\
             def myX : Trust.Temporal.FiniteModel.ScalarExpr := \
             Trust.Temporal.FiniteModel.ScalarExpr.var \"y\"\n\
             attribute [implemented_by myX] RefinementFixture.X\n"
        );
        let outcome = |refinement: &str| {
            check_fixture_units(
                MODEL_SOURCE,
                "RefinementFixture.Model",
                refinement,
                "RefinementFixture.Projection",
                "RefinementFixture.ProgramRefinesModel",
            )
            .map(|_| ())
        };
        let imported = |declaration: &str| {
            Err(ModelProgramRefinementError::Clean(CleanTemporalCertificateError::Elaborate {
                unit: "authored model/program refinement",
                detail: format!(
                    "Cannot add attribute `[implemented_by]` to declaration `{declaration}` \
                     because it is in an imported module"
                ),
            }))
        };
        assert_eq!(
            [outcome(&finite_prelude), outcome(&model)],
            [
                imported("Trust.Temporal.FiniteModel.valueNatProjection"),
                imported("RefinementFixture.X"),
            ]
        );
    }
}
