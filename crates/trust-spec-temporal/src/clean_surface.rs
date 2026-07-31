//! Canonical Clean temporal-source certification.
//!
//! This module owns the positive half of the R5 surface gate: Clean definitions
//! and constructive theorem proofs using `□`, `◇`, `~>`, and `⊨` are parsed,
//! elaborated, checked by the Clean kernel, serialized as a replayable proof
//! artifact, and checked again in a fresh environment. Authored parser or
//! elaborator extensions are conservatively excluded so the canonical temporal
//! prelude remains the sole authority for those symbols. Engine discharge of
//! exact authored `□`/`◇` countdown claims is layered on this surface by
//! `clean_ty_lane`.

use std::fmt;
use std::sync::OnceLock;

use clean_elab::{
    ElabResult, FileContext, elaborate_decl_and_register_with_context, preprocess_decl_with_context,
};
use clean_kernel::ConstantKind;
use clean_kernel::env::{Environment, ProofQuality};
use clean_kernel::expr::Expr;
use clean_kernel::name::Name;
use clean_parser::{SurfaceDecl, parse_file};

/// Schema identifier for replayable Clean temporal certificates.
pub const CLEAN_TEMPORAL_CERT_SCHEMA_V1: &str = "trust.clean-temporal.cert/v1";

/// The canonical Clean temporal vocabulary loaded before authored source.
pub const CLEAN_TEMPORAL_PRELUDE: &str = include_str!("../clean/Trust/Temporal.lean");

/// Return an isolated copy of the kernel prelude.
///
/// Building Clean's hand-checked prelude is substantially more expensive than
/// cloning its persistent expression/declaration graph. The cached value is
/// never exposed for mutation: every elaboration receives an owned
/// [`Environment`] clone. Immutable expression nodes may remain shared, while
/// mutable declaration maps, registries, and transient verification state are
/// cloned so authored state cannot leak between certification or replay
/// contexts.
fn fresh_kernel_prelude_environment() -> Environment {
    static KERNEL_PRELUDE: OnceLock<Environment> = OnceLock::new();
    KERNEL_PRELUDE.get_or_init(Environment::with_prelude).clone()
}

/// Exact-source-bound, independently replayable Clean temporal proof evidence.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CleanTemporalCertificate {
    /// Versioned certificate schema.
    pub schema: String,
    /// Fully qualified theorem name registered by [`source`](Self::source).
    pub theorem: String,
    /// Exact authored Clean source used to create the proof artifact.
    pub source: String,
    /// JSON encoding of the elaborated theorem type.
    pub theorem_type: Vec<u8>,
    /// JSON encoding of the elaborated proof term.
    pub proof_term: Vec<u8>,
}

/// Fail-closed errors from Clean temporal certification or replay.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CleanTemporalCertificateError {
    /// The certificate uses an unknown schema.
    SchemaMismatch { found: String },
    /// The caller's expected source is not byte-for-byte identical.
    SourceMismatch,
    /// The requested theorem is supplied by the canonical prelude, not source.
    ReservedTheorem(String),
    /// Authored source attempted to extend the parser/elaborator surface.
    ///
    /// The temporal prelude is the sole authority for the meaning of its
    /// notation. Even an extension that currently appears unrelated is
    /// rejected because a syntax quotation or later macro rule can otherwise
    /// reinterpret `□`, `◇`, `~>`, or `⊨` before the theorem is elaborated.
    ForbiddenParserExtension { declaration: &'static str },
    /// A Clean source unit did not parse.
    Parse { unit: &'static str, detail: String },
    /// A Clean source unit did not elaborate and register.
    Elaborate { unit: &'static str, detail: String },
    /// The requested theorem was not registered.
    MissingTheorem(String),
    /// The requested declaration is not a theorem.
    NotTheorem(String),
    /// The theorem declaration has no proof term.
    MissingProof(String),
    /// The Clean kernel rejected a proof term.
    KernelRejected(String),
    /// The proof is not classified as constructive.
    NonConstructive { theorem: String, quality: Option<ProofQuality> },
    /// The theorem has an axiom in its dependency closure.
    ForbiddenAxiom { theorem: String, axioms: Vec<String> },
    /// Clean's strict reachable-provenance audit declined certification.
    CertificationRejected { theorem: String, issues: Vec<String> },
    /// A serialized expression could not be encoded or decoded.
    MalformedCertificate(String),
    /// Serialized evidence differs from fresh elaboration of the exact source.
    ArtifactMismatch(String),
}

impl fmt::Display for CleanTemporalCertificateError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SchemaMismatch { found } => {
                write!(formatter, "unsupported Clean temporal certificate schema `{found}`")
            }
            Self::SourceMismatch => {
                formatter.write_str("Clean temporal certificate source does not match")
            }
            Self::ReservedTheorem(theorem) => {
                write!(formatter, "theorem `{theorem}` belongs to the canonical temporal prelude")
            }
            Self::ForbiddenParserExtension { declaration } => write!(
                formatter,
                "authored Clean temporal source may not declare `{declaration}` parser/elaborator extensions"
            ),
            Self::Parse { unit, detail } => {
                write!(formatter, "failed to parse Clean {unit}: {detail}")
            }
            Self::Elaborate { unit, detail } => {
                write!(formatter, "failed to elaborate Clean {unit}: {detail}")
            }
            Self::MissingTheorem(theorem) => {
                write!(formatter, "Clean theorem `{theorem}` was not registered")
            }
            Self::NotTheorem(theorem) => {
                write!(formatter, "Clean declaration `{theorem}` is not a theorem")
            }
            Self::MissingProof(theorem) => {
                write!(formatter, "Clean theorem `{theorem}` has no proof term")
            }
            Self::KernelRejected(detail) => {
                write!(formatter, "Clean kernel rejected the temporal proof: {detail}")
            }
            Self::NonConstructive { theorem, quality } => write!(
                formatter,
                "Clean theorem `{theorem}` is not constructive (quality: {quality:?})"
            ),
            Self::ForbiddenAxiom { theorem, axioms } => write!(
                formatter,
                "Clean theorem `{theorem}` has a forbidden axiom closure: {axioms:?}"
            ),
            Self::CertificationRejected { theorem, issues } => write!(
                formatter,
                "Clean theorem `{theorem}` failed strict certification: {issues:?}"
            ),
            Self::MalformedCertificate(detail) => {
                write!(formatter, "malformed Clean temporal certificate: {detail}")
            }
            Self::ArtifactMismatch(detail) => {
                write!(formatter, "Clean temporal certificate artifact mismatch: {detail}")
            }
        }
    }
}

impl std::error::Error for CleanTemporalCertificateError {}

pub(crate) fn elaborate_unit(
    environment: &mut Environment,
    context: &mut FileContext,
    source: &str,
    unit: &'static str,
    authored_start: Option<usize>,
) -> Result<(), CleanTemporalCertificateError> {
    let declarations = parse_file(source).map_err(|error| {
        CleanTemporalCertificateError::Parse { unit, detail: format!("{error:?}") }
    })?;
    if let Some(authored_start) = authored_start {
        reject_authored_parser_extensions(&declarations, authored_start)?;
    }
    for declaration in &declarations {
        let processed = preprocess_decl_with_context(declaration, context);
        let result = elaborate_decl_and_register_with_context(environment, &processed, context)
            .map_err(|error| CleanTemporalCertificateError::Elaborate {
                unit,
                detail: error.to_string(),
            })?;
        let mut leaves = Vec::new();
        result.leaf_decls(&mut leaves);
        if let Some(ElabResult::Failed { name, error, .. }) =
            leaves.into_iter().find(|leaf| matches!(leaf, ElabResult::Failed { .. }))
        {
            return Err(CleanTemporalCertificateError::Elaborate {
                unit,
                detail: format!("declaration `{name}` failed: {error:?}"),
            });
        }
    }
    Ok(())
}

/// Parse an authored suffix in the same parser session as its fixed notation
/// prelude, but elaborate only the suffix into an already-prepared context.
///
/// Clean's parser registers `notation` declarations while parsing a file;
/// `FileContext` alone is not sufficient to teach a new `parse_file` call
/// about `□`, `◇`, `~>`, or `⊨`. Re-parsing the fixed prefix is cheap and
/// preserves the required parser state, while the cached kernel/environment
/// context avoids re-elaborating it. The byte boundary also lets the extension
/// gate distinguish canonical declarations from authored ones.
pub(crate) fn elaborate_suffix_with_parser_prelude(
    environment: &mut Environment,
    context: &mut FileContext,
    parser_prelude: &str,
    source: &str,
    unit: &'static str,
) -> Result<(), CleanTemporalCertificateError> {
    let mut combined = String::with_capacity(parser_prelude.len() + source.len() + 1);
    combined.push_str(parser_prelude);
    combined.push('\n');
    let authored_start = combined.len();
    combined.push_str(source);

    let declarations = parse_file(&combined).map_err(|error| {
        CleanTemporalCertificateError::Parse { unit, detail: format!("{error:?}") }
    })?;
    reject_authored_parser_extensions(&declarations, authored_start)?;
    for declaration in
        declarations.iter().filter(|declaration| declaration.span().start >= authored_start)
    {
        let processed = preprocess_decl_with_context(declaration, context);
        let result = elaborate_decl_and_register_with_context(environment, &processed, context)
            .map_err(|error| CleanTemporalCertificateError::Elaborate {
                unit,
                detail: error.to_string(),
            })?;
        let mut leaves = Vec::new();
        result.leaf_decls(&mut leaves);
        if let Some(ElabResult::Failed { name, error, .. }) =
            leaves.into_iter().find(|leaf| matches!(leaf, ElabResult::Failed { .. }))
        {
            return Err(CleanTemporalCertificateError::Elaborate {
                unit,
                detail: format!("declaration `{name}` failed: {error:?}"),
            });
        }
    }
    Ok(())
}

/// Return an isolated temporal-prelude environment together with the parser /
/// elaborator context that gives the canonical notation its meaning.
///
/// `FileContext` owns the dynamic notation registry, so caching only the kernel
/// environment would force every authored check to parse and elaborate the
/// prelude again. Both values are persistent/cloneable; callers receive owned
/// clones and cannot leak declarations or parser state into another check.
pub(crate) fn fresh_temporal_prelude_context()
-> Result<(Environment, FileContext), CleanTemporalCertificateError> {
    static TEMPORAL_PRELUDE: OnceLock<
        Result<(Environment, FileContext), CleanTemporalCertificateError>,
    > = OnceLock::new();
    TEMPORAL_PRELUDE
        .get_or_init(|| {
            let mut environment = fresh_kernel_prelude_environment();
            let mut context = FileContext::new();
            context.disable_external_import_search();
            elaborate_unit(
                &mut environment,
                &mut context,
                CLEAN_TEMPORAL_PRELUDE,
                "temporal prelude",
                None,
            )?;
            Ok((environment, context))
        })
        .clone()
}

/// Reject parser-state mutations from the authored suffix of the combined
/// prelude + source parse.
///
/// Clean's fixed-arity notation registry is populated while the file is being
/// parsed. A later declaration with the same token can therefore change the
/// AST of every following theorem even though the canonical prelude was parsed
/// first. Macro and elaborator declarations are rejected with the same policy:
/// their patterns may spell the reserved tokens through syntax quotations, so
/// accepting only declarations whose current AST looks unrelated would make
/// this gate depend on macro-expansion details. The canonical prelude's own
/// declarations have spans before `authored_start` and remain allowed.
fn reject_authored_parser_extensions(
    declarations: &[SurfaceDecl],
    authored_start: usize,
) -> Result<(), CleanTemporalCertificateError> {
    fn forbidden_kind(declaration: &SurfaceDecl, authored_start: usize) -> Option<&'static str> {
        if declaration.span().start >= authored_start {
            let kind = match declaration {
                SurfaceDecl::Syntax { .. } => Some("syntax"),
                SurfaceDecl::DeclareSyntaxCat { .. } => Some("declare_syntax_cat"),
                SurfaceDecl::Macro { .. } => Some("macro"),
                SurfaceDecl::MacroRules { .. } => Some("macro_rules"),
                SurfaceDecl::Notation { .. } => Some("notation"),
                SurfaceDecl::Elab { .. } => Some("elab"),
                SurfaceDecl::Open { scoped: true, .. } => Some("open scoped"),
                _ => None,
            };
            if kind.is_some() {
                return kind;
            }
        }

        let nested = match declaration {
            SurfaceDecl::Namespace { decls, .. }
            | SurfaceDecl::Section { decls, .. }
            | SurfaceDecl::Mutual { decls, .. } => decls.as_slice(),
            SurfaceDecl::Open { body: Some(body), .. }
            | SurfaceDecl::SetOption { body: Some(body), .. } => {
                return forbidden_kind(body, authored_start);
            }
            _ => &[],
        };
        nested.iter().find_map(|declaration| forbidden_kind(declaration, authored_start))
    }

    if let Some(declaration) =
        declarations.iter().find_map(|declaration| forbidden_kind(declaration, authored_start))
    {
        return Err(CleanTemporalCertificateError::ForbiddenParserExtension { declaration });
    }
    Ok(())
}

pub(crate) fn elaborate_temporal_definitions(
    source: &str,
) -> Result<Environment, CleanTemporalCertificateError> {
    // Dynamic notation is parser-local, so retain the fixed temporal prefix in
    // the parse while elaborating only the authored suffix into the isolated
    // clone of the cached prelude context.
    let (mut environment, mut context) = fresh_temporal_prelude_context()?;
    elaborate_suffix_with_parser_prelude(
        &mut environment,
        &mut context,
        CLEAN_TEMPORAL_PRELUDE,
        source,
        "authored source",
    )?;
    Ok(environment)
}

fn elaborate_authored_source(
    source: &str,
    theorem: &str,
) -> Result<Environment, CleanTemporalCertificateError> {
    // Keep the prelude-name collision diagnostic specific for theorem
    // certification. Generic definition elaboration below is used by the
    // Clean→ty router and remains fresh-environment checked as well.
    let (prelude_environment, _) = fresh_temporal_prelude_context()?;
    let theorem_name = Name::from_string(theorem);
    if prelude_environment.get_const(&theorem_name).is_some() {
        return Err(CleanTemporalCertificateError::ReservedTheorem(theorem.to_owned()));
    }
    elaborate_temporal_definitions(source)
}

pub(crate) fn checked_theorem<'environment>(
    environment: &'environment Environment,
    theorem: &str,
) -> Result<(&'environment Expr, &'environment Expr), CleanTemporalCertificateError> {
    let name = Name::from_string(theorem);
    let declaration = environment
        .get_const(&name)
        .ok_or_else(|| CleanTemporalCertificateError::MissingTheorem(theorem.to_owned()))?;
    if declaration.kind != ConstantKind::Theorem {
        return Err(CleanTemporalCertificateError::NotTheorem(theorem.to_owned()));
    }
    let proof = declaration
        .value
        .as_ref()
        .ok_or_else(|| CleanTemporalCertificateError::MissingProof(theorem.to_owned()))?;

    clean_kernel::tc::TypeChecker::with_mode(environment, environment.mode())
        .check_type(proof, &declaration.type_)
        .map_err(|error| CleanTemporalCertificateError::KernelRejected(error.to_string()))?;

    let quality = environment.proof_quality(&name);
    if quality != Some(ProofQuality::Constructive) {
        return Err(CleanTemporalCertificateError::NonConstructive {
            theorem: theorem.to_owned(),
            quality,
        });
    }

    let axioms = environment.axiom_deps(&name).ok_or_else(|| {
        CleanTemporalCertificateError::NonConstructive { theorem: theorem.to_owned(), quality }
    })?;
    if !axioms.is_empty() {
        return Err(CleanTemporalCertificateError::ForbiddenAxiom {
            theorem: theorem.to_owned(),
            axioms: axioms.iter().map(ToString::to_string).collect(),
        });
    }

    // A zero-domain-axiom classification is necessary but not sufficient:
    // reject unsafe, partial, structurally installed, unverified imported, or
    // otherwise non-canonical reachable declarations as well.
    let audit = environment.audit_certification(&declaration.type_, proof);
    if !audit.is_certified() {
        return Err(CleanTemporalCertificateError::CertificationRejected {
            theorem: theorem.to_owned(),
            issues: audit.issues.iter().map(|issue| format!("{issue:?}")).collect(),
        });
    }

    Ok((&declaration.type_, proof))
}

fn encode_expression(expression: &Expr) -> Result<Vec<u8>, CleanTemporalCertificateError> {
    serde_json::to_vec(expression)
        .map_err(|error| CleanTemporalCertificateError::MalformedCertificate(error.to_string()))
}

/// Parse, elaborate, and kernel-check an authored Clean temporal theorem.
///
/// The authored unit may contain ordinary definitions and theorem proofs, but
/// not parser/elaborator extensions: `syntax`, `declare_syntax_cat`, `macro`,
/// `macro_rules`, `notation`, `elab`, and `open scoped` declarations are rejected
/// conservatively, even when they appear unrelated to the temporal symbols.
/// This keeps the canonical prelude as the sole notation authority.
///
/// This path certifies the supplied proof term. It does not assert that `ty`
/// discovered or discharged the theorem and is not a replacement for the
/// independent `ty` certificate lane.
pub fn certify_clean_temporal_source(
    source: &str,
    theorem: &str,
) -> Result<CleanTemporalCertificate, CleanTemporalCertificateError> {
    let environment = elaborate_authored_source(source, theorem)?;
    let (theorem_type, proof_term) = checked_theorem(&environment, theorem)?;
    Ok(CleanTemporalCertificate {
        schema: CLEAN_TEMPORAL_CERT_SCHEMA_V1.to_owned(),
        theorem: theorem.to_owned(),
        source: source.to_owned(),
        theorem_type: encode_expression(theorem_type)?,
        proof_term: encode_expression(proof_term)?,
    })
}

/// Replay a Clean temporal certificate from the canonical prelude and exact source.
///
/// Replay uses a fresh environment, requires byte-identical source and artifacts,
/// and asks the kernel to check the serialized proof against its serialized type.
pub fn recheck_clean_temporal_certificate(
    certificate: &CleanTemporalCertificate,
    expected_source: &str,
) -> Result<(), CleanTemporalCertificateError> {
    if certificate.schema != CLEAN_TEMPORAL_CERT_SCHEMA_V1 {
        return Err(CleanTemporalCertificateError::SchemaMismatch {
            found: certificate.schema.clone(),
        });
    }
    if certificate.source != expected_source {
        return Err(CleanTemporalCertificateError::SourceMismatch);
    }

    let environment = elaborate_authored_source(expected_source, &certificate.theorem)?;
    let (fresh_type, fresh_proof) = checked_theorem(&environment, &certificate.theorem)?;
    let fresh_type = encode_expression(fresh_type)?;
    let fresh_proof = encode_expression(fresh_proof)?;
    if certificate.theorem_type != fresh_type {
        return Err(CleanTemporalCertificateError::ArtifactMismatch(
            "theorem type differs from fresh elaboration".to_owned(),
        ));
    }
    if certificate.proof_term != fresh_proof {
        return Err(CleanTemporalCertificateError::ArtifactMismatch(
            "proof term differs from fresh elaboration".to_owned(),
        ));
    }

    let stored_type: Expr = serde_json::from_slice(&certificate.theorem_type).map_err(|error| {
        CleanTemporalCertificateError::MalformedCertificate(format!(
            "invalid theorem type: {error}"
        ))
    })?;
    let stored_proof: Expr = serde_json::from_slice(&certificate.proof_term).map_err(|error| {
        CleanTemporalCertificateError::MalformedCertificate(format!("invalid proof term: {error}"))
    })?;
    clean_kernel::tc::TypeChecker::with_mode(&environment, environment.mode())
        .check_type(&stored_proof, &stored_type)
        .map_err(|error| CleanTemporalCertificateError::KernelRejected(error.to_string()))?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    const ALL_OPERATORS_SOURCE: &str = r#"
namespace Trust
namespace Temporal

theorem certified_all_operators {State : Type} (F : Formula State) :
    ((□ F) = Always F) ∧ (((◇ F) = Eventually F) ∧ ((F ~> F) = LeadsTo F F)) :=
  And.intro (box_unfolds F)
    (And.intro (diamond_unfolds F) (leadsto_unfolds F F))

end Temporal
end Trust
"#;
    const ALL_OPERATORS_THEOREM: &str = "Trust.Temporal.certified_all_operators";

    const GENERAL_FAIR_LEADSTO_SOURCE: &str = r#"
namespace GeneralTemporal

def Machine : Trust.Temporal.StateMachine Nat :=
  { init := fun _ => True, next := fun _ _ => True }

def Constraints (strong : Bool) : Trust.Temporal.FairnessConstraint Nat :=
  match strong with
  | false => Trust.Temporal.FairnessConstraint.weak Machine.next
  | true => Trust.Temporal.FairnessConstraint.strong Machine.next

def F : Trust.Temporal.Formula Nat :=
  □ ◇ (Trust.Temporal.Lift
    (Trust.Temporal.Enabled Machine.next))
def G : Trust.Temporal.Formula Nat :=
  Trust.Temporal.LiftAction Machine.next

theorem mixed_constraints_expose_weak_and_strong
    (behavior : Trust.Temporal.Behavior Nat)
    (fair : Trust.Temporal.FairFamily Constraints behavior) :
    Trust.Temporal.WeakFair Machine.next behavior ∧
      Trust.Temporal.StrongFair Machine.next behavior :=
  And.intro (fair false) (fair true)

theorem arbitrary_leads_to_under_mixed_fairness
    : Trust.Temporal.SatisfiesUnderFairness Machine Constraints (F ~> G) :=
  fun behavior _runs fair => fair true

end GeneralTemporal
"#;

    #[test]
    fn cached_kernel_prelude_matches_fresh_build_and_cannot_leak_authored_state() {
        fn constant_image(environment: &Environment) -> Vec<(String, Vec<u8>)> {
            let mut image = environment
                .constants()
                .map(|constant| {
                    (
                        constant.name.to_string(),
                        serde_json::to_vec(constant).expect("kernel declaration serializes"),
                    )
                })
                .collect::<Vec<_>>();
            image.sort_by(|left, right| left.0.cmp(&right.0));
            image
        }

        let cached_clone = fresh_kernel_prelude_environment();
        let independently_built = Environment::with_prelude();
        assert_eq!(cached_clone.mode(), independently_built.mode());
        assert_eq!(cached_clone.num_constants(), independently_built.num_constants());
        assert_eq!(cached_clone.num_inductives(), independently_built.num_inductives());
        assert_eq!(cached_clone.num_constructors(), independently_built.num_constructors());
        assert_eq!(cached_clone.num_recursors(), independently_built.num_recursors());
        assert_eq!(cached_clone.num_quotients(), independently_built.num_quotients());
        assert_eq!(
            constant_image(&cached_clone),
            constant_image(&independently_built),
            "cached and independently rebuilt kernel preludes must expose identical declarations",
        );

        const FIRST_SOURCE: &str = r#"
namespace TrustTemporalCacheIsolation
def MustNotLeak : Nat := 7
end TrustTemporalCacheIsolation
"#;
        let first = elaborate_temporal_definitions(FIRST_SOURCE)
            .expect("first isolated elaboration succeeds");
        let leaked_name = Name::from_string("TrustTemporalCacheIsolation.MustNotLeak");
        assert!(first.get_const(&leaked_name).is_some());

        const NOTATION_ATTACK: &str = r#"
prefix:100 "□" => Trust.Temporal.Eventually
"#;
        assert!(matches!(
            elaborate_temporal_definitions(NOTATION_ATTACK),
            Err(CleanTemporalCertificateError::ForbiddenParserExtension {
                declaration: "notation",
            })
        ));

        const SECOND_SOURCE: &str = r#"
namespace TrustTemporalCacheIsolation
def CanonicalBox {State : Type} (F : Trust.Temporal.Formula State) :
    Trust.Temporal.Formula State := □ F
end TrustTemporalCacheIsolation
"#;
        let second = elaborate_temporal_definitions(SECOND_SOURCE)
            .expect("a rejected notation attack cannot affect the next isolated parse");
        assert!(
            second.get_const(&leaked_name).is_none(),
            "an authored declaration from the first clone leaked into the next clone",
        );
        assert!(
            second
                .get_const(&Name::from_string("TrustTemporalCacheIsolation.CanonicalBox"))
                .is_some(),
            "canonical temporal notation must remain available after a rejected attack",
        );
    }

    #[test]
    fn serializes_and_freshly_replays_all_temporal_operators() {
        let certificate =
            certify_clean_temporal_source(ALL_OPERATORS_SOURCE, ALL_OPERATORS_THEOREM)
                .expect("authored Clean theorem must certify");
        assert!(!certificate.theorem_type.is_empty());
        assert!(!certificate.proof_term.is_empty());

        let encoded = serde_json::to_vec(&certificate).expect("certificate serializes");
        let certificate: CleanTemporalCertificate =
            serde_json::from_slice(&encoded).expect("certificate deserializes");
        recheck_clean_temporal_certificate(&certificate, ALL_OPERATORS_SOURCE)
            .expect("deserialized certificate must replay in a fresh environment");

        let mut wrong_schema = certificate.clone();
        wrong_schema.schema = "trust.clean-temporal.cert/unknown".to_owned();
        assert!(matches!(
            recheck_clean_temporal_certificate(&wrong_schema, ALL_OPERATORS_SOURCE),
            Err(CleanTemporalCertificateError::SchemaMismatch { .. })
        ));

        let mut wrong_source = certificate;
        wrong_source.source.push('\n');
        assert_eq!(
            recheck_clean_temporal_certificate(&wrong_source, ALL_OPERATORS_SOURCE),
            Err(CleanTemporalCertificateError::SourceMismatch)
        );
    }

    #[test]
    fn arbitrary_authored_leadsto_and_mixed_fairness_kernel_replay() {
        let theorem = "GeneralTemporal.arbitrary_leads_to_under_mixed_fairness";
        let certificate = certify_clean_temporal_source(GENERAL_FAIR_LEADSTO_SOURCE, theorem)
            .expect("arbitrary authored F ~> G proof under mixed action fairness must certify");
        recheck_clean_temporal_certificate(&certificate, GENERAL_FAIR_LEADSTO_SOURCE)
            .expect("the arbitrary leads-to proof must freshly kernel-replay");

        let distinction = certify_clean_temporal_source(
            GENERAL_FAIR_LEADSTO_SOURCE,
            "GeneralTemporal.mixed_constraints_expose_weak_and_strong",
        )
        .expect("the indexed family must expose genuinely distinct weak and strong obligations");
        recheck_clean_temporal_certificate(&distinction, GENERAL_FAIR_LEADSTO_SOURCE)
            .expect("the mixed weak/strong denotation proof must freshly replay");

        let drifted = GENERAL_FAIR_LEADSTO_SOURCE.replace(
            "FairnessConstraint.strong Machine.next",
            "FairnessConstraint.weak Machine.next",
        );
        assert!(
            certify_clean_temporal_source(
                &drifted,
                "GeneralTemporal.mixed_constraints_expose_weak_and_strong",
            )
            .is_err(),
            "collapsing the strong constraint to weak must invalidate the distinction proof",
        );
        assert_eq!(
            recheck_clean_temporal_certificate(&certificate, &drifted),
            Err(CleanTemporalCertificateError::SourceMismatch)
        );
    }

    #[test]
    fn replay_rejects_source_or_proof_artifact_drift() {
        let certificate =
            certify_clean_temporal_source(ALL_OPERATORS_SOURCE, ALL_OPERATORS_THEOREM)
                .expect("authored Clean theorem must certify");
        assert_eq!(
            recheck_clean_temporal_certificate(&certificate, &format!("{ALL_OPERATORS_SOURCE}\n")),
            Err(CleanTemporalCertificateError::SourceMismatch)
        );

        let mut tampered = certificate;
        tampered.proof_term = serde_json::to_vec(&Expr::bvar(0)).expect("Expr serializes");
        assert!(matches!(
            recheck_clean_temporal_certificate(&tampered, ALL_OPERATORS_SOURCE),
            Err(CleanTemporalCertificateError::ArtifactMismatch(_))
        ));
    }

    #[test]
    fn certification_rejects_axiom_backed_temporal_proof() {
        let source = r#"
namespace Trust
namespace Temporal

axiom temporal_escape {State : Type} (F : Formula State) (b : Behavior State) : (□ F) b

theorem escaped {State : Type} (F : Formula State) (b : Behavior State) : (◇ F) b :=
  box_implies_diamond F b (temporal_escape F b)

end Temporal
end Trust
"#;
        assert!(matches!(
            certify_clean_temporal_source(source, "Trust.Temporal.escaped"),
            Err(CleanTemporalCertificateError::NonConstructive { .. })
                | Err(CleanTemporalCertificateError::ForbiddenAxiom { .. })
        ));
    }

    #[test]
    fn authored_notation_cannot_shadow_any_canonical_temporal_symbol() {
        let attacks = [
            (
                "□",
                r#"
namespace Shadow
prefix:100 "□" => Trust.Temporal.Eventually
theorem forged {State : Type} (F : Trust.Temporal.Formula State) :
    (□ F) = Trust.Temporal.Eventually F := rfl
end Shadow
"#,
            ),
            (
                "◇",
                r#"
namespace Shadow
prefix:100 "◇" => Trust.Temporal.Always
theorem forged {State : Type} (F : Trust.Temporal.Formula State) :
    (◇ F) = Trust.Temporal.Always F := rfl
end Shadow
"#,
            ),
            (
                "~>",
                r#"
namespace Shadow
def FakeLeadsTo {State : Type} (F _G : Trust.Temporal.Formula State) := F
infixl:50 " ~> " => Shadow.FakeLeadsTo
theorem forged {State : Type} (F G : Trust.Temporal.Formula State) :
    (F ~> G) = F := rfl
end Shadow
"#,
            ),
            (
                "⊨",
                r#"
namespace Shadow
def FakeSatisfies {State : Type} (_M : Trust.Temporal.StateMachine State)
    (_F : Trust.Temporal.Formula State) : Prop := True
infixl:45 " ⊨ " => Shadow.FakeSatisfies
theorem forged {State : Type} (M : Trust.Temporal.StateMachine State)
    (F : Trust.Temporal.Formula State) : M ⊨ F := True.intro
end Shadow
"#,
            ),
        ];

        for (symbol, source) in attacks {
            assert_eq!(
                certify_clean_temporal_source(source, "Shadow.forged"),
                Err(CleanTemporalCertificateError::ForbiddenParserExtension {
                    declaration: "notation",
                }),
                "authored notation for `{symbol}` must fail before it can reinterpret a theorem",
            );
        }
    }

    #[test]
    fn authored_parser_and_macro_equivalents_for_temporal_symbols_fail_closed() {
        let attacks = [
            ("syntax category", "declare_syntax_cat", "declare_syntax_cat temporalShadow"),
            ("□", "syntax", r#"syntax "□" term : term"#),
            ("◇", "macro", r#"macro "◇" x:term : term => x"#),
            ("~>", "macro_rules", r#"macro_rules | `(x ~> y) => `(x)"#),
            ("⊨", "elab", r#"elab x:term "⊨" y:term : term => x"#),
        ];

        for (symbol, declaration, source) in attacks {
            assert_eq!(
                certify_clean_temporal_source(source, "missing_by_design"),
                Err(CleanTemporalCertificateError::ForbiddenParserExtension { declaration }),
                "authored `{declaration}` carrier for `{symbol}` must fail before elaboration",
            );
        }
    }

    #[test]
    fn authored_open_scoped_cannot_activate_an_alternate_notation_scope() {
        assert_eq!(
            certify_clean_temporal_source("open scoped Trust.Temporal", "missing_by_design"),
            Err(CleanTemporalCertificateError::ForbiddenParserExtension {
                declaration: "open scoped",
            }),
        );
    }

    #[test]
    fn canonical_temporal_symbols_resist_namespace_prefix_definition_shadowing() {
        const SOURCE: &str = r#"
namespace Shadow
namespace Trust
namespace Temporal

def Always {State : Type} (_F : _root_.Trust.Temporal.Formula State) :
    _root_.Trust.Temporal.Formula State :=
  fun _b => False

def Eventually {State : Type} (_F : _root_.Trust.Temporal.Formula State) :
    _root_.Trust.Temporal.Formula State :=
  fun _b => False

def LeadsTo {State : Type} (F _G : _root_.Trust.Temporal.Formula State) :
    _root_.Trust.Temporal.Formula State :=
  F

def Satisfies {State : Type} (_M : _root_.Trust.Temporal.StateMachine State)
    (_F : _root_.Trust.Temporal.Formula State) : Prop :=
  True

end Temporal
end Trust
end Shadow

namespace Shadow

theorem canonical_notation_targets {State : Type}
    (M : _root_.Trust.Temporal.StateMachine State)
    (F G : _root_.Trust.Temporal.Formula State) :
    ((□ F) = _root_.Trust.Temporal.Always F) ∧
      (((◇ F) = _root_.Trust.Temporal.Eventually F) ∧
        (((F ~> G) = _root_.Trust.Temporal.LeadsTo F G) ∧
          ((M ⊨ F) = _root_.Trust.Temporal.Satisfies M F))) :=
  And.intro rfl (And.intro rfl (And.intro rfl rfl))

end Shadow
"#;
        const THEOREM: &str = "Shadow.canonical_notation_targets";

        let certificate = certify_clean_temporal_source(SOURCE, THEOREM)
            .expect("root-qualified temporal notation must ignore namespace-prefix definitions");
        recheck_clean_temporal_certificate(&certificate, SOURCE)
            .expect("namespace-shadow regression certificate must replay in a fresh environment");
    }
}
