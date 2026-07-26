//! Fresh-context Clean proposition routing into ty.
//!
//! The first applied-claim route is a deterministic natural-number countdown.
//! Unlike the old macro surface, the authored object includes the transition
//! system and propositions applied to that system.  A generated, canonical
//! Clean image is elaborated in the same fresh environment, and the kernel
//! checks transport terms from those exact canonical claims to the exact
//! authored claims.  A small, reviewed Rust adapter then emits the corresponding
//! byte-exact ty countdown image, which ty certifies; that adapter is part of the
//! trusted computing base.  There is not yet a kernel theorem proving the
//! Clean-to-ty translation itself.  A second source image with `Buggy == 1` must
//! produce an independently replayed invariant counterexample.

use clean_kernel::env::Environment;
use clean_kernel::expr::{BinderInfo, Expr, ExprKind, Literal};
use clean_kernel::name::Name;
use clean_kernel::{ConstantKind, FVarId};

use crate::certified_temporal::{
    CertifiedTemporalError, CertifiedTemporalEvidence, certify_liveness_with_ty,
    recheck_certified_temporal_evidence,
};
use crate::clean_surface::{CleanTemporalCertificateError, elaborate_temporal_definitions};

/// Schema for a Clean-claim-bound, TCB-translated ty countdown bundle.
pub const CLEAN_TY_COUNTDOWN_SCHEMA_V2: &str = "trust.clean-ty-countdown/v2";

/// Serialized type and value of one freshly elaborated Clean definition.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CleanDefinitionArtifact {
    pub type_expr: Vec<u8>,
    pub value_expr: Vec<u8>,
}

/// A kernel-checked implication from the exact canonical engine claim to the
/// exact proposition authored by the user.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CleanClaimTransport {
    pub engine_claim: Vec<u8>,
    pub authored_claim: Vec<u8>,
    pub transport_type: Vec<u8>,
    pub transport_proof: Vec<u8>,
}

/// Exact authored machine/claims plus independently replayed ty evidence.
///
/// The Clean claim transports are kernel-checked. The restricted countdown
/// translation into `spec_src` is performed by this reviewed adapter and is TCB,
/// not a kernel proof relating the two semantic representations.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CleanTyCountdownCertificate {
    pub schema: String,
    /// Byte-exact authored Clean source.
    pub clean_source: String,
    /// Fully qualified positive `Nat` definition.
    pub start_definition: String,
    /// Fully qualified `StateMachine Nat` definition.
    pub machine_definition: String,
    /// Fully qualified applied safety proposition (`M ⊨ □P`).
    pub safety_claim_definition: String,
    /// Fully qualified applied liveness proposition with an explicit WF premise.
    pub liveness_claim_definition: String,
    pub start_artifact: CleanDefinitionArtifact,
    pub machine_artifact: CleanDefinitionArtifact,
    pub safety_claim_artifact: CleanDefinitionArtifact,
    pub liveness_claim_artifact: CleanDefinitionArtifact,
    /// Kernel transports pin Init, Next, `[Next]` stutter closure, the exact
    /// non-stuttering weak-fairness premise, and the selected properties.
    pub safety_transport: CleanClaimTransport,
    pub liveness_transport: CleanClaimTransport,
    /// Exact TCB-generated ty-internal source/config for `Buggy == 0`.
    pub spec_src: String,
    pub config_src: String,
    pub safety_evidence: CertifiedTemporalEvidence,
    pub liveness_evidence: CertifiedTemporalEvidence,
    /// Exact `Buggy == 1` input and replayable negative evidence.
    pub buggy_spec_src: String,
    pub buggy_config_src: String,
    pub buggy_counterexample_json: String,
}

/// Fail-closed Clean→ty routing errors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CleanTyCountdownError {
    Clean(CleanTemporalCertificateError),
    Definition(String),
    Temporal(CertifiedTemporalError),
    ArtifactMismatch(String),
}

impl std::fmt::Display for CleanTyCountdownError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Clean(error) => write!(formatter, "Clean temporal source declined: {error}"),
            Self::Definition(detail) => {
                write!(formatter, "unsupported Clean countdown claim: {detail}")
            }
            Self::Temporal(error) => write!(formatter, "ty temporal evidence declined: {error}"),
            Self::ArtifactMismatch(detail) => {
                write!(formatter, "Clean→ty artifact mismatch: {detail}")
            }
        }
    }
}

impl std::error::Error for CleanTyCountdownError {}

impl From<CleanTemporalCertificateError> for CleanTyCountdownError {
    fn from(error: CleanTemporalCertificateError) -> Self {
        Self::Clean(error)
    }
}

impl From<CertifiedTemporalError> for CleanTyCountdownError {
    fn from(error: CertifiedTemporalError) -> Self {
        Self::Temporal(error)
    }
}

#[derive(Clone)]
struct Definition {
    type_: Expr,
    value: Expr,
}

fn definition(environment: &Environment, name: &str) -> Result<Definition, CleanTyCountdownError> {
    let declaration = environment
        .get_const(&Name::from_string(name))
        .ok_or_else(|| CleanTyCountdownError::Definition(format!("missing `{name}`")))?;
    if declaration.kind != ConstantKind::Definition {
        return Err(CleanTyCountdownError::Definition(format!(
            "`{name}` is {:?}, not a definition",
            declaration.kind
        )));
    }
    Ok(Definition {
        type_: declaration.type_.clone(),
        value: declaration
            .value
            .clone()
            .ok_or_else(|| CleanTyCountdownError::Definition(format!("`{name}` has no value")))?,
    })
}

fn encoded(expression: &Expr) -> Result<Vec<u8>, CleanTyCountdownError> {
    serde_json::to_vec(expression)
        .map_err(|error| CleanTyCountdownError::ArtifactMismatch(error.to_string()))
}

fn artifact(definition: &Definition) -> Result<CleanDefinitionArtifact, CleanTyCountdownError> {
    Ok(CleanDefinitionArtifact {
        type_expr: encoded(&definition.type_)?,
        value_expr: encoded(&definition.value)?,
    })
}

fn start_value(
    definition: &Definition,
    environment: &Environment,
) -> Result<u64, CleanTyCountdownError> {
    let checker = clean_kernel::tc::TypeChecker::with_mode(environment, environment.mode());
    if !checker.is_def_eq(&definition.type_, &Expr::const_(Name::from_string("Nat"), vec![])) {
        return Err(CleanTyCountdownError::Definition(
            "start definition must have type Nat".to_owned(),
        ));
    }
    // Clean elaborates an authored numeral through `OfNat.ofNat`; the exact
    // kernel expression is intentionally retained in the replay artifact, but
    // the restricted countdown adapter must inspect its kernel-normal form.
    // Matching the raw surface elaboration here made this lane depend on an
    // elaborator implementation detail and broke as soon as Clean stopped
    // eagerly reducing Nat numerals.
    let normalized_value = checker.whnf(&definition.value);
    match normalized_value.kind() {
        ExprKind::Lit(Literal::Nat(value)) => value.to_string().parse::<u64>().map_err(|_| {
            CleanTyCountdownError::Definition("start value does not fit in u64".to_owned())
        }),
        other => Err(CleanTyCountdownError::Definition(format!(
            "start definition must be a Nat literal, got {other:?}"
        ))),
    }
}

const CANONICAL_NAMESPACE: &str = "Trust.Temporal.R5CanonicalCountdown";

fn canonical_clean_source(start: u64) -> String {
    format!(
        r#"
namespace Trust
namespace Temporal
namespace R5CanonicalCountdown

def Machine : StateMachine Nat := {{
  init := fun s => s = {start},
  next := fun s s' => Nat.le 1 s ∧ s' = Nat.sub s 1
}}

def SafetyFormula : Formula Nat :=
  □ (fun b => Nat.le 0 (b 0) ∧ Nat.le (b 0) {start})
def LivenessFormula : Formula Nat := ◇ (fun b => b 0 = 0)

def SafetyClaim : Prop := Machine ⊨ SafetyFormula
def LivenessClaim : Prop :=
  SatisfiesUnderWeakFairness Machine LivenessFormula

end R5CanonicalCountdown
end Temporal
end Trust
"#
    )
}

fn combined_environment(
    clean_source: &str,
    start: u64,
) -> Result<Environment, CleanTyCountdownError> {
    let canonical = canonical_clean_source(start);
    if clean_source.contains(CANONICAL_NAMESPACE) {
        return Err(CleanTyCountdownError::Definition(
            "authored source uses the reserved canonical bridge namespace".to_owned(),
        ));
    }
    Ok(elaborate_temporal_definitions(&format!("{clean_source}\n{canonical}"))?)
}

fn claim_transport(
    environment: &Environment,
    engine_claim: &Definition,
    authored_claim: &Definition,
    label: &str,
) -> Result<CleanClaimTransport, CleanTyCountdownError> {
    let checker = clean_kernel::tc::TypeChecker::with_mode(environment, environment.mode());
    let prop = Expr::prop();
    if !checker.is_def_eq(&engine_claim.type_, &prop)
        || !checker.is_def_eq(&authored_claim.type_, &prop)
    {
        return Err(CleanTyCountdownError::Definition(format!(
            "{label} claim definitions must have type Prop"
        )));
    }

    // `λ h : EngineClaim, h : AuthoredClaim` kernel-checks iff the complete
    // applied claims are definitionally equal.  This pins more than a digest:
    // changing machine Init/Next, Runs stutter closure, WF's non-stuttering
    // action, the property, or the start literal makes the proof ill-typed.
    let hypothesis_id = FVarId::new(0xF500_0000_0000_0001);
    let hypothesis = Expr::fvar(hypothesis_id);
    let proof = Expr::lam(
        BinderInfo::Default,
        engine_claim.value.clone(),
        hypothesis.abstract_fvar(hypothesis_id),
    );
    let type_ = Expr::arrow(engine_claim.value.clone(), authored_claim.value.clone());
    checker.check_type(&proof, &type_).map_err(|error| {
        CleanTyCountdownError::Definition(format!(
            "{label} is not the exact canonical applied countdown claim: {error}"
        ))
    })?;

    Ok(CleanClaimTransport {
        engine_claim: encoded(&engine_claim.value)?,
        authored_claim: encoded(&authored_claim.value)?,
        transport_type: encoded(&type_)?,
        transport_proof: encoded(&proof)?,
    })
}

fn countdown_spec(start: u64, buggy: u64) -> String {
    let bad = start.saturating_add(1);
    // Keep the committed image inside ty's independently checked deterministic
    // countdown fragment.  This reviewed translation template is part of the
    // TCB: exact replay binds its output, but no kernel theorem currently proves
    // it equivalent to the canonical Clean machine. The mutation image is
    // derived by this same bridge
    // and changes the transition itself: ty's no-AY liveness lanes currently
    // decline an otherwise equivalent `IF Buggy = ...` transition.  `Buggy`
    // therefore labels the two byte-exact images; it is not a configuration
    // dial used by `Next`.  Replay pins the resulting relation byte-for-byte.
    let next = if buggy == 0 { "x > 0 /\\ x' = x - 1".to_owned() } else { format!("x' = {bad}") };
    format!(
        "---- MODULE TrustCleanCountdown ----\n\
VARIABLE x\n\
Buggy == {buggy}\n\
Init == x = {start}\n\
Next == {next}\n\
Safe == x >= 0 /\\ x <= {start}\n\
ReachesZero == <>(x = 0)\n\
Measure == x\n\
Spec == Init /\\ [][Next]_x /\\ WF_x(Next)\n\
====\n"
    )
}

const COUNTDOWN_CONFIG: &str = "SPECIFICATION Spec\nINVARIANT Safe\nCHECK_DEADLOCK FALSE\n";
const COUNTDOWN_REPLAY_CONFIG: &str =
    "INIT Init\nNEXT Next\nINVARIANT Safe\nCHECK_DEADLOCK FALSE\n";

fn safety_evidence(spec_src: &str) -> Result<CertifiedTemporalEvidence, CleanTyCountdownError> {
    let _ty_transaction = crate::in_process_ty_transaction_lock();
    let mut config = tla_check::Config::parse(COUNTDOWN_CONFIG)
        .map_err(|error| CleanTyCountdownError::Definition(format!("{error:?}")))?;
    config.init = Some("Init".to_owned());
    config.next = Some("Next".to_owned());
    let fixpoint =
        tla_check::explicit_fixpoint_cert::certify_explicit_state_spec(spec_src, &config)
            .ok_or_else(|| {
                CleanTyCountdownError::Temporal(CertifiedTemporalError::Declined(
                    "explicit safety fixpoint declined the Clean countdown".to_owned(),
                ))
            })?;
    if !tla_check::explicit_fixpoint_cert::verify_explicit_state_cert(&fixpoint) {
        return Err(CleanTyCountdownError::Temporal(CertifiedTemporalError::Declined(
            "fresh countdown safety fixpoint failed kernel self-check".to_owned(),
        )));
    }
    let raw =
        tla_check::cert::build_explicit_fixpoint_certificate(spec_src, &config, fixpoint).to_json();
    Ok(recheck_certified_temporal_evidence(&raw, spec_src, COUNTDOWN_CONFIG, &["Safe"], None)?)
}

fn buggy_counterexample(spec_src: &str, config_src: &str) -> Result<String, CleanTyCountdownError> {
    let _ty_transaction = crate::in_process_ty_transaction_lock();
    let config = tla_check::Config::parse(config_src)
        .map_err(|error| CleanTyCountdownError::Definition(format!("{error:?}")))?;
    let tree = tla_core::parse_to_syntax_tree(spec_src);
    let module = tla_core::lower(tla_core::FileId(0), &tree).module.ok_or_else(|| {
        CleanTyCountdownError::Definition("Buggy=1 module failed to lower".to_owned())
    })?;
    let result = tla_check::check_module(&module, &config);
    let envelope = tla_check::verdict::build_violation_envelope(
        spec_src,
        Some(config_src),
        &config,
        &result,
        tla_check::verdict::Completeness::Exhaustive,
        tla_check::verdict::ProducerIdentity::current(),
    )
    .ok_or_else(|| {
        CleanTyCountdownError::Temporal(CertifiedTemporalError::Declined(format!(
            "Buggy=1 did not produce a replayable invariant violation: {result:?}"
        )))
    })?;
    let json = envelope.to_json();
    recheck_buggy_counterexample_locked(&json, spec_src, config_src)?;
    Ok(json)
}

fn recheck_buggy_counterexample(
    raw: &str,
    expected_spec_src: &str,
    expected_config_src: &str,
) -> Result<(), CleanTyCountdownError> {
    let _ty_transaction = crate::in_process_ty_transaction_lock();
    recheck_buggy_counterexample_locked(raw, expected_spec_src, expected_config_src)
}

fn recheck_buggy_counterexample_locked(
    raw: &str,
    expected_spec_src: &str,
    expected_config_src: &str,
) -> Result<(), CleanTyCountdownError> {
    let envelope = tla_check::verdict::VerdictEnvelope::from_json(raw).map_err(|error| {
        CleanTyCountdownError::ArtifactMismatch(format!("invalid Buggy=1 envelope: {error}"))
    })?;
    if envelope.spec_src != expected_spec_src
        || envelope.config_src.as_deref() != Some(expected_config_src)
        || envelope.init.as_deref() != Some("Init")
        || envelope.next.as_deref() != Some("Next")
        || envelope.invariants != vec!["Safe".to_owned()]
        || !matches!(envelope.kind, tla_check::verdict::ViolationKind::Invariant)
        || envelope.violated.as_deref() != Some("Safe")
    {
        return Err(CleanTyCountdownError::ArtifactMismatch(
            "Buggy=1 envelope is not bound to the canonical Safe violation".to_owned(),
        ));
    }
    let report = tla_check::verdict::verify_violation_envelope(&envelope);
    if !matches!(report.verdict, tla_check::verdict::VerdictVerdict::Verified) {
        return Err(CleanTyCountdownError::ArtifactMismatch(format!(
            "Buggy=1 counterexample replay declined: {}",
            report.detail
        )));
    }
    Ok(())
}

struct FreshClaims {
    start: Definition,
    machine: Definition,
    safety_claim: Definition,
    liveness_claim: Definition,
    safety_transport: CleanClaimTransport,
    liveness_transport: CleanClaimTransport,
    start_value: u64,
}

fn fresh_claims(
    clean_source: &str,
    start_definition: &str,
    machine_definition: &str,
    safety_claim_definition: &str,
    liveness_claim_definition: &str,
) -> Result<FreshClaims, CleanTyCountdownError> {
    // First obtain and validate Start without trusting any generated bridge
    // declaration.  Then elaborate source + the start-specialized canonical
    // image together in a second fresh environment.
    let authored_only = elaborate_temporal_definitions(clean_source)?;
    let initial_start = definition(&authored_only, start_definition)?;
    let initial_value = start_value(&initial_start, &authored_only)?;

    fresh_claims_with_expected_start(
        clean_source,
        start_definition,
        machine_definition,
        safety_claim_definition,
        liveness_claim_definition,
        initial_value,
    )
}

/// Validate all authored/canonical bridge semantics against an expected Start.
/// Production obtains that value from a source-only environment; the combined
/// environment below independently rechecks the exact value before using it.
/// Keeping this step separate lets mutation tests exercise every production
/// transport check with a known fixture Start without rebuilding an otherwise
/// discarded source-only environment for each mutation.
fn fresh_claims_with_expected_start(
    clean_source: &str,
    start_definition: &str,
    machine_definition: &str,
    safety_claim_definition: &str,
    liveness_claim_definition: &str,
    initial_value: u64,
) -> Result<FreshClaims, CleanTyCountdownError> {
    if initial_value == 0 || initial_value == u64::MAX {
        return Err(CleanTyCountdownError::Definition(
            "start must be in 1..u64::MAX for the liveness and mutation controls".to_owned(),
        ));
    }

    let environment = combined_environment(clean_source, initial_value)?;
    let start = definition(&environment, start_definition)?;
    if start_value(&start, &environment)? != initial_value {
        return Err(CleanTyCountdownError::Definition(
            "start changed while constructing the canonical bridge".to_owned(),
        ));
    }
    let machine = definition(&environment, machine_definition)?;
    let safety_claim = definition(&environment, safety_claim_definition)?;
    let liveness_claim = definition(&environment, liveness_claim_definition)?;
    let engine_safety =
        definition(&environment, "Trust.Temporal.R5CanonicalCountdown.SafetyClaim")?;
    let engine_liveness =
        definition(&environment, "Trust.Temporal.R5CanonicalCountdown.LivenessClaim")?;
    let safety_transport =
        claim_transport(&environment, &engine_safety, &safety_claim, "safety claim")?;
    let liveness_transport =
        claim_transport(&environment, &engine_liveness, &liveness_claim, "liveness claim")?;

    // Requiring the named machine to be the one unfolded by both claim
    // transports prevents a caller from passing an unrelated decorative
    // machine definition while the propositions name the canonical one.
    let canonical_machine =
        definition(&environment, "Trust.Temporal.R5CanonicalCountdown.Machine")?;
    let checker = clean_kernel::tc::TypeChecker::with_mode(&environment, environment.mode());
    if !checker.is_def_eq(&machine.type_, &canonical_machine.type_)
        || !checker.is_def_eq(&machine.value, &canonical_machine.value)
    {
        return Err(CleanTyCountdownError::Definition(
            "named machine is not the exact canonical countdown Init/Next".to_owned(),
        ));
    }
    if !expression_mentions(&safety_claim.value, machine_definition)
        || !expression_mentions(&liveness_claim.value, machine_definition)
    {
        return Err(CleanTyCountdownError::Definition(
            "both applied claims must name the selected authored machine".to_owned(),
        ));
    }

    Ok(FreshClaims {
        start,
        machine,
        safety_claim,
        liveness_claim,
        safety_transport,
        liveness_transport,
        start_value: initial_value,
    })
}

fn expression_mentions(expression: &Expr, expected_name: &str) -> bool {
    match expression.kind() {
        ExprKind::Const(name, _) => name.to_string() == expected_name,
        ExprKind::App(function, argument) => {
            expression_mentions(function, expected_name)
                || expression_mentions(argument, expected_name)
        }
        ExprKind::Lam(_, domain, body) | ExprKind::Pi(_, domain, body) => {
            expression_mentions(domain, expected_name) || expression_mentions(body, expected_name)
        }
        ExprKind::Let(_, type_, value, body, _) => {
            expression_mentions(type_, expected_name)
                || expression_mentions(value, expected_name)
                || expression_mentions(body, expected_name)
        }
        ExprKind::Proj(_, _, structure) => expression_mentions(structure, expected_name),
        ExprKind::MData(_, inner) => expression_mentions(inner, expected_name),
        _ => false,
    }
}

/// Check an exact authored Clean countdown machine plus applied `□`/`◇` claims,
/// translate it through the restricted TCB adapter, and independently replay
/// every positive and negative ty leg.
pub fn certify_clean_countdown_with_ty(
    clean_source: &str,
    start_definition: &str,
    machine_definition: &str,
    safety_claim_definition: &str,
    liveness_claim_definition: &str,
) -> Result<CleanTyCountdownCertificate, CleanTyCountdownError> {
    let _ty_transaction = crate::in_process_ty_transaction_lock();
    let fresh = fresh_claims(
        clean_source,
        start_definition,
        machine_definition,
        safety_claim_definition,
        liveness_claim_definition,
    )?;
    let spec_src = countdown_spec(fresh.start_value, 0);
    let safety_evidence = safety_evidence(&spec_src)?;
    let liveness_evidence =
        certify_liveness_with_ty(&spec_src, COUNTDOWN_CONFIG, "ReachesZero", "Measure")?;
    let buggy_spec_src = countdown_spec(fresh.start_value, 1);
    let buggy_counterexample_json = buggy_counterexample(&buggy_spec_src, COUNTDOWN_REPLAY_CONFIG)?;

    Ok(CleanTyCountdownCertificate {
        schema: CLEAN_TY_COUNTDOWN_SCHEMA_V2.to_owned(),
        clean_source: clean_source.to_owned(),
        start_definition: start_definition.to_owned(),
        machine_definition: machine_definition.to_owned(),
        safety_claim_definition: safety_claim_definition.to_owned(),
        liveness_claim_definition: liveness_claim_definition.to_owned(),
        start_artifact: artifact(&fresh.start)?,
        machine_artifact: artifact(&fresh.machine)?,
        safety_claim_artifact: artifact(&fresh.safety_claim)?,
        liveness_claim_artifact: artifact(&fresh.liveness_claim)?,
        safety_transport: fresh.safety_transport,
        liveness_transport: fresh.liveness_transport,
        spec_src,
        config_src: COUNTDOWN_CONFIG.to_owned(),
        safety_evidence,
        liveness_evidence,
        buggy_spec_src,
        buggy_config_src: COUNTDOWN_REPLAY_CONFIG.to_owned(),
        buggy_counterexample_json,
    })
}

/// Replay a Clean/ty bundle from exact source in fresh environments.
///
/// Replay rechecks both sides and the adapter's exact output; it does not turn
/// the TCB translation into a kernel-checked cross-language theorem.
pub fn recheck_clean_countdown_with_ty(
    certificate: &CleanTyCountdownCertificate,
    expected_clean_source: &str,
) -> Result<(), CleanTyCountdownError> {
    let _ty_transaction = crate::in_process_ty_transaction_lock();
    if certificate.schema != CLEAN_TY_COUNTDOWN_SCHEMA_V2 {
        return Err(CleanTyCountdownError::ArtifactMismatch(format!(
            "unsupported schema `{}`",
            certificate.schema
        )));
    }
    if certificate.clean_source != expected_clean_source {
        return Err(CleanTyCountdownError::ArtifactMismatch(
            "authored Clean source changed".to_owned(),
        ));
    }
    let fresh = fresh_claims(
        expected_clean_source,
        &certificate.start_definition,
        &certificate.machine_definition,
        &certificate.safety_claim_definition,
        &certificate.liveness_claim_definition,
    )?;
    if artifact(&fresh.start)? != certificate.start_artifact
        || artifact(&fresh.machine)? != certificate.machine_artifact
        || artifact(&fresh.safety_claim)? != certificate.safety_claim_artifact
        || artifact(&fresh.liveness_claim)? != certificate.liveness_claim_artifact
        || fresh.safety_transport != certificate.safety_transport
        || fresh.liveness_transport != certificate.liveness_transport
    {
        return Err(CleanTyCountdownError::ArtifactMismatch(
            "fresh Clean elaboration or kernel transport differs".to_owned(),
        ));
    }
    if countdown_spec(fresh.start_value, 0) != certificate.spec_src
        || certificate.config_src != COUNTDOWN_CONFIG
        || countdown_spec(fresh.start_value, 1) != certificate.buggy_spec_src
        || certificate.buggy_config_src != COUNTDOWN_REPLAY_CONFIG
    {
        return Err(CleanTyCountdownError::ArtifactMismatch(
            "TCB-generated ty semantic input differs".to_owned(),
        ));
    }

    let replayed_safety = recheck_certified_temporal_evidence(
        &certificate.safety_evidence.raw_certificate_json,
        &certificate.spec_src,
        &certificate.config_src,
        &["Safe"],
        None,
    )?;
    if replayed_safety != certificate.safety_evidence {
        return Err(CleanTyCountdownError::ArtifactMismatch(
            "normalized safety evidence differs from replay".to_owned(),
        ));
    }
    let replayed_liveness = recheck_certified_temporal_evidence(
        &certificate.liveness_evidence.raw_certificate_json,
        &certificate.spec_src,
        &certificate.config_src,
        &["ReachesZero"],
        Some("Measure"),
    )?;
    if replayed_liveness != certificate.liveness_evidence {
        return Err(CleanTyCountdownError::ArtifactMismatch(
            "normalized liveness evidence differs from replay".to_owned(),
        ));
    }
    recheck_buggy_counterexample(
        &certificate.buggy_counterexample_json,
        &certificate.buggy_spec_src,
        &certificate.buggy_config_src,
    )?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::sync::OnceLock;

    use super::*;

    const SOURCE: &str = r#"
namespace Example

def Start : Nat := 4
def Countdown : Trust.Temporal.StateMachine Nat := {
  init := fun s => s = Start,
  next := fun s s' => Nat.le 1 s ∧ s' = Nat.sub s 1
}
def SafeFormula : Trust.Temporal.Formula Nat :=
  □ (fun b => Nat.le 0 (b 0) ∧ Nat.le (b 0) Start)
def LiveFormula : Trust.Temporal.Formula Nat := ◇ (fun b => b 0 = 0)
def SafeClaim : Prop := Countdown ⊨ SafeFormula
def LiveClaim : Prop :=
  Trust.Temporal.SatisfiesUnderWeakFairness Countdown LiveFormula

end Example
"#;

    fn certify(source: &str) -> Result<CleanTyCountdownCertificate, CleanTyCountdownError> {
        certify_clean_countdown_with_ty(
            source,
            "Example.Start",
            "Example.Countdown",
            "Example.SafeClaim",
            "Example.LiveClaim",
        )
    }

    fn baseline_certificate() -> &'static CleanTyCountdownCertificate {
        static CERTIFICATE: OnceLock<CleanTyCountdownCertificate> = OnceLock::new();
        CERTIFICATE.get_or_init(|| certify(SOURCE).expect("baseline countdown must certify"))
    }

    #[test]
    fn serialized_authored_machine_and_applied_claims_route_to_exact_ty_claims() {
        let encoded =
            serde_json::to_vec(baseline_certificate()).expect("countdown certificate serializes");
        let certificate: CleanTyCountdownCertificate =
            serde_json::from_slice(&encoded).expect("countdown certificate deserializes");
        let envelope =
            tla_check::verdict::VerdictEnvelope::from_json(&certificate.buggy_counterexample_json)
                .expect("counterexample envelope parses");
        assert_eq!(envelope.violated.as_deref(), Some("Safe"));
        recheck_clean_countdown_with_ty(&certificate, SOURCE)
            .expect("fresh Clean and ty replay of the deserialized bundle must agree");

        let mut wrong_schema = certificate.clone();
        wrong_schema.schema = "trust.clean-ty-countdown/unknown".to_owned();
        assert!(matches!(
            recheck_clean_countdown_with_ty(&wrong_schema, SOURCE),
            Err(CleanTyCountdownError::ArtifactMismatch(_))
        ));

        let mut wrong_source = certificate;
        wrong_source.clean_source.push('\n');
        assert!(matches!(
            recheck_clean_countdown_with_ty(&wrong_source, SOURCE),
            Err(CleanTyCountdownError::ArtifactMismatch(_))
        ));
    }

    #[test]
    fn any_semantic_component_drift_fails_closed() {
        for changed in [
            SOURCE.replace("s = Start", "s = Nat.succ Start"),
            SOURCE.replace("Nat.sub s 1", "Nat.sub s 2"),
            SOURCE.replace("Nat.le (b 0) Start", "Nat.le (b 0) (Nat.succ Start)"),
            SOURCE.replace("SatisfiesUnderWeakFairness", "Satisfies"),
            SOURCE.replace("Countdown ⊨ SafeFormula", "SafeFormula (fun _ => 0)"),
        ] {
            assert!(
                fresh_claims_with_expected_start(
                    &changed,
                    "Example.Start",
                    "Example.Countdown",
                    "Example.SafeClaim",
                    "Example.LiveClaim",
                    4,
                )
                .is_err(),
                "semantic drift unexpectedly certified:\n{changed}"
            );
        }

        let certificate = baseline_certificate();
        let changed_start = SOURCE.replace("def Start : Nat := 4", "def Start : Nat := 5");
        assert!(recheck_clean_countdown_with_ty(certificate, &changed_start).is_err());
    }

    #[test]
    fn replay_rejects_forged_transport_and_counterexample() {
        let mut certificate = baseline_certificate().clone();
        certificate.safety_transport.transport_proof =
            encoded(&Expr::bvar(0)).expect("expression serializes");
        assert!(recheck_clean_countdown_with_ty(&certificate, SOURCE).is_err());

        let mut certificate = baseline_certificate().clone();
        let mut envelope =
            tla_check::verdict::VerdictEnvelope::from_json(&certificate.buggy_counterexample_json)
                .expect("envelope parses");
        envelope.violated = Some("ReachesZero".to_owned());
        certificate.buggy_counterexample_json = envelope.to_json();
        assert!(recheck_clean_countdown_with_ty(&certificate, SOURCE).is_err());
    }
}
