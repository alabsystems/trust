//! Obligation → primary-engine routing tables for the full verifier.

use trust_verifier_api::{
    DeclineClass, EngineManifest, EvidenceStatus, ObligationKind, ProofStrength, ReasoningKind,
    TrustObligation,
};

use super::policy::{
    TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY, TRUST_VC_HARDENED_NAMESPACE,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum PrimaryEngine {
    TrustWp,
    TrustVc,
    TrustMc,
    Ty,
}

pub(super) const REQUIRED_PRIMARY_ENGINES: [PrimaryEngine; 4] =
    [PrimaryEngine::TrustWp, PrimaryEngine::TrustVc, PrimaryEngine::TrustMc, PrimaryEngine::Ty];

impl PrimaryEngine {
    pub(super) fn name(self) -> &'static str {
        match self {
            Self::TrustWp => "trust-wp",
            Self::TrustVc => "trust-vc",
            Self::TrustMc => "trust-mc",
            Self::Ty => "ty",
        }
    }

    pub(super) fn matches_manifest(self, manifest: &EngineManifest) -> bool {
        manifest.name == self.name()
    }

    pub(super) fn from_trust_ir_suite_name(name: &str) -> Option<Self> {
        // Trust: accept both hyphen and underscore variants. TrustIr's
        // `NativeVerifierSuite` Display/code emits underscore (`trust_wp`)
        // while the engine manifest name uses hyphen (`trust-wp`).
        match name.to_ascii_lowercase().as_str() {
            "trust-wp" | "trust_wp" => Some(Self::TrustWp),
            "trust-vc" | "trust_vc" => Some(Self::TrustVc),
            "trust-mc" | "trust_mc" => Some(Self::TrustMc),
            _ => None,
        }
    }

    pub(super) fn requires_trust_ir_native_bundle(self) -> bool {
        matches!(self, Self::TrustWp | Self::TrustVc | Self::TrustMc)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ProofFamily {
    TrustWpFunctional,
    TrustVcOwnership,
    TrustMcReachability,
    TyTemporal,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RequiredAssurance {
    SmtBacked,
    Sound,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct ObligationRoute {
    pub(super) obligation_kind: &'static str,
    pub(super) primary: PrimaryEngine,
    pub(super) proof_family: ProofFamily,
    pub(super) minimum_assurance: RequiredAssurance,
}

impl ObligationRoute {
    pub(super) fn accepts_strength(&self, strength: &ProofStrength) -> bool {
        strength.is_publication_grade()
            && assurance_satisfies(strength, self.minimum_assurance)
            && self.accepts_reasoning(&strength.reasoning)
    }

    pub(super) fn accepts_reasoning(&self, reasoning: &ReasoningKind) -> bool {
        match self.proof_family {
            ProofFamily::TrustWpFunctional => {
                matches!(reasoning, ReasoningKind::Deductive | ReasoningKind::Inductive)
            }
            ProofFamily::TrustVcOwnership => {
                matches!(reasoning, ReasoningKind::OwnershipAnalysis | ReasoningKind::Deductive)
            }
            ProofFamily::TrustMcReachability => {
                matches!(reasoning, ReasoningKind::Chc | ReasoningKind::Pdr)
            }
            ProofFamily::TyTemporal => matches!(
                reasoning,
                ReasoningKind::TemporalModelCheck | ReasoningKind::ExplicitStateModel
            ),
        }
    }

    pub(super) fn required_strength_description(&self) -> &'static str {
        match self.proof_family {
            ProofFamily::TrustWpFunctional => "trust-wp deductive or inductive Sound+ proof",
            ProofFamily::TrustVcOwnership => {
                "trust-vc ownership-analysis or deductive Sound+ proof"
            }
            ProofFamily::TrustMcReachability => "trust-mc CHC/PDR SmtBacked+ proof",
            ProofFamily::TyTemporal => "ty temporal or explicit-state Sound+ proof",
        }
    }
}

/// Metadata key marking a body-aware VC that carries a typed `TrustSpecPredicate`
/// formula payload (mirrors `trust.vc.formula.payload` set by the compiler's
/// mir-extract). A `Postcondition` or `Precondition` obligation carrying it is a
/// body-aware VC (`¬cond ∧ body_defs`, a closed CHC-reachability query — the
/// `#[ensures]` VC and the call-site `#[requires]` VC respectively) routed to
/// trust-mc; one without it is a claim-based obligation kept on trust-wp.
const TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY: &str = "trust.vc.formula.payload";
const TRUST_VC_FORMULA_SCHEMA_METADATA_KEY: &str = "trust.vc.formula.schema";

fn obligation_has_vc_formula_payload(obligation: &TrustObligation) -> bool {
    obligation.metadata.iter().any(|entry| entry.key == TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
}

fn unique_metadata_value<'a>(obligation: &'a TrustObligation, key: &str) -> Option<&'a str> {
    let mut matches = obligation.metadata.iter().filter(|entry| entry.key == key);
    let value = matches.next()?.value.as_str();
    matches.next().is_none().then_some(value)
}

/// E4/E5 become TrustMC-owned only for the exact compiler-authored typed VC
/// envelope accepted by the TrustMC adapter. Keeping this test identical to
/// the adapter prevents a partial or forged metadata envelope from changing
/// dispatch ownership even though downstream proof admission is fail-closed.
fn is_typed_body_aware_e4_e5_obligation(obligation: &TrustObligation) -> bool {
    if !matches!(obligation.kind, ObligationKind::LoopInvariant | ObligationKind::Termination) {
        return false;
    }

    let Some(schema) = unique_metadata_value(obligation, TRUST_VC_FORMULA_SCHEMA_METADATA_KEY)
    else {
        return false;
    };
    if schema != trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION {
        return false;
    }

    let Some(payload) = unique_metadata_value(obligation, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
    else {
        return false;
    };
    let Ok(predicate) =
        trust_types::json_depth::from_str_deep::<trust_verifier_api::TrustSpecPredicate>(payload)
    else {
        return false;
    };
    if predicate.validate().is_err()
        || !predicate.has_current_schema()
        || predicate.root_sort != trust_verifier_api::TrustSpecSort::Bool
        || predicate.root.sort != trust_verifier_api::TrustSpecSort::Bool
    {
        return false;
    }

    let Some(encoded_context) =
        unique_metadata_value(obligation, trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY)
    else {
        return false;
    };
    let Ok(context) = trust_types::json_depth::from_str_deep::<trust_verifier_api::ObligationContext>(
        encoded_context,
    ) else {
        return false;
    };
    context.has_current_schema()
        && matches!(&context.producer, trust_verifier_api::ObligationProducer::CompilerMirExtract)
        && matches!(
            &context.origin,
            trust_verifier_api::ObligationOrigin::VerificationCondition {
                formula_schema: Some(formula_schema),
                ..
            } if formula_schema == trust_verifier_api::TRUST_SPEC_PREDICATE_SCHEMA_VERSION
        )
}

fn uniquely_declared_native_primary(obligation: &TrustObligation) -> Option<PrimaryEngine> {
    let mut declarations = obligation
        .metadata
        .iter()
        .filter(|entry| entry.key == TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY);
    let declaration = declarations.next()?;
    if declarations.next().is_some() {
        return None;
    }
    match declaration.value.as_str() {
        "trust-vc" => Some(PrimaryEngine::TrustVc),
        "trust-wp" => Some(PrimaryEngine::TrustWp),
        "trust-mc" => Some(PrimaryEngine::TrustMc),
        "ty" => Some(PrimaryEngine::Ty),
        _ => None,
    }
}

/// Payload-aware routing: keeps [`obligation_route_for_kind`] for every claim,
/// but routes a body-aware VC carrying the compiler's typed violation formula
/// to trust-mc's CHC/PDR lane. E4/E5 require the complete, current typed
/// predicate and compiler-origin envelope accepted by the TrustMC adapter;
/// the older pre/postcondition lane retains its payload-presence dispatch
/// behavior. This must match the compiler's
/// `native_trust_ir_route_for_api_obligation` exactly so engine dispatch and the
/// recorded-suite / expected-suite evidence check agree.
///
/// `Precondition`/`Postcondition` payloads are closed call/body reachability
/// queries. E4 `LoopInvariant` payloads are closed initiation or consecution
/// violations, and E5 `Termination` payloads are closed non-negative/strict-
/// decrease violations over the reconstructed transition. Payload-less authored
/// claims stay on trust-wp. Merely selecting this route is never proof: the
/// trust-mc adapter still requires a well-typed formula plus an exactly matching
/// native request, replay, and proof-check artifact.
pub(super) fn obligation_route(obligation: &TrustObligation) -> Option<ObligationRoute> {
    let body_aware_vc_kind = match &obligation.kind {
        ObligationKind::Postcondition => Some("Postcondition"),
        ObligationKind::Precondition => Some("Precondition"),
        ObligationKind::LoopInvariant => Some("LoopInvariant"),
        ObligationKind::Termination => Some("Termination"),
        _ => None,
    };
    if let Some(obligation_kind) = body_aware_vc_kind {
        let routes_to_trust_mc = match &obligation.kind {
            ObligationKind::Precondition | ObligationKind::Postcondition => {
                obligation_has_vc_formula_payload(obligation)
            }
            ObligationKind::LoopInvariant | ObligationKind::Termination => {
                is_typed_body_aware_e4_e5_obligation(obligation)
            }
            _ => false,
        };
        if routes_to_trust_mc {
            return Some(ObligationRoute {
                obligation_kind,
                primary: PrimaryEngine::TrustMc,
                proof_family: ProofFamily::TrustMcReachability,
                minimum_assurance: RequiredAssurance::SmtBacked,
            });
        }
        // A kernel-certified contract obligation is planned as a typed
        // TrustVc certificate import. Honor that route only for an exact,
        // unique native-suite declaration and only for contract kinds. The
        // declaration is routing input, never proof authority: acceptance
        // still requires the matching validated native request, public claim
        // identity, semantic digest, replayed certificate, and import
        // metadata. Body-aware CHC VCs above retain TrustMc precedence, so a
        // contradictory TrustVc declaration fails later at the typed suite
        // binding instead of changing ownership.
        if uniquely_declared_native_primary(obligation) == Some(PrimaryEngine::TrustVc) {
            return Some(ObligationRoute {
                obligation_kind,
                primary: PrimaryEngine::TrustVc,
                proof_family: ProofFamily::TrustVcOwnership,
                minimum_assurance: RequiredAssurance::Sound,
            });
        }
    }
    obligation_route_for_kind(&obligation.kind)
}

/// A designated deductive-fallback route.
///
/// Newtyped so a PRIMARY route can never be handed to the fallback path by
/// mistake. A fallback is adjudicated AS ITSELF — its own engine, its own proof
/// family, its own assurance floor — because `route` is the sole anchor for the
/// artifact policy, the accepted reasoning family, and the native suite
/// identity. Reusing the primary's family would let a foreign proof satisfy a
/// requirement written to forbid it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct FallbackRoute(pub(super) ObligationRoute);

/// The deductive-fallback table.
///
/// **EMPTY BY DESIGN.** The mechanism ships as a provable no-op; each row added
/// here is its own reviewed commit with its own verdict-flip check.
///
/// A row must NEVER be written as "the primary's route with `primary` swapped" —
/// see [`FallbackRoute`]. Write a complete route, and re-derive the proof family
/// and assurance floor for the engine that will actually run.
///
/// Adding the first row is additionally blocked on work outside this module:
/// `TrustVcVerificationMode` has no solve variant, so trust-vc cannot be asked to
/// derive on the native lane, and the compiler-side suite stamp is one of four
/// tables that must agree.
pub(super) fn fallback_route(_obligation: &TrustObligation) -> Option<FallbackRoute> {
    None
}

/// Why a declined obligation is, or is not, eligible for a second engine.
///
/// Pure and total so the rules are testable without standing up a dispatch.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum FallbackEligibility {
    /// Every rule held. The obligation may be re-attempted by the fallback.
    Eligible,
    /// The decline is terminal. The reason is kept for the audit trail.
    Terminal(FallbackRefusal),
}

/// The specific rule that made a decline terminal.
///
/// Enumerated so a refusal can be explained in a diagnostic rather than
/// silently doing nothing — "engine A declined, and here is why nobody else was
/// allowed to try" is the audit trail this mechanism owes a reader.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum FallbackRefusal {
    /// The primary produced a definitive verdict, or a sibling row did.
    /// A refutation is settled; re-litigating it is laundering.
    Definitive,
    /// The primary's evidence was accepted. Nothing to retry.
    Accepted,
    /// Not an `Unsupported` decline (Timeout, Canceled, Unknown, ...). None of
    /// these is a capability gap.
    NotADecline,
    /// No decline class, or a class that is not retryable. This is the default
    /// for every router-minted decline, every engine that has not been taught
    /// the distinction, and every older wire payload — terminal by construction.
    Unclassified,
    /// No fallback route is designated for this obligation.
    NoRoute,
    /// The designated fallback is the engine that already declined.
    SameEngine,
    /// The verification budget is exhausted; a retry would be unbounded work.
    BudgetExceeded,
}

/// Adjudicate whether a declined obligation may be re-attempted.
///
/// SOUNDNESS: this is written so that EVERY path not explicitly proven safe
/// returns `Terminal`. The rules are conjunctive and each is a positive test.
///
/// The caller must additionally establish, structurally, that the row came from
/// a real engine batch rather than one of the pre-dispatch declines — those are
/// router-minted and carry `decline: None`, so they are already caught by the
/// `Unclassified` arm, but relying on that alone would be relying on an
/// accident.
pub(super) fn fallback_eligibility(
    accepted: bool,
    status: EvidenceStatus,
    decline: Option<DeclineClass>,
    sibling_rows_are_definitive: bool,
    route: Option<FallbackRoute>,
    primary_engine_index: usize,
    fallback_engine_index: Option<usize>,
    budget_exceeded: bool,
) -> FallbackEligibility {
    use FallbackEligibility::{Eligible, Terminal};
    use FallbackRefusal as R;

    // A definitive verdict anywhere for this obligation ends the matter. This is
    // checked FIRST and covers the ladder hole: `rejected_primary_evidence` ranks
    // `Unsupported` above `Proved`, so an engine that returned BOTH a capability
    // decline and a Proved row the router rejected would present the decline as
    // the final row. Retrying there would erase the rejected proof that poisons
    // strict acceptance downstream.
    if sibling_rows_are_definitive {
        return Terminal(R::Definitive);
    }
    if matches!(status, EvidenceStatus::Proved | EvidenceStatus::Failed) {
        return Terminal(R::Definitive);
    }
    if accepted {
        return Terminal(R::Accepted);
    }
    if status != EvidenceStatus::Unsupported {
        return Terminal(R::NotADecline);
    }
    if !DeclineClass::is_retryable(decline) {
        return Terminal(R::Unclassified);
    }
    if budget_exceeded {
        return Terminal(R::BudgetExceeded);
    }
    let Some(_route) = route else {
        return Terminal(R::NoRoute);
    };
    match fallback_engine_index {
        None => Terminal(R::NoRoute),
        Some(index) if index == primary_engine_index => Terminal(R::SameEngine),
        Some(_) => Eligible,
    }
}

pub(super) fn obligation_route_for_kind(kind: &ObligationKind) -> Option<ObligationRoute> {
    let route = match kind {
        ObligationKind::Precondition => ObligationRoute {
            obligation_kind: "Precondition",
            primary: PrimaryEngine::TrustWp,
            proof_family: ProofFamily::TrustWpFunctional,
            minimum_assurance: RequiredAssurance::Sound,
        },
        ObligationKind::Postcondition => ObligationRoute {
            obligation_kind: "Postcondition",
            primary: PrimaryEngine::TrustWp,
            proof_family: ProofFamily::TrustWpFunctional,
            minimum_assurance: RequiredAssurance::Sound,
        },
        ObligationKind::Assertion => ObligationRoute {
            obligation_kind: "Assertion",
            primary: PrimaryEngine::TrustMc,
            proof_family: ProofFamily::TrustMcReachability,
            minimum_assurance: RequiredAssurance::SmtBacked,
        },
        ObligationKind::Invariant => ObligationRoute {
            obligation_kind: "Invariant",
            primary: PrimaryEngine::TrustMc,
            proof_family: ProofFamily::TrustMcReachability,
            minimum_assurance: RequiredAssurance::SmtBacked,
        },
        ObligationKind::LoopInvariant => ObligationRoute {
            obligation_kind: "LoopInvariant",
            primary: PrimaryEngine::TrustWp,
            proof_family: ProofFamily::TrustWpFunctional,
            minimum_assurance: RequiredAssurance::Sound,
        },
        ObligationKind::ArithmeticSafety => ObligationRoute {
            obligation_kind: "ArithmeticSafety",
            primary: PrimaryEngine::TrustMc,
            proof_family: ProofFamily::TrustMcReachability,
            minimum_assurance: RequiredAssurance::SmtBacked,
        },
        ObligationKind::MemorySafety => ObligationRoute {
            obligation_kind: "MemorySafety",
            primary: PrimaryEngine::TrustVc,
            proof_family: ProofFamily::TrustVcOwnership,
            minimum_assurance: RequiredAssurance::Sound,
        },
        // BoundsCheck is trust-vc-owned end-to-end: the compiler constructs a
        // MIR-memory proof unit whose predicate is the negated guard-conjoined
        // bounds VC, and TrustVcTrustEngine discharges it with a replayable
        // certificate at import time. Without this route the full verifier
        // rejected the KIND before any engine saw the discharged evidence.
        ObligationKind::BoundsCheck => ObligationRoute {
            obligation_kind: "BoundsCheck",
            primary: PrimaryEngine::TrustVc,
            proof_family: ProofFamily::TrustVcOwnership,
            minimum_assurance: RequiredAssurance::Sound,
        },
        ObligationKind::Ownership => ObligationRoute {
            obligation_kind: "Ownership",
            primary: PrimaryEngine::TrustVc,
            proof_family: ProofFamily::TrustVcOwnership,
            minimum_assurance: RequiredAssurance::Sound,
        },
        ObligationKind::Refinement => ObligationRoute {
            obligation_kind: "Refinement",
            primary: PrimaryEngine::TrustWp,
            proof_family: ProofFamily::TrustWpFunctional,
            minimum_assurance: RequiredAssurance::Sound,
        },
        ObligationKind::Termination => ObligationRoute {
            obligation_kind: "Termination",
            primary: PrimaryEngine::TrustWp,
            proof_family: ProofFamily::TrustWpFunctional,
            minimum_assurance: RequiredAssurance::Sound,
        },
        ObligationKind::TemporalSafety => ObligationRoute {
            obligation_kind: "TemporalSafety",
            primary: PrimaryEngine::Ty,
            proof_family: ProofFamily::TyTemporal,
            minimum_assurance: RequiredAssurance::Sound,
        },
        ObligationKind::Liveness => ObligationRoute {
            obligation_kind: "Liveness",
            primary: PrimaryEngine::Ty,
            proof_family: ProofFamily::TyTemporal,
            minimum_assurance: RequiredAssurance::Sound,
        },
        ObligationKind::Protocol => ObligationRoute {
            obligation_kind: "Protocol",
            primary: PrimaryEngine::TrustMc,
            proof_family: ProofFamily::TrustMcReachability,
            minimum_assurance: RequiredAssurance::SmtBacked,
        },
        ObligationKind::Custom { namespace, .. } if namespace == TRUST_VC_HARDENED_NAMESPACE => {
            ObligationRoute {
                obligation_kind: "HardenedBoundary",
                primary: PrimaryEngine::TrustMc,
                proof_family: ProofFamily::TrustMcReachability,
                minimum_assurance: RequiredAssurance::SmtBacked,
            }
        }
        ObligationKind::Custom { .. } => return None,
        _ => return None,
    };

    Some(route)
}

pub(super) fn assurance_satisfies(strength: &ProofStrength, minimum: RequiredAssurance) -> bool {
    match minimum {
        RequiredAssurance::SmtBacked => matches!(
            strength.assurance,
            trust_verifier_api::AssuranceLevel::SmtBacked
                | trust_verifier_api::AssuranceLevel::Sound
                | trust_verifier_api::AssuranceLevel::Certified
        ),
        RequiredAssurance::Sound => matches!(
            strength.assurance,
            trust_verifier_api::AssuranceLevel::Sound
                | trust_verifier_api::AssuranceLevel::Certified
        ),
    }
}
